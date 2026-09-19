"""Rotas do módulo de Cobrança (Dashboard Operacional).

Separado do app.py porque o monolito já serve 5 domínios; a cobrança vai crescer
(régua de chamadas, jurídico, negativação) e não cabe lá dentro.

Os paths das 4 rotas antigas foram preservados (/api/cidades, /api/vendedores,
/api/parceiros, /api/receitas-vencidas) para não quebrar o app que já as consome.
As rotas novas ficam sob /api/cobranca/*.
"""

import base64
import hashlib
import hmac
import json
import os
import secrets
import time
from datetime import datetime
from functools import wraps
from urllib.parse import unquote

import cx_Oracle
import requests
from flask import Blueprint, jsonify, request
from werkzeug.utils import secure_filename

import drive
from db import conectar_oracle
# Reaproveita a autenticação de aplicação (OAuth client_credentials) e a base do
# Gateway já usadas no recálculo de impostos. O README marca essas funções como
# reaproveitáveis de propósito.
from impostos import autenticar_sankhya, _api_base

bp = Blueprint("cobranca", __name__)

# Timeout (segundos) das chamadas HTTP ao Gateway do Sankhya.
_TIMEOUT = 30


def _erro(err, codigo=500):
    print("Erro:", err)
    return jsonify({"erro": str(err)}), codigo


def _txt(valor):
    """Texto do banco: espaços em branco viram None.

    Campos como TGFPAR.EMAIL vêm preenchidos com espaços ("  ") em vez de NULL.
    Uma string dessas é "verdadeira" em JS e o front acabaria exibindo um campo
    vazio em vez de "sem e-mail".
    """
    if valor is None:
        return None
    limpo = str(valor).strip()
    return limpo or None


# ---------------------------------------------------------------------------
# RECDESP: por que = 1, e NUNCA 0
#
# RECDESP não é "receita vs. despesa" como o nome sugere:
#    1 → título ATIVO de receita. É o que a cobrança persegue.
#    0 → título NEUTRALIZADO: a origem de uma renegociação. Já foi substituído
#        por outro(s) título(s) e NÃO é mais dívida. Nunca tem baixa, por isso
#        parece "vencido para sempre".
#   -1 → despesa (compra, folha, tributos).
#
# Confirmado com o responsável pela cobrança em 2026-07-13. Incluir o 0 conta a
# mesma dívida DUAS VEZES (o título velho renegociado + o novo que o substituiu):
# chegamos a inflar a carteira em R$ 4,1 milhões de "VENDA GERENCIAL - A VISTA"
# que já estavam renegociados. NÃO reabrir o filtro para 0.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Regra de cheques (pendentes, em aberto e devolvidos)
#
# Cheque não segue a regra dos demais títulos:
#   - CHQ_NORMAL: já foi baixado na conta 16, mas continua pendente;
#   - CHQ_ABERTO: ainda está em aberto no financeiro (sem baixa nenhuma);
#   - DEV_1657: cheque devolvido pela TOP 1657 e ainda pendente.
#
# A regra vive nestas CTEs, reaproveitadas pela consulta de títulos vencidos,
# pelo extrato da Visão 360° e pelo painel da gerência.
#
# Fonte: relatório oficial de cheques do Sankhya (revisão do DBA de 2026-08-10,
# que acrescentou o CHQ_ABERTO — a gerente reportou cheques faltando na tela).
#
# IMPORTANTE sobre CHQ_ABERTO:
# - considera SOMENTE CODTIPTIT = 3; não inclui cartão/POS ou outro tipo;
# - o JOIN com a TGFCHQ é LEFT de propósito: o financeiro pode ainda não ter o
#   registro do cheque formado. Nesse caso o número sai do FIN.NUMNOTA e a data
#   efetiva é o DTVENC;
# - NÃO filtra AD_ACERTADO, porque foi validado no financeiro que um cheque
#   ainda sem baixa pode estar com AD_ACERTADO = 'S' (é o filtro que fazia esses
#   cheques sumirem da consulta);
# - mantém RECDESP = 1 e exclui a origem neutralizada de renegociação;
# - repete a exclusão por devolução TOP 1657 do CHQ_NORMAL: sem ela o mesmo
#   cheque apareceria duas vezes, como "EM ABERTO" (título original) e como
#   "DEVOLVIDO" (título da devolução), dobrando o valor na carteira.
#
# Para cheque, o vencimento que vale é o "bom para" (TGFCHQ.DATACHEQUE) — e não
# o DTVENC do financeiro. O cálculo de atraso segue essa data.
# ---------------------------------------------------------------------------
CTE_CHEQUES = """
WITH ULT_EVENTO AS (
    SELECT
        ECQ.NUCHQ,
        ECQ.NUEVENTO,
        ECQ.DHEVENTO,
        ECQ.TIPO,
        ROW_NUMBER() OVER (
            PARTITION BY ECQ.NUCHQ
            ORDER BY ECQ.NUEVENTO DESC, ECQ.DHEVENTO DESC
        ) AS RN
    FROM TGFECQ ECQ
),
CHQ_NORMAL AS (
    SELECT
        'P' AS STATUS_REGRA,
        'CHQ_NORMAL' AS ORIGEM_REGRA,
        FIN.NUFIN,
        TO_CHAR(CHQ.NUMCHEQUE) AS CHEQUE,
        ROUND(NVL(NULLIF(CHQ.VLRCHEQUE, 0), NVL(FIN.VLRDESDOB, 0)), 2) AS VLRCHEQUE_REGRA,
        NVL(CHQ.DATACHEQUE, FIN.DTVENC) AS DATACHEQUE_REGRA,
        'Pendente' AS ULTIMO_EVENTO_REGRA
    FROM TGFFIN FIN
    JOIN TGFCHQ CHQ ON CHQ.NUFIN = FIN.NUFIN
    JOIN ULT_EVENTO ULT ON ULT.NUCHQ = CHQ.NUCHQ AND ULT.RN = 1
    WHERE FIN.CODTIPTIT = 3
      AND FIN.RECDESP = 1
      AND NVL(FIN.PROVISAO, 'N') = 'N'
      AND FIN.AD_ACERTADO = 'N'
      AND NVL(FIN.CODTIPOPER, 0) <> 1657
      AND FIN.DHBAIXA IS NOT NULL
      AND NVL(FIN.VLRBAIXA, 0) > 0
      AND NVL(FIN.CODCTABCOINT, -1) = 16
      AND ULT.TIPO = 'B'
      AND NVL(CHQ.STATUS, 'X') <> 'T'
      AND NVL(FIN.NUCOMPENS, 0) = 0
      /* Exclui só o título de ORIGEM da renegociação; o de destino continua entrando. */
      AND NOT EXISTS (
          SELECT 1 FROM TGFREN REN_ORIG WHERE REN_ORIG.NUFIN = FIN.NUFIN
      )
      AND NVL(CHQ.DATACHEQUE, FIN.DTVENC) IS NOT NULL
      AND REGEXP_LIKE(TRIM(TO_CHAR(CHQ.NUMCHEQUE)), '[1-9]')
      AND REGEXP_LIKE(
          REGEXP_REPLACE(TRIM(TO_CHAR(NVL(FIN.CONTA_CMC7, CHQ.CMC7))), '[^0-9]', ''),
          '[1-9]'
      )
      AND NOT EXISTS (
          SELECT 1 FROM TGFFRE FRE
          WHERE FRE.NUFIN = FIN.NUFIN AND FRE.TIPACERTO = 'C'
      )
      AND NOT EXISTS (
          SELECT 1 FROM TGFECQ EVTPAG
          WHERE EVTPAG.NUCHQ = CHQ.NUCHQ
            AND EVTPAG.TIPO IN ('P', 'T')
            AND NOT EXISTS (
                SELECT 1 FROM TGFECQ EVTDEV
                WHERE EVTDEV.NUCHQ = EVTPAG.NUCHQ
                  AND EVTDEV.TIPO = 'D'
                  AND NVL(EVTDEV.NUEVENTO, 0) > NVL(EVTPAG.NUEVENTO, 0)
            )
      )
      AND NOT EXISTS (
          SELECT 1 FROM TGFFIN DEV
          WHERE DEV.CODPARC = FIN.CODPARC
            AND DEV.RECDESP = 1
            AND DEV.CODTIPOPER = 1657
            AND NVL(DEV.PROVISAO, 'N') = 'N'
            AND (
                  REGEXP_LIKE(
                      UPPER(NVL(DEV.HISTORICO, ' ')),
                      '(^|[^0-9])0*' ||
                      NVL(NULLIF(LTRIM(TO_CHAR(CHQ.NUMCHEQUE), '0'), ''), '0') ||
                      '([^0-9]|$)'
                  )
                  OR
                  NVL(NULLIF(LTRIM(TO_CHAR(DEV.NUMNOTA), '0'), ''), '0') =
                  NVL(NULLIF(LTRIM(TO_CHAR(CHQ.NUMCHEQUE), '0'), ''), '0')
            )
      )
),
CHQ_ABERTO AS (
    SELECT
        'A' AS STATUS_REGRA,
        'CHQ_ABERTO' AS ORIGEM_REGRA,
        FIN.NUFIN,
        /* Sem TGFCHQ formada, o número do cheque é o da nota. */
        TO_CHAR(NVL(CHQ.NUMCHEQUE, FIN.NUMNOTA)) AS CHEQUE,
        ROUND(NVL(NULLIF(CHQ.VLRCHEQUE, 0), NVL(FIN.VLRDESDOB, 0)), 2) AS VLRCHEQUE_REGRA,
        NVL(CHQ.DATACHEQUE, FIN.DTVENC) AS DATACHEQUE_REGRA,
        'Em aberto' AS ULTIMO_EVENTO_REGRA
    FROM TGFFIN FIN
    /* LEFT de propósito: o financeiro pode não ter o cheque cadastrado ainda. */
    LEFT JOIN TGFCHQ CHQ ON CHQ.NUFIN = FIN.NUFIN
    WHERE FIN.CODTIPTIT = 3
      AND FIN.RECDESP = 1
      AND NVL(FIN.PROVISAO, 'N') = 'N'
      /* Devolução é tratada pela DEV_1657. */
      AND NVL(FIN.CODTIPOPER, 0) <> 1657
      /* Principal diferença para o CHQ_NORMAL: ainda não houve baixa nenhuma. */
      AND FIN.DHBAIXA IS NULL
      AND NVL(FIN.VLRBAIXA, 0) = 0
      AND NVL(FIN.NUCOMPENS, 0) = 0
      /* AD_ACERTADO NÃO é filtro aqui: nos casos validados estava 'S'. */
      /* Exclui só o título de ORIGEM da renegociação; o de destino continua entrando. */
      AND NOT EXISTS (
          SELECT 1 FROM TGFREN REN_ORIG WHERE REN_ORIG.NUFIN = FIN.NUFIN
      )
      /* Se já houver TGFCHQ, respeita o status; sem TGFCHQ, continua entrando. */
      AND NVL(CHQ.STATUS, 'X') <> 'T'
      AND NVL(CHQ.DATACHEQUE, FIN.DTVENC) IS NOT NULL
      AND NOT EXISTS (
          SELECT 1 FROM TGFFRE FRE
          WHERE FRE.NUFIN = FIN.NUFIN AND FRE.TIPACERTO = 'C'
      )
      /* Pagamento/transferência definitivo (sem devolução posterior) não entra. */
      AND NOT EXISTS (
          SELECT 1 FROM TGFECQ EVTPAG
          WHERE EVTPAG.NUCHQ = CHQ.NUCHQ
            AND EVTPAG.TIPO IN ('P', 'T')
            AND NOT EXISTS (
                SELECT 1 FROM TGFECQ EVTDEV
                WHERE EVTDEV.NUCHQ = EVTPAG.NUCHQ
                  AND EVTDEV.TIPO = 'D'
                  AND NVL(EVTDEV.NUEVENTO, 0) > NVL(EVTPAG.NUEVENTO, 0)
            )
      )
      /* Já existe a devolução do mesmo cheque pela TOP 1657: quem vale é ela
         (DEV_1657). Sem esta exclusão o cheque seria contado duas vezes. */
      AND NOT EXISTS (
          SELECT 1 FROM TGFFIN DEV
          WHERE DEV.CODPARC = FIN.CODPARC
            AND DEV.RECDESP = 1
            AND DEV.CODTIPOPER = 1657
            AND NVL(DEV.PROVISAO, 'N') = 'N'
            AND (
                  REGEXP_LIKE(
                      UPPER(NVL(DEV.HISTORICO, ' ')),
                      '(^|[^0-9])0*' ||
                      NVL(NULLIF(LTRIM(TO_CHAR(NVL(CHQ.NUMCHEQUE, FIN.NUMNOTA)), '0'), ''), '0') ||
                      '([^0-9]|$)'
                  )
                  OR
                  NVL(NULLIF(LTRIM(TO_CHAR(DEV.NUMNOTA), '0'), ''), '0') =
                  NVL(NULLIF(LTRIM(TO_CHAR(NVL(CHQ.NUMCHEQUE, FIN.NUMNOTA)), '0'), ''), '0')
            )
      )
),
DEV_1657 AS (
    SELECT
        'D' AS STATUS_REGRA,
        'TOP_1657' AS ORIGEM_REGRA,
        FIN.NUFIN,
        COALESCE(
            REGEXP_REPLACE(
                REGEXP_SUBSTR(
                    UPPER(NVL(FIN.HISTORICO, '')),
                    '(CH|CHQ|CHEQ|CHEQUE)[^0-9]{0,30}[0-9]{1,10}'
                ), '[^0-9]', ''
            ),
            REGEXP_REPLACE(
                REGEXP_SUBSTR(
                    UPPER(NVL(FIN.HISTORICO, '')),
                    '[0-9]{1,10}[[:space:]-]*(CH|CHQ|CHEQ|CHEQUE)'
                ), '[^0-9]', ''
            ),
            TO_CHAR(FIN.NUMNOTA)
        ) AS CHEQUE,
        ROUND(NVL(FIN.VLRDESDOB, 0), 2) AS VLRCHEQUE_REGRA,
        FIN.DTVENC AS DATACHEQUE_REGRA,
        'Devolução' AS ULTIMO_EVENTO_REGRA
    FROM TGFFIN FIN
    WHERE FIN.CODTIPTIT = 3
      AND FIN.RECDESP = 1
      AND NVL(FIN.PROVISAO, 'N') = 'N'
      AND FIN.AD_ACERTADO = 'N'
      AND FIN.CODTIPOPER = 1657
      AND FIN.DHBAIXA IS NULL
      AND NVL(FIN.VLRBAIXA, 0) = 0
      AND NVL(FIN.NUCOMPENS, 0) = 0
      AND NOT EXISTS (
          SELECT 1 FROM TGFREN REN_ORIG WHERE REN_ORIG.NUFIN = FIN.NUFIN
      )
      AND FIN.DTVENC IS NOT NULL
      AND NOT EXISTS (
          SELECT 1 FROM TGFFRE FRE
          WHERE FRE.NUFIN = FIN.NUFIN AND FRE.TIPACERTO = 'C'
      )
),
CHEQUES_REGRA AS (
    SELECT STATUS_REGRA, ORIGEM_REGRA, NUFIN, CHEQUE,
           VLRCHEQUE_REGRA, DATACHEQUE_REGRA, ULTIMO_EVENTO_REGRA
    FROM CHQ_NORMAL
    UNION ALL
    SELECT STATUS_REGRA, ORIGEM_REGRA, NUFIN, CHEQUE,
           VLRCHEQUE_REGRA, DATACHEQUE_REGRA, ULTIMO_EVENTO_REGRA
    FROM CHQ_ABERTO
    UNION ALL
    SELECT STATUS_REGRA, ORIGEM_REGRA, NUFIN, CHEQUE,
           VLRCHEQUE_REGRA, DATACHEQUE_REGRA, ULTIMO_EVENTO_REGRA
    FROM DEV_1657
),
/* Renegociações podem gerar novos títulos sem NUNOTA e com CODVEND = 0.
   Nesse caso, herda o vendedor interno SOMENTE quando todas as origens
   neutralizadas (RECDESP = 0) da renegociação apontam para o mesmo vendedor
   interno válido. Se houver mistura ou origem sem vendedor, mantém 0. */
RENEG_VENDEDOR AS (
    SELECT
        F_ORIG.NURENEG,
        CASE
            WHEN COUNT(DISTINCT CASE
                     WHEN NVL(CAB_ORIG.AD_CODVENDINT, 0) > 0
                      AND VEN_ORIG.AD_VENDINTEXT = 'I'
                     THEN CAB_ORIG.AD_CODVENDINT
                 END) = 1
             AND COUNT(*) = SUM(CASE
                     WHEN NVL(CAB_ORIG.AD_CODVENDINT, 0) > 0
                      AND VEN_ORIG.AD_VENDINTEXT = 'I'
                     THEN 1 ELSE 0
                 END)
            THEN MAX(CASE
                     WHEN NVL(CAB_ORIG.AD_CODVENDINT, 0) > 0
                      AND VEN_ORIG.AD_VENDINTEXT = 'I'
                     THEN CAB_ORIG.AD_CODVENDINT
                 END)
        END AS CODVENDINT_RENEG
    FROM TGFFIN F_ORIG
        LEFT JOIN TGFCAB CAB_ORIG
               ON CAB_ORIG.NUNOTA = F_ORIG.NUNOTA
        LEFT JOIN TGFVEN VEN_ORIG
               ON VEN_ORIG.CODVEND = CAB_ORIG.AD_CODVENDINT
    WHERE F_ORIG.RECDESP = 0
      AND F_ORIG.NURENEG IS NOT NULL
    GROUP BY F_ORIG.NURENEG
)
"""

# Data de vencimento "que vale": bom-para do cheque, ou DTVENC dos demais.
DT_EFETIVA = """
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.DATACHEQUE_REGRA ELSE FIN.DTVENC END
"""

# Vendedor efetivo da cobrança:
# 1) CODVEND > 0 continua sendo soberano;
# 2) com CODVEND 0/nulo, usa AD_CODVENDINT da venda direta;
# 3) se a renegociação perdeu a NUNOTA, herda o único vendedor interno comum
#    às origens neutralizadas da mesma NURENEG; caso ambíguo permanece vendedor 0.
CODVEND_EFETIVO = """
    CASE
        WHEN NVL(FIN.CODVEND, 0) > 0
        THEN FIN.CODVEND

        WHEN NVL(CAB.AD_CODVENDINT, 0) > 0
        THEN CAB.AD_CODVENDINT

        WHEN NVL(RENV.CODVENDINT_RENEG, 0) > 0
        THEN RENV.CODVENDINT_RENEG

        ELSE 0
    END
"""

# JOINs comuns às consultas de títulos.
JOINS_TITULO = f"""
    FROM TGFFIN FIN
        INNER JOIN TGFPAR PAR  ON PAR.CODPARC      = FIN.CODPARC
        LEFT JOIN TGFCAB CAB   ON CAB.NUNOTA       = FIN.NUNOTA
        LEFT JOIN RENEG_VENDEDOR RENV ON RENV.NURENEG = FIN.NURENEG
        LEFT JOIN TSICID CID   ON CID.CODCID       = PAR.CODCID
        LEFT JOIN TSIUFS UFS   ON UFS.CODUF        = CID.UF
        LEFT JOIN TGFTIT TIT   ON TIT.CODTIPTIT    = FIN.CODTIPTIT
        LEFT JOIN TGFVEN VEN   ON VEN.CODVEND      = {CODVEND_EFETIVO}
        LEFT JOIN TSICTA CTA   ON CTA.CODCTABCOINT = FIN.CODCTABCOINT
        LEFT JOIN TGFOBS OBS   ON OBS.CODOBSPADRAO = FIN.CODOBSPADRAO
        LEFT JOIN VGFFIN VFIN  ON VFIN.NUFIN       = FIN.NUFIN
        LEFT JOIN CHEQUES_REGRA CHR ON CHR.NUFIN   = FIN.NUFIN
        LEFT JOIN TGFTOP TOP   ON TOP.CODTIPOPER   = FIN.CODTIPOPER
                              AND TOP.DHALTER      = FIN.DHTIPOPER
"""


# --- Listas de apoio (filtros) ---


@bp.route("/api/cidades", methods=["GET"])
def cidades():
    # TSICID.UF guarda o CÓDIGO da UF; a sigla vem da TSIUFS.
    sql = """
    SELECT CID.CODCID, CID.NOMECID, UFS.UF
    FROM TSICID CID
        LEFT JOIN TSIUFS UFS ON UFS.CODUF = CID.UF
    ORDER BY CID.NOMECID
    """
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(sql)
        dados = [
            {"codCid": r[0], "nomeCid": r[1], "uf": r[2]} for r in cursor.fetchall()
        ]
        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/vendedores", methods=["GET"])
def vendedores():
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute("SELECT CODVEND, APELIDO FROM TGFVEN ORDER BY APELIDO")
        dados = [{"codVend": r[0], "apelido": r[1]} for r in cursor.fetchall()]
        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/parceiros", methods=["GET"])
def parceiros():
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(
            "SELECT CODPARC, NOMEPARC, RAZAOSOCIAL, CGC_CPF FROM TGFPAR ORDER BY NOMEPARC"
        )
        dados = [
            {"codParc": r[0], "nomeParc": r[1], "razaoSocial": r[2], "cgcCpf": r[3]}
            for r in cursor.fetchall()
        ]
        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


# --- Títulos vencidos / cheques pendentes, em aberto e devolvidos ---

SELECT_RECEITAS = f"""
SELECT
    FIN.NOSSONUM,
    FIN.NUCOMPENS,
    FIN.NUNOTA,
    FIN.DTNEG,
    {DT_EFETIVA} AS DT_VENCIMENTO,
    FIN.NUFIN,
    FIN.NUMNOTA,
    FIN.VLRDESDOB,
    VFIN.VLRLIQUIDO,
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.VLRCHEQUE_REGRA ELSE FIN.VLRCHEQUE END AS VLR_CHEQUE,
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.CHEQUE END AS NUMERO_CHEQUE,
    FIN.HISTORICO,
    CTA.DESCRICAO,
    PAR.RAZAOSOCIAL,
    FIN.CODPARC,
    PAR.NOMEPARC,
    PAR.TELEFONE,
    CID.CODCID,
    CID.NOMECID,
    UFS.UF,
    FIN.CGC_CPF_CMC7,
    FIN.CODTIPTIT,
    TIT.DESCRTIPTIT,
    CASE
        WHEN FIN.CODTIPTIT = 3 AND CHR.STATUS_REGRA = 'P' THEN 'CHEQUE PENDENTE'
        WHEN FIN.CODTIPTIT = 3 AND CHR.STATUS_REGRA = 'A' THEN 'CHEQUE EM ABERTO'
        WHEN FIN.CODTIPTIT = 3 AND CHR.STATUS_REGRA = 'D' THEN 'CHEQUE DEVOLVIDO'
        WHEN FIN.CODTIPTIT <> 3 AND FIN.NURENEG IS NOT NULL
            THEN 'TÍTULO RENEGOCIADO VENCIDO SEM PAGAMENTO'
        WHEN FIN.CODTIPTIT IN (2, 4, 5, 39)               THEN 'TÍTULO VENCIDO SEM PAGAMENTO'
    END AS SITUACAO,
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.ULTIMO_EVENTO_REGRA END AS ULTIMO_EVENTO,
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.ORIGEM_REGRA END       AS ORIGEM_REGRA,
    FIN.NURENEG,
    NVL(FIN.VLRDESC, 0),
    CASE
        WHEN LENGTH(REGEXP_REPLACE(PAR.CGC_CPF, '[^0-9]', '')) = 14 THEN
            REGEXP_REPLACE(REGEXP_REPLACE(PAR.CGC_CPF, '[^0-9]', ''), '([0-9]{{2}})([0-9]{{3}})([0-9]{{3}})([0-9]{{4}})([0-9]{{2}})', '\\1.\\2.\\3/\\4-\\5')
        WHEN LENGTH(REGEXP_REPLACE(PAR.CGC_CPF, '[^0-9]', '')) = 11 THEN
            REGEXP_REPLACE(REGEXP_REPLACE(PAR.CGC_CPF, '[^0-9]', ''), '([0-9]{{3}})([0-9]{{3}})([0-9]{{3}})([0-9]{{2}})', '\\1.\\2.\\3-\\4')
        ELSE PAR.CGC_CPF
    END AS CNPJ_CPF,
    NVL(FIN.VLRJURO, 0),
    GREATEST(TRUNC(SYSDATE) - TRUNC({DT_EFETIVA}), 0) AS ATRASO_DIAS,
    NVL(VEN.APELIDO, 'SEM VENDEDOR'),
    FIN.CODOBSPADRAO,
    OBS.OBSERVACAO,
    FIN.DESDOBRAMENTO,
    FIN.NOMEEMITENTE_CMC7,
    FIN.RECDESP,
    FIN.CODTIPOPER,
    TOP.DESCROPER,
    /* Coluna NOVA, no FIM da lista de propósito: o /receitas-vencidas lê o
       resultado POSICIONALMENTE (row[0]..row[38]), e coluna acrescentada no meio
       deslocaria todas as seguintes. Existe para a Visão 360° por Vendedor poder
       AGRUPAR por vendedor — o APELIDO acima é só rótulo e não tem alias, então
       não serve como chave. Ver docs/VENDEDOR-360.md §3. */
    {CODVEND_EFETIVO} AS CODVEND
{JOINS_TITULO}
WHERE FIN.RECDESP = 1
  AND NVL(FIN.PROVISAO, 'N') = 'N'
  AND (
        /* Títulos normais de cobrança. */
        /* (FIN.CODTIPTIT IN (2, 4, 5, 39) AND FIN.DHBAIXA IS NULL AND FIN.DTVENC < TRUNC(SYSDATE)) */
        (FIN.CODTIPTIT IN (2, 4, 5, 39) AND FIN.DHBAIXA IS NULL)
        OR
        /* Cheques: só os aprovados pela regra do relatório. */
        (FIN.CODTIPTIT = 3 AND CHR.NUFIN IS NOT NULL)
        OR
        /* Título ATIVO gerado por renegociação: pode ter tipo fora da lista
           (PIX, cartão...). O título de ORIGEM não entra — ele é RECDESP = 0. */
        (
            FIN.CODTIPTIT NOT IN (2, 3, 4, 5, 39)
            AND FIN.NURENEG IS NOT NULL
            AND FIN.DHBAIXA IS NULL
            /* AND FIN.DTVENC < TRUNC(SYSDATE) */
        )
      )
"""


@bp.route("/api/receitas-vencidas", methods=["POST"])
def receitas_vencidas():
    data = request.get_json() or {}

    cod_emp = data.get("codEmp")
    cod_parc = data.get("codParc")
    cod_vend = data.get("codVend")
    cod_cid = data.get("codCid")
    dt_inicial = data.get("dtInicial")
    dt_final = data.get("dtFinal")

    filtros = []
    params = {}

    if cod_emp:
        filtros.append("AND FIN.CODEMP = :CODEMP")
        params["CODEMP"] = cod_emp
    if cod_parc:
        filtros.append("AND FIN.CODPARC = :CODPARC")
        params["CODPARC"] = cod_parc
    if cod_vend is not None:
        filtros.append(f"AND ({CODVEND_EFETIVO}) = :CODVEND")
        params["CODVEND"] = cod_vend
    if cod_cid:
        filtros.append("AND PAR.CODCID = :CODCID")
        params["CODCID"] = cod_cid
    if dt_inicial and dt_final:
        # O período usa a data efetiva: bom-para do cheque, DTVENC dos demais.
        filtros.append(
            f"AND TRUNC({DT_EFETIVA}) BETWEEN TO_DATE(:DT_INICIAL, 'YYYY-MM-DD') "
            "AND TO_DATE(:DT_FINAL, 'YYYY-MM-DD')"
        )
        params["DT_INICIAL"] = dt_inicial
        params["DT_FINAL"] = dt_final

    sql = (
        CTE_CHEQUES
        + SELECT_RECEITAS
        + "\n".join(filtros)
        + f"\nORDER BY {DT_EFETIVA}, PAR.NOMEPARC, FIN.NUFIN"
    )

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(sql, params)

        dados = []
        for row in cursor.fetchall():
            dados.append(
                {
                    "nossoNum": row[0],
                    "nuCompens": row[1],
                    "nuNota": row[2],
                    "dtNeg": row[3].strftime("%Y-%m-%d") if row[3] else None,
                    "dtVenc": row[4].strftime("%Y-%m-%d") if row[4] else None,
                    "nuFin": row[5],
                    "numNota": row[6],
                    "vlrDesdob": float(row[7]) if row[7] is not None else None,
                    "vlrLiquido": float(row[8]) if row[8] is not None else None,
                    "vlrCheque": float(row[9]) if row[9] is not None else None,
                    "numeroCheque": row[10],
                    "historico": row[11],
                    "contaBancaria": row[12],
                    "razaoSocial": row[13],
                    "codParc": row[14],
                    "nomeParc": row[15],
                    "telefone": row[16],
                    "codCid": row[17],
                    "nomeCid": row[18],
                    "uf": row[19],
                    "cgcCpfCmc7": row[20],
                    "codTipTit": row[21],
                    "tipoTitulo": row[22],
                    "situacao": row[23],
                    "ultimoEvento": row[24],
                    "origemRegra": row[25],
                    "nuReneg": row[26],
                    "vlrDesconto": float(row[27]) if row[27] is not None else 0.0,
                    "cnpjCpf": row[28],
                    "vlrJuros": float(row[29]) if row[29] is not None else 0.0,
                    "atrasoDias": int(row[30]) if row[30] is not None else 0,
                    "vendedor": row[31],
                    "codObsPadrao": row[32],
                    "observacao": row[33],
                    "desdobramento": row[34],
                    "nomeEmitente": row[35],
                    "recDesp": row[36],
                    "codTipOper": row[37],
                    "operacao": _txt(row[38]),
                }
            )

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


# --- Visão 360° do cliente ---

# ---------------------------------------------------------------------------
# Pontualidade: NÃO calcular aqui. Ler da AD_LIMCREDANALISE.
#
# O Sankhya já calcula a pontualidade histórica pela procedure
# PRC_ATUALIZA_LIMCREDANALISE e deixa o resultado MATERIALIZADO na
# AD_LIMCREDANALISE (PCT_PAGO_EM_DIA, já em escala 0-100). A consulta de
# análise de crédito do BI apenas exibe esse valor — e o comentário dela diz o
# porquê: recalcular "na mão" perde os atrasos que foram regularizados por
# renegociação e trata entrada de cheque na conta 16 como pagamento definitivo.
#
# Eram exatamente os dois defeitos da versão anterior daqui, que fazia
# COUNT(DHBAIXA <= DTVENC) sobre os títulos quitados em 12 meses:
#   - cheque que entrou na conta 16 tem DHBAIXA preenchida e contava como pago
#     em dia — sendo que é justamente o cheque pendente que a régua persegue;
#   - título velho pago com atraso e depois renegociado saía da conta.
# O número que mostrávamos era otimista, e diferente do que a gerência vê no BI
# para o mesmo cliente. Dois números para a mesma coisa acabam com a confiança
# nos dois.
#
# O QUE ESSE PERCENTUAL NÃO É (medido no banco em 2026-08-10):
# ele NÃO é a proporção de títulos pagos no prazo. A LOPES E QUINTINO (11538)
# pagou 452 dos 497 títulos COM ATRASO — 9% por contagem — e tem
# PCT_PAGO_EM_DIA = 99, porque o atraso médio dela é de 1,75 dia. O número
# acompanha o ATRASO_MEDIO_DIAS, não a contagem. É um indicador de análise de
# crédito: tolera alguns dias de atraso e pergunta "esse cliente paga?".
# Por isso ATRASO_MEDIO_DIAS vai junto para a tela: "99%" sozinho seria lido
# como "sempre paga em dia", que não é o que o dado diz.
#
# CUIDADO COM O ZERO. A tabela cobre 15.469 clientes e NENHUM tem
# PCT_PAGO_EM_DIA nulo: 14.390 estão zerados, e 14.336 desses não têm nenhum
# título pago nem em atraso — são cadastros sem movimento, não maus pagadores.
# Mas há zero que é VERDADE: a FARMACIA (11107) tem 0 pago, 2 em atraso e 573
# dias de atraso médio. Esconder esse zero apagaria o pior pagador da lista.
# Daí a régua ser "não há base NENHUMA" (pagos = 0 E atraso = 0), e não
# "pagos = 0".
#
# DH_PROCESSAMENTO vai junto porque o valor é MATERIALIZADO por uma procedure
# e NÃO é reprocessado todo dia para todo mundo: as linhas vão de 27/05 a 10/08
# (11 datas distintas). Quem está com o cliente na linha precisa saber de quando
# é o número.
# ---------------------------------------------------------------------------

SQL_CLIENTE = """
SELECT
    PAR.CODPARC,
    PAR.NOMEPARC,
    PAR.RAZAOSOCIAL,
    PAR.CGC_CPF,
    PAR.TELEFONE,
    PAR.EMAIL,
    NVL(PAR.LIMCRED, 0) AS LIMCRED,
    PAR.ATIVO,
    CID.NOMECID,
    UFS.UF,
    NVL(VEN.APELIDO, 'SEM VENDEDOR') AS VENDEDOR,
    -- Pontualidade: ver o bloco de comentário acima do SQL_CLIENTE.
    ANL.PCT_PAGO_EM_DIA,
    ANL.QTD_TIT_PAGOS_12M,
    ANL.QTD_TIT_ATRASO_12M,
    ANL.DH_PROCESSAMENTO,
    ANL.ATRASO_MEDIO_DIAS
FROM TGFPAR PAR
    LEFT JOIN TSICID CID ON CID.CODCID  = PAR.CODCID
    LEFT JOIN TSIUFS UFS ON UFS.CODUF   = CID.UF
    LEFT JOIN TGFVEN VEN ON VEN.CODVEND = PAR.CODVEND
    LEFT JOIN AD_LIMCREDANALISE ANL ON ANL.CODPARC       = PAR.CODPARC
                                   AND ANL.VERSAO_MODELO = 'V1'
WHERE PAR.CODPARC = :CODPARC
"""

# Extrato da 360°: títulos em aberto do cliente, VENCIDOS e A VENCER.
# Não-cheques: sem baixa (independente do vencimento). Cheques: mesma regra da
# consulta de títulos (CHEQUES_REGRA) — pendentes, em aberto e devolvidos.
SELECT_EXTRATO = f"""
SELECT
    FIN.NUFIN,
    FIN.NUMNOTA,
    FIN.NUNOTA,
    FIN.DESDOBRAMENTO,
    FIN.DTNEG,
    {DT_EFETIVA} AS DT_VENCIMENTO,
    FIN.VLRDESDOB,
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.VLRCHEQUE_REGRA ELSE FIN.VLRCHEQUE END AS VLR_CHEQUE,
    VFIN.VLRLIQUIDO,
    NVL(FIN.VLRJURO, 0),
    NVL(FIN.VLRDESC, 0),
    FIN.CODTIPTIT,
    TIT.DESCRTIPTIT,
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.CHEQUE END AS NUMERO_CHEQUE,
    CASE WHEN FIN.CODTIPTIT = 3 THEN CHR.ULTIMO_EVENTO_REGRA END AS ULTIMO_EVENTO,
    FIN.HISTORICO,
    GREATEST(TRUNC(SYSDATE) - TRUNC({DT_EFETIVA}), 0) AS ATRASO_DIAS,
    CASE
        WHEN TRUNC({DT_EFETIVA}) < TRUNC(SYSDATE) THEN 'VENCIDO'
        ELSE 'A_VENCER'
    END AS SITUACAO,
    TOP.DESCROPER,
    FIN.NURENEG
{JOINS_TITULO}
WHERE FIN.CODPARC = :CODPARC
  AND FIN.RECDESP = 1
  AND NVL(FIN.PROVISAO, 'N') = 'N'
  AND (
        (FIN.CODTIPTIT IN (2, 4, 5, 39) AND FIN.DHBAIXA IS NULL)
        OR
        (FIN.CODTIPTIT = 3 AND CHR.NUFIN IS NOT NULL)
        OR
        /* Título ativo gerado por renegociação (PIX, cartão...). Sem o corte de
           vencimento: aqui a 360° também mostra o que ainda está por vencer. */
        (
            FIN.CODTIPTIT NOT IN (2, 3, 4, 5, 39)
            AND FIN.NURENEG IS NOT NULL
            AND FIN.DHBAIXA IS NULL
        )
      )
ORDER BY {DT_EFETIVA}, FIN.NUFIN
"""


@bp.route("/api/cobranca/cliente", methods=["POST"])
def cliente():
    """Identificação + KPIs do cliente para o topo da Visão 360°."""
    data = request.get_json() or {}
    cod_parc = data.get("codParc")
    if not cod_parc:
        return jsonify({"erro": "Parâmetro 'codParc' é obrigatório."}), 400

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()

        cursor.execute(SQL_CLIENTE, {"CODPARC": cod_parc})
        row = cursor.fetchone()
        if not row:
            return jsonify({"erro": f"Cliente {cod_parc} não encontrado."}), 404

        return jsonify(
            {
                "sucesso": True,
                "dados": {
                    "codParc": row[0],
                    "nomeParc": _txt(row[1]),
                    "razaoSocial": _txt(row[2]),
                    "cgcCpf": _txt(row[3]),
                    "telefone": _txt(row[4]),
                    "email": _txt(row[5]),
                    "limiteCredito": float(row[6]) if row[6] is not None else 0.0,
                    "ativo": row[7],
                    "nomeCid": _txt(row[8]),
                    "uf": _txt(row[9]),
                    "vendedor": _txt(row[10]),
                    # Cálculo do próprio Sankhya (AD_LIMCREDANALISE). null só
                    # quando não há base nenhuma — nem título pago, nem em atraso.
                    # Ver o bloco de comentário do SQL_CLIENTE: há zero que é fato.
                    "pontualidade": round(float(row[11]), 1)
                    if row[11] is not None
                    and (int(row[12] or 0) > 0 or int(row[13] or 0) > 0)
                    else None,
                    "titulosPagos12m": int(row[12]) if row[12] is not None else None,
                    "titulosAtraso12m": int(row[13]) if row[13] is not None else None,
                    "atrasoMedioDias": round(float(row[15]), 1)
                    if row[15] is not None
                    else None,
                    "pontualidadeAtualizadaEm": row[14].strftime("%Y-%m-%d")
                    if row[14]
                    else None,
                    "pontualidadeFonte": "SANKHYA_LIMCREDANALISE",
                },
            }
        )

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/extrato", methods=["POST"])
def extrato():
    """Extrato unificado: títulos em aberto do cliente (vencidos e a vencer)."""
    data = request.get_json() or {}
    cod_parc = data.get("codParc")
    if not cod_parc:
        return jsonify({"erro": "Parâmetro 'codParc' é obrigatório."}), 400

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(CTE_CHEQUES + SELECT_EXTRATO, {"CODPARC": cod_parc})
        linhas = cursor.fetchall()

        # Marcador de "cliente informou pagamento", anexado à linha em vez de
        # consultado ao desenhar a célula: assim filtro, contagem e ordenação da
        # tabela funcionam de graça (mesmo padrão do _cobranca em Títulos
        # Vencidos). Consulta separada para não tocar na SELECT_EXTRATO.
        pagtos = _pagtos_informados(cursor, cod_parc)

        dados = []
        for r in linhas:
            dados.append(
                {
                    "nuFin": r[0],
                    "numNota": r[1],
                    "nuNota": r[2],
                    "desdobramento": r[3],
                    "dtNeg": r[4].strftime("%Y-%m-%d") if r[4] else None,
                    "dtVenc": r[5].strftime("%Y-%m-%d") if r[5] else None,
                    "vlrDesdob": float(r[6]) if r[6] is not None else None,
                    "vlrCheque": float(r[7]) if r[7] is not None else None,
                    "vlrLiquido": float(r[8]) if r[8] is not None else None,
                    "vlrJuros": float(r[9]) if r[9] is not None else 0.0,
                    "vlrDesconto": float(r[10]) if r[10] is not None else 0.0,
                    "codTipTit": r[11],
                    "tipoTitulo": r[12],
                    "numeroCheque": r[13],
                    "ultimoEvento": r[14],
                    "historico": r[15],
                    "atrasoDias": int(r[16]) if r[16] is not None else 0,
                    "situacao": r[17],
                    "operacao": _txt(r[18]),
                    "nuReneg": r[19],
                    "pagamentoInformado": pagtos.get(int(r[0])) if r[0] is not None else None,
                }
            )

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


# ===========================================================================
# Operador / autenticação
#
# A cobrança grava ações auditáveis ("quem ligou", "quem mandou pro jurídico").
# Por isso o operador é autenticado de verdade, não só declarado.
#
# A senha NÃO é conferida no Oracle: o hash da TSIUSU é proprietário do Sankhya
# e reproduzi-lo aqui seria frágil. Quem valida a senha é o próprio Sankhya,
# pelo serviço MobileLoginSP.login, chamado via Gateway (mesmo caminho de
# impostos._salvar_dataset). Validada a senha, o CODUSU é resolvido na TSIUSU
# pelo nome de usuário.
#
# A confirmar contra a instância (Om 4.35): (a) o Gateway permite chamar
# MobileLoginSP.login com o token de aplicação; (b) o serviço aceita a senha em
# texto puro no campo INTERNO (versões antigas podiam exigir hash). Se algum
# desses pontos falhar, a alternativa é chamar o mge on-premise direto
# (http://<host>:<porta>/mge/service.sbr) — trocar só o _servico_sankhya.
# ===========================================================================


# ---------------------------------------------------------------------------
# Sessão do operador
#
# Validar a senha no login não bastava: o CODUSU seguia viajando no CORPO das
# requisições de escrita, então qualquer um na rede podia registrar chamada em
# nome de outra pessoa. Como essa trilha justifica negativação — que tem efeito
# jurídico para o cliente —, "quem ligou" precisa ser provado, não declarado.
#
# O token é assinado (HMAC-SHA256), não guardado: não há tabela de sessão nem
# dicionário em memória para sincronizar entre workers. Ele carrega o CODUSU e
# a expiração, e a assinatura impede que sejam alterados.
# ---------------------------------------------------------------------------

_SESSAO_HORAS = 12  # um turno de trabalho: entra uma vez por dia

# Sem COBRANCA_SECRET no ambiente cada processo gera o seu — funciona, mas todo
# mundo é deslogado a cada restart do container. Defina no .env do servidor.
_SEGREDO_VOLATIL = secrets.token_bytes(32)


def _segredo():
    do_ambiente = os.environ.get("COBRANCA_SECRET")
    return do_ambiente.encode() if do_ambiente else _SEGREDO_VOLATIL


def _b64(dados):
    return base64.urlsafe_b64encode(dados).rstrip(b"=").decode()


def _de_b64(texto):
    # Repõe o padding que tiramos na hora de gerar.
    return base64.urlsafe_b64decode(texto + "=" * (-len(texto) % 4))


def _emitir_token(cod_usu, nome_usu):
    corpo = {
        "codUsu": cod_usu,
        "nomeUsu": nome_usu,
        "exp": int(time.time()) + _SESSAO_HORAS * 3600,
    }
    dados = _b64(json.dumps(corpo, separators=(",", ":")).encode())
    assinatura = _b64(hmac.new(_segredo(), dados.encode(), hashlib.sha256).digest())
    return f"{dados}.{assinatura}"


def _ler_token(token):
    """Devolve o conteúdo do token, ou None se for inválido/adulterado/vencido."""
    if not token or "." not in token:
        return None
    dados, _, assinatura = token.partition(".")
    esperada = _b64(hmac.new(_segredo(), dados.encode(), hashlib.sha256).digest())
    # compare_digest em vez de == : comparação de tempo constante.
    if not hmac.compare_digest(esperada, assinatura):
        return None
    try:
        corpo = json.loads(_de_b64(dados))
    except (ValueError, json.JSONDecodeError):
        return None
    if float(corpo.get("exp") or 0) < time.time():
        return None
    return corpo


def _exige_operador(f):
    """Só passa com sessão válida; publica o operador em `request.operador`."""

    @wraps(f)
    def interno(*args, **kwargs):
        cabecalho = request.headers.get("Authorization") or ""
        if cabecalho[:7].lower() == "bearer ":
            token = cabecalho[7:].strip()
        else:
            # navigator.sendBeacon não manda cabeçalho — é assim que o app
            # cancela a chamada quando o operador fecha a aba no meio dela.
            token = request.args.get("token") or ""
        operador = _ler_token(token)
        if not operador:
            return jsonify({"erro": "Sessão expirada ou inválida. Entre de novo."}), 401
        request.operador = operador
        return f(*args, **kwargs)

    return interno


def _servico_sankhya(service_name, request_body):
    """Chama um serviço do Sankhya via Gateway e devolve o envelope JSON cru.

    Não valida o status do envelope — quem chama decide (o login trata status
    "0" como credencial inválida, e não como erro de servidor).
    """
    token = autenticar_sankhya()
    resp = requests.post(
        f"{_api_base()}/gateway/v1/mge/service.sbr",
        # serviceName + outputType=json vão na query string, senão o service.sbr
        # responde XML e o resp.json() estoura (mesma pegadinha do impostos.py).
        params={"serviceName": service_name, "outputType": "json"},
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
        },
        json={"serviceName": service_name, "requestBody": request_body},
        timeout=_TIMEOUT,
    )
    if resp.status_code != 200:
        raise RuntimeError(f"{service_name} HTTP {resp.status_code}: {resp.text}")
    try:
        return resp.json()
    except ValueError:
        raise RuntimeError(
            f"{service_name} retornou corpo não-JSON: {resp.text[:500]}"
        )


@bp.route("/api/cobranca/login", methods=["POST"])
def login():
    """Valida usuário + senha do Sankhya e devolve o operador.

    Body: { "usuario": "<NOMEUSU>", "senha": "<senha>" }
    200:  { "sucesso": true, "codUsu": <int>, "nomeUsu": "<...>", "token": "<...>" }
    401:  credencial inválida.

    O token vale 12 h e é o que autoriza as rotas de escrita da régua.
    """
    data = request.get_json(silent=True) or {}
    usuario = (data.get("usuario") or "").strip()
    senha = data.get("senha") or ""
    if not usuario or not senha:
        return jsonify({"erro": "Parâmetros 'usuario' e 'senha' são obrigatórios."}), 400

    # 1) O Sankhya valida a senha.
    try:
        envelope = _servico_sankhya(
            "MobileLoginSP.login",
            {
                "NOMUSU": {"$": usuario},
                "INTERNO": {"$": senha},
                "KEEPCONNECTED": {"$": "false"},
            },
        )
    except requests.RequestException as err:
        return jsonify({"erro": f"Falha de comunicação com o Sankhya: {err}"}), 502
    except RuntimeError as err:
        return _erro(err)

    if str(envelope.get("status")) != "1":
        # status "0" = login recusado (senha errada, usuário bloqueado, etc.).
        # O statusMessage do Sankhya vem percent-encoded.
        msg = unquote(envelope.get("statusMessage") or "") or "Usuário ou senha inválidos."
        return jsonify({"erro": msg}), 401

    # 2) Resolve o CODUSU pelo nome (a senha já foi validada pelo Sankhya).
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(
            """
            SELECT CODUSU, NOMEUSU
            FROM TSIUSU
            WHERE UPPER(NOMEUSU) = UPPER(:NOMUSU)
            """,
            {"NOMUSU": usuario},
        )
        row = cursor.fetchone()
        if not row:
            # Sankhya validou mas não achamos o CODUSU: não deveria acontecer.
            return (
                jsonify({"erro": f"Usuário '{usuario}' validado, mas sem CODUSU na TSIUSU."}),
                500,
            )
        cod_usu, nome_usu = int(row[0]), _txt(row[1])
        return jsonify(
            {
                "sucesso": True,
                "codUsu": cod_usu,
                "nomeUsu": nome_usu,
                "token": _emitir_token(cod_usu, nome_usu),
                "expiraEmHoras": _SESSAO_HORAS,
            }
        )

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/operadores", methods=["GET"])
def operadores():
    """Lista de usuários — para resolver o NOME do operador nas telas de histórico.

    Sem filtro de status: um CODUSU antigo (de usuário já desativado) ainda
    precisa ser resolvido para exibir "quem ligou" numa chamada antiga.
    """
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(
            """
            SELECT CODUSU, NOMEUSU
            FROM TSIUSU
            ORDER BY NOMEUSU
            """
        )
        dados = [{"codUsu": int(r[0]), "nomeUsu": _txt(r[1])} for r in cursor.fetchall()]
        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


# ===========================================================================
# RÉGUA DE CHAMADAS — primeira ESCRITA do módulo de cobrança
#
# Tabelas (criadas no Sankhya pelo Construtor de Telas):
#   AD_COBRCHAMADA      cabeçalho da chamada (cliente, sentido, situação, trava)
#   AD_COBRCHAMADAITEM  títulos da chamada — a RÉGUA POR TÍTULO vive aqui (ORDEM)
#   AD_COBRANEXO        anexos (só o link do drive; não guardamos arquivo)
#
# PK: as três tabelas usam SEQUENCES DEDICADAS (SEQ_AD_COBRCHAMADA,
# SEQ_AD_COBRCHAMADAITEM, SEQ_AD_COBRANEXO) + RETURNING. NÃO usar o padrão
# TGFNUM daqui: o "autoincremento" que se marca no Sankhya só age em INSERTs
# feitos pela camada dele (DynaForm/DatasetSP) e a TGFNUM não tem registro
# dessas tabelas — gravando direto no Oracle, o PK viria nulo.
#
# Regras que moram AQUI (nunca no React):
#   - Régua do título = nº de itens de chamadas PROATIVA + FINALIZADA daquele
#     NUFIN. Chamada RECEPTIVA entra no histórico mas NÃO incrementa a ORDEM.
#   - Trava "em chamada" = existe item cuja chamada está EM_ANDAMENTO e
#     DHEXPIRA > agora. É derivada (sem campo em TGFFIN) e expira sozinha:
#     toda consulta de trava filtra por DHEXPIRA, então modal abandonado libera.
#   - Obrigatoriedade de campo: o pessoal criou as colunas quase todas
#     NULLABLE, então quem impõe o preenchimento é esta API.
# ===========================================================================

# Duração da trava do título enquanto o modal está aberto.
_TRAVA_MINUTOS = 15
# Teto de títulos por chamada — evita que um clique errado ("selecionar tudo")
# trave a carteira inteira do cliente.
_MAX_TITULOS_CHAMADA = 200

_SENTIDOS = ("PROATIVA", "RECEPTIVA")
_STATUS_CHAMADA = ("ATENDEU", "CAIXA_POSTAL", "RECUSOU", "AGENDOU", "INFORMOU_PAGTO")
_DESFECHOS = ("ACORDO", "SEM_ACORDO", "EM_ABERTO", "PAGAMENTO_INFORMADO")

# Travas ativas. Sem filtro de título: quem chama acrescenta o IN quando precisa.
SQL_TRAVAS = """
    SELECT i.NUFIN, c.CODCHAMADA, c.CODPARC, c.CODUSU, u.NOMEUSU,
           c.DHINICIO, c.DHEXPIRA
    FROM AD_COBRCHAMADAITEM i
    JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = i.CODCHAMADA
    LEFT JOIN TSIUSU u ON u.CODUSU = c.CODUSU
    WHERE c.SITUACAO = 'EM_ANDAMENTO'
      AND c.DHEXPIRA > SYSDATE
"""

# ---------------------------------------------------------------------------
# Pagamento informado pelo cliente (docs/PAGAMENTO-INFORMADO.md)
#
# É "o cliente disse que pagou", NUNCA "pago". A baixa é do financeiro, sai no
# Sankhya depois, e é ela que faz o título deixar a carteira. Medido em 15/08:
# de ~57 títulos que a operadora registrou como pagos, só 1 tinha baixa — a
# janela entre pagar e sumir da tela é de vários dias, e é ela que faz alguém
# ligar de novo para quem já pagou.
#
# Sem tabela nova: o registro é uma chamada RECEPTIVA já FINALIZADA (o cliente
# de fato entrou em contato) e o marcador vive no DESFECHO do título. Receptiva
# não conta na régua, então marcar pagamento nunca empurra ninguém ao jurídico.
# ---------------------------------------------------------------------------

# Sem filtro de SENTIDO de propósito: vale tanto o registro rápido (receptiva)
# quanto o desfecho marcado durante uma ligação normal. NÃO reaproveita a CTE
# REGUA, que é PROATIVA-only por definição — misturar as duas coisas quebraria
# a régua para ganhar um badge.
SQL_PAGTO_INFORMADO = """
    SELECT i.NUFIN,
           MAX(c.DHFIM) AS DHINFORMADO,
           MAX(c.CODUSU) KEEP (DENSE_RANK LAST ORDER BY c.DHFIM) AS CODUSU,
           MAX(u.NOMEUSU) KEEP (DENSE_RANK LAST ORDER BY c.DHFIM) AS NOMEUSU
    FROM AD_COBRCHAMADAITEM i
    JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = i.CODCHAMADA
    LEFT JOIN TSIUSU u ON u.CODUSU = c.CODUSU
    WHERE i.DESFECHO = 'PAGAMENTO_INFORMADO'
      AND c.SITUACAO = 'FINALIZADA'
      {filtro_parc}
    GROUP BY i.NUFIN
"""


def _pagtos_informados(cursor, cod_parc=None):
    """Índice {nufin: {...}} dos títulos com pagamento informado.

    Consulta à parte, e não JOIN na consulta de títulos: a de extrato/carteira é
    grande e delicada (CTEs de cheque), e marcador é dado acessório. Mesmo
    raciocínio do /locks — são poucas linhas, cruzar em Python sai mais barato
    que carregar a consulta principal.

    Sem cod_parc devolve TODOS os marcadores, para a tela de Títulos Vencidos.
    """
    binds = {}
    filtro = ""
    if cod_parc is not None:
        filtro = "AND c.CODPARC = :CODPARC"
        binds["CODPARC"] = cod_parc
    cursor.execute(SQL_PAGTO_INFORMADO.format(filtro_parc=filtro), binds)
    return {
        int(r[0]): {
            "dhInformado": _dh(r[1]),
            "codUsu": int(r[2]) if r[2] is not None else None,
            "nomeUsu": _txt(r[3]),
        }
        for r in cursor.fetchall()
        if r[0] is not None
    }


class _Invalido(Exception):
    """Payload recusado — vira 400. Não é erro de servidor."""


def _obrig_int(dados, campo):
    valor = dados.get(campo)
    if valor is None or valor == "":
        raise _Invalido(f"Parâmetro '{campo}' é obrigatório.")
    try:
        return int(valor)
    except (TypeError, ValueError):
        raise _Invalido(f"Parâmetro '{campo}' deve ser um número inteiro.")


def _obrig_dominio(dados, campo, valores):
    valor = str(dados.get(campo) or "").strip().upper()
    if valor not in valores:
        raise _Invalido(f"Parâmetro '{campo}' deve ser um de: {', '.join(valores)}.")
    return valor


def _lista_nufins(dados, campo="nufins"):
    bruto = dados.get(campo)
    if not isinstance(bruto, (list, tuple)) or not bruto:
        raise _Invalido(f"'{campo}' deve ser uma lista com ao menos um título.")
    nufins = []
    for item in bruto:
        try:
            nufin = int(item)
        except (TypeError, ValueError):
            raise _Invalido(f"'{campo}' contém um valor não numérico: {item!r}.")
        if nufin not in nufins:  # duplicado no payload não vira item duplicado
            nufins.append(nufin)
    if len(nufins) > _MAX_TITULOS_CHAMADA:
        raise _Invalido(
            f"Uma chamada aceita no máximo {_MAX_TITULOS_CHAMADA} títulos "
            f"(recebidos {len(nufins)})."
        )
    return nufins


def _parse_dh(valor, campo):
    """Aceita 'YYYY-MM-DD HH:MM[:SS]', o ISO com 'T' do <input datetime-local>
    e só a data (vira meia-noite)."""
    if valor in (None, ""):
        return None
    texto = str(valor).strip().replace("T", " ")
    for formato in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%d"):
        try:
            return datetime.strptime(texto, formato)
        except ValueError:
            continue
    raise _Invalido(f"'{campo}' deve estar no formato YYYY-MM-DD HH:MM.")


def _dh(valor):
    return valor.strftime("%Y-%m-%d %H:%M:%S") if valor else None


def _binds_lista(prefixo, valores):
    """Placeholders de um IN (...) + o dict de binds (cx_Oracle não aceita lista)."""
    nomes = [f"{prefixo}{i}" for i in range(len(valores))]
    return ", ".join(f":{n}" for n in nomes), dict(zip(nomes, valores))


def _novo_id(cursor, sql, binds):
    """INSERT com RETURNING <pk> INTO :ID — devolve o PK gerado pela sequence."""
    var = cursor.var(cx_Oracle.NUMBER)
    cursor.execute(sql, dict(binds, ID=var))
    valor = var.getvalue()
    if isinstance(valor, list):  # cx_Oracle 8 devolve lista no DML returning
        valor = valor[0]
    return int(valor)


def _texto_lob(valor):
    """AD_COBRANEXO.URL é CLOB: a leitura devolve um LOB, não uma string."""
    if valor is not None and hasattr(valor, "read"):
        valor = valor.read()
    return _txt(valor)


def _linha_trava(r):
    return {
        "nufin": int(r[0]),
        "codChamada": int(r[1]),
        "codParc": int(r[2]) if r[2] is not None else None,
        "codUsu": int(r[3]) if r[3] is not None else None,
        "nomeUsu": _txt(r[4]),
        "desde": _dh(r[5]),
        "expiraEm": _dh(r[6]),
    }


def _erro_oracle(err):
    """ORA-00054 (espera de lock esgotada) e ORA-00060 (deadlock) não são falha
    de servidor: são dois operadores disputando o mesmo título. Viram 409."""
    codigo = None
    if err.args and hasattr(err.args[0], "code"):
        codigo = err.args[0].code
    if codigo in (54, 60):
        return (
            jsonify(
                {
                    "erro": "Outro operador está registrando chamada nestes títulos "
                    "neste instante. Tente novamente."
                }
            ),
            409,
        )
    return _erro(f"Erro de Banco de Dados: {err}")


@bp.route("/api/cobranca/chamadas/iniciar", methods=["POST"])
@_exige_operador
def chamada_iniciar():
    """Abre a chamada e ADQUIRE A TRAVA dos títulos.

    Body: { codParc, nufins: [..], sentido: PROATIVA|RECEPTIVA }
    201:  { codChamada, dhInicio, dhExpira, nufins }
    409:  { nufinsTravados: [{nufin, nomeUsu, desde, ...}] }

    O operador vem da sessão, nunca do corpo: é ele que fica gravado como
    "quem ligou".
    """
    data = request.get_json(silent=True) or {}
    cod_usu = request.operador["codUsu"]
    try:
        cod_parc = _obrig_int(data, "codParc")
        sentido = _obrig_dominio(data, "sentido", _SENTIDOS)
        nufins = _lista_nufins(data)
    except _Invalido as err:
        return jsonify({"erro": str(err)}), 400

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        placeholders, binds = _binds_lista("N", nufins)

        # 1) Serializa a disputa travando as linhas dos títulos em TGFFIN.
        #    Sem isso, dois operadores que clicam no mesmo instante passariam os
        #    dois pelo teste do passo 2 (nenhum enxerga o INSERT não commitado do
        #    outro) e o título ficaria travado em duplicidade. O lock dura o
        #    tempo dos INSERTs; WAIT 5 impede ficarmos pendurados numa transação
        #    longa do próprio Sankhya. De quebra, valida a existência do título.
        cursor.execute(
            f"""
            SELECT NUFIN, CODPARC
            FROM TGFFIN
            WHERE NUFIN IN ({placeholders})
            ORDER BY NUFIN
            FOR UPDATE WAIT 5
            """,
            binds,
        )
        achados = {
            int(r[0]): (int(r[1]) if r[1] is not None else None)
            for r in cursor.fetchall()
        }

        faltando = [n for n in nufins if n not in achados]
        if faltando:
            conexao.rollback()
            return jsonify({"erro": f"Títulos inexistentes: {faltando}"}), 404

        de_outro = [n for n in nufins if achados[n] != cod_parc]
        if de_outro:
            conexao.rollback()
            return (
                jsonify(
                    {
                        "erro": f"Títulos {de_outro} não pertencem ao cliente {cod_parc}.",
                        "nufinsInvalidos": de_outro,
                    }
                ),
                400,
            )

        # 2) Nenhum dos títulos pode estar em chamada agora.
        cursor.execute(SQL_TRAVAS + f" AND i.NUFIN IN ({placeholders})", binds)
        travados = [_linha_trava(r) for r in cursor.fetchall()]
        if travados:
            conexao.rollback()
            quem = travados[0].get("nomeUsu") or f"usuário {travados[0].get('codUsu')}"
            return (
                jsonify(
                    {
                        "erro": f"Título já está em chamada por {quem}.",
                        "nufinsTravados": travados,
                    }
                ),
                409,
            )

        # 3) Cabeçalho + itens. A chamada nasce EM_ANDAMENTO (rascunho): STATUS,
        #    RESUMO e DESFECHO só chegam na finalização.
        cod_chamada = _novo_id(
            cursor,
            """
            INSERT INTO AD_COBRCHAMADA
                (CODCHAMADA, CODPARC, SENTIDO, SITUACAO, DHINICIO, DHEXPIRA, CODUSU)
            VALUES
                (SEQ_AD_COBRCHAMADA.NEXTVAL, :CODPARC, :SENTIDO, 'EM_ANDAMENTO',
                 SYSDATE, SYSDATE + :MINUTOS / 1440, :CODUSU)
            RETURNING CODCHAMADA INTO :ID
            """,
            {
                "CODPARC": cod_parc,
                "SENTIDO": sentido,
                "MINUTOS": _TRAVA_MINUTOS,
                "CODUSU": cod_usu,
            },
        )

        for nufin in nufins:
            cursor.execute(
                """
                INSERT INTO AD_COBRCHAMADAITEM (CODITEM, CODCHAMADA, NUFIN)
                VALUES (SEQ_AD_COBRCHAMADAITEM.NEXTVAL, :CODCHAMADA, :NUFIN)
                """,
                {"CODCHAMADA": cod_chamada, "NUFIN": nufin},
            )

        # Lê as datas do banco (SYSDATE) em vez de usar a hora do container: o
        # front compara a expiração com as travas que vêm do mesmo relógio.
        cursor.execute(
            "SELECT DHINICIO, DHEXPIRA FROM AD_COBRCHAMADA WHERE CODCHAMADA = :ID",
            {"ID": cod_chamada},
        )
        dh_inicio, dh_expira = cursor.fetchone()

        conexao.commit()
        return (
            jsonify(
                {
                    "sucesso": True,
                    "codChamada": cod_chamada,
                    "codParc": cod_parc,
                    "sentido": sentido,
                    "dhInicio": _dh(dh_inicio),
                    "dhExpira": _dh(dh_expira),
                    "nufins": nufins,
                }
            ),
            201,
        )

    except cx_Oracle.Error as err:
        if conexao:
            conexao.rollback()
        return _erro_oracle(err)
    except Exception as e:
        if conexao:
            conexao.rollback()
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/chamadas/<int:cod_chamada>/finalizar", methods=["PUT"])
@_exige_operador
def chamada_finalizar(cod_chamada):
    """Fecha a chamada, grava o desfecho por título e CALCULA A RÉGUA.

    Body: { status, resumo?, dhAgenda?, itens: [{nufin, desfecho}] }
    200:  { itens: [{nufin, ordem, desfecho}] }  (ordem = null em RECEPTIVA)
    """
    data = request.get_json(silent=True) or {}
    try:
        status = _obrig_dominio(data, "status", _STATUS_CHAMADA)
        resumo = (data.get("resumo") or "").strip() or None
        if resumo and len(resumo) > 4000:
            raise _Invalido("'resumo' excede 4000 caracteres.")
        dh_agenda = _parse_dh(data.get("dhAgenda"), "dhAgenda")
        if status == "AGENDOU" and not dh_agenda:
            raise _Invalido("Com status AGENDOU o campo 'dhAgenda' é obrigatório.")

        desfechos = {}
        for item in data.get("itens") or []:
            if not isinstance(item, dict):
                raise _Invalido("'itens' deve ser uma lista de {nufin, desfecho}.")
            nufin = _obrig_int(item, "nufin")
            desfecho = str(item.get("desfecho") or "").strip().upper() or None
            if desfecho and desfecho not in _DESFECHOS:
                raise _Invalido(
                    f"'desfecho' deve ser um de: {', '.join(_DESFECHOS)}."
                )
            desfechos[nufin] = desfecho
    except _Invalido as err:
        return jsonify({"erro": str(err)}), 400

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()

        # FOR UPDATE no cabeçalho: dois "salvar" simultâneos não contam a régua
        # em duplicidade (o segundo encontra a chamada já FINALIZADA).
        cursor.execute(
            "SELECT SENTIDO, SITUACAO FROM AD_COBRCHAMADA WHERE CODCHAMADA = :ID FOR UPDATE",
            {"ID": cod_chamada},
        )
        row = cursor.fetchone()
        if not row:
            conexao.rollback()
            return jsonify({"erro": f"Chamada {cod_chamada} não encontrada."}), 404

        sentido, situacao = _txt(row[0]), _txt(row[1])
        if situacao != "EM_ANDAMENTO":
            conexao.rollback()
            return (
                jsonify({"erro": f"Chamada {cod_chamada} já está {situacao}."}),
                409,
            )
        # Trava expirada NÃO impede finalizar: a expiração serve para liberar o
        # título para outros, não para descartar o que o operador digitou.

        cursor.execute(
            "SELECT CODITEM, NUFIN FROM AD_COBRCHAMADAITEM WHERE CODCHAMADA = :ID ORDER BY CODITEM",
            {"ID": cod_chamada},
        )
        itens = [(int(r[0]), int(r[1])) for r in cursor.fetchall()]
        if not itens:
            conexao.rollback()
            return (
                jsonify({"erro": f"Chamada {cod_chamada} não tem títulos vinculados."}),
                409,
            )

        da_chamada = {nufin for _, nufin in itens}
        desconhecidos = [n for n in desfechos if n not in da_chamada]
        if desconhecidos:
            conexao.rollback()
            return (
                jsonify(
                    {
                        "erro": f"Títulos {desconhecidos} não fazem parte da chamada "
                        f"{cod_chamada}."
                    }
                ),
                400,
            )

        resultado = []
        for cod_item, nufin in itens:
            ordem = None
            if sentido == "PROATIVA":
                # Régua do título: quantas proativas finalizadas ele já teve + 1.
                # Gravada no item para a timeline não mudar retroativamente.
                cursor.execute(
                    """
                    SELECT COUNT(*)
                    FROM AD_COBRCHAMADAITEM i
                    JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = i.CODCHAMADA
                    WHERE i.NUFIN = :NUFIN
                      AND c.SENTIDO = 'PROATIVA'
                      AND c.SITUACAO = 'FINALIZADA'
                      AND c.CODCHAMADA <> :ID
                    """,
                    {"NUFIN": nufin, "ID": cod_chamada},
                )
                ordem = int(cursor.fetchone()[0]) + 1

            cursor.execute(
                """
                UPDATE AD_COBRCHAMADAITEM
                   SET ORDEM = :ORDEM, DESFECHO = :DESFECHO
                 WHERE CODITEM = :CODITEM
                """,
                {
                    "ORDEM": ordem,
                    "DESFECHO": desfechos.get(nufin),
                    "CODITEM": cod_item,
                },
            )
            resultado.append(
                {"nufin": nufin, "ordem": ordem, "desfecho": desfechos.get(nufin)}
            )

        cursor.execute(
            """
            UPDATE AD_COBRCHAMADA
               SET SITUACAO = 'FINALIZADA',
                   DHFIM = SYSDATE,
                   STATUS = :STATUS,
                   RESUMO = :RESUMO,
                   DHAGENDA = :DHAGENDA
             WHERE CODCHAMADA = :ID
            """,
            {
                "STATUS": status,
                "RESUMO": resumo,
                "DHAGENDA": dh_agenda,
                "ID": cod_chamada,
            },
        )

        conexao.commit()
        return jsonify(
            {
                "sucesso": True,
                "codChamada": cod_chamada,
                "sentido": sentido,
                "status": status,
                "itens": resultado,
            }
        )

    except cx_Oracle.Error as err:
        if conexao:
            conexao.rollback()
        return _erro_oracle(err)
    except Exception as e:
        if conexao:
            conexao.rollback()
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/chamadas/<int:cod_chamada>/cancelar", methods=["POST"])
@_exige_operador
def chamada_cancelar(cod_chamada):
    """Descarta a chamada e LIBERA A TRAVA (operador fechou o modal sem registrar)."""
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(
            "SELECT SITUACAO FROM AD_COBRCHAMADA WHERE CODCHAMADA = :ID FOR UPDATE",
            {"ID": cod_chamada},
        )
        row = cursor.fetchone()
        if not row:
            conexao.rollback()
            return jsonify({"erro": f"Chamada {cod_chamada} não encontrada."}), 404

        situacao = _txt(row[0])
        if situacao == "CANCELADA":
            # Idempotente: o front cancela no fechar do modal e de novo no
            # unload da aba; a segunda chamada não pode virar erro na tela.
            conexao.rollback()
            return jsonify({"sucesso": True, "codChamada": cod_chamada, "situacao": situacao})
        if situacao != "EM_ANDAMENTO":
            conexao.rollback()
            return (
                jsonify({"erro": f"Chamada {cod_chamada} já está {situacao}."}),
                409,
            )

        # DHFIM também no cancelamento: registra quando a trava foi liberada.
        cursor.execute(
            """
            UPDATE AD_COBRCHAMADA
               SET SITUACAO = 'CANCELADA', DHFIM = SYSDATE
             WHERE CODCHAMADA = :ID
            """,
            {"ID": cod_chamada},
        )
        conexao.commit()
        return jsonify({"sucesso": True, "codChamada": cod_chamada, "situacao": "CANCELADA"})

    except cx_Oracle.Error as err:
        if conexao:
            conexao.rollback()
        return _erro_oracle(err)
    except Exception as e:
        if conexao:
            conexao.rollback()
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/chamadas/<int:cod_chamada>/renovar", methods=["PUT"])
@_exige_operador
def chamada_renovar(cod_chamada):
    """Heartbeat do modal aberto: empurra a expiração da trava por mais 15 min.

    Se a trava já expirou e outro operador pegou algum título no intervalo,
    devolve 409 — renovar não pode roubar a trava de quem chegou depois.
    """
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(
            "SELECT SITUACAO FROM AD_COBRCHAMADA WHERE CODCHAMADA = :ID FOR UPDATE",
            {"ID": cod_chamada},
        )
        row = cursor.fetchone()
        if not row:
            conexao.rollback()
            return jsonify({"erro": f"Chamada {cod_chamada} não encontrada."}), 404
        if _txt(row[0]) != "EM_ANDAMENTO":
            conexao.rollback()
            return jsonify({"erro": f"Chamada {cod_chamada} já está {_txt(row[0])}."}), 409

        cursor.execute(
            "SELECT NUFIN FROM AD_COBRCHAMADAITEM WHERE CODCHAMADA = :ID",
            {"ID": cod_chamada},
        )
        nufins = [int(r[0]) for r in cursor.fetchall()]
        if nufins:
            placeholders, binds = _binds_lista("N", nufins)
            cursor.execute(
                SQL_TRAVAS
                + f" AND i.NUFIN IN ({placeholders}) AND c.CODCHAMADA <> :ID",
                dict(binds, ID=cod_chamada),
            )
            travados = [_linha_trava(r) for r in cursor.fetchall()]
            if travados:
                conexao.rollback()
                return (
                    jsonify(
                        {
                            "erro": "A trava expirou e outro operador assumiu estes títulos.",
                            "nufinsTravados": travados,
                        }
                    ),
                    409,
                )

        cursor.execute(
            """
            UPDATE AD_COBRCHAMADA
               SET DHEXPIRA = SYSDATE + :MINUTOS / 1440
             WHERE CODCHAMADA = :ID
            """,
            {"MINUTOS": _TRAVA_MINUTOS, "ID": cod_chamada},
        )
        cursor.execute(
            "SELECT DHEXPIRA FROM AD_COBRCHAMADA WHERE CODCHAMADA = :ID",
            {"ID": cod_chamada},
        )
        dh_expira = cursor.fetchone()[0]
        conexao.commit()
        return jsonify(
            {"sucesso": True, "codChamada": cod_chamada, "dhExpira": _dh(dh_expira)}
        )

    except cx_Oracle.Error as err:
        if conexao:
            conexao.rollback()
        return _erro_oracle(err)
    except Exception as e:
        if conexao:
            conexao.rollback()
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


def _gravar_anexo(cod_chamada, descricao, url, cod_usu):
    """Insere o anexo e devolve a resposta pronta (compartilhado pelas 2 rotas)."""
    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(
            "SELECT SITUACAO FROM AD_COBRCHAMADA WHERE CODCHAMADA = :ID",
            {"ID": cod_chamada},
        )
        row = cursor.fetchone()
        if not row:
            return jsonify({"erro": f"Chamada {cod_chamada} não encontrada."}), 404
        if _txt(row[0]) == "CANCELADA":
            return (
                jsonify({"erro": f"Chamada {cod_chamada} foi cancelada; não aceita anexo."}),
                409,
            )

        # URL é CLOB no banco; com cx_Oracle basta bindar a string.
        cod_anexo = _novo_id(
            cursor,
            """
            INSERT INTO AD_COBRANEXO
                (CODANEXO, CODCHAMADA, DESCRICAO, URL, DHANEXO, CODUSU)
            VALUES
                (SEQ_AD_COBRANEXO.NEXTVAL, :CODCHAMADA, :DESCRICAO, :URL,
                 SYSDATE, :CODUSU)
            RETURNING CODANEXO INTO :ID
            """,
            {
                "CODCHAMADA": cod_chamada,
                "DESCRICAO": descricao,
                "URL": url,
                "CODUSU": cod_usu,
            },
        )
        conexao.commit()
        return (
            jsonify(
                {
                    "sucesso": True,
                    "codAnexo": cod_anexo,
                    "codChamada": cod_chamada,
                    "descricao": descricao,
                    "url": url,
                }
            ),
            201,
        )

    except cx_Oracle.Error as err:
        if conexao:
            conexao.rollback()
        return _erro_oracle(err)
    except Exception as e:
        if conexao:
            conexao.rollback()
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/pagamento-informado", methods=["POST"])
@_exige_operador
def pagamento_informado():
    """Registra que o cliente INFORMOU o pagamento de um ou mais títulos.

    Body: { codParc, nufins: [..], obs? }
    201:  { codChamada, nufins, dhInformado }

    Grava uma chamada RECEPTIVA já FINALIZADA (o cliente entrou em contato) com
    STATUS='INFORMOU_PAGTO' e DESFECHO='PAGAMENTO_INFORMADO' nos títulos. O
    codChamada volta para o front pendurar o comprovante na rota de anexo que já
    existe — aqui o arquivo sobe DEPOIS, ao contrário do modal de chamada, porque
    a rota de anexo precisa de uma chamada existente. Como o comprovante é
    opcional, falha no upload não invalida o registro; quem tem de avisar é a
    tela.

    NÃO ADQUIRE TRAVA, de propósito: isto não é uma ligação. Travar criaria um
    "em chamada" falso e um 409 numa ação que precisa ser de dois cliques. Duas
    pessoas marcando o mesmo título é inofensivo — a leitura usa o registro mais
    recente (KEEP DENSE_RANK LAST em SQL_PAGTO_INFORMADO).
    """
    data = request.get_json(silent=True) or {}
    cod_usu = request.operador["codUsu"]
    try:
        cod_parc = _obrig_int(data, "codParc")
        nufins = _lista_nufins(data)
        obs = (data.get("obs") or "").strip() or None
        if obs and len(obs) > 4000:
            raise _Invalido("'obs' excede 4000 caracteres.")
    except _Invalido as err:
        return jsonify({"erro": str(err)}), 400

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        placeholders, binds = _binds_lista("N", nufins)

        # Sem FOR UPDATE: não há disputa a serializar, já que não há trava. A
        # consulta serve só para validar existência e dono do título.
        cursor.execute(
            f"SELECT NUFIN, CODPARC FROM TGFFIN WHERE NUFIN IN ({placeholders})",
            binds,
        )
        achados = {
            int(r[0]): (int(r[1]) if r[1] is not None else None)
            for r in cursor.fetchall()
        }

        faltando = [n for n in nufins if n not in achados]
        if faltando:
            conexao.rollback()
            return jsonify({"erro": f"Títulos inexistentes: {faltando}"}), 404

        de_outro = [n for n in nufins if achados[n] != cod_parc]
        if de_outro:
            conexao.rollback()
            return (
                jsonify(
                    {
                        "erro": f"Títulos {de_outro} não pertencem ao cliente {cod_parc}.",
                        "nufinsInvalidos": de_outro,
                    }
                ),
                400,
            )

        # Nasce FINALIZADA: não existe rascunho aqui, o registro é instantâneo.
        # DHEXPIRA = SYSDATE deixa a trava vencida ao nascer, por garantia — se
        # algum dia SQL_TRAVAS parar de filtrar por SITUACAO, isto ainda não
        # travaria o título.
        cod_chamada = _novo_id(
            cursor,
            """
            INSERT INTO AD_COBRCHAMADA
                (CODCHAMADA, CODPARC, SENTIDO, SITUACAO, DHINICIO, DHEXPIRA,
                 DHFIM, STATUS, RESUMO, CODUSU)
            VALUES
                (SEQ_AD_COBRCHAMADA.NEXTVAL, :CODPARC, 'RECEPTIVA', 'FINALIZADA',
                 SYSDATE, SYSDATE, SYSDATE, 'INFORMOU_PAGTO', :RESUMO, :CODUSU)
            RETURNING CODCHAMADA INTO :ID
            """,
            {"CODPARC": cod_parc, "RESUMO": obs, "CODUSU": cod_usu},
        )

        # ORDEM fica NULL: receptiva não anda na régua (mesma regra do
        # /finalizar). O marcador é o DESFECHO, não a posição.
        for nufin in nufins:
            cursor.execute(
                """
                INSERT INTO AD_COBRCHAMADAITEM
                    (CODITEM, CODCHAMADA, NUFIN, DESFECHO)
                VALUES
                    (SEQ_AD_COBRCHAMADAITEM.NEXTVAL, :CODCHAMADA, :NUFIN,
                     'PAGAMENTO_INFORMADO')
                """,
                {"CODCHAMADA": cod_chamada, "NUFIN": nufin},
            )

        cursor.execute(
            "SELECT DHFIM FROM AD_COBRCHAMADA WHERE CODCHAMADA = :ID",
            {"ID": cod_chamada},
        )
        (dh_fim,) = cursor.fetchone()

        conexao.commit()
        return (
            jsonify(
                {
                    "sucesso": True,
                    "codChamada": cod_chamada,
                    "codParc": cod_parc,
                    "nufins": nufins,
                    "dhInformado": _dh(dh_fim),
                }
            ),
            201,
        )

    except cx_Oracle.Error as err:
        if conexao:
            conexao.rollback()
        return _erro_oracle(err)
    except Exception as e:
        if conexao:
            conexao.rollback()
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/chamadas/<int:cod_chamada>/anexos", methods=["POST"])
@_exige_operador
def chamada_anexo(cod_chamada):
    """Anexa um LINK já existente à chamada (não sobe arquivo nenhum).

    Body: { url, descricao? }
    Para mandar um arquivo do computador, use /anexos/arquivo.
    """
    data = request.get_json(silent=True) or {}
    try:
        url = str(data.get("url") or "").strip()
        if not url:
            raise _Invalido("Parâmetro 'url' é obrigatório.")
        # O app abre esse link direto; aceitar 'javascript:' seria abrir a porta
        # para execução de script a partir de um campo de texto.
        if not url.lower().startswith(("http://", "https://")):
            raise _Invalido("'url' deve começar com http:// ou https://.")
        if len(url) > 2000:
            raise _Invalido("'url' excede 2000 caracteres.")
        descricao = (str(data.get("descricao") or "").strip())[:100] or None
    except _Invalido as err:
        return jsonify({"erro": str(err)}), 400

    return _gravar_anexo(cod_chamada, descricao, url, request.operador["codUsu"])


@bp.route("/api/cobranca/chamadas/<int:cod_chamada>/anexos/arquivo", methods=["POST"])
@_exige_operador
def chamada_anexo_arquivo(cod_chamada):
    """Sobe um ARQUIVO do computador do operador para o Drive da empresa.

    multipart/form-data: campo `arquivo` (obrigatório) e `descricao` (opcional).

    O arquivo não fica aqui: vai para o Drive e o que guardamos é o link. A
    ordem importa — sobe primeiro, grava depois. Se o INSERT falhasse antes do
    upload, sobraria uma linha apontando para nada; do jeito inverso, o pior
    caso é um arquivo órfão no Drive, que não quebra a tela de ninguém.
    """
    enviado = request.files.get("arquivo")
    if not enviado or not enviado.filename:
        return jsonify({"erro": "Envie o arquivo no campo 'arquivo'."}), 400

    conteudo = enviado.read()
    if not conteudo:
        return jsonify({"erro": "Arquivo vazio."}), 400
    if len(conteudo) > drive.LIMITE_BYTES:
        return (
            jsonify(
                {
                    "erro": f"Arquivo maior que o limite de "
                    f"{drive.LIMITE_BYTES // (1024 * 1024)} MB."
                }
            ),
            413,
        )

    nome = secure_filename(enviado.filename) or "anexo"
    descricao = (request.form.get("descricao") or "").strip()[:100] or nome[:100]

    try:
        # Prefixo com o número da chamada: quem abrir a pasta do Drive daqui a
        # seis meses consegue ligar o arquivo ao atendimento que o gerou.
        subido = drive.enviar_arquivo(
            f"chamada-{cod_chamada}-{nome}", enviado.mimetype, conteudo
        )
    except drive.DriveNaoConfigurado as err:
        return jsonify({"erro": str(err)}), 503
    except Exception as e:
        return _erro(f"Falha ao enviar o arquivo para o Drive: {e}", 502)

    return _gravar_anexo(cod_chamada, descricao, subido["url"], request.operador["codUsu"])


@bp.route("/api/cobranca/chamadas", methods=["GET"])
def chamadas():
    """Histórico de chamadas do cliente (cabeçalho + títulos + anexos).

    Query: ?codParc=<int>[&limite=<int>]
    """
    try:
        cod_parc = _obrig_int(request.args, "codParc")
        limite = int(request.args.get("limite") or 100)
    except (_Invalido, ValueError) as err:
        return jsonify({"erro": str(err)}), 400
    limite = max(1, min(limite, 500))

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        # ROWNUM em vez de FETCH FIRST: não depende da versão do Oracle.
        cursor.execute(
            """
            SELECT * FROM (
                SELECT c.CODCHAMADA, c.CODPARC, c.SENTIDO, c.SITUACAO, c.DHINICIO,
                       c.DHEXPIRA, c.DHFIM, c.STATUS, c.RESUMO, c.DHAGENDA,
                       c.CODUSU, u.NOMEUSU
                FROM AD_COBRCHAMADA c
                LEFT JOIN TSIUSU u ON u.CODUSU = c.CODUSU
                WHERE c.CODPARC = :CODPARC
                ORDER BY c.DHINICIO DESC, c.CODCHAMADA DESC
            ) WHERE ROWNUM <= :LIMITE
            """,
            {"CODPARC": cod_parc, "LIMITE": limite},
        )
        chamadas_por_id = {}
        dados = []
        for r in cursor.fetchall():
            registro = {
                "codChamada": int(r[0]),
                "codParc": int(r[1]) if r[1] is not None else None,
                "sentido": _txt(r[2]),
                "situacao": _txt(r[3]),
                "dhInicio": _dh(r[4]),
                "dhExpira": _dh(r[5]),
                "dhFim": _dh(r[6]),
                "status": _txt(r[7]),
                "resumo": _txt(r[8]),
                "dhAgenda": _dh(r[9]),
                "codUsu": int(r[10]) if r[10] is not None else None,
                "nomeUsu": _txt(r[11]),
                "itens": [],
                "anexos": [],
            }
            chamadas_por_id[registro["codChamada"]] = registro
            dados.append(registro)

        if dados:
            # Filhos por CODPARC (e não por IN de ids): uma consulta só, sem
            # estourar o limite de expressões do IN quando o histórico é longo.
            cursor.execute(
                """
                SELECT i.CODCHAMADA, i.CODITEM, i.NUFIN, i.ORDEM, i.DESFECHO
                FROM AD_COBRCHAMADAITEM i
                JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = i.CODCHAMADA
                WHERE c.CODPARC = :CODPARC
                ORDER BY i.CODITEM
                """,
                {"CODPARC": cod_parc},
            )
            for r in cursor.fetchall():
                pai = chamadas_por_id.get(int(r[0]))
                if pai is not None:
                    pai["itens"].append(
                        {
                            "codItem": int(r[1]),
                            "nufin": int(r[2]) if r[2] is not None else None,
                            "ordem": int(r[3]) if r[3] is not None else None,
                            "desfecho": _txt(r[4]),
                        }
                    )

            cursor.execute(
                """
                SELECT a.CODCHAMADA, a.CODANEXO, a.DESCRICAO, a.URL, a.DHANEXO, a.CODUSU
                FROM AD_COBRANEXO a
                JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = a.CODCHAMADA
                WHERE c.CODPARC = :CODPARC
                ORDER BY a.CODANEXO
                """,
                {"CODPARC": cod_parc},
            )
            for r in cursor.fetchall():
                pai = chamadas_por_id.get(int(r[0]))
                if pai is not None:
                    pai["anexos"].append(
                        {
                            "codAnexo": int(r[1]),
                            "descricao": _txt(r[2]),
                            "url": _texto_lob(r[3]),
                            "dhAnexo": _dh(r[4]),
                            "codUsu": int(r[5]) if r[5] is not None else None,
                        }
                    )

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/pagamentos-informados", methods=["GET"])
def pagamentos_informados():
    """Títulos em que o cliente INFORMOU pagamento — alimenta o badge da lista.

    Query: ?codParc=100 (opcional). Sem filtro devolve todos os marcadores; são
    poucos por natureza (só existe marcador em título que alguém marcou à mão),
    então a tela de títulos vencidos cruza em memória em vez de mandar centenas
    de NUFIN na query string. Mesmo raciocínio do /locks.

    Leitura pura: não exige sessão, como as demais rotas de consulta.
    """
    cod_parc = request.args.get("codParc")
    if cod_parc not in (None, ""):
        try:
            cod_parc = int(cod_parc)
        except ValueError:
            return jsonify({"erro": "'codParc' deve ser um número."}), 400
    else:
        cod_parc = None

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        indice = _pagtos_informados(cursor, cod_parc)
        dados = [{"nufin": nufin, **info} for nufin, info in sorted(indice.items())]

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/locks", methods=["GET"])
def locks():
    """Títulos em chamada NESTE MOMENTO — alimenta o badge "em chamada por...".

    Query: ?nufins=1,2,3 (opcional). Sem filtro, devolve todas as travas ativas
    — são poucas por natureza (uma por título aberto num modal), então filtrar
    em Python evita montar um IN com as centenas de títulos da tela.
    """
    filtro = request.args.get("nufins")
    alvo = None
    if filtro:
        try:
            alvo = {int(p) for p in filtro.split(",") if p.strip()}
        except ValueError:
            return jsonify({"erro": "'nufins' deve ser uma lista de inteiros separados por vírgula."}), 400

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(SQL_TRAVAS + " ORDER BY i.NUFIN")
        dados = [_linha_trava(r) for r in cursor.fetchall()]
        if alvo is not None:
            dados = [d for d in dados if d["nufin"] in alvo]

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/regua", methods=["GET"])
def regua():
    """Posição de cada título na régua (badge 1ª/2ª/3ª chamada).

    Query: ?codParc=<int> (opcional — sem ele, devolve a carteira inteira)
    Conta só chamadas PROATIVA + FINALIZADA — receptiva não empurra pro jurídico.
    `podeJuridico` = ordemAtual >= 3 (o envio em si continua manual).
    """
    # codParc é OPCIONAL: a tela de Títulos Vencidos mostra a carteira inteira e
    # precisa dos badges de todos os clientes de uma vez. Sem filtro, a consulta
    # devolve só os títulos que JÁ tiveram chamada proativa finalizada — um
    # subconjunto pequeno da carteira, não a base toda.
    cod_parc = request.args.get("codParc")
    if cod_parc not in (None, ""):
        try:
            cod_parc = _obrig_int(request.args, "codParc")
        except _Invalido as err:
            return jsonify({"erro": str(err)}), 400
    else:
        cod_parc = None

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(
            """
            SELECT NUFIN, CODPARC, ORDEMATUAL, DHULTIMA, DESFECHO, CODCHAMADA
            FROM (
                SELECT i.NUFIN,
                       i.DESFECHO,
                       c.CODPARC,
                       c.CODCHAMADA,
                       COUNT(*)     OVER (PARTITION BY i.NUFIN) AS ORDEMATUAL,
                       MAX(c.DHFIM) OVER (PARTITION BY i.NUFIN) AS DHULTIMA,
                       ROW_NUMBER() OVER (
                           PARTITION BY i.NUFIN
                           ORDER BY NVL(i.ORDEM, 0) DESC, c.DHFIM DESC
                       ) AS RN
                FROM AD_COBRCHAMADAITEM i
                JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = i.CODCHAMADA
                WHERE c.SENTIDO = 'PROATIVA'
                  AND c.SITUACAO = 'FINALIZADA'
                  AND (:CODPARC IS NULL OR c.CODPARC = :CODPARC)
            ) WHERE RN = 1
            ORDER BY NUFIN
            """,
            {"CODPARC": cod_parc},
        )
        dados = []
        for r in cursor.fetchall():
            ordem = int(r[2] or 0)
            dados.append(
                {
                    "nufin": int(r[0]),
                    "codParc": int(r[1]) if r[1] is not None else None,
                    "ordemAtual": ordem,
                    "dhUltima": _dh(r[3]),
                    "ultimoDesfecho": _txt(r[4]),
                    "codChamada": int(r[5]),
                    "podeJuridico": ordem >= 3,
                }
            )

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


# --- Painel da gerência -------------------------------------------------------
#
# Uma linha por cliente **que já foi trabalhado** — ou seja, o painel é da
# COBRANÇA, não da carteira. Quem nunca recebeu uma chamada não aparece aqui:
# para olhar a dívida crua existe a tela de títulos.
# Plano: dashboard-cobranca/docs/PAINEL-GERENTE.md
#
# A base é AD_COBRCHAMADA (quem foi trabalhado) e a carteira entra por LEFT
# JOIN, não o contrário. Isso importa em dois pontos:
#   - o painel não fica com um mar de "sem contato" (hoje seriam 342 de 344
#     clientes, o que afogaria a informação útil);
#   - cliente trabalhado que QUITOU continua aparecendo, com dívida zero, em vez
#     de sumir da tela como se o trabalho não tivesse existido.
#
# A parte da carteira REAPROVEITA CTE_CHEQUES + SELECT_RECEITAS de propósito.
# Reescrever aquela regra à mão (cheques pelo "bom para", RECDESP = 1, Regra 5
# dos renegociados) faria os valores do painel divergirem da tela de títulos —
# e dois números diferentes para a mesma coisa acabam com a confiança nos dois.
#
# O "ATRASO_DIAS > 0" é necessário porque o SELECT_RECEITAS devolve todo título
# em aberto, vencido ou não (o filtro de vencimento está comentado lá de
# propósito: a tela de títulos usa os filtros de data para recortar). Aqui só
# interessa o que já venceu.
#
# --- Por que estas CTEs estão fatiadas em constantes -------------------------
# O painel da gerência e a Visão 360° por Vendedor (docs/VENDEDOR-360.md) fazem a
# MESMA leitura por cliente, mudando só a BASE: o painel parte de quem já foi
# trabalhado (carteira entra por LEFT JOIN); a tela do vendedor parte da carteira
# dele (as chamadas é que entram por LEFT JOIN). Tudo o mais — a regra do valor
# do título, a régua, o marcador de pagamento, a agenda, a trava — é idêntico.
# Duplicar esse SQL seria repetir, dentro de casa, o erro que a REGRA DE OURO
# proíbe com o SELECT_RECEITAS: duas cópias da mesma regra divergem na primeira
# manutenção, e aí duas telas mostram números diferentes para a mesma dívida.
# Por isso: as partes comuns viram SQL_CTE_*, e cada tela escreve só o seu
# POR_CLIENTE e o seu SELECT final.
SQL_CTE_CARTEIRA = """
, TRABALHADOS AS (
    SELECT CODPARC,
           SUM(CASE WHEN SITUACAO = 'FINALIZADA' THEN 1 ELSE 0 END) AS QTD_CHAMADAS
    FROM AD_COBRCHAMADA
    WHERE SITUACAO IN ('FINALIZADA', 'EM_ANDAMENTO')
    GROUP BY CODPARC
),
CARTEIRA AS (
    SELECT CODPARC, NUFIN, ATRASO_DIAS, NVL(CODVEND, 0) AS CODVEND,
           CASE WHEN CODTIPTIT = 3
                THEN NVL(VLR_CHEQUE, NVL(VLRDESDOB, VLRLIQUIDO))
                ELSE NVL(VLRDESDOB, NVL(VLR_CHEQUE, VLRLIQUIDO))
           END AS VALOR
    FROM ( {carteira} )
    WHERE ATRASO_DIAS > 0
      {escopo_carteira}
),
"""

# Régua e marcador de pagamento — por TÍTULO, iguais nas duas telas.
SQL_CTE_REGUA = """
/* Posição de cada título na régua. Mesma regra do /regua: só PROATIVA +
   FINALIZADA conta, porque chamada receptiva não empurra para o jurídico. */
REGUA AS (
    SELECT NUFIN, ORDEM, DHULTIMA, DESFECHO FROM (
        SELECT i.NUFIN,
               i.DESFECHO,
               COUNT(*)     OVER (PARTITION BY i.NUFIN) AS ORDEM,
               MAX(c.DHFIM) OVER (PARTITION BY i.NUFIN) AS DHULTIMA,
               ROW_NUMBER() OVER (
                   PARTITION BY i.NUFIN
                   ORDER BY NVL(i.ORDEM, 0) DESC, c.DHFIM DESC
               ) AS RN
        FROM AD_COBRCHAMADAITEM i
        JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = i.CODCHAMADA
        WHERE c.SENTIDO = 'PROATIVA' AND c.SITUACAO = 'FINALIZADA'
    ) WHERE RN = 1
),
/* Marcador "cliente informou pagamento", por título. Sem filtro de SENTIDO de
   propósito: vale tanto o registro rápido (receptiva) quanto o desfecho marcado
   durante uma ligação normal. */
PAGTO_INF AS (
    SELECT i.NUFIN, MAX(c.DHFIM) AS DHINFORMADO
    FROM AD_COBRCHAMADAITEM i
    JOIN AD_COBRCHAMADA c ON c.CODCHAMADA = i.CODCHAMADA
    WHERE i.DESFECHO = 'PAGAMENTO_INFORMADO'
      AND c.SITUACAO = 'FINALIZADA'
    GROUP BY i.NUFIN
),
"""

# POR_CLIENTE do PAINEL: base = TRABALHADOS (quem já foi cobrado), carteira por
# LEFT JOIN. Cliente trabalhado que quitou continua aparecendo, com dívida zero.
_POR_CLIENTE_PAINEL = """
POR_CLIENTE AS (
    SELECT t.CODPARC,
           t.QTD_CHAMADAS,
           COUNT(ca.NUFIN)          AS QTD_TITULOS,
           NVL(SUM(ca.VALOR), 0)    AS VALOR_TOTAL,
           NVL(MAX(ca.ATRASO_DIAS), 0) AS MAIOR_ATRASO,
           NVL(MAX(r.ORDEM), 0)     AS ESTAGIO,
           SUM(CASE WHEN ca.NUFIN IS NOT NULL AND r.NUFIN IS NULL THEN 1 ELSE 0 END) AS SEM_CONTATO,
           SUM(CASE WHEN r.ORDEM  = 1 THEN 1 ELSE 0 END) AS ORD1,
           SUM(CASE WHEN r.ORDEM  = 2 THEN 1 ELSE 0 END) AS ORD2,
           SUM(CASE WHEN r.ORDEM >= 3 THEN 1 ELSE 0 END) AS ORD3,
           /* Desfecho do título MAIS AVANÇADO na régua — é ele que diz se o
              cliente ainda está em negociação ou já fechou acordo. */
           MAX(r.DESFECHO) KEEP (
               DENSE_RANK LAST ORDER BY NVL(r.ORDEM, 0), r.DHULTIMA
           ) AS ULT_DESFECHO,
           /* Só conta marcador de título QUE AINDA ESTÁ NA CARTEIRA (o join é
              com ca.NUFIN). Quando a baixa sai, o título deixa a CARTEIRA e o
              sinal se apaga sozinho — ninguém precisa limpar marcador nenhum. */
           COUNT(pi.NUFIN)     AS QTD_PAGTO_INF,
           MAX(pi.DHINFORMADO) AS DH_PAGTO_INF
    FROM TRABALHADOS t
        LEFT JOIN CARTEIRA  ca ON ca.CODPARC = t.CODPARC
        LEFT JOIN REGUA     r  ON r.NUFIN    = ca.NUFIN
        LEFT JOIN PAGTO_INF pi ON pi.NUFIN   = ca.NUFIN
    GROUP BY t.CODPARC, t.QTD_CHAMADAS
),
"""

# Último contato, agenda, retorno atrasado e trava — por CLIENTE, iguais nas duas
# telas. Nenhuma delas olha o vendedor: uma ligação é com o cliente, não com o
# título, então quem cobrou e quando não muda ao fatiar a carteira por vendedor.
SQL_CTE_CONTATO = """
ULT_CHAMADA AS (
    SELECT CODPARC, DHFIM, CODUSU FROM (
        SELECT CODPARC, DHFIM, CODUSU,
               ROW_NUMBER() OVER (PARTITION BY CODPARC ORDER BY DHFIM DESC) AS RN
        FROM AD_COBRCHAMADA
        WHERE SITUACAO = 'FINALIZADA'
    ) WHERE RN = 1
),
AGENDA AS (
    SELECT CODPARC, DHAGENDA AS PROX_RETORNO, CODUSU AS PROX_USU FROM (
        SELECT CODPARC, DHAGENDA, CODUSU,
               ROW_NUMBER() OVER (PARTITION BY CODPARC ORDER BY DHAGENDA) AS RN
        FROM AD_COBRCHAMADA
        WHERE SITUACAO = 'FINALIZADA'
          AND DHAGENDA IS NOT NULL
          AND DHAGENDA > SYSDATE
    ) WHERE RN = 1
),
/* "Prometeu voltar e não voltou": existe retorno marcado no passado e NENHUMA
   chamada finalizada depois dele. É o estado mais acionável do painel. */
ATRASADO AS (
    SELECT a.CODPARC, MAX(a.DHAGENDA) AS AGENDA_VENCIDA
    FROM AD_COBRCHAMADA a
    WHERE a.SITUACAO = 'FINALIZADA'
      AND a.DHAGENDA IS NOT NULL
      AND a.DHAGENDA <= SYSDATE
      AND NOT EXISTS (
          SELECT 1 FROM AD_COBRCHAMADA b
          WHERE b.CODPARC  = a.CODPARC
            AND b.SITUACAO = 'FINALIZADA'
            AND b.DHFIM    > a.DHAGENDA
      )
    GROUP BY a.CODPARC
),
TRAVA AS (
    SELECT DISTINCT CODPARC FROM AD_COBRCHAMADA
    WHERE SITUACAO = 'EM_ANDAMENTO' AND DHEXPIRA > SYSDATE
)
"""

_SELECT_PAINEL = """
SELECT pc.CODPARC, par.NOMEPARC, par.CGC_CPF,
       pc.QTD_TITULOS, pc.VALOR_TOTAL, pc.MAIOR_ATRASO,
       pc.ESTAGIO, pc.SEM_CONTATO, pc.ORD1, pc.ORD2, pc.ORD3, pc.ULT_DESFECHO,
       pc.QTD_CHAMADAS,
       uc.DHFIM   AS ULTIMO_CONTATO,
       uu.NOMEUSU AS ULTIMO_POR,
       ag.PROX_RETORNO,
       au.NOMEUSU AS PROX_POR,
       atr.AGENDA_VENCIDA,
       CASE WHEN tv.CODPARC IS NULL THEN 0 ELSE 1 END AS EM_CHAMADA,
       /* No FIM da lista de propósito: a leitura em Python é posicional, então
          coluna nova no meio deslocaria todos os índices seguintes. */
       pc.QTD_PAGTO_INF, pc.DH_PAGTO_INF
FROM POR_CLIENTE pc
    INNER JOIN TGFPAR par ON par.CODPARC = pc.CODPARC
    LEFT JOIN ULT_CHAMADA uc  ON uc.CODPARC  = pc.CODPARC
    LEFT JOIN TSIUSU      uu  ON uu.CODUSU   = uc.CODUSU
    LEFT JOIN AGENDA      ag  ON ag.CODPARC  = pc.CODPARC
    LEFT JOIN TSIUSU      au  ON au.CODUSU   = ag.PROX_USU
    LEFT JOIN ATRASADO    atr ON atr.CODPARC = pc.CODPARC
    LEFT JOIN TRAVA       tv  ON tv.CODPARC  = pc.CODPARC
ORDER BY pc.VALOR_TOTAL DESC
"""

SQL_PAINEL_ENVELOPE = (
    SQL_CTE_CARTEIRA
    + SQL_CTE_REGUA
    + _POR_CLIENTE_PAINEL
    + SQL_CTE_CONTATO
    + _SELECT_PAINEL
)

# Escopo da CTE CARTEIRA no painel: só quem já foi trabalhado. É redundante com o
# FROM TRABALHADOS do POR_CLIENTE, mas poda as linhas antes do JOIN.
ESCOPO_TRABALHADOS = "AND CODPARC IN (SELECT CODPARC FROM TRABALHADOS)"


def _situacao_cliente(
    qtd_titulos, agenda_vencida, prox_retorno, ult_desfecho, tem_chamada=True
):
    """Situação EXCLUSIVA do cliente, na ordem de precedência do plano (§3).

    No PAINEL não existe "SEM_CONTATO": por construção, todo cliente que chega lá
    já foi trabalhado (por isso `tem_chamada` é True por padrão — o painel nem
    passa o parâmetro). Cliente com estágio 0 é o que só teve chamada RECEPTIVA —
    houve contato, mas a régua (que só conta proativa) não começou.

    Na VISÃO POR VENDEDOR o estado volta a existir e é o motivo da tela: ali a
    base é a carteira do vendedor, então entra cliente que ninguém ligou ainda.
    "Sem contato" = nenhuma chamada FINALIZADA nem EM ANDAMENTO (a CTE
    TRABALHADOS ignora CANCELADA — chamada aberta e fechada sem registrar não é
    contato). Ver docs/VENDEDOR-360.md §2.

    "Elegível ao jurídico" NÃO entra: é sinalizador à parte. Um cliente pode
    estar agendado E na 3ª chamada ao mesmo tempo, e transformar isso numa
    situação exclusiva esconderia um dos dois.
    """
    if qtd_titulos == 0:
        return "SEM_DIVIDA"
    if not tem_chamada:
        return "SEM_CONTATO"
    if agenda_vencida:
        return "RETORNO_ATRASADO"
    if prox_retorno:
        return "AGENDADO"
    if ult_desfecho == "ACORDO":
        return "ACORDO"
    return "EM_ANDAMENTO"


def _linha_cliente(r, tem_chamada=True):
    """Linha "um cliente" → dicionário, das colunas 0..20 do SELECT.

    Painel e Visão por Vendedor devolvem exatamente os mesmos 21 primeiros campos
    (é o mesmo cartão de cliente na tela, com outro conjunto de clientes), então
    a montagem fica num lugar só. Cada rota acrescenta os campos próprios dela
    depois — as colunas EXTRA vêm no fim do SELECT, justamente para não deslocar
    os índices lidos aqui.
    """
    qtd_titulos = int(r[3] or 0)
    estagio = int(r[6] or 0)
    ult_desfecho = _txt(r[11])
    prox_retorno = _dh(r[15])
    agenda_vencida = _dh(r[17])
    return {
        "codParc": int(r[0]),
        "nomeParc": _txt(r[1]),
        # Cru, como no /cobranca/cliente — quem formata é o fmtDoc do app.
        "cgcCpf": _txt(r[2]),
        "qtdTitulos": qtd_titulos,
        "valorTotal": float(r[4] or 0),
        "maiorAtrasoDias": int(r[5] or 0),
        "estagio": estagio,
        "titulosSemContato": int(r[7] or 0),
        "porOrdem": {"1": int(r[8] or 0), "2": int(r[9] or 0), "3": int(r[10] or 0)},
        "ultimoDesfecho": ult_desfecho,
        "qtdChamadas": int(r[12] or 0),
        "ultimoContatoEm": _dh(r[13]),
        "ultimoContatoPor": _txt(r[14]),
        "proximoRetornoEm": prox_retorno,
        "proximoRetornoPor": _txt(r[16]),
        "retornoAtrasadoDe": agenda_vencida,
        "emChamadaAgora": bool(r[18]),
        # SINALIZADOR, não situação: o cliente pode ter informado pagamento E
        # estar com retorno atrasado ao mesmo tempo, e virar situação exclusiva
        # esconderia um dos dois — mesmo motivo do podeJuridico
        # (docs/PAINEL-GERENTE.md §3).
        "titulosPagamentoInformado": int(r[19] or 0),
        "pagamentoInformadoEm": _dh(r[20]),
        "situacao": _situacao_cliente(
            qtd_titulos, agenda_vencida, prox_retorno, ult_desfecho, tem_chamada
        ),
        # Elegibilidade, NÃO encaminhamento: não existe Fase 4 no sistema.
        # Ver docs/PAINEL-GERENTE.md §2.
        "podeJuridico": estagio >= 3 and ult_desfecho != "ACORDO",
    }


@bp.route("/api/cobranca/painel", methods=["GET"])
def painel():
    """Uma linha por cliente JÁ TRABALHADO, com a posição dele na régua.

    Query (opcionais): ?codVend=<int>&codCid=<int>
    """
    filtros = []
    params = {}
    for campo, coluna in (("codVend", CODVEND_EFETIVO), ("codCid", "PAR.CODCID")):
        valor = request.args.get(campo)
        if valor not in (None, ""):
            try:
                params[campo.upper()] = int(valor)
            except ValueError:
                return jsonify({"erro": f"Parâmetro '{campo}' deve ser um número."}), 400
            filtros.append(f"AND ({coluna}) = :{campo.upper()}")

    carteira = SELECT_RECEITAS + "\n" + "\n".join(filtros)
    sql = CTE_CHEQUES + SQL_PAINEL_ENVELOPE.format(
        carteira=carteira, escopo_carteira=ESCOPO_TRABALHADOS
    )

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(sql, params)

        dados = [_linha_cliente(r) for r in cursor.fetchall()]

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


# --- Visão 360° por Vendedor --------------------------------------------------
#
# Duas leituras da MESMA carteira (docs/VENDEDOR-360.md):
#   /vendedores-resumo  → uma linha por vendedor  (tela de entrada)
#   /vendedor-360       → uma linha por cliente DAQUELE vendedor (detalhe)
#
# Diferença de fundo para o painel da gerência: aqui a base é a CARTEIRA, e as
# chamadas entram por LEFT JOIN. É o oposto do painel, e de propósito — mostrar
# quem está FORA do radar da cobrança é o motivo desta tela existir.
#
# ⚠️ O vendedor sai do TÍTULO quando FIN.CODVEND > 0. Somente quando ele está
# zerado/nulo, a cobrança herda TGFCAB.AD_CODVENDINT da venda; em título
# renegociado que perdeu a NUNOTA, herda o vendedor interno apenas se todas as
# origens da mesma NURENEG tiverem o mesmo vendedor. O cadastro do cliente
# (PAR.CODVEND) não participa. Um cliente que comprou com dois vendedores aparece nas duas
# telas, cada uma somando só os títulos dela — por isso o total do cliente aqui
# pode ser MENOR que o da Visão 360° dele, que mostra tudo. É a leitura certa
# para "títulos por vendedor" e a mesma que o filtro de vendedor da tela de
# Títulos Vencidos já usa.

# Faixas de atraso (aging). As 5 são as mesmas medidas com a carteira real em
# 08/08 e ficam escritas UMA vez: se a tela de entrada e a de detalhe usassem
# réguas diferentes, os dois gráficos discordariam sobre a mesma dívida.
# Ordem: as 5 contagens e DEPOIS os 5 valores (o _aging lê por deslocamento).
SQL_AGING = """
           SUM(CASE WHEN ca.ATRASO_DIAS <= 30                THEN 1 ELSE 0 END) AS QTD_F1,
           SUM(CASE WHEN ca.ATRASO_DIAS BETWEEN 31  AND 90   THEN 1 ELSE 0 END) AS QTD_F2,
           SUM(CASE WHEN ca.ATRASO_DIAS BETWEEN 91  AND 180  THEN 1 ELSE 0 END) AS QTD_F3,
           SUM(CASE WHEN ca.ATRASO_DIAS BETWEEN 181 AND 365  THEN 1 ELSE 0 END) AS QTD_F4,
           SUM(CASE WHEN ca.ATRASO_DIAS > 365                THEN 1 ELSE 0 END) AS QTD_F5,
           NVL(SUM(CASE WHEN ca.ATRASO_DIAS <= 30               THEN ca.VALOR END), 0) AS VLR_F1,
           NVL(SUM(CASE WHEN ca.ATRASO_DIAS BETWEEN 31  AND 90  THEN ca.VALOR END), 0) AS VLR_F2,
           NVL(SUM(CASE WHEN ca.ATRASO_DIAS BETWEEN 91  AND 180 THEN ca.VALOR END), 0) AS VLR_F3,
           NVL(SUM(CASE WHEN ca.ATRASO_DIAS BETWEEN 181 AND 365 THEN ca.VALOR END), 0) AS VLR_F4,
           NVL(SUM(CASE WHEN ca.ATRASO_DIAS > 365               THEN ca.VALOR END), 0) AS VLR_F5
"""

# Chaves das faixas na resposta JSON, na MESMA ordem das colunas do SQL_AGING.
FAIXAS_ATRASO = ("d1a30", "d31a90", "d91a180", "d181a365", "dMais365")


def _aging(r, base):
    """As 5 faixas a partir de 10 colunas consecutivas (5 contagens, 5 valores)."""
    return {
        chave: {"qtd": int(r[base + i] or 0), "valor": float(r[base + 5 + i] or 0)}
        for i, chave in enumerate(FAIXAS_ATRASO)
    }


# POR_CLIENTE do VENDEDOR: base = CARTEIRA (todo cliente com título vencido dele),
# chamadas por LEFT JOIN. Cliente sem nenhuma chamada entra com TEM_CHAMADA = 0 e
# vira "sem contato" — é justamente quem a tela quer revelar.
_POR_CLIENTE_VENDEDOR = """
POR_CLIENTE AS (
    SELECT ca.CODPARC,
           NVL(t.QTD_CHAMADAS, 0) AS QTD_CHAMADAS,
           COUNT(ca.NUFIN)             AS QTD_TITULOS,
           NVL(SUM(ca.VALOR), 0)       AS VALOR_TOTAL,
           NVL(MAX(ca.ATRASO_DIAS), 0) AS MAIOR_ATRASO,
           NVL(MAX(r.ORDEM), 0)        AS ESTAGIO,
           /* Aqui a CARTEIRA é a base, então ca.NUFIN nunca é nulo: título sem
              linha na régua é título que nunca entrou numa chamada. */
           SUM(CASE WHEN r.NUFIN IS NULL THEN 1 ELSE 0 END) AS SEM_CONTATO,
           SUM(CASE WHEN r.ORDEM  = 1 THEN 1 ELSE 0 END) AS ORD1,
           SUM(CASE WHEN r.ORDEM  = 2 THEN 1 ELSE 0 END) AS ORD2,
           SUM(CASE WHEN r.ORDEM >= 3 THEN 1 ELSE 0 END) AS ORD3,
           MAX(r.DESFECHO) KEEP (
               DENSE_RANK LAST ORDER BY NVL(r.ORDEM, 0), r.DHULTIMA
           ) AS ULT_DESFECHO,
           COUNT(pi.NUFIN)     AS QTD_PAGTO_INF,
           MAX(pi.DHINFORMADO) AS DH_PAGTO_INF,
           CASE WHEN t.CODPARC IS NULL THEN 0 ELSE 1 END AS TEM_CHAMADA,
""" + SQL_AGING + """
    FROM CARTEIRA ca
        LEFT JOIN TRABALHADOS t  ON t.CODPARC  = ca.CODPARC
        LEFT JOIN REGUA       r  ON r.NUFIN    = ca.NUFIN
        LEFT JOIN PAGTO_INF   pi ON pi.NUFIN   = ca.NUFIN
    GROUP BY ca.CODPARC, t.CODPARC, t.QTD_CHAMADAS
),
"""

# As colunas 0..20 são as MESMAS do painel, na mesma ordem — é o que permite os
# dois usarem o _linha_cliente. As novas (21 em diante) vêm depois, no fim.
_SELECT_VENDEDOR = """
SELECT pc.CODPARC, par.NOMEPARC, par.CGC_CPF,
       pc.QTD_TITULOS, pc.VALOR_TOTAL, pc.MAIOR_ATRASO,
       pc.ESTAGIO, pc.SEM_CONTATO, pc.ORD1, pc.ORD2, pc.ORD3, pc.ULT_DESFECHO,
       pc.QTD_CHAMADAS,
       uc.DHFIM   AS ULTIMO_CONTATO,
       uu.NOMEUSU AS ULTIMO_POR,
       ag.PROX_RETORNO,
       au.NOMEUSU AS PROX_POR,
       atr.AGENDA_VENCIDA,
       CASE WHEN tv.CODPARC IS NULL THEN 0 ELSE 1 END AS EM_CHAMADA,
       pc.QTD_PAGTO_INF, pc.DH_PAGTO_INF,
       pc.TEM_CHAMADA,
       pc.QTD_F1, pc.QTD_F2, pc.QTD_F3, pc.QTD_F4, pc.QTD_F5,
       pc.VLR_F1, pc.VLR_F2, pc.VLR_F3, pc.VLR_F4, pc.VLR_F5
FROM POR_CLIENTE pc
    INNER JOIN TGFPAR par ON par.CODPARC = pc.CODPARC
    LEFT JOIN ULT_CHAMADA uc  ON uc.CODPARC  = pc.CODPARC
    LEFT JOIN TSIUSU      uu  ON uu.CODUSU   = uc.CODUSU
    LEFT JOIN AGENDA      ag  ON ag.CODPARC  = pc.CODPARC
    LEFT JOIN TSIUSU      au  ON au.CODUSU   = ag.PROX_USU
    LEFT JOIN ATRASADO    atr ON atr.CODPARC = pc.CODPARC
    LEFT JOIN TRAVA       tv  ON tv.CODPARC  = pc.CODPARC
ORDER BY pc.VALOR_TOTAL DESC
"""

SQL_VENDEDOR_ENVELOPE = (
    SQL_CTE_CARTEIRA
    + SQL_CTE_REGUA
    + _POR_CLIENTE_VENDEDOR
    + SQL_CTE_CONTATO
    + _SELECT_VENDEDOR
)

# Tela de entrada: uma linha por vendedor. Não precisa da régua nem da agenda —
# só da carteira e de quantos clientes dela já receberam alguma chamada.
#
# ⚠️ O `.rstrip()` da vírgula NÃO é firula: as constantes SQL_CTE_* terminam com
# ")," porque nas outras duas consultas sempre vem outra CTE depois. Aqui o
# SELECT vem logo em seguida, e "), SELECT" faz o Oracle procurar mais uma CTE e
# devolver ORA-00903 (nome de tabela inválido) — que foi exatamente o erro que
# esta consulta deu em produção na primeira subida.
SQL_VENDEDORES_RESUMO = SQL_CTE_CARTEIRA.rstrip().rstrip(",") + """
SELECT ca.CODVEND,
       NVL(ven.APELIDO, 'SEM VENDEDOR') AS APELIDO,
       COUNT(DISTINCT ca.CODPARC) AS QTD_CLIENTES,
       /* "Trabalhado" é por CLIENTE, não por título: a chamada é com o cliente.
          Um cliente atendido por dois vendedores conta como trabalhado nos dois,
          porque foi mesmo. */
       COUNT(DISTINCT CASE WHEN t.CODPARC IS NOT NULL THEN ca.CODPARC END) AS QTD_CLI_TRAB,
       COUNT(ca.NUFIN)             AS QTD_TITULOS,
       NVL(SUM(ca.VALOR), 0)       AS VALOR_TOTAL,
       NVL(MAX(ca.ATRASO_DIAS), 0) AS MAIOR_ATRASO,
""" + SQL_AGING + """
FROM CARTEIRA ca
    LEFT JOIN TRABALHADOS t   ON t.CODPARC   = ca.CODPARC
    LEFT JOIN TGFVEN      ven ON ven.CODVEND = ca.CODVEND
GROUP BY ca.CODVEND, ven.APELIDO
ORDER BY VALOR_TOTAL DESC
"""


@bp.route("/api/cobranca/vendedores-resumo", methods=["GET"])
def vendedores_resumo():
    """Uma linha por vendedor, sobre a carteira VENCIDA — tela de entrada.

    Sem filtro: são poucas dezenas de linhas e a tela precisa do ranking inteiro
    para o gerente escolher em quem clicar.
    """
    sql = CTE_CHEQUES + SQL_VENDEDORES_RESUMO.format(
        carteira=SELECT_RECEITAS, escopo_carteira=""
    )

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()
        cursor.execute(sql)

        dados = [
            {
                # CODVEND 0 = título sem vendedor (a CTE CARTEIRA faz NVL para 0).
                # Vira uma linha normal da lista, rotulada "SEM VENDEDOR": é
                # dívida real, só não tem dono.
                "codVend": int(r[0] or 0),
                "apelido": _txt(r[1]) or "SEM VENDEDOR",
                "qtdClientes": int(r[2] or 0),
                "qtdClientesTrabalhados": int(r[3] or 0),
                "qtdTitulos": int(r[4] or 0),
                "valorTotal": float(r[5] or 0),
                "maiorAtrasoDias": int(r[6] or 0),
                "aging": _aging(r, 7),
            }
            for r in cursor.fetchall()
        ]

        return jsonify({"sucesso": True, "totalRegistros": len(dados), "dados": dados})

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()


@bp.route("/api/cobranca/vendedor-360", methods=["GET"])
def vendedor_360():
    """Uma linha por cliente, com a situação de cobrança de cada um.

    Query: ?codVend=<int> (OPCIONAL). Sem ele, devolve a carteira vencida
    INTEIRA — é o consolidado "todos os vendedores" da tela de entrada.

    O consolidado precisa vir do banco, e não de somar as linhas do
    /vendedores-resumo no navegador: quem compra com dois vendedores tem título
    nos dois, então somar os `qtdClientes` contaria o mesmo cliente duas vezes.
    Aqui a base é o CLIENTE, e cada um aparece uma vez só.
    """
    valor = request.args.get("codVend")
    cod_vend = None
    if valor not in (None, ""):
        try:
            cod_vend = int(valor)
        except ValueError:
            return jsonify({"erro": "Parâmetro 'codVend' deve ser um número."}), 400

    carteira = SELECT_RECEITAS
    params = {}
    if cod_vend is not None:
        # NVL(...,0) para casar com o agrupamento do /vendedores-resumo, que junta
        # CODVEND nulo e 0 na mesma linha "SEM VENDEDOR". Sem isso, clicar naquela
        # linha traria menos clientes do que ela mesma diz ter.
        carteira += f"\nAND ({CODVEND_EFETIVO}) = :CODVEND"
        params["CODVEND"] = cod_vend

    sql = CTE_CHEQUES + SQL_VENDEDOR_ENVELOPE.format(
        carteira=carteira, escopo_carteira=""
    )

    conexao = None
    try:
        conexao = conectar_oracle()
        if not conexao:
            return jsonify({"erro": "Falha na conexão com o banco"}), 500

        cursor = conexao.cursor()

        if cod_vend is None:
            apelido = "Todos os vendedores"
        else:
            # Consulta à parte para o nome: se o vendedor não tiver nenhum título
            # vencido, a consulta grande volta vazia e a tela ainda precisa dizer
            # de quem ela está falando.
            cursor.execute(
                "SELECT APELIDO FROM TGFVEN WHERE CODVEND = :CODVEND",
                {"CODVEND": cod_vend},
            )
            linha = cursor.fetchone()
            apelido = (_txt(linha[0]) if linha else None) or "SEM VENDEDOR"

        cursor.execute(sql, params)

        dados = []
        for r in cursor.fetchall():
            cliente = _linha_cliente(r, tem_chamada=bool(r[21]))
            # Por cliente para o gráfico poder filtrar a tabela: clicar numa faixa
            # do aging mostra só quem tem título nela, sem ida nova ao servidor.
            cliente["aging"] = _aging(r, 22)
            dados.append(cliente)

        # Totais do vendedor somados a partir das MESMAS linhas que a tabela
        # mostra — assim o cabeçalho e o gráfico nunca discordam da lista.
        # Não é "somar no navegador": as linhas já vêm agregadas do Oracle.
        vendedor = {
            "codVend": cod_vend,
            "apelido": apelido,
            "qtdClientes": len(dados),
            "qtdTitulos": sum(c["qtdTitulos"] for c in dados),
            "valorTotal": sum(c["valorTotal"] for c in dados),
            "maiorAtrasoDias": max((c["maiorAtrasoDias"] for c in dados), default=0),
            "aging": {
                faixa: {
                    "qtd": sum(c["aging"][faixa]["qtd"] for c in dados),
                    "valor": sum(c["aging"][faixa]["valor"] for c in dados),
                }
                for faixa in FAIXAS_ATRASO
            },
        }

        return jsonify(
            {
                "sucesso": True,
                "totalRegistros": len(dados),
                "vendedor": vendedor,
                "dados": dados,
            }
        )

    except cx_Oracle.Error as err:
        return _erro(f"Erro de Banco de Dados: {err}")
    except Exception as e:
        return _erro(e)
    finally:
        if conexao:
            conexao.close()
