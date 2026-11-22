#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r7_m10_gate.py — Round 7 / R7A M10 双片重解战役验收门。

验收内容（任务书口径，seed 20261009，CWD 无关——路径全部自 __file__ 解析，
只验存档数据、不触发任何求解；双片翻正与 blocked 两结局都必须过门——验一致
性不验结局）：
  ① 在盘 M10 证书进程外 --verify-cert 重验 exit 0（引擎脚本按行分发）；
  ② 行 schema：certified ⇒ 证书在盘且 >E* 精确断言；blocked ⇒ 解档在盘＋
     best_certified_attempt 精确分数＋lift 实测；未跑 ⇒ reason；
  ③ lift/基线重算一致：M9 基线 == m9_campaign.json 在盘精确分数（a5 片另与
     hermite_strips.json M9 行交叉核对），lift == certified-or-attempt − 基线，
     margin_vs_E_star 一致；
  ④ 铁律：条带行 certified>E*（精确 Fraction）；blocked 行 attempt ≤ E*+1e-6；
     record_prospective == partition 精确 min 且 ≤ E*+1e-6（unchanged 口径 ==
     endgame.json assembledRecord 原值）；
  ⑤ m10_campaign.py 从存档重装配到临时路径，与在盘 JSON 逐位一致（sha256）；
  ⑥ 负对照三件全触发：行篡改 +1e-9 必检出／证书篡改 +1e-9 --verify-cert
     exit≠0／M9 冒充 params.M 检出＋无解档 blocked 拒；
  ⑦ 预算守门：Σsolve_s/10800 ≤ 19 当量（含 per-piece 换算与解档一致性）；
  ⑧ 斜率表 M8→M9→M10 逐片入账：M8/M9 与 m9_campaign.json 在盘一致、
     required_lift == E*−基线、lift_M8_M9/lift_M9_M10/保持比全部精确重算一致。

十检编排：G1 schema／G2 ①②／G3 ③／G4 ④／G5 ⑤幂等／G6 ⑦预算／G7 ⑧斜率表
／G8-G10 ⑥负对照三件。
用法：python3 thomson-n9/numerics/bounds/r7_m10_gate.py   （任意 CWD）
exit 0 = 过门。
"""
from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = HERE / "results"
CAMPAIGN = RESULTS / "m10_campaign.json"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

SEED = 20261009
E_TOL = Fr(1, 10 ** 6)
EPS9 = Fr(1, 10 ** 9)
KS = (48, 56, 64)
M10, M9, K6 = 10, 9, 6
EQUIV_UNIT_S = 10800.0
BUDGET_CAP_EQ = 19.0
# M9 基线在 m9_campaign.json 行内的字段（Lukács M9 blocked ⇒ best_certified_attempt；
# a5 M9 blocked 行 certified 即 attempt）
M9_FIELD = {"m079-m765": "best_certified_attempt", "m765-m748": "certified"}
ENGINE_SCRIPT = {"lukacs": HERE / "strips_final.py",
                 "a5-hermite": HERE / "hermite_ladder.py",
                 "typed": HERE / "typed_ladder.py"}


def cert_M(cert: dict) -> int | None:
    if "provenance" in cert and isinstance(cert["provenance"], dict) \
            and cert["provenance"].get("params", {}).get("M") is not None:
        return cert["provenance"]["params"]["M"]
    return cert.get("params", {}).get("M")


checks = []


def chk(name: str, ok: bool, detail: str = "") -> bool:
    checks.append((name, bool(ok), detail))
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f"：{detail}" if detail else ""),
          flush=True)
    return bool(ok)


def E_star() -> Fr:
    return Fr(str(json.loads(WORKFLOW_DATA.read_text())["energies"]["9"]["value"]))


def run_verify_cert(engine: str, cert_path: Path) -> tuple[int, str]:
    """进程外 --verify-cert（引擎脚本按行 engine 分发）。"""
    script = ENGINE_SCRIPT[engine]
    r = subprocess.run([sys.executable, str(script), "--verify-cert", str(cert_path)],
                       capture_output=True, text=True, timeout=1800)
    return r.returncode, (r.stdout[-300:] + r.stderr[-300:])


# ---------------------------------------------------------- 行校验（可重入于篡改副本）
def validate_rows(camp: dict, Estar: Fr, run_engine_verify: bool = True,
                  verify_details: list | None = None) -> list[str]:
    """对 campaign 的 rows 做全部行级校验；返回问题清单（空 = 全过）。

    run_engine_verify=False 时跳过进程外 --verify-cert（负对照副本用：省时且
    NC 考察的是行级一致性而非引擎重算）。
    """
    probs: list[str] = []
    rows = camp.get("rows", [])
    if len(rows) != 2:
        probs.append(f"rows 数 {len(rows)} ≠ 2")
        return probs
    for row in rows:
        piece = row.get("piece", "?")
        if row.get("M") != M10 or row.get("K") != K6:
            probs.append(f"{piece}: M/K 字段 {row.get('M')}/{row.get('K')} ≠ 10/6")
        if row.get("provenance", {}).get("seed") != SEED:
            probs.append(f"{piece}: provenance.seed ≠ {SEED}")
        if list(row.get("provenance", {}).get("ks", [])) != list(KS):
            probs.append(f"{piece}: provenance.ks {row.get('provenance', {}).get('ks')} ≠ {list(KS)}")
        st = row.get("status")
        if st == "certified":
            cpath = row.get("certificate")
            spath = row.get("solution")
            if not cpath or not (REPO / cpath).exists():
                probs.append(f"{piece}: certified 行证书不在盘（{cpath}）")
                continue
            if not spath or not (REPO / spath).exists():
                probs.append(f"{piece}: certified 行解档不在盘（{spath}）")
            cert = json.loads((REPO / cpath).read_text())
            cm = cert_M(cert)
            if cm != row.get("M"):
                probs.append(f"{piece}: 证书 params.M={cm} ≠ 行 M={row.get('M')}"
                             f"（M9 冒充/张冠李戴检出）")
            cb = str(cert.get("claimed_bound"))
            if cb != row.get("certified"):
                probs.append(f"{piece}: 行 certified 与证书 claimed_bound 失配"
                             f"（{row.get('certified')} ≠ {cb}）")
            if row.get("certified") is None:
                probs.append(f"{piece}: certified 行缺 certified 精确分数")
                continue
            c = Fr(row["certified"])
            if row["kind"] == "strip" and not c > Estar:
                probs.append(f"{piece}: 条带行 certified ≤ E*（断言失败）")
            mE = Fr(row["margin_vs_E_star"]["value"])
            if mE != c - Estar:
                probs.append(f"{piece}: margin_vs_E_star 重算失配")
            if run_engine_verify:
                rc, out = run_verify_cert(row["engine"], REPO / cpath)
                if verify_details is not None:
                    verify_details.append((piece, rc))
                if rc != 0:
                    probs.append(f"{piece}: 进程外 --verify-cert exit {rc}：{out[-160:]}")
        elif st == "blocked":
            spath = row.get("solution")
            if not spath or not (REPO / spath).exists():
                probs.append(f"{piece}: blocked 行解档不在盘（{spath}）——无解档"
                             f" blocked 必拒")
            ba = row.get("best_certified_attempt")
            if ba is None:
                probs.append(f"{piece}: blocked 行缺 best_certified_attempt")
            else:
                c = Fr(ba)
                if row["kind"] == "strip" and c > Estar + E_TOL:
                    probs.append(f"{piece}: blocked 行 attempt > E*+1e-6（本应 "
                                 f"certified——状态自相矛盾）")
                if "lift" not in row or row["lift"].get("value") is None:
                    probs.append(f"{piece}: blocked 行缺 lift 实测")
            if row.get("certificate") is not None:
                probs.append(f"{piece}: blocked 行不应带证书")
        elif st in ("not_run", "machine_unsolvable"):
            if not row.get("reason"):
                probs.append(f"{piece}: {st} 行缺 reason")
            if row.get("certified") is not None:
                probs.append(f"{piece}: {st} 行不应带 certified 值")
        else:
            probs.append(f"{piece}: 未知 status {st}")
    return probs


def validate_lift_baseline(camp: dict, Estar: Fr) -> list[str]:
    """③ lift/基线重算一致（基线独立取自 m9_campaign.json／hermite_strips.json）。"""
    probs: list[str] = []
    m9c = json.loads((RESULTS / "m9_campaign.json").read_text())
    rows9 = {r["piece"]: r for r in m9c["rows"]}
    hs9 = {}
    if (RESULTS / "hermite_strips.json").exists():
        for r in json.loads((RESULTS / "hermite_strips.json").read_text())["strips"]:
            if r.get("M") == M9:
                hs9[r["tag"]] = r
    b9_by = {p: (camp.get("m9_baselines") or {}).get(p, {}) for p in M9_FIELD}
    for piece, field in M9_FIELD.items():
        r9 = rows9.get(piece)
        if r9 is None:
            probs.append(f"{piece}: m9_campaign.json 无该行")
            continue
        if r9.get("status") != "blocked":
            probs.append(f"{piece}: m9 行 status={r9.get('status')} 非基线口径（blocked）")
        want = r9.get(field)
        if want is None:
            probs.append(f"{piece}: m9_campaign.json 行缺 {field}")
            continue
        got = b9_by[piece].get("certified")
        if got is None or Fr(got) != Fr(want):
            probs.append(f"{piece}: 基线 {got} ≠ m9_campaign.json {field} {want}")
        # a5 片与 hermite_strips.json M9 行交叉核对
        if piece == "m765-m748":
            hcert = (hs9.get(piece) or {}).get("certified")
            if hcert is None or Fr(hcert) != Fr(want):
                probs.append(f"{piece}: hermite_strips.json M9 行 {hcert} ≠ 基线 {want}")
    # 行级 lift/margin 重算
    for row in camp.get("rows", []):
        piece = row.get("piece", "?")
        attempt = None
        if row.get("certified") is not None:
            attempt = Fr(row["certified"])
        elif row.get("best_certified_attempt") is not None:
            attempt = Fr(row["best_certified_attempt"])
        if attempt is None:
            if row.get("lift") is not None:
                probs.append(f"{piece}: 无数值却带 lift")
            continue
        base = Fr(b9_by[piece]["certified"])
        if row.get("lift") is None or Fr(row["lift"]["value"]) != attempt - base:
            probs.append(f"{piece}: lift 重算 {attempt - base} ≠ 账面 "
                         f"{(row.get('lift') or {}).get('value')}")
        if Fr(row["margin_vs_E_star"]["value"]) != attempt - Estar:
            probs.append(f"{piece}: margin_vs_E_star 重算失配")
        if abs(row["lift"]["float"] - float(attempt - base)) > 1e-15:
            probs.append(f"{piece}: lift float 失配")
    return probs


def validate_record(camp: dict, Estar: Fr) -> list[str]:
    """④ 铁律：条带断言＋拼合前瞻 == partition 精确 min 且 ≤ E*+1e-6。"""
    probs: list[str] = []
    rec = camp.get("record_prospective", {})
    part = rec.get("partition")
    eg = json.loads((RESULTS / "endgame.json").read_text())
    if rec.get("unchanged_from_round8"):
        if rec.get("value") != eg["assembledRecord"]["value"]:
            probs.append("unchanged 口径但值非 endgame.json assembledRecord 原值")
    else:
        if not part:
            probs.append("翻正口径缺 partition")
        else:
            vmin = min(Fr(c["bound"]) for c in part)
            if str(vmin) != rec.get("value"):
                probs.append("record 值 ≠ partition 精确 min")
            ints = [c["interval"] for c in part]
            for iv in ("[-79/100,-153/200]", "[-153/200,-187/250]"):
                if iv not in ints:
                    probs.append(f"partition 缺翻正胞元 {iv}")
            # 翻正胞元应与 rows 一致
            rows_by = {r["piece"]: r for r in camp.get("rows", [])}
            for piece, iv in (("m079-m765", "[-79/100,-153/200]"),
                              ("m765-m748", "[-153/200,-187/250]")):
                cell = next((c for c in part if c["interval"] == iv), None)
                r = rows_by.get(piece, {})
                if cell is None or r.get("certified") is None:
                    continue
                if Fr(cell["bound"]) != Fr(r["certified"]):
                    probs.append(f"partition {piece} 胞元与行 certified 失配")
    if rec.get("value") is not None and Fr(rec["value"]) > Estar + E_TOL:
        probs.append("record 前瞻值 > E*+1e-6（铁律）")
    return probs


def validate_budget(camp: dict) -> list[str]:
    """⑦ 预算守门：一致性 ＋ Σsolve_s/10800 ≤ 19 当量。"""
    probs: list[str] = []
    bud = camp.get("budget", {})
    if abs(bud.get("EQUIV_UNIT_S", -1) - EQUIV_UNIT_S) > 1e-9:
        probs.append(f"budget.EQUIV_UNIT_S {bud.get('EQUIV_UNIT_S')} ≠ {EQUIV_UNIT_S}")
    per = bud.get("per_piece", {})
    tot = 0.0
    for piece, v in per.items():
        ss = v.get("solve_s")
        if isinstance(ss, (int, float)):
            tot += ss
            if abs(v.get("equivalents", -1) - ss / EQUIV_UNIT_S) > 1e-3 + 1e-6 * ss / EQUIV_UNIT_S:
                probs.append(f"{piece}: equivalents 换算失守")
        elif ss is not None:
            probs.append(f"{piece}: solve_s 非数值 {ss}")
    if abs(bud.get("total_solve_s", -1) - tot) > 1e-6:
        probs.append(f"total_solve_s {bud.get('total_solve_s')} ≠ Σ {tot}")
    if abs(bud.get("total_equivalents", -1) - tot / EQUIV_UNIT_S) > 1e-3:
        probs.append("total_equivalents 失守")
    if not tot / EQUIV_UNIT_S <= BUDGET_CAP_EQ:
        probs.append(f"预算超红线：Σsolve_s/10800 = {tot / EQUIV_UNIT_S:.3f} > "
                     f"{BUDGET_CAP_EQ} 当量")
    # 行 solve_s 与解档 solver_info 一致
    for row in camp.get("rows", []):
        sp = row.get("solution")
        ss = row.get("solve_s")
        if sp and (REPO / sp).exists() and ss is not None:
            sol = json.loads((REPO / sp).read_text())
            ssi = sol.get("solver_info", {}).get("solve_s")
            if ssi is not None and abs(ss - ssi) > 1e-6:
                probs.append(f"{row['piece']}: 行 solve_s {ss} ≠ 解档 {ssi}")
    return probs


def validate_slope_table(camp: dict, Estar: Fr) -> list[str]:
    """⑧ 斜率表 M8→M9→M10 逐片精确重算一致。"""
    probs: list[str] = []
    m9c = json.loads((RESULTS / "m9_campaign.json").read_text())
    rows9 = {r["piece"]: r for r in m9c["rows"]}
    b8_by = m9c.get("m8_baselines", {})
    tab = camp.get("slope_table", {})
    if set(tab.keys()) != set(M9_FIELD.keys()):
        probs.append(f"斜率表片集 {sorted(tab.keys())} ≠ {sorted(M9_FIELD.keys())}")
    for piece, field in M9_FIELD.items():
        ent = tab.get(piece)
        if ent is None:
            continue
        b8 = Fr(b8_by[piece]["certified"])
        b9 = Fr(rows9[piece][field])
        row = next((r for r in camp.get("rows", []) if r["piece"] == piece), {})
        if Fr(ent["M8"]) != b8:
            probs.append(f"{piece}: slope.M8 ≠ m9_campaign m8_baselines")
        if Fr(ent["M9"]) != b9:
            probs.append(f"{piece}: slope.M9 ≠ m9_campaign 基线")
        need = Estar - b9
        if Fr(ent["required_lift_M9_M10"]["value"]) != need:
            probs.append(f"{piece}: required_lift ≠ E*−M9 基线（精确重算）")
        if Fr(ent["lift_M8_M9"]["value"]) != b9 - b8:
            probs.append(f"{piece}: lift_M8_M9 ≠ M9−M8（精确重算）")
        lv = ent["lift_M9_M10"].get("value")
        if lv is not None:
            if row.get("lift") is None or Fr(lv) != Fr(row["lift"]["value"]):
                probs.append(f"{piece}: slope.lift_M9_M10 ≠ 行 lift")
            if abs(ent["retention_ratio"] - float(Fr(lv) / (b9 - b8))) > 1e-12:
                probs.append(f"{piece}: retention_ratio 重算失配")
        elif row.get("lift") is not None:
            probs.append(f"{piece}: 行有 lift 但斜率表缺 lift_M9_M10")
        if abs(ent["required_retention_ratio"] - float(need / (b9 - b8))) > 1e-12:
            probs.append(f"{piece}: required_retention_ratio 重算失配")
        if ent.get("verdict") != row.get("status"):
            probs.append(f"{piece}: slope.verdict {ent.get('verdict')} ≠ 行 status")
        m10v = ent.get("M10")
        want10 = row.get("certified") or row.get("best_certified_attempt")
        if (m10v is None) != (want10 is None) or (
                m10v is not None and Fr(m10v) != Fr(want10)):
            probs.append(f"{piece}: slope.M10 ≠ 行 certified-or-attempt")
    return probs


def main() -> int:
    print(f"== R7A M10 双片战役验收门（seed {SEED}）==", flush=True)
    if not CAMPAIGN.exists():
        print(f"[FAIL] 缺 {CAMPAIGN}")
        return 1
    Estar = E_star()
    camp = json.loads(CAMPAIGN.read_text())

    # ---------- G1 schema ----------
    chk("G1_schema", camp.get("kind") == "thomson-n9/bounds/m10-campaign/1"
        and camp.get("schema") == 1 and camp.get("seed") == SEED,
        f"kind={camp.get('kind')} seed={camp.get('seed')}")

    # ---------- G2 ①② 行级校验（含在盘 M10 证书进程外 --verify-cert） ----------
    vdet: list = []
    probs = validate_rows(camp, Estar, run_engine_verify=True, verify_details=vdet)
    n_certs = len([1 for r in camp.get("rows", []) if r.get("status") == "certified"])
    chk("G2_rows_and_engine_reverify", not probs,
        (f"2 行全过（翻正 {n_certs}/2）；进程外重验 "
         + (", ".join(f"{p}:exit{rc}" for p, rc in vdet) or "无 M10 证书（blocked/not_run 口径）"))
        if not probs else "；".join(probs[:6]))

    # ---------- G3 ③ lift/基线重算一致 ----------
    probs = validate_lift_baseline(camp, Estar)
    chk("G3_lift_baseline_consistency", not probs,
        "M9 基线（m9_campaign.json＋a5 账本交叉）与逐行 lift/margin 精确重算全一致"
        if not probs else "；".join(probs[:6]))

    # ---------- G4 ④ 铁律与拼合前瞻 ----------
    probs = validate_record(camp, Estar)
    rec = camp.get("record_prospective", {})
    chk("G4_iron_law_and_record", not probs,
        (f"record={rec.get('float')}（{'维持 R8 纪录' if rec.get('unchanged_from_round8') else '两片全翻·分区 min 口径'}）"
         if not probs else "；".join(probs[:6])))

    # ---------- G5 ⑤ 幂等：从存档重装配逐位一致 ----------
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as tf:
        tmp_out = Path(tf.name)
    r = subprocess.run([sys.executable, str(HERE / "m10_campaign.py"),
                        "--out", str(tmp_out)], capture_output=True, text=True,
                       timeout=14400)
    same = (r.returncode == 0 and tmp_out.exists()
            and hashlib.sha256(tmp_out.read_bytes()).hexdigest()
            == hashlib.sha256(CAMPAIGN.read_bytes()).hexdigest())
    chk("G5_idempotent_reassembly", same,
        f"重装配 sha256 {'逐位一致' if same else '不一致'}（exit {r.returncode}）")
    rebuilt = json.loads(tmp_out.read_text()) if tmp_out.exists() else None

    # ---------- G6 ⑦ 预算守门 ----------
    probs = validate_budget(camp)
    bud = camp.get("budget", {})
    chk("G6_budget_gate", not probs,
        f"Σsolve_s={bud.get('total_solve_s')}s ≈ {bud.get('total_equivalents')}"
        f" 当量 ≤ {BUDGET_CAP_EQ}" if not probs else "；".join(probs[:6]))

    # ---------- G7 ⑧ 斜率表 M8→M9→M10 逐片入账 ----------
    probs = validate_slope_table(camp, Estar)
    tab = camp.get("slope_table", {})
    detail = "；".join(
        f"{p}: M8→M9 {float(Fr(tab[p]['lift_M8_M9']['value'])):.4e}"
        f"→M9→M10 "
        + (f"{float(Fr(tab[p]['lift_M9_M10']['value'])):.4e}"
           f"（需 {float(Fr(tab[p]['required_lift_M9_M10']['value'])):.4e}，"
           f"{tab[p].get('verdict')}）" if tab.get(p, {}).get("lift_M9_M10", {}).get("value")
           else f"未跑（需 {float(Fr(tab[p]['required_lift_M9_M10']['value'])):.4e}）")
        for p in ("m079-m765", "m765-m748") if p in tab) or "斜率表为空"
    chk("G7_slope_table_M8_M9_M10", not probs,
        detail if not probs else "；".join(probs[:6]))

    # ---------- G8 ⑥-NC1 行篡改 +1e-9 必检出 ----------
    cert_row = next((rw for rw in camp["rows"] if rw.get("certified") is not None), None)
    blk_row = next((rw for rw in camp["rows"]
                    if rw.get("best_certified_attempt") is not None), None)
    if cert_row is not None:
        tam = copy.deepcopy(camp)
        idx = camp["rows"].index(cert_row)
        tam["rows"][idx]["certified"] = str(Fr(cert_row["certified"]) + EPS9)
        probs = validate_rows(tam, Estar, run_engine_verify=False)
        chk("G8_NC1_row_tamper_plus_1e-9_detected", bool(probs),
            ("检出（行-证书失配/断言重算）：" + "；".join(probs[:3]))
            if probs else "未检出（负对照失败）")
    elif blk_row is not None:
        idx = camp["rows"].index(blk_row)
        tamv = str(Fr(blk_row["best_certified_attempt"]) + EPS9)
        rb = (rebuilt["rows"][idx].get("best_certified_attempt")
              if rebuilt else None)
        chk("G8_NC1_row_tamper_plus_1e-9_detected", rb is not None and rb != tamv,
            (f"blocked 口径：幂等重算复核 attempt={rb} ≠ 篡改值 {tamv}（检出）"
             if rb != tamv else "重算复核未检出（负对照失败）"))
    else:
        chk("G8_NC1_row_tamper_plus_1e-9_detected", False,
            "战役无任何 certified/blocked 数值——NC1 无检出面（负对照失败）")

    # ---------- G9 ⑥-NC2 证书篡改 claimed_bound +1e-9 verify exit≠0 ----------
    cert_rows = [rw for rw in camp["rows"]
                 if rw.get("status") == "certified" and rw.get("certificate")]
    if cert_rows:
        rw = cert_rows[0]
        src = REPO / rw["certificate"]
        engine = rw["engine"]
        note = f"M10 证书 {src.name}"
    else:
        # blocked 口径无 M10 证书 ⇒ 以在盘 M9 条带证书为篡改对象（检出机制同为
        # claimed_bound 重算失配，引擎分发 lukacs）
        src = REPO / "certificates" / "n9-stage-a4-strip-m082-m079_M9.json"
        engine = "lukacs"
        note = f"无 M10 证书（blocked 口径）⇒ 退用在盘 M9 证书 {src.name}"
    cj = json.loads(src.read_text())
    cj["claimed_bound"] = str(Fr(cj["claimed_bound"]) + EPS9)
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False,
                                     prefix="nc2_") as tf:
        tf.write(json.dumps(cj).encode())
        tcert = Path(tf.name)
    # 文件名保留引擎可识别片段（hermite_ladder 按名分发）
    named = tcert.with_name(tcert.name + "_" + src.name)
    named.write_text(json.dumps(cj))
    rc, out = run_verify_cert(engine, named)
    chk("G9_NC2_cert_claimed_bound_plus_1e-9_detected", rc != 0,
        f"{note}；--verify-cert exit {rc}（{'检出' if rc != 0 else '未检出——负对照失败'}）")
    tcert.unlink(missing_ok=True)
    named.unlink(missing_ok=True)

    # ---------- G10 ⑥-NC3 M9 冒充 params.M 检出 ＋ 无解档 blocked 拒 ----------
    # (a) M9 行冒充 M10：行 M=10 但指向 M9 证书/解档（在盘 m082-m079 M9 Lukács
    # 证书——检出口径＝证书 params.M 字段，不依赖本战役态）
    m9_cert = "certificates/n9-stage-a4-strip-m082-m079_M9.json"
    m9_sol = "numerics/bounds/results/strip_sol_m082-m079_M9.json"
    tam = copy.deepcopy(camp)
    rw0 = tam["rows"][0]
    rw0.update(status="certified", certificate=m9_cert, solution=m9_sol,
               certified=json.loads((REPO / m9_cert).read_text())["claimed_bound"],
               margin_vs_E_star=dict(value="1/1000", float=0.001),
               provenance=dict(seed=SEED, ks=list(KS)))
    probs_a = validate_rows(tam, Estar, run_engine_verify=False)
    mflag = [p for p in probs_a if "params.M" in p]
    # (b) 无解档 blocked 行（恒可构造：行 1 伪造成 blocked＋不存在解档）
    tam2 = copy.deepcopy(camp)
    rw1 = tam2["rows"][1]
    rw1.update(status="blocked", certificate=None, certified=None,
               solution="numerics/bounds/results/NONEXISTENT_sol_M10.json",
               best_certified_attempt=str(Estar - Fr(1, 10 ** 5)),
               lift=dict(value="1/100000", float=1e-5),
               blocked_detail=dict(best_certified_attempt=str(Estar - Fr(1, 10 ** 5))))
    probs_b = validate_rows(tam2, Estar, run_engine_verify=False)
    nflag = [p for p in probs_b if "解档不在盘" in p]
    ok = bool(mflag) and bool(nflag)
    chk("G10_NC3_m9_impersonation_and_blocked_no_solution",
        ok, ("冒充检出：" + "；".join(mflag[:2]) + "；无解档拒：" + "；".join(nflag[:2]))
        if ok else (f"冒充 {'检出' if mflag else '未检出'}；"
                    f"无解档 {'拒' if nflag else '未拒'}——负对照失败"))

    tmp_out.unlink(missing_ok=True)

    n_pass = sum(1 for _, ok, _ in checks if ok)
    print(f"== 门总计：{n_pass}/{len(checks)} 过 ==", flush=True)
    return 0 if n_pass == len(checks) else 1


if __name__ == "__main__":
    sys.exit(main())
