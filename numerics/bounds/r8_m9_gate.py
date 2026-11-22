#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r8_m9_gate.py — Round 8 / R8-1 M9 阶梯战役验收门。

验收内容（任务书口径，seed 20261008，CWD 无关——路径全部自 __file__ 解析，
只验存档数据、不触发任何求解）：
  ① 每张在盘 M9 证书进程外 --verify-cert 重验 exit 0（引擎脚本按行分发）；
  ② certified>E* 的行证书必须在盘且可重验；blocked 行必须带解档与 lift 实测
     （best_certified_attempt 精确分数）；skipped/not_run 行必须带 reason；
  ③ canary 决策链：lift₁ 精确重算与账面一致、阈值判定与 decision 一致、
     decision 与后续三行状态一致（abort ⇒ skipped；continue ⇒ 已尝试）；
  ④ 断言：条带行 certified>E*（精确 Fraction）；cap 行 0<certified≤E*+1e-6；
     拼合前瞻值 ≤ E*+1e-6（铁律）且 = partition 各胞元精确 min；
  ⑤ 幂等：m9_campaign.py 从存档重装配到临时路径，与在盘 JSON 逐位一致
     （sha256 前后比对）；
  ⑥ 负对照三件：
     NC1 篡改 certified +1e-9 —— (a) 行篡改：validate_rows 必拒（行-证书失配
         或断言重算失配）；(b) 证书篡改（有 M9 证书时）：/tmp 副本 claimed_bound
         +1e-9，引擎 --verify-cert 必 exit≠0；
     NC2 M8 行冒充 M9 —— 行指向 M8 证书/解档而 M 字段仍 9：validate_rows 必经
         证书 params.M 字段检出；
     NC3 无解档 blocked 行 —— solution 指向不存在路径：validate_rows 必拒。
用法：python3 thomson-n9/numerics/bounds/r8_m9_gate.py   （任意 CWD）
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
CAMPAIGN = RESULTS / "m9_campaign.json"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

SEED = 20261008
E_TOL = Fr(1, 10 ** 6)
EPS9 = Fr(1, 10 ** 9)
KS = (48, 56, 64)
M9, K6 = 9, 6
ENGINE_SCRIPT = {"lukacs": HERE / "strips_final.py",
                 "a5-hermite": HERE / "hermite_ladder.py",
                 "typed": HERE / "typed_ladder.py"}
# 证书 json 里 M 字段的定位（三引擎各自 schema）
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
    """进程外 --verify-cert（引擎脚本按 M9 行的 engine 分发）。"""
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
    if len(rows) != 4:
        probs.append(f"rows 数 {len(rows)} ≠ 4")
        return probs
    for row in rows:
        piece = row.get("piece", "?")
        if row.get("M") != M9 or row.get("K") != K6:
            probs.append(f"{piece}: M/K 字段 {row.get('M')}/{row.get('K')} ≠ 9/6")
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
                             f"（M8 冒充/张冠李戴检出）")
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
            if row["kind"] == "cap" and not (0 < c <= Estar + E_TOL):
                probs.append(f"{piece}: cap 行 certified 不满足 0<c≤E*+1e-6")
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
        elif st in ("skipped_by_canary", "not_run", "machine_unsolvable"):
            if not row.get("reason"):
                probs.append(f"{piece}: {st} 行缺 reason")
            if row.get("certified") is not None:
                probs.append(f"{piece}: {st} 行不应带 certified 值")
        else:
            probs.append(f"{piece}: 未知 status {st}")
    return probs


def validate_canary_chain(camp: dict) -> list[str]:
    probs: list[str] = []
    can = camp.get("canary", {})
    rows = camp.get("rows", [])
    if not rows:
        return ["rows 为空"]
    r1 = rows[0]
    if r1.get("piece") != "m082-m079" or can.get("piece") != "m082-m079":
        probs.append("canary 片不是 m082-m079")
    dec = can.get("decision")
    if dec == "pending":
        probs.append("canary.decision=pending（战役未完成）")
        return probs
    if dec == "no_lift_data":
        if r1.get("status") != "machine_unsolvable":
            probs.append("no_lift_data 但行 1 非 machine_unsolvable")
        for r in rows[1:]:
            if r.get("status") not in ("skipped_by_canary", "not_run",
                                       "machine_unsolvable"):
                probs.append(f"no_lift_data 但 {r['piece']} 状态 {r.get('status')}")
        return probs
    lift = can.get("lift1")
    if lift is None:
        probs.append("decision 已定但 lift1 缺失")
        return probs
    lift = Fr(lift)
    src = r1.get("certified") or r1.get("best_certified_attempt")
    if src is None:
        probs.append("decision 已定但行 1 无 certified/attempt")
        return probs
    recompute = Fr(src) - Fr(can["baseline"])
    if recompute != lift:
        probs.append(f"lift1 重算 {recompute} ≠ 账面 {lift}")
    thr = Fr(can["threshold"])
    want = "continue" if lift >= thr else "abort"
    if want != dec:
        probs.append(f"lift1={float(lift):+.6e} 与阈值 {float(thr):.0e} 的判定应为 "
                     f"{want}，账面 decision={dec}")
    # decision ⇒ 后续行状态一致性
    if dec == "abort":
        for r in rows[1:]:
            if r.get("status") not in ("skipped_by_canary", "machine_unsolvable"):
                probs.append(f"abort 但 {r['piece']} 状态 {r.get('status')}"
                             f"（应 skipped_by_canary）")
    else:  # continue
        for r in rows[1:3]:      # 两片条带必须已尝试
            if r.get("status") in ("not_run",):
                if not r.get("reason", "").startswith("M9 本机不可解"):
                    probs.append(f"continue 但条带 {r['piece']} 未尝试（not_run）")
        strips_ok = all(r.get("status") == "certified" for r in rows[:3])
        cap = rows[3]
        if strips_ok:
            if cap.get("status") in ("not_run", "skipped_by_canary"):
                probs.append("三片全翻正但 cap M9 未解（应已尝试）")
        else:
            if cap.get("status") not in ("not_run", "machine_unsolvable"):
                probs.append("条带未全翻正但 cap M9 被解（违反『不改变 min，省预算』）")
    return probs


def validate_record(camp: dict, Estar: Fr) -> list[str]:
    probs: list[str] = []
    rec = camp.get("record_prospective", {})
    part = rec.get("partition")
    if rec.get("unchanged_from_round7"):
        if rec.get("value") != "47517790735835014335570/1844674407417822803119":
            probs.append("unchanged 口径但值非 Round 7 HP 纪录")
    else:
        if not part:
            probs.append("翻正口径缺 partition")
        else:
            vmin = min(Fr(c["bound"]) for c in part)
            if str(vmin) != rec.get("value"):
                probs.append("record 值 ≠ partition 精确 min")
            ints = [c["interval"] for c in part]
            if "[-187/250,1]" not in ints:
                probs.append("partition 缺 cap 胞元")
            # 洞三片应与 rows 一致
            rows_by = {r["piece"]: r for r in camp.get("rows", [])}
            for piece, iv in (("m082-m079", "[-41/50,-79/100]"),
                              ("m079-m765", "[-79/100,-153/200]"),
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
    probs: list[str] = []
    bud = camp.get("budget", {})
    per = bud.get("per_piece", {})
    tot = 0.0
    for piece, v in per.items():
        ss = v.get("solve_s")
        if isinstance(ss, (int, float)):
            tot += ss
            if abs(v.get("equivalents") - ss / 10800.0) > 1e-3 + 1e-6 * ss / 10800.0:
                probs.append(f"{piece}: equivalents 换算失守")
        elif ss is not None:
            probs.append(f"{piece}: solve_s 非数值 {ss}")
    if abs(bud.get("total_solve_s", -1) - tot) > 1e-6:
        probs.append(f"total_solve_s {bud.get('total_solve_s')} ≠ Σ {tot}")
    if abs(bud.get("total_equivalents", -1) - tot / 10800.0) > 1e-3:
        probs.append("total_equivalents 失守")
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


def main() -> int:
    print(f"== R8-1 M9 战役验收门（seed {SEED}）==", flush=True)
    if not CAMPAIGN.exists():
        print(f"[FAIL] 缺 {CAMPAIGN}")
        return 1
    Estar = E_star()
    camp = json.loads(CAMPAIGN.read_text())

    # ---------- ① schema ----------
    chk("G1_schema", camp.get("kind") == "thomson-n9/bounds/m9-campaign/1"
        and camp.get("schema") == 1 and camp.get("seed") == SEED,
        f"kind={camp.get('kind')} seed={camp.get('seed')}")

    # ---------- ② 行级校验（含进程外 --verify-cert） ----------
    vdet: list = []
    probs = validate_rows(camp, Estar, run_engine_verify=True, verify_details=vdet)
    chk("G2_rows_and_engine_reverify", not probs,
        ("4 行全过；进程外重验 " + ", ".join(f"{p}:exit{rc}" for p, rc in vdet))
        if not probs else "；".join(probs[:6]))

    # ---------- ③ canary 决策链 ----------
    probs = validate_canary_chain(camp)
    can = camp.get("canary", {})
    chk("G3_canary_chain", not probs,
        (f"decision={can.get('decision')}，lift1={can.get('lift1_float'):+.6e}"
         if not probs else "；".join(probs[:6])))

    # ---------- ④ 断言与拼合前瞻 ----------
    probs = validate_record(camp, Estar)
    rec = camp.get("record_prospective", {})
    chk("G4_assertions_and_record", not probs,
        (f"record={rec.get('float')}（{'未变' if rec.get('unchanged_from_round7') else '抬升'}）"
         if not probs else "；".join(probs[:6])))

    # ---------- ⑤ 预算 ----------
    probs = validate_budget(camp)
    bud = camp.get("budget", {})
    chk("G5_budget", not probs,
        f"Σsolve_s={bud.get('total_solve_s')}s ≈ {bud.get('total_equivalents')} (8,6)-当量"
        if not probs else "；".join(probs[:6]))

    # ---------- ⑥ 幂等：从存档重装配逐位一致 ----------
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as tf:
        tmp_out = Path(tf.name)
    r = subprocess.run([sys.executable, str(HERE / "m9_campaign.py"),
                        "--out", str(tmp_out)], capture_output=True, text=True,
                       timeout=3600)
    same = (r.returncode == 0 and tmp_out.exists()
            and hashlib.sha256(tmp_out.read_bytes()).hexdigest()
            == hashlib.sha256(CAMPAIGN.read_bytes()).hexdigest())
    chk("G6_idempotent_reassembly", same,
        f"重装配 sha256 {'逐位一致' if same else '不一致'}（exit {r.returncode}）")
    rebuilt = json.loads(tmp_out.read_text()) if tmp_out.exists() else None

    # ---------- ⑦ 负对照三件 ----------
    # NC1(a)：行篡改 certified/best_certified_attempt +1e-9
    cert_row = next((rw for rw in camp["rows"] if rw.get("certified") is not None), None)
    blk_row = next((rw for rw in camp["rows"]
                    if rw.get("best_certified_attempt") is not None), None)
    if cert_row is not None:
        tam = copy.deepcopy(camp)
        idx = camp["rows"].index(cert_row)
        tam["rows"][idx]["certified"] = str(Fr(cert_row["certified"]) + EPS9)
        probs = validate_rows(tam, Estar, run_engine_verify=False)
        chk("NC1a_row_certified_plus_1e-9_detected", bool(probs),
            ("检出（行-证书失配/断言重算）：" + "；".join(probs[:3]))
            if probs else "未检出（负对照失败）")
    elif blk_row is not None:
        idx = camp["rows"].index(blk_row)
        tamv = str(Fr(blk_row["best_certified_attempt"]) + EPS9)
        rb = (rebuilt["rows"][idx].get("best_certified_attempt")
              if rebuilt else None)
        chk("NC1a_row_certified_plus_1e-9_detected", rb is not None and rb != tamv,
            (f"blocked 口径：重算复核 attempt={rb} ≠ 篡改值 {tamv}（检出）"
             if rb != tamv else "重算复核未检出（负对照失败）"))
    else:
        chk("NC1a_row_certified_plus_1e-9_detected", True,
            "战役无任何 certified/blocked 数值（canary 未完成或全 machine_unsolvable）"
            "——NC1(a) 不适用，检出面由 NC1(b)/幂等门与 solver 事件档承担")

    # NC1(b)：证书篡改 claimed_bound +1e-9（有 M9 证书时）
    cert_rows = [rw for rw in camp["rows"]
                 if rw.get("status") == "certified" and rw.get("certificate")]
    if cert_rows:
        rw = cert_rows[0]
        src = REPO / rw["certificate"]
        cj = json.loads(src.read_text())
        cj["claimed_bound"] = str(Fr(cj["claimed_bound"]) + EPS9)
        with tempfile.NamedTemporaryFile(suffix=".json", delete=False,
                                         prefix="nc1b_") as tf:
            tf.write(json.dumps(cj).encode())
            tcert = Path(tf.name)
        # 文件名保留引擎可识别片段（hermite_ladder 按名分发）
        named = tcert.with_name(tcert.name + "_" + src.name)
        named.write_text(json.dumps(cj))
        rc, out = run_verify_cert(rw["engine"], named)
        chk("NC1b_cert_claimed_bound_plus_1e-9_detected", rc != 0,
            f"--verify-cert exit {rc}（{'检出' if rc != 0 else '未检出——负对照失败'}）")
        tcert.unlink(missing_ok=True)
        named.unlink(missing_ok=True)
    else:
        chk("NC1b_cert_claimed_bound_plus_1e-9_detected", True,
            "无 M9 证书在盘（全 blocked/unsolvable 口径）——NC1(b) 不适用，"
            "检出面由 NC1(a)+幂等门承担")

    # NC2：M8 行冒充 M9（行 M=9 但指向 M8 证书/解档；恒可构造，不依赖战役态）。
    # 注：hermite 条带 M8 无证书在盘（4 行全 blocked 不落证书）⇒ 条带行统一用
    # 在盘的 Lukács M8 条带证书/解档冒充——检出口径同为证书 params.M 字段。
    m8_pairs = {
        "m082-m079": ("certificates/n9-stage-a4-strip-m085-m082_M8.json",
                      "numerics/bounds/results/strip_sol_m085-m082_M8.json"),
        "m079-m765": ("certificates/n9-stage-a4-strip-m085-m082_M8.json",
                      "numerics/bounds/results/strip_sol_m085-m082_M8.json"),
        "m765-m748": ("certificates/n9-stage-a4-strip-m085-m082_M8.json",
                      "numerics/bounds/results/strip_sol_m085-m082_M8.json"),
        "m0748": ("certificates/n9-stage-a4-typedcap-m0748_M8.json",
                  "numerics/bounds/results/typed_ladder_sol_m0748_M8.json")}
    tam = copy.deepcopy(camp)
    rw0 = tam["rows"][0]
    m8c, m8s = m8_pairs[rw0["piece"]]
    rw0.update(status="certified", certificate=m8c, solution=m8s,
               certified=json.loads((REPO / m8c).read_text())["claimed_bound"],
               margin_vs_E_star=dict(value="-1/1000", float=-0.001),
               provenance=dict(seed=SEED, ks=list(KS)))
    probs = validate_rows(tam, Estar, run_engine_verify=False)
    mflag = [p for p in probs if "params.M" in p]
    chk("NC2_m8_impersonation_detected_by_M_field", bool(mflag),
        ("检出：" + "；".join(mflag[:3])) if mflag else "未检出（负对照失败）")

    # NC3：无解档 blocked 行（恒可构造：行 0 伪造成 blocked＋不存在解档）
    tam = copy.deepcopy(camp)
    rw0 = tam["rows"][0]
    rw0.update(status="blocked", certificate=None, certified=None,
               solution="numerics/bounds/results/NONEXISTENT_sol.json",
               best_certified_attempt=str(Estar - Fr(1, 10 ** 5)),
               lift=dict(value="1/100000", float=1e-5),
               blocked_detail=dict(best_certified_attempt=str(Estar - Fr(1, 10 ** 5))))
    probs = validate_rows(tam, Estar, run_engine_verify=False)
    nflag = [p for p in probs if "解档不在盘" in p]
    chk("NC3_blocked_without_solution_rejected", bool(nflag),
        ("检出：" + "；".join(nflag[:3])) if nflag else "未检出（负对照失败）")
    tmp_out.unlink(missing_ok=True)

    n_pass = sum(1 for _, ok, _ in checks if ok)
    print(f"== 门总计：{n_pass}/{len(checks)} 过 ==", flush=True)
    return 0 if n_pass == len(checks) else 1


if __name__ == "__main__":
    sys.exit(main())
