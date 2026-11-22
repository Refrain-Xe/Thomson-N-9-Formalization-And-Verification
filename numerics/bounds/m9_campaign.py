#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""m9_campaign.py — R8-1 M9 阶梯战役汇总器（schema thomson-n9/bounds/m9-campaign/1）。

## 职责与纪律

从**存档数据**（解档 json / strips.json / hermite_strips.json / typed_ladder.json /
endgame.json / 证书 json）纯装配 results/m9_campaign.json：
  - 不触发任何求解（求解由 strips_final/hermite_ladder/typed_ladder 的正式入口
    后台完成，本脚本只读它们的产出）；
  - 不含墙钟时间戳、不含本脚本自身 code_version ⇒ **幂等**：同一存档状态重跑
    逐字节一致（r8_m9_gate.py 的 G5 以 sha256 前后比对逐位核验）。各行的
    code_version/命令/粒度取自**存档 provenance 原文**（生成时刻的记录），不随
    后续提交漂移。
  - blocked 行（条带正裕度断言失败的 Lukács 片，strips_final fail() 不落账本行）：
    本脚本从解档**离线重算** best_certified_attempt——调 slab_band.certify_slab
    传 E_star=0（关掉末尾正裕度断言，其余认证链照跑：e−膨胀>0、抽查、
    certified≤e+1e-9），对 ks=48/56/64 各算一次取最大（粗粒度舍入只损失），
    精确 Fraction 入账。重算确定性（固定 spot 种子 97531+k）⇒ 幂等成立。

## 行口径（D19 裁决 2：引擎按 M8 逐片最优）

  m082-m079  Lukács strips_final.py  （M8 上高于 a5 +7.47e-5）
  m079-m765  Lukács strips_final.py  （M8 上高于 a5 +6.41e-5）
  m765-m748  a5     hermite_ladder.py（M8 上高于 Lukács-M7 +7.45e-4，k_minor=48）
  m0748 cap  typed  typed_ladder.py  （M8 上高于 a5 +1.31e-5；条带不翻正则不解）

canary 条款：lift₁ = certified(m082-m079 M9) − 25.759782985769（M8 Lukács 最优，
Round 7 账面 best_certified_attempt，GAP-REPORT.md:1313）；lift₁ ≥ +1/10000 才继续
后续求解，否则中止（斜率标定本身入账）。

用法：
  python3 numerics/bounds/m9_campaign.py [--out results/m9_campaign.json]
                                          [--skip-blocked-recompute]
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = HERE / "results"
CERTS = REPO / "certificates"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[2] / "thomson-workflow" / "certificates"))

SEED = 20261008
KS = (48, 56, 64)
K_MINOR = 48
M9, K6 = 9, 6
LIFT_THRESHOLD = Fr(1, 10 ** 4)
E_TOL = Fr(1, 10 ** 6)
# (8,6)-当量换算：1 当量 = 一次 (8,6) 档求解的典型墙钟 10800s（3h；实测 M8
# Lukács 条带 10044–10120s、typed cap 11793s、hermite 条带 4962s）。
EQUIV_UNIT_S = 10800.0

# Round 7 账面 M8 Lukács best_certified_attempt（认证失败未落证书，15 位账面值；
# GAP-REPORT.md:1313-1314）。作精确十进 Fraction 用（与任务书 lift₁ 定义一致）。
M8_LEDGER = {
    "m082-m079": "25.759782985769",
    "m079-m765": "25.759535741156",
}

PIECES = [
    dict(piece="m082-m079", kind="strip", engine="lukacs", lo="-41/50", hi="-79/100",
         cmd=(f'numerics/.venv/bin/python numerics/bounds/strips_final.py '
              f'--strip="-0.82:-0.79" --M 9 --ks 48 56 64'),
         sol=RESULTS / "strip_sol_m082-m079_M9.json",
         db=(RESULTS / "strips.json", "strips", "tag", "m082-m079"),
         cert=CERTS / "n9-stage-a4-strip-m082-m079_M9.json",
         verify=("strips_final.py", "--verify-cert"),
         baseline=("lukacs", M8_LEDGER["m082-m079"],
                   "GAP-REPORT.md:1313（Round 7 账面 best_certified_attempt，无存档证书）")),
    dict(piece="m079-m765", kind="strip", engine="lukacs", lo="-79/100", hi="-153/200",
         cmd=(f'numerics/.venv/bin/python numerics/bounds/strips_final.py '
              f'--strip="-0.79:-0.765" --M 9 --ks 48 56 64'),
         sol=RESULTS / "strip_sol_m079-m765_M9.json",
         db=(RESULTS / "strips.json", "strips", "tag", "m079-m765"),
         cert=CERTS / "n9-stage-a4-strip-m079-m765_M9.json",
         verify=("strips_final.py", "--verify-cert"),
         baseline=("lukacs", M8_LEDGER["m079-m765"],
                   "GAP-REPORT.md:1314（Round 7 账面 best_certified_attempt，无存档证书）")),
    dict(piece="m765-m748", kind="strip", engine="a5-hermite", lo="-153/200", hi="-187/250",
         cmd=(f'python3 numerics/bounds/hermite_ladder.py --strip="-0.765:-0.748" '
              f'--M 9 --ks 48 56 64 --k-minor 48'),
         sol=RESULTS / "hermite_strip_sol_m765-m748_M9.json",
         db=(RESULTS / "hermite_strips.json", "strips", "tag", "m765-m748"),
         cert=CERTS / "n9-stage-a5-hermite-strip-m765-m748_M9.json",
         verify=("hermite_ladder.py", "--verify-cert"),
         baseline=None),      # 运行时自 hermite_strips.json M8 行读精确分数
    dict(piece="m0748", kind="cap", engine="typed", lo="-187/250", hi="1",
         cmd=(f'numerics/.venv/bin/python numerics/bounds/typed_ladder.py '
              f'--rung -0.748 --M 9 --ks 48 56 64'),
         sol=RESULTS / "typed_ladder_sol_m0748_M9.json",
         db=(RESULTS / "typed_ladder.json", "rungs", "tag", "m0748"),
         cert=CERTS / "n9-stage-a4-typedcap-m0748_M9.json",
         verify=("typed_ladder.py", "--verify-cert"),
         baseline=None),      # 运行时自 typed_ladder.json m0748 M8 行读精确分数
]


def load_E_star() -> Fr:
    return Fr(str(json.loads(WORKFLOW_DATA.read_text())["energies"]["9"]["value"]))


def rel(p: Path) -> str:
    return str(p.relative_to(REPO))


def db_rows(db_path: Path, key: str, tag_field: str, tag: str) -> dict:
    """账本 json 中 tag 匹配、M=9 与 M=8 的行（按需取用）。"""
    out = {}
    if db_path.exists():
        db = json.loads(db_path.read_text())
        for r in db.get(key, []):
            if r.get(tag_field) == tag:
                out[r.get("M")] = r
    return out


def solver_events() -> list:
    p = RESULTS / "m9_solver_events.json"
    if p.exists():
        return json.loads(p.read_text()).get("events", [])
    return []


def blocked_attempt_lukacs(sol_path: Path, piece: str) -> dict:
    """Lukács blocked 片的 best_certified_attempt 离线重算（E_star=0 关末尾断言）。

    其余认证链照跑（e−膨胀>0／域抽查／certified≤e+1e-9），ks=48/56/64 全算取
    最大——「舍入只损失」⇒ 最粗粒度最先失败时细粒度仍是有效下界尝试。
    """
    from slab_band import TypedCore, LamMaps, certify_slab
    from strips_final import sol_to_certify_input
    sol_js = json.loads(sol_path.read_text())
    core = TypedCore(9, M9, K6)
    lm = LamMaps(core, Fr(sol_js["lo"]), Fr(sol_js["hi"]))
    sol = sol_to_certify_input(sol_js)
    attempts = {}
    for k in KS:
        try:
            cd = certify_slab(core, lm, sol, k, Fr(0), f"{piece}/M9-blocked")
        except SystemExit as exc:
            attempts[k] = dict(ok=False, why=f"exit {exc.code}")
            continue
        attempts[k] = dict(ok=True, certified=str(cd["certified"]),
                           certified_float=float(cd["certified"]),
                           R1={w: str(v) for w, v in cd["R1"].items()},
                           R2={X: str(v) for X, v in cd["R2"].items()},
                           deflation=str(cd["deflation"]),
                           R2max=str(cd["R2max"]))
    oks = [a for a in attempts.values() if a.get("ok")]
    if not oks:
        return dict(attempts={str(k): a for k, a in attempts.items()},
                    best_certified_attempt=None)
    best = max(oks, key=lambda a: Fr(a["certified"]))
    return dict(attempts={str(k): a for k, a in attempts.items()},
                best_certified_attempt=best["certified"],
                best_certified_attempt_float=best["certified_float"],
                best_k=int(max((k for k, a in attempts.items() if a.get("ok")
                                and a["certified"] == best["certified"]))),
                method=("slab_band.certify_slab(E_star=0)（关正裕度断言，其余链照跑）"
                        "，ks=48/56/64 全算取最大，精确 Fraction"))


def build(skip_blocked_recompute: bool = False) -> dict:
    E_star = load_E_star()
    ev_by_piece = {}
    for e in solver_events():
        ev_by_piece.setdefault(e["piece"], []).append(e)

    # ---- M8 基线（a5/typed 自账本精确分数；Lukács 自 Round 7 账面） ----
    hs_rows = db_rows(RESULTS / "hermite_strips.json", "strips", "tag", "m765-m748")
    tl_rows = db_rows(RESULTS / "typed_ladder.json", "rungs", "tag", "m0748")
    baselines = {}
    for p in PIECES:
        if p["baseline"] is not None:
            eng, val, src = p["baseline"]
        elif p["engine"] == "a5-hermite":
            r8 = hs_rows.get(8)
            eng, val, src = "a5-hermite", r8["certified"], \
                "results/hermite_strips.json（M8 行，精确分数）"
        else:
            r8 = tl_rows.get(8)
            eng, val, src = "typed", r8["certified"], \
                "results/typed_ladder.json（m0748 M8 行，精确分数）"
        baselines[p["piece"]] = dict(engine=eng, certified=val,
                                     certified_float=float(Fr(val)),
                                     source=src)

    rows, canary = [], dict(
        piece="m082-m079", engine="lukacs",
        baseline=baselines["m082-m079"]["certified"],
        baseline_float=baselines["m082-m079"]["certified_float"],
        threshold=str(LIFT_THRESHOLD), threshold_float=float(LIFT_THRESHOLD),
        rule="lift1 = certified(M9) − baseline ≥ +1/10000 ⇒ 继续；否则中止后续求解",
        decision="pending", lift1=None, lift1_float=None)

    for p in PIECES:
        rows_m = db_rows(p["db"][0], p["db"][1], p["db"][2], p["db"][3])
        r9 = rows_m.get(M9)
        sol_exists = p["sol"].exists()
        events = ev_by_piece.get(p["piece"], [])
        # 账本行可用条件：a5/typed 的 blocked/certured 行都落账（status 字段）；
        # Lukács 账本行只含成功行——另须证书在盘佐证。
        db_usable = r9 is not None and (
            p["engine"] != "lukacs" or p["cert"].exists())
        row = dict(piece=p["piece"], kind=p["kind"], engine=p["engine"],
                   lo=p["lo"], hi=p["hi"], M=M9, K=K6,
                   assertion=("certified>E*" if p["kind"] == "strip"
                              else "0<certified<=E*+1e-6"),
                   cmd=p["cmd"])
        if db_usable:
            status = r9.get("status", "certified")
            certified = Fr(r9["certified"])
            row.update(status=status, e_raw=r9.get("e_raw"),
                       certified=r9["certified"], certified_float=float(certified),
                       round_bits=r9.get("round_bits"),
                       minorant_k=r9.get("minorant_k", K_MINOR
                                         if p["engine"] == "a5-hermite" else None),
                       certificate=rel(p["cert"]) if p["cert"].exists() else None,
                       solution=rel(p["sol"]) if sol_exists else None,
                       solve_s=(r9.get("sdpa") or {}).get("solve_s"),
                       sdpa={kk: (r9.get("sdpa") or {}).get(kk)
                             for kk in ("phase_value", "iteration", "stalled_point",
                                        "mu", "relative_gap", "p_feas_error",
                                        "d_feas_error", "reused", "solve_s")},
                       provenance=dict(seed=SEED, code_version=r9.get("code_version"),
                                       ks=list(KS)))
        elif sol_exists:
            # 解在盘、账本无成功行 ⇒ Lukács blocked（a5 的 blocked 行走上面分支）
            row.update(status="blocked", solution=rel(p["sol"]),
                       solve_s=(json.loads(p["sol"].read_text())
                                .get("solver_info", {}).get("solve_s")),
                       certificate=None)
            sol_js = json.loads(p["sol"].read_text())
            si = sol_js.get("solver_info", {})
            row["sdpa"] = {kk: si.get(kk) for kk in
                           ("phase_value", "iteration", "stalled_point", "mu",
                            "relative_gap", "p_feas_error", "d_feas_error",
                            "reused", "solve_s")}
            row["provenance"] = dict(seed=SEED, code_version=sol_js.get("code_version"),
                                     ks=list(KS))
            row["e_raw"] = sol_js.get("e")
            if p["engine"] == "lukacs":
                if skip_blocked_recompute:
                    row["blocked_detail"] = dict(
                        best_certified_attempt=None,
                        method="skipped (--skip-blocked-recompute)")
                else:
                    row["blocked_detail"] = blocked_attempt_lukacs(
                        p["sol"], p["piece"])
            else:
                row["blocked_detail"] = dict(
                    best_certified_attempt=None,
                    method="a5 blocked 行由 hermite_strips.json 落账（本分支不应出现）")
        else:
            if any(e["event"] == "unsolvable" for e in events):
                reason = "M9 本机不可解（回退链三步皆败，见 m9_solver_events.json）"
                status = "machine_unsolvable"
            elif canary["decision"] == "abort":
                reason = "canary lift1 < +1/10000 ⇒ 按条款中止（斜率标定入账）"
                status = "skipped_by_canary"
            elif canary["decision"] == "no_lift_data":
                reason = "canary 无数据（M9 本机不可解）⇒ 后续不解"
                status = "skipped_by_canary"
            elif p["kind"] == "cap":
                reason = "前置条带未全翻正 ⇒ cap 不解（不改变拼合 min，省预算）"
                status = "not_run"
            else:
                reason = "未排／未启动"
                status = "not_run"
            row.update(status=status, e_raw=None, certified=None,
                       certified_float=None, certificate=None, solution=None,
                       solve_s=None, sdpa=None,
                       provenance=dict(seed=SEED, ks=list(KS)),
                       reason=reason)
        # margins（精确 Fraction）；blocked 行统一以 best_certified_attempt 入账
        attempt = None
        if row.get("certified") is not None:
            attempt = Fr(row["certified"])
        elif row["status"] == "blocked":
            ba = (row.get("blocked_detail") or {}).get("best_certified_attempt")
            if ba is not None:
                attempt = Fr(ba)
                row["best_certified_attempt"] = ba
                row["best_certified_attempt_float"] = float(attempt)
        if attempt is not None:
            if row["status"] == "blocked" and row.get("certified") is not None:
                # a5 blocked 行：certified 字段即 best attempt（hermite_strips.json）
                row["best_certified_attempt"] = row["certified"]
                row["best_certified_attempt_float"] = float(attempt)
            row["margin_vs_E_star"] = dict(value=str(attempt - E_star),
                                           float=float(attempt - E_star))
            b = Fr(baselines[p["piece"]]["certified"])
            row["lift"] = dict(value=str(attempt - b), float=float(attempt - b))
            row["margin_vs_m8_best"] = row["lift"]
        rows.append(row)
        if p["piece"] == "m082-m079":
            c1 = rows[0].get("certified") or rows[0].get("best_certified_attempt")
            if c1 is not None:
                lift1 = Fr(c1) - Fr(canary["baseline"])
                canary.update(decision=("continue" if lift1 >= LIFT_THRESHOLD
                                        else "abort"),
                              lift1=str(lift1), lift1_float=float(lift1),
                              certified_source=("certified" if rows[0]["certified"]
                                                else "best_certified_attempt"))
            elif rows[0]["status"] == "machine_unsolvable":
                canary.update(decision="no_lift_data",
                              note="canary 片 M9 本机不可解 ⇒ 无 M8→M9 斜率数据")

    # ---- 拼合前瞻（provisional；正式 assembledRecord 归 endgame_chain/R8-4） ----
    eg = json.loads((RESULTS / "endgame.json").read_text())
    part = [dict(interval=pz["region"], bound=pz["bound"]) for pz in eg["partition"]]
    strip_rows = [r for r in rows if r["kind"] == "strip"]
    all_flipped = all(r["status"] == "certified" for r in strip_rows)
    cap_row = next(r for r in rows if r["kind"] == "cap")
    record = dict(
        note=("provisional——正式 assembledRecord 由 endgame_chain.py（R8-4 收口）"
              "按证书口径重判；本字段只做战役侧前瞻，口径＝10 原子区域取 min、"
              "洞片以 M9 证书替换 HP 兜底（三片全翻时）、cap 片取 M9（已认证时）"),
        all_three_strips_flipped=all_flipped)
    if all_flipped:
        hole_pieces = []
        for r in strip_rows:
            hole_pieces.append(dict(interval=f"[{r['lo']},{r['hi']}]",
                                    bound=r["certified"],
                                    source=f"certificates/{r['certificate'].split('/')[-1]}"
                                    if r.get("certificate") else None))
        others = [pz for pz in part if pz["interval"] not in
                  ("[-41/50,-187/250]", "[-187/250,1]")]
        cap_bound = (cap_row["certified"] if cap_row["status"] == "certified"
                     else [pz for pz in part if pz["interval"] == "[-187/250,1]"][0]["bound"])
        cells = others + [dict(interval=hp["interval"], bound=hp["bound"],
                               source=hp.get("source")) for hp in hole_pieces] + \
            [dict(interval="[-187/250,1]", bound=cap_bound,
                  source=("certificates/n9-stage-a4-typedcap-m0748_M9.json"
                          if cap_row["status"] == "certified"
                          else "certificates/n9-stage-a4-typedcap-m0748_M8.json"))]
        vmin = min(Fr(c["bound"]) for c in cells)
        bott = [c for c in cells if Fr(c["bound"]) == vmin]
        record.update(partition=[dict(interval=c["interval"],
                                      bound=c["bound"],
                                      bound_float=float(Fr(c["bound"])),
                                      source=c.get("source")) for c in cells],
                      value=str(vmin), float=float(vmin),
                      margin_vs_E_star=float(vmin - E_star),
                      bottleneck="；".join(b["interval"] for b in bott),
                      unchanged_from_round7=False)
    else:
        cur = eg["assembledRecord"]
        record.update(value=cur["value"], float=cur["float"],
                      margin_vs_E_star=float(Fr(cur["value"]) - E_star),
                      bottleneck="洞未全翻正 ⇒ 维持 " + cur["bottleneck"],
                      unchanged_from_round7=True)

    # ---- 预算 ----
    per = {r["piece"]: dict(solve_s=r.get("solve_s"),
                            equivalents=(round(r["solve_s"] / EQUIV_UNIT_S, 3)
                                         if isinstance(r.get("solve_s"), (int, float))
                                         else None)) for r in rows}
    tot_s = sum(v["solve_s"] for v in per.values()
                if isinstance(v["solve_s"], (int, float)))
    budget = dict(unit="(8,6)-当量 = 10800s SDPA-GMP 求解墙钟（M8 实测 10044–11793s）",
                  per_piece=per, total_solve_s=tot_s,
                  total_equivalents=round(tot_s / EQUIV_UNIT_S, 3),
                  round_budget="R8-1 ≤ 13 当量（D19 预算与并行）")

    return dict(kind="thomson-n9/bounds/m9-campaign/1", schema=1,
                script="numerics/bounds/m9_campaign.py", seed=SEED,
                E_star=dict(value=str(E_star), float=float(E_star)),
                engine_assignment=dict(
                    rule="D19 裁决 2：按 M8 逐片最优选引擎",
                    rows={p["piece"]: p["engine"] for p in PIECES}),
                m8_baselines=baselines,
                canary=canary, rows=rows,
                record_prospective=record, budget=budget,
                solver_events=ev_by_piece,
                assertions=dict(
                    strip="certified>E*（exclusion 片；违反＝blocked 行带 best_certified_attempt＋lift 实测）",
                    cap="0<certified≤E*+1e-6（TTP-covering 片）",
                    iron="全部 TTP-covering 下界 ≤ E*+1e-6（精确 Fraction）"))


def main() -> int:
    ap = argparse.ArgumentParser(description="M9 战役汇总（纯装配，不求解）")
    ap.add_argument("--out", default=str(RESULTS / "m9_campaign.json"))
    ap.add_argument("--skip-blocked-recompute", action="store_true")
    args = ap.parse_args()
    js = build(skip_blocked_recompute=args.skip_blocked_recompute)
    Path(args.out).write_text(json.dumps(js, ensure_ascii=False, indent=1,
                                         sort_keys=False))
    print(f"[out] {args.out}（{len(js['rows'])} 行；canary.decision="
          f"{js['canary']['decision']}；record="
          f"{js['record_prospective'].get('float')}）", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
