#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""m10_campaign.py — R7A M10 双片重解战役汇总器（schema thomson-n9/bounds/m10-campaign/1）。

## 职责与纪律

从**存档数据**（解档 json / strips.json / hermite_strips.json / m9_campaign.json /
endgame.json / 证书 json）纯装配 results/m10_campaign.json：
  - 不触发任何求解（求解由 strips_final/hermite_ladder 的正式入口后台完成，
    本脚本只读它们的产出）；
  - 不含墙钟时间戳、不含本脚本自身 code_version ⇒ **幂等**：同一存档状态重跑
    逐字节一致（r7_m10_gate.py 的 G5 以 sha256 前后比对逐位核验）。各行的
    code_version/命令/粒度取自**存档 provenance 原文**（生成时刻的记录），不随
    后续提交漂移。
  - blocked 行（条带正裕度断言失败的 Lukács 片，strips_final fail() 不落
    strips[] 行）：本脚本从解档**离线重算** best_certified_attempt——调
    slab_band.certify_slab 传 E_star=0（关掉末尾正裕度断言，其余认证链照跑：
    e−膨胀>0、抽查、certified≤e+1e-9），对 ks=48/56/64 各算一次取最大（粗粒度
    舍入只损失），精确 Fraction 入账。重算确定性（固定 spot 种子 97531+k）
    ⇒ 幂等成立。（同 m9_campaign.py 先例。）

## 行口径（D27 裁决 1：L0 洞余两片按 M9 逐片最优引擎 M10 重解）

  m079-m765  Lukács strips_final.py     （M9 逐片最优，D19 裁决 2 沿用）
  m765-m748  a5     hermite_ladder.py   （M9 逐片最优，D19 裁决 2 沿用，k_minor=48）

翻正判据（精确 Fraction）：certified > E* = 25759986531/10⁹ ⇔ M9→M10 lift ≥
E* − M9 基线（斜率保持阈；实测入账对照，见 slope_table/slope_retention）。

用法：
  python3 numerics/bounds/m10_campaign.py [--out results/m10_campaign.json]
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

SEED = 20261009
KS = (48, 56, 64)
K_MINOR = 48
M10, K6 = 10, 6
E_TOL = Fr(1, 10 ** 6)
# (8,6)-当量换算：1 当量 = 一次 (8,6) 档求解的典型墙钟 10800s（3h；实测 M8
# Lukács 条带 10044–10120s、typed cap 11793s、hermite 条带 4962s）。
EQUIV_UNIT_S = 10800.0
# R7A M10 战役预算红线（任务书 gate ⑦：Σsolve_s/10800 ≤ 19 当量；
# D27 成本外推 10.3+7.7≈18 当量可负担，预算余 32 (8,6)-当量）。
BUDGET_CAP_EQ = 19.0

PIECES = [
    dict(piece="m079-m765", kind="strip", engine="lukacs", lo="-79/100", hi="-153/200",
         cmd=(f'numerics/.venv/bin/python numerics/bounds/strips_final.py '
              f'--strip="-0.79:-0.765" --M 10 --ks 48 56 64'),
         sol=RESULTS / "strip_sol_m079-m765_M10.json",
         db=(RESULTS / "strips.json", "strips", "tag", "m079-m765"),
         cert=CERTS / "n9-stage-a4-strip-m079-m765_M10.json",
         verify=("strips_final.py", "--verify-cert"),
         m9_field="best_certified_attempt",   # Lukács M9 blocked ⇒ attempt 字段
         m9_cross=None),                      # strips 账本无 M9 成功行可交叉
    dict(piece="m765-m748", kind="strip", engine="a5-hermite", lo="-153/200",
         hi="-187/250",
         cmd=(f'python3 numerics/bounds/hermite_ladder.py --strip="-0.765:-0.748" '
              f'--M 10 --ks 48 56 64 --k-minor 48'),
         sol=RESULTS / "hermite_strip_sol_m765-m748_M10.json",
         db=(RESULTS / "hermite_strips.json", "strips", "tag", "m765-m748"),
         cert=CERTS / "n9-stage-a5-hermite-strip-m765-m748_M10.json",
         verify=("hermite_ladder.py", "--verify-cert"),
         m9_field="certified",                # a5 M9 blocked 行 certified 即 attempt
         m9_cross=(RESULTS / "hermite_strips.json", "strips", "tag",
                   "m765-m748", 9, "certified")),
]


def load_E_star() -> Fr:
    return Fr(str(json.loads(WORKFLOW_DATA.read_text())["energies"]["9"]["value"]))


def rel(p: Path) -> str:
    return str(p.relative_to(REPO))


def db_rows(db_path: Path, key: str, tag_field: str, tag: str) -> dict:
    """账本 json 中 tag 匹配、按 M 分桶的行（按需取用）。"""
    out = {}
    if db_path.exists():
        db = json.loads(db_path.read_text())
        for r in db.get(key, []):
            if r.get(tag_field) == tag:
                out[r.get("M")] = r
    return out


def solver_events() -> list:
    p = RESULTS / "m10_solver_events.json"
    if p.exists():
        return json.loads(p.read_text()).get("events", [])
    return []


def m9_baselines() -> dict:
    """M9 基线（精确分数）：m9_campaign.json 行优先，strips 账本交叉核对。

    片 2（Lukács）M9 blocked ⇒ best_certified_attempt（m9_campaign 离线重算的
    精确 Fraction）；片 3（a5）M9 blocked 行 certified 即 attempt（引擎自带
    精确分数）。账本来源在 source 字段留痕。
    """
    m9c = json.loads((RESULTS / "m9_campaign.json").read_text())
    rows9 = {r["piece"]: r for r in m9c["rows"]}
    out = {}
    for p in PIECES:
        r9 = rows9[p["piece"]]
        val = r9[p["m9_field"]]
        assert val is not None, f"{p['piece']}: m9_campaign.json 缺 {p['m9_field']}"
        src = (f"results/m9_campaign.json（{p['piece']} 行 {p['m9_field']}，"
               f"精确分数；status={r9['status']}）")
        eng = r9["engine"]
        # 交叉核对（有账本 M9 成功/blocked 行时必须逐串相等）
        xchk = None
        if p["m9_cross"] is not None:
            cp, ck, ct, ctag, cm, cf = p["m9_cross"]
            crow = db_rows(cp, ck, ct, ctag).get(cm)
            if crow is not None and crow.get(cf) is not None:
                xchk = crow[cf]
                assert Fr(xchk) == Fr(val), (
                    f"{p['piece']}: m9_campaign 基线 {val} ≠ 账本 {xchk}")
                src += f"；交叉核对 results/{cp.name} M{cm} 行相等"
        out[p["piece"]] = dict(engine=eng, certified=val,
                               certified_float=float(Fr(val)), source=src)
    return out


def m8_baselines() -> dict:
    """M8 基线（斜率表 M8→M9→M10 用）：原样取 m9_campaign.json m8_baselines。"""
    m9c = json.loads((RESULTS / "m9_campaign.json").read_text())
    return m9c["m8_baselines"]


def blocked_attempt_lukacs(sol_path: Path, piece: str) -> dict:
    """Lukács blocked 片的 best_certified_attempt 离线重算（E_star=0 关末尾断言）。

    其余认证链照跑（e−膨胀>0／域抽查／certified≤e+1e-9），ks=48/56/64 全算取
    最大——「舍入只损失」⇒ 最粗粒度最先失败时细粒度仍是有效下界尝试。
    """
    from slab_band import TypedCore, LamMaps, certify_slab
    from strips_final import sol_to_certify_input
    sol_js = json.loads(sol_path.read_text())
    core = TypedCore(9, M10, K6)
    lm = LamMaps(core, Fr(sol_js["lo"]), Fr(sol_js["hi"]))
    sol = sol_to_certify_input(sol_js)
    attempts = {}
    for k in KS:
        try:
            cd = certify_slab(core, lm, sol, k, Fr(0), f"{piece}/M10-blocked")
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

    base9 = m9_baselines()
    base8 = m8_baselines()

    rows = []
    for p in PIECES:
        rows_m = db_rows(p["db"][0], p["db"][1], p["db"][2], p["db"][3])
        r10 = rows_m.get(M10)
        sol_exists = p["sol"].exists()
        events = ev_by_piece.get(p["piece"], [])
        # 账本行可用条件：a5 的 blocked/certified 行都落账（status 字段）；
        # Lukács 账本 strips[] 只含成功行——另须证书在盘佐证。
        db_usable = r10 is not None and (
            p["engine"] != "lukacs" or p["cert"].exists())
        row = dict(piece=p["piece"], kind=p["kind"], engine=p["engine"],
                   lo=p["lo"], hi=p["hi"], M=M10, K=K6,
                   assertion="certified>E*（exclusion 片；违反＝blocked 行带 "
                             "best_certified_attempt＋lift 实测）",
                   cmd=p["cmd"])
        if db_usable:
            status = r10.get("status", "certified")
            certified = Fr(r10["certified"])
            row.update(status=status, e_raw=r10.get("e_raw"),
                       certified=r10["certified"], certified_float=float(certified),
                       round_bits=r10.get("round_bits"),
                       minorant_k=r10.get("minorant_k", K_MINOR
                                         if p["engine"] == "a5-hermite" else None),
                       certificate=rel(p["cert"]) if p["cert"].exists() else None,
                       solution=rel(p["sol"]) if sol_exists else None,
                       solve_s=(r10.get("sdpa") or {}).get("solve_s"),
                       sdpa={kk: (r10.get("sdpa") or {}).get(kk)
                             for kk in ("phase_value", "iteration", "stalled_point",
                                        "mu", "relative_gap", "p_feas_error",
                                        "d_feas_error", "reused", "solve_s")},
                       provenance=dict(seed=SEED, code_version=r10.get("code_version"),
                                       ks=list(KS)))
            if status == "blocked":
                # a5 blocked 行：certified 字段即 best attempt（hermite_strips.json）
                row["best_certified_attempt"] = row["certified"]
                row["best_certified_attempt_float"] = float(certified)
                row["certificate"] = None   # blocked 不落证书（防误读）
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
                            "relative_gap", "p_feas_error", "d_feas_error", "reused",
                            "solve_s")}
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
                reason = "M10 本机不可解（见 m10_solver_events.json）"
                status = "machine_unsolvable"
            else:
                reason = "未排／未启动（求解后台进行中或未启动）"
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
            row["margin_vs_E_star"] = dict(value=str(attempt - E_star),
                                           float=float(attempt - E_star))
            b9 = Fr(base9[p["piece"]]["certified"])
            row["lift"] = dict(value=str(attempt - b9), float=float(attempt - b9))
            row["margin_vs_m9_best"] = row["lift"]
        rows.append(row)

    # ---- 斜率保持阈与斜率表（M8→M9→M10 逐片入账，gate ⑧/⑪ 口径） ----
    slope_table, slope_retention = {}, dict(
        rule=("certified(M10) > E* ⇔ lift(M9→M10) ≥ E* − baseline_M9"
              "（精确 Fraction；斜率保持阈＝对 M8→M9 实测 lift 的保持比）"))
    for p in PIECES:
        row = next(r for r in rows if r["piece"] == p["piece"])
        b8 = Fr(base8[p["piece"]]["certified"])
        b9 = Fr(base9[p["piece"]]["certified"])
        need = E_star - b9
        lift89 = b9 - b8
        ent = dict(
            engine=p["engine"],
            M8=base8[p["piece"]]["certified"], M8_float=float(b8),
            M9=base9[p["piece"]]["certified"], M9_float=float(b9),
            M10=(row.get("certified") if row.get("certified") is not None
                 else (row.get("blocked_detail") or {}).get("best_certified_attempt")),
            M10_float=(float(Fr(row["M10"])) if row.get("M10") is not None else None),
            lift_M8_M9=dict(value=str(lift89), float=float(lift89)),
            lift_M9_M10=(row.get("lift") if row.get("lift") is not None
                         else dict(value=None, float=None)),
            required_lift_M9_M10=dict(value=str(need), float=float(need)),
            required_retention_ratio=float(need / lift89),
            retention_ratio=(float(Fr(row["lift"]["value"]) / lift89)
                             if row.get("lift") is not None else None),
            sources=dict(
                M8=base8[p["piece"]]["source"],
                M9=base9[p["piece"]]["source"],
                M10=("row certified（证书口径）" if row.get("certified") is not None
                     else "row best_certified_attempt（离线重算/引擎 blocked 行）"
                          if row.get("best_certified_attempt") is not None
                          else "未跑")),
            verdict=row.get("status"))
        slope_table[p["piece"]] = ent
        slope_retention[p["piece"]] = dict(
            required_lift=dict(value=str(need), float=float(need)),
            measured_lift=(row["lift"] if row.get("lift") is not None
                           else dict(value=None, float=None)),
            met=(bool(Fr(row["lift"]["value"]) >= need)
                 if row.get("lift") is not None else None),
            note="met=None ⇒ 未跑/无数据；met 布尔＝lift 实测 ≥ 阈（精确 Fraction 比较）")

    # ---- 拼合前瞻（provisional；正式 assembledRecord 归 endgame_chain/R7C） ----
    eg = json.loads((RESULTS / "endgame.json").read_text())
    part = [dict(interval=pz["region"], bound=pz["bound"]) for pz in eg["partition"]]
    all_flipped = all(r["status"] == "certified" for r in rows)
    record = dict(
        note=("provisional——正式 assembledRecord 由 endgame_chain.py（R7C 收口）"
              "按证书口径重判；本字段只做战役侧前瞻，口径＝11 原子区域取 min、"
              "洞片以 M10 证书替换 HP 兜底（两片全翻时）"),
        both_strips_flipped=all_flipped)
    if all_flipped:
        hole_pieces = []
        for r in rows:
            hole_pieces.append(dict(interval=f"[{r['lo']},{r['hi']}]",
                                    bound=r["certified"],
                                    source=(f"certificates/{r['certificate'].split('/')[-1]}"
                                            if r.get("certificate") else None)))
        others = [pz for pz in part
                  if pz["interval"] not in ("[-79/100,-187/250]",)]
        cells = others + [dict(interval=hp["interval"], bound=hp["bound"],
                               source=hp.get("source")) for hp in hole_pieces]
        vmin = min(Fr(c["bound"]) for c in cells)
        bott = [c for c in cells if Fr(c["bound"]) == vmin]
        record.update(partition=[dict(interval=c["interval"],
                                      bound=c["bound"],
                                      bound_float=float(Fr(c["bound"])),
                                      source=c.get("source")) for c in cells],
                      value=str(vmin), float=float(vmin),
                      margin_vs_E_star=float(vmin - E_star),
                      bottleneck="；".join(b["interval"] for b in bott),
                      unchanged_from_round8=False)
    else:
        cur = eg["assembledRecord"]
        record.update(value=cur["value"], float=cur["float"],
                      margin_vs_E_star=float(Fr(cur["value"]) - E_star),
                      bottleneck="两片未全翻正 ⇒ 维持 " + cur["bottleneck"],
                      unchanged_from_round8=True)

    # ---- 预算（gate ⑦：Σsolve_s/10800 ≤ 19 当量） ----
    per = {r["piece"]: dict(solve_s=r.get("solve_s"),
                            equivalents=(round(r["solve_s"] / EQUIV_UNIT_S, 3)
                                         if isinstance(r.get("solve_s"), (int, float))
                                         else None)) for r in rows}
    tot_s = sum(v["solve_s"] for v in per.values()
                if isinstance(v["solve_s"], (int, float)))
    budget = dict(unit="(8,6)-当量 = 10800s SDPA-GMP 求解墙钟（M8 实测 10044–11793s）",
                  EQUIV_UNIT_S=EQUIV_UNIT_S,
                  per_piece=per, total_solve_s=tot_s,
                  total_equivalents=round(tot_s / EQUIV_UNIT_S, 3),
                  cap_equivalents=BUDGET_CAP_EQ,
                  within_cap=(tot_s / EQUIV_UNIT_S <= BUDGET_CAP_EQ),
                  round_budget="R7A M10 双片 ≤ 19 当量（任务书 gate ⑦；D27 外推 "
                               "10.3+7.7≈18 当量）")

    return dict(kind="thomson-n9/bounds/m10-campaign/1", schema=1,
                script="numerics/bounds/m10_campaign.py", seed=SEED,
                E_star=dict(value=str(E_star), float=float(E_star)),
                engine_assignment=dict(
                    rule="D27 裁决 1：L0 洞余两片按 M9 逐片最优引擎 M10 重解"
                         "（D19 裁决 2 引擎分派沿用）",
                    rows={p["piece"]: p["engine"] for p in PIECES}),
                m8_baselines=base8,
                m9_baselines=base9,
                slope_retention=slope_retention,
                rows=rows,
                slope_table=slope_table,
                record_prospective=record, budget=budget,
                solver_events=ev_by_piece,
                assertions=dict(
                    strip="certified>E*（exclusion 片；违反＝blocked 行带 "
                          "best_certified_attempt＋lift 实测）",
                    iron="全部 TTP-covering 下界 ≤ E*+1e-6（精确 Fraction）"))


def main() -> int:
    ap = argparse.ArgumentParser(description="M10 双片战役汇总（纯装配，不求解）")
    ap.add_argument("--out", default=str(RESULTS / "m10_campaign.json"))
    ap.add_argument("--skip-blocked-recompute", action="store_true")
    args = ap.parse_args()
    js = build(skip_blocked_recompute=args.skip_blocked_recompute)
    Path(args.out).write_text(json.dumps(js, ensure_ascii=False, indent=1,
                                         sort_keys=False))
    n_flip = sum(1 for r in js["rows"] if r.get("status") == "certified")
    print(f"[out] {args.out}（{len(js['rows'])} 行；翻正 {n_flip}/2；record="
          f"{js['record_prospective'].get('float')}；预算 "
          f"{js['budget']['total_equivalents']}/{js['budget']['cap_equivalents']}"
          f" 当量）", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
