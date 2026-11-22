#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""calibrate_n7.py — typed 构造在 N=7 关键档对 N=7 证明数值的校准。

参照（references/thomson-n7-lean/paper/PAPER.md）：
  §2   E(P) = 1/2 + 5√2 + 5/(2sin(π/5)) + 5/(2sin(2π/5)) = 14.4529774142213429350444915306…
  §6.5 分型证书表：类型 P（极，2 点）/R（环，5 点），F_P/F_R 各 k=0..5（尺寸 6−k，
       即 (M,K)=(6,6)、d_H=10——本包 TCONFIGS["medium"] 同款），五个 slab 与一个 cap：
         cap   [−1, −99/100]   e − E(P) = −2.2737e-16
         slab1 [−99/100, −49/50]  ┐
         slab2 [−49/50, −24/25]   │  同一 e = 14.45298…（25 位），
         slab3 [−24/25, −47/50]   │  e − E(P) = +2.5857787e-6
         slab4 [−47/50, −93/100]  │
         slab5 [−93/100, −9/10]   ┘
  §6.4 域：含极小对 {0,1} 的 slack（λ_A）u 槽带 [lo,hi]、v,t ≥ lo；其余 slack
       只用下切口 lo；类 A 的 H_A ≤ φ 于 [lo,hi]，H_B/H_C 于 [lo,1)。

校准逻辑（typed (2,5)，band 模式，medium (6,6)——与论文同 (M,K,d_H)）：
  * 论文证书值是 typed SDP 的可行点（我们的 SOS 乘子族是论文 6/5/5 块族的超集：
    {1; x−lo ×3; 1−x ×3; detG} ⊇ {1; x−lo ×3; detG}，band 再加 (hi−u)），
    故 e_opt(ours) ≥ e_paper − ε_solver；
  * cap 含 P 本身（极对 t=−1），有效性强制 e_opt(cap) ≤ E(P)，而 e_paper(cap) =
    E(P) − 2.27e-16 ⟹ e_opt(cap) ∈ [E(P)−2.3e-16, E(P)]——数值上应双双贴住 E(P)，
    这是唯一有**两侧**锚的档（同时校准有效性与近紧性）；
  * slab 的 e_opt 上界为该档真最小能量（未知），校准判 e_opt ≥ e_paper 且偏离
    与 untyped 校准（Case 1 最优 14.454504 vs 证书 14.453300，偏差 +1.2e-3）同量级。

判定：cap 两侧贴 E(P)（|e−E(P)| ≤ CAP_TOL 且 e ≤ E(P)+CAP_TOL）；slab 全部
e ≥ e_paper − SLAB_MARGIN_TOL 且 e − e_paper ≤ SLAB_DEV_TOL。先跑后按实测
 solver 噪声登记阈值的理由，不回填凑通过。

用法（在 thomson-n9 下，单命令 ≈ 5 分钟）：
  numerics/.venv/bin/python numerics/bounds/typed/calibrate_n7.py
  numerics/.venv/bin/python numerics/bounds/typed/calibrate_n7.py --cells cap slab5
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
BOUNDS_DIR = HERE.parent
for p in (str(BOUNDS_DIR), str(HERE)):
    if p not in sys.path:
        sys.path.insert(0, p)

import sdp_bound as UB                              # noqa: E402
import core as TC                                   # noqa: E402
import solve as TS                                  # noqa: E402

# ---- 论文参照值（PAPER.md §2/§6.5；cap 的精确分数见 §6.5 注）
E_P_DESC = "E(P) = 1/2+5√2+5/(2sin(π/5))+5/(2sin(2π/5))"
SLAB_MARGIN_PAPER = 2.5857787e-6                    # PAPER.md l.246
CAP_MARGIN_PAPER = -2.2737e-16                      # PAPER.md l.239 表
CELLS = {                                           # 名 -> (lo, hi, 论文 e−E(P))
    "cap": (-1.0, -0.99, CAP_MARGIN_PAPER),
    "slab1": (-0.99, -0.98, SLAB_MARGIN_PAPER),
    "slab2": (-0.98, -0.96, SLAB_MARGIN_PAPER),
    "slab3": (-0.96, -0.94, SLAB_MARGIN_PAPER),
    "slab4": (-0.94, -0.93, SLAB_MARGIN_PAPER),
    "slab5": (-0.93, -0.90, SLAB_MARGIN_PAPER),
}
# 校准阈（登记理由：typed cut 模式 N=7 复跑的求解器噪声 |e 重跑差| ~ 1e-5 量级；
# untyped Case-1 校准偏差 +1.2e-3 作 slab 偏差上限参照；cap 两侧锚用噪声的 2×）
CAP_TOL = 2e-5
SLAB_MARGIN_TOL = 1e-5           # e_opt ≥ e_paper − 1e-5（松弛不弱于论文可行点）
SLAB_DEV_TOL = 5e-3              # |e_opt − e_paper| ≤ 5e-3（与 untyped CALIB_TOL 一致）


def E_pentagonal_bipyramid():
    import mpmath as mp
    mp.mp.dps = 40
    val = (mp.mpf(1) / 2 + 5 * mp.sqrt(2)
           + 5 / (2 * mp.sin(mp.pi / 5)) + 5 / (2 * mp.sin(2 * mp.pi / 5)))
    return val


def main() -> None:
    ap = argparse.ArgumentParser(description="typed N=7 关键档校准")
    ap.add_argument("--cells", nargs="+", default=list(CELLS), choices=list(CELLS))
    ap.add_argument("--config", default="medium", choices=["small", "medium", "midlarge"])
    ap.add_argument("--out", type=str,
                    default=str(BOUNDS_DIR / "results" / "typed_calib_n7.json"))
    args = ap.parse_args()

    if UB.cp is None:
        print("[FAIL] 需要 cvxpy：请用 numerics/.venv/bin/python 运行", flush=True)
        sys.exit(1)

    tconfig = {"small": (6, 4), "medium": (6, 6), "midlarge": (7, 6)}[args.config]
    M, K = tconfig
    EP = E_pentagonal_bipyramid()
    EP_float = float(EP)
    print(f"[calib] E(P) = {str(EP)[:34]}…（{E_P_DESC}）", flush=True)
    print(f"[calib] typed (2,5) band 模式，config {args.config} (M={M},K={K},d_H={2*M-2})"
          f"——论文 §6.5 同款 (M,K,d_H)=(6,6,10)" + ("" if args.config == "medium"
                                                     else "（非论文档，仅探测）"),
          flush=True)

    rng = np.random.default_rng(UB.CFG["SEED"])
    ts = TC.TypeStructure([2, 5])
    rows = []
    all_ok = True
    for name in args.cells:
        lo, hi, margin_paper = CELLS[name]
        e_paper = EP_float + margin_paper
        t0 = time.time()
        maps = TC.assemble_typed(ts, "band", lo, hi, M, K)
        ks = TC.kernel_selftest(maps, rng, n_points=120)
        ids = TC.identity_selftest(maps, rng, n_trials=2)
        st_ok = bool(ks["positivity_ok"] and ks["Q_identity_max_err"] < 1e-9 and ids["ok"])
        e_val, info, chk, _maps, V = TS.solve_case(ts, "band", lo, hi, M, K)
        row = dict(cell=name, lo=lo, hi=hi, e=e_val, e_minus_EP=float(e_val - EP_float),
                   e_paper=e_paper, margin_paper=margin_paper,
                   e_minus_e_paper=float(e_val - e_paper),
                   status=info["status"], solver=info["solver"],
                   solve_s=info["solve_s"], selftests_ok=st_ok,
                   identity_selftest_rel=ids["worst_rel"])
        if not st_ok:
            row["ok"] = False
            row["reason"] = "typed 自检三件套未过"
        elif name == "cap":
            ok_two_sided = abs(e_val - EP_float) <= CAP_TOL
            row["cap_two_sided_ok"] = bool(ok_two_sided)
            row["ok"] = bool(ok_two_sided and e_val <= EP_float + CAP_TOL)
            row["reason"] = (f"cap 两侧锚：|e−E(P)| = {abs(e_val - EP_float):.3e}"
                             f"（阈 {CAP_TOL:.0e}）；有效性方向 e ≤ E(P)+{CAP_TOL:.0e}")
        else:
            row["ok"] = bool(e_val >= e_paper - SLAB_MARGIN_TOL
                             and abs(e_val - e_paper) <= SLAB_DEV_TOL)
            row["reason"] = (f"e − e_paper = {e_val - e_paper:+.3e}（需 ≥ −{SLAB_MARGIN_TOL:.0e}"
                             f" 且 |·| ≤ {SLAB_DEV_TOL:.0e}；上界=该档真最小能量，论文只给"
                             f"下侧可行值）")
        if chk:
            row["check"] = dict(
                resid_slack=chk["identity_residual_slack"],
                resid_minor=chk["identity_residual_minorant"],
                slack_min=min(chk["slack_min_random"], chk["slack_min_boundary"]),
                viol=chk["minorant_max_violation"], deflation=chk["deflation"],
                e_safe=chk["e_safe"])
        all_ok = all_ok and row["ok"]
        rows.append(row)
        print(f"[{name:6s}] [{lo:+.2f},{hi:+.2f}] e = {e_val:.9f}  e−E(P) = "
              f"{e_val - EP_float:+.3e}  e−e_paper = {e_val - e_paper:+.3e}"
              f"（{info['status']}，{time.time() - t0:.0f}s 含自检）ok={row['ok']}",
              flush=True)
        if chk:
            print(f"         复核：slack_min={min(chk['slack_min_random'], chk['slack_min_boundary']):.2e} "
                  f"viol={chk['minorant_max_violation']:.2e} D={chk['deflation']:.2e} "
                  f"e_safe={chk['e_safe']:.9f}", flush=True)

    out = dict(
        kind="typed-calibration-n7",
        script="typed/calibrate_n7.py",
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        reference=("references/thomson-n7-lean/paper/PAPER.md §2（E(P)）、§6.4（域）、"
                   "§6.5（分型证书表：cap/slab 的 e−E(P)）；论文档 (M,K,d_H)=(6,6,10)"),
        E_P=dict(value=str(EP)[:42], float=EP_float, desc=E_P_DESC),
        config=dict(types=[2, 5], mode="band", M=M, K=K, d_H=2 * M - 2,
                    note="类型 0=极对 {0,1}（band 载体），类型 1=环——论文 §6.1 同款"),
        tolerances=dict(cap_two_sided=CAP_TOL, slab_margin_tol=SLAB_MARGIN_TOL,
                        slab_dev_tol=SLAB_DEV_TOL),
        rows=rows,
        all_ok=bool(all_ok),
    )
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)
    print(f"[out] 已写入 {out_path}", flush=True)
    if not all_ok:
        print("[calib] 存在未过档（见上）——typed 构造与 N=7 论文数值不一致，拒绝 exit 0",
              flush=True)
        sys.exit(1)
    print("[calib] 全部关键档与 N=7 论文数值一致（typed 校准 PASS）", flush=True)


if __name__ == "__main__":
    main()
