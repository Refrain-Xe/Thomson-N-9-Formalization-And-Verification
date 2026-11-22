#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""prototype_n9.py — N=9 typed 三点构造原型运行（规模/耗时/界值记录）。

Round 2 背景：untyped (8,6) 的 cap 阶梯在 a₀=−0.755 附近有原始间隙地板
~5.5e-4（PROGRESS.md Round 2 §3），typed（3+3+3 分型）是共同解法方向。本脚本
把 typed 构造在目标规模上实际跑起来并记录：类型结构、d_H、PSD 块数、最大块
尺寸、单次求解耗时、界值（数值证据）、TTP 处的近紧性复核。

  类型结构 (3,3,3)：索引块 = tri_cap_prism 的轨道布局（0–2 顶三角、3–5 底三角、
  6–8 赤道帽；numerics/family.py），cut 模式 a=−151/200（Round 2 区域最好证书
  的同一覆盖域，含 TTP 最小内积 −0.7475605）。cut 模式对任意标号有效（纯组合
  推导），TTP 以其自然标号落入该分型。

  配置阶梯（单命令一档，控制 ≤10 分钟）：
    small=(6,6) d_H=10 → mid=(7,6) d_H=12 → midlarge=(8,6) d_H=14（与 untyped
    cap 阶梯同 (M,K)，可对照）→ large16=(9,6) d_H=16（任务书目标档）。

  每档：typed 自检三件套（核恒等式/分型正性/typed 恒等式）→ 求解 → 数值复核
  与折减 e_safe → TTP 处 Σ_cls H ≥ e、E ≥ e 复核 → 断言 0 < e_safe ≤ E*+1e-6
  （E* 读 thomson-workflow/data/energies.json）。

用法（在 thomson-n9 下；--config 一档一命令）：
  numerics/.venv/bin/python numerics/bounds/typed/prototype_n9.py --config small
  numerics/.venv/bin/python numerics/bounds/typed/prototype_n9.py --config large16
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
NUMERICS_DIR = BOUNDS_DIR.parent
for p in (str(BOUNDS_DIR), str(HERE), str(NUMERICS_DIR)):
    if p not in sys.path:
        sys.path.insert(0, p)

import sdp_bound as UB                              # noqa: E402
import core as TC                                   # noqa: E402
import solve as TS                                  # noqa: E402

E_STAR_FALLBACK = 25.759986531
TCONFIGS = {"small": (6, 6), "mid": (7, 6), "midlarge": (8, 6), "large16": (9, 6)}
A0 = -151.0 / 200.0


def load_E_star():
    path = NUMERICS_DIR.parents[1] / "thomson-workflow" / "data" / "energies.json"
    try:
        with open(path) as f:
            E = float(json.load(f)["energies"]["9"]["value"])
        return E, str(path)
    except Exception as exc:                        # noqa: BLE001
        print(f"[warn] 使用 E* 常数 {E_STAR_FALLBACK}（energies.json 不可读: {exc}）",
              flush=True)
        return E_STAR_FALLBACK, f"fallback（{exc}）"


def ttp_config():
    from family import tri_cap_prism                # noqa: E402
    from scipy.optimize import minimize_scalar      # noqa: E402
    fE = lambda z: float(np.sum(
        1.0 / np.linalg.norm(tri_cap_prism(z)[:, None, :] - tri_cap_prism(z)[None, :, :],
                             axis=2)[np.triu_indices(9, 1)]))
    res = minimize_scalar(fE, bounds=(0.4, 0.9), method="bounded",
                          options={"xatol": 1e-13})
    return tri_cap_prism(float(res.x)), float(res.x), float(res.fun)


def main() -> None:
    ap = argparse.ArgumentParser(description="N=9 typed 原型（3+3+3，cut a=−151/200）")
    ap.add_argument("--config", required=True, choices=list(TCONFIGS))
    ap.add_argument("--a", type=float, default=A0)
    ap.add_argument("--types", nargs="+", type=int, default=[3, 3, 3])
    ap.add_argument("--solver-opts", type=str, default=None,
                    help="JSON 覆盖 Clarabel 选项，如 '{\"time_limit\": 480}'")
    ap.add_argument("--out", type=str,
                    default=str(BOUNDS_DIR / "results" / "typed_prototype_n9.json"))
    args = ap.parse_args()

    if UB.cp is None:
        print("[FAIL] 需要 cvxpy：请用 numerics/.venv/bin/python 运行", flush=True)
        sys.exit(1)

    E_star, src = load_E_star()
    M, K = TCONFIGS[args.config]
    ts = TC.TypeStructure(args.types)
    rng = np.random.default_rng(UB.CFG["SEED"])
    sopts = json.loads(args.solver_opts) if args.solver_opts else None

    t0 = time.time()
    maps = TC.assemble_typed(ts, "cut", args.a, None, M, K)
    ks = TC.kernel_selftest(maps, rng, n_points=120)
    ids = TC.identity_selftest(maps, rng, n_trials=2)
    st_ok = bool(ks["positivity_ok"] and ks["Q_identity_max_err"] < 1e-9 and ids["ok"])
    print(f"[selftest] Q 恒等式 {ks['Q_identity_max_err']:.2e}；分型正性 "
          f"{ks['positivity_sum']:.3e}（ok={ks['positivity_ok']}）；"
          f"typed 恒等式 rel {ids['worst_rel']:.2e}（ok={ids['ok']}）", flush=True)
    if not st_ok:
        print("[assert] typed 自检三件套未过——拒绝继续", flush=True)
        sys.exit(1)

    e_val, info, chk, maps, V = TS.solve_case(ts, "cut", args.a, None, M, K,
                                              solver_opts=sopts)
    print(f"[{args.config}] (M={M},K={K},d_H={2*M-2}) e = {e_val!r}"
          f"（{info['solver']} {info['status']}，build {info['build_s']}s "
          f"+ solve {info['solve_s']}s）", flush=True)
    entry = dict(config=args.config, M=M, K=K, d_H=2 * M - 2,
                 types=list(args.types), a=args.a, e=e_val, info=info,
                 selftests=dict(Q_identity_max_err=ks["Q_identity_max_err"],
                                typed_positivity_ok=bool(ks["positivity_ok"]),
                                typed_identity_rel_err=ids["worst_rel"]),
                 run=dict(timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
                          argv=sys.argv[1:],
                          wall_s=round(time.time() - t0, 1)))
    ttp = None
    if chk:
        print(f"[{args.config}] 复核：slack_min={min(chk['slack_min_random'], chk['slack_min_boundary']):.2e} "
              f"viol={chk['minorant_max_violation']:.2e} D={chk['deflation']:.3e}"
              f" → e_safe={chk['e_safe']:.9f}", flush=True)
        entry["check"] = chk
        if chk["e_safe"] > 0:
            X_ttp, z_star, E_ttp = ttp_config()
            ttp = TS.typed_bound_summary(maps, V, chk["e_safe"], X_ttp)
            ttp.update(z_star=z_star, E_ttp=E_ttp,
                       E_star_minus_E_ttp=float(E_star - E_ttp))
            entry["ttp"] = ttp
            print(f"[{args.config}] TTP：z*={z_star:.12f} E(TTP)={E_ttp:.9f} "
                  f"ΣH−e={ttp['sumH_minus_e']:+.3e} E−e={ttp['E_minus_e']:+.3e}"
                  f"（min 内积 {ttp['min_inner']:.9f}）", flush=True)
    # 断言（数值证据口径）
    ok_bound = bool(chk and chk["e_safe"] > 0 and chk["e_safe"] <= E_star + 1e-6)
    entry["assert_ok"] = ok_bound
    print(f"[{args.config}] E* = {E_star:.9f}（{src}）；"
          f"e_safe ≤ E*+1e-6: {'OK' if ok_bound else 'FAIL/VIRGIN'}", flush=True)

    out_path = Path(args.out)
    results = dict(kind="typed-prototype-n9",
                   script="typed/prototype_n9.py", target=dict(E_star=E_star, source=src))
    if out_path.exists():
        try:
            old = json.load(open(out_path))
            results.update({k: v for k, v in old.items() if k not in ("kind", "script", "target")})
            results["cases"] = [c for c in old.get("cases", [])
                                if c.get("config") != args.config]
        except Exception:                           # noqa: BLE001
            pass
    results.setdefault("cases", []).append(entry)
    with open(out_path, "w") as f:
        json.dump(results, f, ensure_ascii=False, indent=2)
    print(f"[out] 已写入 {out_path}", flush=True)
    if not ok_bound:
        print("[assert] e_safe 缺失或违反 0 < e_safe ≤ E*+1e-6——该档记为未达标"
              "（原型记录，不掩盖）", flush=True)
        sys.exit(1)


if __name__ == "__main__":
    main()
