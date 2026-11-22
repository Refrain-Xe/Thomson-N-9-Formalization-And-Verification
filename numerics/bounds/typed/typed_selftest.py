#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""typed_selftest.py — typed（Bachoc–Vallentin 分型）三点构造的紧合自检表。

Round 2 交付：typed 构造（typed/core.py + typed/solve.py，N=7 论文 §6 的推广）
的正确性外部校验，与 untyped（construction_selftest.py → results/selftest.json）
同一思路、同一参照：N ∈ {3,4,6,12} 的普适最优构型上界应恰为真值
（typed 是 untyped 的分型松弛，最优值 ≥ untyped ≥ LP 紧合界，且有效性 cap
在真值上；构造/装配有真问题则 e > E_true + 阈 判 FAIL）。

  每行 N：
    1) 精确几何构型（同 construction_selftest.build_config / lp_bound.exact_E），
       数值验证最小内积 = 期望有理数（容差 1e-12）；
    2) 类型结构 (2, n−2)（极小对 {0,1} 为类型 0，其余为类型 1——N=7 校准同款
       分型在普适构型上的移植；cut 模式 a = 最小内积 − 1e-9，无需极小对重标，
       对任意标号有效），按 small=(6,4) → medium=(6,6) → midlarge=(7,6) 升档求解，
       直到 |e − E_true| ≤ 1e-4（紧合）；任何档 e > E_true + 5e-6 即 FAIL；
    3) 每档先跑 typed 自检三件套：
       (a) 核恒等式 Q_k = Re(ζ^k \\bar ζ^k)；
       (b) 分型正性（引理 4.1 逐类型，随机 PSD F^{type(i)}）；
       (c) typed 恒等式 Σ_T λ_T + Σ_all = Σ_{i<j}H_{cls} − e（随机数据，
           随机有理无关——覆盖份额、Ψ/gm、核项根和×2、归一化、s(1,1,1) 全通路）。

  N=2 行按理论退化处理：typed 的份额机制要求每个对有 n−2 ≥ 1 个第三点、
  slack 机制要求至少一个三点类；n=2 时两者皆空（assemble_typed 显式报错），
  任何"typed 三点界"无从谈起。该行不求解（assemble 显式拒绝），不计入通过
  判定；N=2 紧合性由两点 LP 自检表覆盖（bounds/README.md，lp.json selftest）。
  ——与 untyped 自检表的 n−2=0 退化（ZeroDivisionError 实测）同一结构性限制。

  判定：N∈{3,4,6,12} 全部紧合 → exit 0 并写 results/typed_selftest.json；
  任一 N 全档后仍 e < E_true − 1e-4（不紧合）或任一档 e > E_true + 5e-6
  （有效性破坏）→ exit 1（JSON 照写，供差距分析）。

用法（在 thomson-n9 下）：
  numerics/.venv/bin/python numerics/bounds/typed/typed_selftest.py
  numerics/.venv/bin/python numerics/bounds/typed/typed_selftest.py --configs small
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
BOUNDS_DIR = HERE.parent
REPO = BOUNDS_DIR.parents[1]
for p in (str(BOUNDS_DIR), str(HERE), str(BOUNDS_DIR.parent)):
    if p not in sys.path:
        sys.path.insert(0, p)

import lp_bound                                     # noqa: E402  （exact_E 真值）
import sdp_bound as UB                              # noqa: E402  （cp 可用性）
import core as TC                                   # noqa: E402
import solve as TS                                  # noqa: E402

VALID_TOL = 5e-6      # e > E_true + 5e-6 ⇒ 构造/装配的硬错误（界被破坏）
TIGHT_TOL = 1e-4      # |e − E_true| ≤ 1e-4 判紧合（与 untyped 表一致）
MIN_IP_TOL = 1e-12
A_SHAVE = 1e-9        # 域下沿余量（构型浮点内积在 a ± 几 ulp 内）

TCONFIGS = {"small": (6, 4), "medium": (6, 6), "midlarge": (7, 6)}

CASES = {  # N -> (期望最小内积(有理), 描述)
    2: (-1, "对径点对"),
    3: (-0.5, "大圆正三角形"),
    4: (-1 / 3, "正四面体"),
    6: (-1, "正八面体"),
    12: (-1, "正二十面体"),
}


def build_config(N: int) -> np.ndarray:
    """普适最优构型的精确几何构造（同 construction_selftest.build_config）。"""
    if N == 2:
        return np.array([[0.0, 0.0, 1.0], [0.0, 0.0, -1.0]])
    if N == 3:
        ang = 2 * np.pi * np.arange(3) / 3
        return np.stack([np.cos(ang), np.sin(ang), np.zeros(3)], axis=1)
    if N == 4:
        X = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], dtype=float)
        return X / np.linalg.norm(X, axis=1, keepdims=True)
    if N == 6:
        return np.array([[1, 0, 0], [-1, 0, 0], [0, 1, 0],
                         [0, -1, 0], [0, 0, 1], [0, 0, -1]], dtype=float)
    if N == 12:
        phi = (1 + math.sqrt(5)) / 2
        r = math.sqrt(1 + phi ** 2)
        V = []
        for a in (-1, 1):
            for b in (-phi, phi):
                V.append((0, a, b))
                V.append((a, b, 0))
                V.append((b, 0, a))
        X = np.array(V, dtype=float)
        return X / np.linalg.norm(X, axis=1, keepdims=True)
    raise ValueError(N)


def main() -> None:
    ap = argparse.ArgumentParser(description="typed 三点构造的普适最优紧合自检")
    ap.add_argument("--configs", nargs="+", default=list(TCONFIGS),
                    choices=list(TCONFIGS))
    ap.add_argument("--out", type=str,
                    default=str(BOUNDS_DIR / "results" / "typed_selftest.json"))
    args = ap.parse_args()

    if UB.cp is None:
        print("[FAIL] 需要 cvxpy：请用 numerics/.venv/bin/python 运行，"
              "例如 `numerics/.venv/bin/python numerics/bounds/typed/typed_selftest.py`",
              flush=True)
        sys.exit(1)

    t_start = time.time()
    rng = np.random.default_rng(UB.CFG["SEED"])
    rows = []
    all_pass = True

    for N in (2, 3, 4, 6, 12):
        a_expect, desc = CASES[N]
        X = build_config(N)
        G = X @ X.T
        iu = np.triu_indices(N, 1)
        min_ip = float(G[iu].min())
        if abs(min_ip - a_expect) > MIN_IP_TOL:
            print(f"[FAIL] N={N}: 构造最小内积 {min_ip!r} ≠ 期望 {a_expect!r}", flush=True)
            rows.append(dict(N=N, ok=False, reason="min_ip mismatch", min_ip=min_ip))
            all_pass = False
            continue
        E_true, desc_E = lp_bound.exact_E(N)
        row = dict(N=N, config_desc=desc, E_true=E_true, E_true_desc=desc_E,
                   min_ip=min_ip, min_ip_expected=a_expect,
                   types=[2, N - 2], a_used=a_expect - A_SHAVE, attempts=[])

        if N == 2:
            # 理论退化行：份额机制（对 {i,j} 的份额在第三点上求和）与 slack 机制
            # （三点类）在 n=2 全空，assemble_typed 显式拒绝（无三点类）。
            try:
                TC.assemble_typed(TC.TypeStructure([1, 1]), "cut", a_expect - A_SHAVE,
                                  None, *TCONFIGS["small"])
                note = "意外成功装配（不应发生）"
            except ValueError as exc:
                note = f"assemble_typed 按预期拒绝：{exc}"
            row["status"] = "degenerate-by-theory"
            row["ok"] = True   # 不计入通过判定（理论结构限制，非实现缺陷）
            row["note"] = (note + "；typed 份额/slack 机制在 n=2 空转；"
                           "紧合性由两点 LP 自检表覆盖（lp_bound.py SELFTEST）")
            rows.append(row)
            print(f"[N={N:2d}] 理论退化行（无三点类）：{note}", flush=True)
            continue

        # ---- n ≥ 3：(2, n−2) 分型，cut 模式，按配置升档求解，判紧合 ----
        ts = TC.TypeStructure([2, N - 2])
        passed = None
        for cname in args.configs:
            M, K = TCONFIGS[cname]
            t0 = time.time()
            maps = TC.assemble_typed(ts, "cut", a_expect - A_SHAVE, None, M, K)
            ks = TC.kernel_selftest(maps, rng, n_points=120)
            ids = TC.identity_selftest(maps, rng, n_trials=2)
            st_ok = bool(ks["positivity_ok"] and ks["Q_identity_max_err"] < 1e-9
                         and ids["ok"])
            e_val, info, chk, _m2, _V = TS.solve_case(ts, "cut", a_expect - A_SHAVE,
                                                      None, M, K)
            att = dict(config=cname, M=M, K=K, e=e_val, status=info["status"],
                       solver=info["solver"], solve_s=info["solve_s"],
                       selftests=dict(Q_identity_max_err=ks["Q_identity_max_err"],
                                      typed_positivity_ok=bool(ks["positivity_ok"]),
                                      typed_identity_rel_err=ids["worst_rel"],
                                      all_ok=st_ok),
                       E_minus_e=E_true - e_val)
            row["attempts"].append(att)
            print(f"[N={N:2d}] {cname}(M={M},K={K})：e = {e_val!r}（{info['status']}，"
                  f"{time.time() - t0:.0f}s 含自检）E_true − e = {E_true - e_val:.3e}",
                  flush=True)
            if not st_ok:
                att["verdict"] = "SELFTEST_FAIL"
                row["ok"] = False
                row["reason"] = "typed 自检三件套未过（核/分型正性/typed 恒等式）"
                passed = False
                break
            if e_val > E_true + VALID_TOL:
                att["verdict"] = "VALIDITY_FAIL"
                row["ok"] = False
                row["reason"] = (f"e = {e_val!r} 超过真值 E_true = {E_true!r} "
                                 f"（+{e_val - E_true:.3e} > {VALID_TOL}）——界在可行"
                                 "构型上被破坏，构造或装配有真问题")
                passed = False
                break
            if abs(e_val - E_true) <= TIGHT_TOL:
                att["verdict"] = "TIGHT"
                passed = True
                break
            att["verdict"] = "not-tight-yet"
        if passed is True:
            row["ok"] = True
            row["status"] = "tight"
        elif passed is None:
            row["ok"] = False
            row["status"] = "not-tight"
            row["reason"] = (f"全部配置 {args.configs} 均未紧合：最好 "
                             f"E_true − e = {max(a['E_minus_e'] for a in row['attempts']):.3e}"
                             f" > {TIGHT_TOL}")
        all_pass = all_pass and row["ok"]
        rows.append(row)

    out = dict(
        kind="typed-construction-selftest",
        script="typed/typed_selftest.py",
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        method=("typed（Bachoc–Vallentin 分型）三点构造（typed/core.py 装配 + "
                "typed/solve.py 求解）在 N∈{2,3,4,6,12} 普适最优构型上的紧合自检："
                "类型结构 (2, n−2)（极小对为类型 0，N=7 论文 §6 同款分型的普适移植），"
                "cut 模式 a=构型最小内积（−1e-9 余量）；typed 是 untyped 的分型松弛，"
                "紧合参照同 untyped 表（LP 紧合 ⊆ 三点界，有效性 cap 在真值上）"),
        tolerances=dict(validity_e_le_E_true_plus=VALID_TOL, tightness_abs=TIGHT_TOL,
                        min_ip_check=MIN_IP_TOL, a_shave=A_SHAVE),
        configs=TCONFIGS,
        n2_policy=("N=2 typed 份额/slack 机制空转（无第三点、无三点类，"
                   "assemble_typed 显式拒绝），degenerate-by-theory 行不计入通过判定；"
                   "紧合性由 lp_bound 两点表覆盖"),
        rows=rows,
        all_pass=bool(all_pass),
        runtime_s=round(time.time() - t_start, 1),
    )
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)
    print(f"[out] 已写入 {out_path}", flush=True)

    print("[table]")
    print(f"{'N':>3} {'E_true':>14} {'e(typed SDP)':>16} {'E_true−e':>10} "
          f"{'config':>9} {'status':>22}")
    for r in rows:
        if r.get("status") == "degenerate-by-theory":
            print(f"{r['N']:>3} {r['E_true']:>14.9f} {'—':>16} {'—':>10} "
                  f"{'—':>9} {r['status']:>22}")
            continue
        best = max(r["attempts"], key=lambda a: a["e"]) if r.get("attempts") else None
        if best is None:
            print(f"{r['N']:>3} {r['E_true']:>14.9f} {'—':>16} {'—':>10} {'—':>9} "
                  f"{r.get('status', 'FAILED'):>22}")
        else:
            print(f"{r['N']:>3} {r['E_true']:>14.9f} {best['e']:>16.9f} "
                  f"{r['E_true'] - best['e']:>10.2e} {best['config']:>9} "
                  f"{r['status']:>22}")
    if not all_pass:
        print("[selftest] 存在未通过行（见上）——构造或装配有真问题，拒绝 exit 0",
              flush=True)
        sys.exit(1)
    print(f"[selftest] N∈{{3,4,6,12}} 全部紧合（typed 自检三件套全过）；N=2 理论退化行"
          f"已记录。SELFTEST PASS（{out['runtime_s']}s）", flush=True)


if __name__ == "__main__":
    main()
