#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""construction_selftest.py — BV/CW 三点构造在普适最优构型上的紧合自检表。

Round 1 遗留（GAP-REPORT.md ④"数值证据而非证明的数字"）：三点 SDP 构造的数学
正确性只有 N=7 校准（e=14.454504 vs 论文 Case 1 证书值 14.453300，容差 5e-3）
**间接**覆盖——那个参照值本身不是 SDP 最优值（是论文证书的可行值），校准过的
是"移植不低于论文"，不是"构造逐点正确"。本脚本换一组成**数学上紧合**的参照：
N ∈ {2,3,4,6,12} 的普适最优构型（对径点 / 正三角形 / 正四面体 / 正八面体 /
正二十面体）。这些构型上两点 LP 界可证紧合（Cohn–Kumar；lp_bound.py 的同款
自检表已实证 ≤4.2e-9），而三点 SDP 松弛包含两点界 ⇒ 其最优值也应**恰为**真值
E_true。若构造/实现有真问题，界会**超过**真值（有效性质被破坏，判 FAIL）；
若松动不足则显著低于真值（按 (M,K) 升档重试）。

  每行 N：
    1) 精确几何构造构型（N=12 用 φ=(1+√5)/2 的二十面体顶点，同 lp_bound.exact_E），
       数值验证其最小内积 = 期望有理数（−1、−1/2、−1/3、−1、−1，容差 1e-12）；
    2) 以 a = 最小内积（域下沿再让 1e-9，保证构型在证书域内部）建三点 SDP，
       按 small=(6,4) → medium=(7,6) → midlarge=(8,6) 依次求解，直到
       |e − E_true| ≤ 1e-4（紧合）；**任何**配置解出 e > E_true + 5e-6 即 FAIL
       （界在可行构型上被破坏——构造或实现的硬错误）；
    3) 附带跑 sdp_bound 的核恒等式/正性/三点恒等式自检（该 n 的实例）。

  N=2 行按**理论退化**处理：三点恒等式 dsum(slack) + (n−2)Σ_all = 2(n−2)(ΣH−e)
  在 n=2 时两边恒为零（dsum 无相异三点、n−2=0），界机制不存在，任何有限的
  "三点界"都无从谈起。该行实际跑一次 SDP 记录其行为（预期无界/异常状态），
  但**不计入**通过判定；N=2 的紧合性由两点 LP 自检表覆盖（bounds/README.md
  "自检（紧合校准）"表，lp.json selftest）。这是三点方法的结构限制，不是本
  实现的缺陷。

  判定：N∈{3,4,6,12} 全部紧合（各自行 pass）→ exit 0 并写 results/selftest.json；
  任一 N 在全部三档 (M,K) 后仍 e < E_true − 1e-4（不紧合）或任一档
  e > E_true + 5e-6（有效性破坏）→ exit 1（JSON 照写，供差距分析）。

用法（在 thomson-n9 下）：
  numerics/.venv/bin/python numerics/bounds/construction_selftest.py
  numerics/.venv/bin/python numerics/bounds/construction_selftest.py --configs small
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
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

import sdp_bound                                    # noqa: E402
import lp_bound                                     # noqa: E402 （exact_E 真值）

VALID_TOL = 5e-6      # e > E_true + 5e-6 ⇒ 构造/实现的硬错误（界被破坏）
TIGHT_TOL = 1e-4      # |e − E_true| ≤ 1e-4 判紧合（LP 表是 5e-6 上侧；SDP 求解器残差留裕）
MIN_IP_TOL = 1e-12
A_SHAVE = 1e-9        # 域下沿再放低的余量（构型浮点内积在 a ± 几 ulp 内）

CASES = {  # N -> (期望最小内积(有理), 描述)
    2: (-1, "对径点对"),
    3: (-0.5, "大圆正三角形"),
    4: (-1 / 3, "正四面体"),
    6: (-1, "正八面体"),
    12: (-1, "正二十面体"),
}


def build_config(N: int) -> np.ndarray:
    """普适最优构型的精确几何构造（同 lp_bound.exact_E 的几何）。"""
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
    ap = argparse.ArgumentParser(description="BV/CW 三点构造的普适最优紧合自检")
    ap.add_argument("--configs", nargs="+",
                    default=["small", "medium", "midlarge"], choices=list(sdp_bound.CFG["CONFIGS"]))
    ap.add_argument("--out", type=str, default=str(HERE / "results" / "selftest.json"))
    args = ap.parse_args()

    if sdp_bound.cp is None:
        print("[FAIL] 本脚本需要求解 SDP（cvxpy）：请用 numerics/.venv/bin/python 运行，"
              "例如 `numerics/.venv/bin/python numerics/bounds/construction_selftest.py`",
              flush=True)
        sys.exit(1)

    t_start = time.time()
    rng = np.random.default_rng(sdp_bound.CFG["SEED"])
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
                   a_used=a_expect - A_SHAVE, attempts=[])

        if N == 2:
            # 理论退化行：n−2 = 0 ⇒ 三点恒等式两边恒零，界机制不存在。
            try:
                M, K = sdp_bound.CFG["CONFIGS"]["small"]
                e_val, info, chk, _maps, _V = sdp_bound.solve_case(
                    2, a_expect - A_SHAVE, M, K)
                row["degenerate_run"] = dict(
                    config="small", e=e_val, status=info["status"],
                    solver=info["solver"],
                    note="n−2=0 ⇒ 恒等式 dsum+(n−2)Σ_all=2(n−2)(ΣH−e) 两边恒零；"
                         "有限的三点界无从谈起，此值不作为任何界的证据")
            except Exception as exc:                       # noqa: BLE001
                row["degenerate_run"] = dict(error=f"{type(exc).__name__}: {exc}")
            row["status"] = "degenerate-by-theory"
            row["ok"] = True   # 不计入通过判定（理论结构限制，非实现缺陷）
            row["note"] = ("三点方法在 n=2 退化（见上）；紧合性由两点 LP 自检表覆盖"
                           "（lp_bound.py SELFTEST，bounds/README.md 表）")
            rows.append(row)
            print(f"[N={N:2d}] 理论退化行（n−2=0）：degenerate_run = "
                  f"{json.dumps(row.get('degenerate_run'), ensure_ascii=False)[:160]}",
                  flush=True)
            continue

        # ---- n ≥ 3：按配置升档求解，判紧合 ----
        passed = None
        for cname in args.configs:
            M, K = sdp_bound.CFG["CONFIGS"][cname]
            t0 = time.time()
            maps = sdp_bound.assemble_maps(N, a_expect - A_SHAVE, M, K)
            ks = sdp_bound.kernel_selftest(maps, rng, n_points=120)
            ids = sdp_bound.identity_selftest(maps, rng)
            e_val, info, chk, _m2, _V = sdp_bound.solve_case(
                N, a_expect - A_SHAVE, M, K)
            att = dict(config=cname, M=M, K=K, e=e_val, status=info["status"],
                       solver=info["solver"], solve_s=info["solve_s"],
                       selftests=dict(kernel_ok=bool(ks["positivity_ok"]),
                                      identity_ok=bool(ids["ok"])),
                       E_minus_e=E_true - e_val)
            row["attempts"].append(att)
            print(f"[N={N:2d}] {cname}(M={M},K={K})：e = {e_val!r}（{info['status']}，"
                  f"{time.time() - t0:.0f}s 含自检）E_true − e = {E_true - e_val:.3e}",
                  flush=True)
            if e_val > E_true + VALID_TOL:
                att["verdict"] = "VALIDITY_FAIL"
                row["ok"] = False
                row["reason"] = (f"e = {e_val!r} 超过真值 E_true = {E_true!r} "
                                 f"（+{e_val - E_true:.3e} > {VALID_TOL}）——界在可行"
                                 "构型上被破坏，构造或实现有真问题")
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
        kind="construction-selftest",
        script="construction_selftest.py",
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        method=("BV/CW 三点构造（sdp_bound.py 的 assemble_maps/build_sdp/solve_case）"
                "在 N∈{2,3,4,6,12} 普适最优构型上的紧合自检：a=构型最小内积"
                f"（−{A_SHAVE} 余量），e 应恰等于 E_true（两点 LP 界紧合 ⊆ 三点 SDP）"),
        tolerances=dict(validity_e_le_E_true_plus=VALID_TOL, tightness_abs=TIGHT_TOL,
                        min_ip_check=MIN_IP_TOL, a_shave=A_SHAVE),
        n2_policy=("N=2 三点恒等式退化（n−2=0 ⇒ 0=0），degenerate-by-theory 行不计入"
                   "通过判定；紧合性由 lp_bound 两点自检表覆盖"),
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
    print(f"{'N':>3} {'E_true':>14} {'e(SDP)':>16} {'E_true−e':>10} {'config':>9} {'status':>22}")
    for r in rows:
        if r.get("status") == "degenerate-by-theory":
            dr = r.get("degenerate_run", {})
            print(f"{r['N']:>3} {r['E_true']:>14.9f} {'—':>16} {'—':>10} "
                  f"{'small':>9} {r['status']:>22}")
            continue
        best = max(r["attempts"], key=lambda a: a["e"]) if r.get("attempts") else None
        if best is None:
            print(f"{r['N']:>3} {r['E_true']:>14.9f} {'—':>16} {'—':>10} {'—':>9} "
                  f"{r.get('status', 'FAILED'):>22}")
        else:
            print(f"{r['N']:>3} {r['E_true']:>14.9f} {best['e']:>16.9f} "
                  f"{r['E_true'] - best['e']:>10.2e} {best['config']:>9} {r['status']:>22}")
    if not all_pass:
        print("[selftest] 存在未通过行（见上）——构造或实现有真问题，拒绝 exit 0",
              flush=True)
        sys.exit(1)
    print(f"[selftest] N∈{{3,4,6,12}} 全部紧合；N=2 理论退化行已记录。"
          f"SELFTEST PASS（{out['runtime_s']}s）", flush=True)


if __name__ == "__main__":
    main()
