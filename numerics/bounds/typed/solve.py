#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""typed 三点 SDP：构建、求解、数值复核（含折减）。

SDP（在 x = [e; h; ψ; c; vec(F)] 与 SOS Gram 阵上最大化 e）：
  (i)   逐三点类 slack 恒等式：λ_m ≡ Σ_r g_r·z_rᵀB_rz_r，B_r ⪰ 0；
        g_r ∈ {1; 各槽−lo ×3; 1−各槽 ×3; detG}，band 的 λ_m 追加 (hi−u)；
        z_r 单项式总次数 ≤ ⌊(D−deg g_r)/2⌋（与 untyped/N=7 论文 §5.2 的块结构同族）；
  (ii)  逐对类 minorant：1 − 2y·H_cls(1−2y²) ≡ Σ σ 块（Lukács/Markov–Lukács 族）；
  (iii) 归一化：Σ_m count(m)·c_m = e + Σ_X n_X·ΣF^{(X,0)}；
  (iv)  F^{(X,k)} ⪰ 0（引理 4.1 的分型正性）。

求解后复核（数值证据，不构成严格证书）：恒等式残差、PSD 最小特征值、slack 于
域内随机 Gram 三点＋边界族的逐点最小、H_cls ≤ φ 逐点、（可选）目标构型处的
ΣH ≥ e 与 E ≥ e；折减 e_safe = e − Δ 与 untyped sdp_bound.verify 同思路。
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

import numpy as np
import scipy.sparse as sp

HERE = Path(__file__).resolve().parent
BOUNDS_DIR = HERE.parent
NUMERICS_DIR = BOUNDS_DIR.parent
for p in (str(BOUNDS_DIR), str(NUMERICS_DIR)):
    if p not in sys.path:
        sys.path.insert(0, p)

try:
    import cvxpy as cp
except ModuleNotFoundError:                        # 装配/自检路径不需要 cvxpy
    cp = None

import sdp_bound as UB                             # noqa: E402
import core as TC                                  # noqa: E402

CFG = dict(
    SEED=20261003,
    SOLVER=dict(max_iter=1000, tol_gap_abs=1e-8, tol_gap_rel=1e-8,
                tol_feas=1e-8, time_limit=420.0),
    FALLBACK=dict(eps=1e-9, max_iters=30000, time_limit_secs=420.0),
    ACCEPT=dict(identity_residual=1e-5, minorant_violation=1e-7,
                slack_min=-1e-6, min_eig=-1e-7),
    GRID_NTRIPLE=20000,
    GRID_NT=40001,
)


def require_cvxpy():
    if cp is None:
        raise ModuleNotFoundError(
            "cvxpy 不可用：求解需要 numerics/.venv 的解释器，"
            "例如 `numerics/.venv/bin/python numerics/bounds/typed/typed_selftest.py`")


# ============================================================ SDP 构建
def _sos_blocks_for(ring, D, lo, hi, band):
    """(名, g 非零元, 单项式表) 列表；band=True 时在 u 槽追加 (hi−u) 乘子。"""
    detG = [((0, 0, 0), 1.0), ((1, 1, 1), 2.0), ((2, 0, 0), -1.0),
            ((0, 2, 0), -1.0), ((0, 0, 2), -1.0)]
    blocks = [("1", [((0, 0, 0), 1.0)], UB.mons_upto(ring, D // 2))]
    for var, slot in (("u", 0), ("v", 1), ("t", 2)):
        blocks.append((f"{var}-lo", [((0, 0, 0), -lo), (UB.unit_exp(slot), 1.0)],
                       UB.mons_upto(ring, (D - 1) // 2)))
    for var, slot in (("u", 0), ("v", 1), ("t", 2)):
        blocks.append((f"1-{var}", [((0, 0, 0), 1.0), (UB.unit_exp(slot), -1.0)],
                       UB.mons_upto(ring, (D - 1) // 2)))
    blocks.append(("detG", detG, UB.mons_upto(ring, (D - 3) // 2)))
    if band:
        blocks.append(("hi-u", [((0, 0, 0), hi), (UB.unit_exp(0), -1.0)],
                       UB.mons_upto(ring, (D - 1) // 2)))
    return blocks


def build_typed_sdp(maps):
    """返回 (prob, handles, meta)。所有数学地图来自 core.assemble_typed。"""
    require_cvxpy()
    ring, ts = maps["ring"], maps["ts"]
    lay = maps["x_layout"]
    D, d_H, K = maps["D"], maps["d_H"], maps["K"]
    lo, hi = maps["lo"], maps["hi"]

    e = cp.Variable(1, name="e")
    h = cp.Variable(lay["n_h"], name="h")
    psi = cp.Variable(lay["n_psi"], name="psi")
    cvar = cp.Variable(lay["n_c"], name="c")
    Fs = {X: [cp.Variable((maps["F_sizes"][k], maps["F_sizes"][k]), symmetric=True,
                          name=f"F_t{X}_k{k}")
              for k in range(K)] for X in range(ts.T)}
    Fall = [Fs[X][k] for X in range(ts.T) for k in range(K)]
    x_expr = cp.hstack([e, h, psi, cvar] + [cp.vec(F, order="C") for F in Fall])

    constraints = []
    for X in range(ts.T):
        constraints += [F >> 0 for F in Fs[X]]

    sos_handles = {}
    block_sizes = {}
    for m in maps["triples"]:
        dom = maps["slack_domains"][m]
        blocks = _sos_blocks_for(ring, D, lo, dom["hi"] if dom["band"] else 1.0,
                                 dom["band"])
        rhs = cp.Constant(np.zeros(ring.nmon))
        lst = []
        for name, gnz, mons in blocks:
            A = UB.sos_block_map(ring, gnz, mons)
            B = cp.Variable((len(mons), len(mons)), symmetric=True,
                            name=f"B_{m}_{name}")
            constraints.append(B >> 0)
            rhs = rhs + A @ cp.vec(B, order="C")
            lst.append((name, A, B))
        sos_handles[m] = lst
        block_sizes[m] = [(nm, len(mo)) for nm, _g, mo in blocks]
        constraints.append(rhs == maps["slack_maps"][m] @ x_expr)

    sig_handles = {}
    sig_sizes = {}
    for cls in maps["classes"]:
        mn = maps["minorants"][cls]
        deg_p = mn["deg_p"]
        rhs = cp.Constant(np.zeros(deg_p + 1))
        lst = []
        for name, mult, dmax in mn["blocks"]:
            mons_y = list(range(dmax + 1))
            A = TC.y_map(mons_y, mult, deg_p)
            B = cp.Variable((len(mons_y), len(mons_y)), symmetric=True,
                            name=f"sig_{cls}_{name}")
            constraints.append(B >> 0)
            rhs = rhs + A @ cp.vec(B, order="C")
            lst.append((name, A, B))
        sig_handles[cls] = lst
        sig_sizes[cls] = [dmax + 1 for _n, _m, dmax in mn["blocks"]]
        constraints.append(rhs == mn["Cp"] @ x_expr + mn["p_const"])

    constraints.append(maps["nrm_row"] @ x_expr == 0)

    prob = cp.Problem(cp.Maximize(e[0]), constraints)
    meta = dict(
        n=ts.n, types="+".join(map(str, ts.sizes)), mode=maps["mode"], lo=lo, hi=hi,
        M=maps["M"], K=K, d_H=d_H, D=D,
        nmon_slack=ring.nmon,
        n_pair_classes=len(maps["classes"]),
        n_triple_classes=len(maps["triples"]),
        F_blocks=[[X, k, sz] for X in range(ts.T) for k, sz in enumerate(maps["F_sizes"])],
        sos_block_sizes={str(m): v for m, v in block_sizes.items()},
        sig_block_sizes={str(cls): v for cls, v in sig_sizes.items()},
        nx=lay["nx"],
        n_scalar_vars=int(sum(v.size for v in prob.variables())),
        n_eq_rows=int(sum(c.size for c in constraints
                          if not isinstance(c, cp.constraints.PSD))),
    )
    handles = dict(prob=prob, e=e, h=h, psi=psi, c=cvar, Fs=Fs, Fall=Fall,
                   x_expr=x_expr, sos=sos_handles, sig=sig_handles)
    return prob, handles, meta


# ============================================================ 求解
def solve_case(ts, mode, lo, hi, M, K, verbose=False, solver_opts=None, fallback_opts=None):
    require_cvxpy()
    t0 = time.time()
    maps = TC.assemble_typed(ts, mode, lo, hi, M, K)
    prob, V, meta = build_typed_sdp(maps)
    build_s = time.time() - t0
    sopts = dict(CFG["SOLVER"]); sopts.update(solver_opts or {})
    fopts = dict(CFG["FALLBACK"]); fopts.update(fallback_opts or {})
    t1 = time.time()
    try:
        prob.solve(solver=cp.CLARABEL, verbose=verbose, **sopts)
        solver, status = "CLARABEL", prob.status
    except Exception as exc:                        # noqa: BLE001
        print(f"[warn] Clarabel 异常（{exc}），SCS 兜底", flush=True)
        prob.solve(solver=cp.SCS, verbose=verbose, **fopts)
        solver, status = "SCS", prob.status
    solve_s = time.time() - t1
    e_val = float(V["e"].value[0]) if V["e"].value is not None else float("nan")
    info = dict(solver=solver, status=status, build_s=round(build_s, 2),
                solve_s=round(solve_s, 2),
                objective=float(prob.value) if prob.value is not None else None, **meta)
    if status not in ("optimal", "optimal_inaccurate") or V["e"].value is None:
        return e_val, info, None, maps, V
    check = verify(maps, V, e_val)
    return e_val, info, check, maps, V


def x_value(V, lay):
    return np.concatenate([np.asarray(V["e"].value).ravel(),
                            np.asarray(V["h"].value).ravel(),
                            np.asarray(V["psi"].value).ravel(),
                            np.asarray(V["c"].value).ravel(),
                            np.concatenate([np.asarray(F.value).reshape(-1, order="C")
                                            for F in V["Fall"]])])


# ============================================================ 复核
def sample_domain_triples(rng, lo, hi, band, n_pts):
    """域内 Gram 三点（按构造可行）：u∈[lo,hi or 1]，v∈[lo,1]，t 取 (u,v) 可行段随机。"""
    us, vs, ts_ = [], [], []
    while len(us) < n_pts:
        m = max(64, n_pts - len(us))
        u = rng.uniform(lo, hi if band else 1.0, size=m)
        v = rng.uniform(lo, 1.0, size=m)
        root = np.sqrt(np.maximum(0.0, (1 - u ** 2) * (1 - v ** 2)))
        lo_t = np.maximum(lo, u * v - root)
        hi_t = np.minimum(1.0, u * v + root)
        ok = lo_t <= hi_t - 1e-12
        if not np.any(ok):
            continue
        t = rng.uniform(lo_t[ok], hi_t[ok])
        us.extend(u[ok].tolist()); vs.extend(v[ok].tolist()); ts_.extend(t.tolist())
    return np.array(us), np.array(vs), np.array(ts_)


def _detg_roots(p, q):
    """detG(p,q,t) ≥ 0 的 t 区间。"""
    root = np.sqrt(max(0.0, (1 - p ** 2) * (1 - q ** 2)))
    return p * q - root, p * q + root


def boundary_families(ring, coeff, lo, hi, band, nt):
    """边界族：(x,x,1) 型（band 时只取 u 槽 ∈ [lo,hi] 的置换）、(lo,lo,t) 与 band 的
    (hi,lo,t) 可行段。返回该族上的最小值。"""
    vals = []
    xtop = hi if band else 1.0
    xg = np.linspace(lo, xtop, nt)
    ones = np.ones_like(xg)
    # (x,x,1)：u=x ✓（band 下 u∈[lo,hi] 合法）
    vals.append(ring.eval_batch(coeff, xg, xg, ones))
    # (x,1,x)：u=x ✓
    vals.append(ring.eval_batch(coeff, xg, ones, xg))
    if not band:
        # (1,x,x)：u=1 越界，band 下跳过；cut 模式 u≤1 合法
        vals.append(ring.eval_batch(coeff, ones, xg, xg))
    # (lo,lo,t)：t ∈ [max(lo,2lo²−1), 1]
    t_lo = max(lo, 2.0 * lo * lo - 1.0)
    if t_lo <= 1.0:
        tg = np.linspace(t_lo, 1.0, nt)
        alo = np.full_like(tg, lo)
        vals.append(ring.eval_batch(coeff, alo, alo, tg))
    if band:
        # (hi,lo,t)：t ∈ detG(hi,lo,·)∩[lo,1]
        r0, r1 = _detg_roots(hi, lo)
        t_lo = max(lo, r0)
        t_hi = min(1.0, r1)
        if t_lo <= t_hi:
            tg = np.linspace(t_lo, t_hi, nt)
            vals.append(ring.eval_batch(coeff, np.full_like(tg, hi),
                                        np.full_like(tg, lo), tg))
    return float(np.min(np.concatenate(vals)))


def verify(maps, V, e_val):
    """数值复核 + 折减。与 untyped sdp_bound.verify 同思路，逐三点类/逐对类展开。"""
    ring, ts = maps["ring"], maps["ts"]
    lay = maps["x_layout"]
    d_H = maps["d_H"]
    lo, hi = maps["lo"], maps["hi"]
    x = x_value(V, lay)
    rng = np.random.default_rng(CFG["SEED"])

    min_eig = {}
    resid_l1 = {}
    slack_min_random = {}
    slack_min_boundary = {}
    psd_def_sos = {}
    for m in maps["triples"]:
        coeff = maps["slack_maps"][m] @ x
        rhs = np.zeros(ring.nmon)
        for name, A, B in V["sos"][m]:
            rhs += A @ np.asarray(B.value).reshape(-1, order="C")
            Bv = (np.asarray(B.value) + np.asarray(B.value).T) / 2
            min_eig[f"B_{m}_{name}"] = float(np.linalg.eigvalsh(Bv).min())
        resid_l1[m] = float(np.abs(coeff - rhs).sum())
        dom = maps["slack_domains"][m]
        u_s, v_s, t_s = sample_domain_triples(rng, dom["lo"], dom["hi"], dom["band"],
                                              CFG["GRID_NTRIPLE"])
        slack_min_random[m] = float(ring.eval_batch(coeff, u_s, v_s, t_s).min())
        slack_min_boundary[m] = boundary_families(ring, coeff, dom["lo"], dom["hi"],
                                                  dom["band"], CFG["GRID_NT"] // 8)
        psd_def_sos[m] = float(sum(
            max(0.0, -min_eig[f"B_{m}_{nm}"]) * 2.0 * B_.shape[0]
            for (nm, _A, B_) in V["sos"][m]))

    # F 块与 minorant
    # Σ_all ≥ −Σ_{X,k} defect·n_X·m_k·n²：逐根 Σ_{j,l}⟨F,Y_k⟩ = ρᵀFρ+ιᵀFι ≥
    # −defect·‖ρ‖²（‖ρ_a‖ ≤ n ⟹ ‖ρ‖² ≤ m_k·n²），类型 X 有 n_X 个根
    psd_def_F = 0.0
    for X in range(ts.T):
        for k, F in enumerate(V["Fs"][X]):
            Fv = (np.asarray(F.value) + np.asarray(F.value).T) / 2
            d = float(np.linalg.eigvalsh(Fv).min())
            min_eig[f"F_t{X}_k{k}"] = d
            mk = maps["F_sizes"][k]
            psd_def_F += max(0.0, -d) * ts.sizes[X] * mk * (ts.n ** 2)
    resid_minorant = {}
    viol_cls = {}
    viol_cls_fine = {}
    for cls in maps["classes"]:
        mn = maps["minorants"][cls]
        deg_p = mn["deg_p"]
        p_lhs = np.zeros(deg_p + 1)
        for name, A, B in V["sig"][cls]:
            p_lhs += A @ np.asarray(B.value).reshape(-1, order="C")
            Bv = (np.asarray(B.value) + np.asarray(B.value).T) / 2
            min_eig[f"sig_{cls}_{name}"] = float(np.linalg.eigvalsh(Bv).min())
        p_rhs = mn["Cp"] @ x + mn["p_const"]
        resid_minorant[cls] = float(np.max(np.abs(p_lhs - p_rhs)))
        hc = x[lay["H_index"][cls]:lay["H_index"][cls] + d_H + 1]
        dlo, dhi = mn["domain"]
        tg = np.linspace(dlo, min(dhi, 1.0 - 1e-9), CFG["GRID_NT"])
        Hv = np.polyval(hc[::-1], tg)
        phi = 1.0 / np.sqrt(2.0 - 2.0 * tg)
        viol_cls[cls] = float(np.max(Hv - phi))
        tfine = np.linspace(dlo, min(dhi, 1.0 - 1e-10), 10 * CFG["GRID_NT"])
        Hf = np.polyval(hc[::-1], tfine)
        phif = 1.0 / np.sqrt(2.0 - 2.0 * tfine)
        dt = float(tfine[1] - tfine[0])
        Hdd = float(sum(j * (j - 1) * abs(hc[j]) for j in range(len(hc))))
        viol_cls_fine[cls] = float(np.max(Hf - phif)) + dt * dt / 8.0 * Hdd

    n2 = ts.n * (ts.n - 1) // 2
    delta = (sum(ts.pair_count(*cls) * max(0.0, viol_cls_fine[cls])
                 for cls in maps["classes"])
             + sum(ts.triple_count(*m) * (resid_l1[m] + psd_def_sos[m])
                   for m in maps["triples"])
             + psd_def_F)
    check = dict(
        identity_residual_slack=max(resid_l1.values()),
        identity_residual_slack_by_class={str(m): resid_l1[m] for m in maps["triples"]},
        identity_residual_minorant=max(resid_minorant.values()),
        identity_l1_slack_by_class={str(m): resid_l1[m] for m in maps["triples"]},
        min_eig=min_eig,
        slack_min_random=min(slack_min_random.values()),
        slack_min_random_by_class={str(m): slack_min_random[m] for m in maps["triples"]},
        slack_min_boundary=min(slack_min_boundary.values()),
        minorant_max_violation=max(viol_cls.values()),
        minorant_violation_by_class={str(cls): viol_cls[cls] for cls in maps["classes"]},
        psd_deficit_sos=max(psd_def_sos.values()),
        psd_deficit_F=psd_def_F,
        deflation=float(delta),
        e_safe=float(e_val - delta),
    )
    acc = CFG["ACCEPT"]
    check["accepted"] = bool(
        check["identity_residual_slack"] <= acc["identity_residual"]
        and check["identity_residual_minorant"] <= acc["identity_residual"]
        and check["minorant_max_violation"] <= acc["minorant_violation"]
        and check["slack_min_random"] >= acc["slack_min"]
        and check["slack_min_boundary"] >= acc["slack_min"]
        and min(min_eig.values()) >= acc["min_eig"])
    return check


def typed_bound_summary(maps, V, e_val, X_cfg):
    """在给定构型（类型按索引块）处复核 Σ_{i<j}H_cls ≥ e 与 E ≥ e（数值证据）。"""
    ring = maps["ring"]
    lay = maps["x_layout"]
    d_H = maps["d_H"]
    x = x_value(V, lay)
    G = X_cfg @ X_cfg.T
    ts = maps["ts"]
    types = ts.types_of_config()
    n = ts.n
    sum_H = 0.0
    by_class = {}
    for i in range(n):
        for j in range(i + 1, n):
            cls = tuple(sorted((types[i], types[j])))
            hc = x[lay["H_index"][cls]:lay["H_index"][cls] + d_H + 1]
            val = float(np.polyval(hc[::-1], G[i, j]))
            sum_H += val
            by_class[str(cls)] = by_class.get(str(cls), 0.0) + val
    D = X_cfg[:, None, :] - X_cfg[None, :, :]
    dist = np.linalg.norm(D, axis=2)
    iu = np.triu_indices(n, 1)
    E_cfg = float(np.sum(1.0 / dist[iu]))
    return dict(sumH_classed=float(sum_H), sumH_by_class=by_class,
                E_config=E_cfg, E_minus_e=float(E_cfg - e_val),
                sumH_minus_e=float(sum_H - e_val),
                min_inner=float(G[iu].min()))
