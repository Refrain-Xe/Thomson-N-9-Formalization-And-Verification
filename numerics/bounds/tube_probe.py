#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""tube_probe.py — L3 路线 b（tube certificate）限时可行性探针（GAP-REPORT Round 5 清单第 1 项）。

只判可行性，不产正式证书。产出 results/tube_probe.json。

## 一、条件证书的数学形式（选型：域乘子条件化＝Lagrange/Putinar 型 + 两点 minorant 管外分段，即"两段式"）

**基线（typed/ 三点构造，core.py/solve.py，全自检通过）**：cut 模式、类型 (3,3,3)、
切口 a₀，证书恒等式 Σ_T count·λ_T + Σ_all = Σ_{i<j}H_cls(t_ij) − e，
约束：(i) λ_T ≡ Σ_r g_r·z_rᵀB_rz_r，B_r ⪰ 0，g_r ∈ {1; s−lo; 1−s; detG}（s=u,v,t），
⟹ λ_T ≥ 0 于域 D = {u,v,t∈[lo,1]}∩Gram；(ii) H_cls ≤ φ=1/t 于 [lo,1]
（Lukács/Markov–Lukács σ 族）；(iii) 归一化；(iv) F^{(X,k)} ⪰ 0。
结论：min 内积 ≥ a₀ ⇒ E ≥ e。cap 证书（L1，m≥−0.748 ⇒ 25.759571186）即此形式。

**条件化（本探针新增，参数＝管半径 ρ 与 TTP 谱节点 ν_1<…<ν_6）**：

  (i-tube) slack 乘子族扩容："管外强制"。family g ← g ∪ {f_{k,s} := (s−ν_k)²−ρ² :
         k=1..6, s∈{u,v,t}}，每个 f_{k,s} 配独立 PSD Gram 块（单项式次数 ≤⌊(D−2)/2⌋）。
         f_{k,s} ≥ 0 ⟺ s 距节点 ν_k ≥ ρ。⟹ λ_T ≥ 0 的认证域收缩为
         D ∩ {u,v,t 均在管外}。管内（某槽距某节点 < ρ）λ_T 不再被约束＝"让界"，
         SDP 可在那里放弃非负性换取更高的 e。
  (ii-tube) 两点 minorant 管外分段："管内让界"。H_cls ≤ φ 不再在整段 [lo,1] 上施加，
         改为对 [lo,1]∖∪_k[ν_k−ρ,ν_k+ρ] 的每个连通分段 [a_r,b_r] 独立施加
         Markov–Lukács（复用 core.build_minorant_maps 的两侧机制；末段接 1 走单侧
         Lukács）。管区间上 H 可自由超过 φ（bulge＝让界量，可测量）。

**证书语义（严格）**：对一切满足
    (C1) 全部 36 个内积 ≥ a₀，且 (C2) 全部内积 t 满足 min_k|t−ν_k| ≥ ρ（"全管外"构型）
的构型 X：E(X) ≥ e_out(ρ,M,K)。理由：此类构型的每个三点三元组落在收缩认证域内
（各槽 ∈ [lo,1]∩Gram∩管外 ⟹ 每个参与约束的 g_r ≥ 0 ⟹ λ_T ≥ 0），每个对值落在
某分段内（⟹ H ≤ φ 于该值处），Σ_all ≥ 0 全局成立（引理 4.1），装配恒等式即得。

**两段式架构位（宽 cap 架构 A）**：piece 1 = 本证书（全管外 ⇒ E ≥ e_out）；
piece 2 = "某内积距节点 < ρ" 的构型，交给 L2 强制 + L3' 谱管（半径 ρ）+ L4 + L6
（SDP 之外，本探针不测；现状 ρ_spec(ε_forcing)=0.6447 > ρ 探针值 ⇒ piece 2 目前
不闭合——见 gaps）。两段合起来 iff ρ_spec(ε) ≤ ρ（把 L3 的达标半径从半谱隙
0.018506 放宽到 ρ）。

**为何不用罚函数/纯目标拉格朗日项**：(a) 目标加 −μ·(管内违规量) 之类非线性、
无精确有理表示，下游 dyadic 认证管线（typed_ladder/slab_band 模式）接不上；
(b) 罚函数给的是"近似条件化"，残差无界、无干净认证集；(c) 域乘子给出**精确**的
条件语义（λ ≥ 0 恰在收缩域上成立），与现有 R1 残差折减机制（乘子在域上逐点非负
⟹ |λ−SOS| ≤ R1 ⇒ 域上 λ ≥ −R1）同构，正式版零新机器——只加块、不改认证算法。

**诚实标注的语义限制**：乘子条件化按槽施加 ⟹ 认证集是"全部内积都在管外"，
比架构需要的"某内积在管外"窄。窄版的补集（某内积在管内）更大 ⇒ piece 2 责任更重
（需全对 ρ_spec ≤ ρ）。"某内积在管外"版的实现＝最小对锚定 + 仅 u 槽管因子
（mode="band" + 单槽因子，repo 已有 band 机制）——列为正式版待测变体，本探针未跑。

## 二、探针矩阵（求解总预算 ≤1h，超时跳档如实记录）

  实际执行＝本脚本三次调用（结果全量合并于 results/tube_probe.json，runs[].invocation
  记来源）：
  ① 默认矩阵：(4,3)/(5,4) × {uncond；full@{2x,3x,4x,halfgap}；slack@2x}；
  ② 规模补档：(5,5)/(6,6) × {uncond；full/slack@halfgap}（halfgap 全规模扫 K=3..6）；
  ③ 阈值扫描：(5,5)/(6,6) × full@{0.5x,1x} ＋ (6,6) full@2x（分离-ρ 曲线定位阈值）。
  ρ 档（dyadic）：2x/3x/4x＝{39,59,78}/256 ≈ 2/3/4×0.076（任务书粗管）、1x＝39/512、
  0.5x＝39/1024、halfgap＝19/1024≈0.0186（架构相关尺度）；a₀=−0.82 单档。
  指标：e_val、折减 e_safe、求解器行为（status/迭代/耗时）、恒等式残差、认证域内
  slack 最小值（随机＋管壁边界族）、分段 minorant 违规、管内 H bulge、TTP 三点处 λ、
  分离度 Δ=e_val/e_safe(cond)−uncond（同 (M,K)）、端到端 spot check（实测全管外构型上
  逐三点 λ≥0、E≥e_val）、认证集非空性与 oracle（tri_cap_prism 族＋随机 20 万＋3 紧簇
  参价族＋SLSQP 多起点，advisory）。

  assert 口径（按任务书）：只做合法性——每档 0 < e_val ≤ E*+1e-2（宽域）。
  无条件档两侧硬断言；条件档若 e_val 越上界（粗管认证集簇化所致的合法现象）
  记 flag 不杀探针（记录在 run.flags，如实写入 JSON）。折减 e_safe 为 advisory，
  可能因探针规模小而折减过大 —— 不入断言、如实记录。

## 三、探针结论（详见 results/tube_probe.json verdict；feasible=false）

  架构 ρ（≤0.038）全档零分离（(4,3)–(6,6)，含 uncond 未饱和的 (6,6)），机制指标
  （bulge/TTP-λ）显示求解器在半谱隙管内根本不动用条件自由度；分离只出现在
  ρ ∈ (0.038,0.076)+ 的粗管区且 E*(ρ) 交叉点不随规模下移；粗管分离因 ε_forcing
  = e_out−E* ≥ 0.8 使 L2 强制退化而无法两段式拼合。(8,6)/(9,6) SDPA-GMP 单点
  （~10–12h/档）未测——见 JSON gaps。

用法（thomson-n9 下，求解用 numerics/.venv 解释器）：
  numerics/.venv/bin/python numerics/bounds/tube_probe.py            # 全矩阵
  numerics/.venv/bin/python numerics/bounds/tube_probe.py --smoke    # (4,3) 两档快验
  numerics/.venv/bin/python numerics/bounds/tube_probe.py --budget-s 3600
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from itertools import combinations
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
NUM = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "typed"))
sys.path.insert(0, str(NUM))

import sdp_bound as UB                                   # noqa: E402
import core as TC                                        # noqa: E402
from family import tri_cap_prism                         # noqa: E402

try:
    import cvxpy as cp
except ModuleNotFoundError:
    cp = None

OUT = HERE / "results" / "tube_probe.json"
E_STAR = 25.759986531                    # thomson-workflow/data/energies.json N=9（三源校验）
E_STAR_HP = 25.75998653127
LAMBDA_MIN_LB = 0.14378982               # results/full_local_min.json lambdaCertifiedLowerBound
CHAIN_TUBE_R = 0.07601                   # sqrt(2·4.1535e-4/0.14378982)，GAP-REPORT R4 §②
A0 = -0.82                               # 唯一切口档（任务书指定）
SEED = 20261005
DYAD = 4096                              # 节点 dyadic 网格 1/2^12（正式版可换精确代数数）

RHOS = [("2x", Fraction(39, 256)),       # 0.15234375 ≈ 2×0.076
        ("3x", Fraction(59, 256)),       # 0.23046875 ≈ 3×0.076
        ("4x", Fraction(78, 256)),       # 0.30468750 ≈ 4×0.076
        ("1x", Fraction(39, 512)),       # 0.076171875 ≈ 1×0.076（链级管半径）
        ("0.5x", Fraction(39, 1024)),    # 0.0380859375 ≈ 0.5×0.076
        ("halfgap", Fraction(19, 1024))]  # 0.0185546875 ≈ 半谱隙 0.018506


def log(msg):
    print(msg, flush=True)


# ============================================================ TTP 谱节点
def ttp_nodes():
    """TTP（tri-cap prism @ z*）Gram 的 6 谱节点（dyadic 网格化）。

    z* 区间取 results/full_local_min.json zStarInterval 中点（0.70364875…），
    与 tube_analysis.ttp_state 的 Brent 值一致量级；节点 dyadic 化供乘子使用，
    精确代数值留正式版（typed_ladder QuotientMaps 的 Fraction 口径）。
    """
    z = 0.5 * (0.703648376463 + 0.703649139406)
    X = tri_cap_prism(z)
    G = X @ X.T
    t = np.sort(G[np.triu_indices(9, 1)])
    vals, counts = np.unique(np.round(t, 10), return_counts=True)
    assert len(vals) == 6, f"TTP 谱节点数 {len(vals)} ≠ 6"
    nodes_dyad = [Fraction(int(round(v * DYAD)), DYAD) for v in vals]
    return z, X, G, [float(v) for v in vals], [int(c) for c in counts], nodes_dyad


def gap_segments(nodes_f, rho_f, lo, hi=1.0):
    """[lo,hi] ∖ ∪_k[ν_k−ρ, ν_k+ρ] 的连通分段（浮点算，边界由调用处 dyadic 化）。"""
    ivs = sorted((max(lo, v - rho_f), min(hi, v + rho_f)) for v in nodes_f)
    merged = []
    for a, b in ivs:
        if b < lo or a > hi or b <= a:
            continue
        if merged and a <= merged[-1][1] + 1e-15:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    segs, cur = [], lo
    for a, b in merged:
        if a - cur > 1e-12:
            segs.append((cur, a))
        cur = max(cur, b)
    if hi - cur > 1e-12:
        segs.append((cur, hi))
    return segs, merged


# ============================================================ SDP 构建（条件版）
def tube_slack_blocks(ring, D, lo, nodes_f, rho_f, band_hi=None):
    """slack 乘子族：基线 {1; s−lo; 1−s; detG; (hi−u)?} + 管因子 (s−ν_k)²−ρ²。

    返回 [(名, g 非零元, 单项式表)]，与 typed/solve._sos_blocks_for 同构。
    """
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
    if band_hi is not None:
        blocks.append(("hi-u", [((0, 0, 0), band_hi), (UB.unit_exp(0), -1.0)],
                       UB.mons_upto(ring, (D - 1) // 2)))
    nk = len(nodes_f)
    for k, nu in enumerate(nodes_f):
        for var, slot in (("u", 0), ("v", 1), ("t", 2)):
            e2 = [0, 0, 0]
            e2[slot] = 2
            e1 = [0, 0, 0]
            e1[slot] = 1
            blocks.append((f"tube_{var}_k{k}",
                           [(tuple(e2), 1.0), (tuple(e1), -2.0 * nu),
                            ((0, 0, 0), nu * nu - rho_f * rho_f)],
                           UB.mons_upto(ring, (D - 2) // 2)))
    assert nk * 3 <= 3 * 6 + 1
    return blocks


def build_probe_sdp(maps, variant, nodes_f, rho_f):
    """variant: 'uncond' | 'slack' | 'full'。返回 (prob, handles, extra_meta)。"""
    if cp is None:
        raise ModuleNotFoundError("cvxpy 不可用：用 numerics/.venv/bin/python 运行")
    ring, ts = maps["ring"], maps["ts"]
    lay = maps["x_layout"]
    D, d_H, K = maps["D"], maps["d_H"], maps["K"]
    lo = maps["lo"]
    segs_by_cls = {}

    e = cp.Variable(1, name="e")
    h = cp.Variable(lay["n_h"], name="h")
    psi = cp.Variable(lay["n_psi"], name="psi")
    cvar = cp.Variable(lay["n_c"], name="c")
    Fs = {X: [cp.Variable((maps["F_sizes"][k], maps["F_sizes"][k]), symmetric=True,
              name=f"F_t{X}_k{k}") for k in range(K)] for X in range(ts.T)}
    Fall = [Fs[X][k] for X in range(ts.T) for k in range(K)]
    x_expr = cp.hstack([e, h, psi, cvar] + [cp.vec(F, order="C") for F in Fall])

    constraints = [F >> 0 for F in Fall]

    # ---- (i) slack 恒等式（族按变体扩容）
    use_tube = variant in ("slack", "full")
    blocks_tpl = tube_slack_blocks(ring, D, lo, nodes_f, rho_f) if use_tube else None
    sos_handles, n_blocks = {}, 0
    for m in maps["triples"]:
        dom = maps["slack_domains"][m]
        assert not dom["band"], "探针用 cut 模式"
        blocks = blocks_tpl if use_tube else None
        if not use_tube:
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
        rhs = cp.Constant(np.zeros(ring.nmon))
        lst = []
        for name, gnz, mons in blocks:
            A = UB.sos_block_map(ring, gnz, mons)
            B = cp.Variable((len(mons), len(mons)), symmetric=True, name=f"B_{m}_{name}")
            constraints.append(B >> 0)
            rhs = rhs + A @ cp.vec(B, order="C")
            lst.append((name, A, B))
            n_blocks += 1
        sos_handles[m] = lst
        constraints.append(rhs == maps["slack_maps"][m] @ x_expr)

    # ---- (ii) minorant：uncond/slack＝整段 [lo,1]；full＝逐分段（末段接 1 单侧）
    sig_handles = {}
    n_sig = 0
    for cls in maps["classes"]:
        if variant == "full":
            segs, _ = gap_segments(nodes_f, rho_f, lo, 1.0)
            segs_dyad = []
            for a, b in segs:
                fa = Fraction(a).limit_denominator(DYAD)
                fb = Fraction(b).limit_denominator(DYAD)
                segs_dyad.append((float(fa), float(fb)))
            segs_by_cls[str(cls)] = segs_dyad
        else:
            segs_dyad = [(lo, 1.0)]
            segs_by_cls[str(cls)] = segs_dyad
        mn_list = []
        for a, b in segs_dyad:
            mn = TC.build_minorant_maps(d_H, (a, b), lay["H_index"][cls], lay["nx"])
            deg_p = mn["deg_p"]
            rhs = cp.Constant(np.zeros(deg_p + 1))
            lst = []
            for name, mult, dmax in mn["blocks"]:
                mons_y = list(range(dmax + 1))
                A = TC.y_map(mons_y, mult, deg_p)
                B = cp.Variable((len(mons_y), len(mons_y)), symmetric=True,
                                name=f"sig_{cls}_{a:.4f}_{name}")
                constraints.append(B >> 0)
                rhs = rhs + A @ cp.vec(B, order="C")
                lst.append((name, A, B))
                n_sig += 1
            constraints.append(rhs == mn["Cp"] @ x_expr + mn["p_const"])
            mn_list.append(((a, b), lst))
        sig_handles[cls] = mn_list

    constraints.append(maps["nrm_row"] @ x_expr == 0)
    prob = cp.Problem(cp.Maximize(e[0]), constraints)
    meta = dict(nSosBlocks=n_blocks, nSigBlocks=n_sig,
                segs_by_cls=segs_by_cls,
                n_scalar_vars=int(sum(v.size for v in prob.variables())),
                n_eq_rows=int(sum(c.size for c in constraints
                                  if not isinstance(c, cp.constraints.PSD))))
    handles = dict(prob=prob, e=e, h=h, psi=psi, c=cvar, Fs=Fs, Fall=Fall,
                   sos=sos_handles, sig=sig_handles)
    return prob, handles, meta


# ============================================================ 求解
def solver_stats(prob):
    ss = prob.solver_stats
    out = {}
    if ss is None:
        return out
    for k in ("solver_name", "status", "num_iters", "solve_time", "extra_stats"):
        v = getattr(ss, k, None)
        if v is not None and isinstance(v, (int, float, str, bool)):
            out[k] = v
    es = out.get("extra_stats")
    if isinstance(es, dict):
        out["extra_stats_keys"] = sorted(es.keys())
        out.pop("extra_stats", None)
    else:
        out.pop("extra_stats", None)
        out["residuals"] = None      # cvxpy/Clarabel 不透出残差表——如实记 null
    return out


def solve_one(ts, M, K, variant, nodes_f, rho_f, verbose=False):
    t0 = time.time()
    maps = TC.assemble_typed(ts, "cut", A0, None, M, K)
    prob, V, meta = build_probe_sdp(maps, variant, nodes_f, rho_f)
    build_s = time.time() - t0
    t1 = time.time()
    prob.solve(solver=cp.CLARABEL, verbose=verbose,
               max_iter=1000, tol_gap_abs=1e-8, tol_gap_rel=1e-8, tol_feas=1e-8,
               time_limit=900.0)
    solve_s = time.time() - t1
    status = prob.status
    e_val = float(V["e"].value[0]) if V["e"].value is not None else float("nan")
    info = dict(variant=variant, M=M, K=K, D=2 * M - 2,
                e_val=e_val,
                build_s=round(build_s, 2), solve_s=round(solve_s, 2),
                **solver_stats(prob), **meta)
    info.setdefault("status", status)
    return info, maps, V, e_val


# ============================================================ 复核（条件版）
def in_gaps(val, segs, tol=1e-12):
    return any(a - tol <= val <= b + tol for a, b in segs)


def sample_gap_triples(rng, lo, segs, n_pts):
    """认证域采样：u,v,t 全在管外分段 ∩ [lo,1] ∩ Gram。拒绝采样。"""
    lens = np.array([b - a for a, b in segs])
    us, vs, ts_ = [], [], []
    tries = 0
    while len(us) < n_pts and tries < 400 * n_pts:
        tries += 1
        m = max(64, n_pts - len(us))
        iu = rng.choice(len(segs), size=m, p=lens / lens.sum())
        su = np.array([segs[i] for i in iu])
        u = rng.uniform(su[:, 0], su[:, 1])
        iv = rng.choice(len(segs), size=m, p=lens / lens.sum())
        sv = np.array([segs[i] for i in iv])
        v = rng.uniform(sv[:, 0], sv[:, 1])
        root = np.sqrt(np.maximum(0.0, (1 - u ** 2) * (1 - v ** 2)))
        tlo, thi = u * v - root, u * v + root
        for j in range(m):
            cand = [(max(tlo[j], a), min(thi[j], b)) for a, b in segs
                    if min(thi[j], b) - max(tlo[j], a) > 1e-12]
            if not cand:
                continue
            w = np.array([b - a for a, b in cand])
            a, b = cand[int(rng.choice(len(cand), p=w / w.sum()))]
            us.append(u[j]); vs.append(v[j]); ts_.append(rng.uniform(a, b))
    return np.array(us), np.array(vs), np.array(ts_), (len(us), tries)


def verify_conditioned(maps, V, e_val, variant, nodes_f, rho_f, X_ttp, rng):
    """数值复核：认证域内 slack ≥ 0、分段 minorant、恒等式残差、PSD、bulge、TTP 处 λ。"""
    ring, ts = maps["ring"], maps["ts"]
    lay = maps["x_layout"]
    d_H = maps["d_H"]
    lo = maps["lo"]
    x = np.concatenate([np.asarray(V["e"].value).ravel(),
                        np.asarray(V["h"].value).ravel(),
                        np.asarray(V["psi"].value).ravel(),
                        np.asarray(V["c"].value).ravel(),
                        np.concatenate([np.asarray(F.value).reshape(-1, order="C")
                                         for F in V["Fall"]])])
    segs_all, _ = gap_segments(nodes_f, rho_f, lo, 1.0)
    # slack 认证域：slack/full 两变体的 slack 都被管因子条件化 ⟹ 采样管外三元组；
    # minorant 认证分段：仅 full 条件化。
    slack_segs = segs_all if variant in ("slack", "full") else [(lo, 1.0)]
    mono_segs = segs_all if variant == "full" else [(lo, 1.0)]

    min_eig, resid_l1 = {}, {}
    slack_min_gap, psd_def_sos = {}, {}
    u_s, v_s, t_s, (n_acc, n_try) = sample_gap_triples(rng, lo, slack_segs, 4000)
    for m in maps["triples"]:
        coeff = maps["slack_maps"][m] @ x
        rhs = np.zeros(ring.nmon)
        for name, A, B in V["sos"][m]:
            rhs += A @ np.asarray(B.value).reshape(-1, order="C")
            Bv = (np.asarray(B.value) + np.asarray(B.value).T) / 2
            min_eig[f"B_{m}_{name}"] = float(np.linalg.eigvalsh(Bv).min())
        resid_l1[str(m)] = float(np.abs(coeff - rhs).sum())
        psd_def_sos[str(m)] = float(sum(
            max(0.0, -min_eig[f"B_{m}_{nm}"]) * 2.0 * B_.shape[0]
            for (nm, _A, B_) in V["sos"][m]))
        if len(u_s):
            slack_min_gap[str(m)] = float(ring.eval_batch(coeff, u_s, v_s, t_s).min())
        else:
            slack_min_gap[str(m)] = None
    # 边界族：u 或 v 取分段端点（管壁 ν_k±ρ 与 lo/1），其余槽在可行∩分段内采样
    edge_vals = []
    for (a, b) in slack_segs:
        for w in (a, b):
            grid = np.linspace(lo, 1.0, 2001)
            feas = [g for g in grid if in_gaps(g, slack_segs)]
            if not feas:
                continue
            fv = np.array(feas)
            for fill in (w, ):
                root = np.sqrt(np.maximum(0.0, (1 - fill ** 2) * (1 - fv ** 2)))
                tlo = np.maximum(fill * fv - root, lo)
                thi = np.minimum(fill * fv + root, 1.0)
                for (aa, bb) in slack_segs:
                    m_ = (fv >= aa) & (fv <= bb)
                    cand = (np.maximum(tlo, aa) < np.minimum(thi, bb))
                    sel = np.nonzero(m_ & cand)[0]
                    if len(sel) == 0:
                        continue
                    sel = sel[:: max(1, len(sel) // 50)][:50]
                    for i in sel:
                        tgrid = np.linspace(max(tlo[i], aa), min(thi[i], bb), 17)
                        edge_vals.append((np.full_like(tgrid, fill), fv[i] * np.ones_like(tgrid), tgrid))
                        edge_vals.append((fv[i] * np.ones_like(tgrid), np.full_like(tgrid, fill), tgrid))
    slack_min_edge = None
    if edge_vals:
        EU = np.concatenate([p[0] for p in edge_vals])
        EV = np.concatenate([p[1] for p in edge_vals])
        ET = np.concatenate([p[2] for p in edge_vals])
        keep = (EU >= lo - 1e-12) & (EV >= lo - 1e-12) & (ET >= lo - 1e-12)
        EU, EV, ET = EU[keep], EV[keep], ET[keep]
        worst = None
        for m in maps["triples"]:
            coeff = maps["slack_maps"][m] @ x
            val = float(ring.eval_batch(coeff, EU, EV, ET).min())
            worst = val if worst is None else min(worst, val)
        slack_min_edge = worst

    # minorant：分段内违规（应 ~0）＋管内 bulge（让界量，full 时可正）
    viol_cls, bulge_cls = {}, {}
    for cls in maps["classes"]:
        hc = x[lay["H_index"][cls]:lay["H_index"][cls] + d_H + 1]
        worst_v, worst_b = 0.0, 0.0
        pieces = mono_segs
        for a, b in pieces:
            tg = np.linspace(a, min(b, 1.0 - 1e-9), 20001)
            Hv = np.polyval(hc[::-1], tg)
            phi = 1.0 / np.sqrt(2.0 - 2.0 * tg)
            worst_v = max(worst_v, float(np.max(Hv - phi)))
        if variant == "full":
            _, tube_ivs = gap_segments(nodes_f, rho_f, lo, 1.0)
            for a, b in tube_ivs:
                tg = np.linspace(a, min(b, 1.0 - 1e-9), 4001)
                Hv = np.polyval(hc[::-1], tg)
                phi = 1.0 / np.sqrt(2.0 - 2.0 * tg)
                worst_b = max(worst_b, float(np.max(Hv - phi)))
        viol_cls[str(cls)] = worst_v
        bulge_cls[str(cls)] = worst_b

    psd_def_F = 0.0
    for X in range(ts.T):
        for k, F in enumerate(V["Fs"][X]):
            Fv = (np.asarray(F.value) + np.asarray(F.value).T) / 2
            d = float(np.linalg.eigvalsh(Fv).min())
            min_eig[f"F_t{X}_k{k}"] = d
            psd_def_F += max(0.0, -d) * ts.sizes[X] * maps["F_sizes"][k] * (ts.n ** 2)

    # TTP 三点处的 λ（让界是否被用到：管内点应允许 < 0）——逐类取全部三元组的最小值
    G = X_ttp @ X_ttp.T
    types = ts.types_of_config()
    ttp_lam = {}
    for (i, j, l) in combinations(range(ts.n), 3):
        tt = sorted([(types[i], i), (types[j], j), (types[l], l)], key=lambda p: p[0])
        (r0, i0), (r1, j0), (r2, l0) = tt
        key = str((r0, r1, r2))
        coeff = maps["slack_maps"][(r0, r1, r2)] @ x
        val = float(ring.eval_batch(coeff, np.array([G[i0, j0]]), np.array([G[i0, l0]]),
                                    np.array([G[j0, l0]]))[0])
        ttp_lam[key] = min(ttp_lam.get(key, val), val)

    defl = (sum(ts.pair_count(*cls) * max(0.0, viol_cls[str(cls)]) for cls in maps["classes"])
            + sum(ts.triple_count(*m) * (resid_l1[str(m)] + psd_def_sos[str(m)])
                  for m in maps["triples"]) + psd_def_F)
    return dict(
        identity_residual_slack=max(resid_l1.values()),
        slack_min_certified_domain=(min(v for v in slack_min_gap.values() if v is not None)
                                    if any(v is not None for v in slack_min_gap.values()) else None),
        slack_min_certified_boundary=slack_min_edge,
        slack_gap_sampling=dict(accepted=int(n_acc), tries=int(n_try)),
        minorant_violation_on_certified_segments=max(viol_cls.values()),
        minorant_violation_by_class=viol_cls,
        minorant_bulge_on_tube=max(bulge_cls.values()),
        minorant_bulge_by_class=bulge_cls,
        min_eig_all_blocks=float(min(min_eig.values())),
        lambda_at_ttp_triples=ttp_lam,
        lambda_at_ttp_min=min(ttp_lam.values()),
        deflation=float(defl),
        e_safe=float(e_val - defl),
    )


# ============================================================ advisory：认证集非空性与 oracle 上界
def family_scan(nodes_f, rho_f, lo, n_grid=4001):
    """tri_cap_prism 单参族上扫：哪些 z 的全部内积在管外∩[lo,1]（认证集非空性）。"""
    zs = np.linspace(0.40, 0.90, n_grid)
    out = []
    for z in zs:
        X = tri_cap_prism(z)
        G = X @ X.T
        t = G[np.triu_indices(9, 1)]
        if t.min() < lo - 1e-12:
            continue
        d = np.min(np.abs(t[:, None] - np.array(nodes_f)[None, :]), axis=1)
        if d.min() >= rho_f - 1e-12:
            d2 = np.linalg.norm(X[:, None, :] - X[None, :, :], axis=2)
            E = float(np.sum(1.0 / d2[np.triu_indices(9, 1)]))
            out.append((float(z), E, float(d.min())))
    return out


def energies_batch(Xs):
    """(N,9,3) → (N,) Coulomb 能量（矢量化）。"""
    D = Xs[:, :, None, :] - Xs[:, None, :, :]
    r = np.sqrt((D ** 2).sum(-1))
    iu = np.triu_indices(9, 1)
    return np.sum(1.0 / r[:, iu[0], iu[1]], axis=1)


def random_scan(nodes_f, rho_f, lo, rng, n=200000, batch=2000, keep_top=8):
    """随机构型中'全管外∩切口内'的占比与最低能量（advisory oracle 上界）。

    返回 (n_qual, min_E, top_Xs)：top_Xs 为能量最低的 keep_top 个全管外构型
    （作为多起点局部极小的种子）。
    """
    nodes = np.array(nodes_f)
    iu = np.triu_indices(9, 1)
    n_qual, cand_E, cand_X = 0, [], []
    for _ in range(n // batch):
        Xb = rng.normal(size=(batch, 9, 3))
        Xb /= np.linalg.norm(Xb, axis=2, keepdims=True)
        G = np.einsum("nik,njk->nij", Xb, Xb)[:, iu[0], iu[1]]      # (batch,36)
        in_cap = G.min(axis=1) >= lo - 1e-12
        d = np.min(np.abs(G[:, :, None] - nodes[None, None, :]), axis=2)
        allout = (d.min(axis=1) >= rho_f - 1e-12) & in_cap
        if np.any(allout):
            sel = np.nonzero(allout)[0]
            E = energies_batch(Xb[sel])
            n_qual += len(sel)
            cand_E.extend(E.tolist())
            cand_X.append(Xb[sel])
    if not cand_E:
        return 0, float("inf"), []
    EX = np.concatenate(cand_X)
    order = np.argsort(np.array(cand_E))
    min_E = float(np.array(cand_E)[order[0]])
    return n_qual, min_E, [EX[i] for i in order[:keep_top]]


def cluster_family_scan(nodes_f, rho_f, lo, n_theta=181, n_delta=121):
    """3 紧簇参价族（簇心等角 θ、簇内角半径 δ）＋单簇 9 点族的能帳（advisory oracle）。

    动机：粗管下随机构型几乎采不到全管外点，但'3 紧簇'型构型（簇内内积 ~1、
    簇间内积 ∈ 负值 gap 段）是全管外集的典型居民——给条件证书一个构造性 oracle。
    """
    nodes = np.array(nodes_f)
    iu = np.triu_indices(9, 1)
    best = []

    def equilateral_centers(theta):
        # 球面等边三角形：三个单位向量两两内积 cos(theta)
        c = np.cos(theta)
        # 取 c1=北移纬线构造：解析构造两两内积 = c 的 3 向量
        # v1=(s,0,c')... 用标准构造：纬度 φ 使 cos(角距)=c
        # 简单做法：在 xz 平面对称构造
        # v_k = normalize((sinθ'·cos(α_k), sinθ'·sin(α_k), cosθ'))，α_k=2πk/3
        # 两两内积 = sin²θ'·cos(120°)+cos²θ' = cos²θ' − sin²θ'/2 = c
        # ⟹ (3cos²θ'−1)/2 = c ⟹ cosθ' = sqrt((2c+1)/3)
        c2 = (2.0 * c + 1.0) / 3.0
        if c2 < 0 or c2 > 1:
            return None
        ct = np.sqrt(c2)
        st = np.sqrt(1.0 - c2)
        out = []
        for k in range(3):
            a = 2.0 * np.pi * k / 3.0
            out.append(np.array([st * np.cos(a), st * np.sin(a), ct]))
        return np.array(out)

    def local_frame(v):
        e1 = np.array([1.0, 0, 0]) if abs(v[0]) < 0.9 else np.array([0, 1.0, 0])
        e1 = e1 - v * np.dot(e1, v)
        e1 /= np.linalg.norm(e1)
        e2 = np.cross(v, e1)
        return e1, e2

    for th in np.linspace(np.pi / 9, np.pi * 0.49, n_theta):
        cs = equilateral_centers(th)
        if cs is None:
            continue
        for dl in np.linspace(0.008, 0.55, n_delta):
            X = []
            for ci in cs:
                e1, e2 = local_frame(ci)
                for k in range(3):
                    a = 2.0 * np.pi * k / 3.0 + 0.35
                    w = ci * np.cos(dl) + (e1 * np.cos(a) + e2 * np.sin(a)) * np.sin(dl)
                    X.append(w)
            X = np.array(X)
            G = (X @ X.T)[iu]
            if G.min() < lo - 1e-12:
                continue
            d = np.min(np.abs(G[:, None] - nodes[None, :]), axis=1)
            if d.min() >= rho_f - 1e-12:
                best.append(float(energies_batch(X[None])[0]))
    return dict(nQualifying=len(best),
                minE=(min(best) if best else None),
                maxE=(max(best) if best else None))


def multistart_local_min(nodes_f, rho_f, lo, rng, seeds=None, n_random=16):
    """SLSQP 多起点局部极小（归一化参数化＋切向投影梯度）：能量地形 advisory。

    seeds＝全管外构型（来自 random_scan）作起点，直接探测认证集附近的 inf E；
    n_random 个额外随机起点给全局地形参照。非全局搜索，只作 oracle 上界改进。
    """
    from scipy.optimize import minimize

    nodes = np.array(nodes_f)
    iu = np.triu_indices(9, 1)
    out = []

    def unpack(y):
        X = y.reshape(9, 3)
        return X / np.linalg.norm(X, axis=1, keepdims=True)

    def obj(y):
        X = unpack(y)
        D = X[:, None, :] - X[None, :, :]
        r2 = (D ** 2).sum(-1) + 1e-18
        if np.min(np.sqrt(r2)[iu]) < 1e-7:
            return 1e6
        return float(np.sum(1.0 / np.sqrt(r2)[iu]))

    def grad(y):
        X = unpack(y)
        D = X[:, None, :] - X[None, :, :]
        r = np.sqrt((D ** 2).sum(-1) + 1e-18)[:, :, None]
        F = D / r ** 3                       # ∂(1/r_ij)/∂x_i（对角≈0）
        g = -F.sum(axis=1)                   # 对 x_i 的梯度（成对求和两侧）
        g = g - (g * X).sum(axis=1, keepdims=True) * X   # 切向投影（球约束一阶）
        return g.reshape(-1)

    starts = [(X, "qualifying") for X in (seeds or [])]
    for _ in range(n_random):
        X0 = rng.normal(size=(9, 3))
        X0 /= np.linalg.norm(X0, axis=1, keepdims=True)
        starts.append((X0, "random"))
    for X0, tag0 in starts:
        res = minimize(obj, X0.reshape(-1), jac=grad, method="SLSQP",
                       options={"maxiter": 250, "ftol": 1e-10})
        X = unpack(res.x)
        G = (X @ X.T)[iu]
        d = np.min(np.abs(G[:, None] - nodes[None, :]), axis=1)
        out.append(dict(E=float(energies_batch(X[None])[0]),
                        seed=tag0,
                        inCap=bool(G.min() >= lo - 1e-9),
                        allOut=bool(d.min() >= rho_f - 1e-9),
                        distToNodes=float(d.min()),
                        converged=bool(res.success)))
    return out


# ============================================================ 证书语义端到端抽查
def certificate_spot_check(maps, V, e_val, X_cfg):
    """在真实全管外构型 X_cfg 上端到端复核条件证书语义（数值，容差级）：

    E − e = Σ_T count·λ_T + Σ_all（恒等式）；逐三元组 λ ≥ −tol（SOS 表示级）、
    Σ_all ≥ −tol、ΣH ≤ E（分段 minorant 级）⟹ E ≥ e − tol。
    与 solve.typed_bound_summary 同思路，但逐三元组展开 λ。
    """
    ring, ts = maps["ring"], maps["ts"]
    lay = maps["x_layout"]
    d_H = maps["d_H"]
    x = np.concatenate([np.asarray(V["e"].value).ravel(),
                        np.asarray(V["h"].value).ravel(),
                        np.asarray(V["psi"].value).ravel(),
                        np.asarray(V["c"].value).ravel(),
                        np.concatenate([np.asarray(F.value).reshape(-1, order="C")
                                         for F in V["Fall"]])])
    G = X_cfg @ X_cfg.T
    types = ts.types_of_config()
    n = ts.n
    # Σ_all（向量化，逐类型）
    sum_all = 0.0
    idx_all = [(i, j, l) for i in range(n) for j in range(n) for l in range(n)]
    for X in range(ts.T):
        sX = maps["sX_cols"][X] @ x[lay["F_index"][X]:lay["F_index"][X] + lay["NF"][X]]
        sel = np.array([ii for ii, (i, _j, _l) in enumerate(idx_all) if types[i] == X])
        uv = np.array([[G[i, j], G[i, l], G[j, l]] for (i, j, l) in
                       (idx_all[k] for k in sel)])
        sum_all += float(ring.eval_batch(sX, uv[:, 0], uv[:, 1], uv[:, 2]).sum())
    # Σ_T（无序三点，最小类型锚定，同 identity_selftest）
    sum_lam, min_lam = 0.0, np.inf
    for (i, j, l) in combinations(range(n), 3):
        tt = sorted([(types[i], i), (types[j], j), (types[l], l)], key=lambda p: p[0])
        (r0, i0), (r1, j0), (r2, l0) = tt
        coeff = maps["slack_maps"][(r0, r1, r2)] @ x
        val = float(ring.eval_batch(coeff, np.array([G[i0, j0]]), np.array([G[i0, l0]]),
                                    np.array([G[j0, l0]]))[0])
        sum_lam += val
        min_lam = min(min_lam, val)
    # ΣH 与 E
    sum_H = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            cls = tuple(sorted((types[i], types[j])))
            hc = x[lay["H_index"][cls]:lay["H_index"][cls] + d_H + 1]
            sum_H += float(np.polyval(hc[::-1], G[i, j]))
    dist = np.linalg.norm(X_cfg[:, None, :] - X_cfg[None, :, :], axis=2)
    E_cfg = float(np.sum(1.0 / dist[np.triu_indices(n, 1)]))
    return dict(E_config=E_cfg, e_val=float(e_val),
                identity_lhs=float(sum_lam + sum_all),
                identity_rhs=float(sum_H - e_val),
                identity_abs_err=float(abs(sum_lam + sum_all - (sum_H - e_val))),
                min_lambda_at_triples=float(min_lam),
                sum_all=float(sum_all),
                sumH_minus_e=float(sum_H - e_val),
                E_minus_e=float(E_cfg - e_val))


# ============================================================ 主流程
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--smoke", action="store_true", help="(4,3) 只跑 uncond+full@2x")
    ap.add_argument("--budget-s", type=float, default=3600.0, help="求解总预算（秒）")
    ap.add_argument("--runs", type=str, default=None,
                    help="显式运行表，';' 分隔，每条 M,K,variant,rhoTag（uncond 用 '-'）——"
                         "追加规模档用")
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()

    t_start = time.time()
    rng = np.random.default_rng(SEED)
    z_star, X_ttp, G_ttp, nodes_f, mults, nodes_dyad = ttp_nodes()
    log(f"TTP z*={z_star:.12f}  nodes={['%.10f' % v for v in nodes_f]}")
    log(f"multiplicities={mults}  dyadic nodes={[str(v) for v in nodes_dyad]}")

    seg_report = {}
    for tag, fr in RHOS:
        segs, tube_ivs = gap_segments(nodes_f, float(fr), A0)
        seg_report[tag] = dict(rho=float(fr), rho_exact=f"{fr.numerator}/{fr.denominator}",
                               gapSegments=segs, tubeIntervals=tube_ivs,
                               gapMeasure=float(sum(b - a for a, b in segs)))
        log(f"ρ={tag} ({float(fr):.7f}): {len(segs)} gap 段 {segs}, "
            f"管测度 {sum(b - a for a, b in segs):.4f}")

    # advisory：认证集非空性与 oracle 上界（族扫描 + 随机扫描 + 簇族 + 多起点局部极小）
    fam, rnd, clu, lmin, seed_cfgs = {}, {}, {}, {}, {}
    for tag, fr in RHOS:
        hits = family_scan(nodes_f, float(fr), A0)
        fam[tag] = dict(nQualifying=len(hits),
                        minE_over_qualifying=(min(h[1] for h in hits) if hits else None),
                        maxDist=(max(h[2] for h in hits) if hits else None),
                        zRange=(min(h[0] for h in hits), max(h[0] for h in hits)) if hits else None)
        nq, me, tops = random_scan(nodes_f, float(fr), A0, rng, n=200000)
        rnd[tag] = dict(nQualifyingOutOf200k=nq,
                        minE_over_qualifying=(me if np.isfinite(me) else None))
        if tops:
            seed_cfgs[tag] = tops[0]
        clu[tag] = cluster_family_scan(nodes_f, float(fr), A0)
        lm = multistart_local_min(nodes_f, float(fr), A0, rng, seeds=tops, n_random=16)
        lmin[tag] = dict(localMinE=[round(r["E"], 6) for r in lm],
                         nSeedStarts=len(tops),
                         nAllOutLocalMinFromSeeds=sum(
                             1 for r in lm if r["allOut"] and r["inCap"]
                             and r["seed"] == "qualifying"),
                         minE_allOutLocalMin=(min((r["E"] for r in lm if r["allOut"] and r["inCap"]),
                                                   default=None)),
                         minE_anyLocalMin=min(r["E"] for r in lm),
                         nConverged=sum(1 for r in lm if r["converged"]))
        log(f"ρ={tag}: 族 {len(hits)}；随机 20 万全管外 {nq} 个"
            + (f"（min E ≈ {me:.4f}）" if np.isfinite(me) else "（随机无全管外）")
            + f"；簇族 qualifying {clu[tag]['nQualifying']}"
            + (f"（min E ≈ {clu[tag]['minE']:.4f}）" if clu[tag]["minE"] else "")
            + f"；多起点 min E {lmin[tag]['minE_anyLocalMin']:.6f}")
    # advisory oracle 上界：min E over 已见全管外构型（条件证书值必须 ≤ 此值 + 容差）
    oracle_ub = {tag: min([v for v in (rnd[tag]["minE_over_qualifying"],
                                       lmin[tag]["minE_allOutLocalMin"],
                                       fam[tag]["minE_over_qualifying"],
                                       clu[tag]["minE"]) if v is not None],
                          default=None) for tag, _fr in RHOS}

    ts = TC.TypeStructure((3, 3, 3))
    plan = []
    if args.runs:
        for spec in args.runs.split(";"):
            M_, K_, var_, rho_ = spec.strip().split(",")
            plan.append((int(M_), int(K_), var_, None if rho_ == "-" else rho_))
    elif args.smoke:
        plan = [(4, 3, "uncond", None), (4, 3, "full", "2x")]
    else:
        plan = [(4, 3, "uncond", None),
                (4, 3, "full", "2x"), (4, 3, "full", "4x"), (4, 3, "slack", "2x"),
                (5, 4, "uncond", None),
                (5, 4, "full", "2x"), (5, 4, "full", "3x"), (5, 4, "full", "4x"),
                (5, 4, "full", "halfgap"), (5, 4, "slack", "2x"),
                (4, 3, "full", "halfgap")]
    runs = []
    spent = 0.0
    for M, K, variant, rtag in plan:
        rho_f = float(dict(RHOS)[rtag]) if rtag else 0.0
        if time.time() - t_start + spent > args.budget_s:
            log(f"[budget] 跳过 ({M},{K}) {variant}@{rtag}（预算尽）")
            runs.append(dict(variant=variant, M=M, K=K, rhoTag=rtag, skipped="budget"))
            continue
        log(f"=== ({M},{K}) {variant}@{rtag} ===")
        try:
            info, maps, V, e_val = solve_one(ts, M, K, variant, nodes_f, rho_f)
        except Exception as exc:                     # noqa: BLE001
            log(f"[error] {exc}")
            runs.append(dict(variant=variant, M=M, K=K, rhoTag=rtag,
                             error=str(exc)))
            continue
        spent += info["solve_s"]
        info["rhoTag"] = rtag
        info["rho"] = rho_f
        # 合法性 assert（任务书口径）：0 < e_val ≤ E*+1e-2
        flags = []
        if not (np.isfinite(e_val) and e_val > 0.0):
            raise SystemExit(f"合法性断言失败：e_val={e_val} 非正/非有限（{variant}@{rtag}）")
        if e_val > E_STAR + 1e-2:
            if variant == "uncond":
                raise SystemExit(f"合法性断言失败：uncond e_val={e_val} > E*+1e-2")
            flags.append("e_val_above_Estar_plus_1e-2（条件档认证集缩小所致的合法现象，见 docstring）")
        # oracle 正确性金丝雀：证书声称 E ≥ e_val 对一切全管外构型成立，
        # 而 oracle_ub 是某个实测全管外构型的能量 ⟹ e_val ≤ oracle_ub + 容差 必须成立
        if rtag is not None and oracle_ub.get(rtag) is not None:
            ob = oracle_ub[rtag]
            info["oracle_upper_bound_sampled"] = ob
            if e_val > ob + 0.05:
                flags.append(f"ORACLE_VIOLATION: e_val={e_val:.6f} > 实测全管外构型 E={ob:.6f}"
                             "（装配/求解器错误金丝雀）")
        if info["status"] not in ("optimal", "optimal_inaccurate"):
            flags.append(f"status={info['status']}")
        info["flags"] = flags
        # 复核
        try:
            check = verify_conditioned(maps, V, e_val, variant, nodes_f, rho_f, X_ttp, rng)
            info["check"] = check
        except Exception as exc:                     # noqa: BLE001
            info["check"] = None
            info["check_error"] = str(exc)
        # 证书语义端到端抽查（在实测全管外构型上；无实测构型的 ρ 档记 None）
        if rtag is not None and variant in ("slack", "full"):
            cfg = seed_cfgs.get(rtag)
            if cfg is not None:
                try:
                    info["certificate_spot_check"] = certificate_spot_check(
                        maps, V, e_val, cfg)
                except Exception as exc:             # noqa: BLE001
                    info["certificate_spot_check"] = None
                    info["spot_check_error"] = str(exc)
        runs.append(info)
        log(f"e_val={e_val:.9f} e_safe={info.get('check', {}).get('e_safe', float('nan')):.9f} "
            f"status={info['status']} iters={info.get('num_iters')} solve_s={info['solve_s']}")

    # ---- 汇总：分离度（同 (M,K) 下 cond − uncond）
    sep = []
    for (M, K) in sorted({(r["M"], r["K"]) for r in runs if "e_val" in r}):
        base = [r for r in runs if r["M"] == M and r["K"] == K
                and r["variant"] == "uncond" and "e_val" in r]
        if not base:
            continue
        b = base[0]
        for r in runs:
            if r["M"] == M and r["K"] == K and r["variant"] != "uncond" and "e_val" in r:
                sep.append(dict(M=M, K=K, variant=r["variant"], rhoTag=r.get("rhoTag"),
                                rho=r.get("rho"),
                                e_val=float(r["e_val"]),
                                e_safe=(r.get("check") or {}).get("e_safe"),
                                delta_e_val_vs_uncond=float(r["e_val"] - b["e_val"]),
                                delta_e_safe_vs_uncond=(
                                    float((r.get("check") or {}).get("e_safe", np.nan)
                                          - (b.get("check") or {}).get("e_safe", np.nan))
                                    if (r.get("check") and b.get("check")) else None),
                                uncond_e_val=float(b["e_val"]),
                                uncond_e_safe=(b.get("check") or {}).get("e_safe")))
    for s in sep:
        log(f"分离度 ({s['M']},{s['K']}) {s['variant']}@{s['rhoTag']}: "
            f"Δe_val={s['delta_e_val_vs_uncond']:+.3e}")

    result = dict(
        kind="tube_probe",
        generated=datetime.now(timezone.utc).isoformat(),
        script="numerics/bounds/tube_probe.py",
        purpose="L3 路线 b tube certificate 限时可行性探针（GAP-REPORT R4 Round 5 清单第 1 项）——"
                "只判可行性，非正式证书；全部数值为探针证据，不进信任链",
        design=dict(
            form="域乘子条件化（Lagrange/Putinar 型）+ 两点 minorant 管外分段＝两段式条件证书",
            slackConditioning="乘子族 g ← g ∪ {(s−ν_k)²−ρ² : k=1..6, s∈{u,v,t}}，"
                              "各配独立 PSD Gram 块（次数 ≤(D−2)//2）⟹ λ_T ≥ 0 的认证域收缩为"
                              " {u,v,t∈[lo,1]}∩Gram∩{全槽管外}＝管外强制；管内不约束＝让界",
            minorantConditioning="H_cls ≤ φ 改为逐分段 [a_r,b_r] ⊂ [lo,1]∖∪_k[ν_k−ρ,ν_k+ρ] "
                                 "独立 Markov–Lukács（末段接 1 单侧 Lukács）＝管内让界（bulge 可正）",
            certificateSemantics="全管外构型（全部 36 内积 ≥ a₀ 且 min_k|t−ν_k| ≥ ρ ∀对）⟹ E ≥ e_out(ρ,M,K)；"
                                 "严格性＝收缩认证域上每个 g_r ≥ 0 ⟹ λ ≥ 0，管外分段上 H ≤ φ，Σ_all ≥ 0（引理 4.1），"
                                 "装配恒等式精确",
            twoPieceArchitecture="piece 1 = 本证书；piece 2 = 某内积距节点 < ρ 的构型 → L2 强制 + L3' 谱管(半径 ρ) + L4 + L6；"
                                 "两段闭合 iff ρ_spec(ε_forcing) ≤ ρ（现状 0.6447 > 全部探针 ρ ⇒ piece 2 不闭合，"
                                 "见 gaps——探针只测 piece 1 的分离能力）",
            whyNotPenalty="罚函数/目标拉格朗日项：非线性、无精确有理表示（dyadic 认证管线接不上）、残差无界无干净认证集；"
                          "域乘子给精确条件语义且与 R1 残差折减机制同构（正式版零新认证机器，只加块）",
            knownLimitation="按槽乘子 ⟹ 认证集是'全部内积都在管外'（窄版）；架构需'某内积在管外'（宽版）——"
                            "宽版实现＝mode='band' 最小对锚定 + 仅 u 槽管因子，本探针未跑（见 gaps）",
            probeDomain=dict(a0=A0, M_K=[[4, 3], [5, 4]], E_star=E_STAR,
                             lambdaMinLb=LAMBDA_MIN_LB, chainTubeRadius=CHAIN_TUBE_R),
        ),
        ttp=dict(zStar=z_star, nodes=nodes_f, multiplicities=mults,
                 nodesDyadic=[str(v) for v in nodes_dyad], dyadicGrid=f"1/{DYAD}"),
        rhoSegments=seg_report,
        certifiedSetProbe=dict(family=fam, randomScan=rnd, clusterFamily=clu,
                               multistart=lmin,
                               oracleUpperBoundSampled=oracle_ub,
                               note="advisory 数值证据：oracleUpperBoundSampled＝已见全管外构型的最低能量，"
                                    "是认证集 inf E 的上界；条件证书 e_val 必须 ≤ 它（金丝雀）。"
                                    "族=tri_cap_prism 单参族；随机=均匀 20 万；簇族=3 紧簇参价族；"
                                    "多起点=SLSQP（种子=随机扫描最优全管外构型）"),
        runs=runs,
        separation=sep,
        budgetS=args.budget_s, wallS=round(time.time() - t_start, 1),
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=1, default=str) + "\n",
                        encoding="utf-8")
    log(f"written {args.out} (wall {result['wallS']}s, solve 累计 {spent:.1f}s)")
    return result


if __name__ == "__main__":
    main()
