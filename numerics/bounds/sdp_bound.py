#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Thomson N=9 的三点 SDP 数值下界（Bachoc–Vallentin / Cohn–Woo 型，按最小内积 m 参数化）。

方法（自 N=7 证明 references/thomson-n7-lean/paper/PAPER.md §4–5.1 移植；与 KLT
arXiv:2609.22077 §4.2–4.3 的 Prop 4.3 同一框架；注：N=7 包的 paper/numerics/
paper_numerics.py 只有能量/Gram/Hessian 复核，并不含 SDP 代码——SDP 构造按 PAPER.md
§4–5.1 的公式重写，结构常数逐条对齐其 §5.2 的证书布局）：

  核：Q_0=1, Q_1=t−uv, Q_{k+2}=2(t−uv)Q_{k+1}−(1−u²)(1−v²)Q_k。
      引理 4.1（正性，PAPER.md Lemma 4.1 / KLT Lemma 4.2）：固定根 x，把 y⊥x 分量复化为
      ζ_y，则 Q_k(u,v,t) = Re(ζ_y^k \\bar{ζ_z}^k)，故 F ⪰ 0 ⇒ Σ_{j,l}⟨F,Y_k⟩ ≥ 0，
      其中 Y_k[a,b] = u^a v^b Q_k；对根求和得 Σ_{i,j,l}⟨F,Y_k⟩ ≥ 0。
      S_k := Y_k 在 (u,v,t) 六置换下的平均（Sym）在全部有序三重点求和下与 Y_k 等价。

  三点恒等式（PAPER.md (1)(2)，KLT (4.4)(4.6)）：s = Σ_k⟨F_k,S_k⟩（F_k ⪰ 0），
      R_s(u,v,t) = (n−2)s(u,v,t) + s(u,u,1)+s(v,v,1)+s(t,t,1) + s(1,1,1)/(n−1),
      slack(u,v,t) = (H(u)+H(v)+H(t))/3 − e/binom(n,2) − R_s(u,v,t),
  则对任何 n 点构型
      dsum(slack) + (n−2)Σ_all = 2(n−2)(Σ_{i<j}H(t_ij) − e)，  Σ_all := Σ_{i,j,l}s ≥ 0。

  推论（three_point_bound_cut，PAPER.md l.5942）：若 slack ≥ 0 于一切 Gram 三点
  （u,v,t ∈ [a,1]、det G = 1+2uvt−u²−v²−t² ≥ 0），且 H ≤ φ = (2−2t)^{−1/2} 于 [a,1)，
  则一切 min_{i<j} x_i·x_j ≥ a 的构型满足 E(x) ≥ e。

SDP（数值）：在 (h, e, F_k, SOS Gram 阵) 上最大化 e，两条多项式恒等式（逐系数相等）：
  (i)  slack ≡ Σ_r g_r·z_rᵀB_rz_r，g_r ∈ {1; u+a, v+a, t+a; 1−u, 1−v, 1−t; detG}，
       B_r ⪰ 0，z_r 单项式次数 ≤ ⌊(D−deg g_r)/2⌋（N=7 Case 1 的 8 块 SOS 结构，
       PAPER.md (3)；在 D=10 时给 56/35×6/20，与 PAPER.md §5.2 表格一致）；
  (ii) minorant：1 − 2yH(1−2y²) ≡ σ_0 + yσ_1 + (b²−y²)σ_2 + y(b²−y²)σ_3，σ_i ⪰ 0，
       b² = (1−a)/2（PAPER.md (4) 的 Lukács 型表示；t ∈ [a,1] ⇔ y ∈ [0,b]）。
  块结构：F_k 尺寸 m_k = M−k（k=0..K−1），H 次数 d_H = 2M−2（N=7 Case 1 为 M=6,K=4；
  KLT N=8 为 M=7,K=6）。

  求解后做数值复核（不构成严格证书）：恒等式残差、PSD 块最小特征值、slack 在随机
  Gram 三点/边界族的逐点最小、H ≤ φ 逐点检查、TTP 候选处 ΣH ≥ e 与 E(TTP) ≥ e。

自检（每次运行先做，不过则拒绝出界）：
  (a) 核自检：随机 Gram 三点上 Q_k(u,v,t) = Re(ζ_y^k\\bar{ζ_z}^k)；
  (b) 正性自检：随机构型 × 随机 PSD F_k ⇒ Σ_{i,j,l}⟨F_k,S_k⟩ ≥ 0（数值验证引理 4.1）；
  (c) 恒等式自检：随机 (h, F) ⇒ dsum(slack) + (n−2)Σ_all = 2(n−2)(ΣH−e)（验证 R_s 装配）。

输出：bounds/results/sdp.json（逐 m：bound、配置、矩阵规模、求解器摘要、复核、自检）。
违反 0 < bound ≤ E* + 1e-6 时打印原因并以 sys.exit(1) 退出。

用法（在 thomson-n9 下，用 numerics/.venv 的解释器）：
  numerics/.venv/bin/python numerics/bounds/sdp_bound.py               # 全流水线
  numerics/.venv/bin/python numerics/bounds/sdp_bound.py --only calib  # 仅 N=7 校准
  numerics/.venv/bin/python numerics/bounds/sdp_bound.py --only m090 --config large
依赖：numpy, scipy（装配/自检/证书复核路径）；cvxpy（Clarabel 主，SCS 兜底）仅
求解路径需要——缺 cvxpy 时模块仍可导入（cp=None），solve_case 入口报可操作错误。
固定种子与求解器参数。
"""
import argparse
import json
import math
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
import scipy.sparse as sp

try:                                    # cvxpy 只在求解路径需要；装配/自检/证书复核
    import cvxpy as cp                  # 路径（sdp_certify.py --solution 等）没有它
except ModuleNotFoundError:             # 也必须能跑——置 None，solve_case 入口拦截
    cp = None


def require_cvxpy():
    """求解路径入口检查：给出可操作的错误而不是深层 traceback。"""
    if cp is None:
        raise ModuleNotFoundError(
            "cvxpy 不可用：求解需要 numerics/.venv 的解释器，"
            "例如 `numerics/.venv/bin/python numerics/bounds/sdp_bound.py`。"
            "（装配/自检不需要 cvxpy；sdp_certify.py 的认证路径可用 --solution "
            "复用已落盘解数据）")

CFG = dict(
    N=9,
    SEED=20261003,
    CONFIGS={"small": (6, 4), "medium": (7, 6), "midlarge": (8, 6), "large": (9, 6)},
    PRIMARY_M=-0.9,
    CALIB=dict(N=7, a=-0.9, config="small",
               expect=14.453300),  # N=7 论文 Case 1 的 e = E(P)+3.2259e-4（PAPER.md §5.2）
    SOLVER=dict(max_iter=1000, tol_gap_abs=1e-8, tol_gap_rel=1e-8,
                tol_feas=1e-8, time_limit=420.0),
    FALLBACK=dict(eps=1e-9, max_iters=30000, time_limit_secs=420.0),
    # 复核接受阈（数值证书的容差；超阈的解不作为出界依据）
    ACCEPT=dict(identity_residual=1e-5, minorant_violation=1e-7,
                slack_min=-1e-6, min_eig=-1e-7),
    GRID_NTRIPLE=40000,   # 随机 Gram 三点数（slack 复核）
    GRID_NT=40001,        # minorant 逐点格点数
    CALIB_TOL=5e-3,       # N=7 校准容差
)

E_STAR_FALLBACK = 25.759986531


# ============================================================ 三元多项式（稠密，总次数 ≤ D）
class Poly3:
    def __init__(self, D):
        self.D = D
        self.mons, self.index = [], {}
        for i in range(D + 1):
            for j in range(D + 1 - i):
                for l in range(D + 1 - i - j):
                    self.index[(i, j, l)] = len(self.mons)
                    self.mons.append((i, j, l))
        self.nmon = len(self.mons)
        self.perm_maps = [
            np.array([self.index[e] for e in
                      [(i, j, l) for (i, j, l) in self.mons]]),
            np.array([self.index[(j, i, l)] for (i, j, l) in self.mons]),
            np.array([self.index[(l, j, i)] for (i, j, l) in self.mons]),
            np.array([self.index[(i, l, j)] for (i, j, l) in self.mons]),
            np.array([self.index[(l, i, j)] for (i, j, l) in self.mons]),
            np.array([self.index[(j, l, i)] for (i, j, l) in self.mons]),
        ]

    def zero(self):
        return np.zeros(self.nmon)

    def mono(self, e, c=1.0):
        v = self.zero()
        v[self.index[e]] = c
        return v

    def mul(self, a, b):
        out = self.zero()
        for p in np.nonzero(a)[0]:
            ep = self.mons[p]
            ca = a[p]
            for q in np.nonzero(b)[0]:
                eq = self.mons[q]
                e = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                if e not in self.index:
                    raise OverflowError(f"degree {sum(e)} exceeds D={self.D}")
                out[self.index[e]] += ca * b[q]
        return out

    def symmetrize(self, a):
        return sum(a[m] for m in self.perm_maps) / 6.0

    def subst_xx1(self, c, slot):
        """s(x,x,1)：u^i v^j t^l → x^{i+j}（x 取 slot 号变量）。"""
        out = self.zero()
        for p in np.nonzero(c)[0]:
            i, j, _l = self.mons[p]
            e = [0, 0, 0]
            e[slot] = i + j
            out[self.index[tuple(e)]] += c[p]
        return out

    def eval_batch(self, c, u, v, t):
        u = np.asarray(u, dtype=float)
        v = np.asarray(v, dtype=float)
        t = np.asarray(t, dtype=float)
        pw = [np.ones_like(u)] + [None] * self.D
        for i in range(1, self.D + 1):
            pw[i] = pw[i - 1] * u
        pv = [np.ones_like(u)] + [None] * self.D
        for i in range(1, self.D + 1):
            pv[i] = pv[i - 1] * v
        pt = [np.ones_like(u)] + [None] * self.D
        for i in range(1, self.D + 1):
            pt[i] = pt[i - 1] * t
        val = np.zeros_like(u)
        for p in np.nonzero(c)[0]:
            i, j, l = self.mons[p]
            val += c[p] * pw[i] * pv[j] * pt[l]
        return val


def build_Q(ring, K):
    """Q_0=1, Q_1=t−uv, Q_{k+2}=2(t−uv)Q_{k+1}−(1−u²)(1−v²)Q_k。"""
    t_m_uv = ring.mono((0, 0, 1), 1.0) - ring.mono((1, 1, 0), 1.0)   # t − uv
    om = (ring.mono((0, 0, 0), 1.0) - ring.mono((2, 0, 0), 1.0)
          - ring.mono((0, 2, 0), 1.0) + ring.mono((2, 2, 0), 1.0))  # (1−u²)(1−v²)
    Qs = [ring.mono((0, 0, 0), 1.0), t_m_uv]
    while len(Qs) < K:
        Qs.append(2.0 * ring.mul(t_m_uv, Qs[-1]) - ring.mul(om, Qs[-2]))
    return Qs[:K]


def unit_exp(slot):
    e = [0, 0, 0]
    e[slot] = 1
    return tuple(e)


# ============================================================ 地图装配（s 与 slack 对变量的线性地图）
def assemble_maps(n, a, M, K):
    """返回 dict：ring, Qs, S_cols（s 对 F 的系数）、R_cols（R_s 对 F 的系数）、
    Ch（slack 对 h）、c_e（slack 对 e）。slack = Ch@h + c_e·e − R_cols@vec(F)。"""
    D = 2 * M - 2
    ring = Poly3(D)
    Qs = build_Q(ring, K)
    nmon, n2 = ring.nmon, n * (n - 1) // 2
    d_H = D

    Ch = np.zeros((nmon, d_H + 1))          # (H(u)+H(v)+H(t))/3
    for j in range(d_H + 1):
        for slot in range(3):
            e = [0, 0, 0]
            e[slot] = j
            Ch[ring.index[tuple(e)], j] += 1.0 / 3.0
    c_e = ring.zero()
    c_e[ring.index[(0, 0, 0)]] = -1.0 / n2

    S_cols, R_cols, S_index = [], [], {}
    for k in range(K):
        m_k = M - k
        for a_ in range(m_k):
            for b_ in range(m_k):
                Y = ring.mul(ring.mono((a_, b_, 0), 1.0), Qs[k])
                S = ring.symmetrize(Y)
                R = (n - 2) * S + sum(ring.subst_xx1(S, slot) for slot in range(3))
                # s(1,1,1)＝S 在 (1,1,1) 的值＝全部系数之和（每个单项式取值 1），
                # 不是常数项（Q_k(1,1,1)=δ_{k0}，PAPER.md §4 "Boundary values"）
                R[ring.index[(0, 0, 0)]] += S.sum() / (n - 1)
                S_index[(k, a_, b_)] = len(S_cols)
                S_cols.append(S)
                R_cols.append(R)
    return dict(ring=ring, Qs=Qs, S_cols=S_cols, R_cols=R_cols, S_index=S_index,
                Ch=Ch, c_e=c_e, D=D, d_H=d_H, n=n, a=a, M=M, K=K,
                F_sizes=[M - k for k in range(K)])


def dense_to_sparse(cols):
    """列向量列表 → csr 矩阵（每列一个 SDP 变量的系数行）。"""
    rows, colsidx, vals = [], [], []
    for j, c in enumerate(cols):
        nz = np.nonzero(c)[0]
        rows.extend(nz.tolist())
        colsidx.extend([j] * len(nz))
        vals.extend(c[nz].tolist())
    return sp.csr_matrix((vals, (rows, colsidx)),
                         shape=(cols[0].shape[0], len(cols)))


def sos_block_map(ring, g_nonzeros, mons):
    """g·zᵀBz 的线性地图（行主序列索引 p*m+q，配 cp.vec(B, order='C')）。"""
    m = len(mons)
    rows, cols, vals = [], [], []
    for p in range(m):
        ep = mons[p]
        for q in range(m):
            eq = mons[q]
            base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
            for (eg, cg) in g_nonzeros:
                e = (base[0] + eg[0], base[1] + eg[1], base[2] + eg[2])
                if e not in ring.index:
                    raise OverflowError(f"SOS 块次数溢出: {e}")
                rows.append(ring.index[e])
                cols.append(p * m + q)
                vals.append(cg)
    return sp.csr_matrix((vals, (rows, cols)), shape=(ring.nmon, m * m))


def mons_upto(ring, dmax):
    return [e for e in ring.mons if sum(e) <= dmax]


# ============================================================ SDP 组装
def build_sdp(maps):
    ring, n, a = maps["ring"], maps["n"], maps["a"]
    D, d_H, nmon = maps["D"], maps["d_H"], maps["ring"].nmon
    K = maps["K"]

    h = cp.Variable(d_H + 1, name="h")
    e = cp.Variable(name="e")
    Fvars = [cp.Variable((m, m), symmetric=True, name=f"F{k}")
             for k, m in enumerate(maps["F_sizes"])]
    AR = dense_to_sparse(maps["R_cols"])
    AR_blocks, off = [], 0
    for m in maps["F_sizes"]:
        w = m * m
        AR_blocks.append(sp.csr_matrix(AR[:, off:off + w]))
        off += w
    F_term = sum(ARb @ cp.vec(F, order="C")
                 for ARb, F in zip(AR_blocks, Fvars))
    lhs_slack = maps["Ch"] @ h + maps["c_e"] * e - F_term

    detG = [((0, 0, 0), 1.0), ((1, 1, 1), 2.0), ((2, 0, 0), -1.0),
            ((0, 2, 0), -1.0), ((0, 0, 2), -1.0)]
    blocks = [("1", [((0, 0, 0), 1.0)], mons_upto(ring, D // 2))]
    for var, slot in (("u", 0), ("v", 1), ("t", 2)):
        # cut 乘子：var − a（a=−9/10 时即 PAPER.md:146 的 "u+9/10"），在域 var ≥ a 上非负
        blocks.append((f"{var}-a", [((0, 0, 0), -a), (unit_exp(slot), 1.0)],
                       mons_upto(ring, (D - 1) // 2)))
    for var, slot in (("u", 0), ("v", 1), ("t", 2)):
        blocks.append((f"1-{var}", [((0, 0, 0), 1.0), (unit_exp(slot), -1.0)],
                       mons_upto(ring, (D - 1) // 2)))
    blocks.append(("detG", detG, mons_upto(ring, (D - 3) // 2)))

    constraints = []
    constraints += [F >> 0 for F in Fvars]     # 引理 4.1 需要 F_k ⪰ 0（正性矩条件）
    sos_rhs = cp.Constant(np.zeros(nmon))
    sos_vars = []
    block_sizes = []
    for name, gnz, mons in blocks:
        A = sos_block_map(ring, gnz, mons)
        m_ = len(mons)
        B = cp.Variable((m_, m_), symmetric=True, name=f"B_{name}")
        constraints.append(B >> 0)
        sos_rhs = sos_rhs + A @ cp.vec(B, order="C")
        sos_vars.append((name, A, B))
        block_sizes.append((name, m_))
    constraints.append(sos_rhs == lhs_slack)

    # ---- minorant：p(y) = 1 − 2yH(1−2y²) 于 [0,b] 的 Lukács 型 SOS 表示
    b2 = (1.0 - a) / 2.0
    deg_p = 2 * d_H + 1
    Csub = np.zeros((deg_p + 1, d_H + 1))   # H(1−2y²) 的系数：y^{2m} ← Σ_i h_i C(i,m)(−2)^m
    for i in range(d_H + 1):
        for m in range(i + 1):
            Csub[2 * m, i] += math.comb(i, m) * ((-2.0) ** m)
    Cp = np.zeros((deg_p + 1, d_H + 1))     # p = 1 − 2y·H(1−2y²)：奇次行 −2·Csub
    for r in range(1, deg_p + 1, 2):
        Cp[r, :] = -2.0 * Csub[r - 1, :]
    p_const = np.zeros(deg_p + 1)
    p_const[0] = 1.0

    def y_map(mons_y, mult):
        m_ = len(mons_y)
        rows, cols, vals = [], [], []
        for p in range(m_):
            for q in range(m_):
                base = mons_y[p] + mons_y[q]
                for (eg, cg) in mult:
                    r_ = base + eg
                    if r_ > deg_p:
                        raise OverflowError("minorant 块次数溢出")
                    rows.append(r_)
                    cols.append(p * m_ + q)
                    vals.append(cg)
        return sp.csr_matrix((vals, (rows, cols)), shape=(deg_p + 1, m_ * m_))

    sig_def = [("sig0", list(range(0, d_H + 1)), [(0, 1.0)]),
               ("sig1", list(range(0, d_H + 1)), [(1, 1.0)]),
               ("sig2", list(range(0, d_H)), [(0, b2), (2, -1.0)]),
               ("sig3", list(range(0, d_H)), [(1, b2), (3, -1.0)])]
    sig_rhs = cp.Constant(np.zeros(deg_p + 1))
    sig_vars = []
    for name, mons_y, mult in sig_def:
        A = y_map(mons_y, mult)
        m_ = len(mons_y)
        B = cp.Variable((m_, m_), symmetric=True, name=name)
        constraints.append(B >> 0)
        sig_rhs = sig_rhs + A @ cp.vec(B, order="C")
        sig_vars.append((name, A, B, mons_y, mult))
    constraints.append(sig_rhs == Cp @ h + p_const)

    prob = cp.Problem(cp.Maximize(e), constraints)
    meta = dict(n=n, a=a, M=maps["M"], K=K, d_H=d_H, D=D, nmon_slack=nmon,
                F_sizes=maps["F_sizes"], sos_block_sizes=block_sizes,
                sig_sizes=[len(mly) for _, mly, _ in sig_def],
                n_scalar_vars=int(sum(v.size for v in prob.variables())),
                n_eq_rows=int(sum(c.size for c in constraints
                                  if not isinstance(c, cp.constraints.PSD))))
    handles = dict(prob=prob, h=h, e=e, F=Fvars, sos=sos_vars, sig=sig_vars,
                   Cp=Cp, p_const=p_const, b2=b2, deg_p=deg_p,
                   AR=AR, block_sizes=block_sizes)
    return prob, handles, meta


# ============================================================ 自检（核、正性、三点恒等式）
def random_config(rng, n):
    X = rng.normal(size=(n, 3))
    return X / np.linalg.norm(X, axis=1, keepdims=True)


def gram_triples(X):
    G = X @ X.T
    n = len(X)
    idx = [(i, j, l) for i in range(n) for j in range(n) for l in range(n)]
    uvl = np.array([[G[i, j], G[i, l], G[j, l]] for (i, j, l) in idx])
    return idx, uvl


def kernel_selftest(maps, rng, n_points=500):
    """(a) Q_k = Re(ζ^k \\bar{ζ}^k)；(b) 引理 4.1：Σ_{i,j,l}⟨F,S_k⟩ ≥ 0（随机 PSD F）。"""
    ring, K = maps["ring"], maps["K"]
    Qs = maps["Qs"]
    # (a) 核恒等式
    x = rng.normal(size=(n_points, 3))
    x /= np.linalg.norm(x, axis=1, keepdims=True)
    y = rng.normal(size=(n_points, 3))
    y /= np.linalg.norm(y, axis=1, keepdims=True)
    z = rng.normal(size=(n_points, 3))
    z /= np.linalg.norm(z, axis=1, keepdims=True)
    u = np.sum(x * y, axis=1)
    v = np.sum(x * z, axis=1)
    t = np.sum(y * z, axis=1)
    # ζ_y：y ⊥ x 分量在 x 的正交补平面里的复坐标
    def zeta(xv, w):
        e1 = np.cross(xv, [1.0, 0, 0]) if abs(xv[0]) < 0.9 else np.cross(xv, [0, 1.0, 0])
        e1 = e1 / np.linalg.norm(e1)
        e2 = np.cross(xv, e1)
        comp = w - np.dot(w, xv) * xv
        return np.dot(comp, e1) + 1j * np.dot(comp, e2)
    worst = 0.0
    for s in range(n_points):
        zy, zz = zeta(x[s], y[s]), zeta(x[s], z[s])
        for k in range(K):
            lhs = ring.eval_batch(Qs[k], np.array([u[s]]), np.array([v[s]]),
                                  np.array([t[s]]))[0]
            rhs = (zy * np.conj(zz)) ** k
            worst = max(worst, abs(lhs - rhs.real))
    # (b) 正性：Σ_{i,j,l}⟨F,S_k⟩ ≥ 0
    n = maps["n"]
    X = random_config(rng, n)
    _, uvl = gram_triples(X)
    total = 0.0
    for k in range(K):
        m_k = maps["F_sizes"][k]
        F = rng.normal(size=(m_k, m_k))
        F = F @ F.T
        acc = 0.0
        for (a_, b_) in [(a_, b_) for a_ in range(m_k) for b_ in range(m_k)]:
            S = maps["S_cols"][maps["S_index"][(k, a_, b_)]]
            acc += F[a_, b_] * ring.eval_batch(S, uvl[:, 0], uvl[:, 1], uvl[:, 2]).sum()
        total += acc
    scale = max(1.0, abs(total))
    return dict(Q_identity_max_err=float(worst),
                positivity_sum=float(total),
                positivity_relative=float(total / scale),
                positivity_ok=bool(total >= -1e-8 * scale))


def identity_selftest(maps, rng):
    """(c) dsum(slack) + (n−2)Σ_all = 2(n−2)(Σ_{i<j}H − e)（随机 h、随机 PSD F、随机 e）。"""
    ring, n = maps["ring"], maps["n"]
    d_H = maps["d_H"]
    h = rng.normal(size=d_H + 1)
    e0 = rng.normal()
    Fvals = {}
    s_coeff = ring.zero()
    R_coeff = ring.zero()
    for k, m_k in enumerate(maps["F_sizes"]):
        F = rng.normal(size=(m_k, m_k))
        F = F @ F.T
        Fvals[k] = F
    for (k, a_, b_), gi in maps["S_index"].items():
        s_coeff = s_coeff + Fvals[k][a_, b_] * maps["S_cols"][gi]
        R_coeff = R_coeff + Fvals[k][a_, b_] * maps["R_cols"][gi]
    slack_coeff = maps["Ch"] @ h + maps["c_e"] * e0 - R_coeff
    X = random_config(rng, n)
    idx, uvl = gram_triples(X)
    s_all = ring.eval_batch(s_coeff, uvl[:, 0], uvl[:, 1], uvl[:, 2]).sum()
    dist = [(i, j, l) for (i, j, l) in idx if i != j and j != l and i != l]
    duvl = np.array([[float(np.dot(X[i], X[j])), float(np.dot(X[i], X[l])),
                      float(np.dot(X[j], X[l]))] for (i, j, l) in dist])
    dsum = ring.eval_batch(slack_coeff, duvl[:, 0], duvl[:, 1], duvl[:, 2]).sum()
    G = X @ X.T
    iu = np.triu_indices(n, 1)
    sumH = np.polyval(h[::-1], G[iu]).sum()
    lhs = dsum + (n - 2) * s_all
    rhs = 2.0 * (n - 2) * (sumH - e0)
    return dict(lhs=float(lhs), rhs=float(rhs),
                abs_err=float(abs(lhs - rhs)),
                rel_err=float(abs(lhs - rhs) / max(1.0, abs(rhs))),
                ok=bool(abs(lhs - rhs) <= 1e-8 * max(1.0, abs(rhs))))


# ============================================================ 求解与复核
def solve_case(n, a, M, K, verbose=False):
    require_cvxpy()
    t0 = time.time()
    maps = assemble_maps(n, a, M, K)
    prob, V, meta = build_sdp(maps)
    build_s = time.time() - t0
    t1 = time.time()
    try:
        prob.solve(solver=cp.CLARABEL, verbose=verbose,
                   max_iter=CFG["SOLVER"]["max_iter"],
                   tol_gap_abs=CFG["SOLVER"]["tol_gap_abs"],
                   tol_gap_rel=CFG["SOLVER"]["tol_gap_rel"],
                   tol_feas=CFG["SOLVER"]["tol_feas"],
                   time_limit=CFG["SOLVER"]["time_limit"])
        solver, status = "CLARABEL", prob.status
    except Exception as exc:
        print(f"[warn] Clarabel 异常（{exc}），SCS 兜底", flush=True)
        prob.solve(solver=cp.SCS, verbose=verbose,
                   eps=CFG["FALLBACK"]["eps"],
                   max_iters=CFG["FALLBACK"]["max_iters"],
                   time_limit_secs=CFG["FALLBACK"]["time_limit_secs"])
        solver, status = "SCS", prob.status
    solve_s = time.time() - t1
    e_val = float(V["e"].value) if V["e"].value is not None else float("nan")
    info = dict(solver=solver, status=status, build_s=round(build_s, 2),
                solve_s=round(solve_s, 2),
                objective=prob.value if prob.value is not None else None, **meta)
    if status not in ("optimal", "optimal_inaccurate") or V["e"].value is None:
        return e_val, info, None, maps, V
    check = verify(maps, V, e_val)
    return e_val, info, check, maps, V


def verify(maps, V, e_val):
    """数值复核：恒等式残差、PSD 最小特征值、slack/H 的逐点检查、TTP 处的界。"""
    ring = maps["ring"]
    a = maps["a"]
    h = V["h"].value
    Fvec = np.concatenate([np.asarray(F.value).reshape(-1) for F in V["F"]])
    slack_coeff = maps["Ch"] @ h + maps["c_e"] * e_val - V["AR"] @ Fvec
    rhs = np.zeros(ring.nmon)
    min_eig = {}
    for name, A, B in V["sos"]:
        rhs += A @ np.asarray(B.value).reshape(-1, order="C")
        Bv = (np.asarray(B.value) + np.asarray(B.value).T) / 2
        min_eig[f"B_{name}"] = float(np.linalg.eigvalsh(Bv).min())
    resid_slack = float(np.max(np.abs(slack_coeff - rhs)))
    for k, F in enumerate(V["F"]):
        Fv = (np.asarray(F.value) + np.asarray(F.value).T) / 2
        min_eig[f"F{k}"] = float(np.linalg.eigvalsh(Fv).min())
    # minorant 恒等式残差
    deg_p = V["deg_p"]
    p_lhs = np.zeros(deg_p + 1)
    for name, A, B, mons_y, mult in V["sig"]:
        p_lhs += A @ np.asarray(B.value).reshape(-1, order="C")
        Bv = (np.asarray(B.value) + np.asarray(B.value).T) / 2
        min_eig[name] = float(np.linalg.eigvalsh(Bv).min())
    p_rhs = V["Cp"] @ h + V["p_const"]
    resid_minorant = float(np.max(np.abs(p_lhs - p_rhs)))

    # slack ≥ 0 于随机 Gram 三点（内积 ≥ a）
    rng = np.random.default_rng(CFG["SEED"])
    nt = CFG["GRID_NTRIPLE"] * 4
    xs = rng.normal(size=(nt, 3)); xs /= np.linalg.norm(xs, axis=1, keepdims=True)
    ys = rng.normal(size=(nt, 3)); ys /= np.linalg.norm(ys, axis=1, keepdims=True)
    zs = rng.normal(size=(nt, 3)); zs /= np.linalg.norm(zs, axis=1, keepdims=True)
    u = np.sum(xs * ys, axis=1); v = np.sum(xs * zs, axis=1); t = np.sum(ys * zs, axis=1)
    keep = (u >= a) & (v >= a) & (t >= a)
    u, v, t = u[keep], v[keep], t[keep]
    sl_random = ring.eval_batch(slack_coeff, u, v, t) if len(u) else np.array([np.nan])
    # 边界族：(x,x,1) 三槽（detG=0 面）+ (a,a,t) 型（cut 边界；仅取 Gram 可行段：
    # (a,a,t) 的 detG=(1−t)(1+t−2a²)，故 t ∈ [2a²−1, 1]，否则该点不在证书域内）
    tg = np.linspace(a, 1.0, CFG["GRID_NT"] // 8)
    ones = np.ones_like(tg)
    sl_b = [ring.eval_batch(slack_coeff, tg, tg, ones),
            ring.eval_batch(slack_coeff, tg, ones, tg),
            ring.eval_batch(slack_coeff, ones, tg, tg)]
    t_lo = max(a, 2.0 * a * a - 1.0)
    if t_lo <= 1.0:
        tg2 = np.linspace(t_lo, 1.0, CFG["GRID_NT"] // 8)
        for _ in range(3):
            args = [np.full_like(tg2, a), np.full_like(tg2, a), tg2]
            sl_b.append(ring.eval_batch(slack_coeff, args[0], args[1], args[2]))
    sl_boundary = np.min(np.concatenate(sl_b))
    # H ≤ φ 于 [a, 1)：粗格点（快查）＋细格点（折减用，含 H'' 插值余量）
    tgrid = np.linspace(a, 1.0 - 1e-9, CFG["GRID_NT"])
    Hv = np.polyval(h[::-1], tgrid)
    phi = 1.0 / np.sqrt(2.0 - 2.0 * tgrid)
    viol_minorant = float(np.max(Hv - phi))
    tfine = np.linspace(a, 1.0 - 1e-10, 10 * CFG["GRID_NT"])
    Hf = np.polyval(h[::-1], tfine)
    phif = 1.0 / np.sqrt(2.0 - 2.0 * tfine)
    dt = float(tfine[1] - tfine[0])
    Hdd = float(sum(j * (j - 1) * abs(h[j]) for j in range(len(h))))
    viol_fine = float(np.max(Hf - phif)) + dt * dt / 8.0 * Hdd
    n = maps["n"]
    check = dict(identity_residual_slack=resid_slack,
                 identity_residual_minorant=resid_minorant,
                 identity_l1_slack=float(np.abs(slack_coeff - rhs).sum()),
                 min_eig=min_eig,
                 slack_min_random=float(sl_random.min()),
                 slack_min_boundary=float(sl_boundary),
                 minorant_max_violation=viol_minorant,
                 n_gram_points=int(len(u)))

    # ---- 折减（数值证书 → 诚实下界 e_safe = e − Δ）：
    # E ≥ Σφ ≥ ΣH − 36·violH（逐点）
    # ΣH − e = [dsum(slack) + (n−2)Σ_all]/(2(n−2))（对返回的 (h,e,F) 精确成立）
    # slack(pt) ≥ −(‖resid‖₁ + Σ_r 2·m_r·max(0,−λmin(B_r)))，对一切 Gram 点
    #   （域上 g_r ∈ [0,2]、detG ≤ 1（Hadamard），单项式绝对值 ≤ 1）
    # Σ_all ≥ −max(0,−λmin(F))·2n²Σ_k m_k（引理 4.1 的 PSD 亏损）
    n2 = n * (n - 1) // 2
    ntrip = n * (n - 1) * (n - 2)
    psd_def_sos = float(sum(max(0.0, -min_eig[f"B_{nm}"]) * 2.0 * B_.shape[0]
                            for (nm, _A, B_) in V["sos"]))
    psd_def_f = float(max(0.0, -min(min_eig[f"F{k}"] for k in range(len(V["F"]))))
                      * 2.0 * n * n * sum(m_ for m_ in maps["F_sizes"]))
    delta = (float(n2) * viol_fine
             + ntrip * (check["identity_l1_slack"] + psd_def_sos) / (2.0 * (n - 2))
             + psd_def_f / (2.0 * (n - 2)))
    check.update(viol_fine=viol_fine, psd_deficit_sos=psd_def_sos,
                 psd_deficit_F=psd_def_f, deflation=float(delta),
                 e_safe=float(e_val - delta))
    acc = CFG["ACCEPT"]
    check["accepted"] = bool(
        resid_slack <= acc["identity_residual"]
        and resid_minorant <= acc["identity_residual"]
        and viol_minorant <= acc["minorant_violation"]
        and float(sl_random.min()) >= acc["slack_min"]
        and sl_boundary >= acc["slack_min"]
        and min(min_eig.values()) >= acc["min_eig"])
    return check


def ttp_check(h, e_val, E_star):
    """在 TTP 候选（z* 由 numerics/family.py 的构造＋Brent 求得）处复核 ΣH ≥ e、E ≥ e。"""
    try:
        sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
        from family import tri_cap_prism  # noqa: E402
        from scipy.optimize import minimize_scalar  # noqa: E402
        fE = lambda z: float(np.sum(
            1.0 / np.linalg.norm(tri_cap_prism(z)[:, None, :] - tri_cap_prism(z)[None, :, :],
                                 axis=2)[np.triu_indices(9, 1)]))
        res = minimize_scalar(fE, bounds=(0.4, 0.9), method="bounded",
                              options={"xatol": 1e-13})
        z_star = float(res.x)
        X = tri_cap_prism(z_star)
        G = X @ X.T
        iu = np.triu_indices(9, 1)
        E_ttp = float(fE(z_star))
        sumH = float(np.polyval(h[::-1], G[iu]).sum())
        return dict(z_star=z_star, E_ttp=E_ttp, sumH_at_ttp=sumH,
                    min_inner=float(G[iu].min()),
                    E_minus_e=float(E_ttp - e_val),
                    sumH_minus_e=float(sumH - e_val),
                    E_matches_star=bool(abs(E_ttp - E_star) <= 1e-6))
    except Exception as exc:
        return dict(error=f"TTP 复核失败: {exc}")


# ============================================================ 主流程
def main():
    ap = argparse.ArgumentParser(description="N=9 三点 SDP 下界（Bachoc–Vallentin / Cohn–Woo）")
    ap.add_argument("--only", choices=["calib", "m090", "m095", "selftest"], default=None)
    ap.add_argument("--config", choices=list(CFG["CONFIGS"]), default=None)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(CFG["SEED"])

    here = Path(__file__).resolve().parent
    out_path = Path(args.out) if args.out else here / "results" / "sdp.json"
    energies_path = here.parents[2] / "thomson-workflow" / "data" / "energies.json"
    try:
        with open(energies_path) as f:
            E_star = float(json.load(f)["energies"]["9"]["value"])
        src = str(energies_path)
    except Exception as exc:
        E_star, src = E_STAR_FALLBACK, f"fallback 常数（energies.json 不可读: {exc}）"
        print(f"[warn] 使用 E* 常数 {E_star}（{exc}）", flush=True)

    results = {"kind": "sdp", "script": "sdp_bound.py",
               "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
               "seed": CFG["SEED"],
               "target": {"N": CFG["N"], "E_star": E_star, "source": src},
               "solver": {"primary": "CLARABEL", **CFG["SOLVER"],
                          "fallback": "SCS", **CFG["FALLBACK"]},
               "method": ("Bachoc–Vallentin / Cohn–Woo 三点 SDP，自 N=7 PAPER.md §4–5.1 移植"
                          "（核 Q_k、S_k=Sym(u^a v^b Q_k)、三点恒等式 (1)(2)、8 块 SOS 模"
                          "（1/cut×3/cap×3/detG）、Lukács 型 minorant (4)）；"
                          "N=7 包不含 SDP 数值代码，本脚本按论文公式重建"),
               "selftests": {}, "cases": []}
    # 复跑时合并已有结果（同 (m, config) 覆盖，其他保留；校准块一并保留）。
    # 溯源以每个 case 的 run 块为准（timestamp/argv/solver_opts/repro）；
    # 无 run 块的条目是旧版脚本合并进来的遗留数据（当前默认流水线 run_m 只跑
    # midlarge+small，不会再生它们）——主界断言不依赖遗留条目。
    if out_path.exists():
        try:
            old = json.load(open(out_path))
            for c in old.get("cases", []):
                results["cases"].append(c)
            if "calibration" in old and args.only != "calib":
                results["calibration"] = old["calibration"]
            for k, v in old.get("selftests", {}).items():
                results["selftests"][k] = v
        except Exception:
            pass

    exit_code = 0

    def selftests_for(n, a, M, K):
        maps = assemble_maps(n, a, M, K)
        ks = kernel_selftest(maps, rng)
        ids = identity_selftest(maps, rng)
        tag = f"N{n}_M{M}"
        results["selftests"][tag] = dict(kernel=ks, identity=ids)
        ok = ks["positivity_ok"] and ids["ok"]
        print(f"[selftest:{tag}] Q 恒等式 max err = {ks['Q_identity_max_err']:.2e}；"
              f"正性和 = {ks['positivity_sum']:.3e}（ok={ks['positivity_ok']}）；"
              f"恒等式 |lhs−rhs|/scale = {ids['rel_err']:.2e}（ok={ids['ok']}）", flush=True)
        if not ok:
            print(f"[assert] N={n} 自检失败——机器移植有 bug，拒绝出界", flush=True)
            dump(results, out_path)
            sys.exit(1)

    if args.only == "selftest":
        selftests_for(7, -0.9, *CFG["CONFIGS"]["small"])
        selftests_for(9, -0.9, *CFG["CONFIGS"]["midlarge"])

    # ---- 校准：N=7, a=−0.9（N=7 论文 Case 1 同结构），期望 e ≈ E(P)+3.2259e−4
    if args.only in (None, "calib"):
        selftests_for(7, -0.9, *CFG["CONFIGS"]["small"])
        M, K = CFG["CONFIGS"][CFG["CALIB"]["config"]]
        n, a = CFG["CALIB"]["N"], CFG["CALIB"]["a"]
        print(f"[calib] N={n} a={a} M={M} K={K}（期望 ≈ {CFG['CALIB']['expect']}）", flush=True)
        e_val, info, chk, _, _ = solve_case(n, a, M, K, verbose=args.verbose)
        print(f"[calib] e = {e_val:.9f}（{info['solver']} {info['status']}，"
              f"{info['build_s']}s 构建 + {info['solve_s']}s 求解）", flush=True)
        if chk:
            print(f"[calib] 复核：resid_slack={chk['identity_residual_slack']:.2e} "
                  f"resid_minor={chk['identity_residual_minorant']:.2e} "
                  f"slack_min={min(chk['slack_min_random'], chk['slack_min_boundary']):.2e} "
                  f"minor_viol={chk['minorant_max_violation']:.2e} "
                  f"accepted={chk['accepted']}", flush=True)
        diff = abs(e_val - CFG["CALIB"]["expect"])
        cal_ok = bool(chk and chk["accepted"] and diff <= CFG["CALIB_TOL"])
        results["calibration"] = dict(N=n, a=a, M=M, K=K, e=e_val,
                                      expect=CFG["CALIB"]["expect"], absdiff=diff,
                                      tol=CFG["CALIB_TOL"], ok=cal_ok,
                                      info=info, check=chk)
        print(f"[calib] {'OK' if cal_ok else 'MISMATCH'}：|e − 期望| = {diff:.2e}", flush=True)

    def run_m(a, tag, default_cfgs):
        cfgs = [args.config] if args.config else default_cfgs
        for cname in cfgs:
            M, K = CFG["CONFIGS"][cname]
            selftests_for(9, a, M, K)
            print(f"[{tag}] N=9 a={a} config={cname} (M={M},K={K})", flush=True)
            e_val, info, chk, maps, V = solve_case(9, a, M, K, verbose=args.verbose)
            print(f"[{tag}] e = {e_val!r}（{info['solver']} {info['status']}）", flush=True)
            ttp = None
            if chk:
                print(f"[{tag}] 复核：resid_slack={chk['identity_residual_slack']:.2e} "
                      f"resid_minor={chk['identity_residual_minorant']:.2e} "
                      f"slack_min={min(chk['slack_min_random'], chk['slack_min_boundary']):.2e} "
                      f"minor_viol={chk['minorant_max_violation']:.2e} "
                      f"accepted={chk['accepted']}", flush=True)
                print(f"[{tag}] 折减：Δ={chk['deflation']:.3e}"
                      f"（violH={chk['viol_fine']:.1e}, L1={chk['identity_l1_slack']:.1e}, "
                      f"psdSOS={chk['psd_deficit_sos']:.1e}, psdF={chk['psd_deficit_F']:.1e}）"
                      f"→ e_safe={chk['e_safe']:.9f}", flush=True)
                if chk["e_safe"] > 0:
                    ttp = ttp_check(V["h"].value, chk["e_safe"], E_star)
                    print(f"[{tag}] TTP 复核：{json.dumps(ttp, ensure_ascii=False)}", flush=True)
            entry = dict(m=a, config=cname, M=M, K=K, e=e_val, info=info, check=chk,
                         ttp=ttp,
                         run={"timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
                              "argv": sys.argv[1:],
                              "solver_opts": dict(CFG["SOLVER"]),
                              "repro": ("numerics/.venv/bin/python numerics/bounds/"
                                        f"sdp_bound.py --only {tag} --config {cname}")})
            results["cases"] = [c for c in results["cases"]
                                if not (c["m"] == a and c["config"] == cname)] + [entry]

    if args.only in (None, "m090"):
        run_m(CFG["PRIMARY_M"], "m090", ["midlarge", "small"])
    if args.only in (None, "m095"):
        run_m(-0.95, "m095", ["midlarge", "small"])

    if args.only in ("calib",):
        # 校准模式：若已有 m=−0.9 案例仍输出主界，保证 JSON 完整
        if not any(c["m"] == CFG["PRIMARY_M"] and (c.get("check") or {}).get("e_safe", 0) > 0
                   for c in results["cases"]):
            dump(results, out_path)
            print("[done] --only calib 完成（无 N=9 案例，不出主界）", flush=True)
            return

    # ---- 主界（m=−0.9 里 e_safe > 0 的最大者）与合法性断言
    primary = None
    for c in results["cases"]:
        if c["m"] == CFG["PRIMARY_M"] and c.get("check") and c["check"].get("e_safe", 0) > 0:
            if primary is None or c["check"]["e_safe"] > primary["check"]["e_safe"]:
                primary = c
    if primary is None:
        print("[assert] 没有 m=−0.9 的可用（e_safe > 0）的解——拒绝出界", flush=True)
        dump(results, out_path)
        sys.exit(1)
    bound = primary["check"]["e_safe"]
    if primary.get("ttp"):
        results["ttp_check_primary"] = primary["ttp"]
    results["bound"] = bound
    results["bound_raw_sdp_value"] = primary["e"]
    results["bound_deflation"] = primary["check"]["deflation"]
    results["bound_m"] = primary["m"]
    results["bound_config"] = primary["config"]
    results["gap_to_E_star"] = E_star - bound
    gap = E_star - bound
    print(f"[result] 三点 SDP 下界（m={primary['m']}, config={primary['config']}）"
          f" = {bound:.9f}", flush=True)
    print(f"[result] E* = {E_star:.9f}（{src}）", flush=True)
    print(f"[result] 差距 E* − bound = {gap:.9f}", flush=True)
    if not (0 < bound <= E_star + 1e-6):
        print(f"[assert] 违反 0 < bound ≤ E* + 1e-6：bound={bound!r}, E*={E_star!r}",
              flush=True)
        dump(results, out_path)
        sys.exit(1)
    dump(results, out_path)
    sys.exit(exit_code)


def dump(results, out_path):
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(results, f, ensure_ascii=False, indent=2)
    print(f"[out] 已写入 {out_path}", flush=True)


if __name__ == "__main__":
    main()
