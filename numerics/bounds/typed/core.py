#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""typed 三点构造（Bachoc–Vallentin 分型，S² 适配）——核心装配与自检。

数学（references/thomson-n7-lean/paper/PAPER.md §4–6 的直接推广）：

  类型结构：[n] 按索引块分成 T 个类型（type(v) = v 所在块）。分型基沿用 S² 的
  调和分解：以 Q_k（PAPER.md §4 的核，= 复坐标下 Re(ζ^k \\bar ζ^k)，即调和空间
  H_k 在根的正交补平面上的再现核）与协变块 Y_k[a,b] = u^a v^b Q_k
  （a,b < m_k = M−k）为基——与 untyped（bounds/sdp_bound.py）共用 build_Q/Poly3，
  保证引理 4.1 的正性机制逐位同源。

  typed 三点对称化（PAPER.md §6.2 的因子 2 结构，替代 untyped 的六置换 Sym）：
  无序三点 {i,j,l}（锚定 (i;j,l)，u=t_ij, v=t_il, t=t_jl）上
      D_T = 2·[ s_X(u,v,t) + s_Y(u,t,v) + s_Z(v,t,u) ]，
  其中 s_X = Σ_k⟨F^{(X,k)}, Y_k⟩ 为**未对称化**的核形式（每类型一套 PSD 块，
  X=type(i) 等）。六个有序三点 = 3 根 × 2 换位；换位只把 Y_k 变为转置（与对称
  F 配对不变），故 Σ_{有序相异} s_{type(root)} = Σ_T D_T。

  记 gm_X(τ) = s_X(1,τ,τ)+s_X(τ,1,τ)+s_X(τ,τ,1)（重复索引三点的三项），
  Ψ_{(X,Y)} = H_{(X,Y)} − gm_X − gm_Y（逐对类一元多项式，d_H 次）。

  份额（shares，PAPER.md §6.2 表的推广）：对类 (X,Y) 的对 {i,j}，第三点 l 按
  type(l) 分类（X<Y：inX=l∈X\\{i} / inY=l∈Y\\{j} / out=l∉X∪Y；X=Y：
  inX=l∈X\\{i,j} / out=l∉X），每个非空类别一个一元 ψ（d_H 次），最后一个
  非空类别取残差 residual = (Ψ − Σ_{其他} count·ψ)/count_resid，
  使每对的份额在全部 n−2 个第三点上求和恰为 Ψ。

  逐三点 slack（每个类型多重集 {X,Y,Z} 一条，锚定最小类型为根）：
      λ_{XYZ} = Sh_{(X,Y)|cat(Z)}(u) + Sh_{(X,Z)|cat(Y)}(v) + Sh_{(Y,Z)|cat(X)}(t)
                − c_{XYZ} − 2[s_X(u,v,t) + s_Y(u,t,v) + s_Z(v,t,u)]，
  常数 c 满足归一化（PAPER.md (6) 的推广）
      Σ_m count(m)·c_m = e + Σ_X n_X·s_X(1,1,1)，  s_X(1,1,1)=ΣF^{(X,0)} 全元素和
  （k≥1 时 Q_k(1,1,1)=0，PAPER.md §4 Boundary values）。

  核心恒等式（identity_selftest 逐点机器验证）：
      Σ_T λ_T + Σ_all = Σ_{i<j} H_{cls(i,j)}(t_ij) − e，
  其中 Σ_all = Σ_{i,j,l} s_{type(i)}(t_ij,t_il,t_jl) ≥ 0（引理 4.1 逐根逐类型）。
  于是 λ_T ≥ 0 于出现的三点域 + H_cls ≤ φ 于各类区间 ⟹ E ≥ ΣH ≥ e。

  域（PAPER.md §6.4）：
    mode="cut"  单切口：一切类区间 [a,1)，slack 域 {u,v,t∈[a,1]}∩Gram；
                对任意类型划分有效（纯组合推导，无需极小对标定）。
    mode="band" 带状：要求 sizes[0]==2（类型 0 = 重标后的极小对 {0,1}）；
                类 (0,0) 的 H 与含 {0,1} 的三点 slack 带 [lo,hi]（u 槽），
                其余类/slack 只用下切口 lo。cap = lo=−1 的带。

全部线性对象装配为对变量向量 x = [e; h_all; ψ_all; c_all; vec(F_all)] 的稀疏
矩阵（λ_m = slack_maps[m] @ x 等），SDP 侧（solve.py）只做 cvxpy 布线。
"""
from __future__ import annotations

import math
import sys
from itertools import combinations
from pathlib import Path

import numpy as np
import scipy.sparse as sp

HERE = Path(__file__).resolve().parent
BOUNDS_DIR = HERE.parent
if str(BOUNDS_DIR) not in sys.path:
    sys.path.insert(0, str(BOUNDS_DIR))

import sdp_bound as UB  # noqa: E402  （untyped 基座：Poly3/build_Q/…，同一 Q_k 机制）


# ============================================================ 类型结构
class TypeStructure:
    """[n] 的索引块分型：sizes=[n_1,…,n_T]，type(v)=v 所在块号（0 起）。"""

    def __init__(self, sizes):
        self.sizes = [int(s) for s in sizes]
        if any(s <= 0 for s in self.sizes):
            raise ValueError(f"类型尺寸必须为正: {self.sizes}")
        self.n = sum(self.sizes)
        self.T = len(self.sizes)
        self.start = np.concatenate([[0], np.cumsum(self.sizes)]).astype(int)

    def type_of(self, v):
        return int(np.searchsorted(self.start, v, side="right") - 1)

    def types_of_config(self):
        return [self.type_of(v) for v in range(self.n)]

    # ---- 对类 ----
    def pair_classes(self):
        return [(X, Y) for X in range(self.T) for Y in range(X, self.T)]

    def pair_count(self, X, Y):
        nx, ny = self.sizes[X], self.sizes[Y]
        return nx * (nx - 1) // 2 if X == Y else nx * ny

    def pair_categories(self, X, Y):
        """[(类别键, 第三点数)]；最后一个类别固定是 l∉…（外类）。"""
        nx, ny = self.sizes[X], self.sizes[Y]
        if X < Y:
            return [("inX", nx - 1), ("inY", ny - 1), ("out", self.n - nx - ny)]
        return [("inX", nx - 2), ("out", self.n - nx)]

    def cat_of(self, X, Y, Z):
        """类型 Z 的第三点在对类 (X,Y)（X≤Y）下的类别键。"""
        if X < Y:
            if Z == X:
                return "inX"
            if Z == Y:
                return "inY"
            return "out"
        return "inX" if Z == X else "out"

    # ---- 三点类（类型多重集，X≤Y≤Z，重复数不超过类容量）----
    def triple_multisets(self):
        out = []
        for X in range(self.T):
            for Y in range(X, self.T):
                for Z in range(Y, self.T):
                    need = {}
                    for t in (X, Y, Z):
                        need[t] = need.get(t, 0) + 1
                    if all(self.sizes[t] >= c for t, c in need.items()):
                        out.append((X, Y, Z))
        return out

    def triple_count(self, X, Y, Z):
        s = self.sizes
        if X == Y == Z:
            return s[X] * (s[X] - 1) * (s[X] - 2) // 6
        if X == Y:
            return s[X] * (s[X] - 1) // 2 * s[Z]
        if Y == Z:
            return s[X] * s[Y] * (s[Y] - 1) // 2
        return s[X] * s[Y] * s[Z]

    def __repr__(self):
        return f"TypeStructure({'+'.join(map(str, self.sizes))}, n={self.n})"


def check_band_structure(ts: TypeStructure):
    """带状模式要求类型 0 恰为重标后的极小对 {0,1}（尺寸 2）。"""
    if ts.sizes[0] != 2:
        raise ValueError(
            f"band 模式要求类型 0 恰为极小对 {{0,1}}（尺寸 2），得到 sizes[0]={ts.sizes[0]}")


# ============================================================ 一元工具
def uni_embed(ring, coeffs, slot):
    """一元系数向量（度 ≤ ring.D）→ Poly3 向量（放在 slot 号变量上）。"""
    out = ring.zero()
    for j, c in enumerate(coeffs):
        if c != 0.0:
            e = [0, 0, 0]
            e[slot] = j
            out[ring.index[tuple(e)]] += c
    return out


def poly3_to_uni(ring, col, pattern):
    """Poly3 向量在一元代入下的像：'vtt'→(1,τ,τ)，'tut'→(τ,1,τ)，'ttu'→(τ,τ,1)。"""
    out = np.zeros(ring.D + 1)
    for p in np.nonzero(col)[0]:
        i, j, l = ring.mons[p]
        if pattern == "vtt":            # u=1, v=τ, t=τ
            d = j + l
        elif pattern == "tut":          # u=τ, v=1, t=τ
            d = i + l
        elif pattern == "ttu":          # u=τ, v=τ, t=1
            d = i + j
        else:
            raise ValueError(pattern)
        if d > ring.D:
            raise OverflowError(f"一元化次数 {d} > D={ring.D}")
        out[d] += col[p]
    return out


def embed_block(mat, col0, ncols):
    """把 mat（r×m）嵌到 r×ncols 的第 col0 列起。"""
    left = sp.csr_matrix((mat.shape[0], col0))
    right = sp.csr_matrix((mat.shape[0], ncols - col0 - mat.shape[1]))
    return sp.hstack([left, sp.csr_matrix(mat), right], format="csr")


# ============================================================ typed 装配
def assemble_typed(ts: TypeStructure, mode, lo, hi, M, K):
    """装配全部线性地图（详见模块 docstring）。"""
    if mode == "cut":
        if hi is not None and hi < 1.0:
            raise ValueError("cut 模式无上沿（hi 应为 None 或 1）")
        hi = 1.0
        band_cls = None
    elif mode == "band":
        check_band_structure(ts)
        if not (lo < hi <= 1.0):
            raise ValueError(f"band 模式需 lo < hi ≤ 1，得到 [{lo},{hi}]")
        band_cls = (0, 0)
    else:
        raise ValueError(mode)

    D = 2 * M - 2
    d_H = D
    ring = UB.Poly3(D)
    Qs = UB.build_Q(ring, K)
    mks = [M - k for k in range(K)]

    classes = ts.pair_classes()
    cats_of = {cls: ts.pair_categories(*cls) for cls in classes}
    psi_list = []                                  # [(cls, cat)]（非残差自由份额）
    for cls in classes:
        nz = [c for c in cats_of[cls] if c[1] > 0]
        for cat, _cnt in nz[:-1]:
            psi_list.append((cls, cat))
    triples = ts.triple_multisets()
    if not triples:
        raise ValueError(
            f"typed 构造在 n={ts.n} 退化：无三点类（份额/slack 机制空转）——"
            "N=2 属理论退化行，见 typed_selftest.py 的处理")

    # ---- 变量布局 x = [e; h（逐类 d_H+1）; ψ（逐自由份额 d_H+1）; c（逐三点类）; vec(F^X)]
    F_slices, NF = {}, {}
    for X in range(ts.T):
        cols = []
        for k in range(K):
            for a in range(mks[k]):
                for b in range(mks[k]):
                    cols.append((k, a, b))
        F_slices[X] = cols
        NF[X] = len(cols)
    n_e = 1
    n_h = len(classes) * (d_H + 1)
    n_psi = len(psi_list) * (d_H + 1)
    n_c = len(triples)
    n_F = sum(NF.values())
    nx = n_e + n_h + n_psi + n_c + n_F
    o_e = 0
    o_h = n_e
    o_psi = o_h + n_h
    o_c = o_psi + n_psi
    o_F = o_c + n_c

    H_index = {cls: o_h + i_cls * (d_H + 1) for i_cls, cls in enumerate(classes)}
    psi_index = {(cls, cat): o_psi + j * (d_H + 1) for j, (cls, cat) in enumerate(psi_list)}
    c_index = {m: o_c + j for j, m in enumerate(triples)}
    F_index = {X: o_F + sum(NF[Y] for Y in range(X)) for X in range(ts.T)}

    def uni_on_x(col0):
        rows = list(range(d_H + 1))
        cols = list(range(col0, col0 + d_H + 1))
        vals = [1.0] * (d_H + 1)
        return sp.csr_matrix((vals, (rows, cols)), shape=(d_H + 1, nx))

    # ---- 每类型核形式（未对称化）与其置换、gm

    # ---- 每类型核形式（未对称化）与其置换、gm
    raw_cols = {}
    for X in range(ts.T):
        raw_cols[X] = [ring.mul(ring.mono((a, b, 0), 1.0), Qs[k])
                       for (k, a, b) in F_slices[X]]
    P_3, P_5 = ring.perm_maps[3], ring.perm_maps[5]   # (u,t,v) 与 (v,t,u)

    def cols_to_matrix(cols, perm=None):
        rows_x, cols_x, vals = [], [], []
        for j, c in enumerate(cols):
            cc = c if perm is None else c[perm]
            nz = np.nonzero(cc)[0]
            rows_x.extend(nz.tolist())
            cols_x.extend([j] * len(nz))
            vals.extend(cc[nz].tolist())
        return sp.csr_matrix((vals, (rows_x, cols_x)), shape=(ring.nmon, len(cols)))

    sX_cols = {X: cols_to_matrix(raw_cols[X]) for X in range(ts.T)}
    sX_perm = {X: (cols_to_matrix(raw_cols[X], P_3), cols_to_matrix(raw_cols[X], P_5))
               for X in range(ts.T)}
    gm_maps = {}
    for X in range(ts.T):
        rows_x, cols_x, vals = [], [], []
        for j, c in enumerate(raw_cols[X]):
            uni = (poly3_to_uni(ring, c, "vtt") + poly3_to_uni(ring, c, "tut")
                   + poly3_to_uni(ring, c, "ttu"))
            nz = np.nonzero(uni)[0]
            rows_x.extend(nz.tolist())
            cols_x.extend([j] * len(nz))
            vals.extend(uni[nz].tolist())
        gm_maps[X] = sp.csr_matrix((vals, (rows_x, cols_x)), shape=(d_H + 1, NF[X]))

    # ---- 份额 Sh_{cls|cat}（(d_H+1) × nx，含 F 侧的 gm）
    def share_map(cls, cat):
        X, Y = cls
        nz = [c for c in cats_of[cls] if c[1] > 0]
        resid_cat, resid_cnt = nz[-1]
        hM = uni_on_x(H_index[cls])
        gmM = embed_block(gm_maps[X], F_index[X], nx) + embed_block(gm_maps[Y], F_index[Y], nx)
        Psi = hM - gmM                              # Ψ = h_cls − gm_X − gm_Y
        if cat == resid_cat:
            sub = sp.csr_matrix((d_H + 1, nx))
            for c, cnt in nz[:-1]:
                sub = sub + cnt * uni_on_x(psi_index[(cls, c)])
            return ((Psi - sub) * (1.0 / resid_cnt)).tocsr()
        return uni_on_x(psi_index[(cls, cat)])

    def lift_uni_to_slot(mat_u, slot):
        """(d_H+1)×nx 一元地图 → nmon×nx：τ^j 放到 slot 变量上。"""
        coo = mat_u.tocoo()
        rows_x, cols_x, vals = [], [], []
        for r_, c_, v_ in zip(coo.row, coo.col, coo.data):
            e = [0, 0, 0]
            e[slot] = int(r_)
            rows_x.append(ring.index[tuple(e)])
            cols_x.append(int(c_))
            vals.append(float(v_))
        return sp.csr_matrix((vals, (rows_x, cols_x)), shape=(ring.nmon, nx))

    # ---- 三点 slack 地图 λ_m = A_m @ x
    slack_maps, slack_domains = {}, {}
    for (X, Y, Z) in triples:
        A = sp.csr_matrix((ring.nmon, nx))
        A = A + lift_uni_to_slot(share_map((X, Y), ts.cat_of(X, Y, Z)), 0)
        A = A + lift_uni_to_slot(share_map((X, Z), ts.cat_of(X, Z, Y)), 1)
        A = A + lift_uni_to_slot(share_map((Y, Z), ts.cat_of(Y, Z, X)), 2)
        A = A + sp.csr_matrix(([-1.0], ([ring.index[(0, 0, 0)]], [c_index[(X, Y, Z)]])),
                              shape=(ring.nmon, nx))
        for XX, mat in ((X, sX_cols[X]), (Y, sX_perm[Y][0]), (Z, sX_perm[Z][1])):
            A = A - 2.0 * embed_block(mat, F_index[XX], nx)
        slack_maps[(X, Y, Z)] = A.tocsr()
        is_band = (mode == "band" and X == Y == 0)
        slack_domains[(X, Y, Z)] = dict(
            band=is_band, lo=lo, hi=hi if is_band else 1.0,
            anchor=(X, Y, Z),
            note=("含极小对 {0,1}：u 槽带 [%g,%g]，v,t ≥ %g" % (lo, hi, lo)) if is_band
            else ("全部槽 ≥ %g" % lo))

    # ---- 归一化行：Σ_m count·c − e − Σ_X n_X·ΣF^{(X,0)} = 0
    rows_x, cols_x, vals = [], [], []
    for m in triples:
        cols_x.append(c_index[m])
        vals.append(float(ts.triple_count(*m)))
    cols_x.append(o_e)
    vals.append(-1.0)
    for X in range(ts.T):
        for idx, (k, a, b) in enumerate(F_slices[X]):
            if k == 0:
                cols_x.append(F_index[X] + idx)
                vals.append(-float(ts.sizes[X]))
    nrm_row = sp.csr_matrix((vals, ([0] * len(cols_x), cols_x)), shape=(1, nx))

    # ---- minorant：每类 H ≤ φ 于该类区间
    minorants = {}
    for cls in classes:
        dom = (lo, hi) if (mode == "band" and cls == band_cls) else (lo, 1.0)
        minorants[cls] = build_minorant_maps(d_H, dom, H_index[cls], nx)

    # ---- s_X(1,1,1) 行（复核用）
    s111_rows = {}
    for X in range(ts.T):
        cols_x, vals = [], []
        for idx, (k, a, b) in enumerate(F_slices[X]):
            if k == 0:
                cols_x.append(F_index[X] + idx)
                vals.append(1.0)
        s111_rows[X] = sp.csr_matrix((vals, ([0] * len(cols_x), cols_x)), shape=(1, nx))

    return dict(
        ts=ts, mode=mode, lo=lo, hi=hi, band_cls=band_cls,
        ring=ring, Qs=Qs, D=D, d_H=d_H, M=M, K=K, F_sizes=mks,
        classes=classes, cats_of=cats_of, psi_list=psi_list, triples=triples,
        x_layout=dict(nx=nx, o_e=o_e, o_h=o_h, o_psi=o_psi, o_c=o_c, o_F=o_F,
                      n_h=n_h, n_psi=n_psi, n_c=n_c, n_F=n_F,
                      H_index=H_index, psi_index=psi_index, c_index=c_index,
                      F_index=F_index, F_slices=F_slices, NF=NF),
        sX_cols=sX_cols, sX_perm=sX_perm, gm_maps=gm_maps,
        slack_maps=slack_maps, slack_domains=slack_domains, nrm_row=nrm_row,
        s111_rows=s111_rows, minorants=minorants,
    )


def build_minorant_maps(d_H, dom, h_col0, nx):
    """一维 minorant 线性地图：p(y) = 1 − 2y·H(1−2y²) 于区间 dom=(lo,hi)。

    一侧 [lo,1)：y∈[0,b]，b²=(1−lo)/2，Lukács 族（与 untyped sdp_bound 一致）
        p = σ0 + yσ1 + (b²−y²)σ2 + y(b²−y²)σ3。
    两侧 [lo,hi]：y∈[α,β]，α=√((1−hi)/2)，β=√((1−lo)/2)，Markov–Lukács 族
        p = σ0 + (y−α)σ1 + (β−y)σ2 + (y−α)(β−y)σ3
    （含奇次 Lukács 精确表示 σ0=σ3=0；σ ⪰ 0 ⟹ 各项区间非负 ⟹ p ≥ 0）。
    """
    lo, hi = dom
    deg_p = 2 * d_H + 1
    Csub = np.zeros((deg_p + 1, d_H + 1))          # H(1−2y²)：y^{2m} ← Σ_i h_i C(i,m)(−2)^m
    for i in range(d_H + 1):
        for m_ in range(i + 1):
            Csub[2 * m_, i] += math.comb(i, m_) * ((-2.0) ** m_)
    Cp = np.zeros((deg_p + 1, d_H + 1))            # p = 1 − 2y·H(1−2y²)：奇次行 −2·Csub
    for r in range(1, deg_p + 1, 2):
        Cp[r, :] = -2.0 * Csub[r - 1, :]
    p_const = np.zeros(deg_p + 1)
    p_const[0] = 1.0
    Cpx = np.zeros((deg_p + 1, nx))
    Cpx[:, h_col0:h_col0 + d_H + 1] = Cp

    if hi >= 1.0:
        b2 = (1.0 - lo) / 2.0
        blocks = [("sig0", [(0, 1.0)], d_H),
                  ("sig1", [(1, 1.0)], d_H),
                  ("sig2", [(0, b2), (2, -1.0)], d_H - 1),
                  ("sig3", [(1, b2), (3, -1.0)], d_H - 1)]
        interval = (0.0, math.sqrt(b2))
    else:
        alpha = math.sqrt(max(0.0, (1.0 - hi) / 2.0))
        beta = math.sqrt(max(0.0, (1.0 - lo) / 2.0))
        blocks = [("sig0", [(0, 1.0)], d_H),
                  ("sig1", [(0, -alpha), (1, 1.0)], d_H),
                  ("sig2", [(0, beta), (1, -1.0)], d_H),
                  ("sig3", [(0, -alpha * beta), (1, alpha + beta), (2, -1.0)], d_H - 1)]
        interval = (alpha, beta)
    return dict(deg_p=deg_p, Cp=Cpx, p_const=p_const, blocks=blocks, interval=interval,
                domain=(lo, hi))


def y_map(mons_y, mult, deg_p):
    """σ 块（行主序 vec）→ p(y) 系数的地图。"""
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


# ============================================================ 自检
def random_config(rng, n):
    X = rng.normal(size=(n, 3))
    return X / np.linalg.norm(X, axis=1, keepdims=True)


def gram_triples(X):
    G = X @ X.T
    n = len(X)
    idx = [(i, j, l) for i in range(n) for j in range(n) for l in range(n)]
    uvl = np.array([[G[i, j], G[i, l], G[j, l]] for (i, j, l) in idx])
    return idx, uvl


def kernel_selftest(maps, rng, n_points=300):
    """(a) Q_k(u,v,t) = Re(ζ_y^k \\bar ζ_z^k)（随机 Gram 三点）；
    (b) 分型正性（引理 4.1 逐类型）：Σ_{i,j,l}⟨F^{type(i),k}, Y_k(t_ij,t_il,t_jl)⟩ ≥ 0，
        随机 PSD F 逐类型验证（向量化实现：⟨F, Y_k⟩ 三点批 = ((U*Q)F Vᵀ) 的对角）。"""
    ring, K, Qs = maps["ring"], maps["K"], maps["Qs"]
    x = rng.normal(size=(n_points, 3)); x /= np.linalg.norm(x, axis=1, keepdims=True)
    y = rng.normal(size=(n_points, 3)); y /= np.linalg.norm(y, axis=1, keepdims=True)
    z = rng.normal(size=(n_points, 3)); z /= np.linalg.norm(z, axis=1, keepdims=True)
    u = np.sum(x * y, axis=1); v = np.sum(x * z, axis=1); t = np.sum(y * z, axis=1)

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
            worst = max(worst, abs(lhs - ((zy * np.conj(zz)) ** k).real))

    # (b) 分型正性（向量化）
    ts = maps["ts"]
    lay = maps["x_layout"]
    Xc = random_config(rng, ts.n)
    idx, uvl = gram_triples(Xc)
    types = np.array(ts.types_of_config())
    root_types = types[np.array([i for (i, j, l) in idx])]
    total = 0.0
    for X in range(ts.T):
        sel = np.nonzero(root_types == X)[0]
        if len(sel) == 0:
            continue
        uX, vX, tX = uvl[sel, 0], uvl[sel, 1], uvl[sel, 2]
        for k in range(K):
            mk = maps["F_sizes"][k]
            G = rng.normal(size=(mk, mk))
            F = G @ G.T
            Qk = ring.eval_batch(Qs[k], uX, vX, tX)
            U = np.stack([uX ** a for a in range(mk)], axis=1)      # (Npt, mk)
            V = np.stack([vX ** b for b in range(mk)], axis=1)
            pairings = ((U * Qk[:, None]) @ F @ V.T).diagonal()     # ⟨F, Y_k⟩ 批
            total += float(pairings.sum())
    scale = max(1.0, abs(total))
    return dict(Q_identity_max_err=float(worst),
                positivity_sum=float(total),
                positivity_ok=bool(total >= -1e-8 * scale))


def identity_selftest(maps, rng, n_trials=3):
    """typed 恒等式：Σ_T λ_T + Σ_all = Σ_{i<j}H_{cls(i,j)}(t_ij) − e（随机数据）。

    随机 h_cls、随机 PSD F^X、随机 ψ、按归一化解残差 c、随机 e，在随机构型上
    数值验证两边逐位相等。覆盖：份额求和=Ψ、Ψ/gm 定义、核项根和×2=D、归一化
    计数、s(1,1,1)、slack 装配的全部通路。
    """
    ring, ts = maps["ring"], maps["ts"]
    lay = maps["x_layout"]
    d_H = maps["d_H"]
    results = []
    for _ in range(n_trials):
        x = rng.normal(size=lay["nx"])            # h/ψ 段保留随机值
        x[lay["o_e"]] = rng.normal() * 3.0
        # F：每类型每 k 随机 PSD（F_slices 行主序）——必须在解残差 c 之前放好，
        # 因为归一化行含 Σ n_X·ΣF^{(X,0)} 项
        for X in range(ts.T):
            for k in range(maps["K"]):
                mk = maps["F_sizes"][k]
                G = rng.normal(size=(mk, mk))
                Fp = G @ G.T
                base = lay["F_index"][X] + sum(m_ * m_ for m_ in maps["F_sizes"][:k])
                x[base:base + mk * mk] = Fp.reshape(-1, order="C")
        # c：非残差随机，残差由归一化 nrm_row@x=0 解出（残差 = 枚举最后一个三点类）
        x[lay["o_c"]:lay["o_c"] + lay["n_c"]] = 0.0
        c_nonres = rng.normal(size=lay["n_c"] - 1)
        x[lay["o_c"]:lay["o_c"] + lay["n_c"] - 1] = c_nonres
        row = np.asarray(maps["nrm_row"].todense()).ravel()
        resid_col = lay["o_c"] + lay["n_c"] - 1
        c_res = -(row @ x) / row[resid_col]
        x[resid_col] = c_res
        assert abs(row @ x) <= 1e-9 * max(1.0, abs(c_res)), "归一化残差求解失败"

        Xc = random_config(rng, ts.n)
        G = Xc @ Xc.T
        n = ts.n
        idx, uvl = gram_triples(Xc)
        types = ts.types_of_config()
        # Σ_all = Σ_{i,j,l} s_{type(i)}（向量化：逐类型算多项式再批量求值）
        sum_all = 0.0
        for X in range(ts.T):
            sX = maps["sX_cols"][X] @ x[lay["F_index"][X]:lay["F_index"][X] + lay["NF"][X]]
            sel = [ii for ii, (i, j, l) in enumerate(idx) if types[i] == X]
            sel = np.array(sel, dtype=int)
            sum_all += float(ring.eval_batch(sX, uvl[sel, 0], uvl[sel, 1],
                                             uvl[sel, 2]).sum())
        # Σ_T λ_T：无序相异三点，按类型多重集锚定（最小类型为根）
        sum_lam = 0.0
        for (i, j, l) in combinations(range(n), 3):
            tt = [(types[i], i), (types[j], j), (types[l], l)]
            tt.sort(key=lambda p: p[0])
            (r0, i0), (r1, j0), (r2, l0) = tt
            key = (r0, r1, r2)
            col = maps["slack_maps"][key] @ x
            sum_lam += float(ring.eval_batch(col, np.array([G[i0, j0]]),
                                             np.array([G[i0, l0]]),
                                             np.array([G[j0, l0]]))[0])
        # Σ_{i<j} H_cls − e
        e_val = x[lay["o_e"]]
        sum_H = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                cls = tuple(sorted((types[i], types[j])))
                hc = x[lay["H_index"][cls]:lay["H_index"][cls] + d_H + 1]
                sum_H += float(np.polyval(hc[::-1], G[i, j]))
        lhs = sum_lam + sum_all
        rhs = sum_H - e_val
        results.append(dict(lhs=float(lhs), rhs=float(rhs),
                            abs_err=float(abs(lhs - rhs)),
                            rel_err=float(abs(lhs - rhs) / max(1.0, abs(rhs)))))
    worst = max(results, key=lambda r: r["abs_err"])
    return dict(trials=results, worst_abs_err=worst["abs_err"],
                worst_rel=worst["rel_err"],
                ok=bool(worst["abs_err"] <= 1e-8 * max(1.0, abs(worst["rhs"]))))
