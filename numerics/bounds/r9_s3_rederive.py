#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r9_s3_rederive.py — R9A s3-quotient-rederive：S₃ 商 cut 装配的自写第二实现重推。

【任务定位（D33 裁决 5① 收账；D34 裁决 2）】cap M9 证书
certificates/n9-stage-a4-typedcap-m0748_M9.json 的 certified
=（e−defl)/(1+R2max) 已有构造端认证链（typed_ladder --verify-cert +
l2_rigorize 重建）。本文件给出**独立第二实现**：从数学定义出发重推
S₃ 商环装配全链，全部算术 Python Fraction（严格数值层），对证书
provenance.residuals 与 results/l2_rigorous.json 存档**逐位（精确
Fraction）**比对。独立性口径＝「零 import 复用」：本文件只用 stdlib
（json/fractions/math/random/subprocess 等），禁止 import
typed_ladder / QuotientMaps / thomson_certs / sdp_bound / sdp_certify /
l2_rigorize（仓码只读理解定义，代码路径全部自写——沿复算员 R8 自写
LDLᵀ 先例；多项式内部表示取稀疏 dict 而非原实现的稠密 list；枚举
次序取证书 B/sig Gram 块的隐式基约定——数据格式对齐，值级结果与
枚举次序无关）。

【数学内容（全部自定义重实现）】
  (i)   FRing：变量 (u,v,t) 的分次单项式环（总次数 ≤ D=2M−2=16，
        nmon=C(19,3)=969）；乘法／三元求值／槽置换（subst_vars）。
  (ii)  Q_k 递推（K=6）：Q₀=1、Q₁=t−uv、
        Q_j=2(t−uv)Q_{j−1}−(1−u²)(1−v²)Q_{j−2}
        （定义出处 typed_ladder.py:245-253 / sdp_bound.build_Q——本文
        独立重实现并以 (u,v) 系数对称＋deg_t=k 自查）。
  (iii) Y_cols：k=0..K−1 × (M−k)² 列 u^a v^b Q_k（M=9 共 271 列）；
        gm_cols＝三对槽坍缩 subst_keep 的和；
        K_cols=−2(Y+Y^{(u,t,v)}+Y^{(v,t,u)})。
  (iv)  share_lp：AA_in=ψ_AA、AB_in=ψ_AB、AA_out=(h_AA−ψ_AA)/6、
        AB_out=(h_AB−4ψ_AB)/3；GM_OF{−1/3,−2/3}；lam(orbit) 全装配
        （三槽一元份额 − c + Σ_k⟨F^k, Y_k⟩ 的 K/gm 列展开）。
  (v)   sos_sum：8 块 sos_def（1；3×(slot−lo)；3×(1−slot)；detG
        =1+2uvt−u²−v²−t²）× 证书 B Gram 块。
  (vi)  minorant：Cp 矩阵 Csub[2m][i]+=C(i,m)(−2)^m、奇次行 ×−2；
        sig_def 4 块；ŵ=⌈√b²⌉、b²=(1−lo)/2；deg_p=2d_H+1=33。
  (vii) R1_orbit=ℓ₁(λ−sos_sum)、R2_cls=Σ_j|rhs_j−lhs_j|ŵ^j、
        defl=3R1_AAA+54R1_AAB+27R1_ABC、R2max=max(R2_AA,R2_AB)、
        certified=(e−defl)/(1+R2max)。
  (viii) 恒等式 Σ_84 λ_cls+Σ_all == ΣH−e_dy（随机有理 9 点构型，
        seed 20261011，≥3 trial，精确 ==0——端到端验证整套装配）＋
        全 10 类 λ_full == λ_orbit∘P 逐系数一致性。

【明确不在范围（如实分层）】PSD/LDLᵀ 38 块判定不在本验证器范围：
复算员 R8 ⑧ 已自写 Fractions LDLᵀ 独立过 38/38＋三负对照（GAP-REPORT
Round 8 节 ⑧），本文件不重复也不冒充。E*=25.759986531 为三源校验
参考值（十进制口径，D28 裁决 3），非已证最优。

【数据输入】唯一推导输入＝证书 json 本身（blocks＋provenance）；
l2_rigorous.json 只作为**比对存档**（验收 ①②④ 的对账目标），不参与
任何推导。

用法（thomson-n9 下）：
  python3 numerics/bounds/r9_s3_rederive.py [--cert PATH] [--out PATH]
      [--trials 3] [--seed 20261011]
默认 cert=certificates/n9-stage-a4-typedcap-m0748_M9.json、
out=results/r9_s3_rederive.json。检查次序 cheap-first（结构性自查→
残差重算比对→certified/ε→轨道一致→随机恒等式最贵殿后），使篡改
副本在早期快速失败。
"""
from __future__ import annotations

import argparse
import json
import math
import random
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from itertools import combinations
from pathlib import Path

F0, F1 = Fraction(0), Fraction(1)
E_STAR_DEC = Fraction("25.759986531")      # 十进制主口径（D28 裁决 3）
SEED_DEFAULT = 20261011                     # ③ 恒等式随机 trial 种子（任务书）
TRIALS_DEFAULT = 3
FORBIDDEN_ROOTS = ("typed_ladder", "QuotientMaps", "thomson_certs",
                   "sdp_bound", "sdp_certify", "l2_rigorize")

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CERT_DEFAULT = REPO / "certificates" / "n9-stage-a4-typedcap-m0748_M9.json"
L2R_PATH = HERE / "results" / "l2_rigorous.json"
OUT_DEFAULT = HERE / "results" / "r9_s3_rederive.json"

N_POINTS = 9
TYPES = (0, 0, 0, 1, 1, 1, 2, 2, 2)         # (3,3,3) 分型


def log(msg: str) -> None:
    print(msg, flush=True)


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


def ceil_sqrt_rat(x: Fraction) -> Fraction:
    """⌈√x⌉ 的精确有理值（x ≥ 0）。"""
    p, q = x.numerator, x.denominator
    s = math.isqrt(p * q)
    return Fraction(s if s * s == p * q else s + 1, q)


# ============================================================ (i) FRing
class FRing:
    """(u,v,t) 单项式环（总次数 ≤ D）。多项式＝稀疏 dict {指数三元组: Fraction}。

    与构造端 FRing（sdp_bound.Poly3 的稠密 list 镜像）为独立第二实现：
    内部表示稀疏 dict、乘法/求值/槽置换全部自写；枚举次序取证书 B/sig
    Gram 块的隐式基约定（见 __init__ 注——纯数据格式对齐，一切值级结果
    与枚举次序无关）。
    """

    def __init__(self, D: int):
        self.D = D
        # 枚举次序＝证书 B/sig Gram 块的隐式基约定（i 外层、j 中层、l 内层，
        # i+j+l ≤ D——证书格式的数据约定，非代码复用）；多项式内部表示仍取
        # 稀疏 dict，与构造端稠密 list 实现独立；一切值级结果（ℓ₁/求值/
        # 逐系数恒等）与枚举次序无关。
        mons = []
        for i in range(D + 1):
            for j in range(D + 1 - i):
                for l in range(D + 1 - i - j):
                    mons.append((i, j, l))
        self.mons = tuple(mons)
        self.index = {e: p for p, e in enumerate(mons)}
        self.nmon = len(mons)

    @staticmethod
    def zero():
        return {}

    @staticmethod
    def mono(e, c=F1):
        return {tuple(e): c}

    @staticmethod
    def add(av, bv):
        if not av:
            return dict(bv)
        if not bv:
            return dict(av)
        out = dict(av)
        for e, c in bv.items():
            s = out.get(e, F0) + c
            if s:
                out[e] = s
            else:
                out.pop(e, None)
        return out

    @staticmethod
    def scale(a, k):
        if k == 0:
            return {}
        return {e: c * k for e, c in a.items()}

    @staticmethod
    def sub_(av, bv):
        return FRing.add(av, FRing.scale(bv, Fraction(-1)))

    def mul(self, av, bv):
        out = {}
        D = self.D
        for (ea, ca) in av.items():
            for (eb, cb) in bv.items():
                e = (ea[0] + eb[0], ea[1] + eb[1], ea[2] + eb[2])
                if e[0] + e[1] + e[2] > D:
                    raise OverflowError(f"degree {sum(e)} exceeds D={D}")
                s = out.get(e, F0) + ca * cb
                if s:
                    out[e] = s
                else:
                    out.pop(e, None)
        return out

    def subst_vars(self, a, slot_of_old):
        """变量替换 p(x0,x1,x2) → q 使 q(new0,new1,new2)=p(x·)。

        slot_of_old[a]＝旧变量 a 落到新变量的槽号。三个用例：
          p(u,t,v)：x0→u(槽0)、x1→t(槽2)、x2→v(槽1) ⇒ [0,2,1]
          p(v,t,u)：x0→v(槽1)、x1→t(槽2)、x2→u(槽0) ⇒ [1,2,0]
          p(t,v,u)（u↔t 换位）：[2,1,0]
        """
        out = {}
        for (e, c) in a.items():
            ne = [0, 0, 0]
            for oldpos in range(3):
                ne[slot_of_old[oldpos]] += e[oldpos]
            key = (ne[0], ne[1], ne[2])
            s = out.get(key, F0) + c
            if s:
                out[key] = s
            else:
                out.pop(key, None)
        return out

    @staticmethod
    def swap_uv_exp(a):
        """系数级 (u,v) 对称化镜像：p(u,v,t) ↦ p(v,u,t)（自查 Q_k 对称用）。"""
        return {(j, i, l): c for ((i, j, l), c) in a.items()}

    def eval3(self, a, u, v, t):
        """三元求值（Fraction 慢路径；trial 批量求值用 IntPoly.eval3）。"""
        pu, pv, pt = [F1], [F1], [F1]
        for _ in range(self.D):
            pu.append(pu[-1] * u)
            pv.append(pv[-1] * v)
            pt.append(pt[-1] * t)
        acc = F0
        for ((i, j, l), c) in a.items():
            acc += c * pu[i] * pv[j] * pt[l]
        return acc

    @staticmethod
    def eval1(coeffs, x):
        acc, xp = F0, F1
        for c in coeffs:
            acc += c * xp
            xp *= x
        return acc

    def uni_at_slot(self, uni, slot):
        """一元系数（index=次数）→ 放到槽变量上的多项式。"""
        out = {}
        for d, c in enumerate(uni):
            if c:
                e = [0, 0, 0]
                e[slot] = d
                out[tuple(e)] = out.get(tuple(e), F0) + c
        return out

    def lift_slot0(self, vec, slot):
        """支撑在槽0 (d,0,0) 的多项式 → 支撑搬到指定槽。"""
        out = {}
        for d in range(self.D + 1):
            c = vec.get((d, 0, 0))
            if c:
                e = [0, 0, 0]
                e[slot] = d
                out[tuple(e)] = c
        return out


class IntPoly:
    """整数系数快速求值：{指数: int}＋公分母（eval3 的整数快速路径）。

    term = (n/den)·u^i v^j t^l 通分到 den·ud^D·vd^D·td^D 后纯整数累加，
    一次 Fraction 归一——与 Fraction 逐项累加严格等值（端到端 trial 上
    两路径抽点对拍过，见 structural check eval_fastpath_agrees）。
    """

    def __init__(self, poly: dict, D: int):
        den = 1
        for c in poly.values():
            q = c.denominator
            den = den * q // math.gcd(den, q)
        self.nums = {}
        for e, c in poly.items():
            n = c.numerator * (den // c.denominator)
            if n:
                self.nums[e] = n
        self.den = den
        self.D = D

    def eval3(self, u, v, t):
        D = self.D

        def powers(x: Fraction):
            num, dnm = x.numerator, x.denominator
            pn, pd = [1] * (D + 1), [1] * (D + 1)
            for i in range(1, D + 1):
                pn[i] = pn[i - 1] * num
                pd[i] = pd[i - 1] * dnm
            return pn, pd

        UN, UD = powers(u)
        VN, VD = powers(v)
        TN, TD = powers(t)
        acc = 0
        for ((i, j, l), n) in self.nums.items():
            acc += (n * UN[i] * VN[j] * TN[l]
                    * UD[D - i] * VD[D - j] * TD[D - l])
        return Fraction(acc, self.den * UD[D] * VD[D] * TD[D])


# ============================================================ (ii)–(iv) 商装配
class S3Assembly:
    """S₃ 商 cut 构造的独立第二实现（数学定义直译，零仓码 import）。"""

    SLOT_SHARES_GM = {                       # share 键 → gm 系数 GM_OF
        "AA_in": F0, "AA_inX": F0,
        "AB_in": F0, "AB_inX": F0, "AB_inY": F0,
        "AA_out": Fraction(-1, 3),           # (h_AA−ψ_AA)/6 − gm/3
        "AB_out": Fraction(-2, 3),           # (h_AB−4ψ_AB)/3 − 2gm/3
    }
    LAM_SPEC = {                             # 轨道 → (三槽 share 键, 常数变量)
        "AAA": (("AA_in", "AA_in", "AA_in"), "c_A"),
        "AAB": (("AA_out", "AB_in", "AB_in"), "c_B"),
        "ABC": (("AB_out", "AB_out", "AB_out"), "c_C"),
    }
    CLASS_COUNTS = {"AAA": 3, "AAB": 6, "ABC": 1}     # 每轨道类数
    TRIPLE_COUNTS = {"AAA": 1, "AAB": 9, "ABC": 27}   # 每类三点计数

    def __init__(self, lo: Fraction, M: int, K: int):
        self.lo, self.M, self.K = lo, M, K
        self.D = self.d_H = 2 * M - 2
        self.ring = FRing(self.D)
        ring = self.ring
        self.F_sizes = [M - k for k in range(K)]

        # ---- (ii) Q_k 递推 ----
        one = ring.mono((0, 0, 0))
        t_m_uv = ring.sub_(ring.mono((0, 0, 1)), ring.mono((1, 1, 0)))
        om = ring.sub_(ring.add(ring.add(one, ring.mono((2, 0, 0), Fraction(-1))),
                                ring.mono((0, 2, 0), Fraction(-1))),
                       ring.mono((2, 2, 0), Fraction(-1)))   # 1−u²−v²+u²v²
        assert om == ring.mul(ring.sub_(ring.mono((0, 0, 0)), ring.mono((2, 0, 0))),
                              ring.sub_(ring.mono((0, 0, 0)), ring.mono((0, 2, 0))))
        Qs = [one, t_m_uv]
        while len(Qs) < K:
            Qs.append(ring.sub_(ring.scale(ring.mul(t_m_uv, Qs[-1]), 2),
                                ring.mul(om, Qs[-2])))
        self.Qs = Qs[:K]

        # ---- (iii) Y_cols / gm_cols / K_cols ----
        self.Y_cols, self.col_kab = [], []
        for k in range(K):
            for a_ in range(M - k):
                for b_ in range(M - k):
                    self.col_kab.append((k, a_, b_))
                    self.Y_cols.append(
                        ring.mul(ring.mono((a_, b_, 0)), Qs[k]))
        self.Y3_cols = [ring.subst_vars(Y, (0, 2, 1)) for Y in self.Y_cols]  # p(u,t,v)
        self.Y5_cols = [ring.subst_vars(Y, (1, 2, 0)) for Y in self.Y_cols]  # p(v,t,u)

        def subst_keep(vec, keep):
            out = {}
            for ((i, j, l), c) in vec.items():
                d = ((i if keep[0] else 0) + (j if keep[1] else 0)
                     + (l if keep[2] else 0))
                out[(d, 0, 0)] = out.get((d, 0, 0), F0) + c
            return out

        self.gm_cols = [ring.add(ring.add(subst_keep(Y, (False, True, True)),
                                          subst_keep(Y, (True, False, True))),
                                 subst_keep(Y, (True, True, False)))
                        for Y in self.Y_cols]
        self.K_cols = [ring.scale(ring.add(ring.add(Y, Y3), Y5), Fraction(-2))
                       for Y, Y3, Y5 in zip(self.Y_cols, self.Y3_cols, self.Y5_cols)]
        self._colcache = {}

        # ---- (v) sos_def（cut 域乘子族）----
        def mons_upto(dmax):
            return [e for e in ring.mons if sum(e) <= dmax]

        detG = [((0, 0, 0), F1), ((1, 1, 1), Fraction(2)),
                ((2, 0, 0), Fraction(-1)), ((0, 2, 0), Fraction(-1)),
                ((0, 0, 2), Fraction(-1))]
        self.sos_def = [("1", [((0, 0, 0), F1)], mons_upto(self.D // 2))]
        for slot in range(3):
            ue = tuple(1 if s == slot else 0 for s in range(3))
            self.sos_def.append((f"{'uvt'[slot]}-lo",
                                 [((0, 0, 0), -lo), (ue, F1)],
                                 mons_upto((self.D - 1) // 2)))
        for slot in range(3):
            ue = tuple(1 if s == slot else 0 for s in range(3))
            self.sos_def.append((f"1-{'uvt'[slot]}",
                                 [((0, 0, 0), F1), (ue, Fraction(-1))],
                                 mons_upto((self.D - 1) // 2)))
        self.sos_def.append(("detG", detG, mons_upto((self.D - 3) // 2)))

        # ---- (vi) minorant（Lukács；一侧 [lo,1)）----
        self.deg_p = 2 * self.d_H + 1
        d_H = self.d_H
        Csub = [[F0] * (d_H + 1) for _ in range(self.deg_p + 1)]
        for i in range(d_H + 1):
            for m_ in range(i + 1):
                Csub[2 * m_][i] += Fraction(math.comb(i, m_) * ((-2) ** m_))
        self.Cp = [[F0] * (d_H + 1) for _ in range(self.deg_p + 1)]
        for r in range(1, self.deg_p + 1, 2):
            self.Cp[r] = [-2 * x for x in Csub[r - 1]]
        self.p_const = [F0] * (self.deg_p + 1)
        self.p_const[0] = F1
        self.b2 = (F1 - lo) / 2
        self.sig_def = [("sig0", list(range(0, d_H + 1)), [(0, F1)]),
                        ("sig1", list(range(0, d_H + 1)), [(1, F1)]),
                        ("sig2", list(range(0, d_H)), [(0, self.b2), (2, Fraction(-1))]),
                        ("sig3", list(range(0, d_H)),
                         [(1, self.b2), (3, Fraction(-1))])]
        self.w_hat = ceil_sqrt_rat(self.b2)
        self.h_of = {"AA": "h_AA", "AB": "h_AB"}

        # ---- 全 10 类结构（⑧ 一致性＋③ 恒等式用）----
        self.full_classes = []
        for X in range(3):
            for Y in range(X, 3):
                for Z in range(Y, 3):
                    need = {}
                    for tt in (X, Y, Z):
                        need[tt] = need.get(tt, 0) + 1
                    mult = sorted(need.values(), reverse=True)
                    orbit = "AAA" if mult == [3] else ("AAB" if mult == [2, 1] else "ABC")
                    perm_id = "ut" if (Y == Z and X != Y) else "id"
                    self.full_classes.append(((X, Y, Z), orbit, perm_id))
        assert len(self.full_classes) == 10

        def cat_key(pair, W):
            P, Q = pair
            if P < Q:
                if W == P:
                    return "inX"
                if W == Q:
                    return "inY"
                return "out"
            return "inX" if W == P else "out"

        def share_key(P, Q, W):
            same = "AA" if P == Q else "AB"
            return f"{same}_{cat_key((P, Q), W)}"

        self.full_share_keys = {}
        for (cls, _orbit, _pid) in self.full_classes:
            X, Y, Z = cls
            self.full_share_keys[cls] = (share_key(X, Y, Z), share_key(X, Z, Y),
                                         share_key(Y, Z, X))

    # ---------------- share / λ / SOS / minorant ----------------
    def share_lp(self, key, data):
        """share 的一元 LP 部分（键归一化：AA_inX→AA_in=ψ_AA 等）。"""
        if key in ("AA_inX", "AA_in"):
            return list(data["psi_AA"])
        if key in ("AB_inX", "AB_inY", "AB_in"):
            return list(data["psi_AB"])
        if key == "AA_out":
            return [(hh - pp) / 6 for hh, pp in zip(data["h_AA"], data["psi_AA"])]
        if key == "AB_out":
            return [(hh - 4 * pp) / 3 for hh, pp in zip(data["h_AB"], data["psi_AB"])]
        raise KeyError(key)

    def _cols_for_gm(self, gpat):
        """列族缓存：K_col + Σ_slot g_slot·lift_slot0(gm_col, slot)。"""
        key = tuple(gpat)
        if key in self._colcache:
            return self._colcache[key]
        cols = []
        for idx in range(len(self.Y_cols)):
            col = dict(self.K_cols[idx])
            gmc = self.gm_cols[idx]
            for slot in range(3):
                g = gpat[slot]
                if g:
                    for d in range(self.D + 1):
                        c = gmc.get((d, 0, 0))
                        if c:
                            e = [0, 0, 0]
                            e[slot] = d
                            k2 = tuple(e)
                            s = col.get(k2, F0) + g * c
                            if s:
                                col[k2] = s
                            else:
                                col.pop(k2, None)
            cols.append({e: c for e, c in col.items() if c})
        self._colcache[key] = cols
        return cols

    def lam(self, orbit: str, data: dict):
        """(iv) λ_orbit 系数向量（份额 + c + K/gm 列全装配）。"""
        ring = self.ring
        keys, cvar = self.LAM_SPEC[orbit]
        out = {}
        for slot in range(3):
            out = ring.add(out, ring.uni_at_slot(self.share_lp(keys[slot], data), slot))
        out = ring.add(out, {(0, 0, 0): -data[cvar]})
        gpat = tuple(self.SLOT_SHARES_GM[k] for k in keys)
        cols = self._cols_for_gm(gpat)
        F = data["F"]
        for idx, (k, a_, b_) in enumerate(self.col_kab):
            c = F[k][a_][b_]
            if c:
                for (e, cc) in cols[idx].items():
                    s = out.get(e, F0) + c * cc
                    if s:
                        out[e] = s
                    else:
                        out.pop(e, None)
        return out

    def full_lam(self, cls, data: dict):
        """⑧ 全类 (X,Y,Z) 的 λ（一般 share 公式，独立于轨道代表）。"""
        ring = self.ring
        keys = self.full_share_keys[cls]
        orbit = next(o for (c, o, _p) in self.full_classes if c == cls)
        _, cvar = self.LAM_SPEC[orbit]
        out = {}
        for slot in range(3):
            out = ring.add(out, ring.uni_at_slot(self.share_lp(keys[slot], data), slot))
        out = ring.add(out, {(0, 0, 0): -data[cvar]})
        gpat = tuple(self.SLOT_SHARES_GM[k] for k in keys)
        cols = self._cols_for_gm(gpat)
        F = data["F"]
        for idx, (k, a_, b_) in enumerate(self.col_kab):
            c = F[k][a_][b_]
            if c:
                for (e, cc) in cols[idx].items():
                    s = out.get(e, F0) + c * cc
                    if s:
                        out[e] = s
                    else:
                        out.pop(e, None)
        return out

    def sos_sum(self, Bblocks: dict):
        """(v) Σ_8块 mult(p)·(v_pᵀ B v_p) 的系数向量。"""
        out = {}
        for (name, mult, mons) in self.sos_def:
            B = Bblocks[name]
            m = len(mons)
            for p_ in range(m):
                row = B[p_]
                ep = mons[p_]
                for q_ in range(m):
                    c = row[q_]
                    if not c:
                        continue
                    eq = mons[q_]
                    b0, b1, b2 = ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2]
                    for (eg, cg) in mult:
                        k2 = (b0 + eg[0], b1 + eg[1], b2 + eg[2])
                        s = out.get(k2, F0) + c * cg
                        if s:
                            out[k2] = s
                        else:
                            out.pop(k2, None)
        return out

    def minorant_rhs(self, h):
        """(vi) rhs_r = Σ_j Cp[r][j]·h[j] + p_const[r]。"""
        return [sum(self.Cp[r][j] * h[j] for j in range(self.d_H + 1))
                + self.p_const[r] for r in range(self.deg_p + 1)]

    def minorant_lhs(self, Sblocks: dict):
        """(vi) Σ_4σ块 (Σ y^{yp+yq})·mult 的系数向量。"""
        out = [F0] * (self.deg_p + 1)
        for (name, mons_y, mult) in self.sig_def:
            S = Sblocks[name]
            m = len(mons_y)
            for p_ in range(m):
                row = S[p_]
                for q_ in range(m):
                    c = row[q_]
                    if not c:
                        continue
                    base = mons_y[p_] + mons_y[q_]
                    for (eg, cg) in mult:
                        out[base + eg] += c * cg
        return out

    def s_forms(self, data: dict):
        """(viii) s=Σ_k⟨F^k,Y_k⟩ 的系数向量与 s(1,1,1)=ΣΣF⁽⁰⁾。"""
        vec = {}
        F = data["F"]
        for idx, (k, a_, b_) in enumerate(self.col_kab):
            c = F[k][a_][b_]
            if c:
                vec = self.ring.add(vec, self.ring.scale(self.Y_cols[idx], c))
        s111 = sum(sum(row) for row in F[0])
        return vec, s111

    def gm_uni(self, data: dict):
        """gm 的一元系数（d_H+1；独立装配面，供记录）。"""
        out = [F0] * (self.d_H + 1)
        F = data["F"]
        for idx, (k, a_, b_) in enumerate(self.col_kab):
            c = F[k][a_][b_]
            if c:
                gmc = self.gm_cols[idx]
                for d in range(self.d_H + 1):
                    cc = gmc.get((d, 0, 0))
                    if cc:
                        out[d] += c * cc
        return out


# ============================================================ 证书装载
SOS_NAMES = ("1", "u-lo", "v-lo", "t-lo", "1-u", "1-v", "1-t", "detG")
SIG_NAMES = ("sig0", "sig1", "sig2", "sig3")


def load_data(asm: S3Assembly, cert: dict):
    b = cert["blocks"]
    if cert["params"]["M"] != asm.M or cert["params"]["K"] != asm.K:
        fail(f"证书 params 与装配不符：{cert['params']}")
    if Fraction(cert["params"]["a0"]) != asm.lo:
        fail(f"证书 a0={cert['params']['a0']} ≠ 装配 lo={asm.lo}")

    def uni(name):
        v = [Fraction(x) for x in b[f"{name}_diag"]]
        if len(v) != asm.d_H + 1:
            fail(f"{name}_diag 长度 {len(v)} ≠ d_H+1={asm.d_H + 1}")
        return v

    data = dict(
        h_AA=uni("h_AA"), h_AB=uni("h_AB"),
        psi_AA=uni("psi_AA"), psi_AB=uni("psi_AB"),
        e=Fraction(b["e"][0]), c_A=Fraction(b["c_A"][0]),
        c_B=Fraction(b["c_B"][0]), c_C=Fraction(b["c_C"][0]),
        F=[],
        B={}, sig={},
    )
    for k, mk in enumerate(asm.F_sizes):
        Mx = [[Fraction(x) for x in row] for row in b[f"F{k}"]]
        if len(Mx) != mk or any(len(r) != mk for r in Mx):
            fail(f"F{k} 尺寸不符（期望 {mk}×{mk}）")
        data["F"].append(Mx)
    for orbit in ("AAA", "AAB", "ABC"):
        for nm in SOS_NAMES:
            Mx = [[Fraction(x) for x in row] for row in b[f"B_{orbit}_{nm}"]]
            data["B"][f"{orbit}_{nm}"] = Mx
    for cls in ("AA", "AB"):
        for nm in SIG_NAMES:
            Mx = [[Fraction(x) for x in row] for row in b[f"sig_{cls}_{nm}"]]
            data["sig"][f"{cls}_{nm}"] = Mx
    return data


# ============================================================ 结构性自查（⑤）
def structural_checks(asm: S3Assembly, data: dict, rng) -> dict:
    ring = asm.ring
    out = {}

    # ⑤-1 单项式计数：分次枚举 |mons| = C(D+3,3) = 969 = C(19,3)
    expect_nmon = math.comb(asm.D + 3, 3)
    out["nmon_equals_C19_3"] = bool(asm.ring.nmon == expect_nmon == 969)

    # ⑤-2 Y 列计数：Σ_k (M−k)² = 271
    expect_y = sum(mk * mk for mk in asm.F_sizes)
    out["Y_cols_equals_271"] = bool(len(asm.Y_cols) == expect_y == 271)

    # ⑤-3 Q_k 的 (u,v) 系数对称（逐系数精确）
    sym_ok = True
    for k, Q in enumerate(asm.Qs):
        if ring.swap_uv_exp(Q) != Q:
            sym_ok = False
    out["Q_uv_symmetric_all_k"] = sym_ok

    # ⑤-4 deg_t(Q_k)=k（递推结构；Q_k 关于 t 恰为 k 次）
    deg_ok = all(max((e[2] for e in Q), default=0) == k for k, Q in enumerate(asm.Qs))
    out["Q_degree_in_t_equals_k"] = bool(deg_ok)

    # ⑤-5 槽置换方向：subst(t−uv) 得 v−ut（p(u,t,v)）/ u−vt（p(v,t,u)）
    p = ring.sub_(ring.mono((0, 0, 1)), ring.mono((1, 1, 0)))
    got3 = ring.subst_vars(p, (0, 2, 1))
    got5 = ring.subst_vars(p, (1, 2, 0))
    exp3 = ring.sub_(ring.mono((0, 1, 0)), ring.mono((1, 0, 1)))
    exp5 = ring.sub_(ring.mono((1, 0, 0)), ring.mono((0, 1, 1)))
    out["perm_direction_t_minus_uv"] = bool(got3 == exp3 and got5 == exp5)

    # ⑤-6 ŵ=⌈√b²⌉ 覆盖：ŵ² ≥ b²（R2 权重常数覆盖 y 域）
    out["w_hat_sq_ge_b2"] = bool(asm.w_hat * asm.w_hat >= asm.b2)
    out["w_hat_is_117_125"] = bool(asm.w_hat == Fraction(117, 125))

    # ⑤-7 B/sig 块维度与 sos/sig 基尺寸一致
    dims_ok = True
    for orbit in ("AAA", "AAB", "ABC"):
        for (nm, _m, mons) in asm.sos_def:
            Bx = data["B"][f"{orbit}_{nm}"]
            m = len(mons)
            if len(Bx) != m or any(len(r) != m for r in Bx):
                dims_ok = False
    for cls in ("AA", "AB"):
        for (nm, mons_y, _mu) in asm.sig_def:
            Sx = data["sig"][f"{cls}_{nm}"]
            m = len(mons_y)
            if len(Sx) != m or any(len(r) != m for r in Sx):
                dims_ok = False
    out["block_dims_match_bases"] = dims_ok
    expect_dims = {nm: len(m) for (nm, _g, m) in asm.sos_def}
    out["sos_base_dims"] = expect_dims           # {1:165, u-lo:120, …, detG:84}

    # ⑤-8 IntPoly 快速路径与 Fraction 慢路径求值一致（随机点抽点对拍）
    s_vec, _ = asm.s_forms(data)
    ip = IntPoly(s_vec, asm.D)
    agree = all(ip.eval3(Fraction(-1, 3), Fraction(2, 5), Fraction(-1, 7))
                == ring.eval3(s_vec, Fraction(-1, 3), Fraction(2, 5), Fraction(-1, 7))
                for _ in range(2))
    u_, v_, t_ = (Fraction(rng.randint(-64, 64), 64) for _ in range(3))
    agree = agree and ip.eval3(u_, v_, t_) == ring.eval3(s_vec, u_, v_, t_)
    out["eval_fastpath_agrees"] = bool(agree)

    if not all(v for k, v in out.items() if isinstance(v, bool)):
        bad = [k for k, v in out.items() if isinstance(v, bool) and not v]
        fail(f"结构性自查失败：{bad}")
    return out


# ============================================================ 恒等式 trial（③）
def rational_point(a: Fraction, b: Fraction):
    """单位球面的有理点（球极投影参数化，自写）：(2a,2b,1−a²−b²)/(1+a²+b²)。"""
    s = 1 + a * a + b * b
    return (2 * a / s, 2 * b / s, (1 - a * a - b * b) / s)


def identity_trials(asm: S3Assembly, data: dict, trials: int, seed: int) -> dict:
    """③ Σ_84 λ_cls + Σ_all == ΣH − e_dy（随机有理构型，精确 == 0）。"""
    ring = asm.ring
    rng = random.Random(seed)
    s_vec, _s111 = asm.s_forms(data)
    s_ip = IntPoly(s_vec, asm.D)
    lam_ip = {}
    lam_full = {}
    for cls in (c for (c, _o, _p) in asm.full_classes):
        lam_full[cls] = asm.full_lam(cls, data)
        lam_ip[cls] = IntPoly(lam_full[cls], asm.D)
    recs = []
    for ti in range(trials):
        X = [rational_point(Fraction(rng.randint(-64, 64), 64),
                            Fraction(rng.randint(-64, 64), 64)) for _ in range(N_POINTS)]
        G = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        sum_all = F0
        for i in range(N_POINTS):
            for j in range(N_POINTS):
                for l in range(N_POINTS):
                    sum_all += s_ip.eval3(G[i][j], G[i][l], G[j][l])
        sum_lam = F0
        for (i, j, l) in combinations(range(N_POINTS), 3):
            tt = sorted([(TYPES[i], i), (TYPES[j], j), (TYPES[l], l)])
            (_r0, i0), (_r1, j0), (_r2, l0) = tt
            cls = tuple(x[0] for x in tt)
            sum_lam += lam_ip[cls].eval3(G[i0][j0], G[i0][l0], G[j0][l0])
        sum_H = F0
        for i in range(N_POINTS):
            for j in range(i + 1, N_POINTS):
                cls = "AA" if TYPES[i] == TYPES[j] else "AB"
                sum_H += ring.eval1(data[asm.h_of[cls]], G[i][j])
        diff = (sum_lam + sum_all) - (sum_H - data["e"])
        ok = (diff == 0) and sum_all >= 0
        recs.append(dict(diff=str(diff), sum_all_sign_ok=bool(sum_all >= 0),
                         ok=bool(ok)))
        log(f"[ident] trial {ti + 1}/{trials}: Σλ+Σ_all−(ΣH−e) = {diff}"
            f"（Σ_all {'≥0 ✓' if sum_all >= 0 else '<0 ✗'}）")
        if diff != 0:
            fail("typed 恒等式失败（残差 ≠ 0）——独立装配与证书数据不相容")
        if sum_all < 0:
            fail("分型正性抽查失败（Σ_all < 0）")
    return dict(seed=seed, trials_expected=trials, records=recs,
                residual="0（精确，== 0 逐 trial）",
                statement=("Σ_84 λ_cls(x) + Σ_all(x) = ΣH(x) − e_dy，证书 dyadic 数据、"
                           "随机有理构型（球极投影有理点）× %d；Σ_all ≥ 0 为引理 4.1 "
                           "分型正性抽查" % trials))


def orbit_consistency(asm: S3Assembly, data: dict) -> dict:
    """⑧ 全 10 类 λ_full == λ_orbit∘P（P=id 或 u↔t 换位；逐系数精确）。"""
    ring = asm.ring
    lam_orbit = {o: asm.lam(o, data) for o in ("AAA", "AAB", "ABC")}
    ok_all, details = True, []
    for (cls, orbit, perm_id) in asm.full_classes:
        lf = asm.full_lam(cls, data)
        ref = (lam_orbit[orbit] if perm_id == "id"
               else ring.subst_vars(lam_orbit[orbit], (2, 1, 0)))
        ok = (lf == ref)
        ok_all = ok_all and ok
        details.append(dict(cls=list(cls), orbit=orbit, perm=perm_id, ok=bool(ok)))
    if not ok_all:
        fail("轨道置换一致性失败（λ_full ≠ λ_orbit∘P 的类存在）")
    return dict(classes=10, all_ok=True, details=details)


# ============================================================ 主流程
def main() -> None:
    t0 = time.time()
    ap = argparse.ArgumentParser(description="R9A S₃ 商环装配自写重推（第二实现）")
    ap.add_argument("--cert", default=str(CERT_DEFAULT))
    ap.add_argument("--out", default=str(OUT_DEFAULT))
    ap.add_argument("--trials", type=int, default=TRIALS_DEFAULT)
    ap.add_argument("--seed", type=int, default=SEED_DEFAULT)
    args = ap.parse_args()
    cert_path = Path(args.cert).resolve()
    out_path = Path(args.out).resolve()

    cert = json.loads(cert_path.read_text())
    A0 = Fraction(cert["params"]["a0"])      # 切口 lo 由证书参数自持（唯一输入）
    assert A0 == Fraction(-187, 250) and cert["params"]["M"] == 9 \
        and cert["params"]["K"] == 6, cert["params"]
    log(f"[load ] 证书 {cert_path.name}（{cert_path.stat().st_size / 1e6:.1f}MB）："
        f"kind={cert['kind']} tag={cert['tag']} params={cert['params']}")
    asm = S3Assembly(A0, cert["params"]["M"], cert["params"]["K"])
    log(f"[asm  ] FRing D={asm.D} nmon={asm.ring.nmon}（C(19,3)={math.comb(19, 3)}）；"
        f"Y_cols={len(asm.Y_cols)}；deg_p={asm.deg_p}；"
        f"ŵ={asm.w_hat}（b²={asm.b2}）")

    # ---- 数据装载（唯一推导输入＝证书 blocks）----
    data = load_data(asm, cert)
    log(f"[data ] blocks→Fraction 完成：F×{len(data['F'])}＋B×{len(data['B'])}"
        f"＋sig×{len(data['sig'])}＋一元 4＋标量 4")

    # ---- 结构性自查（cheap-first 第一层）----
    rng = random.Random(args.seed)
    sc = structural_checks(asm, data, rng)
    log(f"[struc] 结构性自查 {sum(1 for v in sc.values() if isinstance(v, bool))} 项全过"
        f"（Q_(u,v)对称/deg_t=k/置换方向/ŵ²≥b²/块维度/快慢求值对拍…）")

    # ---- 归一化（恒等式的代数基础）----
    s111 = sum(sum(row) for row in data["F"][0])
    nrm = (3 * data["c_A"] + 54 * data["c_B"] + 27 * data["c_C"]
           - 9 * s111 - data["e"])
    if nrm != 0:
        fail(f"归一化残差 {nrm} ≠ 0（3c_A+54c_B+27c_C−9ΣF⁽⁰⁾−e）")
    log("[nrm  ] 归一化残差 = 0（精确）✓")

    # ---- (vii) R1 逐轨道重算＋provenance 逐位比对 ----
    prov = cert["provenance"]["residuals"]
    R1, R1_resid = {}, {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = asm.lam(orbit, data)
        sv = asm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in asm.sos_def})
        resid = {e: lv.get(e, F0) - sv.get(e, F0) for e in set(lv) | set(sv)}
        R1_resid[orbit] = resid
        R1[orbit] = sum(abs(x) for x in resid.values())
        if Fraction(prov["R1"][orbit]) != R1[orbit]:
            fail(f"R1_{orbit} 重算 {R1[orbit]} ≠ provenance {prov['R1'][orbit]}"
                 f"（R1 逐位失配——独立装配与证书不符）")
        log(f"[R1   ] R1_{orbit} = {R1[orbit]} = {float(R1[orbit]):.6e} ✓ 逐位")

    # ---- (vii) R2 逐类重算＋provenance 逐位比对 ----
    R2 = {}
    for cls in ("AA", "AB"):
        lhs = asm.minorant_lhs({nm: data["sig"][f"{cls}_{nm}"]
                                for (nm, _my, _mu) in asm.sig_def})
        rhs = asm.minorant_rhs(data[asm.h_of[cls]])
        R2[cls] = sum(abs(rhs[j] - lhs[j]) * asm.w_hat ** j
                      for j in range(asm.deg_p + 1))
        if Fraction(prov["R2"][cls]) != R2[cls]:
            fail(f"R2_{cls} 重算 ≠ provenance（R2 逐位失配）")
        log(f"[R2   ] R2_{cls} = {float(R2[cls]):.6e} ✓ 逐位")

    defl = sum(asm.CLASS_COUNTS[o] * asm.TRIPLE_COUNTS[o] * R1[o] for o in R1)
    R2max = max(R2.values())
    if Fraction(prov["defl"]) != defl:
        fail(f"defl 重算 {defl} ≠ provenance {prov['defl']}")
    if Fraction(prov["R2max"]) != R2max:
        fail(f"R2max 重算 ≠ provenance")
    log(f"[defl ] defl = {defl} = {float(defl):.6e} ✓；"
        f"R2max = {float(R2max):.6e} ✓（均逐位）")

    # ---- certified 重算 == claimed_bound（②）----
    certified = (data["e"] - defl) / (1 + R2max)
    claimed = Fraction(cert["claimed_bound"])
    if certified != claimed:
        fail(f"certified 重算 {certified} ≠ claimed_bound {cert['claimed_bound']}"
             f"（certified 逐位失配）")
    log(f"[cert ] certified 重算 == claimed_bound ✓ 逐位 "
        f"（= {float(certified):.15f}）")
    if claimed > E_STAR_DEC + Fraction(1, 10 ** 6):
        fail(f"claimed_bound {float(claimed)} > E*+1e-6（铁律）")

    # ---- ④ 消费端交叉核验：ε_forcing==(1+R2max)(E*−certified) ----
    eps = (1 + R2max) * (E_STAR_DEC - certified)
    eps_alt = (1 + R2max) * E_STAR_DEC - data["e"] + defl   # 展开形（应相等）
    l2r_ok, l2r_eps, three_way = None, None, None
    if L2R_PATH.exists():
        l2r = json.loads(L2R_PATH.read_text())
        l2r_eps = l2r["eps_forcing"]["exact"]
        l2r_ok = (eps == Fraction(l2r_eps))
        if not l2r_ok:
            fail(f"ε_forcing 重算 {eps} ≠ l2_rigorous.json eps_forcing.exact")
        cr = l2r["certificate_rebuild"]
        three_way = dict(
            R1={o: bool(Fraction(cr["R1_exact"][o]) == R1[o]) for o in R1},
            R2={c: bool(Fraction(cr["R2_exact"][c]) == R2[c]) for c in R2},
            defl=bool(Fraction(cr["defl_exact"]) == defl),
            R2max=bool(Fraction(cr["R2max_exact"]) == R2max),
            certified=bool(Fraction(cr["certified_recomputed"]) == certified
                           == Fraction(cr["claimed_bound"]) == claimed),
        )
        if not all(all(v.values()) if isinstance(v, dict) else v
                   for v in three_way.values()):
            fail("与 l2_rigorous.json certificate_rebuild 逐位对账失败")
        log(f"[eps  ] ε_forcing = {float(eps):.10e} ✓ 与 l2_rigorous.json "
            f"eps_forcing.exact 逐位相等；certificate_rebuild 全项三方逐位 ✓")
    else:
        log("[eps  ] l2_rigorous.json 不在盘（--cert 指向副本？）——④ 对账跳过，如实记")
    if eps != eps_alt:
        fail("ε_forcing 两种装配（(1+R2max)(E*−c) vs (1+R2max)E*−e+defl）不相等")

    # ---- ⑧ 轨道置换一致性（10 类逐系数）----
    oc = orbit_consistency(asm, data)
    log("[orbit] 全 10 类 λ_full == λ_orbit∘P 逐系数一致 ✓")
    swap_l1 = all(
        sum(abs(x) for x in R1_resid[o].values())
        == sum(abs(x) for x in asm.ring.subst_vars(R1_resid[o], (2, 1, 0)).values())
        for o in ("AAA", "AAB", "ABC"))
    if not swap_l1:
        fail("swap_ut 未保持 ℓ₁（换位类的 −R1 界不成立）")
    log("[swap ] u↔t 换位保持 λ−SOS 残差 ℓ₁ ✓（三轨道）")

    # ---- ③ 恒等式 trial（最贵殿后）----
    ident = identity_trials(asm, data, max(args.trials, 3), args.seed)

    # ---- 运行时零 import 复核 ----
    loaded_forbidden = sorted({m.split(".")[0] for m in sys.modules}
                              & set(FORBIDDEN_ROOTS))
    if loaded_forbidden:
        fail(f"运行时检出禁 import 模块：{loaded_forbidden}")

    doc = dict(
        kind="n9-r9-s3-rederive",
        script="bounds/r9_s3_rederive.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        cli=dict(argv=sys.argv[1:], trials=max(args.trials, 3), seed=args.seed,
                 cert=str(cert_path), out=str(out_path)),
        inputs=dict(
            certificate=str(cert_path),
            certificate_is_sole_derivation_input=True,
            l2_rigorous=str(L2R_PATH),
            l2_rigorous_role="对账存档（验收①②④目标），不参与推导",
            E_star=dict(value=str(E_STAR_DEC),
                        caliber="十进制 25759986531/10^9（D28 裁决 3 主口径）",
                        semantics="三源校验参考值，非已证最优")),
        independence=dict(
            stdlib_only=True,
            forbidden_imports=list(FORBIDDEN_ROOTS),
            static_scan_owner="r9_s3_gate.py G1（AST）",
            runtime_modules_check="sys.modules 根集合 ∩ 禁清单 = ∅（本文件末尾复核）",
            second_implementation=(
                "多项式＝稀疏 dict {指数:Fraction}（构造端为稠密 list）；"
                "Q_k/Y_cols/gm_cols/K_cols/lam/sos_sum/minorant 全部"
                "自数学定义重写，未 import typed_ladder/QuotientMaps/thomson_certs/"
                "sdp_bound/sdp_certify/l2_rigorize 任何代码路径；单项式枚举次序取"
                "证书 Gram 块的隐式基约定（数据格式对齐，值级结果与枚举次序无关）")),
        provenance_echo=dict(
            cert_code_version=cert["provenance"]["code_version"],
            round_bits_k=cert["provenance"]["round_bits"],
            solution_sha256_16=cert["provenance"]["solution_sha256_16"],
            cert_date=cert["provenance"]["date"],
            bound_formula=cert["provenance"]["bound_formula"],
            note="round_bits（--k）＝dyadic 舍入位数 48，由证书 provenance 回声；"
                 "本验证器消费已舍入证书、不做舍入"),
        sizes=dict(D=asm.D, nmon=asm.ring.nmon, Y_cols=len(asm.Y_cols),
                   sos_base_dims=sc.pop("sos_base_dims"),
                   deg_p=asm.deg_p, w_hat=str(asm.w_hat), b2=str(asm.b2),
                   class_counts={"AAA": "3类×1", "AAB": "6类×9", "ABC": "1类×27"}),
        structural_checks=sc,
        normalization_residual="0（精确：3c_A+54c_B+27c_C−9·ΣF⁽⁰⁾−e == 0）",
        R1_exact={o: str(v) for o, v in R1.items()},
        R1_float={o: float(v) for o, v in R1.items()},
        R2_exact={c: str(v) for c, v in R2.items()},
        R2_float={c: float(v) for c, v in R2.items()},
        defl_exact=str(defl), defl_float=float(defl),
        R2max_exact=str(R2max), R2max_float=float(R2max),
        certified_recomputed=str(certified), certified_float=float(certified),
        claimed_bound=cert["claimed_bound"],
        bitwise_equal_to_claimed=True,
        provenance_residuals_match=dict(
            R1={o: True for o in R1}, R2={c: True for c in R2},
            defl=True, R2max=True),
        l2_rigorous_match=dict(
            eps_forcing_exact=l2r_eps, eps_recomputed=str(eps),
            eps_bitwise_equal=l2r_ok,
            eps_formula="ε_forcing == (1+R2max)·(E*−certified)（E* 十进制口径）",
            certificate_rebuild_three_way=bool(l2r_ok),
            certificate_rebuild_items=three_way),
        orbit_perm_consistency=oc,
        swap_ut_preserves_l1=True,
        identity=ident,
        scope=("严格数值层（Python Fraction）；PSD/LDLᵀ 38 块判定明确不在本验证器"
               "范围——复算员 R8 ⑧ 已自写 Fractions LDLᵀ 独立过 38/38＋三负对照"
               "（GAP-REPORT Round 8 节 ⑧），本文件不重复不冒充；typed 恒等式/"
               "引理 4.1 正性/Lukács 表示为结构性定理（PAPER.md §4–6.3），本文件"
               "的机器验证为随机有理点精确实例核验＋逐系数精确等式，未过 Lean 内核"),
        wall_s=round(time.time() - t0, 1),
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    print(json.dumps(dict(
        R1={o: str(v) for o, v in R1.items()},
        R2={c: str(v) for c, v in R2.items()},
        defl=str(defl), R2max=str(R2max),
        certified=str(certified), claimed_match=True,
        eps_forcing=str(eps), l2_rigorous_match=l2r_ok,
        identity_trials=len(ident["records"]),
        structural_checks_all_pass=True,
        out=str(out_path), wall_s=doc["wall_s"]), ensure_ascii=False, indent=1))
    log(f"[done ] R9A S₃ 商环装配自写重推全过（{doc['wall_s']}s）；"
        f"结果入 {out_path}；exit 0")


if __name__ == "__main__":
    main()
