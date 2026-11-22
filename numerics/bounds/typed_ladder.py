#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""typed_ladder.py — N=9 typed (3,3,3) cap 阶梯 Round 3：切口从 −0.90 抬向 m*。

构造 = typed/ 三点分型构造（core.py/solve.py，已过三层自检）的 **S₃ 商**版本 +
高精度路线 a（SDPA-GMP，与 hp_solve.py 同管线）+ slab_band.py 式精确认证。

## S₃ 商（本文件的核心省力装置）

(3,3,3) 分型在类型重标号群 S₃ 下不变：SDP 凸 ⟹ 最优解可取 S₃ 不变
（群平均不降 e）。不变解的结构：
  对类轨道 2 条：AA = {(X,X)}（9 对）、AB = {(X,Y),X<Y}（27 对）；
  三点轨道 3 条：AAA（3 个）、AAB（6 类 × 9 = 54 个）、ABC（27 个），合 84 ✓；
  F^{(X,k)} = F^{(k)}（每 k 一块，共 K 块）；ψ^{AB,inX} = ψ^{AB,inY} =: ψ_AB。
商 SDP 只解代表约束（3 条 slack 恒等式 + 2 条 minorant + 1 条归一化）：
  λ_AAA = ψ_AA(u)+ψ_AA(v)+ψ_AA(t) − c_A − 2[s(u,v,t)+s(u,t,v)+s(v,t,u)]
  λ_AAB = Sh^{AA,out}(u) + ψ_AB(v) + ψ_AB(t) − c_B − 2[s(u,v,t)+s(u,t,v)+s(v,t,u)]
  λ_ABC = Sh^{AB,out}(u)+Sh^{AB,out}(v)+Sh^{AB,out}(t) − c_C − 2[同上]
  Sh^{AA,out} = (h_AA − 2gm − ψ_AA)/6，Sh^{AB,out} = (h_AB − 2gm − 4ψ_AB)/3
  3c_A + 54c_B + 27c_C = e + 9·ΣF^{(0)}
（形式 (a,b,b) 的类满足 λ = λ_rep∘(u↔t 换位)——槽置换下 8 块乘子族封闭，
SOS 经 ΠBΠᵀ 转移；认证时对全部 10 类做**逐系数精确**核对，不靠这条论证。）

## SDPA-GMP 导出（与 hp_solve.py 同约定，已在该文件经 Clarabel 代入逐条校验）

  块：LP 对角（e；h/ψ/c 一律 ± 拆分——SDPA 的 LP 块是**非负**锥：2026-10-03
  本机以 b=−2 的 1×1 LP 块实测 pUNBD 证实；slab 证书里 h/ψ 有负系数），
  + F 块 K 块 + SOS 块 3×8 + σ 块 2×4；行 = 3·nmon(slack) + 2·(2d_H+2)
  (minorant) + 1(归一化)。系数全部纯 Fraction，40 位十进制写 .dat-s；
  SDPA-GMP 7.1.3（GMP 200 位）求解，.result 按 66 位十进制精确回读。
  F 块系数按对称化 (W_ab+W_ba)/2（a<b）发射——SDPA 的 2·X_ij 约定。

## 认证（对齐 slab_band.certify_slab 的"舍入＋精确残差折减"模式）

  1) dyadic 舍入 2^-k：h/ψ/c 最近、e 向下、F/SOS/σ 最近 + δI 修复
     （sdp_certify.repair_psd：exact LDLᵀ 判定，2^-40 地板）；c_C 由归一化
     以 Fraction 精确重算；
  2) 精确残差（纯 Fraction）：R1_orbit = ‖λ − SOS‖₁（域上逐点 |·| ≤ R1；
     乘子 1,u−lo,v−lo,t−lo,1−u,1−v,1−t,detG 在域 {≥lo}∩Gram 上非负）；
     R2_cls = Σ_j |r_j|·ŵ^j（ŵ ≥ b = √((1−lo)/2) 有理上界，ceil_sqrt）；
  3) certified = (e − (3R1_A + 54R1_B + 27R1_C)) / (1 + max(R2_AA, R2_AB))
     （恒等式 Σ_T λ_T + Σ_all = ΣH − e 精确自检；Σ_all ≥ 0 由 F ⪰ 0 精确成立）；
  4) 全 10 类逐系数核对 λ_full = λ_orbit∘P + 域抽查（有理点）+ minorant
     抽查 + 断言；证书 certificates/n9-stage-a4-typedcap-<tag>.json（全 'p/q'），
     --verify-cert 进程外独立重算（重建 + 精确 residual/certified 比对）。

## 阶梯（--all）

  a₀ ∈ {−0.90, −0.85, −0.80, −0.77, −0.755, −0.748}，(M,K) 默认 (7,6)；
  每档断言 0 < certified ≤ E* + 1e-6（违反 sys.exit(1)）；
  −0.748 档额外断言 certified > 25.757085350767（Round 2 区域纪录 m ≥ −151/200，
  其区域 ⊃ 本档区域，SDP 值单调 ⟹ 本档应更高）。结果写 results/typed_ladder.json。

用法（thomson-n9 下；求解 >10 分钟建议 run_in_background）：
  python3 numerics/bounds/typed_ladder.py --selftest          # 精确自检（无需 cvxpy）
  python3 numerics/bounds/typed_ladder.py --rung -0.748 [--M 8]      # 单档全流程
  python3 numerics/bounds/typed_ladder.py --certify -0.748 [--M 7]   # 只认证已解档
  python3 numerics/bounds/typed_ladder.py --all [--M 7]              # 阶梯
  python3 numerics/bounds/typed_ladder.py --crosscheck -0.9 6   # (6,6) Clarabel 交叉验证
  python3 numerics/bounds/typed_ladder.py --strip-study        # 条带可行性研究
  python3 numerics/bounds/typed_ladder.py --verify-cert certificates/n9-stage-a4-typedcap-m0748.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
WORKFLOW_CERTS = HERE.parents[2] / "thomson-workflow" / "certificates"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "typed"))
sys.path.insert(0, str(WORKFLOW_CERTS))

import sdp_bound                                              # noqa: E402
from sdp_certify import dyad, repair_psd, rational_point      # noqa: E402
from thomson_certs.exact import is_positive_definite         # noqa: E402

F0, F1 = Fraction(0), Fraction(1)
SEED = 20261003
TYPES = (3, 3, 3)
N = 9
REGIONAL_RECORD = Fraction("25.757085350767")   # Round 2: m ≥ −151/200 认证纪录
PHI_TOL = Fraction(1, 10 ** 6)
PARAM_SDPA = """500unsigned int maxIteration;
1.0E-30\tdouble 0.0 < epsilonStar;
1.0E4   double 0.0 < lambdaStar;
2.0   \tdouble 1.0 < omegaStar;
-1.0E5  double lowerBound;
1.0E5   double upperBound;
0.1    \tdouble 0.0 <= betaStar <  1.0;
0.3    \tdouble 0.0 <= betaBar  <  1.0, betaStar <= betaBar;
0.9    \tdouble 0.0 < gammaStar <  1.0;
1.0E-30\tdouble 0.0 < epsilonDash;
200     precision
"""
LADDER = [("-0.90", "-9/10"), ("-0.85", "-17/20"), ("-0.80", "-4/5"),
          ("-0.77", "-77/100"), ("-0.755", "-151/200"), ("-0.748", "-187/250")]


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    """结果 json/证书 provenance 的代码版本（git describe --always --dirty）。

    防 M6 式复现尾差：复算员曾发现代码版本演进致 −3.68e-9~−3.0e-8 尾差
    （commit e56be8f 以 HEAD 全档重解消除）——此后每份产物记录生成代码版本。"""
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


def load_E_star() -> Fraction:
    with open(WORKFLOW_CERTS.parent / "data" / "energies.json") as f:
        return Fraction(json.load(f)["energies"]["9"]["value"])


# ============================================================ Fraction 多项式环
class FRing:
    """sdp_bound.Poly3 的纯 Fraction 镜像（只取其索引结构，系数全重算）。"""

    def __init__(self, D: int):
        self.D = D
        ring = sdp_bound.Poly3(D)
        self.mons, self.index, self.nmon = ring.mons, ring.index, ring.nmon
        self._perm = ring.perm_maps

    def zero(self):
        return [F0] * self.nmon

    def mono(self, e, c=F1):
        v = self.zero()
        v[self.index[tuple(e)]] = c
        return v

    def mul(self, av, bv):
        out = self.zero()
        for p, ca in enumerate(av):
            if ca == 0:
                continue
            ep = self.mons[p]
            for q, cb in enumerate(bv):
                if cb == 0:
                    continue
                eq = self.mons[q]
                out[self.index[(ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])]] += ca * cb
        return out

    def perm(self, vec, which: int):
        """numpy 语义 cc[perm_maps[which]]：perm_maps[3] = p(u,t,v)、
        perm_maps[5] = p(v,t,u)（--selftest 以 (t−uv) ↦ v−ut / u−vt 复核）。"""
        pm = self._perm[which]
        return [vec[pm[j]] for j in range(self.nmon)]

    def swap_ut(self, vec):
        """p(u,v,t) ↦ p(t,v,u)（u↔t 换位；AAB 轨道形式 (a,b,b) 类的槽置换）。"""
        return [vec[self.index[(l, j, i)]] for (i, j, l) in self.mons]

    def eval3(self, vec, u, v, t):
        pu = [F1] + [F0] * self.D
        pv = [F1] + [F0] * self.D
        pt = [F1] + [F0] * self.D
        for i in range(1, self.D + 1):
            pu[i] = pu[i - 1] * u
            pv[i] = pv[i - 1] * v
            pt[i] = pt[i - 1] * t
        acc = F0
        for p, c in enumerate(vec):
            if c:
                i, j, l = self.mons[p]
                acc += c * pu[i] * pv[j] * pt[l]
        return acc

    def eval1(self, coeffs, x):
        acc, xp = F0, F1
        for c in coeffs:
            acc += c * xp
            xp *= x
        return acc

    def uni_at_slot(self, uni, slot):
        """一元系数（index=次数，长 d_H+1）→ 放到 slot 变量上的 Poly3 向量。"""
        out = self.zero()
        e = [0, 0, 0]
        for d, c in enumerate(uni):
            if c:
                e[slot] = d
                out[self.index[tuple(e)]] += c
                e[slot] = 0
        return out

    def lift_slot0(self, vec, slot):
        """Poly3 向量（支撑在 slot0 的 (d,0,0)）→ 支撑搬到指定 slot。"""
        out = self.zero()
        for d in range(self.D + 1):
            c = vec[self.index[(d, 0, 0)]]
            if c:
                e = [0, 0, 0]
                e[slot] = d
                out[self.index[tuple(e)]] += c
        return out
        return out


def ceil_sqrt_rat(x: Fraction) -> Fraction:
    p, q = x.numerator, x.denominator
    s = math.isqrt(p * q)
    return Fraction(s if s * s == p * q else s + 1, q)


# ============================================================ 商装配（精确）
class QuotientMaps:
    """(3,3,3) S₃ 商 cut 构造的全部精确映射（Fraction 主本）。

    data dict 约定（认证/求解共用）：
      h_AA, h_AB, psi_AA, psi_AB：一元系数（长 d_H+1）
      e, c_A, c_B, c_C：标量；F：list of K 个对称方阵（尺寸 M−k）
      B_<orbit>_<name>：SOS Gram；sig_<cls>_<name>：minorant Gram
    """

    SLOT_SHARES = {          # (LP 一元部分, gm 系数)：share 的完整描述
        "AA_in": ("psi_AA", F1, F0),
        "AA_out": ("mix_AA", F1, Fraction(-1, 3)),      # (h_AA − ψ_AA)/6 − gm/3
        "AB_in": ("psi_AB", F1, F0),
        "AB_out": ("mix_AB", F1, Fraction(-2, 3)),      # (h_AB − 4ψ_AB)/3 − 2gm/3
    }

    def __init__(self, lo: Fraction, M: int, K: int):
        self.lo, self.M, self.K = lo, M, K
        self.D = self.d_H = 2 * M - 2
        self.ring = FRing(self.D)
        ring = self.ring
        self.nmon = ring.nmon
        self.F_sizes = [M - k for k in range(K)]

        # ---- Q_k（递推；与 sdp_bound.build_Q 逐系数对拍 + (u,v) 对称自检）----
        t_m_uv = [x - y for x, y in zip(ring.mono((0, 0, 1)), ring.mono((1, 1, 0)))]
        om = [x + y for x, y in zip(
            [x - y for x, y in zip(
                [x - y for x, y in zip(ring.mono((0, 0, 0)), ring.mono((2, 0, 0)))],
                ring.mono((0, 2, 0)))], ring.mono((2, 2, 0)))]
        Qs = [ring.mono((0, 0, 0)), t_m_uv]
        while len(Qs) < K:
            prev1 = [2 * x for x in ring.mul(t_m_uv, Qs[-1])]
            prev2 = ring.mul(om, Qs[-2])
            Qs.append([x - y for x, y in zip(prev1, prev2)])
        self.Qs = Qs[:K]
        for k, Q in enumerate(self.Qs):
            a = ring.eval3(Q, Fraction(1, 3), Fraction(2, 5), Fraction(-1, 7))
            b = ring.eval3(Q, Fraction(2, 5), Fraction(1, 3), Fraction(-1, 7))
            assert a == b, f"Q_{k} 不对称于 (u,v)"
        Qf = sdp_bound.build_Q(sdp_bound.Poly3(self.D), K)
        for k in range(K):
            for p in range(self.nmon):
                assert float(self.Qs[k][p]) == Qf[k][p], f"Q_{k} 对拍失败"

        # ---- 核列 Y（未对称化）与其换位、gm、D_T 列 ----
        self.Y_cols, self.Y_index = [], {}
        for k in range(K):
            for a_ in range(M - k):
                for b_ in range(M - k):
                    self.Y_index[(k, a_, b_)] = len(self.Y_cols)
                    self.Y_cols.append(ring.mul(ring.mono((a_, b_, 0)), Qs[k]))
        self.col_kab = [None] * len(self.Y_cols)
        for kab, i in self.Y_index.items():
            self.col_kab[i] = kab
        self.Y3_cols = [ring.perm(c, 3) for c in self.Y_cols]     # p(u,t,v)
        self.Y5_cols = [ring.perm(c, 5) for c in self.Y_cols]     # p(v,t,u)

        def subst_keep(vec, keep):
            out = ring.zero()
            for p, c in enumerate(vec):
                if c == 0:
                    continue
                i, j, l = ring.mons[p]
                d = (i if keep[0] else 0) + (j if keep[1] else 0) + (l if keep[2] else 0)
                out[ring.index[(d, 0, 0)]] += c
            return out

        self.gm_cols = [[x + y for x, y in zip(
            [x + y for x, y in zip(subst_keep(Y, (False, True, True)),
                                   subst_keep(Y, (True, False, True)))],
            subst_keep(Y, (True, True, False)))] for Y in self.Y_cols]
        # D_T 的 F 列（三轨道共用）：−2(Y + Y^{(u,t,v)} + Y^{(v,t,u)})
        self.K_cols = [[-2 * (a + b + c) for a, b, c in zip(Y, Y3, Y5)]
                       for Y, Y3, Y5 in zip(self.Y_cols, self.Y3_cols, self.Y5_cols)]

        # ---- λ 轨道描述：三槽 share 键 + 常数变量 ----
        self.lam_spec = {
            "AAA": (("AA_in", "AA_in", "AA_in"), "c_A"),
            "AAB": (("AA_out", "AB_in", "AB_in"), "c_B"),
            "ABC": (("AB_out", "AB_out", "AB_out"), "c_C"),
        }
        self.counts = {"AAA": 1, "AAB": 9, "ABC": 27}     # 每类计数
        self.class_counts = {"AAA": 3, "AAB": 6, "ABC": 1}
        self.nrm = {"c_A": Fraction(3), "c_B": Fraction(54),
                    "c_C": Fraction(27), "e": Fraction(-1)}
        self.s111_factor = 9                                # Σ_X n_X·s_X(1,1,1)

        # ---- SOS 块族（cut 域乘子；与 typed/solve._sos_blocks_for 一致）----
        def mons_upto(dmax):
            return [e for e in ring.mons if sum(e) <= dmax]

        detG = [((0, 0, 0), F1), ((1, 1, 1), Fraction(2)), ((2, 0, 0), Fraction(-1)),
                ((0, 2, 0), Fraction(-1)), ((0, 0, 2), Fraction(-1))]
        self.sos_def = [("1", [((0, 0, 0), F1)], mons_upto(self.D // 2))]
        for slot in range(3):
            ue = (1 if s == slot else 0 for s in range(3))
            ue = tuple(ue)
            blocks_cut = [((0, 0, 0), -lo), (ue, F1)]
            self.sos_def.append((f"{'uvt'[slot]}-lo", blocks_cut, mons_upto((self.D - 1) // 2)))
        for slot in range(3):
            ue = tuple(1 if s == slot else 0 for s in range(3))
            self.sos_def.append((f"1-{'uvt'[slot]}",
                                 [((0, 0, 0), F1), (ue, Fraction(-1))],
                                 mons_upto((self.D - 1) // 2)))
        self.sos_def.append(("detG", detG, mons_upto((self.D - 3) // 2)))

        # ---- minorant（cut：一侧 [lo,1)，Lukács）----
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
        self.pair_classes = ["AA", "AB"]
        self.h_of = {"AA": "h_AA", "AB": "h_AB"}
        self.pair_count = {"AA": 9, "AB": 27}

        # ---- 全 10 类结构（展开核对用）：类 → (轨道, 槽置换 id/ut) ----
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
        # 全类 share 键（一般公式的槽描述，用于逐系数核对与恒等式自检）
        self.full_share_keys = {}
        for (cls, orbit, perm_id) in self.full_classes:
            X, Y, Z = cls

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

            self.full_share_keys[cls] = (
                share_key(X, Y, Z), share_key(X, Z, Y), share_key(Y, Z, X))

    # ---------------- λ / SOS / minorant 装配 ----------------
    def share_lp(self, key, data):
        """share 的一元 LP 部分（h/ψ 组合；gm 部分由 GM_OF 表達）。

        键归一化：AA_inX→AA_in（ψ_AA）；AB_inX/AB_inY→AB_in（S₃ 不变：
        ψ^{AB,inX} = ψ^{AB,inY} = ψ_AB）；*_out 为残差份额。"""
        if key in ("AA_inX", "AA_in"):
            return list(data["psi_AA"])
        if key in ("AB_inX", "AB_inY", "AB_in"):
            return list(data["psi_AB"])
        if key == "AA_out":
            return [(hh - pp) / 6 for hh, pp in zip(data["h_AA"], data["psi_AA"])]
        if key == "AB_out":
            return [(hh - 4 * pp) / 3 for hh, pp in zip(data["h_AB"], data["psi_AB"])]
        raise KeyError(key)

    GM_OF = {"AA_in": F0, "AA_out": Fraction(-1, 3), "AA_inX": F0,
             "AB_in": F0, "AB_out": Fraction(-2, 3),
             "AB_inX": F0, "AB_inY": F0}

    def lam(self, orbit: str, data: dict) -> list[Fraction]:
        """data → λ_orbit 系数向量（份额 + c + D_T 全装配）。"""
        ring = self.ring
        out = ring.zero()
        keys, cvar = self.lam_spec[orbit]
        for slot in range(3):
            uni = self.share_lp(keys[slot], data)
            out = [x + y for x, y in zip(out, ring.uni_at_slot(uni, slot))]
        out[ring.index[(0, 0, 0)]] -= data[cvar]
        for idx in range(len(self.Y_cols)):
            k, a_, b_ = self.col_kab[idx]
            c = data["F"][k][a_][b_]
            if c == 0:
                continue
            col = list(self.K_cols[idx])
            for slot in range(3):
                g = self.GM_OF[keys[slot]]
                if g:
                    col = [x + g * y for x, y in zip(
                        col, ring.lift_slot0(self.gm_cols[idx], slot))]
            out = [x + c * y for x, y in zip(out, col)]
        return out

    def full_lam(self, cls, data: dict) -> list[Fraction]:
        """全类 (X,Y,Z) 的 λ（一般公式，独立实现，用于逐系数核对）。"""
        ring = self.ring
        keys = self.full_share_keys[cls]
        orbit = next(o for (c, o, _p) in self.full_classes if c == cls)
        _, cvar = self.lam_spec[orbit]
        out = ring.zero()
        for slot in range(3):
            uni = self.share_lp(keys[slot], data)
            out = [x + y for x, y in zip(out, ring.uni_at_slot(uni, slot))]
        out[ring.index[(0, 0, 0)]] -= data[cvar]
        for idx in range(len(self.Y_cols)):
            k, a_, b_ = self.col_kab[idx]
            c = data["F"][k][a_][b_]
            if c == 0:
                continue
            col = list(self.K_cols[idx])
            for slot in range(3):
                g = self.GM_OF[keys[slot]]
                if g:
                    col = [x + g * y for x, y in zip(
                        col, ring.lift_slot0(self.gm_cols[idx], slot))]
            out = [x + c * y for x, y in zip(out, col)]
        return out

    def sos_sum(self, Bblocks: dict) -> list[Fraction]:
        ring = self.ring
        out = ring.zero()
        for name, gnz, mons in self.sos_def:
            B = Bblocks[name]
            m = len(mons)
            for p_ in range(m):
                ep = mons[p_]
                row = B[p_]
                for q_ in range(m):
                    c = row[q_]
                    if c == 0:
                        continue
                    eq = mons[q_]
                    base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                    for (eg, cg) in gnz:
                        out[ring.index[(base[0] + eg[0], base[1] + eg[1],
                                        base[2] + eg[2])]] += c * cg
        return out

    def minorant_rhs(self, h: list[Fraction]) -> list[Fraction]:
        return [sum(self.Cp[r][j] * h[j] for j in range(self.d_H + 1))
                + self.p_const[r] for r in range(self.deg_p + 1)]

    def minorant_lhs(self, Sblocks: dict) -> list[Fraction]:
        out = [F0] * (self.deg_p + 1)
        for name, mons_y, mult in self.sig_def:
            S = Sblocks[name]
            m = len(mons_y)
            for p_ in range(m):
                row = S[p_]
                for q_ in range(m):
                    c = row[q_]
                    if c == 0:
                        continue
                    base = mons_y[p_] + mons_y[q_]
                    for (eg, cg) in mult:
                        out[base + eg] += c * cg
        return out

    def s_forms(self, data: dict):
        """s（= Σ_k⟨F^k,Y_k⟩）的 Poly3 系数向量与 s(1,1,1)。"""
        ring = self.ring
        vec = ring.zero()
        for idx in range(len(self.Y_cols)):
            k, a_, b_ = self.col_kab[idx]
            c = data["F"][k][a_][b_]
            if c:
                vec = [x + c * y for x, y in zip(vec, self.Y_cols[idx])]
        s111 = sum(sum(row) for row in data["F"][0])
        return vec, s111

    def gm_uni(self, data: dict) -> list[Fraction]:
        """gm（一元，d_H+1 系数）。"""
        out = [F0] * (self.d_H + 1)
        for idx in range(len(self.Y_cols)):
            k, a_, b_ = self.col_kab[idx]
            c = data["F"][k][a_][b_]
            if c:
                gc = self.gm_cols[idx]
                for d in range(self.d_H + 1):
                    if gc[self.ring.index[(d, 0, 0)]]:
                        out[d] += c * gc[self.ring.index[(d, 0, 0)]]
        return out


# ============================================================ 精确自检
def random_dyadic_data(qm: QuotientMaps, rng, scale_bits=10):
    """随机有理数据（h/ψ/c/e 随机、F 每 k 随机 PSD、归一化精确重算 c_C）。"""
    d_H = qm.d_H
    data = dict(
        h_AA=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
              for _ in range(d_H + 1)],
        h_AB=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
              for _ in range(d_H + 1)],
        psi_AA=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
                for _ in range(d_H + 1)],
        psi_AB=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
                for _ in range(d_H + 1)],
        e=Fraction(rng.randint(20 << 8, 30 << 8), 1 << 8),
        c_A=Fraction(rng.randint(-8, 8), 4),
        c_B=Fraction(rng.randint(-8, 8), 4),
        F=[],
    )
    for k, mk in enumerate(qm.F_sizes):
        G = [[Fraction(rng.randint(-8, 8), 4) for _ in range(mk)] for _ in range(mk)]
        data["F"].append([[sum(G[i][t] * G[j][t] for t in range(mk)) for j in range(mk)]
                          for i in range(mk)])
    s111 = sum(sum(row) for row in data["F"][0])
    data["c_C"] = (data["e"] + qm.s111_factor * s111
                   - qm.nrm["c_A"] * data["c_A"] - qm.nrm["c_B"] * data["c_B"]) / qm.nrm["c_C"]
    return data


def random_rational_config(rng, n):
    return [rational_point(Fraction(rng.randint(-1 << 6, 1 << 6), 1 << 6),
                           Fraction(rng.randint(-1 << 6, 1 << 6), 1 << 6))
            for _ in range(n)]


def exact_identity_selftest(qm: QuotientMaps, rng, trials=2):
    """typed 恒等式（全类展开形式）：Σ_T λ_T + Σ_all = Σ_{i<j}H_cls − e 于随机
    有理 config × 随机数据（全 Fraction，== 0 精确比对）。Σ_T 对全部 84 个无序
    三点按类锚定求值（full_lam 一般公式）；Σ_all 直接逐有序三点求值。"""
    ring = qm.ring
    results = []
    types = [0] * 3 + [1] * 3 + [2] * 3
    from itertools import combinations
    for _ in range(trials):
        data = random_dyadic_data(qm, rng)
        X = random_rational_config(rng, N)
        G = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        s_vec, _s111 = qm.s_forms(data)
        sum_all = F0
        for i in range(N):
            for j in range(N):
                for l in range(N):
                    sum_all += ring.eval3(s_vec, G[i][j], G[i][l], G[j][l])
        lam_vecs = {cls: qm.full_lam(cls, data) for (cls, _o, _p) in qm.full_classes}
        sum_lam = F0
        for (i, j, l) in combinations(range(N), 3):
            tt = sorted([(types[i], i), (types[j], j), (types[l], l)])
            (_r0, i0), (_r1, j0), (_r2, l0) = tt
            cls = tuple(x[0] for x in tt)
            sum_lam += ring.eval3(lam_vecs[cls], G[i0][j0], G[i0][l0], G[j0][l0])
        sum_H = F0
        for i in range(N):
            for j in range(i + 1, N):
                cls = "AA" if types[i] == types[j] else "AB"
                sum_H += ring.eval1(data[qm.h_of[cls]], G[i][j])
        lhs, rhs = sum_lam + sum_all, sum_H - data["e"]
        results.append(dict(diff=str(lhs - rhs), ok=bool(lhs == rhs)))
        assert lhs == rhs, f"typed 恒等式失败：{lhs} != {rhs}"
    return dict(trials=results, ok=True)


def exact_orbit_perm_selftest(qm: QuotientMaps, rng, trials=2):
    """全 10 类：λ_full(cls) == λ_orbit ∘ P_cls（逐系数精确；P=id 或 u↔t）。"""
    ring = qm.ring
    for _ in range(trials):
        data = random_dyadic_data(qm, rng)
        lam_orbit = {o: qm.lam(o, data) for o in ("AAA", "AAB", "ABC")}
        for (cls, orbit, perm_id) in qm.full_classes:
            lf = qm.full_lam(cls, data)
            lo_ = lam_orbit[orbit]
            ref = lo_ if perm_id == "id" else ring.swap_ut(lo_)
            assert lf == ref, f"类 {cls} 的 λ_full ≠ λ_{orbit}∘{perm_id}"
    return dict(ok=True, classes=10)


def exact_positivity_selftest(qm: QuotientMaps, rng, trials=1):
    """引理 4.1 分型正性：Σ_{i,j,l} s_{type(i)} ≥ 0（随机 PSD F、随机有理 config）。"""
    ring = qm.ring
    for _ in range(trials):
        data = random_dyadic_data(qm, rng)
        X = random_rational_config(rng, N)
        G = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        s_vec, _ = qm.s_forms(data)
        tot = F0
        for i in range(N):
            for j in range(N):
                for l in range(N):
                    tot += ring.eval3(s_vec, G[i][j], G[i][l], G[j][l])
        assert tot >= 0, f"分型正性失败：Σ_all = {tot}"
    return dict(ok=True)


def perm_direction_selftest(qm: QuotientMaps):
    """FRing.perm 方向复核：p = t−uv 时 perm(3) = v−ut = p(u,t,v)、
    perm(5) = u−vt = p(v,t,u)（typed/core.py 同约定）。"""
    ring = qm.ring
    p = [x - y for x, y in zip(ring.mono((0, 0, 1)), ring.mono((1, 1, 0)))]
    p3, p5 = ring.perm(p, 3), ring.perm(p, 5)
    exp3 = [x - y for x, y in zip(ring.mono((0, 1, 0)), ring.mono((1, 0, 1)))]
    exp5 = [x - y for x, y in zip(ring.mono((1, 0, 0)), ring.mono((0, 1, 1)))]
    assert p3 == exp3 and p5 == exp5, "perm 方向与 typed/core.py 不一致"
    return dict(ok=True)


def run_selftests(M=6, K=6, lo=Fraction(-9, 10)):
    t0 = time.time()
    qm = QuotientMaps(lo, M, K)
    rng = random.Random(SEED)
    out = dict(
        perm_direction=perm_direction_selftest(qm),
        identity=exact_identity_selftest(qm, rng, trials=2),
        orbit_perm=exact_orbit_perm_selftest(qm, rng, trials=2),
        positivity=exact_positivity_selftest(qm, rng, trials=1),
        sizes=dict(nmon=qm.nmon, d_H=qm.d_H, deg_p=qm.deg_p,
                   rows_total=3 * qm.nmon + 2 * (qm.deg_p + 1) + 1,
                   n_lp=1 + 8 * (qm.d_H + 1) + 6),
        runtime_s=round(time.time() - t0, 1),
    )
    print(f"[selftest] 全过（{out['runtime_s']}s）：identity/orbit_perm/positivity/"
          f"perm_direction ✓  nmon={qm.nmon} rows={out['sizes']['rows_total']}")
    return out


# ============================================================ SDPA 导出
def frac_dec(f: Fraction, digits: int = 40) -> str:
    num, den = f.numerator, f.denominator
    sign = "-" if num < 0 else ""
    num = abs(num)
    ip, rem = divmod(num, den)
    out = []
    for _ in range(digits):
        if rem == 0:
            break
        rem *= 10
        d, rem = divmod(rem, den)
        out.append(str(d))
    if not out:
        return f"{sign}{ip}.0"
    return f"{sign}{ip}.{''.join(out)}"


class SDPAExporter:
    """商 SDP → SDPA sparse .dat-s（块布局与解回读的单一事实源）。

    行：3·nmon（slack，b=0）+ 2·(deg_p+1)（minorant，b=p_const）+ 1（归一化，b=0）。
    块：LP 对角（e；h/ψ/c ± 拆分）+ F×K + SOS×3×8 + σ×2×4。
    约定（hp_solve.py 经 Clarabel 代入逐条校验）：非对角 (i<j) 存裸系数，
    SDPA 按 2·X_ij 计入；F 块系数对称化 (W_ab+W_ba)/2；LP 块非负（实测）。
    """

    def __init__(self, qm: QuotientMaps, lp_penalty=Fraction(1, 10 ** 11)):
        self.qm = qm
        self.lp_penalty = lp_penalty
        d_H1 = qm.d_H + 1
        pos = 1
        self.e_pos = 1
        pos += 1
        self.vpos = {}
        for name in ("h_AA", "h_AB", "psi_AA", "psi_AB"):
            self.vpos[name] = (pos, pos + d_H1)
            pos += 2 * d_H1
        for name in ("c_A", "c_B", "c_C"):
            self.vpos[name] = (pos, pos + 1)
            pos += 2
        self.n_lp = pos - 1                            # 已用位置数
        self.blk = ([-self.n_lp] + list(qm.F_sizes)
                    + [len(m) for _n, _g, m in qm.sos_def] * 3
                    + [len(m) for _n, m, _mu in qm.sig_def] * 2)
        self.f_off = 2                                   # 块 1 = LP
        self.sos_off = self.f_off + len(qm.F_sizes)
        self.sig_off = self.sos_off + 3 * len(qm.sos_def)
        self.orbit_row = {o: i * qm.nmon + 1 for i, o in enumerate(("AAA", "AAB", "ABC"))}
        self.minor_row = {"AA": 3 * qm.nmon + 1, "AB": 3 * qm.nmon + qm.deg_p + 2}
        self.row_norm = 3 * qm.nmon + 2 * (qm.deg_p + 1) + 1
        self.m = self.row_norm

    def build_entries(self):
        """全部行条目，(k,l,i,j) 累加去重（SDPA 不合并重复条目）。"""
        acc: dict = {}

        def put(k, l, i, j, v):
            if v:
                acc[(k, l, i, j)] = acc.get((k, l, i, j), F0) + v

        for orbit in ("AAA", "AAB", "ABC"):
            for (k, l, i, j, v) in self._slack_rows(orbit):
                put(k, l, i, j, v)
        for cls in ("AA", "AB"):
            for (k, l, i, j, v) in self._minor_rows(cls):
                put(k, l, i, j, v)
        for (k, l, i, j, v) in self._norm_rows():
            put(k, l, i, j, v)
        put(0, 1, self.e_pos, self.e_pos, F1)            # 目标 max e
        # LP ± 拆分的零空间锚定：对全部 ⁺/⁻ 槽加 −ε 罚（ε=1e-11）。
        # 解问题的 max(e − εΣ±)；读回的 e⁺ 满足原始行 ⟹ 认证零损失；
        # 最优 e 至多低 ε·Σ|±|（~1e-8），换掉精确零空间方向（(7,6) 上
        # SDPA-GMP 曾因它在 iter 34 原始目标跑飞到 26.3 后 dFEAS 崩溃）。
        if self.lp_penalty:
            eps = self.lp_penalty
            for (pp, mm) in self.vpos.values():
                n_here = (mm - pp + 1) // 2
                for d in range(n_here):
                    put(0, 1, pp + d, pp + d, -eps)
                    put(0, 1, mm + d, mm + d, -eps)
        return [(k, l, i, j, v) for (k, l, i, j), v in acc.items()]

    def _slack_rows(self, orbit):
        qm, ring = self.qm, self.qm.ring
        E = []
        row0 = self.orbit_row[orbit]
        keys, cvar = qm.lam_spec[orbit]
        d_H1 = qm.d_H + 1

        def uni_add(slot, name, num, den=F1):
            pp, mm = self.vpos[name]
            v = Fraction(num, den)
            for d in range(d_H1):
                e = [0, 0, 0]
                e[slot] = d
                r = row0 + ring.index[tuple(e)]
                E.append((r, 1, pp + d, pp + d, v))
                E.append((r, 1, mm + d, mm + d, -v))

        def sca_add(name, num, den=F1):
            pp, mm = self.vpos[name]
            r = row0 + ring.index[(0, 0, 0)]
            v = Fraction(num, den)
            E.append((r, 1, pp, pp, v))
            E.append((r, 1, mm, mm, -v))

        if orbit == "AAA":
            for slot in range(3):
                uni_add(slot, "psi_AA", 1)
            sca_add("c_A", -1)
        elif orbit == "AAB":
            uni_add(0, "h_AA", 1, 6)
            uni_add(0, "psi_AA", -1, 6)
            uni_add(1, "psi_AB", 1)
            uni_add(2, "psi_AB", 1)
            sca_add("c_B", -1)
        else:
            for slot in range(3):
                uni_add(slot, "h_AB", 1, 3)
                uni_add(slot, "psi_AB", -4, 3)
            sca_add("c_C", -1)
        # F 侧：列 = K_cols[idx] + Σ_slot GM_OF·gm@slot；(a<b) 对称化 (W+Wᵀ)/2
        for idx in range(len(qm.Y_cols)):
            k, a_, b_ = qm.col_kab[idx]
            l = self.f_off + k
            col = self._f_col(orbit, keys, idx)
            if a_ == b_:
                for p, c in enumerate(col):
                    if c:
                        E.append((row0 + p, l, a_ + 1, a_ + 1, c))
            elif a_ < b_:
                colT = self._f_col(orbit, keys, qm.Y_index[(k, b_, a_)])
                sym = [(x + y) / 2 for x, y in zip(col, colT)]
                for p, c in enumerate(sym):
                    if c:
                        E.append((row0 + p, l, a_ + 1, b_ + 1, c))
        # SOS 侧：−Σ_r g_r·z_rᵀB_rz_r（p≤q 裸系数；行 = slack 恒等式移项后 −cg）
        oi = ("AAA", "AAB", "ABC").index(orbit)
        for bi, (name, gnz, mons) in enumerate(qm.sos_def):
            l = self.sos_off + oi * len(qm.sos_def) + bi
            m_ = len(mons)
            for p_ in range(m_):
                ep = mons[p_]
                for q_ in range(p_, m_):
                    eq = mons[q_]
                    base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                    for (eg, cg) in gnz:
                        r = row0 + ring.index[(base[0] + eg[0], base[1] + eg[1],
                                               base[2] + eg[2])]
                        E.append((r, l, p_ + 1, q_ + 1, -cg))
        return E

    def _f_col(self, orbit, keys, idx):
        """λ_orbit 的 F 列（含 share 的 gm 附加）。"""
        qm, ring = self.qm, self.qm.ring
        col = list(qm.K_cols[idx])
        for slot in range(3):
            g = qm.GM_OF[keys[slot]]
            if g:
                col = [x + g * y for x, y in zip(
                    col, ring.lift_slot0(qm.gm_cols[idx], slot))]
        return col

    def _minor_rows(self, cls):
        qm = self.qm
        E = []
        row0 = self.minor_row[cls]
        pp, mm = self.vpos[qm.h_of[cls]]
        d_H1 = qm.d_H + 1
        for bi, (name, mons_y, mult) in enumerate(qm.sig_def):
            l = self.sig_off + (0 if cls == "AA" else len(qm.sig_def)) + bi
            m_ = len(mons_y)
            for p_ in range(m_):
                for q_ in range(p_, m_):
                    base = mons_y[p_] + mons_y[q_]
                    for (eg, cg) in mult:
                        E.append((row0 + base + eg, l, p_ + 1, q_ + 1, cg))
        for r in range(qm.deg_p + 1):
            for j in range(d_H1):
                v = qm.Cp[r][j]
                if v:
                    E.append((row0 + r, 1, pp + j, pp + j, -v))
                    E.append((row0 + r, 1, mm + j, mm + j, v))
        return E

    def _norm_rows(self):
        qm = self.qm
        E = []
        r = self.row_norm
        for name in ("c_A", "c_B", "c_C"):
            v = qm.nrm[name]
            pp, mm = self.vpos[name]
            E.append((r, 1, pp, pp, v))
            E.append((r, 1, mm, mm, -v))
        E.append((r, 1, self.e_pos, self.e_pos, qm.nrm["e"]))
        m0 = qm.F_sizes[0]
        l = self.f_off
        s111c = -Fraction(qm.s111_factor)   # −9·Σ_{a,b}F_ab：对角 −9·X_aa，
        for a_ in range(m0):                # 非对角条目 v 满足 2v·X_ab = −18·X_ab → v = −9
            for b_ in range(m0):
                E.append((r, l, a_ + 1, b_ + 1, s111c))
        return E

    def b_vector(self):
        qm = self.qm
        b = [F0] * self.m
        for cls in ("AA", "AB"):
            row0 = self.minor_row[cls]
            for r in range(qm.deg_p + 1):
                b[row0 - 1 + r] = qm.p_const[r]
        return b

    def write_dat(self, path: Path):
        E = self.build_entries()
        b = self.b_vector()
        with open(path, "w") as f:
            f.write('"N=9 typed (3,3,3) S3-quotient cap SDP (exact rational coefficients)"\n')
            f.write(f"{self.m} = mDIM\n{len(self.blk)} = nBLOCK\n")
            f.write(" ".join(str(s) for s in self.blk) + " = bLOCKsTRUCT\n")
            f.write(" ".join(frac_dec(x) for x in b) + "\n")
            for (k, l, i, j, v) in E:
                f.write(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        return self.m, len(E)



# ============================================================ .result 解析与回读
def parse_result(path: Path) -> dict:
    """sdpa_gmp .result：统计 + yMat（REVERSE_PRIMAL_DUAL build：我们的 X 在 yMat）。"""
    text = path.read_text()

    def grab(pat, flags=0):
        m = re.search(pat, text, flags)
        return m.group(1) if m else None

    info = dict(
        phase_value=grab(r"phase\.value = (\S+)"),
        iteration=int(grab(r"Iteration = (\d+)") or -1),
        mu=float(grab(r"mu = ([0-9.eE+-]+)") or "nan"),
        relative_gap=float(grab(r"relative gap = ([0-9.eE+-]+)") or "nan"),
        p_feas_error=grab(r"p\.feas\.error = ([0-9.eE+-]+)"),
        d_feas_error=grab(r"d\.feas\.error = ([0-9.eE+-]+)"),
        obj_primal=grab(r"objValPrimal = ([0-9.eE+-]+)"),
        obj_dual=grab(r"objValDual = ([0-9.eE+-]+)"),
    )
    mm = re.search(r"yMat = \s*\n\{\n(.*)\n\}", text, re.S)
    if mm is None:
        fail("yMat 段未找到")
    body = mm.group(1)
    groups, depth, start = [], 0, None
    for idx, ch in enumerate(body):
        if ch == "{":
            if depth == 0:
                start = idx
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(body[start:idx + 1])
                start = None
    if not groups:
        fail("yMat 顶层组扫描为空")
    lp_str = groups[0]
    if "{" in lp_str[1:-1]:
        fail("首组不是 LP 平铺块")
    lp_vals = [s for s in re.split(r"[{},\s]+", lp_str[1:-1]) if s]
    sdp = []
    for g in groups[1:]:
        rows = re.findall(r"\{([^{}]*)\}", g)
        if not rows:
            fail("SDP 组内未找到行")
        sdp.append([[x for x in re.split(r"[,\s]+", r_) if x] for r_ in rows])
    return dict(info=info, lp=[Fraction(s) for s in lp_vals], sdp=sdp)


def solution_from_parse(ex: SDPAExporter, parsed: dict, E_limit: Fraction) -> dict:
    """yMat → 商数据 dict（Fraction）＋ e 封顶。"""
    qm = ex.qm
    lp = parsed["lp"]
    if len(lp) != ex.n_lp:
        fail(f"LP 块长度 {len(lp)} ≠ {ex.n_lp}")
    d_H1 = qm.d_H + 1

    def split_get(name):
        pp, mm_ = ex.vpos[name]
        return [lp[pp - 1 + d] - lp[mm_ - 1 + d] for d in range(d_H1)] \
            if name in ("h_AA", "h_AB", "psi_AA", "psi_AB") else lp[pp - 1] - lp[mm_ - 1]

    e_raw = lp[ex.e_pos - 1]
    data = dict(h_AA=split_get("h_AA"), h_AB=split_get("h_AB"),
                psi_AA=split_get("psi_AA"), psi_AB=split_get("psi_AB"),
                c_A=split_get("c_A"), c_B=split_get("c_B"), c_C=split_get("c_C"),
                e=e_raw)
    mats = []
    for g in parsed["sdp"]:
        n = len(g)
        if any(len(r) != n for r in g):
            fail("SDP 块非方阵")
        mats.append([[Fraction(x) for x in r] for r in g])
    n_expect = len(qm.F_sizes) + 3 * len(qm.sos_def) + 2 * len(qm.sig_def)
    if len(mats) != n_expect:
        fail(f"SDP 块数 {len(mats)} ≠ {n_expect}")
    off = 0
    F = mats[off:off + len(qm.F_sizes)]
    for kk, m_ in enumerate(F):
        if len(m_) != qm.F_sizes[kk]:
            fail(f"F{kk} 尺寸不符")
    data["F"] = F
    off += len(qm.F_sizes)
    B = {}
    for oi, orbit in enumerate(("AAA", "AAB", "ABC")):
        for bi, (name, _g, mons) in enumerate(qm.sos_def):
            m_ = mats[off]
            if len(m_) != len(mons):
                fail(f"B_{orbit}_{name} 尺寸不符")
            B[f"{orbit}_{name}"] = m_
            off += 1
    data["B"] = B
    sig = {}
    for ci, cls in enumerate(("AA", "AB")):
        for bi, (name, mons_y, _mu) in enumerate(qm.sig_def):
            m_ = mats[off]
            if len(m_) != len(mons_y):
                fail(f"sig_{cls}_{name} 尺寸不符")
            sig[f"{cls}_{name}"] = m_
            off += 1
    data["sig"] = sig
    e_cap = E_limit - Fraction(2, 10 ** 5)
    capped = None
    if e_raw > e_cap:
        data["e"] = e_cap
        capped = dict(e_raw=str(e_raw), e_used=str(e_cap))
    data["_e_capped"] = capped
    return data


def raw_residuals(qm: QuotientMaps, data: dict) -> dict:
    """未舍入解的精确恒等式残差（对照用）。"""
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"]
                         for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    R2 = {}
    for cls in ("AA", "AB"):
        lhs = qm.minorant_lhs({nm: data["sig"][f"{cls}_{nm}"]
                               for (nm, _my, _mu) in qm.sig_def})
        rhs = qm.minorant_rhs(data[qm.h_of[cls]])
        rr = [x - y for x, y in zip(rhs, lhs)]
        R2[cls] = sum(abs(rr[j]) * qm.w_hat ** j for j in range(len(rr)))
    nrm_resid = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
                 + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
                 - Fraction(qm.s111_factor) * sum(sum(r) for r in data["F"][0]))
    return dict(R1=R1, R2=R2, norm_resid=nrm_resid)


# ============================================================ 求解
def solve_rung(a0: Fraction, M: int, K: int, sdpa_bin: Path, workroot: Path,
               timeout_s=172800):
    """timeout 21600→172800（D20）：M9 外推 ~9h（M8 11793s × ~2.8），超旧 6h
    上限会杀健康求解；求解纪律不变（外部后台进程＋轮询，单命令 ≤10 分钟）。"""
    """导出 + SDPA-GMP 求解 + 回读落盘。返回 (solution_path, solve_info)。"""
    tag = rung_tag(a0)
    qm = QuotientMaps(a0, M, K)
    ex = SDPAExporter(qm)
    workdir = workroot / f"{tag}_M{M}"
    workdir.mkdir(parents=True, exist_ok=True)
    dat = workdir / "typed_cap.dat-s"
    if dat.exists():
        dat.unlink()
    m_dim, n_entries = ex.write_dat(dat)
    param = workdir / "param.sdpa"
    param.write_text(PARAM_SDPA)
    result = workdir / "typed_cap.result"
    sol_path = HERE / "results" / f"typed_ladder_sol_{tag}_M{M}.json"
    print(f"[export] {tag} M={M}: m={m_dim}, entries={n_entries}, blocks={len(ex.blk)} "
          f"(n_lp={ex.n_lp})", flush=True)
    cmd = [str(sdpa_bin), "-ds", str(dat), "-o", str(result), "-p", str(param)]
    reused = False
    parsed = None
    if result.exists():
        try:
            cand = parse_result(result)
            if cand["info"]["phase_value"] == "pdOPT":
                reused, parsed = True, cand
        except SystemExit:
            pass
    if reused:
        info = parsed["info"]
        print(f"[solve] {tag}: 复用已有 pdOPT 结果 {result}", flush=True)
        solve_s = 0.0
    else:
        if result.exists():
            result.unlink()
        print(f"[solve] {tag}: {' '.join(cmd)}", flush=True)
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              cwd=str(workdir), timeout=timeout_s)
        solve_s = time.time() - t0
        if proc.returncode != 0 or not result.exists():
            fail(f"{tag}: sdpa_gmp 退出码 {proc.returncode}："
                 f"{proc.stdout[-1500:]} {proc.stderr[-1500:]}")
        parsed = parse_result(result)
        info = parsed["info"]
    print(f"[solve] {tag}: phase={info['phase_value']} iter={info['iteration']} "
          f"mu={info['mu']:.2e} relgap={info['relative_gap']:.2e} "
          f"p.feas={info['p_feas_error']} d.feas={info['d_feas_error']} "
          f"({solve_s:.0f}s)", flush=True)
    if info["phase_value"] != "pdOPT":
        fail(f"{tag}: SDPA-GMP 未达 pdOPT：{info['phase_value']}")
    E_star = load_E_star()
    data = solution_from_parse(ex, parsed, E_star + PHI_TOL)
    rr = raw_residuals(qm, data)
    print(f"[resid] {tag}: e = {float(data['e']):.15f}；R1 = "
          f"{ {k: float(v) for k, v in rr['R1'].items()} }，R2 = "
          f"{ {k: float(v) for k, v in rr['R2'].items()} }，nrm = "
          f"{float(rr['norm_resid']):.2e}", flush=True)
    sol_js = dict(
        tag=tag, a0=str(a0), M=M, K=K,
        e=float(data["e"]),
        exact=dict(h_AA=[str(x) for x in data["h_AA"]],
                   h_AB=[str(x) for x in data["h_AB"]],
                   psi_AA=[str(x) for x in data["psi_AA"]],
                   psi_AB=[str(x) for x in data["psi_AB"]],
                   c_A=str(data["c_A"]), c_B=str(data["c_B"]), c_C=str(data["c_C"]),
                   e=str(data["e"]),
                   F=[[[str(x) for x in row] for row in m_] for m_ in data["F"]],
                   B={n: [[str(x) for x in row] for row in m_]
                      for n, m_ in data["B"].items()},
                   sig={n: [[str(x) for x in row] for row in m_]
                        for n, m_ in data["sig"].items()},
                   note="SDPA-GMP .result 66 位十进制精确回读的 Fraction"),
        solver_info=dict(route="SDPA-GMP 7.1.3 (GMP 200)", reused=bool(reused),
                         solve_s=round(solve_s, 1), lp_penalty=str(ex.lp_penalty),
                         **info),
        raw_residuals={k: ({kk: str(vv) for kk, vv in v.items()}
                           if isinstance(v, dict) else str(v))
                       for k, v in rr.items()},
        e_capped=data.pop("_e_capped"),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    sol_path.write_text(json.dumps(sol_js, ensure_ascii=False))
    print(f"[out] {tag}: 解数据 {sol_path.relative_to(REPO)}", flush=True)
    return sol_path, dict(sdpa_info=info, solve_s=round(solve_s, 1), reused=bool(reused),
                          m=m_dim, entries=n_entries)


# ============================================================ 认证
def certify(qm: QuotientMaps, sol: dict, k: int, tag: str, E_star: Fraction,
            min_bound: Fraction = F0, spot_seed: int = 97531):
    """一个 dyadic 粒度的完整认证链；断言失败 raise CertError。"""
    t0 = time.time()

    def rround(x):
        return dyad(x, k)

    def load_solution_exact():
        ex = sol["exact"]
        return dict(
            h_AA=[Fraction(s) for s in ex["h_AA"]], h_AB=[Fraction(s) for s in ex["h_AB"]],
            psi_AA=[Fraction(s) for s in ex["psi_AA"]],
            psi_AB=[Fraction(s) for s in ex["psi_AB"]],
            c_A=Fraction(ex["c_A"]), c_B=Fraction(ex["c_B"]), c_C=Fraction(ex["c_C"]),
            e=Fraction(ex["e"]),
            F=[[[Fraction(s) for s in row] for row in m_] for m_ in ex["F"]],
            B={n: [[Fraction(s) for s in row] for row in m_]
               for n, m_ in ex["B"].items()},
            sig={n: [[Fraction(s) for s in row] for row in m_]
                 for n, m_ in ex["sig"].items()})

    data = load_solution_exact()
    d_H = qm.d_H
    data_dy = dict(
        h_AA=[rround(x) for x in data["h_AA"]], h_AB=[rround(x) for x in data["h_AB"]],
        psi_AA=[rround(x) for x in data["psi_AA"]],
        psi_AB=[rround(x) for x in data["psi_AB"]],
        c_A=rround(data["c_A"]), c_B=rround(data["c_B"]),
        e=dyad(data["e"], k, floor=True), F=[])
    shifts = {}
    for kk, m_k in enumerate(qm.F_sizes):
        Mfr, dlt, _tries = repair_psd(f"F{kk}", [[rround(x) for x in row]
                                                  for row in data["F"][kk]], k)
        shifts[f"F{kk}"] = dlt
        data_dy["F"].append(Mfr)
    B_dy = {}
    for orbit in ("AAA", "AAB", "ABC"):
        for name, _g, _m in qm.sos_def:
            key = f"{orbit}_{name}"
            Mfr, dlt, _t = repair_psd(f"B_{key}", [[rround(x) for x in row]
                                                   for row in data["B"][key]], k)
            shifts[f"B_{key}"] = dlt
            B_dy[key] = Mfr
    sig_dy = {}
    for cls in ("AA", "AB"):
        for name, _my, _mu in qm.sig_def:
            key = f"{cls}_{name}"
            Mfr, dlt, _t = repair_psd(f"sig_{key}", [[rround(x) for x in row]
                                                     for row in data["sig"][key]], k)
            shifts[f"sig_{key}"] = dlt
            sig_dy[key] = Mfr
    # c_C 由归一化精确重算
    s111 = sum(sum(row) for row in data_dy["F"][0])
    data_dy["c_C"] = (data_dy["e"] + qm.s111_factor * s111
                      - qm.nrm["c_A"] * data_dy["c_A"]
                      - qm.nrm["c_B"] * data_dy["c_B"]) / qm.nrm["c_C"]

    # ---- 精确残差 ----
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data_dy)
        sv = qm.sos_sum({nm: B_dy[f"{orbit}_{nm}"]
                         for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    R2 = {}
    for cls in ("AA", "AB"):
        lhs = qm.minorant_lhs({nm: sig_dy[f"{cls}_{nm}"]
                               for (nm, _my, _mu) in qm.sig_def})
        rhs = qm.minorant_rhs(data_dy[qm.h_of[cls]])
        rr = [x - y for x, y in zip(rhs, lhs)]
        R2[cls] = sum(abs(rr[j]) * qm.w_hat ** j for j in range(len(rr)))
    defl = sum(qm.class_counts[o] * qm.counts[o] * R1[o] for o in R1)
    R2max = max(R2.values())
    e_dy = data_dy["e"]
    if e_dy - defl <= 0:
        raise CertError(f"[{tag}] e − defl ≤ 0")
    certified = (e_dy - defl) / (1 + R2max)

    # ---- 全 10 类逐系数核对（S₃ 展开的机器验证）----
    ring = qm.ring
    lam_orbit = {o: qm.lam(o, data_dy) for o in ("AAA", "AAB", "ABC")}
    for (cls, orbit, perm_id) in qm.full_classes:
        lf = qm.full_lam(cls, data_dy)
        ref = lam_orbit[orbit] if perm_id == "id" else ring.swap_ut(lam_orbit[orbit])
        if lf != ref:
            raise CertError(f"[{tag}] 类 {cls} 展开核对失败")

    # ---- 域抽查（有理点；SOS 乘子非负 + λ ≥ −R1）----
    rng = random.Random(spot_seed + k)
    lo = qm.lo
    for orbit in ("AAA", "AAB", "ABC"):
        lv = lam_orbit[orbit]
        ok_pts = 0
        tries = 0
        while tries < 300 and ok_pts < 8:
            tries += 1

            def rq(a, b):
                return a + (b - a) * Fraction(rng.randint(0, 64), 64)

            u, v, t = rq(lo, F1), rq(lo, F1), rq(lo, F1)
            detg = F1 + 2 * u * v * t - u * u - v * v - t * t
            if detg < 0:
                continue
            ok_pts += 1
            sos_pt = F0
            for name, gnz, mons in qm.sos_def:
                Bm = B_dy[f"{orbit}_{name}"]
                m_ = len(mons)
                zp = [(u ** e2[0]) * (v ** e2[1]) * (t ** e2[2]) for e2 in mons]
                quad = sum(Bm[p][q] * zp[p] * zp[q] for p in range(m_) for q in range(m_))
                g = sum(c * (u ** eg[0]) * (v ** eg[1]) * (t ** eg[2]) for eg, c in gnz)
                if g < 0:
                    raise CertError(f"[{tag}] 抽查乘子负值 g_{name} = {g}")
                sos_pt += g * quad
            if sos_pt < 0:
                raise CertError(f"[{tag}] SOS 抽查负值（{orbit}）")
            if ring.eval3(lv, u, v, t) + R1[orbit] < 0:
                raise CertError(f"[{tag}] λ_{orbit} 抽查 < −R1")
        if ok_pts == 0:
            raise CertError(f"[{tag}] λ_{orbit} 抽查未取到域内点")
    # minorant 抽查：(2−2t)·H² ≤ (1+R2)² 于 [lo,1) 有理点
    for cls in ("AA", "AB"):
        h = data_dy[qm.h_of[cls]]
        pts = [lo, (lo + F1) / 2, Fraction(-1, 2) if lo <= Fraction(-1, 2) else lo,
               Fraction(-3, 4) if lo <= Fraction(-3, 4) else lo, F0,
               Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(995, 1000)]
        for tp in pts:
            if not (lo <= tp < 1):
                continue
            Ht = ring.eval1(h, tp)
            if Ht <= 0:
                continue
            if (2 - 2 * tp) * Ht * Ht > (1 + R2[cls]) ** 2:
                raise CertError(f"[{tag}] minorant {cls} 抽查失败 @t={float(tp)}")

    # ---- 断言 ----
    if not (0 < certified <= E_star + PHI_TOL):
        raise CertError(f"[{tag}] certified = {float(certified):.15e} 违反 "
                        f"0 < c ≤ E*+1e-6（粒度 2^-{k}）")
    if certified <= min_bound:
        raise CertError(f"[{tag}] certified = {float(certified):.12f} ≤ 下限 "
                        f"{float(min_bound):.12f}（粒度 2^-{k}）")
    e_raw = Fraction(sol["exact"]["e"])
    if certified > e_raw + Fraction(1, 10 ** 9):
        raise CertError(f"[{tag}] certified > e + 1e-9（不可能）")
    print(f"[cert ] {tag}（2^-{k}）：certified = {float(certified):.12f}；"
          f"R1 = { {o2: float(R1[o2]) for o2 in R1} }，defl = {float(defl):.3e}，"
          f"R2max = {float(R2max):.3e}，认证链 {time.time() - t0:.0f}s", flush=True)
    return dict(data=data_dy, B=B_dy, sig=sig_dy, shifts=shifts, R1=R1, R2=R2,
                defl=defl, R2max=R2max, certified=certified, k=k)


class CertError(Exception):
    pass


def rung_tag(a0: Fraction) -> str:
    """−0.90→m090，−0.755→m0755（Round 2 命名约定；分母只含 2/5 因子）。"""
    digits = frac_dec(-a0).replace(".", "")
    while len(digits) < 3:
        digits += "0"
    return "m" + digits


# ============================================================ 证书
def write_certificate(qm: QuotientMaps, cert: dict, tag: str, a0: Fraction, M, K,
                      sol: dict, solve_info: dict, out_path: Path):
    data = cert["data"]

    def uni(name):
        return [str(x) for x in data[name]]

    blocks = {}
    for name in ("h_AA", "h_AB", "psi_AA", "psi_AB"):
        blocks[f"{name}_diag"] = uni(name)
    for name in ("e", "c_A", "c_B", "c_C"):
        blocks[name] = [str(data[name])]
    for kk, m_ in enumerate(data["F"]):
        blocks[f"F{kk}"] = [[str(x) for x in row] for row in m_]
    for key, m_ in cert["B"].items():
        blocks[f"B_{key}"] = [[str(x) for x in row] for row in m_]
    for key, m_ in cert["sig"].items():
        blocks[f"sig_{key}"] = [[str(x) for x in row] for row in m_]
    cert_js = dict(
        kind="n9-stage-a4-typedcap",
        tag=tag,
        params=dict(a0=str(a0), M=M, K=K, cover=f"min inner product >= {a0} "
                     f"({frac_dec(a0)})"),
        blocks=blocks,
        claimed_bound=str(cert["certified"]),
        provenance=dict(
            code_version=code_version(),
            construction=("typed 三点 (3,3,3) S₃ 商 cut 构造（typed/core.py 的精确"
                          "Fraction 实现；恒等式/正性/轨道展开自检见 selftest 段）"),
            counts=dict(triples={"AAA": "3x1", "AAB": "6x9", "ABC": "1x27"},
                        pairs={"AA": 9, "AB": 27},
                        normalization="3c_A+54c_B+27c_C = e+9·ΣF^(0)"),
            bound_formula="certified = (e − (3R1_AAA+54R1_AAB+27R1_ABC))/(1+max(R2_AA,R2_AB))",
            round_bits=cert["k"],
            psd_shifts={k2: str(v) for k2, v in cert["shifts"].items()},
            residuals=dict(R1={o: str(v) for o, v in cert["R1"].items()},
                           R2={c2: str(v) for c2, v in cert["R2"].items()},
                           defl=str(cert["defl"]), R2max=str(cert["R2max"])),
            solver=dict(route="SDPA-GMP 7.1.3 (GMP 200-digit)",
                        sdpa=solve_info.get("sdpa_info"),
                        reused=solve_info.get("reused")),
            solution_sha256_16=hashlib.sha256(
                json.dumps(sol["exact"], sort_keys=True).encode()).hexdigest()[:16],
            date=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        ),
    )
    out_path.write_text(json.dumps(cert_js, ensure_ascii=False, indent=1))
    return cert_js


def verify_cert_file(path: Path):
    """进程外独立复核：只读 JSON → 重建 → 精确重算 certified，逐位比对。"""
    cert = json.loads(path.read_text())
    prm = cert["params"]
    qm = QuotientMaps(Fraction(prm["a0"]), prm["M"], prm["K"])
    b = cert["blocks"]

    def uni(name):
        return [Fraction(x) for x in b[f"{name}_diag"]]

    data = dict(h_AA=uni("h_AA"), h_AB=uni("h_AB"), psi_AA=uni("psi_AA"),
                psi_AB=uni("psi_AB"), e=Fraction(b["e"][0]),
                c_A=Fraction(b["c_A"][0]), c_B=Fraction(b["c_B"][0]),
                c_C=Fraction(b["c_C"][0]),
                F=[[[Fraction(x) for x in row] for row in b[f"F{kk}"]]
                   for kk in range(len(qm.F_sizes))],
                B={k2[2:]: [[Fraction(x) for x in row] for row in m_]
                   for k2, m_ in b.items() if k2.startswith("B_")},
                sig={k2[4:]: [[Fraction(x) for x in row] for row in m_]
                     for k2, m_ in b.items() if k2.startswith("sig_")})
    # PSD 全块精确 LDLᵀ
    n_psd = 0
    for m_ in data["F"] + list(data["B"].values()) + list(data["sig"].values()):
        if not is_positive_definite([[x for x in row] for row in m_]):
            fail(f"{path.name}: PSD 块 LDLᵀ 失败")
        n_psd += 1
    # 归一化精确
    s111 = sum(sum(row) for row in data["F"][0])
    nrm = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
           + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
           - Fraction(qm.s111_factor) * s111)
    if nrm != 0:
        fail(f"{path.name}: 归一化残差 {nrm} ≠ 0")
    # R1/R2 精确重算
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"]
                         for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    R2 = {}
    for cls in ("AA", "AB"):
        lhs = qm.minorant_lhs({nm: data["sig"][f"{cls}_{nm}"]
                               for (nm, _my, _mu) in qm.sig_def})
        rhs = qm.minorant_rhs(data[qm.h_of[cls]])
        rr = [x - y for x, y in zip(rhs, lhs)]
        R2[cls] = sum(abs(rr[j]) * qm.w_hat ** j for j in range(len(rr)))
    defl = sum(qm.class_counts[o] * qm.counts[o] * R1[o] for o in R1)
    certified = (data["e"] - defl) / (1 + max(R2.values()))
    claimed = Fraction(cert["claimed_bound"])
    if certified != claimed:
        fail(f"{path.name}: 重算 certified {float(certified):.15f} ≠ claimed "
             f"{float(claimed):.15f}")
    E_star = load_E_star()
    print(f"[vcert] {path.name}: certified = {float(certified):.12f} 重算一致 ✓"
          f"（{n_psd} PSD 块 LDLᵀ 通过，归一化残差 = 0；"
          f"E* − certified = {float(E_star - certified):.9f}）")
    return certified


# ============================================================ 单档全流程
def run_rung(a0_str: str, M: int, K: int, sdpa_bin: Path, ks=(48, 56, 64),
             skip_solve=False, min_bound=None):
    a0 = Fraction(a0_str)
    tag = rung_tag(a0)
    E_star = load_E_star()
    qm = QuotientMaps(a0, M, K)
    if min_bound is None:
        min_bound = REGIONAL_RECORD if tag == "m0748" else F0
    workroot = HERE / "results" / "typed_ladder_work"
    sol_path = HERE / "results" / f"typed_ladder_sol_{tag}_M{M}.json"
    solve_info = None
    if skip_solve:
        if not sol_path.exists():
            fail(f"--skip-solve 但解数据不存在：{sol_path}")
        print(f"[rung ] {tag} M={M}：复用解数据 {sol_path.relative_to(REPO)}", flush=True)
    else:
        if sol_path.exists():
            print(f"[rung ] {tag} M={M}：已有解数据，跳过求解（删 {sol_path.name} 重解）",
                  flush=True)
            solve_info = dict(reused_file=True)
        else:
            sol_path, solve_info = solve_rung(a0, M, K, sdpa_bin, workroot)
    sol = json.loads(sol_path.read_text())
    cert_name = f"n9-stage-a4-typedcap-{tag}" + (f"_M{M}.json" if M != 7 else ".json")
    cert_path = REPO / "certificates" / cert_name
    last_err = None
    for k in ks:
        try:
            cert = certify(qm, sol, k, f"{tag}/M{M}", E_star, min_bound=min_bound)
        except CertError as exc:
            print(f"[retry] {tag} 粒度 2^-{k} 未通过：{exc}", flush=True)
            last_err = str(exc)
            continue
        cert_js = write_certificate(qm, cert, tag, a0, M, K, sol,
                                    solve_info or {}, cert_path)
        _c = verify_cert_file(cert_path)
        rung = dict(
            tag=tag, a0=a0_str, a0_float=float(a0), M=M, K=K,
            e_raw=float(Fraction(sol["exact"]["e"])),
            certified=str(cert["certified"]), certified_float=float(cert["certified"]),
            gap_to_E_star=float(E_star - cert["certified"]),
            improvement_over_regional_record=float(cert["certified"] - REGIONAL_RECORD),
            round_bits=k,
            R1={o: float(v) for o, v in cert["R1"].items()},
            R2={c: float(v) for c, v in cert["R2"].items()},
            deflation=float(cert["defl"]), R2max=float(cert["R2max"]),
            certificate=str(cert_path.relative_to(REPO)),
            solution=str(sol_path.relative_to(REPO)),
            sdpa=sol.get("solver_info"),
            cover=f"min_inner >= {a0_str}",
        )
        if tag == "m0748":
            if not (cert["certified"] > REGIONAL_RECORD):
                fail(f"{tag}: certified ≤ 区域纪录 {float(REGIONAL_RECORD)}（已在上游断言）")
        print(f"[rung ] {tag} M={M} ✓ certified = {float(cert['certified']):.12f}"
              f"（E* − c = {float(E_star - cert['certified']):.9f}；"
              f"vs 区域纪录 {float(cert['certified'] - REGIONAL_RECORD):+.3e}）",
              flush=True)
        return rung
    fail(f"{tag}: 全部粒度 {list(ks)} 认证失败（最后：{last_err}）")


# ============================================================ Clarabel 交叉验证（导出正确性）
def crosscheck(a0_str: str, M: int, K: int, sdpa_bin: Path):
    """(6,6) 档：typed/solve.py 的**全 SDP**（Clarabel，独立浮点实现）vs 本文件
    商 SDP 的 SDPA-GMP 解：值一致（±Clarabel 折减）⟹ 商等价 + 导出正确。"""
    a0 = Fraction(a0_str)
    tag = rung_tag(a0)
    print(f"[xchk ] {tag} M={M}：Clarabel 全 typed SDP 求解中……", flush=True)
    import solve as typed_solve                       # typed/solve.py
    from core import TypeStructure
    ts = TypeStructure(list(TYPES))
    e_full, info, _chk, _maps, _V = typed_solve.solve_case(
        ts, "cut", float(a0), None, M, K)
    print(f"[xchk ] Clarabel 全 SDP：e = {e_full:.12f}（{info['status']}，"
          f"{info['solve_s']}s）", flush=True)
    workroot = HERE / "results" / "typed_ladder_work"
    sol_path, sinfo = solve_rung(a0, M, K, sdpa_bin, workroot, timeout_s=7200)
    sol = json.loads(sol_path.read_text())
    e_quot = float(Fraction(sol["exact"]["e"]))
    rr = json.loads(sol_path.read_text())["raw_residuals"]
    r1max = max(float(Fraction(v)) for v in rr["R1"].values())
    r2max = max(float(Fraction(v)) for v in rr["R2"].values())
    E_star = float(load_E_star())
    ok_val = abs(e_quot - e_full) <= 3e-3
    ok_resid = r1max < 1e-20 and r2max < 1e-20
    ok_cap = e_quot <= E_star + 1e-3
    print(f"[xchk ] SDPA-GMP 商 SDP：e = {e_quot:.12f}；|Δ| = {abs(e_quot - e_full):.2e}"
          f"（阈值 3e-3）；raw R1 ≤ {r1max:.1e}，R2 ≤ {r2max:.1e}", flush=True)
    if not (ok_val and ok_resid and ok_cap):
        fail(f"交叉验证失败：ok_val={ok_val} ok_resid={ok_resid} ok_cap={ok_cap}")
    print(f"[xchk ] ✓ 商等价 + 导出正确（值贴合、残差 ~1e-30 量级、未超 E*）", flush=True)
    return dict(e_clarabel_full=e_full, e_quotient=e_quot, delta=abs(e_quot - e_full),
                raw_R1_max=r1max, raw_R2_max=r2max,
                clarabel_status=info["status"], ok=True)


# ============================================================ 条带可行性研究
def strip_study(M=7, K=6, bands=None, out_note=None):
    """[−0.90,−0.755] typed 条带覆盖可行性：测试带的 e_opt − 目标 裕度衰减。

    用 slab_band.py（Round 2 (2,7) 分带 typed，独立实现）在测试带上跑 Clarabel
    (M,K)，量 e_raw 与 deflation；据裕度衰减外推盖满 [−0.90,−0.755]（及到
    −0.748）的片数与瓶颈。目标线：E*（完整证明）与当前全局纪录（拼合）。
    """
    import slab_band
    E_star = load_E_star()
    global_record = Fraction("25.759445973097478")   # Round 3 HP（untyped m≥−0.9）
    if bands is None:
        bands = [("-0.90", "-0.88"), ("-0.88", "-0.86"), ("-0.86", "-0.84"),
                 ("-0.82", "-0.80"), ("-0.78", "-0.76"), ("-0.76", "-0.755")]
    rows = []
    for (lo_s, hi_s) in bands:
        lo, hi = Fraction(lo_s), Fraction(hi_s)
        t0 = time.time()
        e_val, info, chk, _sol, _core, _lm, _V = slab_band.solve_slab(N, lo, hi, M, K)
        e_safe = chk["e_safe_indicative"] if chk else None
        deflate = chk["indicative_deflation"] if chk else None
        row = dict(band=f"[{lo_s},{hi_s}]", e_raw=e_val, e_safe=e_safe,
                   deflation=deflate, solve_s=info["solve_s"],
                   status=info["status"],
                   margin_over_E_star=(e_val - float(E_star)),
                   margin_safe_over_E_star=(e_safe - float(E_star)
                                            if e_safe is not None else None),
                   margin_safe_over_global=(e_safe - float(global_record)
                                            if e_safe is not None else None))
        rows.append(row)
        print(f"[strip] {row['band']}: e_raw = {e_val:.9f}（e_safe = "
              f"{e_safe:.9f}，defl = {deflate:.2e}）→ vs E* {row['margin_over_E_star']:+.4f}"
              f" / vs 全局纪录 {row['margin_safe_over_global']:+.4f}"
              f"（{info['solve_s']}s，{time.time() - t0:.0f}s）", flush=True)
    return dict(config=dict(M=M, K=K, tool="slab_band.py (2,7) typed band, Clarabel"),
                bands=rows, E_star=float(E_star), global_record=float(global_record),
                note=out_note or "")


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="typed (3,3,3) cap 阶梯（Round 3）")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--rung", help="单档，如 -0.748")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--M", type=int, default=7)
    ap.add_argument("--K", type=int, default=6)
    ap.add_argument("--skip-solve", action="store_true")
    ap.add_argument("--ks", type=int, nargs="+", default=[48, 56, 64])
    ap.add_argument("--crosscheck", help="Clarabel 全 SDP 交叉验证（建议 6 6）")
    ap.add_argument("--strip-study", action="store_true")
    ap.add_argument("--verify-cert", help="证书独立复核")
    ap.add_argument("--sdpa-bin", default=os.environ.get(
        "SDPA_GMP_BIN", "/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp"))
    ap.add_argument("--out", default=str(HERE / "results" / "typed_ladder.json"))
    args = ap.parse_args()
    sdpa_bin = Path(args.sdpa_bin)
    out_path = Path(args.out)

    if args.selftest:
        run_selftests()
        return
    if args.verify_cert:
        verify_cert_file(Path(args.verify_cert))
        return
    if args.crosscheck:
        res = crosscheck(args.crosscheck, args.M, args.K, sdpa_bin)
        db = json.loads(out_path.read_text()) if out_path.exists() else {}
        db.setdefault("crosschecks", {})[f"M{args.M}_{args.crosscheck}"] = res
        db["kind"] = db.get("kind") or "typed-ladder"
        out_path.write_text(json.dumps(db, ensure_ascii=False, indent=1))
        return
    if args.strip_study:
        res = strip_study(M=args.M, K=args.K)
        db = json.loads(out_path.read_text()) if out_path.exists() else {}
        db.setdefault("stripFeasibility", {})
        db["stripFeasibility"][f"M{args.M}"] = res
        out_path.write_text(json.dumps(db, ensure_ascii=False, indent=1))
        print(f"[out] 条带研究已并入 {out_path}")
        return

    if not (sdpa_bin.exists() and os.access(sdpa_bin, os.X_OK)):
        fail(f"sdpa_gmp 不可执行：{sdpa_bin}（--sdpa-bin 或 SDPA_GMP_BIN）")

    rungs = []
    if args.rung:
        rungs.append(args.rung)
    elif args.all:
        rungs = [r[1] for r in LADDER]
    else:
        ap.error("需要 --rung / --all / --selftest / --crosscheck / --strip-study / --verify-cert")

    results = []
    for a0_str in rungs:
        results.append(run_rung(a0_str, args.M, args.K, sdpa_bin, ks=tuple(args.ks),
                                skip_solve=args.skip_solve))
    db = json.loads(out_path.read_text()) if out_path.exists() else {}
    db.setdefault("rungs", [])
    by_key = {f"{r['tag']}_M{r['M']}": r for r in db["rungs"]}
    for r in results:
        by_key[f"{r['tag']}_M{r['M']}"] = r
    db["rungs"] = list(by_key.values())
    best = max(db["rungs"], key=lambda r: r["certified_float"])
    db["best"] = dict(tag=best["tag"], M=best["M"],
                      certified=best["certified"], certified_float=best["certified_float"],
                      gap_to_E_star=best["gap_to_E_star"])
    db["kind"] = "typed-ladder"
    db["script"] = "typed_ladder.py"
    db["code_version"] = code_version()
    db["E_star"] = float(load_E_star())
    db["regional_record_round2"] = float(REGIONAL_RECORD)
    db["updated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    out_path.write_text(json.dumps(db, ensure_ascii=False, indent=1))
    print(f"[out] 已写 {out_path}（best: {db['best']['tag']} M={db['best']['M']} "
          f"certified = {db['best']['certified_float']:.12f}）")


if __name__ == "__main__":
    main()
