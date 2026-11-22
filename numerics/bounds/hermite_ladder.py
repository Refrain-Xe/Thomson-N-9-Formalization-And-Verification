#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""hermite_ladder.py — R6-2/R6-3 Hermite 引擎：cap 缺口归零 ＋ 受阻条带重盖（Round 6 相位 B/C）.

架构（裁决 D6，notes/decisions.md）：
  保留 typed_ladder.py 的 (3,3,3) S₃ 商 cut 构造与 slab_band.py 的 (2,7) 条带
  构造的**全部**身份结构（ψ share、c 常数、F 矩容器块、SOS 域乘子块），
  把三条类 minorant 多项式 H_cls 从"自由变量＋Lukács SOS 约束"换成**固定的
  精确 dyadic Hermite minorant M**（hermite_minorant.hermite_minorant_dyadic：
  φ(t)=(2−2t)^{−1/2} 六节点值＋一阶导插值，区间算术证书 φ ≥ M 于 [−1,1]，
  节点处裕度≈W=2^-48 量级）。

  数学链（cap，域 m ≥ a₀）：
    E(X) = Σ_{i<j}φ ≥ Σ_{i<j}M（φ ≥ M 全局逐点，解析证书）
    Σ_{i<j}M − e = Σ_T λ_T + Σ_all（typed 组合恒等式，精确自检）
    λ_T ≥ −R1_T 于域（SOS ≥ 0 ＋ ‖resid‖₁，|u|,|v|,|t| ≤ 1）；Σ_all ≥ 0
    ⟹ E ≥ e − defl ＝ certified。**无 R2 膨胀项**（Lukács 的 (1+R2) 分母消失）。

  条带（域 m ∈ [lo,hi]，(0,1) 为最小内积对）同构：certified = e − (7R1_A+42R1_B+35R1_Γ)。

  SDP 变化：LP 块只剩 e/ψ/c（h 位置删除）；minorant 行与 σ/τ 块整段删除；
  h 的份额贡献（(h_AA−ψ_AA)/6 等）作为常数进 b 向量。行数与块数更少。

用法（thomson-n9 下；求解 >10 分钟须后台＋轮询）：
  python3 numerics/bounds/hermite_ladder.py --selftest          # 精确恒等式自检
  python3 numerics/bounds/hermite_ladder.py --cap -0.748 --M 8  # 相位 B 全流程
  python3 numerics/bounds/hermite_ladder.py --cap -0.748 --M 8 --skip-solve
  python3 numerics/bounds/hermite_ladder.py --strip "-0.82:-0.79" --M 8
  python3 numerics/bounds/hermite_ladder.py --verify-cert certificates/n9-stage-a5-hermite-cap-m0748_M8.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
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

from typed_ladder import (QuotientMaps, FRing, frac_dec, parse_result,   # noqa: E402
                          PARAM_SDPA, rung_tag, load_E_star, code_version,
                          F0, F1, fail, CertError)
from slab_band import TypedCore, LamMaps                                  # noqa: E402
from hermite_minorant import (hermite_minorant_dyadic,                   # noqa: E402
                              V2_VARIANTS, load_ttp_spectrum, eval_poly_frac)
from sdp_certify import dyad, repair_psd                                 # noqa: E402
from thomson_certs.exact import is_positive_definite                     # noqa: E402

SEED = 20261006
N = 9
PHI_TOL = Fraction(1, 10 ** 6)
E_TTP_TUBE = Fraction("25.75998653126983")     # tube.json 全精度口径（读回护栏）
E_STAR_DEC = Fraction("25.759986531")          # E* 十进制精确口径（D28 裁决 3）
WOULD_BE = Fraction("25.759571185600716")      # 现行 L1 cap（拼合 wouldBe 参照）
# 停滞点接受阈：phase≠pdOPT 但恒等式回读残差 R1 ≤ 此值时，作为**合法但可能
# 次优**的可行点走认证（证书链从数据精确重推，与求解器自评无关；provenance
# 如实记录 phase/iteration/stalled）。2026-10-05 实测 M8 档在 iter 47–49
# noINFO 停滞、R1 ~1e-20 量级。
STALLED_R1_TOL = Fraction(1, 10 ** 12)


# ============================================================ 固定 Hermite minorant
_HERMITE_CACHE: dict = {}


def fixed_minorant(k: int = 48, variant: str = "hermite") -> dict:
    """确定性构造（与 hermite_probe.json 同链）：M ≤ φ 于 [−1,1]。

    variant="hermite"（12 条 deg≤11，历史档）；"contact"（17 条 deg≤16，
    −1 处 0–4 阶接触）；"triple"（18 条 deg≤17，三重接触）——R8B v2。"""
    key = (k, variant)
    if key not in _HERMITE_CACHE:
        spec = load_ttp_spectrum()
        if variant == "hermite":
            _HERMITE_CACHE[key] = hermite_minorant_dyadic(spec["nodes"], k=k)
        else:
            cfg = V2_VARIANTS[variant]
            _HERMITE_CACHE[key] = hermite_minorant_dyadic(
                spec["nodes"], k=k, contact_minus1=cfg["contact_minus1"],
                orders=cfg["orders"])
    return _HERMITE_CACHE[key]


def check_variant_fit(variant: str, M: int, dy: dict) -> None:
    """变体↔档位结构容纳性（d_H=2M−2；ncond ≤ d_H+1 且 M ≥ min_M）。"""
    if variant not in ("hermite", "contact", "triple"):
        fail(f"未知变体：{variant}")
    if variant != "hermite":
        cfg = V2_VARIANTS[variant]
        if M < cfg["min_M"] or len(dy["coeffs"]) > 2 * M - 1:
            fail(f"变体 {variant}（{len(dy['coeffs'])} 系数，min_M="
                 f"{cfg['min_M']}）不容于 M={M}（d_H=2M−2="
                 f"{2 * M - 2}，槽位 {2 * M - 1}）")


def pad_h(coeffs: list[Fraction], d_H: int) -> list[Fraction]:
    out = list(coeffs) + [F0] * (d_H + 1 - len(coeffs))
    assert len(out) == d_H + 1
    return out


def check_minorant_validity(k: int = 48) -> dict:
    """证书用 M 的独立复核：区间构造重跑（确定性）＋float 采样 φ ≥ M。"""
    dy = fixed_minorant(k)
    spec = load_ttp_spectrum()
    # float 采样（rigorous 主体是区间论证；此处为独立数值见证）
    worst = None
    for i in range(200001):
        t = -1.0 + i * (2.0 - 1e-9) / 200000
        val = eval_poly_frac(dy["coeffs"], Fraction(t))
        ph = 1.0 / math.sqrt(2.0 - 2.0 * t)
        worst = min(worst if worst is not None else 1e9, ph - float(val))
    assert worst is not None and worst >= -1e-15, f"φ ≥ M 采样失败：{worst}"
    return dict(k=k, W=str(dy["W"]), float_spot_min=worst,
                remainder=dy["remainder"], ncond=dy["ncond"],
                coeffs_sha16=hashlib.sha256(
                    json.dumps([str(c) for c in dy["coeffs"]]).encode()
                ).hexdigest()[:16])


# ============================================================ 精确自检（固定 h 的恒等式）
def random_dyadic_data_fixed_h(qm: QuotientMaps, rng, h_AA, h_AB, scale_bits=10):
    d_H = qm.d_H
    data = dict(
        h_AA=list(h_AA), h_AB=list(h_AB),
        psi_AA=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
                for _ in range(d_H + 1)],
        psi_AB=[Fraction(rng.randint(-1 << scale_bits, 1 << scale_bits), 1 << scale_bits)
                for _ in range(d_H + 1)],
        e=Fraction(rng.randint(20 << 8, 30 << 8), 1 << 8),
        c_A=Fraction(rng.randint(-8, 8), 4),
        c_B=Fraction(rng.randint(-8, 8), 4),
        F=[])
    for mk in qm.F_sizes:
        G = [[Fraction(rng.randint(-8, 8), 4) for _ in range(mk)] for _ in range(mk)]
        data["F"].append([[sum(G[i][t] * G[j][t] for t in range(mk)) for j in range(mk)]
                          for i in range(mk)])
    s111 = sum(sum(row) for row in data["F"][0])
    data["c_C"] = (data["e"] + qm.s111_factor * s111
                   - qm.nrm["c_A"] * data["c_A"] - qm.nrm["c_B"] * data["c_B"]) / qm.nrm["c_C"]
    return data


def exact_identity_selftest_fixed_h(qm: QuotientMaps, rng, trials=2):
    """typed 组合恒等式在固定 h=M、随机 ψ/c/F/e 上精确 == 0（typed_ladder 的
    全类展开路径，h 固定）。"""
    ring = qm.ring
    dy = fixed_minorant(48)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    from itertools import combinations
    types = [0] * 3 + [1] * 3 + [2] * 3

    def rational_config(rng, n):
        return [(Fraction(rng.randint(-64, 64), 64), Fraction(rng.randint(-64, 64), 64))
                for _ in range(n)]

    for _ in range(trials):
        data = random_dyadic_data_fixed_h(qm, rng, h_AA, h_AA)
        pts = rational_config(rng, N)
        P = [((2 * a) / (1 + a * a + b * b), (2 * b) / (1 + a * a + b * b),
              (1 - a * a - b * b) / (1 + a * a + b * b)) for (a, b) in pts]
        G = [[sum(x * y for x, y in zip(xi, xj)) for xj in P] for xi in P]
        s_vec, _ = qm.s_forms(data)
        sum_all = sum(ring.eval3(s_vec, G[i][j], G[i][l], G[j][l])
                      for i in range(N) for j in range(N) for l in range(N))
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
                key = qm.h_of["AA" if types[i] == types[j] else "AB"]
                sum_H += ring.eval1(data[key], G[i][j])
        assert sum_lam + sum_all == sum_H - data["e"], \
            f"固定 h 恒等式失败：{sum_lam + sum_all} != {sum_H - data['e']}"
    return dict(ok=True, trials=trials)


def strip_identity_selftest_fixed_h(core: TypedCore, lm: LamMaps, rng, trials=2):
    """slab 组合恒等式在固定 hA=hB=hC=M 上精确 == 0（slab_band.
    exact_typed_identity_selftest 的固定 h 复刻：数据随机、h 固定、
    λ 片段直接求值＋lam() 装配一致性）。"""
    from slab_band import s_forms, gm_vec, random_dyadic_config
    n = core.n
    dy = fixed_minorant(48)
    hM = pad_h(dy["coeffs"], core.d_H)
    d_H = core.d_H
    for _ in range(trials):
        data = dict(
            hA=list(hM), hB=list(hM), hC=list(hM),
            psiBa=[Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12)
                   for _ in range(d_H + 1)],
            psiCb=[Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12)
                   for _ in range(d_H + 1)],
            e=Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12),
            cA=Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12),
            cB=Fraction(rng.randint(-1 << 12, 1 << 12), 1 << 12))
        data["FP"], data["FR"] = [], []
        for key in ("FP", "FR"):
            lst = []
            for m_k in core.F_sizes:
                G = [[Fraction(rng.randint(-6, 6), 2) for _ in range(m_k)]
                     for _ in range(m_k)]
                Fk = [[sum(G[i][t] * G[j][t] for t in range(m_k)) for j in range(m_k)]
                      for i in range(m_k)]
                lst.append(Fk)
            data[key] = lst
        sP111 = sum(sum(row) for row in data["FP"][0])
        sR111 = sum(sum(row) for row in data["FR"][0])
        cG = (data["e"] + 2 * sP111 + core.ring_n * sR111
              - core.nPPR * data["cA"] - core.nPRR * data["cB"]) / core.nRRR
        X = random_dyadic_config(rng, n)
        G = [[sum(xi[t] * xj[t] for t in range(3)) for xj in X] for xi in X]
        sP_vec, sR_vec = s_forms(core, (data["FP"], data["FR"]))
        gmP, gmR = gm_vec(core, data["FP"]), gm_vec(core, data["FR"])

        def sP(u, v, t):
            return core.eval3(sP_vec, u, v, t)

        def sR(u, v, t):
            return core.eval3(sR_vec, u, v, t)

        def H(vec, x):
            return core.eval1(vec, x)

        sall = F0
        for i in range(n):
            f = sP if i < 2 else sR
            for j in range(n):
                for l in range(n):
                    sall += f(G[i][j], G[i][l], G[j][l])
        sumH = H(data["hA"], G[0][1])
        for r in range(2, n):
            sumH += H(data["hB"], G[0][r]) + H(data["hB"], G[1][r])
        for r in range(2, n):
            for r2 in range(r + 1, n):
                sumH += H(data["hC"], G[r][r2])
        lam_sum = F0
        PsiA = [data["hA"][j] - 2 * gmP[j] for j in range(d_H + 1)]
        PsiB = [data["hB"][j] - gmP[j] - gmR[j] for j in range(d_H + 1)]
        wB = [(PsiB[j] - data["psiBa"][j]) * Fraction(1, core.dB)
              for j in range(d_H + 1)]
        wC = [(data["hC"][j] - 2 * gmR[j] - 2 * data["psiCb"][j]) * Fraction(1, core.dC)
              for j in range(d_H + 1)]
        for r in range(2, n):                                   # PPR {0,1,r}
            u, v, t = G[0][1], G[0][r], G[1][r]
            lam_sum += (H(PsiA, u) * Fraction(1, core.dA) + H(data["psiBa"], v)
                        + H(data["psiBa"], t) - data["cA"]
                        - 2 * (sP(u, v, t) + sP(u, t, v) + sR(v, t, u)))
        for p in (0, 1):                                        # PRR {p,r,r'}
            for r in range(2, n):
                for r2 in range(r + 1, n):
                    u, v, t = G[p][r], G[p][r2], G[r][r2]
                    lam_sum += (H(wB, u) + H(wB, v) + H(data["psiCb"], t) - data["cB"]
                                - 2 * (sP(u, v, t) + sR(u, t, v) + sR(v, t, u)))
        for r in range(2, n):                                   # RRR
            for r2 in range(r + 1, n):
                for r3 in range(r2 + 1, n):
                    u, v, t = G[r][r2], G[r][r3], G[r2][r3]
                    lam_sum += (H(wC, u) + H(wC, v) + H(wC, t) - cG
                                - 2 * (sR(u, v, t) + sR(u, t, v) + sR(v, t, u)))
        if sumH - data["e"] != lam_sum + sall:
            fail(f"条带固定 h 恒等式失败：{sumH - data['e'] - lam_sum - sall} ≠ 0")
        for which, pt in (("A", (G[0][1], G[0][2], G[1][2])),
                          ("B", (G[0][2], G[0][3], G[2][3])),
                          ("G", (G[2][3], G[2][4], G[3][4]))):
            vec = lm.lam(which, data)
            u, v, t = pt
            if which == "A":
                direct = (H(PsiA, u) * Fraction(1, core.dA) + H(data["psiBa"], v)
                          + H(data["psiBa"], t) - data["cA"]
                          - 2 * (sP(u, v, t) + sP(u, t, v) + sR(v, t, u)))
            elif which == "B":
                direct = (H(wB, u) + H(wB, v) + H(data["psiCb"], t) - data["cB"]
                          - 2 * (sP(u, v, t) + sR(u, t, v) + sR(v, t, u)))
            else:
                direct = (H(wC, u) + H(wC, v) + H(wC, t) - cG
                          - 2 * (sR(u, v, t) + sR(u, t, v) + sR(v, t, u)))
            if core.eval3(vec, u, v, t) != direct:
                fail(f"λ_{which} 装配与片段求值不一致（固定 h）")
    return dict(ok=True, trials=trials)


# ============================================================ cap SDPA 导出（Hermite 版）
class HermiteCapExporter:
    """typed_ladder.SDPAExporter 的 Hermite 版：h 固定（常数进 b），无 minorant 行/σ 块。

    变量：LP 对角（e⁺；psi_AA/psi_AB/c_A/c_B/c_C ± 拆分）＋F×K＋SOS×3×8。
    行：3·nmon（slack，b 含 h 份额）＋1（归一化）。"""

    def __init__(self, qm: QuotientMaps, h_AA, h_AB,
                 lp_penalty=Fraction(1, 10 ** 11)):
        self.qm, self.lp_penalty = qm, (lp_penalty or None)
        if lp_penalty is None:
            self.lp_penalty = Fraction(0)
        self.h_AA, self.h_AB = list(h_AA), list(h_AB)
        d_H1 = qm.d_H + 1
        assert len(self.h_AA) == d_H1 and len(self.h_AB) == d_H1
        pos = 1
        self.e_pos = 1
        pos += 1
        self.vpos = {}
        for name in ("psi_AA", "psi_AB"):
            self.vpos[name] = (pos, pos + d_H1)
            pos += 2 * d_H1
        for name in ("c_A", "c_B", "c_C"):
            self.vpos[name] = (pos, pos + 1)
            pos += 2
        self.n_lp = pos - 1
        self.blk = [-self.n_lp] + list(qm.F_sizes) \
            + [len(m) for _n, _g, m in qm.sos_def] * 3
        self.f_off = 2
        self.sos_off = self.f_off + len(qm.F_sizes)
        self.orbit_row = {o: i * qm.nmon + 1
                          for i, o in enumerate(("AAA", "AAB", "ABC"))}
        self.row_norm = 3 * qm.nmon + 1
        self.m = self.row_norm

    def h_const_rows(self):
        """h 的份额贡献 → b（AAB slot0：(h_AA−ψ)/6 中 h_AA/6；ABC 三槽 h_AB/3）。

        行约束是 Σ entries·X = b，其中 entries 只含变量侧（ψ/c/F/SOS）：
        ψ+F−SOS = −h_const ⟹ b 取 **负** h 份额。"""
        qm, ring = self.qm, self.qm.ring
        b = {}
        for d in range(qm.d_H + 1):
            e0 = (d, 0, 0)
            r = self.orbit_row["AAB"] + ring.index[e0]
            b[r] = b.get(r, F0) - self.h_AA[d] / 6
            for slot in range(3):
                e = [0, 0, 0]
                e[slot] = d
                r = self.orbit_row["ABC"] + ring.index[tuple(e)]
                b[r] = b.get(r, F0) - self.h_AB[d] / 3
        return b

    def build_entries(self):
        qm, ring = self.qm, self.qm.ring
        acc: dict = {}

        def put(k, l, i, j, v):
            if v:
                acc[(k, l, i, j)] = acc.get((k, l, i, j), F0) + v

        for orbit in ("AAA", "AAB", "ABC"):
            for (k, l, i, j, v) in self._slack_rows(orbit):
                put(k, l, i, j, v)
        for (k, l, i, j, v) in self._norm_rows():
            put(k, l, i, j, v)
        put(0, 1, self.e_pos, self.e_pos, F1)
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
            uni_add(0, "psi_AA", -1, 6)       # (h_AA−ψ_AA)/6 的变量部分
            uni_add(1, "psi_AB", 1)
            uni_add(2, "psi_AB", 1)
            sca_add("c_B", -1)
        else:
            for slot in range(3):
                uni_add(slot, "psi_AB", -4, 3)    # (h_AB−4ψ_AB)/3 变量部分
            sca_add("c_C", -1)
        for idx in range(len(qm.Y_cols)):
            k, a_, b_ = qm.col_kab[idx]
            l = self.f_off + k
            col = self._f_col(orbit, idx)
            if a_ == b_:
                for p, c in enumerate(col):
                    if c:
                        E.append((row0 + p, l, a_ + 1, a_ + 1, c))
            elif a_ < b_:
                colT = self._f_col(orbit, qm.Y_index[(k, b_, a_)])
                sym = [(x + y) / 2 for x, y in zip(col, colT)]
                for p, c in enumerate(sym):
                    if c:
                        E.append((row0 + p, l, a_ + 1, b_ + 1, c))
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

    def _f_col(self, orbit, idx):
        qm, ring = self.qm, self.qm.ring
        keys = qm.lam_spec[orbit][0]
        col = list(qm.K_cols[idx])
        for slot in range(3):
            g = qm.GM_OF[keys[slot]]
            if g:
                col = [x + g * y for x, y in zip(
                    col, ring.lift_slot0(qm.gm_cols[idx], slot))]
        return col

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
        for a_ in range(m0):
            for b_ in range(m0):
                E.append((r, l, a_ + 1, b_ + 1, -Fraction(qm.s111_factor)))
        return E

    def b_vector(self):
        b = [F0] * self.m
        for r, v in self.h_const_rows().items():
            b[r - 1] += v
        return b

    def write_dat(self, path: Path):
        E = self.build_entries()
        b = self.b_vector()
        with open(path, "w") as f:
            f.write('"N=9 typed (3,3,3) S3-quotient Hermite-fixed cap SDP (exact rational)"\n')
            f.write(f"{self.m} = mDIM\n{len(self.blk)} = nBLOCK\n")
            f.write(" ".join(str(s) for s in self.blk) + " = bLOCKsTRUCT\n")
            f.write(" ".join(frac_dec(x) for x in b) + "\n")
            for (k, l, i, j, v) in E:
                f.write(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        return self.m, len(E)


# ============================================================ cap 回读
def solution_from_parse_cap(ex: HermiteCapExporter, parsed: dict,
                            h_AA, h_AB) -> dict:
    qm = ex.qm
    lp = parsed["lp"]
    if len(lp) != ex.n_lp:
        fail(f"LP 块长度 {len(lp)} ≠ {ex.n_lp}")
    d_H1 = qm.d_H + 1

    def split_get(name):
        pp, mm_ = ex.vpos[name]
        return [lp[pp - 1 + d] - lp[mm_ - 1 + d] for d in range(d_H1)]

    def split_scal(name):
        pp, mm_ = ex.vpos[name]
        return lp[pp - 1] - lp[mm_ - 1]

    data = dict(h_AA=list(h_AA), h_AB=list(h_AB),
                psi_AA=split_get("psi_AA"), psi_AB=split_get("psi_AB"),
                c_A=split_scal("c_A"), c_B=split_scal("c_B"),
                c_C=split_scal("c_C"), e=lp[ex.e_pos - 1])
    mats = []
    for g in parsed["sdp"]:
        n = len(g)
        if any(len(r) != n for r in g):
            fail("SDP 块非方阵")
        mats.append([[Fraction(x) for x in r] for r in g])
    n_expect = len(qm.F_sizes) + 3 * len(qm.sos_def)
    if len(mats) != n_expect:
        fail(f"SDP 块数 {len(mats)} ≠ {n_expect}")
    off = 0
    data["F"] = mats[off:off + len(qm.F_sizes)]
    off += len(qm.F_sizes)
    B = {}
    for oi, orbit in enumerate(("AAA", "AAB", "ABC")):
        for bi, (name, _g, mons) in enumerate(qm.sos_def):
            B[f"{orbit}_{name}"] = mats[off]
            off += 1
    data["B"] = B
    return data


def raw_residuals_cap(qm: QuotientMaps, data: dict) -> dict:
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    nrm_resid = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
                 + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
                 - Fraction(qm.s111_factor) * sum(sum(r) for r in data["F"][0]))
    return dict(R1=R1, nrm=nrm_resid)


# ============================================================ cap 求解
def solve_cap(a0: Fraction, M: int, K: int, sdpa_bin: Path, k_minor: int = 48,
              timeout_s=172800):
    tag = rung_tag(a0)
    dy = fixed_minorant(k_minor)
    qm = QuotientMaps(a0, M, K)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    ex = HermiteCapExporter(qm, h_AA, h_AA)
    workdir = HERE / "results" / "hermite_work" / f"cap_{tag}_M{M}"
    workdir.mkdir(parents=True, exist_ok=True)
    dat = workdir / "hermite_cap.dat-s"
    if dat.exists():
        dat.unlink()
    m_dim, n_entries = ex.write_dat(dat)
    (workdir / "param.sdpa").write_text(PARAM_SDPA)
    result = workdir / "hermite_cap.result"
    sol_path = HERE / "results" / f"hermite_cap_sol_{tag}_M{M}.json"
    print(f"[export] cap {tag} M={M}: m={m_dim}, entries={n_entries}, "
          f"blocks={len(ex.blk)} (n_lp={ex.n_lp})", flush=True)
    cmd = [str(sdpa_bin), "-ds", str(dat), "-o", str(result),
           "-p", str(workdir / "param.sdpa")]

    def accept(parsed_cand):
        """pdOPT 或（停滞点）回读恒等式残差 ≤ STALLED_R1_TOL。"""
        if parsed_cand["info"]["phase_value"] == "pdOPT":
            return True, False
        try:
            data_c = solution_from_parse_cap(ex, parsed_cand, h_AA, h_AA)
            rr_c = raw_residuals_cap(qm, data_c)
            ok = max(rr_c["R1"].values()) <= STALLED_R1_TOL
            return ok, ok
        except SystemExit:
            return False, False

    reused, parsed, stalled = False, None, False
    if result.exists():
        try:
            cand = parse_result(result)
            ok, st = accept(cand)
            if ok:
                reused, parsed, stalled = True, cand, st
        except SystemExit:
            pass
    if reused:
        info = parsed["info"]
        print(f"[solve] cap {tag}: 复用已有结果 {result}"
              f"（phase={info['phase_value']}）", flush=True)
        solve_s = 0.0
    else:
        if result.exists():
            result.unlink()
        print(f"[solve] cap {tag}: {' '.join(cmd)}", flush=True)
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              cwd=str(workdir), timeout=timeout_s)
        solve_s = time.time() - t0
        if proc.returncode != 0 or not result.exists():
            fail(f"cap {tag}: sdpa_gmp 退出码 {proc.returncode}："
                 f"{proc.stdout[-1500:]} {proc.stderr[-1500:]}")
        parsed = parse_result(result)
        ok, stalled = accept(parsed)
        if not ok:
            fail(f"cap {tag}: SDPA-GMP 未达 pdOPT 且停滞点回读残差超阈："
                 f"{parsed['info']['phase_value']}")
        info = parsed["info"]
    print(f"[solve] cap {tag}: phase={info['phase_value']} iter={info['iteration']} "
          f"mu={info['mu']:.2e} relgap={info['relative_gap']:.2e} "
          f"p.feas={info['p_feas_error']} d.feas={info['d_feas_error']} "
          f"({solve_s:.0f}s)" + ("；**停滞点认证（可能次优）**" if stalled else ""),
          flush=True)
    data = solution_from_parse_cap(ex, parsed, h_AA, h_AA)
    # 读回护栏：cap 域含 TTP ⟹ e ≤ ΣH(X_TTP) ≈ E_ttp；超界即导出/求解事故
    if data["e"] > E_TTP_TUBE + Fraction(1, 10 ** 6):
        fail(f"cap {tag}: e = {float(data['e']):.15f} > E_ttp+1e-6（不可能，导出有误）")
    rr = raw_residuals_cap(qm, data)
    print(f"[resid] cap {tag}: e = {float(data['e']):.15f}；R1 = "
          f"{ {k2: float(v) for k2, v in rr['R1'].items()} }，nrm = "
          f"{float(rr['nrm']):.2e}", flush=True)
    sol_js = dict(
        tag=tag, a0=str(a0), M=M, K=K, minorant_k=k_minor,
        e=float(data["e"]),
        exact=dict(h_AA=[str(x) for x in data["h_AA"]],
                   h_AB=[str(x) for x in data["h_AB"]],
                   psi_AA=[str(x) for x in data["psi_AA"]],
                   psi_AB=[str(x) for x in data["psi_AB"]],
                   c_A=str(data["c_A"]), c_B=str(data["c_B"]), c_C=str(data["c_C"]),
                   e=str(data["e"]),
                   F=[[[str(x) for x in row] for row in m_] for m_ in data["F"]],
                   B={n: [[str(x) for x in row] for row in m_] for n, m_ in data["B"].items()},
                   note="SDPA-GMP .result 66 位十进制精确回读的 Fraction"),
        solver_info=dict(route="SDPA-GMP 7.1.3 (GMP 200)", reused=bool(reused),
                         stalled_point=bool(stalled),
                         solve_s=round(solve_s, 1), lp_penalty=str(ex.lp_penalty),
                         **info),
        raw_residuals={k2: ({kk: str(vv) for kk, vv in v.items()} if isinstance(v, dict)
                            else str(v)) for k2, v in rr.items()},
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    sol_path.write_text(json.dumps(sol_js, ensure_ascii=False))
    print(f"[out] cap {tag}: 解数据 {sol_path.relative_to(REPO)}", flush=True)
    return sol_path, dict(sdpa_info=info, solve_s=round(solve_s, 1), reused=bool(reused),
                          m=m_dim, entries=n_entries)


# ============================================================ cap 认证
def certify_cap(qm: QuotientMaps, sol: dict, k: int, tag: str, E_star: Fraction,
                h_AA, h_AB, spot_seed: int = 97531):
    t0 = time.time()

    def rround(x):
        return dyad(x, k)

    ex = sol["exact"]
    data = dict(h_AA=list(h_AA), h_AB=list(h_AB),
                psi_AA=[rround(Fraction(s)) for s in ex["psi_AA"]],
                psi_AB=[rround(Fraction(s)) for s in ex["psi_AB"]],
                c_A=rround(Fraction(ex["c_A"])), c_B=rround(Fraction(ex["c_B"])),
                e=dyad(Fraction(ex["e"]), k, floor=True), F=[])
    shifts = {}
    for kk, mk in enumerate(qm.F_sizes):
        Mfr, dlt, _t = repair_psd(f"F{kk}", [[rround(Fraction(x)) for x in row]
                                             for row in ex["F"][kk]], k)
        shifts[f"F{kk}"] = dlt
        data["F"].append(Mfr)
    B_dy = {}
    for orbit in ("AAA", "AAB", "ABC"):
        for name, _g, _m in qm.sos_def:
            key = f"{orbit}_{name}"
            Mfr, dlt, _t = repair_psd(f"B_{key}", [[rround(Fraction(x)) for x in row]
                                                   for row in ex["B"][key]], k)
            shifts[f"B_{key}"] = dlt
            B_dy[key] = Mfr
    s111 = sum(sum(row) for row in data["F"][0])
    data["c_C"] = (data["e"] + qm.s111_factor * s111
                   - qm.nrm["c_A"] * data["c_A"] - qm.nrm["c_B"] * data["c_B"]) \
        / qm.nrm["c_C"]
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: B_dy[f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    defl = sum(qm.class_counts[o] * qm.counts[o] * R1[o] for o in R1)
    certified = data["e"] - defl
    if certified <= 0:
        raise CertError(f"[{tag}] e − defl ≤ 0")

    # 域抽查（有理点：SOS 乘子非负＋λ ≥ −R1）
    rng = random.Random(spot_seed + k)
    lo = qm.lo
    lam_orbit = {o: qm.lam(o, data) for o in ("AAA", "AAB", "ABC")}
    ring = qm.ring
    for orbit in ("AAA", "AAB", "ABC"):
        lv = lam_orbit[orbit]
        ok_pts = tries = 0
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
                quad = sum(Bm[p][q] * zp[p] * zp[q]
                           for p in range(m_) for q in range(m_))
                g = sum(c * (u ** eg[0]) * (v ** eg[1]) * (t ** eg[2]) for eg, c in gnz)
                if g < 0:
                    raise CertError(f"[{tag}] 抽查乘子负值 g_{name} = {g}")
                sos_pt += g * quad
            if sos_pt < 0:
                raise CertError(f"[{tag}] SOS 抽查负值（{orbit}）")
            if ring.eval3(lv, u, v, t) + R1[orbit] < 0:
                raise CertError(f"[{tag}] λ_{orbit} 抽查 < −R1")

    if not (0 < certified <= E_star + PHI_TOL):
        raise CertError(f"[{tag}] certified = {float(certified):.15e} 违反 "
                        f"0 < c ≤ E*+1e-6（粒度 2^-{k}）")
    e_raw = Fraction(sol["exact"]["e"])
    if certified > e_raw + Fraction(1, 10 ** 9):
        raise CertError(f"[{tag}] certified > e + 1e-9（不可能）")
    print(f"[cert ] cap {tag}（2^-{k}）：certified = {float(certified):.12f}；"
          f"R1 = { {o: float(R1[o]) for o in R1} }，defl = {float(defl):.3e}，"
          f"（无 R2：Hermite 固定 minorant）认证链 {time.time() - t0:.0f}s", flush=True)
    return dict(data=data, B=B_dy, shifts=shifts, R1=R1, defl=defl,
                certified=certified, k=k)


# ============================================================ cap 证书
def write_cap_certificate(qm: QuotientMaps, cert: dict, tag: str, a0: Fraction,
                          M, K, sol: dict, solve_info: dict, out_path: Path,
                          k_minor: int, cmdline: str):
    data = cert["data"]
    dy = fixed_minorant(k_minor)
    blocks = {"M": [str(x) for x in dy["coeffs"]]}
    for name in ("psi_AA", "psi_AB"):
        blocks[f"{name}_diag"] = [str(x) for x in data[name]]
    for name in ("e", "c_A", "c_B", "c_C"):
        blocks[name] = [str(data[name])]
    for kk, m_ in enumerate(data["F"]):
        blocks[f"F{kk}"] = [[str(x) for x in row] for row in m_]
    for key, m_ in cert["B"].items():
        blocks[f"B_{key}"] = [[str(x) for x in row] for row in m_]
    cert_js = dict(
        kind="n9-stage-a5-hermite-cap",
        tag=tag,
        params=dict(a0=str(a0), M=M, K=K,
                    cover=f"min inner product >= {a0}"),
        blocks=blocks,
        claimed_bound=str(cert["certified"]),
        provenance=dict(
            code_version=code_version(),
            seed=SEED,
            round_bits=cert["k"],
            cmdline=cmdline,
            construction=("typed (3,3,3) S₃ 商 cut 构造（typed_ladder.py 同构）＋"
                          "固定 Hermite minorant（hermite_minorant.py 区间算术："
                          "φ ≥ M 于 [−1,1]，12 条 deg≤11，节点＝tube.json 原值）"),
            minorant=dict(
                theorem=("φ(t) − H_exact(t) = φ^{(12)}(ξ)/12!·∏_k(t−ν_k)² ≥ 0"
                         "（φ^{(m)} = (2m−1)!!(2−2t)^{−(2m+1)/2} > 0）；M = "
                         "区间中点 dyadic 舍入 − W，W = Σ 半宽"),
                k=k_minor, W=str(dy["W"]), ncond=dy["ncond"],
                remainder=dy["remainder"]),
            counts=dict(triples={"AAA": "3x1", "AAB": "6x9", "ABC": "1x27"},
                        pairs={"AA": 9, "AB": 27},
                        normalization="3c_A+54c_B+27c_C = e+9·ΣF^(0)"),
            bound_formula="certified = e − (3R1_AAA+54R1_AAB+27R1_ABC)（无 R2 膨胀）",
            psd_shifts={k2: str(v) for k2, v in cert["shifts"].items()},
            residuals=dict(R1={o: str(v) for o, v in cert["R1"].items()},
                           defl=str(cert["defl"])),
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


def verify_cap_cert_file(path: Path):
    """进程外独立复核：只读 JSON → 重建 → 精确重算 certified 逐位比对。"""
    cert = json.loads(path.read_text())
    prm = cert["params"]
    qm = QuotientMaps(Fraction(prm["a0"]), prm["M"], prm["K"])
    b = cert["blocks"]
    dy = fixed_minorant(cert["provenance"]["minorant"]["k"])
    M_coeffs = [Fraction(x) for x in b["M"]]
    if M_coeffs != dy["coeffs"]:
        fail(f"{path.name}: blocks.M ≠ hermite_minorant_dyadic 重构（固定 minorant 被篡改）")
    h_AA = pad_h(M_coeffs, qm.d_H)

    def uni(name):
        return [Fraction(x) for x in b[f"{name}_diag"]]

    data = dict(h_AA=h_AA, h_AB=h_AA,
                psi_AA=uni("psi_AA"), psi_AB=uni("psi_AB"),
                e=Fraction(b["e"][0]), c_A=Fraction(b["c_A"][0]),
                c_B=Fraction(b["c_B"][0]), c_C=Fraction(b["c_C"][0]),
                F=[[[Fraction(x) for x in row] for row in b[f"F{kk}"]]
                   for kk in range(len(qm.F_sizes))],
                B={k2[2:]: [[Fraction(x) for x in row] for row in m_]
                   for k2, m_ in b.items() if k2.startswith("B_")})
    n_psd = 0
    for m_ in data["F"] + list(data["B"].values()):
        if not is_positive_definite([[x for x in row] for row in m_]):
            fail(f"{path.name}: PSD 块 LDLᵀ 失败")
        n_psd += 1
    s111 = sum(sum(row) for row in data["F"][0])
    nrm = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
           + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
           - Fraction(qm.s111_factor) * s111)
    if nrm != 0:
        fail(f"{path.name}: 归一化残差 {nrm} ≠ 0")
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    defl = sum(qm.class_counts[o] * qm.counts[o] * R1[o] for o in R1)
    certified = data["e"] - defl
    claimed = Fraction(cert["claimed_bound"])
    if certified != claimed:
        fail(f"{path.name}: 重算 certified {float(certified):.15f} ≠ claimed "
             f"{float(claimed):.15f}")
    E_star = load_E_star()
    if not (0 < certified <= E_star + PHI_TOL):
        fail(f"{path.name}: certified 违反 0 < c ≤ E*+1e-6")
    prov = cert["provenance"]
    for field in ("round_bits", "code_version", "seed"):
        if field not in prov:
            fail(f"{path.name}: provenance 缺 {field}")
    print(f"[vcert] {path.name}: certified = {float(certified):.12f} 重算一致 ✓"
          f"（{n_psd} PSD 块 LDLᵀ；归一化 = 0；E* − certified = "
          f"{float(E_star - certified):.9f}）", flush=True)
    return certified


# ============================================================ cap 主流程
def run_cap(a0_str: str, M: int, K: int, sdpa_bin: Path, ks=(48, 56, 64),
            skip_solve=False, k_minor: int = 48):
    a0 = Fraction(a0_str)
    tag = rung_tag(a0)
    E_star = load_E_star()
    qm = QuotientMaps(a0, M, K)
    dy = fixed_minorant(k_minor)
    h_AA = pad_h(dy["coeffs"], qm.d_H)
    sol_path = HERE / "results" / f"hermite_cap_sol_{tag}_M{M}.json"
    solve_info = None
    if skip_solve:
        if not sol_path.exists():
            fail(f"--skip-solve 但解数据不存在：{sol_path}")
        print(f"[cap ] {tag} M={M}：复用解数据 {sol_path.relative_to(REPO)}", flush=True)
    else:
        if sol_path.exists():
            print(f"[cap ] {tag} M={M}：已有解数据，跳过求解（删文件重解）", flush=True)
            solve_info = dict(reused_file=True)
        else:
            sol_path, solve_info = solve_cap(a0, M, K, sdpa_bin, k_minor)
    sol = json.loads(sol_path.read_text())
    cert_name = f"n9-stage-a5-hermite-cap-{tag}" + (f"_M{M}.json" if M != 7 else ".json")
    cert_path = REPO / "certificates" / cert_name
    cmdline = (f"python3 numerics/bounds/hermite_ladder.py --cap {a0_str} "
               f"--M {M} --ks {' '.join(str(x) for x in ks)}")
    last_err = None
    for k in ks:
        try:
            cert = certify_cap(qm, sol, k, f"cap-{tag}/M{M}", E_star, h_AA, h_AA)
        except CertError as exc:
            print(f"[retry] cap {tag} 粒度 2^-{k} 未通过：{exc}", flush=True)
            last_err = str(exc)
            continue
        write_cap_certificate(qm, cert, tag, a0, M, K, sol, solve_info or {},
                              cert_path, k_minor, cmdline)
        _c = verify_cap_cert_file(cert_path)
        rung = dict(
            tag=tag, a0=a0_str, M=M, K=K,
            e_raw=float(Fraction(sol["exact"]["e"])),
            certified=str(cert["certified"]), certified_float=float(cert["certified"]),
            gap_to_E_star=float(E_star - cert["certified"]),
            gap_to_E_ttp=float(E_TTP_TUBE - cert["certified"]),
            round_bits=k, minorant_k=k_minor,
            R1={o: float(v) for o, v in cert["R1"].items()},
            deflation=float(cert["defl"]),
            certificate=str(cert_path.relative_to(REPO)),
            solution=str(sol_path.relative_to(REPO)),
            sdpa=sol.get("solver_info"),
            code_version=code_version(),
        )
        print(f"[cap ] {tag} M={M} ✓ certified = {rung['certified_float']:.12f}"
              f"（E* − c = {rung['gap_to_E_star']:.9f}）", flush=True)
        return rung
    fail(f"cap {tag}: 全部粒度 {list(ks)} 认证失败（最后：{last_err}）")


# ============================================================ 条带导出（Hermite 版）
class HermiteStripExporter:
    """strips_final.SDPAExporterStrip 的 Hermite 版：hA/hB/hC 固定（常数进 b），
    无 minorant 行/τ/σ 块。变量：e＋psiBa/psiCb/cA/cB ± 拆分＋FP/FR×K＋SOS 6+5+5。"""

    def __init__(self, core: TypedCore, lm: LamMaps, hA, hB, hC,
                 lp_penalty=Fraction(1, 10 ** 11)):
        self.core, self.lm = core, lm
        self.lp_penalty = lp_penalty
        self.hA, self.hB, self.hC = list(hA), list(hB), list(hC)
        d_H1 = core.d_H + 1
        pos = 1
        self.e_pos = 1
        pos += 1
        self.vpos = {}
        for name in ("psiBa", "psiCb"):
            self.vpos[name] = (pos, pos + d_H1)
            pos += 2 * d_H1
        for name in ("cA", "cB"):
            self.vpos[name] = (pos, pos + 1)
            pos += 2
        self.n_lp = pos - 1
        K = core.K
        self.blk = ([-self.n_lp] + list(core.F_sizes) + list(core.F_sizes)
                    + [len(m) for _n, _g, m in lm.sosA]
                    + [len(m) for _n, _g, m in lm.sosB]
                    + [len(m) for _n, _g, m in lm.sosG])
        self.f_off = 2
        self.fr_off = self.f_off + K
        self.sos_off = self.fr_off + K
        nmon = core.nmon
        self.rowA, self.rowB, self.rowG = 1, 1 + nmon, 1 + 2 * nmon
        self.m = 3 * nmon

    def h_const_rows(self):
        """h 份额 → b：行约束 Σ entries·X = b 的变量侧为 ψ/c/F−SOS，
        λ = h_const + 变量侧 ⟹ 约束 λ−SOS=0 给 b = −h_const。"""
        lm = self.lm
        b = {}
        for i in range(self.core.nmon):
            for j in range(self.core.d_H + 1):
                if lm.MA_hA[i][j]:
                    r = self.rowA + i
                    b[r] = b.get(r, F0) - lm.MA_hA[i][j] * self.hA[j]
                if lm.MB_hB[i][j]:
                    r = self.rowB + i
                    b[r] = b.get(r, F0) - lm.MB_hB[i][j] * self.hB[j]
                if lm.MG_hC[i][j]:
                    r = self.rowG + i
                    b[r] = b.get(r, F0) - lm.MG_hC[i][j] * self.hC[j]
        return b

    def build_entries(self):
        core, lm = self.core, self.lm
        acc: dict = {}

        def put(k, l, i, j, v):
            if v:
                acc[(k, l, i, j)] = acc.get((k, l, i, j), F0) + v

        for which, row0 in (("A", self.rowA), ("B", self.rowB), ("G", self.rowG)):
            self._lam_linear(which, row0, put)
            self._f_rows(which, row0, put)
            self._sos_rows(which, row0, put)
        put(0, 1, self.e_pos, self.e_pos, F1)
        if self.lp_penalty:
            eps = self.lp_penalty
            for (pp, mm) in self.vpos.values():
                n_here = (mm - pp + 1) // 2
                for d in range(n_here):
                    put(0, 1, pp + d, pp + d, -eps)
                    put(0, 1, mm + d, mm + d, -eps)
        return [(k, l, i, j, v) for (k, l, i, j), v in acc.items()]

    def _lam_linear(self, which, row0, put):
        lm = self.lm
        mats = {"A": ((lm.MA_psiBa, "psiBa"),),
                "B": ((lm.MB_psiBa, "psiBa"), (lm.MB_psiCb, "psiCb")),
                "G": ((lm.MG_psiCb, "psiCb"),)}[which]

        def uni_mat(Mx, name):
            pp, mm = self.vpos[name]
            for i in range(len(Mx)):
                row = Mx[i]
                for j, v in enumerate(row):
                    if v:
                        put(row0 + i, 1, pp + j, pp + j, v)
                        put(row0 + i, 1, mm + j, mm + j, -v)

        for Mx, name in mats:
            uni_mat(Mx, name)
        const = self.core.ring.index[(0, 0, 0)]
        if which == "A":
            pp, mm = self.vpos["cA"]
            put(row0 + const, 1, pp, pp, lm.MA_cA[const])
            put(row0 + const, 1, mm, mm, -lm.MA_cA[const])
        elif which == "B":
            pp, mm = self.vpos["cB"]
            put(row0 + const, 1, pp, pp, lm.MB_cB[const])
            put(row0 + const, 1, mm, mm, -lm.MB_cB[const])
        else:
            put(row0 + const, 1, self.e_pos, self.e_pos, lm.MG_e[const])
            for nm, vec in (("cA", lm.MG_cA), ("cB", lm.MG_cB)):
                pp, mm = self.vpos[nm]
                put(row0 + const, 1, pp, pp, vec[const])
                put(row0 + const, 1, mm, mm, -vec[const])
            m0 = self.core.F_sizes[0]
            for w_mat, off in ((lm.MG_s111_FP0, self.f_off),
                               (lm.MG_s111_FR0, self.fr_off)):
                w = w_mat[0][0]
                for a_ in range(m0):
                    for b_ in range(a_, m0):
                        put(row0 + const, off, a_ + 1, b_ + 1, w)

    def _f_rows(self, which, row0, put):
        core = self.core
        colsP = {"A": core.KA_P, "B": core.KB_P, "G": None}[which]
        colsR = {"A": core.KA_R, "B": core.KB_R, "G": core.KG_R}[which]
        for cols, side_off in ((colsP, self.f_off), (colsR, self.fr_off)):
            if cols is None:
                continue
            for k in range(core.K):
                mk = core.F_sizes[k]
                for a_ in range(mk):
                    for b_ in range(a_, mk):
                        col = cols[core.Y_index[(k, a_, b_)]]
                        if a_ == b_:
                            for p, c in enumerate(col):
                                if c:
                                    put(row0 + p, side_off + k, a_ + 1, a_ + 1, c)
                        else:
                            colT = cols[core.Y_index[(k, b_, a_)]]
                            sym = [(x + y) / 2 for x, y in zip(col, colT)]
                            for p, c in enumerate(sym):
                                if c:
                                    put(row0 + p, side_off + k, a_ + 1, b_ + 1, c)

    def _sos_rows(self, which, row0, put):
        lm, ring = self.lm, self.core.ring
        blocks_def = {"A": lm.sosA, "B": lm.sosB, "G": lm.sosG}[which]
        base_off = self.sos_off + {"A": 0, "B": len(lm.sosA),
                                   "G": len(lm.sosA) + len(lm.sosB)}[which]
        for bi, (name, gnz, mons) in enumerate(blocks_def):
            l = base_off + bi
            m_ = len(mons)
            for p_ in range(m_):
                ep = mons[p_]
                for q_ in range(p_, m_):
                    eq = mons[q_]
                    base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                    for (eg, cg) in gnz:
                        put(row0 + ring.index[(base[0] + eg[0], base[1] + eg[1],
                                               base[2] + eg[2])], l, p_ + 1, q_ + 1, -cg)

    def b_vector(self):
        b = [F0] * self.m
        for r, v in self.h_const_rows().items():
            b[r - 1] += v
        return b

    def write_dat(self, path: Path):
        E = self.build_entries()
        b = self.b_vector()
        with open(path, "w") as f:
            f.write('"N=9 typed (2,7) strip Hermite-fixed SDP (exact rational)"\n')
            f.write(f"{self.m} = mDIM\n{len(self.blk)} = nBLOCK\n")
            f.write(" ".join(str(s) for s in self.blk) + " = bLOCKsTRUCT\n")
            f.write(" ".join(frac_dec(x) for x in b) + "\n")
            for (k, l, i, j, v) in E:
                f.write(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        return self.m, len(E)


# ============================================================ 条带回读/残差/求解
def solution_from_parse_strip(ex: HermiteStripExporter, parsed: dict,
                              hA, hB, hC, E_cap: Fraction):
    core, lm = ex.core, ex.lm
    lp = parsed["lp"]
    if len(lp) != ex.n_lp:
        fail(f"LP 块长度 {len(lp)} ≠ {ex.n_lp}")
    d_H1 = core.d_H + 1

    def split_get(name):
        pp, mm = ex.vpos[name]
        return [lp[pp - 1 + d] - lp[mm - 1 + d] for d in range(d_H1)]

    def split_scal(name):
        pp, mm = ex.vpos[name]
        return lp[pp - 1] - lp[mm - 1]

    data = dict(hA=list(hA), hB=list(hB), hC=list(hC),
                psiBa=split_get("psiBa"), psiCb=split_get("psiCb"),
                cA=split_scal("cA"), cB=split_scal("cB"), e=lp[ex.e_pos - 1])
    mats = []
    for g in parsed["sdp"]:
        n = len(g)
        if any(len(r) != n for r in g):
            fail("SDP 块非方阵")
        mats.append([[Fraction(x) for x in r] for r in g])
    n_expect = 2 * core.K + len(lm.sosA) + len(lm.sosB) + len(lm.sosG)
    if len(mats) != n_expect:
        fail(f"SDP 块数 {len(mats)} ≠ {n_expect}")
    off = 0
    data["FP"] = mats[off:off + core.K]
    off += core.K
    data["FR"] = mats[off:off + core.K]
    off += core.K
    blocks = {}
    for which, blocks_def, base in (("A", lm.sosA, off),
                                    ("B", lm.sosB, off + len(lm.sosA)),
                                    ("G", lm.sosG, off + len(lm.sosA) + len(lm.sosB))):
        for bi, (name, _g, mons) in enumerate(blocks_def):
            blocks[f"{'BA' if which == 'A' else 'BB' if which == 'B' else 'BG'}_{name}"] \
                = mats[base + bi]
    capped = None
    if data["e"] > E_cap:
        capped = dict(e_raw=str(data["e"]), e_used=str(E_cap))
        data["e"] = E_cap
    return data, dict(blocks=blocks, e_capped=capped)


def raw_residuals_strip(lm: LamMaps, data: dict, blocks: dict) -> dict:
    R1 = {}
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        lv = lm.lam(which, data)
        sv = lm.sos_sum(blocks_def, {name: blocks[f"{prefix}_{name}"]
                                     for name, _g, _m in blocks_def})
        R1[which] = sum(abs(x - y) for x, y in zip(lv, sv))
    return dict(R1=R1)


def strip_tag_of(lo: Fraction, hi: Fraction) -> str:
    from strips_final import strip_tag
    return strip_tag(lo, hi)


def solve_strip_hermite(lo: Fraction, hi: Fraction, M: int, K: int,
                        sdpa_bin: Path, k_minor: int = 48, timeout_s=172800,
                        variant: str = "hermite"):
    tag = strip_tag_of(lo, hi)
    t0 = time.time()
    core = TypedCore(9, M, K)
    lm = LamMaps(core, lo, hi)
    dy = fixed_minorant(k_minor, variant)
    check_variant_fit(variant, M, dy)
    hM = pad_h(dy["coeffs"], core.d_H)
    ex = HermiteStripExporter(core, lm, hM, hM, hM)
    vtag = "" if variant == "hermite" else f"_v2-{variant}"
    workdir = HERE / "results" / "hermite_work" / f"strip_{tag}_M{M}{vtag}"
    workdir.mkdir(parents=True, exist_ok=True)
    dat = workdir / "hermite_strip.dat-s"
    if dat.exists():
        dat.unlink()
    m_dim, n_entries = ex.write_dat(dat)
    (workdir / "param.sdpa").write_text(PARAM_SDPA)
    result = workdir / "hermite_strip.result"
    sol_path = HERE / "results" / f"hermite_strip_sol_{tag}_M{M}{vtag}.json"
    print(f"[export] strip {tag} M={M}: m={m_dim}, entries={n_entries}, "
          f"blocks={len(ex.blk)} (n_lp={ex.n_lp})", flush=True)
    cmd = [str(sdpa_bin), "-ds", str(dat), "-o", str(result),
           "-p", str(workdir / "param.sdpa")]

    def accept(parsed_cand):
        if parsed_cand["info"]["phase_value"] == "pdOPT":
            return True, False
        try:
            E_star_c = load_E_star()
            data_c, extra_c = solution_from_parse_strip(
                ex, parsed_cand, hM, hM, hM, E_star_c + Fraction(5, 100))
            rr_c = raw_residuals_strip(lm, data_c, extra_c["blocks"])
            ok = max(rr_c["R1"].values()) <= STALLED_R1_TOL
            return ok, ok
        except SystemExit:
            return False, False

    reused, parsed, stalled = False, None, False
    if result.exists():
        try:
            cand = parse_result(result)
            ok, st = accept(cand)
            if ok:
                reused, parsed, stalled = True, cand, st
        except SystemExit:
            pass
    if reused:
        info = parsed["info"]
        print(f"[solve] strip {tag}: 复用已有结果 {result}"
              f"（phase={info['phase_value']}）", flush=True)
        solve_s = 0.0
    else:
        if result.exists():
            result.unlink()
        print(f"[solve] strip {tag}: {' '.join(cmd)}", flush=True)
        t1 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              cwd=str(workdir), timeout=timeout_s)
        solve_s = time.time() - t1
        if proc.returncode != 0 or not result.exists():
            fail(f"strip {tag}: sdpa_gmp 退出码 {proc.returncode}："
                 f"{proc.stdout[-1500:]} {proc.stderr[-1500:]}")
        parsed = parse_result(result)
        ok, stalled = accept(parsed)
        if not ok:
            fail(f"strip {tag}: SDPA-GMP 未达 pdOPT 且停滞点回读残差超阈："
                 f"{parsed['info']['phase_value']}")
        info = parsed["info"]
    print(f"[solve] strip {tag}: phase={info['phase_value']} iter={info['iteration']} "
          f"mu={info['mu']:.2e} relgap={info['relative_gap']:.2e} "
          f"p.feas={info['p_feas_error']} d.feas={info['d_feas_error']} "
          f"({solve_s:.0f}s)" + ("；**停滞点认证（可能次优）**" if stalled else ""),
          flush=True)
    E_star = load_E_star()
    E_cap = E_star + Fraction(5, 100)
    data, extra = solution_from_parse_strip(ex, parsed, hM, hM, hM, E_cap)
    blocks = extra["blocks"]
    rr = raw_residuals_strip(lm, data, blocks)
    print(f"[resid] strip {tag}: e = {float(data['e']):.15f}；R1 = "
          f"{ {k2: float(v) for k2, v in rr['R1'].items()} }"
          f"（LamMaps 独立重算；总 {time.time() - t0:.0f}s）", flush=True)
    sol_js = dict(
        tag=tag, lo=str(lo), hi=str(hi), M=M, K=K, minorant_k=k_minor,
        variant=variant,
        e=float(data["e"]),
        exact=dict(hA=[str(x) for x in data["hA"]], hB=[str(x) for x in data["hB"]],
                   hC=[str(x) for x in data["hC"]],
                   psiBa=[str(x) for x in data["psiBa"]],
                   psiCb=[str(x) for x in data["psiCb"]],
                   cA=str(data["cA"]), cB=str(data["cB"]), e=str(data["e"]),
                   FP=[[[str(x) for x in row] for row in m_] for m_ in data["FP"]],
                   FR=[[[str(x) for x in row] for row in m_] for m_ in data["FR"]],
                   **{nm: [[str(x) for x in row] for row in m_]
                      for nm, m_ in blocks.items()}),
        solver_info=dict(route="SDPA-GMP 7.1.3 (GMP 200)", reused=bool(reused),
                         stalled_point=bool(stalled),
                         solve_s=round(solve_s, 1),
                         lp_penalty=str(ex.lp_penalty), **info),
        raw_residuals=dict(R1={k2: str(v) for k2, v in rr["R1"].items()}),
        e_capped=extra["e_capped"],
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    sol_path.write_text(json.dumps(sol_js, ensure_ascii=False))
    print(f"[out] strip {tag}: 解数据 {sol_path.relative_to(REPO)}", flush=True)
    return sol_path, dict(sdpa_info=info, solve_s=round(solve_s, 1),
                          reused=bool(reused), m=m_dim, entries=n_entries)


# ============================================================ 条带认证＋证书
def certify_strip_hermite(core: TypedCore, lm: LamMaps, sol: dict, k: int,
                          hM, spot_seed: int = 97531):
    t0 = time.time()

    def rround(x):
        return dyad(x, k)

    ex = sol["exact"]
    data = dict(hA=list(hM), hB=list(hM), hC=list(hM),
                psiBa=[rround(Fraction(s)) for s in ex["psiBa"]],
                psiCb=[rround(Fraction(s)) for s in ex["psiCb"]],
                cA=rround(Fraction(ex["cA"])), cB=rround(Fraction(ex["cB"])),
                e=dyad(Fraction(ex["e"]), k, floor=True))
    shifts = {}
    for nm in ("FP", "FR"):
        data[nm] = []
        for kk, mk in enumerate(core.F_sizes):
            Mfr, dlt, _t = repair_psd(f"{nm}{kk}", [[rround(Fraction(x)) for x in row]
                                                    for row in ex[nm][kk]], k)
            shifts[f"{nm}{kk}"] = dlt
            data[nm].append(Mfr)
    sos_dy = {}
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        sos_dy[which] = {}
        for name, _g, _m in blocks_def:
            Mfr, dlt, _t = repair_psd(f"{prefix}_{name}",
                                      [[rround(Fraction(x)) for x in row]
                                       for row in ex[f"{prefix}_{name}"]], k)
            shifts[f"{prefix}_{name}"] = dlt
            sos_dy[which][name] = Mfr
    from slab_band import c_gamma
    data["cG"] = c_gamma(core, data)
    R1 = {}
    for which, blocks_def in (("A", lm.sosA), ("B", lm.sosB), ("G", lm.sosG)):
        lv = lm.lam(which, data)
        sv = lm.sos_sum(blocks_def, sos_dy[which])
        R1[which] = sum(abs(x - y) for x, y in zip(lv, sv))
    defl = core.nPPR * R1["A"] + core.nPRR * R1["B"] + core.nRRR * R1["G"]
    certified = data["e"] - defl
    if certified <= 0:
        raise CertError(f"e − defl ≤ 0（{float(certified)}）")
    # 域抽查
    rng = random.Random(spot_seed + k)
    lam_vecs = {w: lm.lam(w, data) for w in "ABG"}
    ring = core.ring
    for which, blocks_def in (("A", lm.sosA), ("B", lm.sosB), ("G", lm.sosG)):
        u_ok = tries = 0
        while tries < 200 and u_ok < 8:
            tries += 1

            def rq(a, b):
                return a + (b - a) * Fraction(rng.randint(0, 64), 64)

            u = rq(lm.lo, lm.hi if which == "A" else F1)
            v = rq(lm.lo, F1)
            t = rq(lm.lo, F1)
            detg = F1 + 2 * u * v * t - u * u - v * v - t * t
            if detg < 0:
                continue
            u_ok += 1
            sos_pt = F0
            for name, gnz, mons in blocks_def:
                Bm = sos_dy[which][name]
                m_ = len(mons)
                zp = [(u ** e2[0]) * (v ** e2[1]) * (t ** e2[2]) for e2 in mons]
                quad = sum(Bm[p][q] * zp[p] * zp[q]
                           for p in range(m_) for q in range(m_))
                g = sum(c * (u ** eg[0]) * (v ** eg[1]) * (t ** eg[2]) for eg, c in gnz)
                if g < 0:
                    raise CertError(f"抽查乘子负值 g_{name} = {g}")
                sos_pt += g * quad
            if sos_pt < 0:
                raise CertError(f"SOS 抽查负值（{which}）")
            if core.eval3(lam_vecs[which], u, v, t) + R1[which] < 0:
                raise CertError(f"λ_{which} 抽查 < −R1")
    print(f"[cert ] strip {sol['tag']}（2^-{k}）：certified = {float(certified):.12f}；"
          f"R1 = { {w: float(R1[w]) for w in 'ABG'} }，defl = {float(defl):.3e}，"
          f"认证链 {time.time() - t0:.0f}s", flush=True)
    return dict(data=data, sos=sos_dy, shifts=shifts, R1=R1, defl=defl,
                certified=certified, k=k)


def write_strip_certificate_h(core: TypedCore, lm: LamMaps, cert_data: dict,
                              tag: str, sol_js: dict, solve_info: dict,
                              out_path: Path, k_minor: int, cmdline: str,
                              variant: str = "hermite"):
    data = cert_data["data"]
    dy = fixed_minorant(k_minor, variant)
    if variant != "hermite":
        vcfg = V2_VARIANTS[variant]
        minorant_prov = dict(
            variant=variant,
            theorem=(f"φ(t) − H_exact(t) = {vcfg['theorem']}；"
                     "M = 区间中点 dyadic − W（W = Σ 半宽；φ ≥ M 于 [−1,1]，"
                     "R8B 相位 0 区间算术证书 hermite_v2_probe_" + variant + ".json）"),
            k=k_minor, W=str(dy["W"]), ncond=dy["ncond"],
            orders=list(dy["orders"]),
            contact_minus1=dy["contact_minus1"],
            remainder=dy["remainder"],
            probe_file=f"results/hermite_v2_probe_{variant}.json")
    else:
        minorant_prov = dict(
            variant=variant,
            theorem=("φ(t) − H_exact(t) = φ^{(12)}(ξ)/12!·∏_k(t−ν_k)² ≥ 0；"
                     "M = 区间中点 dyadic − W"),
            k=k_minor, W=str(dy["W"]), ncond=dy["ncond"],
            orders=list(dy["orders"]),
            contact_minus1=dy["contact_minus1"],
            remainder=dy["remainder"])
    blocks = {"M": [str(x) for x in dy["coeffs"]],
              "e": [str(data["e"])], "cA": [str(data["cA"])],
              "cB": [str(data["cB"])], "cG": [str(data["cG"])]}
    for key in ("psiBa", "psiCb"):
        blocks[f"{key}_diag"] = [str(x) for x in data[key]]
    for nm in ("FP", "FR"):
        for kk in range(core.K):
            blocks[f"{nm}{kk}"] = [[str(x) for x in row] for row in data[nm][kk]]
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        for name, _g, _m in blocks_def:
            blocks[f"{prefix}_{name}"] = [[str(x) for x in row] for row in
                                          cert_data["sos"][which][name]]
    E_star = load_E_star()
    prov = dict(
        code_version=code_version(),
        seed=SEED,
        round_bits=cert_data["k"],
        cmdline=cmdline,
        generator="numerics/bounds/hermite_ladder.py（Hermite 固定 minorant 条带"
                  f"；variant={variant}）",
        upstream=("typed (2,7) 分型条带构造＝slab_band.py（LamMaps 主本）；固定 "
                  "Hermite minorant＝hermite_minorant.py（区间算术 φ ≥ M 于 [−1,1]）"),
        params=dict(N=core.n, M=core.M, K=core.K, d_H=core.d_H, D=core.D,
                    nmon=core.nmon, F_sizes=core.F_sizes,
                    m_lo=str(lm.lo), m_hi=str(lm.hi), round_bits=cert_data["k"],
                    minorant_k=k_minor, variant=variant,
                    counts=dict(PPR=core.nPPR, PRR=core.nPRR, RRR=core.nRRR)),
        minorant=minorant_prov,
        scope=(f"对一切可重排使 (0,1) 为最小内积对且 m = ⟨x_0,x_1⟩ ∈ "
               f"[{lm.lo}, {lm.hi}] 的 {core.n} 点单位球面构型，E(x) ≥ claimed_bound"),
        bound_formula=("certified = e − (nPPR·R1_A + nPRR·R1_B + nRRR·R1_Γ)"
                       "（无 R2：E ≥ ΣM ≥ e − defl，φ ≥ M 全局解析证书）"),
        R1={w: str(v) for w, v in cert_data["R1"].items()},
        deflation_exact=str(cert_data["defl"]),
        psd_shifts={nm: str(d) for nm, d in cert_data["shifts"].items()},
        exact_bound=str(cert_data["certified"]),
        margin_over_E_star=str(cert_data["certified"] - E_star),
        date=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    cert_js = dict(kind=("n9-stage-a5-hermite-strip" if variant == "hermite"
                         else "n9-stage-a5v2-strip"),
                   tag=tag,
                   params=dict(m_lo=str(lm.lo), m_hi=str(lm.hi), M=core.M,
                               K=core.K, variant=variant),
                   blocks=blocks, claimed_bound=str(cert_data["certified"]),
                   provenance=prov)
    out_path.write_text(json.dumps(cert_js, ensure_ascii=False, indent=1))
    return cert_js


def verify_strip_cert_file(path: Path):
    cert = json.loads(path.read_text())
    prm = cert["params"]
    lo, hi = Fraction(prm["m_lo"]), Fraction(prm["m_hi"])
    core = TypedCore(9, prm["M"], prm["K"])
    lm = LamMaps(core, lo, hi)
    b = cert["blocks"]
    k_minor = cert["provenance"]["minorant"]["k"]
    variant = cert["provenance"]["minorant"].get("variant", "hermite")
    dy = fixed_minorant(k_minor, variant)
    check_variant_fit(variant, prm["M"], dy)
    M_coeffs = [Fraction(x) for x in b["M"]]
    if M_coeffs != dy["coeffs"]:
        fail(f"{path.name}: blocks.M ≠ hermite_minorant_dyadic 重构"
             f"（variant={variant}，固定 minorant 被篡改）")
    hM = pad_h(M_coeffs, core.d_H)
    data = dict(hA=hM, hB=hM, hC=hM,
                psiBa=[Fraction(x) for x in b["psiBa_diag"]],
                psiCb=[Fraction(x) for x in b["psiCb_diag"]],
                e=Fraction(b["e"][0]), cA=Fraction(b["cA"][0]),
                cB=Fraction(b["cB"][0]), cG=Fraction(b["cG"][0]),
                FP=[[[Fraction(x) for x in row] for row in b[f"FP{kk}"]]
                    for kk in range(core.K)],
                FR=[[[Fraction(x) for x in row] for row in b[f"FR{kk}"]]
                    for kk in range(core.K)])
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        for name, _g, _m in blocks_def:
            data[f"{prefix}_{name}"] = [[Fraction(x) for x in row]
                                        for row in b[f"{prefix}_{name}"]]
    # 归一化（c_γ 重算须一致）
    from slab_band import c_gamma
    if c_gamma(core, data) != data["cG"]:
        fail(f"{path.name}: c_γ 归一化不一致")
    n_psd = 0
    for nm in ("FP", "FR"):
        for kk in range(core.K):
            if not is_positive_definite(data[f"{nm}{kk}"]):
                fail(f"{path.name}: 块 {nm}{kk} LDLᵀ 非正定")
            n_psd += 1
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        for name, _g, _m in blocks_def:
            if not is_positive_definite(data[f"{prefix}_{name}"]):
                fail(f"{path.name}: 块 {prefix}_{name} LDLᵀ 非正定")
            n_psd += 1
    R1 = {}
    for which, blocks_def in (("A", lm.sosA), ("B", lm.sosB), ("G", lm.sosG)):
        lv = lm.lam(which, data)
        sv = lm.sos_sum(blocks_def, {name: data[f"{'BA' if which == 'A' else 'BB' if which == 'B' else 'BG'}_{name}"]
                                     for name, _g, _m in blocks_def})
        R1[which] = sum(abs(x - y) for x, y in zip(lv, sv))
    defl = core.nPPR * R1["A"] + core.nPRR * R1["B"] + core.nRRR * R1["G"]
    certified = data["e"] - defl
    if certified != Fraction(cert["claimed_bound"]):
        fail(f"{path.name}: 重算 certified {float(certified):.15f} ≠ claimed")
    E_star = load_E_star()
    if not certified > E_star:
        fail(f"{path.name}: certified ≤ E*（条带正裕度断言失败）")
    prov = cert["provenance"]
    for field in ("round_bits", "code_version", "seed"):
        if field not in prov:
            fail(f"{path.name}: provenance 缺 {field}")
    print(f"[vcert] {path.name}: certified = {float(certified):.12f} 重算一致 ✓"
          f"（{n_psd} PSD 块；E* 裕度 {float(certified - E_star):+.3e}）", flush=True)
    return certified


# ============================================================ 条带主流程
def run_strip_hermite(lo_s: str, hi_s: str, M: int, K: int, sdpa_bin: Path,
                      ks=(48, 56, 64), skip_solve=False, k_minor: int = 48,
                      variant: str = "hermite"):
    from strips_final import strip_tag
    lo, hi = Fraction(lo_s), Fraction(hi_s)
    tag = strip_tag(lo, hi)
    E_star = load_E_star()
    core = TypedCore(9, M, K)
    lm = LamMaps(core, lo, hi)
    dy = fixed_minorant(k_minor, variant)
    check_variant_fit(variant, M, dy)
    hM = pad_h(dy["coeffs"], core.d_H)
    vtag = "" if variant == "hermite" else f"_v2-{variant}"
    sol_path = HERE / "results" / f"hermite_strip_sol_{tag}_M{M}{vtag}.json"
    solve_info = None
    if skip_solve:
        if not sol_path.exists():
            fail(f"--skip-solve 但解数据不存在：{sol_path}")
        print(f"[strip] {tag} M={M} variant={variant}：复用解数据 "
              f"{sol_path.relative_to(REPO)}", flush=True)
    else:
        if sol_path.exists():
            print(f"[strip] {tag} M={M} variant={variant}：已有解数据，跳过求解",
                  flush=True)
            solve_info = dict(reused_file=True)
        else:
            sol_path, solve_info = solve_strip_hermite(
                lo, hi, M, K, sdpa_bin, k_minor, variant=variant)
    sol_js = json.loads(sol_path.read_text())
    if variant == "hermite":
        cert_path = REPO / "certificates" / (
            f"n9-stage-a5-hermite-strip-{tag}" + (f"_M{M}.json" if M != 7 else ".json"))
    else:
        cert_path = REPO / "certificates" / f"n9-stage-a5v2-strip-{tag}_M{M}.json"
    cmdline = (f"python3 numerics/bounds/hermite_ladder.py --strip "
               f"\"{lo_s}:{hi_s}\" --M {M} --variant {variant} "
               f"--ks {' '.join(str(x) for x in ks)}")
    last_err = None
    for k in ks:
        try:
            cert_data = certify_strip_hermite(core, lm, sol_js, k, hM)
        except CertError as exc:
            print(f"[retry] strip {tag} 粒度 2^-{k} 未通过：{exc}", flush=True)
            last_err = str(exc)
            continue
        certified = cert_data["certified"]
        row = dict(tag=tag, lo=str(lo), hi=str(hi),
                   cover=f"[{float(lo)},{float(hi)}]", M=M, K=K,
                   variant=variant, minorant_variant=variant,
                   e_raw=sol_js["e"], certified=str(certified),
                   certified_float=float(certified),
                   margin_over_E_star=float(certified - E_star),
                   margin_over_E_star_dec=float(certified - E_STAR_DEC),
                   margin_over_E_star_dec_exact=str(certified - E_STAR_DEC),
                   flips_decimal_E_star=bool(certified > E_STAR_DEC),
                   margin_over_wouldBe=float(certified - WOULD_BE),
                   round_bits=k, minorant_k=k_minor,
                   R1={w: float(v) for w, v in cert_data["R1"].items()},
                   deflation=float(cert_data["defl"]),
                   certificate=str(cert_path.relative_to(REPO)),
                   solution=str(sol_path.relative_to(REPO)),
                   sdpa=sol_js.get("solver_info"), code_version=code_version())
        if not certified > E_star:
            # 正裕度断言失败 ⇒ blocked 记账（不出证书），如实带 best_certified_attempt
            print(f"[strip] {tag} M={M} variant={variant}: certified = "
                  f"{row['certified_float']:.12f} ≤ E*（正裕度断言失败，记 blocked；"
                  f"十进制口径 margin {row['margin_over_E_star_dec']:+.3e}）", flush=True)
            return dict(status="blocked", **row)
        write_strip_certificate_h(core, lm, cert_data, tag, sol_js, solve_info or {},
                                  cert_path, k_minor, cmdline, variant=variant)
        verify_strip_cert_file(cert_path)
        print(f"[strip] {tag} M={M} ✓ certified = {row['certified_float']:.12f}"
              f"（裕度 {row['margin_over_E_star']:+.3e} over E*）", flush=True)
        return dict(status="certified", **row)
    fail(f"strip {tag} M={M}: 全部粒度 {list(ks)} 认证失败（最后：{last_err}）")


# ============================================================ 导出行泛函一致性（防 3h 白跑的笼子）
def _row_functional(entries, lp_vals, mat_vals):
    """SDPA 行泛函。语义（2026-10-05 本机对已解 m0748_M8 实测标定）：
    非对角条目 (i<j) 贡献 2·v·X_ij；对称重复条目（(i,j) 与 (j,i) 都写）
    去重后仍共 2·v·X_ij（替换式合并）。此处按键 (l, min, max) 累加等价
    （我们写的对称重复值相等）。LP 对角贡献 v·x。"""
    func: dict = {}
    seen: dict = {}          # (k,l,mi,mj) → 已计值（对称去重）

    def add(k, val):
        func[k] = func.get(k, F0) + val

    for (k, l, i, j, v) in entries:
        if k == 0:
            continue                                    # 目标/罚（非约束行）
        if l == 1:
            add(k, v * lp_vals[i])
            continue
        mi, mj = (i, j) if i <= j else (j, i)
        key = (k, l, mi, mj)
        if key in seen:
            continue                                    # 对称重复：只计一次
        seen[key] = True
        X = mat_vals[l]
        w = 1 if mi == mj else 2
        add(k, v * w * X[mi - 1][mj - 1])
    return func


def export_row_check_cap(qm: QuotientMaps, ex: HermiteCapExporter, rng) -> dict:
    """随机变量赋值上逐行核对：b[row]＋entries 泛函 == λ_orbit − SOS（QuotientMaps
    独立装配）。导出器的任何行/符号/常数错位在此暴露。"""
    d_H1 = qm.d_H + 1
    psi_AA = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    psi_AB = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    cvals = {n: Fraction(rng.randint(-9, 9), 7) for n in ("c_A", "c_B", "c_C")}
    lp_vals = {ex.e_pos: Fraction(25, 1)}
    for name, vec in (("psi_AA", psi_AA), ("psi_AB", psi_AB)):
        pp, mm = ex.vpos[name]
        for d in range(d_H1):
            lp_vals[pp + d] = vec[d]
            lp_vals[mm + d] = F0                       # ± 拆分只放 ⁺ 侧
    for name in cvals:
        pp, mm = ex.vpos[name]
        lp_vals[pp] = cvals[name]
        lp_vals[mm] = F0
    mat_vals, F_list = {}, []
    for kk, mk in enumerate(qm.F_sizes):
        G = [[Fraction(rng.randint(-6, 6), 4) for _ in range(mk)] for _ in range(mk)]
        Fk = [[sum(G[i][t] * G[j][t] for t in range(mk)) for j in range(mk)]
              for i in range(mk)]
        F_list.append(Fk)
        mat_vals[ex.f_off + kk] = Fk
    B = {}
    for oi, orbit in enumerate(("AAA", "AAB", "ABC")):
        for bi, (name, _g, mons) in enumerate(qm.sos_def):
            m_ = len(mons)
            G = [[Fraction(rng.randint(-6, 6), 4) for _ in range(m_)] for _ in range(m_)]
            Bm = [[sum(G[i][t] * G[j][t] for t in range(m_)) for j in range(m_)]
                  for i in range(m_)]
            B[f"{orbit}_{name}"] = Bm
            mat_vals[ex.sos_off + oi * len(qm.sos_def) + bi] = Bm
    func = _row_functional(ex.build_entries(), lp_vals, mat_vals)
    b = ex.b_vector()
    data = dict(h_AA=ex.h_AA, h_AB=ex.h_AB, psi_AA=psi_AA, psi_AB=psi_AB,
                c_A=cvals["c_A"], c_B=cvals["c_B"], c_C=cvals["c_C"],
                e=lp_vals[ex.e_pos], F=F_list, B=B)
    checked = 0
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: B[f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        row0 = ex.orbit_row[orbit]
        for p in range(qm.nmon):
            # λ − SOS = h_const + Σentries·X = (−b) + func
            lhs = func.get(row0 + p, F0) - b[row0 + p - 1]
            if lhs != lv[p] - sv[p]:
                fail(f"cap 导出行泛函不一致：{orbit} mon #{p}: {lhs} ≠ {lv[p] - sv[p]}")
            checked += 1
    # 归一化行：行泛函应精确等于 3c_A+54c_B+27c_C − e − 9·ΣF^(0)（结构核对，
    # 随机数据下该式非零——它是求解器要满足的约束，不是恒等式）
    r = ex.row_norm
    s111 = sum(sum(row) for row in F_list[0])
    expected = (qm.nrm["c_A"] * cvals["c_A"] + qm.nrm["c_B"] * cvals["c_B"]
                + qm.nrm["c_C"] * cvals["c_C"] + qm.nrm["e"] * lp_vals[ex.e_pos]
                - Fraction(qm.s111_factor) * s111)
    if func.get(r, F0) != expected:
        fail("cap 归一化行泛函与 3cA+54cB+27cC−e−9ΣF 不一致")
    return dict(rows_checked=checked + 1, ok=True)


def export_row_check_strip(core: TypedCore, lm: LamMaps, ex: HermiteStripExporter,
                           rng) -> dict:
    d_H1 = core.d_H + 1
    psiBa = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    psiCb = [Fraction(rng.randint(-9, 9), 7) for _ in range(d_H1)]
    cA, cB = Fraction(rng.randint(-9, 9), 7), Fraction(rng.randint(-9, 9), 7)
    lp_vals = {ex.e_pos: Fraction(25, 1)}
    for name, vec in (("psiBa", psiBa), ("psiCb", psiCb)):
        pp, mm = ex.vpos[name]
        for d in range(d_H1):
            lp_vals[pp + d] = vec[d]
            lp_vals[mm + d] = F0
    for name, val in (("cA", cA), ("cB", cB)):
        pp, mm = ex.vpos[name]
        lp_vals[pp] = val
        lp_vals[mm] = F0
    mat_vals = {}
    data = dict(hA=ex.hA, hB=ex.hB, hC=ex.hC, psiBa=psiBa, psiCb=psiCb,
                cA=cA, cB=cB, e=lp_vals[ex.e_pos])
    for nm, off in (("FP", ex.f_off), ("FR", ex.fr_off)):
        data[nm] = []
        for kk, mk in enumerate(core.F_sizes):
            G = [[Fraction(rng.randint(-6, 6), 4) for _ in range(mk)] for _ in range(mk)]
            Fk = [[sum(G[i][t] * G[j][t] for t in range(mk)) for j in range(mk)]
                  for i in range(mk)]
            data[nm].append(Fk)
            mat_vals[off + kk] = Fk
    blocks = {}
    for which, blocks_def, base in (("A", lm.sosA, ex.sos_off),
                                    ("B", lm.sosB, ex.sos_off + len(lm.sosA)),
                                    ("G", lm.sosG, ex.sos_off + len(lm.sosA)
                                     + len(lm.sosB))):
        for bi, (name, _g, mons) in enumerate(blocks_def):
            m_ = len(mons)
            G = [[Fraction(rng.randint(-6, 6), 4) for _ in range(m_)] for _ in range(m_)]
            Bm = [[sum(G[i][t] * G[j][t] for t in range(m_)) for j in range(m_)]
                  for i in range(m_)]
            prefix = {"A": "BA", "B": "BB", "G": "BG"}[which]
            blocks[f"{prefix}_{name}"] = Bm
            mat_vals[base + bi] = Bm
    func = _row_functional(ex.build_entries(), lp_vals, mat_vals)
    b = ex.b_vector()
    checked = 0
    for which, blocks_def, row0, prefix in (
            ("A", lm.sosA, ex.rowA, "BA"), ("B", lm.sosB, ex.rowB, "BB"),
            ("G", lm.sosG, ex.rowG, "BG")):
        lv = lm.lam(which, data)
        sv = lm.sos_sum(blocks_def, {name: blocks[f"{prefix}_{name}"]
                                     for name, _g, _m in blocks_def})
        for p in range(core.nmon):
            lhs = func.get(row0 + p, F0) - b[row0 + p - 1]
            if lhs != lv[p] - sv[p]:
                fail(f"strip 导出行泛函不一致：λ_{which} mon #{p}: {lhs} ≠ {lv[p] - sv[p]}")
            checked += 1
    return dict(rows_checked=checked, ok=True)


# ============================================================ 自检
def run_selftests():
    t0 = time.time()
    print("[selftest] ① 固定 minorant 有效性（区间构造＋float 采样见证）", flush=True)
    mv = check_minorant_validity(48)
    print(f"[selftest] ① W={float(Fraction(mv['W'])):.3e}, "
          f"spot min={mv['float_spot_min']:.3e} ✓", flush=True)
    print("[selftest] ② cap 固定 h typed 恒等式（(7,6)，随机 ψ/c/F/e × 2，精确 ==0）",
          flush=True)
    qm = QuotientMaps(Fraction(-187, 250), 7, 6)
    rng = random.Random(SEED)
    r2 = exact_identity_selftest_fixed_h(qm, rng, trials=2)
    print(f"[selftest] ② {r2} ✓", flush=True)
    print("[selftest] ③ strip 固定 h slab 恒等式（(7,6) on [−0.90,−0.88]，2 trials）",
          flush=True)
    core = TypedCore(9, 7, 6)
    lm = LamMaps(core, Fraction(-9, 10), Fraction(-22, 25))
    r3 = strip_identity_selftest_fixed_h(core, lm, rng, trials=2)
    print(f"[selftest] ③ {r3} ✓", flush=True)
    print("[selftest] ④ 导出器结构（cap/strip (7,6)：行数/块数/LP 长度）", flush=True)
    dy = fixed_minorant(48)
    hM = pad_h(dy["coeffs"], qm.d_H)
    assert len(hM) == qm.d_H + 1
    ex_cap = HermiteCapExporter(qm, hM, hM)
    st = HERE / "results" / "hermite_work"
    st.mkdir(parents=True, exist_ok=True)
    m1, e1 = ex_cap.write_dat(st / "selftest_cap.dat-s")
    assert m1 == 3 * qm.nmon + 1 and ex_cap.blk[0] == -ex_cap.n_lp, "cap 导出结构不符"
    ex_str = HermiteStripExporter(core, lm, hM, hM, hM)
    m2, e2 = ex_str.write_dat(st / "selftest_strip.dat-s")
    assert m2 == 3 * core.nmon and ex_str.blk[0] == -ex_str.n_lp, "strip 导出结构不符"
    assert len(ex_str.blk) == 1 + 2 * core.K + len(lm.sosA) + len(lm.sosB) + len(lm.sosG)
    print(f"[selftest] ④ cap m={m1} entries={e1} n_lp={ex_cap.n_lp}；"
          f"strip m={m2} entries={e2} n_lp={ex_str.n_lp} ✓", flush=True)
    print("[selftest] ⑤ 导出行泛函 vs QuotientMaps/LamMaps 独立装配（随机赋值逐行精确比对）",
          flush=True)
    r5a = export_row_check_cap(qm, ex_cap, rng)
    r5b = export_row_check_strip(core, lm, ex_str, rng)
    print(f"[selftest] ⑤ cap {r5a}；strip {r5b} ✓", flush=True)
    print(f"[selftest] 完成（{time.time() - t0:.0f}s）", flush=True)
    return dict(minorant=mv, identity=r2, strip_identity=r3,
                row_check_cap=r5a, row_check_strip=r5b)


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="Hermite 引擎 cap/条带（R6-2/R6-3）")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--cap", help="cap 档，如 -0.748")
    ap.add_argument("--strip", help='条带，如 "-0.82:-0.79"')
    ap.add_argument("--M", type=int, default=8)
    ap.add_argument("--K", type=int, default=6)
    ap.add_argument("--ks", type=int, nargs="+", default=[48, 56, 64])
    ap.add_argument("--k-minor", type=int, default=48)
    ap.add_argument("--variant", default="hermite",
                    choices=["hermite", "contact", "triple"],
                    help="固定 minorant 变体（R8B v2：contact=17 条 deg≤16 需"
                         " M≥9；triple=18 条 deg≤17 需 M≥10）")
    ap.add_argument("--skip-solve", action="store_true")
    ap.add_argument("--verify-cert", help="证书独立复核")
    ap.add_argument("--out-cap", default=str(HERE / "results" / "hermite_cap.json"))
    ap.add_argument("--out-strips", default=str(HERE / "results" / "hermite_strips.json"))
    ap.add_argument("--sdpa-bin", default=os.environ.get(
        "SDPA_GMP_BIN", "/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp"))
    args = ap.parse_args()
    sdpa_bin = Path(args.sdpa_bin)

    if args.selftest:
        run_selftests()
        return
    if args.verify_cert:
        p = Path(args.verify_cert)
        if "hermite-cap" in p.name:
            verify_cap_cert_file(p)
        elif "hermite-strip" in p.name or "a5v2-strip" in p.name:
            verify_strip_cert_file(p)
        else:
            fail(f"无法识别证书类型：{p.name}")
        return
    if args.cap:
        if not (sdpa_bin.exists() and os.access(sdpa_bin, os.X_OK)):
            fail(f"sdpa_gmp 不可执行：{sdpa_bin}")
        row = run_cap(args.cap, args.M, args.K, sdpa_bin, ks=tuple(args.ks),
                      skip_solve=args.skip_solve, k_minor=args.k_minor)
        out = Path(args.out_cap)
        db = json.loads(out.read_text()) if out.exists() else {}
        db.setdefault("rungs", [])
        by_key = {f"{r['tag']}_M{r['M']}": r for r in db["rungs"]}
        by_key[f"{row['tag']}_M{row['M']}"] = row
        db["rungs"] = list(by_key.values())
        db["kind"] = "hermite-cap-ladder"
        db["script"] = "hermite_ladder.py"
        db["code_version"] = code_version()
        db["E_star"] = float(load_E_star())
        db["E_ttp_tube"] = float(E_TTP_TUBE)
        db["updated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        out.write_text(json.dumps(db, ensure_ascii=False, indent=1))
        print(f"[out] 已写 {out}", flush=True)
        return
    if args.strip:
        if not (sdpa_bin.exists() and os.access(sdpa_bin, os.X_OK)):
            fail(f"sdpa_gmp 不可执行：{sdpa_bin}")
        lo_s, hi_s = args.strip.split(":")
        row = run_strip_hermite(lo_s, hi_s, args.M, args.K, sdpa_bin,
                                ks=tuple(args.ks), skip_solve=args.skip_solve,
                                k_minor=args.k_minor, variant=args.variant)
        out = Path(args.out_strips)
        db = json.loads(out.read_text()) if out.exists() else {}
        db.setdefault("strips", [])
        by_key = {f"{r['tag']}_M{r['M']}_{r.get('variant', 'hermite')}": r
                  for r in db["strips"]}
        by_key[f"{row['tag']}_M{row['M']}_{row.get('variant', 'hermite')}"] = row
        db["strips"] = list(by_key.values())
        db["kind"] = "hermite-strips"
        db["script"] = "hermite_ladder.py"
        db["code_version"] = code_version()
        db["E_star"] = float(load_E_star())
        db["wouldBe_reference"] = float(WOULD_BE)
        db["updated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        out.write_text(json.dumps(db, ensure_ascii=False, indent=1))
        print(f"[out] 已写 {out}", flush=True)
        return
    ap.error("需要 --selftest / --cap / --strip / --verify-cert")


if __name__ == "__main__":
    main()
