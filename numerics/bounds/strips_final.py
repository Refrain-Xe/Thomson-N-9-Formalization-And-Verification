#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""strips_final.py — N=9 typed 条带证书（Round 4）：最小内积 m ∈ [lo,hi] ⊆ [−0.90,−0.748]。

## 为什么是条带、为什么用 (2,7) 分型构造

cap 证书（typed_ladder.py 的 (3,3,3) S₃ 商）盖 m ≥ a₀，切口含 TTP（m* =
−0.7475605 > −0.748）时 SDP 值恒 ≤ E*、无正裕度。条带 [lo,hi] 用**上下双切口**
排除 TTP：域条件 (0,1) 为最小内积对且 lo ≤ u=⟨x₀,x₁⟩ ≤ hi。这要求**指定极小对**
的分型构造（类型 P＝{0,1}、环 R＝其余 7，PAPER.md §6.4 域机制）——即
slab_band.py 的 (2,7) 商（Round 2 已在 [−1,−0.90] 认证 5 片）。本文件把同一
构造推进到 [−0.90,−0.748]，求解换成 SDPA-GMP 高精度路线（Round 3 条带可行性
研究的保留项：Clarabel 折减 1e-4~2e-3 会吃掉第 3 片起的全部裕度）。

## 管线（与 typed_ladder.py 的 SDPA-GMP 路线同约定）

  1) TypedCore/LamMaps（slab_band.py 的纯 Fraction 主本，构造/自检已被
     Round 2 的 5 份 slab 证书与 N=7 校准背书）；
  2) SDPAExporterStrip（本文件新写）：商 SDP 的 .dat-s 精确有理导出——
     LP 对角块（e；h/ψ/c ± 拆分＋1e-11 罚锚定零空间）＋F 块 2K＋SOS 块
     6+5+5（λ_A 含上切口 hi−u 块——条带机制所在）＋minorant 块 6+4+4
     （τ＝H_A 双侧 [c,b]）；
  3) SDPA-GMP 7.1.3（GMP 200 位）求解，.result 66 位十进制精确回读；
     回读解用 LamMaps **独立重算**恒等式残差（R1/R2 ≈ 求解器残差水平 1e-30
     量级）⟹ 导出正确性的逐条核验（导出行≠LamMaps 装配时立刻暴露）；
  4) 认证 = slab_band.certify_slab：dyadic 舍入（sdp_certify.dyad，exact.py
     LDLᵀ PSD 修复）→ 纯 Fraction 残差 → certified =
     (e − (7R1_A+42R1_B+35R1_Γ))/(1+R2max) → **assert certified > E***
     （正裕度，条带不含 TTP；违反 fail()→sys.exit(1)）；
  5) 证书 certificates/n9-stage-a4-strip-<tag>.json（thomson_certs schema，
     全 'p/q'），回读 decode→rebuild→recompute 逐位比对。

  证书有效性只依赖 4)（从舍入数据 exact 重推），导出/求解错误只会导致认证
  失败或界变弱，不会产生假证书——这是把新导出器风险关在笼子里的机制。

## 预算纪律（Round 4 任务书）

  (7,6) 起步；某片不够升 (8,6) 重做，全轮 (8,6) ≤3 次。条带可行性实测
  （typed_ladder.json stripFeasibility.M7）：(7,6) 地板 ≈ E*−1.3e-3，hi ≲ −0.84
  的片在 (7,6) 不可行。

用法（thomson-n9 下；SDPA 求解 >10 分钟，建议后台＋轮询）：
  numerics/.venv/bin/python numerics/bounds/strips_final.py --selftest
  numerics/.venv/bin/python numerics/bounds/strips_final.py --triage "-0.90:-0.88,..."  # Clarabel 侦察
  numerics/.venv/bin/python numerics/bounds/strips_final.py --strip "-0.90:-0.88" [--M 7]
  numerics/.venv/bin/python numerics/bounds/strips_final.py --verify-cert certificates/n9-stage-a4-strip-m090-m088.json
"""
from __future__ import annotations

import argparse
import json
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
sys.path.insert(0, str(WORKFLOW_CERTS))

from slab_band import (TypedCore, LamMaps, certify_slab, c_gamma,     # noqa: E402
                       rebuild_from_params, recompute_certified,
                       exact_typed_identity_selftest,
                       exact_typed_positivity_selftest)
from typed_ladder import frac_dec, parse_result, PARAM_SDPA           # noqa: E402
from thomson_certs.exact import is_positive_definite                  # noqa: E402
from thomson_certs.schema import (Certificate, decode_certificate,   # noqa: E402
                                  encode_certificate, fraction_to_str)

F0, F1 = Fraction(0), Fraction(1)
E_STAR_FALLBACK = 25.759986531
DEFAULT_STRIPS = [("-0.90", "-0.88"), ("-0.88", "-0.85"), ("-0.85", "-0.82"),
                  ("-0.82", "-0.79"), ("-0.79", "-0.765"), ("-0.765", "-0.748")]
# 条带解封顶：条带不含 TTP，e 可合法超过 E*（正裕度是任务目标），
# 只在明显异常（>E*+0.05）时截断防读回事故。
E_CAP_MARGIN = Fraction(5, 100)


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    """证书/结果 provenance 的代码版本（git describe --always --dirty）。"""
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


def load_E_star() -> Fraction:
    p = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"
    try:
        with open(p) as f:
            return Fraction(json.load(f)["energies"]["9"]["value"])
    except Exception as exc:
        print(f"[warn] energies.json 不可读（{exc}），用常数 {E_STAR_FALLBACK}",
              flush=True)
        return Fraction(E_STAR_FALLBACK)


def strip_tag(lo: Fraction, hi: Fraction) -> str:
    """端点十进制标签：−0.90→m090、−0.765→m0765（去尾零、左补零到 3 位）。"""
    def dec(x: Fraction) -> str:
        s = frac_dec(-x, 12)         # 条带端点均为负
        digits = s.split(".")[1].rstrip("0")
        if len(digits) < 2:          # 0.9→"90"（两位起步），再左补零到 3 位
            digits += "0" * (2 - len(digits))
        return "m" + digits.zfill(3)
    return f"{dec(lo)}-{dec(hi)}"


# ============================================================ SDPA 导出（条带商 SDP）
class SDPAExporterStrip:
    """slab_band 商 SDP 的 .dat-s 精确有理导出（typed_ladder.SDPAExporter 同约定）。

    变量布局：LP 对角块（位置 1＝e⁺；hA/hB/hC/psiBa/psiCb ± 各 d_H+1；cA/cB ±）
    ＋F_P 0..K-1 ＋F_R 0..K-1 ＋BA(6)/BB(5)/BG(5) SOS 块 ＋tauA(6)/sigB(4)/sigC(4)。
    行：λ_A/λ_B/λ_Γ 恒等式各 nmon 行 ＋ minorant A/B/C 各 deg_p+1 行（b=p_const）。
    c_γ 已在 LamMaps 中消元进 λ_Γ（MG_e/MG_cA/MG_cB/MG_s111_*），无独立归一化行。
    """

    def __init__(self, core: TypedCore, lm: LamMaps,
                 lp_penalty=Fraction(1, 10 ** 11)):
        self.core, self.lm, self.lp_penalty = core, lm, lp_penalty
        d_H1 = core.d_H + 1
        pos = 1
        self.e_pos = 1
        pos += 1
        self.vpos = {}
        for name in ("hA", "hB", "hC", "psiBa", "psiCb"):
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
                    + [len(m) for _n, _g, m in lm.sosG]
                    + [len(mm) for _n, mm, _mu in lm.tau_def]
                    + [len(mm) for _n, mm, _mu in lm.sig_def]
                    + [len(mm) for _n, mm, _mu in lm.sig_def])
        self.f_off = 2                                  # 块 1 = LP
        self.fr_off = self.f_off + K
        self.sos_off = self.fr_off + K
        self.tau_off = self.sos_off + len(lm.sosA) + len(lm.sosB) + len(lm.sosG)
        self.sig_off = self.tau_off + len(lm.tau_def)
        nmon = core.nmon
        self.rowA, self.rowB, self.rowG = 1, 1 + nmon, 1 + 2 * nmon
        self.minor_row = {"A": 1 + 3 * nmon,
                          "B": 1 + 3 * nmon + (lm.deg_p + 1),
                          "C": 1 + 3 * nmon + 2 * (lm.deg_p + 1)}
        # 无独立归一化行（c_γ 已消元进 λ_Γ），故 m 不加 1——空行会让
        # SDPA 正规方程奇异（iter0 cholesky miss，2026-10-04 实测）
        self.m = 3 * nmon + 3 * (lm.deg_p + 1)

    # ---------------- 行条目 ----------------
    def build_entries(self):
        core, lm, ring = self.core, self.lm, self.core.ring
        acc: dict = {}

        def put(k, l, i, j, v):
            if v:
                acc[(k, l, i, j)] = acc.get((k, l, i, j), F0) + v

        for which, row0 in (("A", self.rowA), ("B", self.rowB), ("G", self.rowG)):
            self._lam_linear(which, row0, put)
            self._f_rows(which, row0, put)
            self._sos_rows(which, row0, put)
        for X in ("A", "B", "C"):
            self._minor_rows(X, put)
        put(0, 1, self.e_pos, self.e_pos, F1)           # 目标 max e
        # LP ± 拆分零空间锚定（typed_ladder 实测规避 dFEAS 崩溃；读回 e⁺ 对原
        # 行精确可行，认证零损失，最优值至多低 ε·Σ|±| ~ 1e-8）
        if self.lp_penalty:
            eps = self.lp_penalty
            for (pp, mm) in self.vpos.values():
                n_here = (mm - pp + 1) // 2
                for d in range(n_here):
                    put(0, 1, pp + d, pp + d, -eps)
                    put(0, 1, mm + d, mm + d, -eps)
        return [(k, l, i, j, v) for (k, l, i, j), v in acc.items()]

    def _lam_linear(self, which, row0, put):
        """λ_which 的 h/ψ/c/e 线性侧（符号照 LamMaps 装配矩阵原样）。"""
        lm, ring = self.lm, self.core.ring
        mats = {"A": ((lm.MA_hA, "hA"), (lm.MA_psiBa, "psiBa")),
                "B": ((lm.MB_hB, "hB"), (lm.MB_psiBa, "psiBa"),
                      (lm.MB_psiCb, "psiCb")),
                "G": ((lm.MG_hC, "hC"), (lm.MG_psiCb, "psiCb"))}[which]

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
        const = ring.index[(0, 0, 0)]
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
            # s111 常数矩阵（每个元素同值 w → 全 (a,b) 裸写，含 a<b：
            # SDPA 非对角翻倍恰还原 Σ_{a,b} w·F_ab）
            m0 = self.core.F_sizes[0]
            for w_mat, off in ((lm.MG_s111_FP0, self.f_off),
                               (lm.MG_s111_FR0, self.fr_off)):
                w = w_mat[0][0]
                for a_ in range(m0):
                    for b_ in range(a_, m0):
                        put(row0 + const, off, a_ + 1, b_ + 1, w)

    def _f_rows(self, which, row0, put):
        """λ_which 的 F 侧（K 列＝Y 列＋share 的 gm 提升；(a<b) 对称化 (W+Wᵀ)/2）。"""
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
        """−Σ_r g_r·z_rᵀB_r z_r（p≤q 裸系数，SDPA 非对角翻倍）。"""
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

    def _minor_rows(self, X, put):
        lm, core = self.lm, self.core
        blocks_def, off, hname = {
            "A": (lm.tau_def, self.tau_off, "hA"),
            "B": (lm.sig_def, self.sig_off, "hB"),
            "C": (lm.sig_def, self.sig_off + len(lm.sig_def), "hC")}[X]
        row0 = self.minor_row[X]
        pp, mm = self.vpos[hname]
        for bi, (name, mons_y, mult) in enumerate(blocks_def):
            l = off + bi
            m_ = len(mons_y)
            for p_ in range(m_):
                for q_ in range(p_, m_):
                    base = mons_y[p_] + mons_y[q_]
                    for (eg, cg) in mult:
                        put(row0 + base + eg, l, p_ + 1, q_ + 1, cg)
        for r in range(lm.deg_p + 1):
            for j in range(core.d_H + 1):
                v = lm.Cp[r][j]
                if v:
                    put(row0 + r, 1, pp + j, pp + j, -v)
                    put(row0 + r, 1, mm + j, mm + j, v)

    def b_vector(self):
        b = [F0] * self.m
        for X in ("A", "B", "C"):
            row0 = self.minor_row[X]
            for r in range(self.lm.deg_p + 1):
                b[row0 - 1 + r] = self.lm.p_const[r]
        return b

    def write_dat(self, path: Path):
        E = self.build_entries()
        b = self.b_vector()
        with open(path, "w") as f:
            f.write('"N=9 typed (2,7) strip SDP (exact rational coefficients)"\n')
            f.write(f"{self.m} = mDIM\n{len(self.blk)} = nBLOCK\n")
            f.write(" ".join(str(s) for s in self.blk) + " = bLOCKsTRUCT\n")
            f.write(" ".join(frac_dec(x) for x in b) + "\n")
            for (k, l, i, j, v) in E:
                f.write(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        return self.m, len(E)


# ============================================================ 回读与独立残差核验
def solution_from_parse(ex: SDPAExporterStrip, parsed: dict,
                        E_cap: Fraction) -> tuple[dict, dict]:
    """yMat → slab_band.sol 同构数据（Fraction）＋ SOS/minorant 块表。"""
    core, lm = ex.core, ex.lm
    lp = parsed["lp"]
    if len(lp) != ex.n_lp:
        fail(f"LP 块长度 {len(lp)} ≠ {ex.n_lp}")
    d_H1 = core.d_H + 1

    def split_get(name):
        pp, mm = ex.vpos[name]
        if name in ("hA", "hB", "hC", "psiBa", "psiCb"):
            return [lp[pp - 1 + d] - lp[mm - 1 + d] for d in range(d_H1)]
        return lp[pp - 1] - lp[mm - 1]

    data = dict(hA=split_get("hA"), hB=split_get("hB"), hC=split_get("hC"),
                psiBa=split_get("psiBa"), psiCb=split_get("psiCb"),
                cA=split_get("cA"), cB=split_get("cB"),
                e=lp[ex.e_pos - 1])
    mats = []
    for g in parsed["sdp"]:
        n = len(g)
        if any(len(r) != n for r in g):
            fail("SDP 块非方阵")
        mats.append([[Fraction(x) for x in r] for r in g])
    n_expect = (2 * core.K + len(lm.sosA) + len(lm.sosB) + len(lm.sosG)
                + len(lm.tau_def) + 2 * len(lm.sig_def))
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
            m_ = mats[base + bi]
            if len(m_) != len(mons):
                fail(f"B_{which}_{name} 尺寸不符")
            blocks[f"{'BA' if which == 'A' else 'BB' if which == 'B' else 'BG'}_{name}"] = m_
    off += len(lm.sosA) + len(lm.sosB) + len(lm.sosG)
    for X, blocks_def, base, prefix in (
            ("A", lm.tau_def, off, "tauA"),
            ("B", lm.sig_def, off + len(lm.tau_def), "sigB"),
            ("C", lm.sig_def, off + len(lm.tau_def) + len(lm.sig_def), "sigC")):
        for bi, (name, _my, _mu) in enumerate(blocks_def):
            m_ = mats[base + bi]
            if len(m_) != len(_my):
                fail(f"{prefix}_{name} 尺寸不符")
            blocks[f"{prefix}_{name}"] = m_
    capped = None
    if data["e"] > E_cap:
        capped = dict(e_raw=str(data["e"]), e_used=str(E_cap))
        data["e"] = E_cap
    return data, dict(blocks=blocks, e_capped=capped)


def raw_residuals_strip(lm: LamMaps, data: dict, blocks: dict) -> dict:
    """回读解经 LamMaps 独立装配重算的精确恒等式残差（导出正确性核验）。"""
    R1 = {}
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        lv = lm.lam(which, data)
        sv = lm.sos_sum(blocks_def, {name: blocks[f"{prefix}_{name}"]
                                     for name, _g, _m in blocks_def})
        R1[which] = sum(abs(x - y) for x, y in zip(lv, sv))
    R2 = {}
    for X, blocks_def, prefix, hkey in (("A", lm.tau_def, "tauA", "hA"),
                                        ("B", lm.sig_def, "sigB", "hB"),
                                        ("C", lm.sig_def, "sigC", "hC")):
        lhs = lm.minorant_lhs(blocks_def, {name: blocks[f"{prefix}_{name}"]
                                           for name, _my, _mu in blocks_def})
        rhs = lm.minorant_rhs(data[hkey])
        rr = [x - y for x, y in zip(rhs, lhs)]
        R2[X] = sum(abs(rr[j]) * lm.w_hat ** j for j in range(len(rr)))
    return dict(R1=R1, R2=R2)


# ============================================================ 求解
def solve_strip(lo: Fraction, hi: Fraction, M: int, K: int, sdpa_bin: Path,
                timeout_s=172800):
    """timeout 21600→172800（D20）：M8→M9 维度比 ~1.41 ⇒ 每 iter ~2.8×，
    实测 M8 Lukács 条带 ~10100s ⇒ M9 外推 ~8h，超旧 6h 上限会杀健康求解。"""
    """导出 + SDPA-GMP 求解 + 回读 + 独立残差核验 + 解数据落盘。"""
    tag = strip_tag(lo, hi)
    t0 = time.time()
    core = TypedCore(9, M, K)
    lm = LamMaps(core, lo, hi)
    ex = SDPAExporterStrip(core, lm)
    workroot = HERE / "results" / "strip_work"
    workdir = workroot / f"{tag}_M{M}"
    workdir.mkdir(parents=True, exist_ok=True)
    dat = workdir / "strip.dat-s"
    if dat.exists():
        dat.unlink()
    m_dim, n_entries = ex.write_dat(dat)
    (workdir / "param.sdpa").write_text(PARAM_SDPA)
    result = workdir / "strip.result"
    sol_path = HERE / "results" / f"strip_sol_{tag}_M{M}.json"
    print(f"[export] {tag} M={M}: m={m_dim}, entries={n_entries}, "
          f"blocks={len(ex.blk)} (n_lp={ex.n_lp})", flush=True)
    cmd = [str(sdpa_bin), "-ds", str(dat), "-o", str(result),
           "-p", str(workdir / "param.sdpa")]
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
        t1 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              cwd=str(workdir), timeout=timeout_s)
        solve_s = time.time() - t1
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
    data, extra = solution_from_parse(ex, parsed, E_star + E_CAP_MARGIN)
    blocks = extra["blocks"]
    rr = raw_residuals_strip(lm, data, blocks)
    print(f"[resid] {tag}: e = {float(data['e']):.15f}；R1 = "
          f"{ {k: float(v) for k, v in rr['R1'].items()} }，R2 = "
          f"{ {k: float(v) for k, v in rr['R2'].items()} }"
          f"（LamMaps 独立重算；总 {time.time() - t0:.0f}s）", flush=True)
    sol_js = dict(
        tag=tag, lo=str(lo), hi=str(hi), M=M, K=K,
        e=float(data["e"]),
        exact=dict(hA=[str(x) for x in data["hA"]],
                   hB=[str(x) for x in data["hB"]], hC=[str(x) for x in data["hC"]],
                   psiBa=[str(x) for x in data["psiBa"]],
                   psiCb=[str(x) for x in data["psiCb"]],
                   cA=str(data["cA"]), cB=str(data["cB"]), cG=str(c_gamma(core, data)),
                   e=str(data["e"]),
                   FP=[[[str(x) for x in row] for row in m_] for m_ in data["FP"]],
                   FR=[[[str(x) for x in row] for row in m_] for m_ in data["FR"]],
                   **{nm: [[str(x) for x in row] for row in m_]
                      for nm, m_ in blocks.items()}),
        solver_info=dict(route="SDPA-GMP 7.1.3 (GMP 200)", reused=bool(reused),
                         solve_s=round(solve_s, 1),
                         lp_penalty=str(ex.lp_penalty), **info),
        raw_residuals=dict(R1={k: str(v) for k, v in rr["R1"].items()},
                           R2={k: str(v) for k, v in rr["R2"].items()}),
        e_capped=extra["e_capped"],
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    sol_path.write_text(json.dumps(sol_js, ensure_ascii=False))
    print(f"[out] {tag}: 解数据 {sol_path.relative_to(REPO)}", flush=True)
    return sol_path, dict(sdpa_info=info, solve_s=round(solve_s, 1),
                          reused=bool(reused), m=m_dim, entries=n_entries)


def sol_to_certify_input(sol_js: dict) -> dict:
    """解 json → certify_slab 需要的 sol dict（全 float 可转对象）。"""
    ex = sol_js["exact"]
    out = dict(hA=[Fraction(x) for x in ex["hA"]], hB=[Fraction(x) for x in ex["hB"]],
               hC=[Fraction(x) for x in ex["hC"]],
               psiBa=[Fraction(x) for x in ex["psiBa"]],
               psiCb=[Fraction(x) for x in ex["psiCb"]],
               e=Fraction(ex["e"]), cA=Fraction(ex["cA"]), cB=Fraction(ex["cB"]),
               FP=[[[Fraction(x) for x in row] for row in m_] for m_ in ex["FP"]],
               FR=[[[Fraction(x) for x in row] for row in m_] for m_ in ex["FR"]])
    for k, v in ex.items():
        if k in out or k in ("cG", "e", "hA", "hB", "hC", "psiBa", "psiCb",
                             "cA", "cB", "FP", "FR"):
            continue
        out[k] = [[Fraction(x) for x in row] for row in v]
    return out


# ============================================================ 证书写出（条带版）
def write_strip_certificate(core: TypedCore, lm: LamMaps, cert_data: dict,
                            E_star: Fraction, tag: str, sol_js: dict,
                            solve_info: dict, out_path: Path, cmdline: str):
    d_H = core.d_H
    data = cert_data["data"]
    blocks = {"e": [[fraction_to_str(data["e"])]],
              "cA": [[fraction_to_str(data["cA"])]],
              "cB": [[fraction_to_str(data["cB"])]],
              "cG": [[fraction_to_str(c_gamma(core, data))]]}
    for key in ("hA", "hB", "hC", "psiBa", "psiCb"):
        blocks[f"{key}_diag"] = [[fraction_to_str(data[key][j]) if i == j else "0"
                                  for j in range(d_H + 1)] for i in range(d_H + 1)]
    for nm in ("FP", "FR"):
        for kk in range(core.K):
            blocks[f"{nm}{kk}"] = [[fraction_to_str(x) for x in row]
                                   for row in data[nm][kk]]
    for which, blocks_def, prefix in (("A", lm.sosA, "BA"), ("B", lm.sosB, "BB"),
                                      ("G", lm.sosG, "BG")):
        for name, _g, _m in blocks_def:
            blocks[f"{prefix}_{name}"] = [[fraction_to_str(x) for x in row]
                                          for row in cert_data["sos"][which][name]]
    for X, blocks_def, prefix in (("A", lm.tau_def, "tauA"), ("B", lm.sig_def, "sigB"),
                                  ("C", lm.sig_def, "sigC")):
        for name, _my, _mu in blocks_def:
            blocks[f"{prefix}_{name}"] = [[fraction_to_str(x) for x in row]
                                          for row in cert_data["mino"][X][name]]
    certified = cert_data["certified"]
    prov = {
        "repo": "thomson-n9",
        "code_version": code_version(),
        "generator": "numerics/bounds/strips_final.py（SDPA-GMP 高精度路线）",
        "date": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "upstream": ("typed (2,7) 分型条带构造＝slab_band.py（Round 2 在 [−1,−0.90] "
                     "认证 5 片的同构实现，N=7 校准背书）；构造移植自 "
                     "references/thomson-n7-lean/paper/PAPER.md §6–7.1；"
                     "SDPA-GMP 管线同 typed_ladder.py/hp_solve.py；"
                     "exact.py LDLᵀ＋schema.py 交接"),
        "params": {
            "N": core.n, "M": core.M, "K": core.K, "d_H": d_H, "D": core.D,
            "nmon": core.nmon, "F_sizes": core.F_sizes,
            "m_lo": fraction_to_str(lm.lo), "m_hi": fraction_to_str(lm.hi),
            "b2": fraction_to_str(lm.b2), "c2": fraction_to_str(lm.c2),
            "w_hat": fraction_to_str(lm.w_hat), "round_bits": cert_data["k"],
            "counts": dict(PPR=core.nPPR, PRR=core.nPRR, RRR=core.nRRR,
                           pairA=1, pairB=2 * core.ring_n,
                           pairC=core.ring_n * (core.ring_n - 1) // 2),
            "shares": (f"pair A @ring ×{core.dA}：Ψ_A/{core.dA}；pair B @pole ψ_Ba、"
                       f"@ring ×{core.dB}：(Ψ_B−ψ_Ba)/{core.dB}；pair C @pole ×2 ψ_Cb、"
                       f"@ring ×{core.dC}：(Ψ_C−2ψ_Cb)/{core.dC}"),
            "constant_condition": (f"{core.nPPR}·c_α+{core.nPRR}·c_β+{core.nRRR}·c_γ "
                                   f"= e + 2·s_P(1,1,1) + {core.ring_n}·s_R(1,1,1)"),
            "scope": (f"对一切可重排使 (0,1) 为最小内积对且 m = ⟨x_0,x_1⟩ ∈ "
                      f"[{fraction_to_str(lm.lo)}, {fraction_to_str(lm.hi)}] 的 "
                      f"{core.n} 点单位球面构型，E(x) ≥ claimed_bound。"
                      f"候选 TTP（m* = −0.7475605）不在域内——正裕度的来源"),
            "blocks_map": ("e/cA/cB/cG＝标量；hA/hB/hC/psiBa/psiCb_diag 对角线＝多项式"
                           "系数（t^0..t^d_H）；FP0..FP{K-1}/FR0..FR{K-1}＝F 块；"
                           "BA_/BB_/BG_＋乘子名＝λ SOS Gram（乘子 1,u−lo,v−lo,t−lo,"
                           "hi-u(仅 A),detG，单项式表由 D 定）；tauA_/sigB_/sigC_＝"
                           "minorant Lukács 块（H_A 双侧 [c,b]，H_B/H_C 单侧 [0,b]）"),
            "bound_formula": (
                "certified = (e − (nPPR·R1_A + nPRR·R1_B + nRRR·R1_Γ)) / (1 + R2_max)。"
                "推导：typed 组合恒等式 Σ_{i<j}H_cls − e = Σ_T λ_T + Σ_all（精确自检）；"
                "Σ_all ≥ 0（F ⪰ 0 LDLᵀ 已验 ＋ 引理 4.1 逐根正性）；λ_X ≥ −R1_X 于域"
                "（SOS ≥ 0 ＋ |resid| ≤ ‖resid‖₁，|u|,|v|,|t| ≤ 1）⇒ ΣH ≥ e − 膨胀；"
                "1−2yH_X(1−2y²) ≥ −R2_X 于 y 域（块 ⪰ 0）⇒ H_X ≤ (1+R2_max)·φ ⇒ "
                "E = Σφ ≥ ΣH/(1+R2_max) ≥ certified"),
            "R1": {w: fraction_to_str(cert_data["R1"][w]) for w in "ABG"},
            "R2": {X: fraction_to_str(cert_data["R2"][X]) for X in "ABC"},
            "deflation_exact": fraction_to_str(cert_data["deflation"]),
            "R2max_exact": fraction_to_str(cert_data["R2max"]),
            "psd_shifts": {nm: fraction_to_str(d)
                           for nm, d in cert_data["shifts"].items()},
        },
        "numerical_bound": {"e_raw": sol_js.get("e"),
                            "solver": solve_info.get("sdpa_info", {}).get(
                                "phase_value") and "SDPA-GMP 7.1.3",
                            "raw_residuals_max": max(
                                [abs(float(Fraction(v))) for v in
                                 sol_js["raw_residuals"]["R1"].values()]
                                + [abs(float(Fraction(v))) for v in
                                   sol_js["raw_residuals"]["R2"].values()])},
        "exact_bound": fraction_to_str(certified),
        "margin_over_E_star": fraction_to_str(certified - E_star),
        "checks": {
            "exact_typed_combination_identity_random_rational": True,
            "exact_lemma4_1_typed_positivity_random_rational": True,
            "all_blocks_exact_ldlt_positive_definite": True,
            "lam_spot_checks_domain": cert_data["spot"],
            "certified_gt_E_star_positive_margin": True,
            "readback_recompute_bitwise": True,
        },
        "repro": cmdline,
    }
    cert_obj = Certificate(m_lo=fraction_to_str(lm.lo), m_hi=fraction_to_str(lm.hi),
                           blocks=blocks, claimed_bound=fraction_to_str(certified),
                           provenance=prov)
    text = encode_certificate(cert_obj)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text)
    rt = decode_certificate(out_path.read_text())
    rt_core, rt_lm = rebuild_from_params(rt)
    rt_certified = recompute_certified(rt_core, rt_lm, rt)
    if rt_certified != certified:
        fail(f"[{tag}] 回读重算不一致：{rt_certified} ≠ {certified}")
    if encode_certificate(rt) != text:
        fail(f"[{tag}] 回读再编码不逐字节一致")
    for name, mat in rt.blocks.items():
        if name.endswith("_diag") or name in ("e", "cA", "cB", "cG"):
            continue
        if not is_positive_definite([[Fraction(x) for x in row] for row in mat]):
            fail(f"[{tag}] 块 {name} LDLᵀ 非正定")
    print(f"[{tag}] 证书写入 {out_path.relative_to(REPO)}（{len(text)} 字节）；"
          f"回读重算逐位一致 ✓ 全块 LDLᵀ ✓", flush=True)
    return out_path


# ============================================================ 独立复核
def verify_cert_file(path: Path):
    rt = decode_certificate(path.read_text())
    core, lm = rebuild_from_params(rt)
    certified = recompute_certified(core, lm, rt)
    E_star = load_E_star()
    print(f"[verify] {path.name}: certified = {float(certified):.12f} "
          f"（重算 vs 声称：{certified == Fraction(rt.claimed_bound)}；"
          f"E* 裕度 {float(certified - E_star):+.3e}）", flush=True)
    if certified != Fraction(rt.claimed_bound):
        fail("重算与 claimed_bound 不一致")
    if not certified > E_star:
        fail("certified ≤ E*（条带正裕度断言失败）")
    n_psd = 0
    for name, mat in rt.blocks.items():
        if name.endswith("_diag") or name in ("e", "cA", "cB", "cG"):
            continue
        if not is_positive_definite([[Fraction(x) for x in row] for row in mat]):
            fail(f"块 {name} LDLᵀ 非正定")
        n_psd += 1
    print(f"[verify] {path.name}: {n_psd} 个 PSD 块 LDLᵀ 全正定 ✓", flush=True)


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="N=9 typed 条带证书（Round 4）")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--triage", help="Clarabel 侦察（逗号分隔 lo:hi 列表），不认证")
    ap.add_argument("--strip", help="单片全流程，如 \"-0.90:-0.88\"")
    ap.add_argument("--M", type=int, default=7)
    ap.add_argument("--K", type=int, default=6)
    ap.add_argument("--ks", type=int, nargs="+", default=[48, 56, 64])
    ap.add_argument("--skip-solve", action="store_true",
                    help="复用已落盘解数据，只认证")
    ap.add_argument("--verify-cert", help="证书独立复核")
    ap.add_argument("--crosscheck", action="store_true",
                    help="selftest 附加：(6,6) SDPA-GMP vs Clarabel 值交叉验证")
    ap.add_argument("--sdpa-bin", default=os.environ.get(
        "SDPA_GMP_BIN", "/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp"))
    args = ap.parse_args()
    sdpa_bin = Path(args.sdpa_bin)

    if args.selftest:
        run_selftests(crosscheck=args.crosscheck, sdpa_bin=sdpa_bin)
        return
    if args.verify_cert:
        verify_cert_file(Path(args.verify_cert))
        return
    if args.triage:
        triage(args.triage, args.M, args.K)
        return
    if args.strip:
        lo_s, hi_s = args.strip.split(":")
        lo, hi = Fraction(lo_s), Fraction(hi_s)
        run_strip(lo, hi, args.M, args.K, sdpa_bin, ks=tuple(args.ks),
                  skip_solve=args.skip_solve, cmdline_prefix=None)
        return
    ap.error("需要 --selftest / --triage / --strip / --verify-cert")


def run_strip(lo: Fraction, hi: Fraction, M: int, K: int, sdpa_bin: Path,
              ks=(48, 56, 64), skip_solve=False, cmdline_prefix=None) -> dict:
    tag = strip_tag(lo, hi)
    E_star = load_E_star()
    sol_path = HERE / "results" / f"strip_sol_{tag}_M{M}.json"
    if skip_solve:
        if not sol_path.exists():
            fail(f"--skip-solve 但解数据不存在：{sol_path}")
        solve_info = dict(reused_file=True)
        print(f"[strip] {tag} M={M}：复用解数据 {sol_path.relative_to(REPO)}",
              flush=True)
    else:
        if sol_path.exists():
            print(f"[strip] {tag} M={M}：已有解数据，跳过求解（删文件重解）",
                  flush=True)
            solve_info = dict(reused_file=True)
        else:
            sol_path, solve_info = solve_strip(lo, hi, M, K, sdpa_bin)
    sol_js = json.loads(sol_path.read_text())
    core = TypedCore(9, M, K)
    lm = LamMaps(core, lo, hi)
    sol = sol_to_certify_input(sol_js)
    cert_path = REPO / "certificates" / (
        f"n9-stage-a4-strip-{tag}" + (f"_M{M}.json" if M != 7 else ".json"))
    cmdline = cmdline_prefix or (
        f"numerics/.venv/bin/python numerics/bounds/strips_final.py "
        f"--strip \"{lo}:{hi}\" --M {M} --ks {' '.join(str(k) for k in ks)}")
    last_err = None
    for k in ks:
        try:
            cert_data = certify_slab(core, lm, sol, k, E_star, tag)
        except SystemExit as exc:
            print(f"[retry] {tag} 粒度 2^-{k} 未通过（exit {exc.code}）", flush=True)
            last_err = f"k={k}"
            continue
        write_strip_certificate(core, lm, cert_data, E_star, tag, sol_js,
                                solve_info, cert_path, cmdline)
        verify_cert_file(cert_path)
        row = dict(tag=tag, lo=str(lo), hi=str(hi), cover=f"[{float(lo)},{float(hi)}]",
                   M=M, K=K, e_raw=sol_js["e"],
                   certified=str(cert_data["certified"]),
                   certified_float=float(cert_data["certified"]),
                   margin_over_E_star=float(cert_data["certified"] - E_star),
                   round_bits=k,
                   R1={w: float(v) for w, v in cert_data["R1"].items()},
                   R2={X: float(v) for X, v in cert_data["R2"].items()},
                   deflation=float(cert_data["deflation"]),
                   certificate=str(cert_path.relative_to(REPO)),
                   solution=str(sol_path.relative_to(REPO)),
                   sdpa=sol_js.get("solver_info"), code_version=code_version())
        # 汇入结果 db
        db_path = HERE / "results" / "strips.json"
        db = json.loads(db_path.read_text()) if db_path.exists() else {}
        db.setdefault("strips", [])
        by_tag = {r["tag"] + f"_M{r['M']}": r for r in db["strips"]}
        by_tag[f"{tag}_M{M}"] = row
        db["strips"] = list(by_tag.values())
        db["kind"] = "strips-final"
        db["script"] = "strips_final.py"
        db["code_version"] = code_version()
        db["E_star"] = float(E_star)
        db["updated"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        db_path.write_text(json.dumps(db, ensure_ascii=False, indent=1))
        print(f"[strip] {tag} M={M} ✓ certified = {row['certified_float']:.12f}"
              f"（裕度 {row['margin_over_E_star']:+.3e} over E*）", flush=True)
        return row
    fail(f"{tag} M={M}: 全部粒度 {list(ks)} 认证失败（最后：{last_err}）")


def triage(spec: str, M: int, K: int):
    """Clarabel 数值侦察（slab_band.solve_slab），量 e_raw 裕度，不认证。"""
    import slab_band
    E_star = load_E_star()
    rows = []
    for pair in spec.split(","):
        lo_s, hi_s = pair.split(":")
        lo, hi = Fraction(lo_s), Fraction(hi_s)
        t0 = time.time()
        e_val, info, chk, _sol, _core, _lm, _V = slab_band.solve_slab(9, lo, hi, M, K)
        row = dict(band=f"[{lo_s},{hi_s}]", e_raw=e_val,
                   margin_over_E_star=e_val - float(E_star),
                   e_safe=(chk or {}).get("e_safe_indicative"),
                   deflation=(chk or {}).get("indicative_deflation"),
                   status=info["status"], solve_s=info["solve_s"],
                   wall_s=round(time.time() - t0, 1))
        rows.append(row)
        print(f"[triage] {row['band']} (M={M}): e_raw = {e_val:.9f} → "
              f"E* 裕度 {row['margin_over_E_star']:+.4e}（{info['status']}，"
              f"{info['solve_s']}s）", flush=True)
    db_path = HERE / "results" / "strips.json"
    db = json.loads(db_path.read_text()) if db_path.exists() else {}
    db.setdefault("triage", {})
    db["triage"][f"M{M}"] = dict(rows=rows, tool="slab_band.solve_slab (Clarabel)",
                                 ts=datetime.now(timezone.utc).isoformat(
                                     timespec="seconds"))
    db["code_version"] = code_version()
    db_path.write_text(json.dumps(db, ensure_ascii=False, indent=1))


def run_selftests(crosscheck=False, sdpa_bin=None):
    print("=" * 72, flush=True)
    print("[selftest] ① slab_band 精确自检（组合恒等式＋引理 4.1 正性）on "
          "[−0.90,−0.88] (7,6)", flush=True)
    core = TypedCore(9, 7, 6)
    lm = LamMaps(core, Fraction(-9, 10), Fraction(-22, 25))
    rng = random.Random(20261004)
    exact_typed_identity_selftest(core, lm, rng, trials=2)
    exact_typed_positivity_selftest(core, rng, trials=1)
    print("[selftest] ① 全过 ✓", flush=True)

    print("[selftest] ② 导出器结构自检：条目行数/块数与 LamMaps 维度一致", flush=True)
    ex = SDPAExporterStrip(core, lm)
    st_dir = HERE / "results" / "strip_work"
    st_dir.mkdir(parents=True, exist_ok=True)
    m_dim, n_entries = ex.write_dat(st_dir / "selftest.dat-s")
    print(f"[selftest] m={m_dim}（期望 3·{core.nmon}+3·{lm.deg_p + 1}="
          f"{3 * core.nmon + 3 * (lm.deg_p + 1)}），entries={n_entries}，"
          f"blocks={len(ex.blk)}，n_lp={ex.n_lp}", flush=True)
    assert m_dim == 3 * core.nmon + 3 * (lm.deg_p + 1)
    assert ex.blk[0] == -ex.n_lp and len(ex.blk) == (
        1 + 2 * core.K + len(lm.sosA) + len(lm.sosB) + len(lm.sosG)
        + len(lm.tau_def) + 2 * len(lm.sig_def))
    print("[selftest] ② 全过 ✓", flush=True)

    if crosscheck and sdpa_bin is not None:
        print("[selftest] ③ (6,6) SDPA-GMP vs Clarabel 交叉验证 on [−0.90,−0.88]",
              flush=True)
        lo, hi = Fraction(-9, 10), Fraction(-22, 25)
        sol_path, sinfo = solve_strip(lo, hi, 6, 6, sdpa_bin, timeout_s=3600)
        sol_js = json.loads(sol_path.read_text())
        e_sdpa = sol_js["e"]
        import slab_band
        e_cl, info, chk, _s, _c, _l, _V = slab_band.solve_slab(9, lo, hi, 6, 6)
        diff = e_sdpa - e_cl
        print(f"[selftest] ③ SDPA e = {e_sdpa:.12f} vs Clarabel e_raw = "
              f"{e_cl:.12f}（差 {diff:+.3e}，Clarabel {info['status']}，"
              f"折减指示 {(chk or {}).get('indicative_deflation')}）", flush=True)
        rr = sol_js["raw_residuals"]
        rmax = max([abs(float(Fraction(v))) for v in rr["R1"].values()]
                   + [abs(float(Fraction(v))) for v in rr["R2"].values()])
        print(f"[selftest] ③ LamMaps 独立重算残差最大 {rmax:.3e}"
              f"（导出正确性核验；应 ~1e-30 量级）", flush=True)
        if rmax > 1e-8:
            fail("导出器与 LamMaps 装配不一致（残差过大）")
        if abs(diff) > 5e-3:
            fail(f"SDPA 与 Clarabel 值差 {diff:.3e} 过大——导出或读回有误")
        print("[selftest] ③ 全过 ✓", flush=True)
    print("[selftest] 完成", flush=True)


if __name__ == "__main__":
    main()
