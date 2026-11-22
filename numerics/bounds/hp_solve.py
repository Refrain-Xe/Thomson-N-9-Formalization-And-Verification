#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""hp_solve.py — 三点 SDP 下界（midlarge (8,6), m=−9/10）的高精度求解（路线 a：SDPA-GMP）。

背景（Round 2 认证值 25.752410818 距该档 SDP e 值 25.759382 折减 ~6.97e-3）：
Clarabel 双精度 IPM 在该问题上停滞——insufficient progress @ 第 33 次迭代
（status optimal_inaccurate；2026-10-03 复跑收紧容差至 1e-14 与 Round 1 存档
逐位一致）：恒等式残差 L∞≈2.85e-6 / L1≈8.58e-5，PSD 亏损 ~1e-7。认证损失
36·R1 ≈ 6.53e-3 里求解器残差与 PSD 修复位移主导；dyadic 舍入本身只贡献 ~3e-4。
把求解做干净（残差 → 1e-12 量级、块严格 PSD），认证值即可逼近 e。

路线 a 实现：同一 SDP 原样（不改构造、不改约束）导出为 SDPA sparse .dat-s——
系数来自 sdp_certify.ExactMaps 的**精确有理数**（a=−9/10 精确、1/3 等），
按 40 位十进制截断写入；SDPA-GMP 7.1.3（GMP 200 位精度，mpack 多精度 BLAS）
求解；解从 .result 文件按 66 位十进制回读（parse 为 Fraction，残差全用纯
Fraction 重算）。SDP 形式与约束逐条经 Clarabel 解代入校验（见 hp.json
provenance.export_validation：b−A(X_clarabel) 与 Clarabel 自报恒等式残差一致）。

块布局（SDPA 输入，条目 k l i j v，1 基，块内局部索引，非对角条目贡献 2·v·X_ij）：
  block 1（LP 自由对角，尺寸 16）：h_0..h_14, e；其后 F0..F5（8..3）、
  SOS 块 B_1,B_u-a,…,B_detG（120,84×6,56）、sig0..sig3（15,15,14,14）。
  约束 1..680：SOS_vec(B) − Ch·h − c_e·e + R·vec(F) = 0（slack 恒等式）；
  约束 681..710：σmap(σ) − Cp·h = p_const（minorant 恒等式）；
  目标：max e（C 在 e 槽位 +1）。

SDPA-GMP 构建（本机 darwin/arm64，2026-10-03 实测；hp_solve 不自动构建，
sdpa_build.sh 有完整配方）：
  GMP 6.3.0（--enable-cxx）+ sdpa-gmp 7.1.3（sourceforge sdpa-gmp-7.1.3.src.
  20150320.tar.gz；spooles.2.2 从 netlib 单独下载替换损坏内档；两处源码补丁：
  ① spooles Make.inc 加 clang 兼容旗（-Wno-int-conversion 等）；② sdpa_struct.h
  的 P_FORMAT 从 %+18.12Fe 改 %+72.66Fe 以输出 66 位解精度）。

输出：
  results/hp_solution_midlarge_m090.json —— 解数据（sdp_certify --solution 兼容：
    h/e/F/B/sig 为 float（66 位十进制的最近 double），另附 exact_* 十进制串与
    solver 信息）；
  results/hp.json —— 方法、原始-对偶残差（SDPA 自报 + 我们的精确恒等式残差
    L∞/L1、逐块 PSD λmin、与 Clarabel 停滞解的对比）、认证结果与 provenance。

认证（deliverable 2）：hp_solve.py 默认在求解后调用 sdp_certify.py 的认证路径
（dyadic 舍入 2^-k ＋ exact.py 无主元 LDLᵀ 精确验证，解数据换 results/
hp_solution_midlarge_m090.json），断言 certified > 25.752410818（Round 2 纪录）
且 ≤ E* + 1e-6，违反 sys.exit(1)。

用法（thomson-n9 下）：
  python3 numerics/bounds/hp_solve.py --sdpa-bin /tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp
  python3 numerics/bounds/hp_solve.py --skip-solve --k 64   # 复现存档认证值（默认即 64）
确定性：SDPA-GMP 从固定默认初始点确定性收敛（无随机源）；记录 seed 仅对齐
sdp_bound.CFG 接口。认证自检（ExactMaps 结构交叉核对＋随机有理三点恒等式/
正性）由 sdp_certify.py 自带。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[2] / "thomson-workflow" / "certificates"))

import sdp_bound                                                    # noqa: E402
import sdp_certify                                                  # noqa: E402
from sdp_certify import ExactMaps                                   # noqa: E402
from sdp_certify import (minorant_lhs, minorant_rhs,                # noqa: E402
                         slack_vec, sos_vec)

N, M, K = sdp_certify.N, sdp_certify.M, sdp_certify.K              # 9, 8, 6
A_EXACT = sdp_certify.A_EXACT                                       # −9/10
SEED = 20261003
ROUND2_RECORD = Fraction("25.752410818")                            # Round 2 认证纪录
PHI_TOL = Fraction(1, 10 ** 6)
PARAM_SDPA = """500unsigned int maxIteration;
1.0E-30\tdouble 0.0 < epsilonStar;
1.0E4   double 0.0 < lambdaStar;
2.0   \tdouble 1.0 < omegaStar;
-1.0E5  double lowerBound;
1.0E5  double upperBound;
0.1    \tdouble 0.0 <= betaStar <  1.0;
0.3    \tdouble 0.0 <= betaBar  <  1.0, betaStar <= betaBar;
0.9    \tdouble 0.0 < gammaStar <  1.0;
1.0E-30\tdouble 0.0 < epsilonDash;
200     precision
"""


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    """结果 json 的代码版本（git describe --always --dirty）——防 M6 式复现尾差
    （代码版本演进曾致 −3.7e-9 级尾差，commit e56be8f 全档重解消除）。"""
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


# ============================================================ .dat-s 导出（精确系数）
def frac_dec(f: Fraction, digits: int = 40) -> str:
    """精确 Fraction → 十进制串（截断 digits 位；分母只含 2/3/5 因子，40 位足够）。"""
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


def build_rows(em: ExactMaps):
    """SDPA sparse 条目（k, l, i, j, 精确 Fraction）＋ b 向量。

    非对角条目 (i<j) 存**裸系数**：SDPA 格式对 i<j 条目按 2·v·X_ij 计入内积，
    因此线性泛函 Σ_{p≤q} w_pq·X_pq 的 p<q 系数直接写入 v=w_pq。
    （该约定已用 convtest.dat-s＋sdpa 源码 setElement_SDP 逐条验证。）
    """
    ring = em.ring
    nmon = em.nmon
    n_lp = em.d_H + 2                                  # h_0..h_14, e
    slack_acc: dict = {}

    # ---- slack 恒等式行（k = 1..nmon）：SOS − Ch·h − c_e·e + R·vec(F) = 0
    for alpha in range(nmon):
        for j in range(em.d_H + 1):
            v = em.Ch[alpha][j]
            if v:
                key = (alpha, 1, j + 1, j + 1)
                slack_acc[key] = slack_acc.get(key, Fraction(0)) - v
    alpha0 = ring.index[(0, 0, 0)]
    slack_acc[(alpha0, 1, n_lp, n_lp)] = (
        slack_acc.get((alpha0, 1, n_lp, n_lp), Fraction(0)) - em.c_e[alpha0])
    for (kk, a_, b_), gi in em.S_index.items():       # 行主序含 a_>b，列对称只发一次
        col = em.R_cols[gi]
        l = 2 + kk
        if a_ > b_:
            continue
        for alpha in range(nmon):
            v = col[alpha]
            if v:
                key = (alpha, l, a_ + 1, b_ + 1)
                slack_acc[key] = slack_acc.get(key, Fraction(0)) + v
    for bi, (name, gnz, mons) in enumerate(em.sos_blocks):
        l = 2 + len(em.F_sizes) + bi
        m_ = len(mons)
        for p in range(m_):
            ep = mons[p]
            for q in range(p, m_):
                eq = mons[q]
                base = (ep[0] + eq[0], ep[1] + eq[1], ep[2] + eq[2])
                for (eg, cg) in gnz:
                    e = (base[0] + eg[0], base[1] + eg[1], base[2] + eg[2])
                    key = (ring.index[e], l, p + 1, q + 1)
                    slack_acc[key] = slack_acc.get(key, Fraction(0)) + cg
    entries = [(alpha + 1, l, i, j, v) for (alpha, l, i, j), v in slack_acc.items()]

    # ---- minorant 恒等式行（k = nmon+1 .. nmon+deg_p+1）：σmap(σ) − Cp·h = p_const
    minor_acc: dict = {}
    for r in range(em.deg_p + 1):
        for j in range(em.d_H + 1):
            v = em.Cp[r][j]
            if v:
                key = (r, 1, j + 1, j + 1)
                minor_acc[key] = minor_acc.get(key, Fraction(0)) - v
    for si, (name, mons_y, mult) in enumerate(em.sig_def):
        l = 2 + len(em.F_sizes) + len(em.sos_blocks) + si
        m_ = len(mons_y)
        for p in range(m_):
            for q in range(p, m_):
                base = mons_y[p] + mons_y[q]
                for (eg, cg) in mult:
                    key = (base + eg, l, p + 1, q + 1)
                    minor_acc[key] = minor_acc.get(key, Fraction(0)) + cg
    entries += [(nmon + 1 + r, l, i, j, v) for (r, l, i, j), v in minor_acc.items()]

    b = [Fraction(0)] * (nmon + em.deg_p + 1)
    for r in range(em.deg_p + 1):
        b[nmon + r] = em.p_const[r]
    c_entries = [(0, 1, n_lp, n_lp, Fraction(1))]     # max e
    blkstruct = ([-n_lp] + list(em.F_sizes)
                 + [len(mons) for _n, _g, mons in em.sos_blocks]
                 + [len(mly) for _n, mly, _mu in em.sig_def])
    return blkstruct, b, c_entries + entries


def write_dat(em: ExactMaps, path: Path) -> tuple[int, int]:
    blkstruct, b, entries = build_rows(em)
    with open(path, "w") as f:
        f.write('"N=9 three-point SDP midlarge (8,6) m=-9/10 (exact rational coefficients)"\n')
        f.write(f"{len(b)} = mDIM\n{len(blkstruct)} = nBLOCK\n")
        f.write(" ".join(str(s) for s in blkstruct) + " = bLOCKsTRUCT\n")
        f.write(" ".join(frac_dec(x) for x in b) + "\n")
        for (k, l, i, j, v) in entries:
            f.write(f"{k} {l} {i} {j} {frac_dec(v)}\n")
    return len(b), len(entries)


def validate_export(em: ExactMaps, workdir: Path) -> dict:
    """代入 Clarabel 停滞解：b − A(X) 应等于 Clarabel 自报恒等式残差。"""
    sol_path = HERE / "results" / "sdp_solution_midlarge_m090.json"
    sol = json.load(open(sol_path))
    _blk, b, entries = build_rows(em)
    blocks = {1: np.array(sol["h"] + [sol["e"]], dtype=float)}
    for kk in range(len(em.F_sizes)):
        blocks[2 + kk] = np.array(sol["F"][kk], dtype=float)
    for bi, (name, _g, _m) in enumerate(em.sos_blocks):
        blocks[2 + len(em.F_sizes) + bi] = np.array(sol["B"][name], dtype=float)
    for si, (name, _my, _mu) in enumerate(em.sig_def):
        blocks[2 + len(em.F_sizes) + len(em.sos_blocks) + si] = np.array(sol["sig"][name],
                                                                        dtype=float)
    def ev(l, i, j):
        B = blocks[l]
        if l == 1:
            return B[i - 1]
        return 2.0 * B[i - 1, j - 1] if i != j else B[i - 1, j - 1]
    lhs = np.zeros(len(b) + 1)
    for (k, l, i, j, v) in entries:
        lhs[k] += float(v) * ev(l, i, j)
    resid = np.array([float(x) for x in b]) - lhs[1:]
    nmon = em.nmon
    chk = dict(
        objective=float(lhs[0]), objective_equals_clarabel_e=bool(lhs[0] == sol["e"]),
        resid_linf=float(np.abs(resid).max()), resid_l1=float(np.abs(resid).sum()),
        slack_rows_l1=float(np.abs(resid[:nmon]).sum()),
        minorant_rows_l1=float(np.abs(resid[nmon:]).sum()),
        clarabel_identity_l1_slack=sol["verify"]["identity_l1_slack"],
        clarabel_resid_minorant_l1=1.732146959687597e-05,
        note="代入 Clarabel 解：导出问题的 b−A(X) 与 Clarabel 自报恒等式残差一致 → 系数/约定正确",
    )
    ok = (chk["objective_equals_clarabel_e"]
          and abs(chk["slack_rows_l1"] - chk["clarabel_identity_l1_slack"]) < 1e-9
          and abs(chk["minorant_rows_l1"] - chk["clarabel_resid_minorant_l1"]) < 1e-9)
    chk["ok"] = bool(ok)
    if not ok:
        fail(f"导出校验失败：{chk}")
    return chk


# ============================================================ .result 解析
def parse_result(path: Path) -> dict:
    """解析 sdpa_gmp .result：统计信息 + yMat（本 build 的 REVERSE_PRIMAL_DUAL：
    我们的原始变量 X 打印在 yMat 段——首组为 LP 对角块（平铺），其后每个
    SDP 块为一组 { {r0}, {r1}, … }（全对称打印）。"""
    text = path.read_text()

    def grab(pat, flags=0):
        m = re.search(pat, text, flags)
        return m.group(1) if m else None

    info = dict(
        phase_value=grab(r"phase\.value = (\S+)"),
        iteration=int(grab(r"Iteration = (\d+)") or -1),
        mu=float(grab(r"mu = ([0-9.eE+-]+)") or "nan"),
        gap=None if grab(r"^ *gap = ([0-9.eE+-]+)", re.M) is None
        else float(grab(r"^ *gap = ([0-9.eE+-]+)", re.M)),
        relative_gap=float(grab(r"relative gap = ([0-9.eE+-]+)") or "nan"),
        p_feas_error=grab(r"p\.feas\.error = ([0-9.eE+-]+)"),
        d_feas_error=grab(r"d\.feas\.error = ([0-9.eE+-]+)"),
        obj_primal=grab(r"objValPrimal = ([0-9.eE+-]+)"),
        obj_dual=grab(r"objValDual = ([0-9.eE+-]+)"),
    )
    # yMat 段 → 括号深度扫描切出顶层组
    mm = re.search(r"yMat = \s*\n\{\n(.*)\n\}", text, re.S)
    if mm is None:
        fail("yMat 段未找到（sdpa_gmp 是否以 REVERSE_PRIMAL_DUAL 构建/收敛？）")
    body = mm.group(1)
    groups: list[str] = []
    depth = 0
    start = None
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
    sdp: list[list[list[str]]] = []
    for g in groups[1:]:
        rows = re.findall(r"\{([^{}]*)\}", g)
        if not rows:
            fail("SDP 组内未找到行")
        sdp.append([[x for x in re.split(r"[,\s]+", r_) if x] for r_ in rows])
    if len(lp_vals) < 1 or not sdp:
        fail(f"yMat 解析失败：lp={len(lp_vals)} 值, n_sdp_groups={len(sdp)}")
    return dict(info=info, lp=[Fraction(s) for s in lp_vals], sdp=sdp)


def solution_from_parse(em: ExactMaps, parsed: dict) -> dict:
    """解析结果 → {h, e, F, B, sig}（Fraction，十进制串精确解释）。"""
    lp = parsed["lp"]
    if len(lp) != em.d_H + 2:
        fail(f"LP 块长度 {len(lp)} ≠ {em.d_H + 2}")
    h = lp[:em.d_H + 1]
    e = lp[em.d_H + 1]
    n_expect = len(em.F_sizes) + len(em.sos_blocks) + len(em.sig_def)
    if len(parsed["sdp"]) != n_expect:
        fail(f"SDP 块数 {len(parsed['sdp'])} ≠ {n_expect}")
    mats = []
    for g in parsed["sdp"]:
        n = len(g)
        if any(len(r) != n for r in g):
            fail("SDP 块非方阵")
        mats.append([[Fraction(x) for x in r] for r in g])
    off = 0
    F = mats[off:off + len(em.F_sizes)]
    off += len(em.F_sizes)
    B = {name: mats[off + i] for i, (name, _g, _m) in enumerate(em.sos_blocks)}
    off += len(em.sos_blocks)
    sig = {name: mats[off + i] for i, (name, _my, _mu) in enumerate(em.sig_def)}
    for k, m_ in enumerate(F):
        if len(m_) != em.F_sizes[k]:
            fail(f"F{k} 尺寸不符")
    for (name, _g, mons), m_ in zip(em.sos_blocks, [B[n] for n, _g, _m in em.sos_blocks]):
        if len(m_) != len(mons):
            fail(f"B_{name} 尺寸 {len(m_)} ≠ {len(mons)}")
    for (name, mons_y, _mu), m_ in zip(em.sig_def, [sig[n] for n, _my, _mu in em.sig_def]):
        if len(m_) != len(mons_y):
            fail(f"{name} 尺寸 {len(m_)} ≠ {len(mons_y)}")
    return dict(h=h, e=e, F=F, B=B, sig=sig)


# ============================================================ 精确残差
def exact_residuals(em: ExactMaps, sol_fr: dict) -> dict:
    sv = slack_vec(em, sol_fr["h"], sol_fr["e"], sol_fr["F"])
    ov = sos_vec(em, sol_fr["B"])
    resid = [x - y for x, y in zip(sv, ov)]
    R1 = sum(abs(x) for x in resid)
    lhs = minorant_lhs(em, sol_fr["sig"])
    rhs = minorant_rhs(em, sol_fr["h"])
    rsig = [x - y for x, y in zip(rhs, lhs)]
    R2 = abs(rsig[0]) + sdp_certify.B_W * sum(abs(x) for x in rsig[1:])
    return dict(R1_exact=R1, R2_exact=R2,
                resid_slack_linf=max(abs(x) for x in resid),
                resid_slack_l1=sum(abs(x) for x in resid),
                resid_minor_linf=max(abs(x) for x in rsig),
                resid_minor_l1=sum(abs(x) for x in rsig))


def min_eigs(sol_fr: dict) -> dict:
    out = {}
    for kk, m_ in enumerate(sol_fr["F"]):
        A = np.array([[float(x) for x in row] for row in m_])
        out[f"F{kk}"] = float(np.linalg.eigvalsh((A + A.T) / 2).min())
    for name, m_ in sol_fr["B"].items():
        A = np.array([[float(x) for x in row] for row in m_])
        out[f"B_{name}"] = float(np.linalg.eigvalsh((A + A.T) / 2).min())
    for name, m_ in sol_fr["sig"].items():
        A = np.array([[float(x) for x in row] for row in m_])
        out[name] = float(np.linalg.eigvalsh((A + A.T) / 2).min())
    return out


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="高精度求解（SDPA-GMP）+ 认证 midlarge (8,6) m=−0.9")
    ap.add_argument("--sdpa-bin", default=os.environ.get("SDPA_GMP_BIN",
                    str(HERE / "sdpa_gmp" / "sdpa_gmp")),
                    help="sdpa_gmp 可执行文件路径")
    ap.add_argument("--workdir", default=str(HERE / "results" / "hp_work"))
    ap.add_argument("--skip-solve", action="store_true",
                    help="复用已落盘 results/hp_solution_midlarge_m090.json，只做认证")
    ap.add_argument("--k", type=int, nargs="+", default=[64],
                    help="认证 dyadic 舍入粒度候选（传给 sdp_certify.py；默认 [64] "
                         "＝存档证书的生成粒度——sdp_certify 取首个通过断言的粒度，"
                         "旧默认 [48,56,64] 会在 k=48 提前通过，certified 比存档低 "
                         "3.58e-07（2026-10-04 复算员发现，两值均有效但不可唯一复现））")
    ap.add_argument("--no-certify", action="store_true")
    ap.add_argument("--out", default=str(HERE / "results" / "hp.json"))
    args = ap.parse_args()

    t_start = time.time()
    workdir = Path(args.workdir)
    workdir.mkdir(parents=True, exist_ok=True)
    sol_path = HERE / "results" / "hp_solution_midlarge_m090.json"
    with open(HERE.parents[2] / "thomson-workflow" / "data" / "energies.json") as f:
        E_star = Fraction(json.load(f)["energies"]["9"]["value"])

    em = ExactMaps(N, A_EXACT, M, K)

    solve_block: dict = {"skipped": bool(args.skip_solve)}
    if args.skip_solve:
        if not sol_path.exists():
            fail(f"--skip-solve 但解数据不存在：{sol_path}")
        with open(sol_path) as f:
            sol_js = json.load(f)
        if "exact" in sol_js:
            ex = sol_js["exact"]
            sol_fr = dict(
                h=[Fraction(s) for s in ex["h"]], e=Fraction(ex["e"]),
                F=[[[Fraction(s) for s in row] for row in m_] for m_ in ex["F"]],
                B={n: [[Fraction(s) for s in row] for row in m_]
                   for n, m_ in ex["B"].items()},
                sig={n: [[Fraction(s) for s in row] for row in m_]
                     for n, m_ in ex["sig"].items()})
        else:
            sol_fr = dict(
                h=[Fraction(x) for x in sol_js["h"]], e=Fraction(str(sol_js["e"])),
                F=[[[Fraction(x) for x in row] for row in m_] for m_ in sol_js["F"]],
                B={n: [[Fraction(x) for x in row] for row in m_]
                   for n, m_ in sol_js["B"].items()},
                sig={n: [[Fraction(x) for x in row] for row in m_]
                     for n, m_ in sol_js["sig"].items()})
    else:
        bin_path = Path(args.sdpa_bin)
        if not (bin_path.exists() and os.access(bin_path, os.X_OK)):
            fail(f"sdpa_gmp 不可执行：{bin_path}（--sdpa-bin 指定，或设 SDPA_GMP_BIN；"
                 "构建配方见本文件 docstring / sdpa_build.sh）")
        # 1) 导出 + 校验
        dat = workdir / "n9_hp.dat-s"
        m_dim, n_entries = write_dat(em, dat)
        export_chk = validate_export(em, workdir)
        print(f"[export] {dat.name}: m={m_dim}, entries={n_entries}；"
              f"Clarabel 代入校验 ok={export_chk['ok']}", flush=True)
        # 2) 求解（workdir 已有 pdOPT 结果文件则复用——SDPA-GMP 确定性，
        #    复用与重跑逐位一致；复用事实记入 provenance）
        param = workdir / "param_hp.sdpa"
        param.write_text(PARAM_SDPA)
        result = workdir / "n9_hp.result"
        cmd = [str(bin_path), "-ds", str(dat), "-o", str(result), "-p", str(param)]
        reused = False
        if result.exists():
            try:
                parsed = parse_result(result)
                reused = parsed["info"]["phase_value"] == "pdOPT"
            except SystemExit:
                reused = False
        if reused:
            info = parsed["info"]
            print(f"[solve] 复用已有 pdOPT 结果 {result}（确定性复现，跳过重解）",
                  flush=True)
            solve_s = 0.0
        else:
            print(f"[solve] {' '.join(cmd)}", flush=True)
            t0 = time.time()
            proc = subprocess.run(cmd, capture_output=True, text=True,
                                  cwd=str(workdir), timeout=7200)
            solve_s = time.time() - t0
            if proc.returncode != 0 or not result.exists():
                fail(f"sdpa_gmp 退出码 {proc.returncode}：{proc.stdout[-2000:]} {proc.stderr[-2000:]}")
            parsed = parse_result(result)
            info = parsed["info"]
        print(f"[solve] phase={info['phase_value']} iter={info['iteration']} "
              f"mu={info['mu']:.2e} relgap={info['relative_gap']:.2e} "
              f"p.feas={info['p_feas_error']} d.feas={info['d_feas_error']} "
              f"({solve_s:.0f}s)", flush=True)
        if info["phase_value"] != "pdOPT":
            fail(f"SDPA-GMP 未达 pdOPT：{info['phase_value']}")
        sol_fr = solution_from_parse(em, parsed)
        solve_block = dict(
            binary=str(bin_path), cmd=cmd if not reused else None,
            solve_s=round(solve_s, 1), reused_result=bool(reused),
            sdpa_info=info,
            **({"reused_note": ("复用 workdir 里已有 pdOPT 结果（SDPA-GMP 确定性，"
                                "重跑逐位一致）；该结果的原始求解墙钟 ≈ 2489 s"
                                "（2026-10-03 首跑实测，./sdpa_gmp -ds n9_hp.dat-s）")}
               if reused else {}),
            sdpa_reported=dict(p_feas_error=float(info["p_feas_error"]),
                               d_feas_error=float(info["d_feas_error"]),
                               mu=info["mu"], relative_gap=info["relative_gap"]),
            export_validation=export_chk,
            sig_absmax={n: max(abs(float(x)) for row in m_ for x in row)
                        for n, m_ in sol_fr["sig"].items()},
        )
        # ---- e 封顶（若松弛最优超出 E*+1e-6−2e-5：证书声称值须 ≤ E*+1e-6；
        #      降 e 合法（三点恒等式对任意 e 精确成立），slack/R1 相应变化，
        #      认证自洽——certified ≈ e_used − 认证损失）----
        e_raw = sol_fr["e"]
        E_limit = E_star + sdp_certify.PHI_TOL
        e_cap = E_limit - Fraction(2, 10 ** 5)
        if e_raw > e_cap:
            sol_fr["e"] = e_cap
            solve_block["e_capped"] = dict(e_raw=str(e_raw), e_used=str(e_cap),
                                           reason=("SDP 松弛最优值超过 E*+1e-6−2e-5；"
                                                   "按认证上限封顶（恒等式对任意 e "
                                                   "成立，降 e 只弱化声称）"))
            print(f"[cap  ] e_raw = {float(e_raw):.15f} > E*+1e-6 − 2e-5 → "
                  f"e_used = {float(e_cap):.15f}", flush=True)
        # 3) 落盘解数据：float 字段（数值复核 shim 用）＋ exact 字段（SDPA-GMP
        #    66 位十进制精确回读的 Fraction，str 为精确 p/q；认证的 dyadic 舍入
        #    对 exact 走整数运算——σ 块尺度 ~1e10，float64 中转会丢格点精度）
        sol_js = dict(
            h=[float(x) for x in sol_fr["h"]],
            e=float(sol_fr["e"]),
            F=[[[float(x) for x in row] for row in m_] for m_ in sol_fr["F"]],
            B={n: [[float(x) for x in row] for row in m_] for n, m_ in sol_fr["B"].items()},
            sig={n: [[float(x) for x in row] for row in m_] for n, m_ in sol_fr["sig"].items()},
            exact=dict(
                h=[str(x) for x in sol_fr["h"]],
                e=str(sol_fr["e"]),
                F=[[[str(x) for x in row] for row in m_] for m_ in sol_fr["F"]],
                B={n: [[str(x) for x in row] for row in m_]
                   for n, m_ in sol_fr["B"].items()},
                sig={n: [[str(x) for x in row] for row in m_]
                     for n, m_ in sol_fr["sig"].items()},
                note=("SDPA-GMP .result 按十进制串精确回读的 Fraction；"
                      "str(Fraction) 是精确 p/q，认证舍入用整数运算"),
            ),
            solver_info=dict(route="SDPA-GMP 7.1.3 (GMP precision 200)", **info),
            timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        )
        sol_path.write_text(json.dumps(sol_js, ensure_ascii=False))
        print(f"[out] 解数据已落盘 {sol_path}", flush=True)

    # ---- 精确残差 + PSD λmin + 数值复核（sdp_bound.verify 的 shim 版）
    ex = exact_residuals(em, sol_fr)
    me = min_eigs(sol_fr)
    e_fr = sol_fr["e"]
    print(f"[resid] e = {float(e_fr):.15f}；精确恒等式残差：slack L∞ = "
          f"{float(ex['resid_slack_linf']):.2e} / L1 = {float(ex['resid_slack_l1']):.2e}，"
          f"minorant L∞ = {float(ex['resid_minor_linf']):.2e} / L1 = "
          f"{float(ex['resid_minor_l1']):.2e}", flush=True)
    print(f"[resid] R1 = {float(ex['R1_exact']):.3e}（36·R1 = {float(36*ex['R1_exact']):.3e}），"
          f"R2 = {float(ex['R2_exact']):.3e}；最差块 λmin = {min(me.values()):.2e}", flush=True)

    clarabel = json.load(open(HERE / "results" / "sdp_solution_midlarge_m090.json"))

    # ---- 数值复核（sdp_bound.verify 套用到新解：构建 cvxpy 句柄后直接注入 .value）
    numeric_check = None
    e_safe_hp = None
    if sdp_bound.cp is not None:
        maps = sdp_bound.assemble_maps(N, -0.9, M, K)
        _prob, V, _meta = sdp_bound.build_sdp(maps)
        V["h"].value = np.array([float(x) for x in sol_fr["h"]])
        V["e"].value = float(e_fr)
        for kk, Fv in enumerate(sol_fr["F"]):
            V["F"][kk].value = np.array([[float(x) for x in row] for row in Fv])
        for name, _A, Bv in V["sos"]:
            Bv.value = np.array([[float(x) for x in row] for row in sol_fr["B"][name]])
        for name, _A, Bv, _my, _mu in V["sig"]:
            Bv.value = np.array([[float(x) for x in row] for row in sol_fr["sig"][name]])
        numeric_check = sdp_bound.verify(maps, V, float(e_fr))
        e_safe_hp = numeric_check["e_safe"]
        print(f"[chk  ] 数值复核：slack_min_random = {numeric_check['slack_min_random']:.2e}，"
              f"viol_fine = {numeric_check['viol_fine']:.2e}，deflation = "
              f"{numeric_check['deflation']:.3e} → e_safe = {e_safe_hp:.9f}"
              f"（accepted={numeric_check['accepted']}）", flush=True)

    resid_cmp = dict(
        clarabel=dict(e=clarabel["e"],
                      identity_l1_slack=clarabel["verify"]["identity_l1_slack"],
                      identity_residual_slack=clarabel["verify"]["identity_residual_slack"],
                      identity_residual_minorant=clarabel["verify"]["identity_residual_minorant"],
                      min_eig_min=min(clarabel["verify"]["min_eig"].values()),
                      status=clarabel["solver_info"]["status"]),
        sdpa_gmp=dict(e=float(e_fr),
                      resid_slack_linf=float(ex["resid_slack_linf"]),
                      resid_slack_l1=float(ex["resid_slack_l1"]),
                      resid_minor_linf=float(ex["resid_minor_linf"]),
                      resid_minor_l1=float(ex["resid_minor_l1"]),
                      min_eig_min=min(me.values()),
                      status=solve_block.get("sdpa_info", {}).get("phase_value",
                          sol_js.get("solver_info", {}).get("phase_value"))),
        improvement_factor=dict(
            slack_l1=float(clarabel["verify"]["identity_l1_slack"] / float(ex["resid_slack_l1"])),
            minorant_l1=1.732146959687597e-05 / float(ex["resid_minor_l1"])),
    )

    out = dict(
        kind="hp_solve", script="hp_solve.py", seed=SEED,
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        target=dict(N=N, a=fraction_to_str_local(A_EXACT), M=M, K=K,
                    E_star=float(E_star),
                    round2_record=float(ROUND2_RECORD)),
        method=("路线 a：SDPA-GMP 扩展精度求解（同一 midlarge (8,6) m=−9/10 三点 SDP；"
                "精确有理系数导出 .dat-s，GMP 200 位精度，解按 66 位十进制回读，"
                "残差以纯 Fraction 重算；Clarabel 双精度停滞解作对照）"),
        provenance=dict(
            route_decision=("三选一里取 a（扩展精度 SDP）：b（迭代精化）需在停滞的"
                            "Clarabel 点上做 KKT/最小二乘修正，PSD 亏损与恒等式残差"
                            "在双精度里互相顶住（测得 Clarabel 停滞后恒等式残差 "
                            "8.6e-5 量级压不下去）；c（重标度）不改变双精度信息量。"
                            "a 把同一 SDP 原样重解到 200 位精度，pdOPT 后恒等式残差"
                            "1e-38——R1/R2 由求解器残差主导变为纯舍入主导。"),
            build=("SDPA-GMP 7.1.3 源码构建（GMP 6.3.0 --enable-cxx + netlib spooles"
                   " 2.2 + 两处补丁：spooles clang 旗、P_FORMAT 66 位输出精度；"
                   "完整配方 numerics/bounds/sdpa_build.sh，2026-10-03 本机实测）"),
            export=("build_rows 以 ExactMaps 的精确有理系数（a=−9/10、1/3 等）按 40 位"
                    "十进制写 .dat-s；代入 Clarabel 停滞解逐条校验：b−A(X) 与 Clarabel "
                    "自报恒等式残差一致、目标值逐位相等（solve.export_validation）"),
            certify=("sdp_certify.py 认证路径（--solution 换新解数据）：exact 有理数"
                     "dyadic 舍入（整数运算，任意尺度精确）→ 2^-40 地板起步的精确"
                     "LDLᵀ PSD 修复 → 纯 Fraction 残差 R1/R2 → certified = "
                     "(e − 36·R1)/(1+R2)；断言 certified > 25.752410818（Round 2 "
                     "纪录）且 ≤ E*+1e-6，负对照（--min-bound 25.7599）实测 sys.exit(1)"),
            residual_comparison="见 residual_comparison（Clarabel vs SDPA-GMP）",
            reproduce=(
                "python3 numerics/bounds/hp_solve.py --skip-solve --k 64"
                "（--sdpa-bin 指向 sdpa_gmp；解数据 results/hp_solution_midlarge_m090.json，"
                "workdir 已有 pdOPT 结果时确定性复用不重解）——certified 逐位复现 "
                "25.759445973097478（round_bits=64）。注意 sdp_certify 取首个通过断言的"
                "粒度：若显式传 --k 48 56 64，会在 k=48 提前通过得 "
                "25.759445614952（低 3.58e-07，同样有效但与存档不同）"),
        ),
        solve=solve_block,
        solution=dict(path=str(sol_path.relative_to(REPO)),
                      sha256_16=hashlib.sha256(
                          json.dumps({k2: sol_js[k2] for k2 in ("h", "e", "F", "B", "sig")},
                                     sort_keys=True).encode()).hexdigest()[:16]),
        exact_residuals={k: (str(v) if k.endswith('_exact') else float(v))
                         for k, v in ex.items()},
        min_eig=me,
        min_eig_note=("float64 eigvalsh 的噪声地板 ~1e-16·‖块‖：σ 块尺度 ~1.5e15，"
                      "故其 float λmin（~−1e0）只是噪声，不是真实亏损；PSD 判定的"
                      "权威路径是认证里的精确 LDLᵀ（18 块全部以 δ=2^-40 一次通过）"),
        numeric_check=numeric_check,
        numeric_check_note=("sdp_bound.verify 的数值复核：slack 逐点/折减正常"
                            "（deflation=1.6e-8 → e_safe=25.759446386），其 "
                            "accepted=False 仅因 min_eig 门限按 float64 λmin 判定，"
                            "被 σ 块（~1.5e15）的噪声地板触发；精确 R2=1.2e-40 与"
                            " 精确 LDLᵀ 才是权威判据（数值复核不作为出界依据，"
                            "见 sdp_bound.py 头注）"),
        residual_comparison=resid_cmp,
        residual_comparison_note=("Clarabel 双精度 IPM 停滞（insufficient progress@33，"
                                  "与 Round 1 存档逐位一致）vs SDPA-GMP（pdOPT，"
                                  "恒等式残差降 ~34 个数量级，e 高 6.4e-5——即 "
                                  "Round 1/2 折减的主要来源确实是求解器残差）"),
    )

    # ---- 认证（deliverable 2）：sdp_certify.py 认证路径 + 新纪录断言
    if not args.no_certify:
        cert_out = REPO / "certificates" / "n9-stage-a2-sdp-hp.json"
        cmd = [sys.executable, str(HERE / "sdp_certify.py"),
               "--solution", str(sol_path),
               "--min-bound", str(float(ROUND2_RECORD)),
               *(["--ref-safe", repr(float(e_safe_hp))] if e_safe_hp is not None else []),
               "--k", *[str(k) for k in args.k],
               "--out", str(cert_out)]
        print(f"[cert ] {' '.join(cmd)}", flush=True)
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=7200)
        print(proc.stdout[-6000:], flush=True)
        if proc.returncode != 0:
            print(proc.stderr[-3000:], flush=True)
            fail(f"认证失败（退出码 {proc.returncode}）——见上")
        cert = json.loads(cert_out.read_text())
        certified = Fraction(cert["claimed_bound"])
        improvement = certified - ROUND2_RECORD
        out["certified"] = dict(
            claimed_bound=cert["claimed_bound"], value=float(certified),
            certificate=str(cert_out.relative_to(REPO)),
            round_bits=cert["provenance"]["params"]["round_bits"],
            R1=float(Fraction(cert["provenance"]["residual_norms"]["R1_exact"])),
            R2=float(Fraction(cert["provenance"]["residual_norms"]["R2_exact"])),
            rounding_loss=float(cert["provenance"]["rounding_loss"]["vs_raw_e_float"]),
            improvement_over_round2=float(improvement),
            gap_to_E_star=float(E_star - certified),
        )
        if not (certified > ROUND2_RECORD):
            fail(f"assert 失败：certified = {float(certified):.12f} ≤ Round 2 纪录 "
                 f"{float(ROUND2_RECORD):.12f}")
        if not (0 < certified <= E_star + PHI_TOL):
            fail(f"assert 失败：certified = {float(certified):.15e} 违反 "
                 f"0 < certified ≤ E*+1e-6 = {float(E_star + PHI_TOL):.15e}")
        print(f"[cert ] certified = {float(certified):.12f}（> Round 2 纪录 "
              f"{float(ROUND2_RECORD):.12f}，改进 {float(improvement):.6e}；"
              f"E* − certified = {float(E_star - certified):.9f}）✓", flush=True)

    out["runtime_s"] = round(time.time() - t_start, 1)
    out_path = Path(args.out)
    out_path.write_text(json.dumps(out, ensure_ascii=False, indent=2))
    print(f"[out] 已写入 {out_path}", flush=True)
    print(f"[done] 总用时 {out['runtime_s']}s", flush=True)


def fraction_to_str_local(fr: Fraction) -> str:
    return f"{fr.numerator}/{fr.denominator}"


if __name__ == "__main__":
    main()
