#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r13_a6_data.py — R13B A6（Lukács·Markov–Lukács 平方表示件）数据件。

【任务定位（r13b-tablea-a6，D52 裁决 3）】M9 cap 证书
certificates/n9-stage-a4-typedcap-m0748_M9.json 一类侧 minorant σ 族的
平方表示与 R2 折减恒等式的**数据面**：只读消费证书（blocks.sig_AA/AB_sig0..3
＋ h_AA/AB_diag）与 results/r9_s3_rederive.json（R2_exact 对账目标，不参与
推导），以 Python Fraction 精确重算并落盘 results/r13_a6_data.json，
供 TableA6.lean 字面量生成与 r13_a6_gate.py G5 离线复核。

【数学内容（自写第二实现，stdlib only）】
  (a) σ 块 8 件（AA/AB × sig0..3，维 17/17/16/16，证书 dyadic Gram）的
      精确 LDLᵀ（单位下三角 L、对角 D）＋主元全正布尔＋L·D·Lᵀ==S 逐位重构。
  (b) minorant 装配：Cp 矩阵（Csub[2m][i]+=C(i,m)(−2)^m、奇次行×−2）、
      rhs_r=Σ_j Cp[r][j]·h[j]+p_const[r]（deg_p=2d_H+1=33）、
      lhs=Σ_4σ块 (Σ y^{p+q})·mult 系数向量（mult 族 1/y/(b²−y²)/y(b²−y²)）。
  (c) R2_cls=Σ_{j=0}^{33}|rhs_j−lhs_j|·ŵ^j（ŵ=⌈√b²⌉=117/125、b²=437/500）
      与 r9_s3_rederive.json R2_exact 逐位（Fraction）对账；残差 33 非零
      系数带号（sgn_j=sgn(rhs_j−lhs_j)∈{−1,0,+1}）。
  (d) 乘子族域非负性记录：[0,b] 上 1/y/(b²−y²)/y(b²−y²) ≥ 0（陈述性，
      Lean 件内证）。

【边界如实】H≤φ 于 [lo,1] 的逐点优越性与一般 Lukács 存在定理均不在本件
（D52 裁决 3：本件为证书数据具体表示的机器验证）。

用法（CWD 无关）：
  python3 numerics/bounds/r13_a6_data.py [--cert PATH] [--out PATH]
默认 cert=certificates/n9-stage-a4-typedcap-m0748_M9.json、
out=results/r13_a6_data.json。heavySolves=0（纯 Fraction 精确线代，
无 SDP/求解器）。
"""
from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

F0, F1 = Fraction(0), Fraction(1)

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CERT_DEFAULT = REPO / "certificates" / "n9-stage-a4-typedcap-m0748_M9.json"
R9JSON_PATH = HERE / "results" / "r9_s3_rederive.json"
OUT_DEFAULT = HERE / "results" / "r13_a6_data.json"

CLASSES = ("AA", "AB")
SIG_NAMES = ("sig0", "sig1", "sig2", "sig3")
SEED_SPOT = 20261015                # 抽查求值点种子（D52 裁决 2 同款口径）

import random


def spot_points() -> list:
    """3 个固定有理抽查点 y ∈ (0,b)（b²=437/500 ⇒ b≈0.9347），seed 20261015。"""
    rng = random.Random(SEED_SPOT)
    b2 = Fraction(437, 500)
    cands = [Fraction(k, 40) for k in range(4, 37)]     # 0.1 .. 0.925 < b
    return sorted(rng.sample(cands, 3))


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
    p, q = x.numerator, x.denominator
    s = math.isqrt(p * q)
    return Fraction(s if s * s == p * q else s + 1, q)


# ---------------------------------------------------------------- 装配
class Minorant:
    """一侧 [lo,1) minorant 的 σ 装配与 Cp/h 装置（自写第二实现）。"""

    def __init__(self, lo: Fraction, M: int):
        self.lo = lo
        self.M = M
        self.d_H = 2 * M - 2
        self.deg_p = 2 * self.d_H + 1
        d_H = self.d_H
        Csub = [[F0] * (d_H + 1) for _ in range(self.deg_p + 1)]
        for i in range(d_H + 1):
            for m in range(i + 1):
                Csub[2 * m][i] += Fraction(math.comb(i, m) * ((-2) ** m))
        self.Cp = [[F0] * (d_H + 1) for _ in range(self.deg_p + 1)]
        for r in range(1, self.deg_p + 1, 2):
            self.Cp[r] = [-2 * x for x in Csub[r - 1]]
        self.p_const = [F0] * (self.deg_p + 1)
        self.p_const[0] = F1
        self.b2 = (F1 - lo) / 2
        self.w_hat = ceil_sqrt_rat(self.b2)
        # sig_def：块名 → (y-单项式基指数, 乘子 (指数,系数) 族)
        self.sig_def = [
            ("sig0", list(range(0, d_H + 1)), [(0, F1)]),
            ("sig1", list(range(0, d_H + 1)), [(1, F1)]),
            ("sig2", list(range(0, d_H)), [(0, self.b2), (2, Fraction(-1))]),
            ("sig3", list(range(0, d_H)),
             [(1, self.b2), (3, Fraction(-1))]),
        ]

    def rhs(self, h: list) -> list:
        return [sum(self.Cp[r][j] * h[j] for j in range(self.d_H + 1))
                + self.p_const[r] for r in range(self.deg_p + 1)]

    def lhs(self, Sblocks: dict) -> list:
        out = [F0] * (self.deg_p + 1)
        for (name, mons_y, mult) in self.sig_def:
            S = Sblocks[name]
            m = len(mons_y)
            for p in range(m):
                for q in range(m):
                    c = S[p][q]
                    if not c:
                        continue
                    base = mons_y[p] + mons_y[q]
                    for (eg, cg) in mult:
                        out[base + eg] += c * cg
        return out


def ldl(S: list) -> tuple:
    """精确 LDLᵀ：S 对称 ⇒ S = L·diag(D)·Lᵀ，L 单位下三角。"""
    n = len(S)
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n
    for j in range(n):
        s = S[j][j] - sum(L[j][k] * L[j][k] * D[k] for k in range(j))
        D[j] = s
        L[j][j] = F1
        for i in range(j + 1, n):
            L[i][j] = (S[i][j]
                       - sum(L[i][k] * L[j][k] * D[k] for k in range(j))) / s
    return L, D


def mat_eq(A: list, B: list) -> bool:
    return all(A[i][j] == B[i][j] for i in range(len(B)) for j in range(len(B)))


# ---------------------------------------------------------------- 主流程
def main() -> None:
    t0 = time.time()
    ap = argparse.ArgumentParser(description="R13B A6 数据件（Fraction 精确）")
    ap.add_argument("--cert", default=str(CERT_DEFAULT))
    ap.add_argument("--out", default=str(OUT_DEFAULT))
    args = ap.parse_args()
    cert_path = Path(args.cert).resolve()
    out_path = Path(args.out).resolve()

    cert = json.loads(cert_path.read_text())
    if cert["kind"] != "n9-typed-cap-cert" and "tag" not in cert:
        log(f"[warn ] 证书 kind={cert.get('kind')!r}（继续，字段面以 blocks 为准）")
    lo = Fraction(cert["params"]["a0"])
    M, K = cert["params"]["M"], cert["params"]["K"]
    if (lo, M, K) != (Fraction(-187, 250), 9, 6):
        fail(f"证书参数失配：a0={lo}, M={M}, K={K}（预期 −187/250, 9, 6）")
    b = cert["blocks"]
    asm = Minorant(lo, M)
    if asm.b2 != Fraction(437, 500):
        fail(f"b2={asm.b2} ≠ 437/500")
    if asm.w_hat != Fraction(117, 125):
        fail(f"w_hat={asm.w_hat} ≠ 117/125")

    r9 = json.loads(R9JSON_PATH.read_text())
    if Fraction(r9["sizes"]["b2"]) != asm.b2 or \
            Fraction(r9["sizes"]["w_hat"]) != asm.w_hat:
        fail("r9_s3_rederive.json b2/w_hat 与本装配失配")

    blocks_out, residual_out, R2_exact, r9_match = {}, {}, {}, {}
    for cls in CLASSES:
        h = [Fraction(x) for x in b[f"h_{cls}_diag"]]
        if len(h) != asm.d_H + 1:
            fail(f"h_{cls} 长度 {len(h)} ≠ d_H+1")
        rhs = asm.rhs(h)
        Sb = {nm: [[Fraction(x) for x in row] for row in b[f"sig_{cls}_{nm}"]]
              for (nm, _my, _mu) in asm.sig_def}
        lhs = asm.lhs(Sb)
        diff = [rhs[j] - lhs[j] for j in range(asm.deg_p + 1)]
        sgn = [Fraction(s) for s in
               ((1 if d > 0 else (-1 if d < 0 else 0)) for d in diff)]
        R2 = sum(abs(d) * asm.w_hat ** j for j, d in enumerate(diff))
        R2_exact[cls] = R2
        r9_match[cls] = (R2 == Fraction(r9["R2_exact"][cls]))
        if not r9_match[cls]:
            fail(f"R2_{cls} 与 r9_s3_rederive.json R2_exact 逐位失配")
        nz = sum(1 for d in diff if d != 0)
        if nz != 33:
            fail(f"{cls} 残差非零系数 {nz} ≠ 33")
        residual_out[cls] = dict(
            lhs=[str(v) for v in lhs], rhs=[str(v) for v in rhs],
            diff=[str(v) for v in diff], sgn=[str(v) for v in sgn],
            nz_count=nz)
        for (nm, mons_y, _mu) in asm.sig_def:
            S = Sb[nm]
            n = len(mons_y)
            if len(S) != n or any(len(r) != n for r in S):
                fail(f"sig_{cls}_{nm} 尺寸 {len(S)}×{[len(r) for r in S]} ≠ {n}")
            if any(S[i][j] != S[j][i] for i in range(n) for j in range(n)):
                fail(f"sig_{cls}_{nm} 非对称")
            L, D = ldl(S)
            recon = [[sum(L[i][k] * D[k] * L[j][k] for k in range(min(i, j) + 1))
                      for j in range(n)] for i in range(n)]
            if not mat_eq(recon, S):
                fail(f"sig_{cls}_{nm} LDLᵀ 重构 ≠ S（逐位）")
            if not all(d > 0 for d in D):
                fail(f"sig_{cls}_{nm} 存在非正主元")
            Mm = [[L[i][j] * D[j] for j in range(n)] for i in range(n)]
            blocks_out[f"{cls}_{nm}"] = dict(
                dim=n, nnz=sum(1 for r in S for x in r if x),
                S=[[str(x) for x in r] for r in S],
                L=[[str(x) for x in r] for r in L],
                D=[str(x) for x in D],
                M=[[str(x) for x in r] for r in Mm],
                pivots_pos=[bool(d > 0) for d in D],
                all_pivots_pos=True, min_pivot=str(min(D)),
                recon_bitwise=True)
        log(f"[A6   ] {cls}: R2 == r9 R2_exact 逐位 ✓；残差非零 {nz}/34；"
            f"4 块 LDLᵀ 全主元>0＋重构逐位 ✓")

    doc = dict(
        kind="n9-r13-a6-data",
        script="bounds/r13_a6_data.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        cli=dict(argv=sys.argv[1:], cert=str(cert_path), out=str(out_path)),
        inputs=dict(
            certificate=str(cert_path),
            certificate_is_sole_derivation_input=True,
            r9_s3_rederive=str(R9JSON_PATH),
            r9_s3_rederive_role="R2_exact 对账目标（验收 ④），不参与推导",
            cert_provenance_echo=dict(
                code_version=cert["provenance"]["code_version"],
                round_bits=cert["provenance"]["round_bits"],
                solution_sha256_16=cert["provenance"]["solution_sha256_16"],
                date=cert["provenance"]["date"])),
        params=dict(lo=str(lo), M=M, K=K, d_H=asm.d_H, deg_p=asm.deg_p,
                    b2=str(asm.b2), b2_value="437/500",
                    w_hat=str(asm.w_hat), w_hat_value="117/125",
                    w_hat_formula="⌈√b²⌉，b²=(1−lo)/2",
                    multiplier_family=["1", "y", "b²−y²", "y·(b²−y²)"],
                    multiplier_domain="[0,b]（b²=437/500，√b 无理化陈述）",
                    p_formula=("p_cls(y)=σ₀(y)+y·σ₁(y)+(b²−y²)·σ₂(y)"
                               "+y·(b²−y²)·σ₃(y)"),
                    sigma_formula="σ_i(y)=v(y)ᵀ S_i v(y)，v(y)=(y^0..y^(n_i−1))"),
        sizes=dict(blocks=8, dims="AA/AB×sig0..3 = 17/17/16/16",
                   residual_coeffs=34, residual_nonzero=33),
        spot_points=dict(seed=SEED_SPOT,
                         y=[str(v) for v in spot_points()],
                         role="Lean 抽查求值定理的固定有理点（lhs 多项式 = p_cls 的抽样桥梁）"),
        blocks=blocks_out,
        residual=residual_out,
        R2_exact={c: str(v) for c, v in R2_exact.items()},
        R2_r9_match={c: bool(r9_match[c]) for c in CLASSES},
        checks=dict(
            all_ldlt_pivots_pos=True,
            all_ldlt_recon_bitwise=True,
            R2_exact_bitwise_match_r9=True,
            residual_nonzero_count_33=True,
            b2_is_437_500=True, w_hat_is_117_125=True),
        scope=("严格数值层（Python Fraction）；σ 块 LDLᵀ 平方表示、域非负乘子"
               "族与 R2 折减恒等式的 Lean 机器验证在 TableA6.lean（本件供字面量"
               "与复核）；H≤φ 逐点优越性与一般 Lukács 存在定理不在本件"),
        wall_s=round(time.time() - t0, 1),
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    log(f"[done ] A6 数据件全过（{doc['wall_s']}s）：8 块 LDLᵀ（全主元>0＋重构"
        f"逐位）＋R2 两类对账 match＋残差 33 带号；出 {out_path}；exit 0")


if __name__ == "__main__":
    main()
