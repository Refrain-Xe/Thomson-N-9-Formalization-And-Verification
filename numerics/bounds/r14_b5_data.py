#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r14_b5_data.py — R14A 表 B 首件 B5（Procrustes 刚性常数）数据发射器
（D56 主攻件；heavySolves=0，零求解零 SDP 零新数值证书）.

任务书口径（r14a-b5-procrustes-lean）：l4.json 的常数已是精确 Fraction
（无 dyadic 舍入面），本发射器以 stdlib Fraction 只读消费
results/l4.json＋results/local_min.json，独立第二实现重导全部常数层对象、
发射 formal/lean/ThomsonN9/TableB5Data.lean（仅 import Mathlib，ℚ 字面量
＋装配恒等式四件＋λ 支配前提＋S 区间端点事实＋diagQ 随机点抽查）并回读
自检逐位对账。主件 TableB5.lean（二次型对角化恒等式＋λ 夹逼＋S 容器＋
sqrt 界＋C/δ_max 有效性）为手写件，不含数值字面量，由验收门
r14_b5_gate.py G2/G3/G4 验证——本发射器只对其在场性与 import 面做弱检查。

数学层（三层，与 l4_procrustes.py 对账但不 import 它——独立第二实现）：
  (i) TTP 族（tri_cap_prism）9 行构型二次型对角化：
      行集 = 上三角 (ρ,0,z),(−ρ/2,±√3ρ/2,z),(−ρ/2,∓√3ρ/2,z) ＋ 下三角
      同构 z→−z ＋ 三帽行 (1/2,±√3/2,0),(−1,0,0)，ρ=√(1−z²)。符号引擎在
      ℚ[ρ,s]/(ρ²=1−z², s²=3) 上算 Σᵢ(xᵢ·v)² 与 Gram S=XᵀX，验证
      vᵀXᵀXv == (3(1−z²)+3/2)(v₀²+v₁²)+6z²v₂²（diagQ）、S 对角为
      (3(1−z²)+3/2, 3(1−z²)+3/2, 6z²)、S 非对角全零（Lean 面以混合二阶
      差消失陈述，D57-3）。z 盒取 local_min.json zStarIntervalMpmath 严格
      隔离区间（与 l4.json ttp_interval.z_box 逐位同源，重导验证）。
  (ii) 常数装配恒等式四件（ℚ norm_num 面的字面量三方对账 json↔源码↔重算）：
      C_inner==u₁·s1_up/l₃²+2/s3_dn、C==sqrt72_up·C_inner、C_chord==2C、
      δ_max==(s3_dn/(2·s1_up))·l₃²/(sqrt72_up·u₁)（min(1/2,·) 取
      s3_dn/(2·s1_up) 支路——reg2<1/2 独立验证）。
  (iii) 有效性前提（ℚ 字面量）：sqrt 有理界四件前提（s1_up²≥u₁、s3_dn²≤l₃、
      sqrt72_up²≥72、s3_dn≤s1_up）＋对角路线支配记录 λ 界（6z_lo²≥l₃、
      9/2−3z_lo²≤u₁、z_hi²<1/2）＋S 区间容器（S22 端点==6z² 逐位、
      S00/S11 为 ρ 外扩严格容器、非对角对称含 0）。

抽查（seed 20261016，A5/A6 家法）：z 盒内 3 个随机有理点（2⁻⁴⁰ 网格，
i=rng.randint(⌊z_lo·2⁴⁰⌋,⌈z_hi·2⁴⁰⌉)，z=i/2⁴⁰）×v 三分量（/64 网格），
期望值 diagQ 由发射器 Fraction 重算、门内独立第二实现（符号行展开）复算。

诚实边界（docstring 级，表 B 首件范围声明）：d_P(X,Y)≤C·δ 的解析本体
（l4_procrustes.py 证明步骤 1–6：投影分解/极分解/旋转规范）不在本件；
区间 Sylvester 法 soundness（顶点多线性）为 stretch 非必需面，未成不阻断。

用法（CWD 无关）：
  python3 numerics/bounds/r14_b5_data.py
产出：
  formal/lean/ThomsonN9/TableB5Data.lean（确定性发射）
  numerics/bounds/results/r14_b5_data.json
"""
from __future__ import annotations

import hashlib
import json
import math
import random
import subprocess
import time
from datetime import datetime, timezone
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                       # thomson-n9/

L4_JSON = RESULTS / "l4.json"
LOCAL_MIN_JSON = RESULTS / "local_min.json"
OUT_JSON = RESULTS / "r14_b5_data.json"
DATA_LEAN = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Data.lean"
MAIN_LEAN = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5.lean"

SEED = 20261016                             # R14 各件统一 seed（D56 任务书）
SQ_BITS = 200                               # 有理平方根包精度（bit，与 l4 同族参数）
ZGRID = 1 << 40                             # z 盒随机点网格 2⁻⁴⁰（宽度 ~838,863 格）

F0, F1 = Fr(0), Fr(1)
FHALF = Fr(1, 2)


def log(msg: str) -> None:
    print(f"[r14b5] {msg}", flush=True)


def code_version() -> str:
    r = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                       cwd=str(REPO), capture_output=True, text=True)
    if r.returncode != 0:
        return "unknown"
    return r.stdout.strip() + ("-dirty" if subprocess.run(
        ["git", "diff", "--quiet"], cwd=str(REPO)).returncode != 0 else "")


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fail(msg: str) -> None:
    raise SystemExit(f"[r14b5][FAIL] {msg}")


# ============================================================ 独立第二实现
def sqrt_rat(q: Fr, side: str) -> Fr:
    """√q 的有理下界（'lo'）/上界（'hi'），整数 Newton（math.isqrt），q>0。

    与 l4_procrustes.sqrt_rat 同族算法的独立重导（不 import 之）：上界侧
    取 isqrt(⌊q·2^(2p)⌋+1)+1 保证严格上界，下界侧取 isqrt 严格下界。
    """
    p = SQ_BITS
    num, den = q.numerator, q.denominator
    if side == "lo":
        return Fr(math.isqrt((num << (2 * p)) // den), 1 << p)
    return Fr(math.isqrt((num << (2 * p)) // den + 1) + 1, 1 << p)


# ---- 符号引擎：ℚ[ρ,s]/(ρ²=1−z², s²=3) 上的多项式（monomial = (e_r, e_s)）
MONOS = ((0, 0), (1, 0), (0, 1), (1, 1))     # 基 {1, ρ, s, ρs}


def poly_add(a, b):
    return {k: a.get(k, F0) + b.get(k, F0) for k in MONOS}


def poly_mul(a, b, r2: Fr):
    out = {k: F0 for k in MONOS}
    for (ar, as_), ca in a.items():
        if ca == 0:
            continue
        for (br, bs), cb in b.items():
            if cb == 0:
                continue
            er, es = ar + br, as_ + bs
            c = ca * cb
            if es >= 2:                       # s² = 3
                es -= 2
                c *= 3
            if er >= 2:                       # ρ² = 1 − z²（以 r2 代入）
                er -= 2
                c *= r2
            assert es < 2 and er < 2
            out[(er, es)] += c
    return out


def poly_scale(a, c: Fr):
    return {k: v * c for k, v in a.items()}


def ttp_rows(z: Fr) -> list:
    """9 行 TTP 构型（tri_cap_prism），每行 3 个坐标各为 {monomial: 系数}。

    行序（与 l4_procrustes.ttp_interval 同构）：上三角 k=0,1,2（z 坐标 +z）
    → 下三角 k=0,1,2（z 坐标 −z）→ 三帽行。坐标：
      三角 (ρ,0,±z)、(−ρ/2, √3ρ/2, ±z)、(−ρ/2, −√3ρ/2, ±z)
      帽   (1/2, √3/2, 0)、(−1,0,0)、(1/2, −√3/2, 0)
    """
    rows = []
    rho = {(1, 0): F1}                       # ρ
    s = {(0, 1): F1}                         # √3
    for zs in (z, -z):                       # 上三角、下三角
        zc = {(0, 0): zs}
        rows.append([rho, {k: F0 for k in MONOS}, zc])
        rows.append([poly_scale(rho, Fr(-1, 2)),
                     poly_scale(poly_mul(rho, s, F1), FHALF), zc])
        rows.append([poly_scale(rho, Fr(-1, 2)),
                     poly_scale(poly_mul(rho, s, F1), -FHALF), zc])
    rows.append([{(0, 0): FHALF}, poly_scale(s, FHALF),
                 {k: F0 for k in MONOS}])
    rows.append([{(0, 0): -F1}, {k: F0 for k in MONOS},
                 {k: F0 for k in MONOS}])
    rows.append([{(0, 0): FHALF}, poly_scale(s, -FHALF),
                 {k: F0 for k in MONOS}])
    return rows


def symbolic_gram(z: Fr) -> list:
    """S = XᵀX 的 3×3 符号矩阵（ρ²=1−z² 代入后；z 本身为有理数）。"""
    r2 = F1 - z * z
    rows = ttp_rows(z)
    S = [[{k: F0 for k in MONOS} for _ in range(3)] for _ in range(3)]
    for r in rows:
        for i in range(3):
            for j in range(3):
                S[i][j] = poly_add(S[i][j], poly_mul(r[i], r[j], r2))
    return S


def symbolic_quad(z: Fr, v) -> Fr:
    """Σᵢ(xᵢ·v)² 的精确有理值（符号求值后取常数项；验证 ρ/s 项全零）。"""
    r2 = F1 - z * z
    rows = ttp_rows(z)
    tot = {k: F0 for k in MONOS}
    for r in rows:
        dot = {k: F0 for k in MONOS}
        for c, vi in zip(r, v):
            dot = poly_add(dot, poly_mul(c, {(0, 0): vi}, r2))
        tot = poly_add(tot, poly_mul(dot, dot, r2))
    for k in MONOS:
        if k != (0, 0) and tot[k] != 0:
            fail(f"符号二次型 ρ/s 项非零（{k}={tot[k]}）——对角化失败")
    return tot[(0, 0)]


def diag_q(z: Fr, v0: Fr, v1: Fr, v2: Fr) -> Fr:
    """对角化公式 diagQ = (3(1−z²)+3/2)(v₀²+v₁²)+6z²v₂²（Fraction）。"""
    a = 3 * (F1 - z * z) + Fr(3, 2)
    return a * (v0 * v0 + v1 * v1) + 6 * z * z * v2 * v2


# ============================================================ 重导层
def rederive():
    l4 = json.loads(L4_JSON.read_text())
    lm = json.loads(LOCAL_MIN_JSON.read_text())
    ti = l4["ttp_interval"]
    co = l4["constants"]

    # z 盒：local_min zStarIntervalMpmath 重导（Fraction）== l4.json z_box 逐位
    zl_s, zh_s = lm["zStarIntervalMpmath"].strip("[]").split(", ")
    z_lo, z_hi = Fr(zl_s.strip()), Fr(zh_s.strip())
    z_box_json = [Fr(*[int(x) for x in s.split("/")]) for s in ti["z_box"]]
    if [z_lo, z_hi] != z_box_json:
        fail("z 盒重导失配：local_min zStarIntervalMpmath ≠ l4.json z_box")

    l3 = Fr(ti["lambda3_lower_exact"])
    u1 = Fr(ti["lambda1_upper_exact"])
    # λ 界独立复核：l3/u1 的 10⁻⁶ 网格值（区间 Sylvester 产物）满足对角路线支配
    if l3 != Fr(1485363, 500000) or u1 != Fr(1507319, 500000):
        fail("λ 界字面量与重导网格值失配（1485363/500000, 1507319/500000）")

    # sqrt 有理包独立重导（Newton 200-bit）＋与 l4.json 记录值逐位对账
    s1_up = sqrt_rat(u1, "hi")
    s3_dn = sqrt_rat(l3, "lo")
    sqrt72_up = sqrt_rat(Fr(72), "hi")
    if str(s1_up) != ti["sigma1_upper"]:
        fail("s1_up 重导 ≠ l4.json sigma1_upper")
    if str(s3_dn) != ti["sigma3_lower"]:
        fail("s3_dn 重导 ≠ l4.json sigma3_lower")

    # 装配四件独立重算
    C_inner = u1 * s1_up / (l3 * l3) + Fr(2) / s3_dn
    C_val = sqrt72_up * C_inner
    C_chord = 2 * C_val
    reg2 = s3_dn / (2 * s1_up)
    reg = min(FHALF, reg2)
    delta_max = reg * l3 * l3 / (sqrt72_up * u1)
    for name, mine, ref in (
            ("C_inner", C_inner, co["C_inner_Frobenius_exact"]),
            ("C", C_val, co["C_exact"]),
            ("C_chord", C_chord, co["C_chord_distance_exact"]),
            ("delta_max", delta_max, co["delta_max_exact"])):
        if str(mine) != ref:
            fail(f"装配恒等式 {name} 重算 ≠ l4.json 记录值")

    # S 区间容器（对角端点 ∈ 记录区间；S22 端点==6z² 逐位；非对角对称含 0）
    S_iv = [[tuple(Fr(x) for x in c.strip("[]").split(",")) for c in row]
            for row in ti["S_interval"]]
    a_hi = 3 * (F1 - z_lo * z_lo) + Fr(3, 2)     # a 随 z² 递减 ⇒ z=z_lo 处最大
    a_lo = 3 * (F1 - z_hi * z_hi) + Fr(3, 2)
    for k, (i, j) in enumerate([(0, 0), (1, 1)]):
        lo, hi = S_iv[i][j]
        if not (lo < a_lo and a_hi < hi):
            fail(f"S[{i}][{j}] 非 ρ 外扩严格容器")
    if S_iv[2][2] != (6 * z_lo * z_lo, 6 * z_hi * z_hi):
        fail("S[2][2] 端点 ≠ 6z² 逐位")
    for (i, j) in [(0, 1), (0, 2), (1, 2)]:
        lo, hi = S_iv[i][j]
        if lo != -hi or not (lo <= 0 <= hi):
            fail(f"S[{i}][{j}] 非对称含零区间")

    # 符号引擎：对角化恒等式＋Gram 结构（z 盒两端点＋中点三处符号验证）
    sym_checks = []
    for z in (z_lo, z_hi, (z_lo + z_hi) / 2):
        S = symbolic_gram(z)
        want = [[Fr(0)] * 3 for _ in range(3)]
        a = 3 * (F1 - z * z) + Fr(3, 2)
        want[0][0] = want[1][1] = a
        want[2][2] = 6 * z * z
        for i in range(3):
            for j in range(3):
                got = S[i][j]
                extra = {k: v for k, v in got.items() if k != (0, 0) and v != 0}
                if extra:
                    fail(f"z={z}: S[{i}][{j}] 有非平凡 ρ/s 项（{extra}）")
                got_v = got[(0, 0)]
                if got_v != want[i][j]:
                    fail(f"z={z}: S[{i}][{j}]={got_v} ≠ 对角真值 {want[i][j]}")
        sym_checks.append(fs(z))
    return dict(l4=l4, lm=lm, z_lo=z_lo, z_hi=z_hi, l3=l3, u1=u1,
                s1_up=s1_up, s3_dn=s3_dn, sqrt72_up=sqrt72_up,
                C_inner=C_inner, C_val=C_val, C_chord=C_chord,
                reg2=reg2, delta_max=delta_max, S_iv=S_iv,
                a_lo=a_lo, a_hi=a_hi, sym_checks=sym_checks)


# ============================================================ 抽查点
def spot_points(z_lo: Fr, z_hi: Fr):
    """seed 20261016 固定抽样：3 个 z∈盒（2⁻⁴⁰ 网格）×v 三分量（/64）。

    顺序（复现关键）：对 k=0,1,2 依次 i=randint(⌊z_lo·2⁴⁰⌋,⌈z_hi·2⁴⁰⌉)、
    z=i/2⁴⁰，随后 vⱼ=Fraction(randint(−64,64),64) 三连。
    """
    rng = random.Random(SEED)
    lo_i = math.floor(z_lo * ZGRID)
    hi_i = math.ceil(z_hi * ZGRID)
    pts = []
    for _ in range(3):
        i = rng.randint(lo_i, hi_i)
        z = Fr(i, ZGRID)
        if not (z_lo <= z <= z_hi):
            fail(f"抽查 z 越盒：{z}")
        v = [Fr(rng.randint(-64, 64), 64) for _ in range(3)]
        pts.append((z, v))
    return pts


# ============================================================ Lean 发射
def emit_data_lean(W, spots):
    def d(name: str, val: Fr, doc: str) -> str:
        return f"/-- {doc} -/\ndef {name} : ℚ := {fs(val)}\n"

    L = []
    L.append("import Mathlib")
    L.append("/-!")
    L.append("# Table B5 data (R14 / r14a): the exact rational constants of the B5")
    L.append("# Procrustes rigidity package")
    L.append("")
    L.append("This module is deliberately self-contained: it imports only `Mathlib`,")
    L.append("imports no in-repo solution module, and is imported only by")
    L.append("`ThomsonN9/TableB5.lean`.  It materialises, as explicit `ℚ` literals,")
    L.append("the constant layer of the L4 Procrustes theorem")
    L.append("(`numerics/bounds/results/l4.json`, read-only, re-derived here through")
    L.append("the independent second implementation of `numerics/bounds/r14_b5_data.py`:")
    L.append("stdlib-Fraction Newton square-root envelopes and a symbolic engine over")
    L.append("ℚ[ρ,√3]/(ρ² = 1−z², (√3)² = 3); provenance = sha256 of l4.json and")
    L.append("local_min.json, recorded in `results/r14_b5_data.json` — the constants are")
    L.append("exact Fractions, so there is no dyadic rounding surface here):")
    L.append("")
    L.append("* `zLo`, `zHi` — the TTP z-box, identical to the strict isolation")
    L.append("  interval `zStarIntervalMpmath` of `results/local_min.json`;")
    L.append("* `l3`, `u1` — the recorded interval-Sylvester eigenvalue bounds")
    L.append("  λ₃ ≥ l₃, λ₁ ≤ u₁, dominated by the diagonal route")
    L.append("  (6·zLo² ≥ l₃, 9/2 − 3·zLo² ≤ u₁, zHi² < 1/2);")
    L.append("* `s1Up`, `s3Dn`, `sqrt72Up` — the 200-bit rational square-root")
    L.append("  envelopes σ₁ ≤ s1Up, σ₃ ≥ s3Dn, √72 ≤ sqrt72Up;")
    L.append("* `CInner`, `CVal`, `CChord`, `deltaMax` — the four assembled")
    L.append("  constants, with the four assembly identities as `norm_num` theorems")
    L.append("  (636-bit Fractions, D56 probe ②);")
    L.append("* the twelve `S**` endpoints — the recorded l4.json `S_interval`")
    L.append("  entries (S22 endpoints are exactly 6·zLo² / 6·zHi²; S00/S11 are")
    L.append("  strictly widened ρ-enclosures; the off-diagonal recorded intervals")
    L.append("  are symmetric and contain 0);")
    L.append("* `diagQ` — the ℚ diagonal quadratic form of the TTP family,")
    L.append("  (3(1−z²)+3/2)(v₀²+v₁²) + 6z²v₂², with three fixed random rational")
    L.append("  spot checks (seed 20261016, z on the 2⁻⁴⁰ grid inside the z-box,")
    L.append("  v on the /64 grid) whose expected values are independently computed")
    L.append("  in Python `Fraction` and cross-checked by the gate's symbolic")
    L.append("  row-expansion second implementation.")
    L.append("")
    L.append("Honest scope note (B5-first-piece boundary): the analytic body")
    L.append("d_P(X,Y) ≤ C·δ (l4_procrustes.py proof steps 1–6: projection split /")
    L.append("polar decomposition / rotation normalisation) is NOT part of this file;")
    L.append("`TableB5.lean` proves the constant-layer validity theorems only.")
    L.append("-/")
    L.append("")
    L.append("set_option maxHeartbeats 1000000")
    L.append("set_option linter.unusedVariables false")
    L.append("")
    L.append("namespace ThomsonN9.TableB5Data")
    L.append("")
    L.append(d("zLo", W["z_lo"], "TTP z 盒下端（local_min zStarIntervalMpmath 严格隔离区间下端，与 l4.json z_box 逐位同源）。"))
    L.append(d("zHi", W["z_hi"], "TTP z 盒上端（同上）。"))
    L.append(d("l3", W["l3"], "记录 λ₃ 下界（区间 Sylvester 产物；对角路线支配：6·zLo² ≥ l₃）。"))
    L.append(d("u1", W["u1"], "记录 λ₁ 上界（区间 Sylvester 产物；对角路线支配：9/2 − 3·zLo² ≤ u₁）。"))
    L.append(d("s1Up", W["s1_up"], "σ₁ = √λ₁ 的 200-bit 有理上界包（s1Up² ≥ u₁）。"))
    L.append(d("s3Dn", W["s3_dn"], "σ₃ = √λ₃ 的 200-bit 有理下界包（s3Dn² ≤ l₃）。"))
    L.append(d("sqrt72Up", W["sqrt72_up"], "√72 的 200-bit 有理上界包（sqrt72Up² ≥ 72）。"))
    L.append(d("CInner", W["C_inner"], "内积口径内常数 C_inner = u₁·s1Up/l₃² + 2/s3Dn（Frobenius 谱因子）。"))
    L.append(d("CVal", W["C_val"], "C = sqrt72Up·CInner（η ≤ √72·δ 口径下的 d_P ≤ C·δ 常数）。"))
    L.append(d("CChord", W["C_chord"], "弦距离口径常数 C_chord = 2·C。"))
    L.append(d("deltaMax", W["delta_max"], "适用域半径 δ_max = (s3Dn/(2·s1Up))·l₃²/(sqrt72Up·u₁)（min(1/2, σ₃/(2σ₁)) 取 s3Dn/(2·s1Up) 支路）。"))
    for (nm, val, doc) in [
            ("S00lo", W["S_iv"][0][0][0], "记录 S[0][0] 区间下端（ρ 外扩，严格容 a(z)）。"),
            ("S00hi", W["S_iv"][0][0][1], "记录 S[0][0] 区间上端。"),
            ("S11lo", W["S_iv"][1][1][0], "记录 S[1][1] 区间下端。"),
            ("S11hi", W["S_iv"][1][1][1], "记录 S[1][1] 区间上端。"),
            ("S22lo", W["S_iv"][2][2][0], "记录 S[2][2] 区间下端 == 6·zLo² 逐位。"),
            ("S22hi", W["S_iv"][2][2][1], "记录 S[2][2] 区间上端 == 6·zHi² 逐位。"),
            ("S01lo", W["S_iv"][0][1][0], "记录 S[0][1] 区间下端（对称含 0）。"),
            ("S01hi", W["S_iv"][0][1][1], "记录 S[0][1] 区间上端。"),
            ("S02lo", W["S_iv"][0][2][0], "记录 S[0][2] 区间下端（对称含 0）。"),
            ("S02hi", W["S_iv"][0][2][1], "记录 S[0][2] 区间上端。"),
            ("S12lo", W["S_iv"][1][2][0], "记录 S[1][2] 区间下端（对称含 0）。"),
            ("S12hi", W["S_iv"][1][2][1], "记录 S[1][2] 区间上端。")]:
        L.append(d(nm, val, doc))
    L.append("/-- TTP 族对角化二次型（ℚ 面）：vᵀXᵀXv 的对角公式。 -/")
    L.append("def diagQ (z v0 v1 v2 : ℚ) : ℚ := (3*(1-z^2)+3/2)*(v0^2+v1^2) + 6*z^2*v2^2")
    L.append("")
    # ---- A 组：z 盒与 λ 支配前提
    L.append("/-- z 盒下端为正（z 盒内 z>0，z² 单调可比）。 -/")
    L.append("theorem zLo_pos : (0:ℚ) < zLo := by norm_num [zLo]")
    L.append("/-- z_hi² < 1/2（⇒ 6z_hi² < 3 ≤ u₁ 且 a(z) = 3(1−z²)+3/2 > 3 > l₃）。 -/")
    L.append("theorem zHi_sq_lt_half : zHi^2 < 1/2 := by norm_num [zHi]")
    L.append("/-- 对角路线支配记录 λ₃ 下界：l₃ ≤ 6·zLo²。 -/")
    L.append("theorem six_zLo_sq_ge_l3 : l3 ≤ 6 * zLo^2 := by norm_num [zLo, l3]")
    L.append("/-- 对角路线支配记录 λ₁ 上界：9/2 − 3·zLo² ≤ u₁（a(zLo) ≤ u₁）。 -/")
    L.append("theorem fourhalf_three_zLo_le_u1 : 9/2 - 3 * zLo^2 ≤ u1 := by norm_num [zLo, u1]")
    L.append("/-- l₃ > 0（λ₃ ≥ l₃ > 0）。 -/")
    L.append("theorem l3_pos : (0:ℚ) < l3 := by norm_num [l3]")
    L.append("/-- l₃ < 3（配合 z_hi²<1/2 给 l₃ ≤ a(z)）。 -/")
    L.append("theorem l3_lt_three : l3 < 3 := by norm_num [l3]")
    L.append("/-- 3 ≤ u₁（配合 z_hi²<1/2 给 6z² ≤ u₁）。 -/")
    L.append("theorem three_le_u1 : (3:ℚ) ≤ u1 := by norm_num [u1]")
    L.append("/-- l₃ ≤ u₁（λ 序 l₃ ≤ λ₃ ≤ λ₁ ≤ u₁ 的端点相容）。 -/")
    L.append("theorem l3_le_u1 : l3 ≤ u1 := by norm_num [l3, u1]")
    L.append("")
    # ---- B 组：sqrt 有理界前提
    L.append("/-- s1Up > 0。 -/")
    L.append("theorem s1Up_pos : (0:ℚ) < s1Up := by norm_num [s1Up]")
    L.append("/-- s3Dn > 0。 -/")
    L.append("theorem s3Dn_pos : (0:ℚ) < s3Dn := by norm_num [s3Dn]")
    L.append("/-- sqrt72Up > 0。 -/")
    L.append("theorem sqrt72Up_pos : (0:ℚ) < sqrt72Up := by norm_num [sqrt72Up]")
    L.append("/-- deltaMax > 0（适用域非空）。 -/")
    L.append("theorem deltaMax_pos : (0:ℚ) < deltaMax := by norm_num [deltaMax]")
    L.append("/-- sqrt 界前提①：u₁ ≤ s1Up²（⇒ √u₁ ≤ s1Up）。 -/")
    L.append("theorem s1Up_sq_ge_u1 : u1 ≤ s1Up^2 := by norm_num [s1Up, u1]")
    L.append("/-- sqrt 界前提②：s3Dn² ≤ l₃（⇒ s3Dn ≤ √l₃）。 -/")
    L.append("theorem s3Dn_sq_le_l3 : s3Dn^2 ≤ l3 := by norm_num [s3Dn, l3]")
    L.append("/-- sqrt 界前提③：72 ≤ sqrt72Up²（⇒ √72 ≤ sqrt72Up）。 -/")
    L.append("theorem sqrt72Up_sq_ge_72 : (72:ℚ) ≤ sqrt72Up^2 := by norm_num [sqrt72Up]")
    L.append("/-- sqrt 界前提④：s3Dn ≤ s1Up（⇒ s3Dn/(2·s1Up) ≤ 1/2，δ_max 适用的 min 支路）。 -/")
    L.append("theorem s3Dn_le_s1Up : s3Dn ≤ s1Up := by norm_num [s3Dn, s1Up]")
    L.append("")
    # ---- C 组：装配恒等式四件
    L.append("/-- 装配①：C_inner = u₁·s1Up/l₃² + 2/s3Dn（636-bit norm_num，D56 探针②）。 -/")
    L.append("theorem C_inner_val : u1 * s1Up / (l3*l3) + 2/s3Dn = CInner := by\n  norm_num [u1, s1Up, l3, s3Dn, CInner]")
    L.append("/-- 装配②：C = sqrt72Up·CInner。 -/")
    L.append("theorem C_val : sqrt72Up * CInner = CVal := by norm_num [sqrt72Up, CInner, CVal]")
    L.append("/-- 装配③：C_chord = 2·C（弦距离口径）。 -/")
    L.append("theorem C_chord_val : 2 * CVal = CChord := by norm_num [CVal, CChord]")
    L.append("/-- 装配④：δ_max = (s3Dn/(2·s1Up))·l₃²/(sqrt72Up·u₁)。 -/")
    L.append("theorem delta_max_val : (s3Dn/(2*s1Up)) * (l3*l3) / (sqrt72Up * u1) = deltaMax := by\n  norm_num [s3Dn, s1Up, l3, sqrt72Up, u1, deltaMax]")
    L.append("")
    # ---- D 组：S 区间端点事实
    L.append("/-- S[2][2] 记录区间端点==6z² 逐位（下端）。 -/")
    L.append("theorem S22_lo_eq : S22lo = 6 * zLo^2 := by norm_num [S22lo, zLo]")
    L.append("/-- S[2][2] 记录区间端点==6z² 逐位（上端）。 -/")
    L.append("theorem S22_hi_eq : S22hi = 6 * zHi^2 := by norm_num [S22hi, zHi]")
    L.append("/-- S[0][0] 为 ρ 外扩严格容器：S00lo < a(zHi) 且 a(zLo) < S00hi。 -/")
    L.append("theorem S00_container : S00lo < 9/2 - 3*zHi^2 ∧ 9/2 - 3*zLo^2 < S00hi := by\n  constructor <;> norm_num [S00lo, S00hi, zLo, zHi]")
    L.append("/-- S[1][1] 为 ρ 外扩严格容器。 -/")
    L.append("theorem S11_container : S11lo < 9/2 - 3*zHi^2 ∧ 9/2 - 3*zLo^2 < S11hi := by\n  constructor <;> norm_num [S11lo, S11hi, zLo, zHi]")
    L.append("/-- S[0][1] 记录区间对称且上端为正（真值 0 ∈ 区间）。 -/")
    L.append("theorem S01_sym : S01lo = -S01hi ∧ 0 < S01hi := by constructor <;> norm_num [S01lo, S01hi]")
    L.append("/-- S[0][2] 记录区间对称且上端为正。 -/")
    L.append("theorem S02_sym : S02lo = -S02hi ∧ 0 < S02hi := by constructor <;> norm_num [S02lo, S02hi]")
    L.append("/-- S[1][2] 记录区间对称且上端为正。 -/")
    L.append("theorem S12_sym : S12lo = -S12hi ∧ 0 < S12hi := by constructor <;> norm_num [S12lo, S12hi]")
    L.append("")
    # ---- E 组：diagQ 抽查（3 点）
    for k, (z, v) in enumerate(spots):
        q = diag_q(z, *v)
        norm2 = sum(c * c for c in v)
        zs = fs(z)
        vs = " ".join(fs(c) for c in v)
        n2 = " + ".join(f"({fs(c)})^2" for c in v)
        args = f"({zs}) " + " ".join(f"({fs(c)})" for c in v)
        L.append(f"/-- 抽查 {k}（seed 20261016）：diagQ 于盒内有理点求值＝独立 Fraction 期望值。 -/")
        L.append(f"theorem diagQ_spot{k} : diagQ {args} = ({fs(q)}) := by")
        L.append("  unfold diagQ; norm_num")
        L.append(f"/-- 抽查 {k}（seed 20261016）：λ 夹逼在该盒内随机点成立（l₃‖v‖² ≤ q ≤ u₁‖v‖²）。 -/")
        L.append(f"theorem diagQ_sandwich_spot{k} :")
        L.append(f"    l3 * ({n2}) ≤ diagQ {args} ∧ diagQ {args} ≤ u1 * ({n2}) := by")
        L.append("  constructor <;> unfold diagQ <;> norm_num [l3, u1]")
    L.append("")
    L.append("end ThomsonN9.TableB5Data")
    DATA_LEAN.parent.mkdir(parents=True, exist_ok=True)
    DATA_LEAN.write_text("\n".join(L) + "\n")


# ============================================================ 回读自检
def reparse_defs(src: str) -> dict:
    import re
    out = {}
    for m in re.finditer(r"^def (\w+) : ℚ := (-?\d+/\d+)$", src, re.M):
        out[m.group(1)] = Fr(m.group(2))
    return out


def selfcheck(W, spots, parsed):
    want = {"zLo": W["z_lo"], "zHi": W["z_hi"], "l3": W["l3"], "u1": W["u1"],
            "s1Up": W["s1_up"], "s3Dn": W["s3_dn"], "sqrt72Up": W["sqrt72_up"],
            "CInner": W["C_inner"], "CVal": W["C_val"], "CChord": W["C_chord"],
            "deltaMax": W["delta_max"],
            "S00lo": W["S_iv"][0][0][0], "S00hi": W["S_iv"][0][0][1],
            "S11lo": W["S_iv"][1][1][0], "S11hi": W["S_iv"][1][1][1],
            "S22lo": W["S_iv"][2][2][0], "S22hi": W["S_iv"][2][2][1],
            "S01lo": W["S_iv"][0][1][0], "S01hi": W["S_iv"][0][1][1],
            "S02lo": W["S_iv"][0][2][0], "S02hi": W["S_iv"][0][2][1],
            "S12lo": W["S_iv"][1][2][0], "S12hi": W["S_iv"][1][2][1]}
    for k, v in want.items():
        if parsed.get(k) != v:
            fail(f"回读自检失配：def {k} 源码字面量 ≠ 重导值")
    # 抽查点：diagQ_spot 字面量重算（对角公式）＋符号引擎独立复算
    import re
    for k, (z, v) in enumerate(spots):
        m = re.search(rf"theorem diagQ_spot{k} : diagQ \((-?\d+/\d+)\) \((-?\d+/\d+)\)"
                      rf" \((-?\d+/\d+)\) \((-?\d+/\d+)\) = \((-?\d+)/(\d+)\)",
                      DATA_LEAN.read_text())
        if not m:
            fail(f"回读自检失配：diagQ_spot{k} 形状解析失败")
        zc = Fr(m.group(1))
        vc = [Fr(m.group(i)) for i in (2, 3, 4)]
        if (zc, vc) != (z, v):
            fail(f"回读自检失配：diagQ_spot{k} 点字面量 ≠ 抽样点")
        want_q = Fr(int(m.group(5)), int(m.group(6)))
        if diag_q(zc, *vc) != want_q or symbolic_quad(zc, vc) != want_q:
            fail(f"回读自检失配：diagQ_spot{k} 期望值双实现不一致")
    return len(want)


# ============================================================ 主流程
def main() -> None:
    t0 = time.time()
    W = rederive()
    log(f"[rederive] z 盒==local_min 严格区间逐位 ✓；λ 界/sqrt 包/装配四件/"
        f"S 容器独立重导全对账（对角路线支配 6z_lo²≥l₃、9/2−3z_lo²≤u₁、"
        f"z_hi²<1/2 全过；reg2=s3_dn/(2·s1_up)<1/2={W['reg2'] < FHALF}）")

    spots = spot_points(W["z_lo"], W["z_hi"])
    for k, (z, v) in enumerate(spots):
        qd = diag_q(z, *v)
        qs = symbolic_quad(z, v)
        if qd != qs:
            fail(f"抽查 {k}：对角公式 ≠ 符号行展开（{qd} vs {qs}）")
        n2 = sum(c * c for c in v)
        if not (W["l3"] * n2 <= qs <= W["u1"] * n2):
            fail(f"抽查 {k}：λ 夹逼数值失守")
    log(f"[spots ] seed={SEED} 3 点：diagQ==符号行展开逐位一致＋λ 夹逼全过")

    emit_data_lean(W, spots)
    parsed = reparse_defs(DATA_LEAN.read_text())
    n_defs = selfcheck(W, spots, parsed)
    log(f"[emit ] TableB5Data.lean（{DATA_LEAN.stat().st_size / 1e3:.0f}KB，"
        f"{n_defs} 个 ℚ def）＋回读自检逐位对账全过")

    if not MAIN_LEAN.is_file():
        fail("主件 TableB5.lean 不在场（手写件，须与本发射器同轮交付）")
    main_src = MAIN_LEAN.read_text()
    import re as _re
    if _re.findall(r"^import\s+\S+$", main_src, _re.M) != \
            ["import Mathlib", "import ThomsonN9.TableB5Data"]:
        fail("主件 import 面失配（应恰为 [Mathlib, ThomsonN9.TableB5Data]）")
    log("[main  ] TableB5.lean 在场且 import 面恰 [Mathlib, ThomsonN9.TableB5Data]")

    checks = dict(
        z_box_same_as_local_min=True,
        six_zLo_sq_ge_l3=W["l3"] <= 6 * W["z_lo"] ** 2,
        fourhalf_three_zLo_le_u1=Fr(9, 2) - 3 * W["z_lo"] ** 2 <= W["u1"],
        zHi_sq_lt_half=W["z_hi"] ** 2 < FHALF,
        l3_lt_three=W["l3"] < 3,
        three_le_u1=Fr(3) <= W["u1"],
        l3_le_u1=W["l3"] <= W["u1"],
        s1Up_sq_ge_u1=W["u1"] <= W["s1_up"] ** 2,
        s3Dn_sq_le_l3=W["s3_dn"] ** 2 <= W["l3"],
        sqrt72Up_sq_ge_72=Fr(72) <= W["sqrt72_up"] ** 2,
        s3Dn_le_s1Up=W["s3_dn"] <= W["s1_up"],
        reg2_lt_half=W["reg2"] < FHALF,
        delta_max_pos=0 < W["delta_max"],
        S00_strict=W["S_iv"][0][0][0] < W["a_lo"] and W["a_hi"] < W["S_iv"][0][0][1],
        S11_strict=W["S_iv"][1][1][0] < W["a_lo"] and W["a_hi"] < W["S_iv"][1][1][1],
        S22_endpoints_exact=W["S_iv"][2][2] == (6 * W["z_lo"] ** 2, 6 * W["z_hi"] ** 2),
        offdiag_symmetric_zero=all(
            W["S_iv"][i][j][0] == -W["S_iv"][i][j][1]
            and W["S_iv"][i][j][0] <= 0 <= W["S_iv"][i][j][1]
            for (i, j) in [(0, 1), (0, 2), (1, 2)]),
        symbolic_gram_diag=W["sym_checks"],
    )
    for k, v in checks.items():
        if v is False:
            fail(f"重导检查失守：{k}")

    doc = dict(
        kind="n9-r14-b5-data",
        task="r14a-b5-procrustes-lean",
        script="bounds/r14_b5_data.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        seed=SEED,
        heavy_solves=0,
        inputs=dict(
            l4_json=dict(path="numerics/bounds/results/l4.json",
                         sha256=sha256_of(L4_JSON), role="只读（常数/区间唯一记录源）"),
            local_min_json=dict(path="numerics/bounds/results/local_min.json",
                                sha256=sha256_of(LOCAL_MIN_JSON),
                                role="只读（z 盒唯一隔离源 zStarIntervalMpmath）")),
        constants=dict(
            z_lo=fs(W["z_lo"]), z_hi=fs(W["z_hi"]),
            z_box_source="local_min.json zStarIntervalMpmath（严格隔离区间；与 l4.json z_box 逐位同源）",
            l3=fs(W["l3"]), u1=fs(W["u1"]),
            s1_up=fs(W["s1_up"]), s3_dn=fs(W["s3_dn"]), sqrt72_up=fs(W["sqrt72_up"]),
            C_inner=fs(W["C_inner"]), C=fs(W["C_val"]), C_chord=fs(W["C_chord"]),
            reg2=fs(W["reg2"]), reg="min(1/2, reg2) = reg2（reg2 < 1/2 独立验证）",
            delta_max=fs(W["delta_max"]),
            float_advisory=dict(l3=float(W["l3"]), u1=float(W["u1"]),
                                C=float(W["C_val"]), C_chord=float(W["C_chord"]),
                                delta_max=float(W["delta_max"]))),
        assembly=dict(
            C_inner="u1*s1Up/(l3*l3) + 2/s3Dn",
            C="sqrt72Up*CInner", C_chord="2*CVal",
            delta_max="(s3Dn/(2*s1Up))*(l3*l3)/(sqrt72Up*u1)",
            bit_exact_against_l4_json=True),
        rederive_checks={k: (v if isinstance(v, (bool, list)) else bool(v))
                         for k, v in checks.items()},
        S_interval=dict(
            recorded="l4.json ttp_interval.S_interval（3×3 Fraction 闭区间）",
            S00=[fs(W["S_iv"][0][0][0]), fs(W["S_iv"][0][0][1])],
            S11=[fs(W["S_iv"][1][1][0]), fs(W["S_iv"][1][1][1])],
            S22=[fs(W["S_iv"][2][2][0]), fs(W["S_iv"][2][2][1])],
            diagonal_true_range_a=[fs(W["a_lo"]), fs(W["a_hi"])],
            diagonal_true_range_b=[fs(6 * W["z_lo"] ** 2), fs(6 * W["z_hi"] ** 2)],
            note="a(z)=3(1−z²)+3/2 递减于 z²；S00/S11 严格含 [a(z_hi),a(z_lo)]；S22 端点==6z_lo²/6z_hi² 逐位"),
        spot_checks=dict(
            scheme=("seed 20261016；k=0,1,2 依次 i=rng.randint(⌊z_lo·2⁴⁰⌋,⌈z_hi·2⁴⁰⌉)、"
                    "z=i/2⁴⁰（2⁻⁴⁰ 网格，盒宽≈838,863 格）、vⱼ=Fraction(randint(−64,64),64)；"
                    "期望值 diagQ（对角公式）与符号行展开（ℚ[ρ,√3] 引擎）双实现一致"),
            points=[dict(z=fs(z), v=[fs(c) for c in v],
                         q_diag=fs(diag_q(z, *v)),
                         q_symbolic=fs(symbolic_quad(z, v)),
                         sandwich_l3_le_q_le_u1=bool(
                             W["l3"] * sum(c * c for c in v)
                             <= symbolic_quad(z, v)
                             <= W["u1"] * sum(c * c for c in v)))
                    for (z, v) in spots]),
        lean=dict(
            data_file="formal/lean/ThomsonN9/TableB5Data.lean（本发射器确定性生成；仅 import Mathlib）",
            main_file="formal/lean/ThomsonN9/TableB5.lean（手写主件；仅 import Mathlib＋ThomsonN9.TableB5Data；"
                      "不含数值字面量——数值面全部锚定 Data 件）",
            theorem_counts=dict(
                data=len(_re.findall(r"^theorem ", DATA_LEAN.read_text(), _re.M)),
                main=len(_re.findall(r"^theorem ", main_src, _re.M)))),
        scope_note=("B5 常数认证层（表 B 首件）：二次型对角化+λ 夹逼+装配四件+有效性定理；"
                    "d_P(X,Y)≤C·δ 解析本体（l4_procrustes.py 步骤 1–6）不在件内；"
                    "区间 Sylvester soundness 为 stretch 非必需面（D56 裁决）"),
        wall_s=round(time.time() - t0, 1),
    )
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    log(f"[done ] {OUT_JSON}（{doc['wall_s']}s）；exit 0")


if __name__ == "__main__":
    main()
