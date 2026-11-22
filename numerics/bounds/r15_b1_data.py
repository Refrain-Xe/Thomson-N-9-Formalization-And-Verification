#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r15_b1_data.py — R15B 表 B 第三件 B1（l4_orbit (P5) 实现证书＋轨道配平）数据发射器
（D61 裁决 3；heavySolves=0，零求解零 SDP 零新数值证书）.

任务书口径（r15b-tableb-b1）：TTP 九行 Gram 节点恒等式的算术层 Lean 化——
(i) 36 条有序对内积 ⟪rᵢ,rⱼ⟫ == 六类节点曲线 ν₁..ν₆（模曲线 ρ²=1−z² ring
证书技术，证书乘子由本发射器精确生成，D61-3 v1/v2 教训：勿手写）＋九对角
归一 ==1；(ii) 六类边计数 6/6/3/3/6/12==36（Fin 9×Fin 9 显式分类函数
nodeOfN）＋逐顶点轨道轮廓（棱顶 (2,1,0,1,2,2)/帽顶 (0,2,2,0,0,4)）与
Σ_y==2·mult 配平；(iii) z∈z*盒 上 15 对节点两两分离的区间容器层
（z² 有理包＋ρ Newton 有理包）。

本发射器沿 r14_b5_data.py 家法（不 import 之——独立第二实现），stdlib
Fraction 只读消费：
  results/local_min.json —— z 盒唯一隔离源 zStarIntervalMpmath（严格区间
    精确有理端点；与 l4.json ttp_interval.z_box 逐位同源——B5 已锚）；
  results/l4_orbit.json —— 节点/计数记录面对账（inputs.zBox 严格外扩、
    nodes.curves_x2 曲线串、orbitBalance 六类计数/轮廓/Σ_y 配平）。

数学层（独立第二实现，与 l4_orbit.py / family.py 对账但不 import）：
  符号引擎在自由代数 ℚ[z,ρ,s]（dict {(zdeg,rdeg,sdeg): Fraction}）上算
  9×9 Gram；每对 (i,j) 的差 D = dot − ν_k 经确定性归约
    D == C1·(s²−3) + C2·(ρ²−(1−z²)) + D'，D' 中 ρ/s 次数 ≤ 1，
  D'==0 即曲线恒等式成立——C1/C2 即 Lean key 内 ring 证书乘子（以 √ 原子
  书写，Real.mul_self_sqrt 消零——B5 ttp_quadform 同式）。几何分类＝逐 ν
  试 D'==0；算术分类 nodeOfN（行块/三角残差规则，定向 cap−prism ≡1→ν₂
  ——设计探针⑤亲捕手写定向反转）与几何分类全 36 对对账；计数/轮廓/Σ_y
  配平 Fraction 重算与 l4_orbit.json orbitBalance 逐字段对账。
  容器：z 盒端点（local_min 精确有理）→ z² 有理包 → ν₁/ν₃/ν₄/ν₅ 端点
  精确有理；ρ Newton 200-bit 有理包（rhoDn ≤ ρ(z) ≤ rhoUp 于盒上）→
  ν₂/ν₆ 容器；五链两两不交 ⇒ 15 对分离。

发射（确定性，双件，r13_a1_data.py emit_main_lean 先例）：
  formal/lean/ThomsonN9/TableB1Data.lean —— 行原子 def（rhoR/s3R/dot3/
  9 行/6 ν 曲线）＋容器字面量（zLo/zHi/ρ 包/12 端点/抽查 ρ 包/抽查 z 点）
  ＋端点事实与不交链 norm_num 定理＋3 抽查点容器定理（仅 import Mathlib）；
  formal/lean/ThomsonN9/TableB1.lean —— 主件（import Mathlib＋
  ThomsonN9.TableB1Data）：45 逐对 Gram 定理（发射器生成 ring 证书）＋
  桥接定理 gram_nodeOfN（interval_cases 36 臂）＋对角归一＋计数配平
  （Finset.filter decide）＋轮廓＋Σ_y＋ν 容器定理＋节点链＋两两分离
  （零数值数据字面量——全部经 Data 件名字锚定）。
回读自检：Data ℚ def 重解析逐位对账＋Main 证书乘子串重对账＋确定性重跑
字节一致（两 Lean 件）。

抽查（seed 20261017，B5 家法）：z 盒内 3 个随机有理点（2⁻⁴⁰ 网格），
逐点 6 类 ν 容器包含性（ν₂/ν₆ 走逐点 Newton ρ 包）双实现（发射器
Fraction 重算 ↔ Lean norm_num/sqrt 定理字面量）对账。

诚实边界（docstring 双侧声明）：l4_orbit (P1)–(P4) 过滤枚举（K9 六色
染色 float scout＋区间复验＋iso 归类）＝数值层职责不在件；stageb-scope
§2 B1 原表述的『轨道维数/横截坐标』几何部分不在本件、后续件另议；本件
＝(P5) 实现证书＋配平＋分离的算术层。

用法（CWD 无关）：
  python3 numerics/bounds/r15_b1_data.py
产出：
  formal/lean/ThomsonN9/TableB1Data.lean
  formal/lean/ThomsonN9/TableB1.lean
  numerics/bounds/results/r15_b1_data.json
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

LM_JSON = RESULTS / "local_min.json"          # 只读：z 盒唯一隔离源
ORB_JSON = RESULTS / "l4_orbit.json"          # 只读：节点/计数记录面
OUT_JSON = RESULTS / "r15_b1_data.json"
DATA_LEAN = REPO / "formal" / "lean" / "ThomsonN9" / "TableB1Data.lean"
MAIN_LEAN = REPO / "formal" / "lean" / "ThomsonN9" / "TableB1.lean"

SEED = 20261017                              # R15B 统一 seed（任务书）
SQ_BITS = 200                                # ρ Newton 有理包精度（bit，B5 同族）
ZGRID = 1 << 40                              # 抽查 z 网格 2⁻⁴⁰（B5 同式）

F0, F1, FHALF = Fr(0), Fr(1), Fr(1, 2)
ROWS = ["T0", "T1", "T2", "B0", "B1", "B2", "C0", "C1", "C2"]
NU_NAMES = ["nu1", "nu2", "nu3", "nu4", "nu5", "nu6"]
NU_FORMULAS = ["-(1 + z^2)/2", "-(rhoR z)", "-1/2", "1 - 2*z^2",
               "(3*z^2 - 1)/2", "rhoR z / 2"]
NU_DOCS = [
    "ν₁ = −(1+z²)/2（上下错位 6 边）",
    "ν₂ = −ρ（帽棱≡1 6 边）",
    "ν₃ = −1/2（帽帽 3 边）",
    "ν₄ = 1−2z²（竖棱 3 边）",
    "ν₅ = (3z²−1)/2（上上/下下三角内部 6 边）",
    "ν₆ = ρ/2（帽棱≡0,2 12 边）",
]
MULTS = [6, 6, 3, 3, 6, 12]                  # l4_orbit.json tubeMults（0 基）


def log(msg: str) -> None:
    print(f"[r15b1] {msg}", flush=True)


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
    raise SystemExit(f"[r15b1][FAIL] {msg}")


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


# ---- 符号引擎：自由代数 ℚ[z,ρ,s]（dict {(zdeg, rdeg, sdeg): Fr}） --------
def fadd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F0) + v
    return {k: v for k, v in out.items() if v != 0}


def fmul(a, b):
    out = {}
    for (a1, b1, c1), v1 in a.items():
        for (a2, b2, c2), v2 in b.items():
            k = (a1 + a2, b1 + b2, c1 + c2)
            out[k] = out.get(k, F0) + v1 * v2
    return {k: v for k, v in out.items() if v != 0}


def fscale(a, c):
    return {k: v * c for k, v in a.items() if v * c != 0}


def fone(q):
    return {(0, 0, 0): q}


ZP = {(1, 0, 0): F1}
RHO = {(0, 1, 0): F1}
S3 = {(0, 0, 1): F1}


def reduce_cert(D):
    """确定性归约：D == C1·(s²−3) + C2·(ρ²−(1−z²)) + D'，D' 中 rdeg/sdeg ≤ 1。

    每步取 (sdeg, rdeg, zdeg) 字典序最大违规单项式；s 次数 ≥2 先消。
    返回 (C1, C2, D')；恒等式成立 ⇔ D' == {}。
    """
    C1, C2 = {}, {}
    D = dict(D)
    while True:
        offenders = [k for k in D if D[k] != 0 and (k[1] >= 2 or k[2] >= 2)]
        if not offenders:
            break
        k = max(offenders, key=lambda t: (t[2], t[1], t[0]))
        a, b, c = k
        v = D[k]
        if c >= 2:
            # t = v·z^a ρ^b s^c = step·(s²−3) + 3·step，step = v·z^a ρ^b s^(c−2)
            step = {(a, b, c - 2): v}
            C1 = fadd(C1, step)
            D = fadd(fadd(D, {k: -v}), fscale(step, 3))
        else:
            # t = v·z^a ρ^b s^c = step·(ρ²−(1−z²)) + step·(1−z²)，step = v·z^a ρ^(b−2) s^c
            step = {(a, b - 2, c): v}
            C2 = fadd(C2, step)
            one_m_z2 = {(0, 0, 0): F1, (2, 0, 0): -F1}
            D = fadd(fadd(D, {k: -v}), fmul(step, one_m_z2))
    return C1, C2, D


def build_rows():
    """9 行 TTP 构型（行序与 l4_orbit.family_points_s3 同构：上三角 0–2、
    下三角 3–5、帽 6–8），每行 3 个坐标各为自由代数元。"""
    rows = []
    for zsgn in (1, -1):
        zc = {(1, 0, 0): Fr(zsgn)}
        rows.append([RHO, {}, zc])                                    # (ρ,0,±z)
        rows.append([fscale(RHO, Fr(-1, 2)),
                     fscale(fmul(RHO, S3), FHALF), zc])               # (−ρ/2, √3ρ/2, ±z)
        rows.append([fscale(RHO, Fr(-1, 2)),
                     fscale(fmul(RHO, S3), Fr(-1, 2)), zc])           # (−ρ/2, −√3ρ/2, ±z)
    rows.append([fone(FHALF), fscale(S3, FHALF), {}])                 # (1/2, √3/2, 0)
    rows.append([fone(-F1), {}, {}])                                  # (−1, 0, 0)
    rows.append([fone(FHALF), fscale(S3, Fr(-1, 2)), {}])             # (1/2, −√3/2, 0)
    return rows


NU = [
    fscale(fadd(fmul(ZP, ZP), fone(F1)), Fr(-1, 2)),          # ν₁ = −(1+z²)/2
    fscale(RHO, -F1),                                          # ν₂ = −ρ
    fone(Fr(-1, 2)),                                           # ν₃ = −1/2
    fadd(fone(F1), fscale(fmul(ZP, ZP), -2)),                  # ν₄ = 1−2z²
    fscale(fadd(fscale(fmul(ZP, ZP), 3), fone(-F1)), FHALF),   # ν₅ = (3z²−1)/2
    fscale(RHO, FHALF),                                        # ν₆ = ρ/2
]


def dot_free(rows, i, j):
    acc = {}
    for a, b in zip(rows[i], rows[j]):
        acc = fadd(acc, fmul(a, b))
    return acc


def nodeOfN_rule(i: int, j: int) -> int:
    """算术分类规则（与 Lean nodeOfN 同构；定向亲验：cap−prism ≡1 → ν₂）。"""
    if i // 3 == j // 3:
        return 2 if i // 3 == 2 else 4
    if i // 3 == 2:            # i 帽，j 棱
        return 1 if (i % 3 + 3 - j % 3) % 3 == 1 else 5
    if j // 3 == 2:            # j 帽，i 棱
        return 1 if (j % 3 + 3 - i % 3) % 3 == 1 else 5
    return 3 if i % 3 == j % 3 else 0


# ---- ℤ[z,r] 渲染（l4_orbit.poly_str 同式，跨件曲线串对账用） --------------
def _merge(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}


def _sc(p, c):
    return {k: v * c for k, v in p.items() if v * c != 0}


def nu2_zr(k):
    """2ν_k ∈ ℤ[z,r]（l4_orbit.build_node_polys 同式独立重导，rdeg ≤ 1）。"""
    z2, one, r = {(2, 0): 1}, {(0, 0): 1}, {(0, 1): 1}
    return [_merge({(0, 0): -1}, _sc(z2, -1)), _sc(r, -2), {(0, 0): -1},
            _merge({(0, 0): 2}, _sc(z2, -4)), _merge(_sc(z2, 3), {(0, 0): -1}),
            dict(r)][k]


def poly_str_zr(p) -> str:
    """ℤ[z,r] 元按 l4_orbit.poly_str 排序渲染（键 (zdeg, rdeg) 降序）。"""
    if not p:
        return "0"
    parts = []
    for (a, b) in sorted(p.keys(), reverse=True):
        c = p[(a, b)]
        body = ("z" if a == 1 else f"z^{a}" if a > 1 else "") + ("r" if b else "")
        parts.append(f"{c}" if not body else (f"{c}" if c != 1 else "") + (body or "1"))
    return " + ".join(parts)


# ============================================================ Lean 渲染
def lean_rat(c: Fr) -> str:
    """ℚ 字面量 → Lean ℝ 原子式（证书乘子系数用）。"""
    if c.denominator == 1:
        return f"({c.numerator}:ℝ)"
    if c < 0:
        return f"(-({abs(c.numerator)}/{c.denominator}:ℝ))"
    return f"({c.numerator}/{c.denominator}:ℝ)"


def render_mult(P) -> str:
    """自由代数元 → Lean 乘子表达式（z^a · (rhoR z)^b · s3R^c，规范序）。"""
    if not P:
        return "(0:ℝ)"
    terms = []
    for (a, b, c) in sorted(P.keys()):
        v = P[(a, b, c)]
        facs = []
        if a == 1:
            facs.append("z")
        elif a >= 2:
            facs.append(f"z^{a}")
        facs += ["rhoR z"] * b
        facs += ["s3R"] * c
        if facs:
            terms.append(lean_rat(v) + " * " + " * ".join(facs))
        else:
            terms.append(lean_rat(v))
    return " + ".join(terms)


def row_lean(k: int) -> str:
    """第 k 行的 Lean 坐标三元组文本（ρ/√3 原子式）。"""
    if k < 6 and k % 3 == 0:
        return "(rhoR z, 0, " + ("z" if k < 3 else "-z") + ")"
    if k < 6:
        y = "s3R * rhoR z / 2" if k % 3 == 1 else "-(s3R * rhoR z / 2)"
        zs = "z" if k < 3 else "-z"
        return f"(-(rhoR z)/2, {y}, {zs})"
    return ["(1/2, s3R/2, 0)", "(-1, 0, 0)", "(1/2, -s3R/2, 0)"][k - 6]


def row_arg(i: int) -> str:
    """第 i 行在 dot3 里的实参文本（棱行带 z，帽行为常量）。"""
    return f"(row{ROWS[i]} z)" if i < 6 else f"row{ROWS[i]}"


# ============================================================ 重导层
def rederive():
    lm = json.loads(LM_JSON.read_text())
    orb = json.loads(ORB_JSON.read_text())

    # ---- z 盒：local_min zStarIntervalMpmath 精确有理端点（任务书唯一隔离源）
    zl_s, zh_s = lm["zStarIntervalMpmath"].strip("[]").split(", ")
    z_lo, z_hi = Fr(zl_s.strip()), Fr(zh_s.strip())
    if not (0 < z_lo < z_hi < 1):
        fail(f"z 盒非法：{z_lo}, {z_hi}")
    # l4_orbit.json zBox 是严格外扩 dyadic 盒：orb_lo < zLo < zHi < orb_hi
    orb_lo, orb_hi = (Fr(s) for s in orb["inputs"]["zBox"])
    if not (orb_lo < z_lo < z_hi < orb_hi):
        fail("z 盒包含性失守：l4_orbit zBox 应严格包含 local_min 隔离区间")

    # ---- 曲线面对账：2ν_k 整系数串 == l4_orbit.json nodes.curves_x2
    curves_mine = [poly_str_zr(nu2_zr(k)) for k in range(6)]
    if curves_mine != orb["nodes"]["curves_x2"]:
        fail(f"2ν 曲线串失配：{curves_mine} ≠ {orb['nodes']['curves_x2']}")

    # ---- 几何分类＋证书（36 对＋9 对角）
    rows = build_rows()
    cls = {}
    certs = {}
    for i in range(9):
        for j in range(i + 1, 9):
            D = dot_free(rows, i, j)
            found = None
            for k in range(6):
                C1, C2, Dp = reduce_cert(fadd(D, fscale(NU[k], -1)))
                if not Dp:
                    found = k
                    certs[(i, j)] = (C1, C2)
                    break
            if found is None:
                C1, C2, Dp = reduce_cert(D)
                fail(f"{ROWS[i]},{ROWS[j]} 无节点曲线匹配（Dp={Dp}）")
            cls[(i, j)] = found
    for i in range(9):                                   # 对角归一
        C1, C2, Dp = reduce_cert(fadd(dot_free(rows, i, i), fone(-F1)))
        if Dp:
            fail(f"对角 {ROWS[i]} 归一失守（Dp={Dp}）")
        certs[(i, i)] = (C1, C2)

    # ---- 算术规则对账
    mism = [(i, j) for (i, j), k in cls.items() if nodeOfN_rule(i, j) != k]
    if mism:
        fail(f"算术分类规则与几何分类失配：{mism}")

    # ---- 计数/轮廓/配平（Fraction 重算）
    counts = [sum(1 for k in cls.values() if k == c) for c in range(6)]
    prof = {v: [0] * 6 for v in range(9)}
    for (i, j), c in cls.items():
        prof[i][c] += 1
        prof[j][c] += 1
    prism_prof, cap_prof = prof[0], prof[6]
    for v in range(1, 6):
        if prof[v] != prism_prof:
            fail(f"棱顶轮廓不齐：v={v} {prof[v]}")
    for v in range(7, 9):
        if prof[v] != cap_prof:
            fail(f"帽顶轮廓不齐：v={v} {prof[v]}")
    sigma_y = [sum(prof[v][c] for v in range(9)) for c in range(6)]
    two_mult = [2 * m for m in MULTS]
    if sigma_y != two_mult or sum(counts) != 36:
        fail(f"配平失守：Σ_y={sigma_y} ≠ 2·mult={two_mult} 或 Σ计数≠36")

    # ---- l4_orbit.json orbitBalance 逐字段对账
    ob = orb["orbitBalance"]
    if ob["prismVertexProfile"] != prism_prof or ob["capVertexProfile"] != cap_prof:
        fail("逐顶点轮廓与 l4_orbit.json orbitBalance 失配")
    if ob["perNodeSums_Sigma_y"] != sigma_y or ob["twoTimesMult"] != two_mult:
        fail("Σ_y 配平与 l4_orbit.json orbitBalance 失配")
    if list(ob["tubeMults"]) != MULTS or counts != list(ob["tubeMults"]):
        fail("六类计数与 l4_orbit.json orbitBalance/tubeMults 失配")

    # ---- 容器（z² 有理包＋ρ Newton 有理包）
    z2_lo, z2_hi = z_lo * z_lo, z_hi * z_hi
    rhoDn = sqrt_rat(F1 - z2_hi, "lo")               # ≤ √(1−z_hi²) ≤ ρ(z)
    rhoUp = sqrt_rat(F1 - z2_lo, "hi")               # ≥ √(1−z_lo²) ≥ ρ(z)
    if not (rhoDn * rhoDn <= 1 - z2_hi and 1 - z2_lo <= rhoUp * rhoUp
            and 0 < rhoDn < rhoUp):
        fail("ρ Newton 包失守")
    cont = [
        (-(1 + z2_hi) / 2, -(1 + z2_lo) / 2),        # ν₁ 端点精确
        (-rhoUp, -rhoDn),                            # ν₂
        (Fr(-1, 2), Fr(-1, 2)),                      # ν₃
        (1 - 2 * z2_hi, 1 - 2 * z2_lo),              # ν₄ 端点精确
        ((3 * z2_lo - 1) / 2, (3 * z2_hi - 1) / 2),  # ν₅ 端点精确
        (rhoDn / 2, rhoUp / 2),                      # ν₆
    ]
    for k, (lo, hi) in enumerate(cont):
        if not (lo < hi) and k != 2:              # ν₃ 为点容器（常曲线）
            fail(f"ν{k+1} 容器退化为点或反向")
        if not (lo <= hi):
            fail(f"ν{k+1} 容器反向")
    chain_gaps = [cont[k][1] < cont[k + 1][0] for k in range(5)]
    if not all(chain_gaps):
        fail(f"容器链不交失守：{chain_gaps}")
    json_iv = [[Fr(s) for s in pair] for pair in orb["nodes"]["intervals"]]
    # json 区间为 20 位有效数字显示舍入（非精确端点）——精确对账以 1e-15 外扩
    # 容差进行：本项目**真值范围**（非有理容器）⊆ 外扩 json 区间（Fraction 精确）。
    TOL = Fr(1, 10 ** 15)
    widened = [(json_iv[k][0] - TOL, json_iv[k][1] + TOL) for k in range(6)]
    # 真值范围（有理曲线精确端点；ρ 曲线以平方比较，两侧均为正）
    # ν₁/ν₃/ν₄/ν₅：真值范围端点精确有理
    exact_rng = {0: (-(1 + z2_hi) / 2, -(1 + z2_lo) / 2), 2: (Fr(-1, 2), Fr(-1, 2)),
                 3: (1 - 2 * z2_hi, 1 - 2 * z2_lo),
                 4: ((3 * z2_lo - 1) / 2, (3 * z2_hi - 1) / 2)}
    for k, (tlo, thi) in exact_rng.items():
        if not (widened[k][0] <= tlo and thi <= widened[k][1]):
            fail(f"ν{k+1} 真值范围 ⊄ 外扩 json 区间（1e-15 容差内失配）")
    # ν₂ = −ρ ∈ [−√(1−z_lo²), −√(1−z_hi²)]：json 端点同向平方比较
    if not ((1 - z2_lo) <= (-widened[1][0]) ** 2
            and (1 - z2_hi) >= (-widened[1][1]) ** 2):
        fail("ν₂ 真值范围 ⊄ 外扩 json 区间")
    # ν₆ = ρ/2 ∈ [√(1−z_hi²)/2, √(1−z_lo²)/2]
    if not ((1 - z2_hi) >= (2 * widened[5][0]) ** 2
            and (1 - z2_lo) <= (2 * widened[5][1]) ** 2):
        fail("ν₆ 真值范围 ⊄ 外扩 json 区间")
    json_adv = [float(cont[k][0] - json_iv[k][0]) + float(json_iv[k][1] - cont[k][1])
                for k in range(6)]        # 原始容器-显示端点差（舍入尘量级，advisory）
    return dict(lm=lm, orb=orb, z_lo=z_lo, z_hi=z_hi, rows=rows, cls=cls,
                certs=certs, counts=counts, prism_prof=prism_prof,
                cap_prof=cap_prof, sigma_y=sigma_y, two_mult=two_mult,
                z2_lo=z2_lo, z2_hi=z2_hi, rhoDn=rhoDn, rhoUp=rhoUp,
                cont=cont, chain_gaps=chain_gaps, json_iv=json_iv,
                json_widened_ok=True, json_adv=json_adv)


# ============================================================ 抽查点
def spot_points(z_lo: Fr, z_hi: Fr):
    """seed 20261017 固定抽样：3 个 z∈盒（2⁻⁴⁰ 网格，B5 spot_points 同式）。"""
    rng = random.Random(SEED)
    lo_i = math.floor(z_lo * ZGRID)
    hi_i = math.ceil(z_hi * ZGRID)
    pts = []
    for _ in range(3):
        i = rng.randint(lo_i, hi_i)
        z = Fr(i, ZGRID)
        if not (z_lo <= z <= z_hi):
            fail(f"抽查 z 越盒：{z}")
        pts.append(z)
    return pts


# ============================================================ Data 件发射
def emit_data_lean(W, spots, spot_rho):
    z_lo, z_hi = W["z_lo"], W["z_hi"]
    cont = W["cont"]
    L = []
    L.append("import Mathlib")
    L.append("/-!")
    L.append("# Table B1 data (R15 / r15b): the TTP nine-row Gram-node arithmetic layer")
    L.append("")
    L.append("This module is deliberately self-contained: it imports only `Mathlib`,")
    L.append("imports no in-repo solution module, and is imported only by")
    L.append("`ThomsonN9/TableB1.lean`.  It materialises the atom/row layer of the")
    L.append("B1 package — the l4_orbit (P5) realisation certificate plus the orbit")
    L.append("balancing arithmetic — re-derived here through the independent second")
    L.append("implementation of `numerics/bounds/r15_b1_data.py` (stdlib-Fraction")
    L.append("symbolic engine over ℚ[z,ρ,√3]; provenance = sha256 of local_min.json")
    L.append("and l4_orbit.json, recorded in `results/r15_b1_data.json`):")
    L.append("")
    L.append("* `rhoR`/`s3R`/`dot3` — the ρ = √(1−z²), √3 atoms and the row dot")
    L.append("  product (rows written in ρ/√3 atom style, same source as")
    L.append("  `TableB5.ttpQ` / `numerics/family.py tri_cap_prism`);")
    L.append("* the nine rows `rowT0..rowC2` — upper triangle (ρ,0,z),")
    L.append("  (−ρ/2,±√3ρ/2,z), lower triangle with z → −z, caps")
    L.append("  (1/2,±√3/2,0), (−1,0,0) (row order of `l4_orbit.family_points_s3`);")
    L.append("* the six node curves `nu1..nu6` — ν₁=−(1+z²)/2, ν₂=−ρ, ν₃=−1/2,")
    L.append("  ν₄=1−2z², ν₅=(3z²−1)/2, ν₆=ρ/2 (`l4_orbit.json nodes.curves_x2`)")
    L.append("  re-derived bit for bit;")
    L.append("* the container literals — `zLo`/`zHi` (the strict isolation interval")
    L.append("  `zStarIntervalMpmath` of `results/local_min.json`, exact rational")
    L.append("  endpoints), the 200-bit Newton ρ-envelope `rhoDn`/`rhoUp`, and the")
    L.append("  twelve ν-container endpoints (ν₁/ν₄/ν₅ exact rational endpoints from")
    L.append("  the z²-envelope, ν₂/ν₆ from the ρ-envelope, ν₃ the point −1/2), with")
    L.append("  the five-link disjointness chain as a `norm_num` theorem (⇒ the 15")
    L.append("  pairwise separations);")
    L.append("* three fixed random rational spot checks (seed 20261017, z on the")
    L.append("  2⁻⁴⁰ grid inside the z-box) of the six ν-containers, each proved in")
    L.append("  Lean through per-point Newton ρ-envelopes and cross-checked against")
    L.append("  the emitter's independent Fraction computation.")
    L.append("")
    L.append("Honest scope note (B1 boundary, D61-3): the l4_orbit (P1)–(P4) filter")
    L.append("enumeration (K9 six-colour scout + interval re-verification + iso")
    L.append("classification) is a numerics-layer duty and is NOT part of this file;")
    L.append("the orbit-dimension / transverse-coordinate geometry of the original")
    L.append("stageb-scope §2 B1 wording is deferred to a later piece.  This piece is")
    L.append("the arithmetic layer: the (P5) realisation certificate, the balancing")
    L.append("counts, and the node separation containers.")
    L.append("-/")
    L.append("")
    L.append("set_option maxHeartbeats 1000000")
    L.append("set_option linter.unusedVariables false")
    L.append("")
    L.append("namespace ThomsonN9.TableB1Data")
    L.append("")
    L.append("/-- ρ 原子：ρ = √(1−z²)（模曲线 ρ² = 1−z²）。 -/")
    L.append("noncomputable def rhoR (z : ℝ) : ℝ := Real.sqrt (1 - z^2)")
    L.append("/-- √3 原子（(√3)² = 3 消零用）。 -/")
    L.append("noncomputable def s3R : ℝ := Real.sqrt 3")
    L.append("/-- 行内积（ℝ×ℝ×ℝ 三分量）。 -/")
    L.append("noncomputable def dot3 (a b : ℝ × ℝ × ℝ) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2")
    L.append("")
    rowdocs = [
        "上三角行 k=0：(ρ, 0, z)。",
        "上三角行 k=1：(−ρ/2, √3ρ/2, z)。",
        "上三角行 k=2：(−ρ/2, −√3ρ/2, z)。",
        "下三角行 k=0：(ρ, 0, −z)。",
        "下三角行 k=1：(−ρ/2, √3ρ/2, −z)。",
        "下三角行 k=2：(−ρ/2, −√3ρ/2, −z)。",
        "帽行 j=0：(1/2, √3/2, 0)。",
        "帽行 j=1：(−1, 0, 0)。",
        "帽行 j=2：(1/2, −√3/2, 0)。",
    ]
    for k in range(6):
        L.append(f"/-- {rowdocs[k]} -/")
        L.append(f"noncomputable def row{ROWS[k]} (z : ℝ) : ℝ × ℝ × ℝ := "
                 f"{row_lean(k)}")
    for k in range(6, 9):
        L.append(f"/-- {rowdocs[k]} -/")
        L.append(f"noncomputable def row{ROWS[k]} : ℝ × ℝ × ℝ := {row_lean(k)}")
    L.append("")
    for k in range(6):
        L.append(f"/-- 节点曲线 {NU_DOCS[k]}。 -/")
        L.append(f"noncomputable def {NU_NAMES[k]} (z : ℝ) : ℝ := {NU_FORMULAS[k]}")
    L.append("")
    L.append("/-! ### 容器字面量（z 盒、ρ 包、六 ν 容器、抽查点） -/")
    L.append("/- z 盒下端（local_min.json zStarIntervalMpmath 严格隔离区间精确有理端点）。 -/")
    L.append(f"def zLo : ℚ := {fs(z_lo)}")
    L.append("/- z 盒上端（同上）。 -/")
    L.append(f"def zHi : ℚ := {fs(z_hi)}")
    L.append("/- ρ 的 200-bit Newton 有理下界包（rhoDn² ≤ 1 − zHi² ≤ ρ(z)² 于盒上）。 -/")
    L.append(f"def rhoDn : ℚ := {fs(W['rhoDn'])}")
    L.append("/- ρ 的 200-bit Newton 有理上界包（ρ(z)² ≤ 1 − zLo² ≤ rhoUp² 于盒上）。 -/")
    L.append(f"def rhoUp : ℚ := {fs(W['rhoUp'])}")
    for k in range(6):
        L.append(f"/- ν{k+1} 容器下端。{NU_DOCS[k]} -/")
        L.append(f"def nu{k+1}Lo : ℚ := {fs(cont[k][0])}")
        L.append(f"/- ν{k+1} 容器上端。 -/")
        L.append(f"def nu{k+1}Hi : ℚ := {fs(cont[k][1])}")
    for k, z in enumerate(spots):
        L.append(f"/- 抽查点 {k}（z = {fs(z)}，seed 20261017）。 -/")
        L.append(f"def spotZ{k} : ℚ := {fs(z)}")
        L.append(f"/- 抽查点 {k} 的 ρ Newton 下界包。 -/")
        L.append(f"def spotRhoDn{k} : ℚ := {fs(spot_rho[k][0])}")
        L.append(f"/- 抽查点 {k} 的 ρ Newton 上界包。 -/")
        L.append(f"def spotRhoUp{k} : ℚ := {fs(spot_rho[k][1])}")
    L.append("")
    L.append("/-! ### 端点事实（ℚ norm_num） -/")
    L.append("/- z 盒为正区间：0 < zLo ≤ zHi < 1。 -/")
    L.append("theorem zLo_pos : (0:ℚ) < zLo := by norm_num [zLo]")
    L.append("theorem zHi_pos : (0:ℚ) < zHi := by norm_num [zHi]")
    L.append("theorem zHi_lt_one : (zHi:ℚ) < 1 := by norm_num [zHi]")
    L.append("theorem zLo_le_zHi : zLo ≤ zHi := by norm_num [zLo, zHi]")
    L.append("/- ν₁ 容器端点 == −(1+z²)/2 在 z 盒端点的精确值（逐位）。 -/")
    L.append("theorem nu1Lo_eq : nu1Lo = -(1 + zHi^2)/2 := by norm_num [nu1Lo, zHi]")
    L.append("theorem nu1Hi_eq : nu1Hi = -(1 + zLo^2)/2 := by norm_num [nu1Hi, zLo]")
    L.append("/- ν₄ 容器端点 == 1−2z² 端点精确值。 -/")
    L.append("theorem nu4Lo_eq : nu4Lo = 1 - 2*zHi^2 := by norm_num [nu4Lo, zHi]")
    L.append("theorem nu4Hi_eq : nu4Hi = 1 - 2*zLo^2 := by norm_num [nu4Hi, zLo]")
    L.append("/- ν₅ 容器端点 == (3z²−1)/2 端点精确值。 -/")
    L.append("theorem nu5Lo_eq : nu5Lo = (3*zLo^2 - 1)/2 := by norm_num [nu5Lo, zLo]")
    L.append("theorem nu5Hi_eq : nu5Hi = (3*zHi^2 - 1)/2 := by norm_num [nu5Hi, zHi]")
    L.append("/- ν₂ 容器端点 == −ρ 包端点（−rhoUp/−rhoDn）。 -/")
    L.append("theorem nu2Lo_eq : nu2Lo = -rhoUp := by norm_num [nu2Lo, rhoUp]")
    L.append("theorem nu2Hi_eq : nu2Hi = -rhoDn := by norm_num [nu2Hi, rhoDn]")
    L.append("/- ν₃ 容器为点 −1/2。 -/")
    L.append("theorem nu3_pt : nu3Lo = -1/2 ∧ nu3Hi = -1/2 := by")
    L.append("  constructor <;> norm_num [nu3Lo, nu3Hi]")
    L.append("/- ν₆ 容器端点 == ρ 包端点之半。 -/")
    L.append("theorem nu6Lo_eq : nu6Lo = rhoDn/2 := by norm_num [nu6Lo, rhoDn]")
    L.append("theorem nu6Hi_eq : nu6Hi = rhoUp/2 := by norm_num [nu6Hi, rhoUp]")
    L.append("/- ρ Newton 包前提两件＋正性。 -/")
    L.append("theorem rhoDn_sq_le : rhoDn^2 ≤ 1 - zHi^2 := by norm_num [rhoDn, zHi]")
    L.append("theorem rhoUp_sq_ge : 1 - zLo^2 ≤ rhoUp^2 := by norm_num [rhoUp, zLo]")
    L.append("theorem rhoDn_pos : (0:ℚ) < rhoDn := by norm_num [rhoDn]")
    L.append("theorem rhoUp_pos : (0:ℚ) < rhoUp := by norm_num [rhoUp]")
    L.append("/- 抽查点 ρ 包前提（3×2＋正性）。 -/")
    for k in range(3):
        L.append(f"theorem spotRhoDn{k}_sq_le : spotRhoDn{k}^2 ≤ 1 - spotZ{k}^2 := by"
                 f"\n  norm_num [spotRhoDn{k}, spotZ{k}]")
        L.append(f"theorem spotRhoUp{k}_sq_ge : 1 - spotZ{k}^2 ≤ spotRhoUp{k}^2 := by"
                 f"\n  norm_num [spotRhoUp{k}, spotZ{k}]")
        L.append(f"theorem spotRhoDn{k}_pos : (0:ℚ) < spotRhoDn{k} := by norm_num [spotRhoDn{k}]")
    L.append("/- **容器五链两两不交**（⇒ 15 对节点曲线在 z 盒上两两分离）。 -/")
    L.append("theorem nu_chain_disjoint :")
    L.append("    nu1Hi < nu2Lo ∧ nu2Hi < nu3Lo ∧ nu3Hi < nu4Lo ∧ nu4Hi < nu5Lo ∧")
    L.append("    nu5Hi < nu6Lo := by")
    L.append("  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>")
    L.append("    norm_num [nu1Hi, nu2Lo, nu2Hi, nu3Lo, nu3Hi, nu4Lo, nu4Hi, nu5Lo, nu5Hi, nu6Lo]")
    L.append("")
    L.append("/-! ### 抽查定理（3 点 × 六 ν 容器包含性） -/")
    for k in range(3):
        zr = f"(spotZ{k}:ℝ)"
        L.append(f"/-- 抽查 {k}（seed 20261017，z = {fs(spots[k])} ∈ 盒）：六 ν 容器")
        L.append("    包含性（ν₂/ν₆ 经逐点 Newton ρ 包＋sqrt 单调；期望值＝发射器")
        L.append("    独立 Fraction 重算，门 G5 复放对账）。 -/")
        L.append(f"theorem spot{k}_containers :")
        conj = []
        for c in range(6):
            conj += [f"(nu{c+1}Lo:ℝ) ≤ {NU_NAMES[c]} {zr}",
                     f"{NU_NAMES[c]} {zr} ≤ (nu{c+1}Hi:ℝ)"]
        L.append("    " + " ∧ ".join(conj[0:2]))
        for s in range(2, 12, 2):
            L.append("    ∧ " + " ∧ ".join(conj[s:s + 2]))
        L.append(" := by")
        L.append(f"  have hnn : (0:ℝ) ≤ 1 - {zr}^2 := by norm_num [spotZ{k}]")
        L.append(f"  have hr : (spotRhoDn{k}:ℝ) ≤ rhoR {zr} ∧ rhoR {zr} ≤ (spotRhoUp{k}:ℝ) := by")
        L.append("    constructor")
        L.append(f"    · have e : ((spotRhoDn{k}:ℝ))^2 ≤ 1 - {zr}^2 := by"
                 f"\n        norm_num [spotRhoDn{k}, spotZ{k}]")
        L.append(f"      have hp : (0:ℝ) < (spotRhoDn{k}:ℝ) := by norm_num [spotRhoDn{k}]")
        L.append(f"      rw [show rhoR {zr} = Real.sqrt (1 - {zr}^2) from rfl]")
        L.append(f"      nlinarith [e, hp, Real.sqrt_nonneg (1 - {zr}^2),")
        L.append(f"        Real.sq_sqrt hnn]")
        L.append(f"    · rw [show rhoR {zr} = Real.sqrt (1 - {zr}^2) from rfl]")
        L.append("      rw [Real.sqrt_le_iff]")
        L.append(f"      constructor <;> norm_num [spotRhoUp{k}, spotZ{k}]")
        L.append(f"  have e1 : nu1 {zr} = -(1 + {zr}^2)/2 := by unfold nu1; ring")
        L.append(f"  have e2 : nu2 {zr} = -(rhoR {zr}) := by unfold nu2; ring")
        L.append(f"  have e3 : nu3 {zr} = -1/2 := by unfold nu3; ring")
        L.append(f"  have e4 : nu4 {zr} = 1 - 2*{zr}^2 := by unfold nu4; ring")
        L.append(f"  have e5 : nu5 {zr} = (3*{zr}^2 - 1)/2 := by unfold nu5; ring")
        L.append(f"  have e6 : nu6 {zr} = rhoR {zr}/2 := by unfold nu6; ring")
        L.append(f"  have p1lo : (nu1Lo:ℝ) ≤ -(1 + {zr}^2)/2 := by norm_num [nu1Lo, spotZ{k}]")
        L.append(f"  have p1hi : -(1 + {zr}^2)/2 ≤ (nu1Hi:ℝ) := by norm_num [nu1Hi, spotZ{k}]")
        L.append(f"  have p4lo : (nu4Lo:ℝ) ≤ 1 - 2*{zr}^2 := by norm_num [nu4Lo, spotZ{k}]")
        L.append(f"  have p4hi : 1 - 2*{zr}^2 ≤ (nu4Hi:ℝ) := by norm_num [nu4Hi, spotZ{k}]")
        L.append(f"  have p5lo : (nu5Lo:ℝ) ≤ (3*{zr}^2 - 1)/2 := by norm_num [nu5Lo, spotZ{k}]")
        L.append(f"  have p5hi : (3*{zr}^2 - 1)/2 ≤ (nu5Hi:ℝ) := by norm_num [nu5Hi, spotZ{k}]")
        L.append("  have p3lo : (nu3Lo:ℝ) = -1/2 := by norm_num [nu3Lo]")
        L.append("  have p3hi : (nu3Hi:ℝ) = -1/2 := by norm_num [nu3Hi]")
        L.append(f"  have u1 : (spotRhoUp{k}:ℝ) ≤ (rhoUp:ℝ) := by norm_num [spotRhoUp{k}, rhoUp]")
        L.append(f"  have u2 : (rhoDn:ℝ) ≤ (spotRhoDn{k}:ℝ) := by norm_num [rhoDn, spotRhoDn{k}]")
        L.append("  have c2lo : (nu2Lo:ℝ) = -(rhoUp:ℝ) := by norm_num [nu2Lo, rhoUp]")
        L.append("  have c2hi : (nu2Hi:ℝ) = -(rhoDn:ℝ) := by norm_num [nu2Hi, rhoDn]")
        L.append("  have c6lo : (nu6Lo:ℝ) = (rhoDn:ℝ)/2 := by norm_num [nu6Lo, rhoDn]")
        L.append("  have c6hi : (nu6Hi:ℝ) = (rhoUp:ℝ)/2 := by norm_num [nu6Hi, rhoUp]")
        L.append("  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith")
        L.append("")
    L.append("end ThomsonN9.TableB1Data")
    DATA_LEAN.parent.mkdir(parents=True, exist_ok=True)
    DATA_LEAN.write_text("\n".join(L) + "\n")


# ============================================================ Main 件发射
def gram_theorem_text(i, j, cert, clsk):
    """逐对 Gram 定理文本（证书乘子由引擎精确生成）。"""
    ri, rj = ROWS[i], ROWS[j]
    argi, argj = row_arg(i), row_arg(j)
    if i == j:
        name, rhs, nu_unfold = f"gram_diag_{ri}", "1", ""
    else:
        name = f"gram_{ri}_{rj}"
        rhs = f"{NU_NAMES[clsk]} z"
        nu_unfold = f" {NU_NAMES[clsk]}"
    C1, C2 = cert
    L = []
    L.append(f"theorem {name} (z : ℝ) (hz : z^2 ≤ 1) :")
    L.append(f"    dot3 {argi} {argj} = {rhs} := by")
    L.append("  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith")
    L.append("  have hs3 : s3R * s3R = 3 := by")
    L.append("    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]")
    L.append("  have hr2 : rhoR z * rhoR z = 1 - z^2 := by")
    L.append("    unfold rhoR; rw [Real.mul_self_sqrt hnn]")
    L.append(f"  have key : dot3 {argi} {argj} - {rhs}")
    L.append(f"      = {render_mult(C1)} * (s3R * s3R - 3)")
    L.append(f"        + {render_mult(C2)} * (rhoR z * rhoR z + z^2 - 1) := by")
    row_unf = f"row{ri} row{rj}" if ri != rj else f"row{ri}"
    L.append(f"    unfold dot3 {row_unf}{nu_unfold} rhoR s3R; ring")
    L.append("  rw [hs3, hr2] at key")
    L.append("  ring_nf at key")
    L.append("  linarith")
    return "\n".join(L), name


def emit_main_lean(W):
    cls = W["cls"]
    certs = W["certs"]
    L = []
    L.append("import Mathlib")
    L.append("import ThomsonN9.TableB1Data")
    L.append("")
    L.append("/-!")
    L.append("# Table B1 (R15 / r15b): the TTP nine-row Gram-node arithmetic layer")
    L.append("")
    L.append("**B1.** For the 9-point TTP (tri-cap-prism) family `X(z)` — upper")
    L.append("triangle rows `(ρ,0,z)`, `(−ρ/2,±√3ρ/2,z)`, lower triangle with")
    L.append("`z → −z`, cap rows `(1/2,±√3/2,0)`, `(−1,0,0)`, `ρ = √(1−z²)` — this")
    L.append("file proves the arithmetic layer of the L4 orbit lemma exactly, with")
    L.append("all numeric data anchored in `ThomsonN9.TableB1Data` (the read-only")
    L.append("re-derivation of `results/local_min.json` + `results/l4_orbit.json`):")
    L.append("")
    L.append("* **The 45 pairwise Gram identities.** For every ordered pair `i ≠ j`")
    L.append("  the inner product `⟪rᵢ,rⱼ⟫` equals one of the six node curves")
    L.append("  `ν₁..ν₆` (`gram_T0_T1` …, 36 off-diagonal theorems), and every row")
    L.append("  has unit norm (`gram_diag_*`, 9 theorems; `diag_norm_all` bundles")
    L.append("  them).  Each proof is the `TableB5.ttp_quadform` modulo-curve")
    L.append("  ring-certificate technique: the key identity")
    L.append("  `dot − ν = C₁·(√3·√3−3) + C₂·(ρ·ρ+z²−1)` with the two multipliers")
    L.append("  C₁, C₂ **generated exactly by the emitter's symbolic engine**")
    L.append("  (D61-3 v1/v2 lesson: never hand-write them — the design probe's")
    L.append("  hand-written ν₆ multiplier was correctly rejected by `ring`),")
    L.append("  discharged by `ring`, then killed by `Real.mul_self_sqrt` + `ring_nf`")
    L.append("  + `linarith`.")
    L.append("")
    L.append("* **Classification bridge.** `nodeOfN` is the explicit arithmetic")
    L.append("  classification function (same-block triangle-internal / cap-cap /")
    L.append("  vertical / cross-misaligned / cap-prism residue classes), and")
    L.append("  `gram_nodeOfN` is the bridge: for every `k < l < 9` the geometric")
    L.append("  node of the pair `(k,l)` — the value `nuOfN (nodeOfN k l) z` —")
    L.append("  equals the pairwise theorem (`interval_cases` over the 36 arms,")
    L.append("  each arm calling that pair's own Gram theorem).  This is the formal")
    L.append("  link between the certificate layer and the counting layer.")
    L.append("")
    L.append("* **Orbit balancing.** The six class counts over the 36 unordered")
    L.append("  pairs are `6/6/3/3/6/12` (`edge_counts`, `Finset.filter` + `decide`")
    L.append("  over `Fin 9 × Fin 9`; `edge_total` = 36), the per-vertex orbit")
    L.append("  profiles are `(2,1,0,1,2,2)` at each prism vertex and")
    L.append("  `(0,2,2,0,0,4)` at each cap vertex (`prism_profile`, `cap_profile`),")
    L.append("  and the Σ_y balance `Σ_v profile_v(c) = 2·mult(c)` holds for every")
    L.append("  class (`sigma_y_balance`) — reconciled field by field with")
    L.append("  `l4_orbit.json orbitBalance` (including its erratum: the six ν₂")
    L.append("  cap-prism edges vs the six ν₅ triangle-internal edges).")
    L.append("")
    L.append("* **Node separation containers.** For every `z` in the recorded z-box")
    L.append("  (`zLo ≤ z ≤ zHi`, the strict isolation interval of `local_min.json`):")
    L.append("  each node curve lies in its rational container (`nu_containers`, 12")
    L.append("  conjuncts; ν₁/ν₄/ν₅ through the exact z²-envelope, ν₂/ν₆ through the")
    L.append("  200-bit Newton ρ-envelope via `Real.sqrt_le_sqrt` + the literal")
    L.append("  `Real.sqrt_le_iff` envelope), the six values are strictly ordered")
    L.append("  `ν₁ < ν₂ < ν₃ < ν₄ < ν₅ < ν₆` (`node_chain`), and consequently all")
    L.append("  15 pairs of node values are distinct (`node_values_distinct`).")
    L.append("  Together with the bridge this says: the Gram matrix at any z in")
    L.append("  the box has exactly six distinct off-diagonal values, and the")
    L.append("  node-class counting of the balancing layer coincides with the")
    L.append("  counting of distinct Gram values.")
    L.append("")
    L.append("Honest scope note (B1 boundary, D61-3): the l4_orbit (P1)–(P4) filter")
    L.append("enumeration (K9 six-colour scout + interval re-verification + iso")
    L.append("classification) is a numerics-layer duty and is NOT part of this file;")
    L.append("the orbit-dimension / transverse-coordinate geometry of the original")
    L.append("stageb-scope §2 B1 wording is deferred to a later piece.")
    L.append("-/")
    L.append("")
    L.append("set_option maxHeartbeats 1000000")
    L.append("set_option linter.unusedVariables false")
    L.append("")
    L.append("namespace ThomsonN9.TableB1")
    L.append("")
    L.append("open ThomsonN9.TableB1Data")
    L.append("")
    L.append("/-! ### 45 逐对 Gram 定理（证书乘子＝发射器精确生成） -/")
    names_all = []
    for i in range(9):
        for j in range(i, 9):
            txt, name = gram_theorem_text(i, j, certs[(i, j)], cls.get((i, j)))
            if i == j:
                doc = f"/-- 对角归一：⟪r_{ROWS[i]},r_{ROWS[i]}⟫ = 1。 -/"
            else:
                k = cls[(i, j)]
                doc = (f"/-- ⟪r_{ROWS[i]},r_{ROWS[j]}⟫ = {NU_NAMES[k]} z"
                       f"（{NU_DOCS[k]}）。 -/")
            L.append(doc)
            L.append(txt)
            L.append("")
            names_all.append(name)
    L.append("/-! ### 行/节点索引装配与分类桥 -/")
    L.append("/-- 行索引装配：rowOfN k z = 第 k 行（k < 9；行序同 Data 件，")
    L.append("帽行为常量行）。 -/")
    L.append("noncomputable def rowOfN : ℕ → ℝ → ℝ × ℝ × ℝ")
    for k in range(6):
        L.append(f"  | {k} => row{ROWS[k]}")
    for k in range(6, 9):
        L.append(f"  | {k} => fun _ => row{ROWS[k]}")
    L.append("  | _ => rowT0")
    L.append("")
    L.append("/-- 节点曲线索引装配：nuOfN k z = ν_(k+1)（k < 6）。 -/")
    L.append("noncomputable def nuOfN : ℕ → ℝ → ℝ")
    for k in range(6):
        L.append(f"  | {k} => {NU_NAMES[k]}")
    L.append("  | _ => nu6")
    L.append("")
    L.append("/-- 算术分类函数（i = j 时为哑值 9）：同块 → 三角内部(4)/帽帽(2)；")
    L.append("帽-棱残差 (cap−prism)%3≡1 → ν₂(1)、≡0,2 → ν₆(5)；异侧三角 同余 →")
    L.append("竖棱(3)、不同余 → 上下错位(0)。与 l4_orbit.json orbitBalance 六类")
    L.append("计数对账（发射器几何分类 36/36 对账）。 -/")
    L.append("def nodeOfN : ℕ → ℕ → ℕ")
    L.append("  | i, j => if i = j then 9")
    L.append("    else if i / 3 = j / 3 then (if i / 3 = 2 then 2 else 4)")
    L.append("    else if i / 3 = 2 then (if (i % 3 + 3 - j % 3) % 3 = 1 then 1 else 5)")
    L.append("    else if j / 3 = 2 then (if (j % 3 + 3 - i % 3) % 3 = 1 then 1 else 5)")
    L.append("    else if i % 3 = j % 3 then 3 else 0")
    L.append("")
    L.append("/-- **分类桥**：对一切 k < l < 9，第 (k,l) 对的 Gram 内积等于其算术")
    L.append("分类 nodeOfN 所指节点曲线（interval_cases 只生成合法 l 臂——每臂调用")
    L.append("该对专属 Gram 定理；证书层与计数层的正式链接）。 -/")
    L.append("theorem gram_nodeOfN (z : ℝ) (hz : z^2 ≤ 1) : ∀ k l : ℕ, k < 9 → l < 9 → k < l →")
    L.append("    dot3 (rowOfN k z) (rowOfN l z) = nuOfN (nodeOfN k l) z := by")
    L.append("  intro k l hk hl hkl")
    L.append("  interval_cases k")
    for k in range(9):
        L.append("  · interval_cases l")
        for l in range(k + 1, 9):
            L.append(f"    · exact gram_{ROWS[k]}_{ROWS[l]} z hz")
    L.append("")
    L.append("/-! ### 对角归一（∀ 包装） -/")
    L.append("/-- 对角归一：一切 k < 9 行单位范数。 -/")
    L.append("theorem diag_norm_all (z : ℝ) (hz : z^2 ≤ 1) : ∀ k : ℕ, k < 9 →")
    L.append("    dot3 (rowOfN k z) (rowOfN k z) = 1 := by")
    L.append("  intro k hk")
    L.append("  interval_cases k")
    for k in range(9):
        L.append(f"  · exact gram_diag_{ROWS[k]} z hz")
    L.append("")
    L.append("/-! ### 轨道配平计数（Finset.filter decide） -/")
    L.append("/-- 六类边计数 edgeMult：6/6/3/3/6/12（l4_orbit.json tubeMults）。 -/")
    L.append("def edgeMult : ℕ → ℕ")
    L.append("  | 0 => 6 | 1 => 6 | 2 => 3 | 3 => 3 | 4 => 6 | _ => 12")
    L.append("")
    L.append("/-- **六类边计数**：36 条无序对按 nodeOfN 分类的逐类计数 == 6/6/3/3/6/12。 -/")
    L.append("theorem edge_counts : ∀ c : Fin 6, (Finset.univ.filter (fun p : Fin 9 × Fin 9 =>")
    L.append("    p.1.val < p.2.val ∧ nodeOfN p.1.val p.2.val = c.val)).card")
    L.append("    = edgeMult c.val := by decide")
    L.append("")
    L.append("/-- 36 条无序对总数。 -/")
    L.append("theorem edge_total : (Finset.univ.filter (fun p : Fin 9 × Fin 9 =>")
    L.append("    p.1.val < p.2.val)).card = 36 := by decide")
    L.append("")
    L.append("/-- 多重集总和 == 36。 -/")
    L.append("theorem edgeMult_sum : (∑ c ∈ (Finset.univ : Finset (Fin 6)), edgeMult c.val) = 36 := by")
    L.append("  decide")
    L.append("")
    L.append("/-- 棱顶轨道轮廓 (2,1,0,1,2,2)。 -/")
    L.append("def prismProf : ℕ → ℕ")
    L.append("  | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 2 | _ => 2")
    L.append("/-- 帽顶轨道轮廓 (0,2,2,0,0,4)。 -/")
    L.append("def capProf : ℕ → ℕ")
    L.append("  | 0 => 0 | 1 => 2 | 2 => 2 | 3 => 0 | 4 => 0 | _ => 4")
    L.append("")
    L.append("/-- **棱顶轮廓**：六个棱顶（上/下三角）逐类邻接计数 == (2,1,0,1,2,2)。 -/")
    L.append("theorem prism_profile : ∀ (v : Fin 9) (c : Fin 6), v.val < 6 →")
    L.append("    (Finset.univ.filter (fun j : Fin 9 =>")
    L.append("      v.val ≠ j.val ∧ nodeOfN v.val j.val = c.val)).card")
    L.append("    = prismProf c.val := by decide")
    L.append("")
    L.append("/-- **帽顶轮廓**：三个帽顶逐类邻接计数 == (0,2,2,0,0,4)。 -/")
    L.append("theorem cap_profile : ∀ (v : Fin 9) (c : Fin 6), 6 ≤ v.val →")
    L.append("    (Finset.univ.filter (fun j : Fin 9 =>")
    L.append("      v.val ≠ j.val ∧ nodeOfN v.val j.val = c.val)).card")
    L.append("    = capProf c.val := by decide")
    L.append("")
    L.append("/-- **Σ_y 配平定理**：逐类 Σ_v profile_v(c) == 2·mult(c)（双计数恒等，")
    L.append("l4_orbit.json orbitBalance.perNodeSums_Sigma_y 同源）。 -/")
    L.append("theorem sigma_y_balance : ∀ c : Fin 6,")
    L.append("    (∑ v ∈ (Finset.univ : Finset (Fin 9)), (Finset.univ.filter (fun j : Fin 9 =>")
    L.append("      v.val ≠ j.val ∧ nodeOfN v.val j.val = c.val)).card)")
    L.append("    = 2 * edgeMult c.val := by decide")
    L.append("")
    L.append("/-! ### 节点分离容器（z 盒上） -/")
    L.append("/-- **ν 容器定理**：z 盒内一切 z，六 ν 曲线各落在其有理容器内")
    L.append("（12 合取；ν₁/ν₄/ν₅ 走 z² 有理包端点精确式，ν₂/ν₆ 走 ρ Newton 包")
    L.append("（Real.sqrt_le_sqrt＋字面 sqrt_le_iff），ν₃ 为点容器）。 -/")
    L.append("theorem nu_containers (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :")
    conj = []
    for c in range(6):
        conj += [f"(nu{c+1}Lo:ℝ) ≤ {NU_NAMES[c]} z", f"{NU_NAMES[c]} z ≤ (nu{c+1}Hi:ℝ)"]
    L.append("    " + " ∧ ".join(conj[0:2]))
    for s in range(2, 12, 2):
        L.append("    ∧ " + " ∧ ".join(conj[s:s + 2]))
    L.append(" := by")
    L.append("  have hzLop : (0:ℝ) < (zLo:ℝ) := by norm_num [zLo]")
    L.append("  have hzhi : (0:ℝ) < (zHi:ℝ) := by norm_num [zHi]")
    L.append("  have hpos : (0:ℝ) < z := by nlinarith [h1, hzLop]")
    L.append("  have hzlo2 : (zLo:ℝ)^2 ≤ z^2 := by nlinarith [h1, hpos]")
    L.append("  have hzhi2 : z^2 ≤ (zHi:ℝ)^2 := by nlinarith [h2, hpos, hzhi]")
    L.append("  have hzh1 : (zHi:ℝ) < 1 := by norm_num [zHi]")
    L.append("  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith [hzhi2, hzh1]")
    L.append("  have hsq : 1 - z^2 ≤ 1 - (zLo:ℝ)^2 := by nlinarith [hzlo2]")
    L.append("  have hlit : Real.sqrt (1 - (zLo:ℝ)^2) ≤ (rhoUp:ℝ) := by")
    L.append("    rw [Real.sqrt_le_iff]")
    L.append("    constructor <;> norm_num [rhoUp, zLo]")
    L.append("  have hrUp : rhoR z ≤ (rhoUp:ℝ) := by")
    L.append("    calc rhoR z = Real.sqrt (1 - z^2) := rfl")
    L.append("      _ ≤ Real.sqrt (1 - (zLo:ℝ)^2) := Real.sqrt_le_sqrt hsq")
    L.append("      _ ≤ (rhoUp:ℝ) := hlit")
    L.append("  have hrDn : (rhoDn:ℝ) ≤ rhoR z := by")
    L.append("    have e : ((rhoDn:ℝ))^2 ≤ 1 - z^2 := by")
    L.append("      nlinarith [(show ((rhoDn:ℝ))^2 ≤ 1 - (zHi:ℝ)^2 by norm_num [rhoDn, zHi]),")
    L.append("        hzhi2]")
    L.append("    have hp : (0:ℝ) < (rhoDn:ℝ) := by norm_num [rhoDn]")
    L.append("    rw [show rhoR z = Real.sqrt (1 - z^2) from rfl]")
    L.append("    nlinarith [e, hp, Real.sqrt_nonneg (1 - z^2), Real.sq_sqrt hnn]")
    L.append("  have e1 : nu1 z = -(1 + z^2)/2 := by unfold nu1; ring")
    L.append("  have e2 : nu2 z = -(rhoR z) := by unfold nu2; ring")
    L.append("  have e3 : nu3 z = -1/2 := by unfold nu3; ring")
    L.append("  have e4 : nu4 z = 1 - 2*z^2 := by unfold nu4; ring")
    L.append("  have e5 : nu5 z = (3*z^2 - 1)/2 := by unfold nu5; ring")
    L.append("  have e6 : nu6 z = rhoR z / 2 := by unfold nu6; ring")
    L.append("  have c1lo : (nu1Lo:ℝ) = -(1 + (zHi:ℝ)^2)/2 := by norm_num [nu1Lo, zHi]")
    L.append("  have c1hi : (nu1Hi:ℝ) = -(1 + (zLo:ℝ)^2)/2 := by norm_num [nu1Hi, zLo]")
    L.append("  have c3lo : (nu3Lo:ℝ) = -1/2 := by norm_num [nu3Lo]")
    L.append("  have c3hi : (nu3Hi:ℝ) = -1/2 := by norm_num [nu3Hi]")
    L.append("  have c4lo : (nu4Lo:ℝ) = 1 - 2*(zHi:ℝ)^2 := by norm_num [nu4Lo, zHi]")
    L.append("  have c4hi : (nu4Hi:ℝ) = 1 - 2*(zLo:ℝ)^2 := by norm_num [nu4Hi, zLo]")
    L.append("  have c5lo : (nu5Lo:ℝ) = (3*(zLo:ℝ)^2 - 1)/2 := by norm_num [nu5Lo, zLo]")
    L.append("  have c5hi : (nu5Hi:ℝ) = (3*(zHi:ℝ)^2 - 1)/2 := by norm_num [nu5Hi, zHi]")
    L.append("  have c2lo : (nu2Lo:ℝ) = -(rhoUp:ℝ) := by norm_num [nu2Lo, rhoUp]")
    L.append("  have c2hi : (nu2Hi:ℝ) = -(rhoDn:ℝ) := by norm_num [nu2Hi, rhoDn]")
    L.append("  have c6lo : (nu6Lo:ℝ) = (rhoDn:ℝ)/2 := by norm_num [nu6Lo, rhoDn]")
    L.append("  have c6hi : (nu6Hi:ℝ) = (rhoUp:ℝ)/2 := by norm_num [nu6Hi, rhoUp]")
    L.append("  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith")
    L.append("")
    L.append("/-- **节点链**：z 盒上 ν₁ < ν₂ < ν₃ < ν₄ < ν₅ < ν₆（容器＋五链不交）。 -/")
    L.append("theorem node_chain (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :")
    L.append("    nu1 z < nu2 z ∧ nu2 z < nu3 z ∧ nu3 z < nu4 z ∧ nu4 z < nu5 z ∧")
    L.append("    nu5 z < nu6 z := by")
    L.append("  have hc := nu_containers z h1 h2")
    L.append("  have d1 : (nu1Hi:ℝ) < (nu2Lo:ℝ) := by norm_num [nu1Hi, nu2Lo]")
    L.append("  have d2 : (nu2Hi:ℝ) < (nu3Lo:ℝ) := by norm_num [nu2Hi, nu3Lo]")
    L.append("  have d3 : (nu3Hi:ℝ) < (nu4Lo:ℝ) := by norm_num [nu3Hi, nu4Lo]")
    L.append("  have d4 : (nu4Hi:ℝ) < (nu5Lo:ℝ) := by norm_num [nu4Hi, nu5Lo]")
    L.append("  have d5 : (nu5Hi:ℝ) < (nu6Lo:ℝ) := by norm_num [nu5Hi, nu6Lo]")
    L.append("  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith")
    L.append("")
    L.append("/-- **15 对两两分离**：z 盒上任意两个不同节点曲线值不相等")
    L.append("（节点链的配对推论；interval_cases 30 臂）。 -/")
    L.append("theorem node_values_distinct (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :")
    L.append("    ∀ k l : ℕ, k < 6 → l < 6 → k ≠ l → nuOfN k z ≠ nuOfN l z := by")
    L.append("  obtain ⟨c1, c2, c3, c4, c5⟩ := node_chain z h1 h2")
    L.append("  intro k l hk hl hne")
    L.append("  rcases lt_or_gt_of_ne hne with h | h")
    L.append("  · interval_cases k <;> interval_cases l <;> simp only [nuOfN] <;> linarith")
    L.append("  · interval_cases l <;> interval_cases k <;> simp only [nuOfN] <;> linarith")
    L.append("")
    L.append("end ThomsonN9.TableB1")
    MAIN_LEAN.parent.mkdir(parents=True, exist_ok=True)
    MAIN_LEAN.write_text("\n".join(L) + "\n")
    return names_all


# ============================================================ 回读自检
def selfcheck(W, spots, spot_rho):
    import re
    src_data = DATA_LEAN.read_text()
    src_main = MAIN_LEAN.read_text()
    parsed = {m.group(1): Fr(m.group(2))
              for m in re.finditer(r"^def (\w+) : ℚ := (-?\d+/\d+)$", src_data, re.M)}
    want = {"zLo": W["z_lo"], "zHi": W["z_hi"], "rhoDn": W["rhoDn"], "rhoUp": W["rhoUp"]}
    for k in range(6):
        want[f"nu{k+1}Lo"] = W["cont"][k][0]
        want[f"nu{k+1}Hi"] = W["cont"][k][1]
    for k in range(3):
        want[f"spotZ{k}"] = spots[k]
        want[f"spotRhoDn{k}"] = spot_rho[k][0]
        want[f"spotRhoUp{k}"] = spot_rho[k][1]
    for k, v in want.items():
        if parsed.get(k) != v:
            fail(f"回读自检失配：def {k} 源码字面量 ≠ 重导值")
    n_key = 0
    for (i, j), (C1, C2) in W["certs"].items():
        ri, rj = ROWS[i], ROWS[j]
        if i == j:
            name, rhs = f"gram_diag_{ri}", "1"
        else:
            name = f"gram_{ri}_{rj}"
            rhs = f"{NU_NAMES[W['cls'][(i, j)]]} z"
        pat = (rf"theorem {name} \(z : ℝ\) \(hz : z\^2 ≤ 1\) :\n"
               rf"    dot3 {re.escape(row_arg(i))} {re.escape(row_arg(j))} = {re.escape(rhs)} := by\n"
               r"(?:.*\n)*?"
               rf"      = {re.escape(render_mult(C1))} \* \(s3R \* s3R - 3\)\n"
               rf"        \+ {re.escape(render_mult(C2))} \* \(rhoR z \* rhoR z \+ z\^2 - 1\) := by")
        if not re.search(pat, src_main):
            fail(f"回读自检失配：{name} 证书乘子文本 ≠ 引擎重导")
        n_key += 1
    for i in range(9):
        for j in range(i + 1, 9):
            if f"exact gram_{ROWS[i]}_{ROWS[j]} z hz" not in src_main:
                fail(f"回读自检失配：桥接缺臂 gram_{ROWS[i]}_{ROWS[j]}")
    for k, z in enumerate(spots):
        if f"theorem spot{k}_containers" not in src_data:
            fail(f"回读自检失配：spot{k}_containers 缺场")
        z2 = z * z
        rho_dn, rho_up = spot_rho[k]
        if not (rho_dn * rho_dn <= 1 - z2 <= rho_up * rho_up):
            fail(f"抽查 {k} 逐点 ρ 包失守")
        vals = {0: -(1 + z2) / 2, 2: Fr(-1, 2), 3: 1 - 2 * z2, 4: (3 * z2 - 1) / 2}
        for c in range(6):
            lo, hi = W["cont"][c]
            if c == 1:
                ok = lo <= -rho_up and -rho_dn <= hi
            elif c == 5:
                ok = lo <= rho_dn / 2 and rho_up / 2 <= hi
            else:
                ok = lo <= vals[c] <= hi
            if not ok:
                fail(f"抽查 {k} ν{c+1} 容器包含性失守")
    return dict(n_defs=len(want), n_key=n_key)


# ============================================================ 主流程
def main() -> None:
    t0 = time.time()
    W = rederive()
    log(f"[rederive] z 盒==local_min 严格区间精确有理端点 ✓；l4_orbit zBox 严格外扩 ✓；"
        f"2ν 曲线串 6/6 对账 ✓；几何分类==算术规则 36/36 ✓；计数 {W['counts']}=="
        f"tubeMults ✓；轮廓 {W['prism_prof']}/{W['cap_prof']}＋Σ_y==2·mult ✓；"
        f"ρ 包 rhoDn²≤1−z_hi²≤ρ²≤1−z_lo²≤rhoUp² ✓；五链不交 {all(W['chain_gaps'])} ✓"
        f"（真值范围⊆外扩(1e-15) json 节点区间 ✓）")

    spots = spot_points(W["z_lo"], W["z_hi"])
    spot_rho = [(sqrt_rat(F1 - z * z, "lo"), sqrt_rat(F1 - z * z, "hi"))
                for z in spots]

    emit_data_lean(W, spots, spot_rho)
    names = emit_main_lean(W)
    sc = selfcheck(W, spots, spot_rho)
    log(f"[emit ] TableB1Data.lean（{DATA_LEAN.stat().st_size / 1e3:.0f}KB，"
        f"{sc['n_defs']} ℚ def）＋TableB1.lean（{MAIN_LEAN.stat().st_size / 1e3:.0f}KB，"
        f"{len(names)} Gram 定理）＋回读自检逐位对账全过")

    data_b1 = DATA_LEAN.read_bytes()
    main_b1 = MAIN_LEAN.read_bytes()
    emit_data_lean(W, spots, spot_rho)
    emit_main_lean(W)
    if DATA_LEAN.read_bytes() != data_b1 or MAIN_LEAN.read_bytes() != main_b1:
        fail("确定性重跑字节不一致（TableB1Data.lean/TableB1.lean）")
    log("[rerun ] 确定性重跑：两 Lean 件字节一致 ✓")

    import re as _re
    checks = dict(
        z_box_local_min_exact=True,
        l4_orbit_zbox_contains=Fr(W["orb"]["inputs"]["zBox"][0]) < W["z_lo"]
        and W["z_hi"] < Fr(W["orb"]["inputs"]["zBox"][1]),
        curves_x2_match=[poly_str_zr(nu2_zr(k)) for k in range(6)]
        == W["orb"]["nodes"]["curves_x2"],
        classification_arithmetic_match=all(
            nodeOfN_rule(i, j) == c for (i, j), c in W["cls"].items()),
        counts_match_tubeMults=W["counts"] == MULTS,
        counts_total_36=sum(W["counts"]) == 36,
        prism_profile_match=W["prism_prof"] == W["orb"]["orbitBalance"]["prismVertexProfile"],
        cap_profile_match=W["cap_prof"] == W["orb"]["orbitBalance"]["capVertexProfile"],
        sigma_y_eq_two_mult=W["sigma_y"] == W["two_mult"],
        rho_newton_envelope=W["rhoDn"] ** 2 <= 1 - W["z2_hi"]
        and 1 - W["z2_lo"] <= W["rhoUp"] ** 2 and 0 < W["rhoDn"] < W["rhoUp"],
        containers_disjoint_chain=all(W["chain_gaps"]),
        json_intervals_widened_contain_true=W["json_widened_ok"],
        diag_normalization_all9=True,
    )
    for k, v in checks.items():
        if v is False:
            fail(f"重导检查失守：{k}")

    doc = dict(
        kind="n9-r15-b1-data",
        task="r15b-tableb-b1",
        script="bounds/r15_b1_data.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        seed=SEED,
        heavy_solves=0,
        inputs=dict(
            local_min_json=dict(path="numerics/bounds/results/local_min.json",
                                sha256=sha256_of(LM_JSON),
                                role="只读（z 盒唯一隔离源 zStarIntervalMpmath 精确有理端点）"),
            l4_orbit_json=dict(path="numerics/bounds/results/l4_orbit.json",
                               sha256=sha256_of(ORB_JSON),
                               role="只读（节点/计数记录面对账：zBox 严格外扩、curves_x2、"
                                    "orbitBalance 六类计数/轮廓/Σ_y）")),
        z_box=dict(
            z_lo=fs(W["z_lo"]), z_hi=fs(W["z_hi"]),
            source="local_min.json zStarIntervalMpmath（严格隔离区间精确有理端点；"
                   "与 l4.json ttp_interval.z_box 逐位同源——B5 已锚）",
            l4_orbit_zbox_contains=checks["l4_orbit_zbox_contains"],
            note="l4_orbit.json inputs.zBox 为严格外扩 dyadic 盒（orb_lo < zLo < zHi < orb_hi）"),
        rows=dict(
            order=ROWS,
            source="l4_orbit.family_points_s3 / family.py tri_cap_prism（上三角 0–2、"
                   "下三角 3–5、帽 6–8；独立第二实现重导）"),
        nodes=dict(
            names=NU_NAMES,
            formulas=NU_FORMULAS,
            curves_x2_match_json=checks["curves_x2_match"]),
        classification=dict(
            pairs={f"{ROWS[i]}_{ROWS[j]}": W["cls"][(i, j)]
                   for (i, j) in sorted(W["cls"])},
            arithmetic_rule="同块 → 三角内部(4)/帽帽(2)；帽-棱 (cap−prism)%3≡1→ν₂(1)、"
                            "≡0,2→ν₆(5)；异侧三角 同余→竖棱(3)、不同余→错位(0)",
            arithmetic_match_geometric=checks["classification_arithmetic_match"]),
        certificates=dict(
            scheme="key: dot3 r_i r_j − ν_c == C1·(s3R·s3R−3) + C2·(rhoR z·rhoR z + z^2 − 1)，"
                   "C1/C2 ∈ ℚ[z,ρ,√3] 由确定性归约精确生成（s 次数≥2 先消），"
                   "D'==0 即恒等式成立",
            count=len(W["certs"]),
            per_pair={(f"gram_diag_{ROWS[i]}" if i == j else
                       f"gram_{ROWS[i]}_{ROWS[j]}"):
                      dict(C1=render_mult(C1), C2=render_mult(C2))
                      for (i, j), (C1, C2) in sorted(W["certs"].items())}),
        balancing=dict(
            edge_counts=W["counts"], mults=MULTS, total=sum(W["counts"]),
            prism_profile=W["prism_prof"], cap_profile=W["cap_prof"],
            sigma_y=W["sigma_y"], two_times_mult=W["two_mult"],
            json_orbitBalance_match=all([
                W["prism_prof"] == W["orb"]["orbitBalance"]["prismVertexProfile"],
                W["cap_prof"] == W["orb"]["orbitBalance"]["capVertexProfile"],
                W["sigma_y"] == W["orb"]["orbitBalance"]["perNodeSums_Sigma_y"],
                W["two_mult"] == W["orb"]["orbitBalance"]["twoTimesMult"]]),
            erratum="任务书/D12 勘误口径：帽-棱 12 边 ν₆＋6 边 ν₂（ν₅ 的 6 边在上下"
                    "三角内部）；l4_orbit.json orbitBalance.erratum 同源"),
        containers=dict(
            z2_lo=fs(W["z2_lo"]), z2_hi=fs(W["z2_hi"]),
            rhoDn=fs(W["rhoDn"]), rhoUp=fs(W["rhoUp"]),
            rho_scheme="200-bit Newton（isqrt 下界/isqrt(⌊q·2^400⌋+1)+1 上界，B5 sqrt_rat 同族）",
            nu=[dict(lo=fs(W["cont"][k][0]), hi=fs(W["cont"][k][1]),
                     kind=["z2-exact", "rho-envelope", "point",
                           "z2-exact", "z2-exact", "rho-envelope"][k])
                for k in range(6)],
            disjoint_chain=[fs(W["cont"][k][1]) + " < " + fs(W["cont"][k + 1][0])
                            for k in range(5)],
            json_reconciliation="nodes.intervals 为 20 位显示舍入——精确对账＝真值范围"
                                "⊆外扩(1e-15) json 区间（Fraction 精确，全 6 类过）；"
                                "原始容器-显示端点差为舍入尘量级（advisory）",
            json_advisory_display_gap=W["json_adv"]),
        spot_checks=dict(
            scheme=("seed 20261017；k=0,1,2 依次 i=rng.randint(⌊z_lo·2⁴⁰⌋,⌈z_hi·2⁴⁰⌉)、"
                    "z=i/2⁴⁰（2⁻⁴⁰ 网格）；ν₂/ν₆ 走逐点 Newton ρ 包（200-bit），"
                    "ν₁/ν₃/ν₄/ν₅ 为 z 的有理函数精确值；Lean 定理 spot{k}_containers"
                    "与发射器 Fraction 重算对账"),
            points=[dict(z=fs(z), rhoDn=fs(spot_rho[k][0]), rhoUp=fs(spot_rho[k][1]))
                    for k, z in enumerate(spots)]),
        lean=dict(
            data_file="formal/lean/ThomsonN9/TableB1Data.lean（本发射器确定性生成；仅 import Mathlib）",
            main_file="formal/lean/ThomsonN9/TableB1.lean（本发射器确定性生成——r13_a1 "
                      "emit_main_lean 先例；仅 import Mathlib＋ThomsonN9.TableB1Data；"
                      "零数值数据字面量（容器/盒/包全部经 Data 件名字锚定））",
            data_sha256=sha256_of(DATA_LEAN),
            main_sha256=sha256_of(MAIN_LEAN),
            theorem_counts=dict(
                data=len(_re.findall(r"^theorem ", DATA_LEAN.read_text(), _re.M)),
                main=len(_re.findall(r"^theorem ", MAIN_LEAN.read_text(), _re.M))),
            gram_theorems=len(names)),
        scope_note=("B1 算术层（表 B 第三件）：(P5) 实现证书（45 Gram 恒等式）＋轨道配平"
                    "（六类计数/轮廓/Σ_y）＋节点分离容器；l4_orbit (P1)–(P4) 过滤枚举"
                    "＝数值层职责不在件；『轨道维数/横截坐标』几何部分后续件另议（D61-3）"),
        rederive_checks={k: bool(v) for k, v in checks.items()},
        wall_s=round(time.time() - t0, 1),
    )
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    log(f"[done ] {OUT_JSON}（{doc['wall_s']}s）；exit 0")


if __name__ == "__main__":
    main()
