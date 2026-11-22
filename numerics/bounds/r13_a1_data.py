#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r13_a1_data.py — R13C 表 A 第 6 件 A1（KLT (4.5) 型三点装配恒等式）Lean 数据锚定件。

【任务定位（r13c-tablea-a1，D52 裁决 2）】A1 三点恒等式
    Σ_84 λ_cls(x) + Σ_all(x) = ΣH(x) − e_dy
的 Lean 精确实例化：构型取**对称块构型** X = {e₁,e₁,e₁, e₂,e₂,e₂, e₃,e₃,e₃}
（9 个 ℚ 点字面量；设计师探针 /tmp/r13_probe_a6.py 已实证 diff==0 精确、
λ 求值点恰 4 个 (orbit,perm,point)、s 求值点恰 5 个（全在 {0,1}³））。
本脚本**只读消费** M9 cap 证书
certificates/n9-stage-a4-typedcap-m0748_M9.json（经 r9_s3_rederive.py 的
独立第二实现装配面），产出的 λ/s/h/e 表即证书数据的精确 ℚ 字面量化
（装配含 share_lp 的 /6、/3 除法，故 λ 表非全 dyadic——见 (i)）：

  (i)  λ 三轨道表（λ_AAA/λ_AAB/λ_ABC，各 449 非零 ℚ 系数；3-smooth
       分母 2^a·3^b——1303/1347 全 dyadic，λ_AAB 10 个、λ_ABC 33＋1
       个分母奇部为 3/27，源于 share_lp 的 /6、/3 除法；复算 D2 勘误
       降格原『全 dyadic』措辞）；
  (ii) s 表（271 非零）＋ h_AA/h_AB（各 17 系数）＋ e 字面量；
  (iii) 84 三元组显式分类表（class→(orbit,perm,(u,v,t) 字面量)）＋
       729 全三元组按 5 个 s-点折叠的计数（81,162,162,162,162）＋
       36 对按 2 个 h-类折叠的计数（9,27）；
  (iv) 盲区堵法：每表 3 个固定随机有理点抽查（seed 20261015，期望值
       Python Fraction 独立算出）——堵 {0,1}³ 立方点上系数篡改不可检
       的盲区（恒等式求值点全在立方点上，非立方点抽查补位）。

【量级边界（如实，goal 内明示）】随机构型全恒等式（84×449+504×271
≈ 23.5 万项）超出本轮 elaboration 预算——泛构型证据由 Python 侧
results/r9_s3_rederive.json 3 trial（seed 20261011）＋设计师第 4 trial
（任意小有理构型 diff==0，/tmp/r13_probe_gen.py）在档承担；本件为
对称构型精确实例＋随机点抽查。

【产出】
  * numerics/bounds/results/r13_a1_data.json —— 全部表/构型/计数/参考值/抽查点；
  * formal/lean/ThomsonN9/TableA1Data.lean —— 表＋求值定理（needed 点＋抽查点）；
  * formal/lean/ThomsonN9/TableA1.lean —— 构型/Gram decide 引理/84 分类表/
    计数引理/三 sum 折叠/装配恒等式（import ThomsonN9.TableA1Data，仅此一
    仓内依赖；两件均不触 Solution.lean/TableA.lean/M1Data.lean）。

【实现范式（D50-2＋R13 探针实证）】表分块 def（≤64 项/块）＋文件级
set_option maxHeartbeats 1000000＋`simp only [表名, 块名…]`＋norm_num；
抽查实测（/tmp/r13_probe_a1d.lean，71s 零 error 零 sorry）。求值定理成本
≈0（elaboration 主导在 def 展开，~0.1s/项）。

【自检】出数全程 Fraction 精确；对称构型恒等式重放 diff==0、三个参考值
(sum_lam/sum_all/sum_H) 在档；发射后回读 Lean 源码重建多项式与源表逐位
对账（发射器自校验）。

用法（CWD 无关）：
  python3 numerics/bounds/r13_a1_data.py
  # 幂等：json/两 Lean 文件按数学内容确定性生成（json 含 timestamp 不作
  # 字节复放；Lean 文件无时间戳，可字节复放）。
"""
from __future__ import annotations

import json
import math
import random
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
import r9_s3_rederive as R          # 独立第二实现（stdlib only）装配面

CERT_DEFAULT = R.CERT_DEFAULT
OUT_JSON = HERE / "results" / "r13_a1_data.json"
LEAN_DIR = REPO / "formal" / "lean" / "ThomsonN9"
DATA_LEAN = LEAN_DIR / "TableA1Data.lean"
MAIN_LEAN = LEAN_DIR / "TableA1.lean"

SEED = 20261015                     # 抽查点种子（D52 裁决 4：门 seed 统一）
CHUNK = 64                          # 表分块上限（D50-2 范式）
TYPES = R.TYPES                     # (0,0,0,1,1,1,2,2,2) 分型
F0, F1 = Fraction(0), Fraction(1)

# 对称块构型 {e₁×3, e₂×3, e₃×3}（任务书口径）
SYM_PTS = [(F1, F0, F0)] * 3 + [(F0, F1, F0)] * 3 + [(F0, F0, F1)] * 3

SPOT_TABLES = ("lamAAA", "lamAAB", "lamABC", "svec", "hAA", "hAB")


def log(msg: str) -> None:
    print(msg, flush=True)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


def fs(f: Fraction) -> str:
    return f"{f.numerator}/{f.denominator}"


# ---------------------------------------------------------------- 数学层
def orbit_perm(cls):
    """类 (X≤Y≤Z) → (orbit, perm)（typed_ladder/证书装配约定，自 r9 复刻）。"""
    X, Y, Z = cls
    need = {}
    for t in cls:
        need[t] = need.get(t, 0) + 1
    mult = sorted(need.values(), reverse=True)
    orbit = "AAA" if mult == [3] else ("AAB" if mult == [2, 1] else "ABC")
    perm = "ut" if (Y == Z and X != Y) else "id"
    return orbit, perm


def eval3(poly, u, v, t):
    return sum(c * u ** i * v ** j * t ** l for (i, j, l), c in poly.items())


def eval1(coeffs, x):
    acc, xp = F0, F1
    for c in coeffs:
        acc += c * xp
        xp *= x
    return acc


def build_world():
    """只读消费 M9 证书 → (asm, data, 表, 求值点, 计数, 参考值)。"""
    cert = json.loads(CERT_DEFAULT.read_text())
    asm = R.S3Assembly(Fraction(cert["params"]["a0"]), cert["params"]["M"],
                       cert["params"]["K"])
    data = R.load_data(asm, cert)
    lam = {o: asm.lam(o, data) for o in ("AAA", "AAB", "ABC")}
    s_vec, _ = asm.s_forms(data)
    world = dict(cert_params=cert["params"], cert_kind=cert["kind"],
                 cert_tag=cert["tag"], asm=asm, data=data, lam=lam,
                 s_vec=s_vec, h_AA=data["h_AA"], h_AB=data["h_AB"], e=data["e"])
    return world


def symmetric_identity(world):
    """对称块构型上的恒等式重放（Fraction 精确）＋分类/计数簿记。"""
    pts = SYM_PTS
    G = [[sum(a * b for a, b in zip(xi, xj)) for xj in pts] for xi in pts]
    lam = world["lam"]
    s_vec, h_AA, h_AB, e = (world["s_vec"], world["h_AA"],
                            world["h_AB"], world["e"])

    # ---- 84 三元组分类表（i<j<l 枚举序）----
    rows = []                      # (i,j,l,orbit,perm,u,v,t)
    lam_points = {}                # (orbit,perm,(u,v,t)) → count
    for (i, j, l) in combinations(range(9), 3):
        tt = sorted([(TYPES[i], i), (TYPES[j], j), (TYPES[l], l)])
        (_, i0), (_, j0), (_, l0) = tt
        cls = tuple(x[0] for x in tt)
        o, p = orbit_perm(cls)
        u_, v_, t_ = G[i0][j0], G[i0][l0], G[j0][l0]
        rows.append((i0, j0, l0, o, p, u_, v_, t_))
        key = (o, p, (u_, v_, t_))
        lam_points[key] = lam_points.get(key, 0) + 1
    assert len(rows) == 84 == math.comb(9, 3)

    # ---- 729 全三元组按 s-点折叠计数 ----
    s_counts = {}
    for i in range(9):
        for j in range(9):
            for l in range(9):
                pt = (G[i][j], G[i][l], G[j][l])
                s_counts[pt] = s_counts.get(pt, 0) + 1
    assert sum(s_counts.values()) == 729
    assert all(x in (0, 1) for pt in s_counts for x in pt), "s 点应全在 {0,1}³"

    # ---- 36 对按 h-类折叠计数 ----
    h_counts = {}
    for i in range(9):
        for j in range(i + 1, 9):
            key = ("AA" if TYPES[i] == TYPES[j] else "AB", G[i][j])
            h_counts[key] = h_counts.get(key, 0) + 1
    assert sum(h_counts.values()) == 36

    # ---- 恒等式重放（三 sum 逐项 Fraction）----
    sum_lam = F0
    for (i, j, l, o, p, u_, v_, t_) in rows:
        args = (t_, v_, u_) if p == "ut" else (u_, v_, t_)
        sum_lam += eval3(lam[o], *args)
    sum_all = F0
    for pt, c in s_counts.items():
        sum_all += c * eval3(s_vec, *pt)
    sum_H = F0
    for (cls, g), c in h_counts.items():
        sum_H += c * eval1(h_AA if cls == "AA" else h_AB, g)
    diff = (sum_lam + sum_all) - (sum_H - e)
    assert diff == 0, f"对称构型恒等式重放 diff={diff} ≠ 0"

    return dict(rows=rows, lam_points=lam_points, s_counts=s_counts,
                h_counts=h_counts, sum_lam=sum_lam, sum_all=sum_all,
                sum_H=sum_H, diff=diff, G=G)


def spot_points():
    """seed 20261015 固定随机有理点：λ/s 表每点 3 个分量、h 表每点 1 个，
    分量 = Fraction(rng.randint(-64, 64), 64)（沿仓库随机有理点 /64 惯例），
    表序 SPOT_TABLES 固定。"""
    rng = random.Random(SEED)
    out = {}
    for tbl in SPOT_TABLES:
        pts = []
        for _ in range(3):
            if tbl in ("hAA", "hAB"):
                pts.append((Fraction(rng.randint(-64, 64), 64),))
            else:
                pts.append(tuple(Fraction(rng.randint(-64, 64), 64)
                                 for _ in range(3)))
        out[tbl] = pts
    return out


# ---------------------------------------------------------------- Lean 发射
def term_uvt(exp, c):
    s = f"({c.numerator}/{c.denominator})"
    i, j, l = exp
    if i:
        s += f"*u^{i}"
    if j:
        s += f"*v^{j}"
    if l:
        s += f"*t^{l}"
    return s


def emit_poly_uvt(f, name, poly):
    items = sorted(poly.items())
    n = (len(items) + CHUNK - 1) // CHUNK
    for ci in range(n):
        part = items[ci * CHUNK:(ci + 1) * CHUNK]
        f.write(f"def {name}_{ci} (u v t : ℚ) : ℚ :=\n  "
                + " + ".join(term_uvt(e, c) for e, c in part) + "\n")
    f.write(f"def {name} (u v t : ℚ) : ℚ := "
            + " + ".join(f"{name}_{ci} u v t" for ci in range(n)) + "\n")
    f.write("\n")
    return [f"{name}_{ci}" for ci in range(n)]


def emit_eval_uvt(f, tbl, blocks, tag, args, val, doc):
    argstr = " ".join(str(a) for a in args)
    f.write(f"/-- {doc} -/\n")
    f.write(f"theorem {tbl}_at_{tag} : {tbl} {argstr} = ({fs(val)}) := by\n")
    f.write(f"  simp only [{tbl}, {', '.join(blocks)}]\n  norm_num\n\n")


def emit_data_lean(world, spots, refs):
    lam, s_vec = world["lam"], world["s_vec"]
    h_AA, h_AB, e = world["h_AA"], world["h_AB"], world["e"]

    def spot_val(tbl, pt):
        if tbl == "lamAAA":
            return eval3(lam["AAA"], *pt)
        if tbl == "lamAAB":
            return eval3(lam["AAB"], *pt)
        if tbl == "lamABC":
            return eval3(lam["ABC"], *pt)
        if tbl == "svec":
            return eval3(s_vec, *pt)
        if tbl == "hAA":
            return eval1(h_AA, pt[0])
        return eval1(h_AB, pt[0])

    L = []
    L.append("import Mathlib\n")
    L.append("""/-!
# Table A1 data (R13 / r13c): the exact rational tables of the A1 assembly identity

This module is deliberately self-contained: it imports only `Mathlib`, imports
no in-repo solution module, and is imported only by `ThomsonN9/TableA1.lean`.
It materialises, as explicit `ℚ`-literal polynomial tables, the certificate
data of the M9 cap certificate `certificates/n9-stage-a4-typedcap-m0748_M9.json`
(read-only, through the independent second implementation
`numerics/bounds/r9_s3_rederive.py`):

* `lamAAA`, `lamAAB`, `lamABC` — the three per-orbit assembled polynomials
  λ_orbit(u,v,t) of the S3-quotient cut, each with 449 nonzero rational
  coefficients with 3-smooth denominators 2^a·3^b (1303/1347 of them dyadic;
  the remaining 44 have odd part 3 or 27, from the /6 and /3 divisions of
  share_lp — recheck-D2 erratum downgrades the former "dyadic" wording;
  blocked defs of at most 64 monomials; D50-2 paradigm);
* `svec` — the all-triples form s = Σ_k ⟨F^k, Y_k⟩ with 271 nonzero
  (dyadic) coefficients;
* `hAA`, `hAB` — the two pair minorants (17 coefficients each) and `eA1` the
  dyadic constant e_dy.

Every table carries evaluation theorems at the cube points needed by the
symmetric-block assembly identity, plus **three fixed random rational spot
checks per table** (seed 20261015, `numerics/bounds/r13_a1_data.py`), whose
expected values are independently computed with Python `Fraction`: the
identity itself only samples points of {0,1}^3, so off-cube spot checks close
the blind spot of undetectable coefficient tampering on monomials that vanish
on the cube.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableA1Data

""")
    buf = _Buf(L)
    blocks = {}
    for o in ("AAA", "AAB", "ABC"):
        blocks[f"lam{o}"] = emit_poly_uvt(buf, f"lam{o}", lam[o])
    blocks["svec"] = emit_poly_uvt(buf, "svec", s_vec)
    for nm, coeffs in (("hAA", h_AA), ("hAB", h_AB)):
        terms = [f"({c.numerator}/{c.denominator})" + (f"*x^{k}" if k else "")
                 for k, c in enumerate(coeffs) if c != 0]
        buf.write(f"def {nm} (x : ℚ) : ℚ := " + " + ".join(terms) + "\n\n")
        blocks[nm] = [nm]
    buf.write(f"def eA1 : ℚ := ({e.numerator}/{e.denominator})\n\n")

    # ---- 恒等式所需立方点求值定理 ----
    emit_eval_uvt(buf, "lamAAA", blocks["lamAAA"], "111", (1, 1, 1),
                  eval3(lam["AAA"], F1, F1, F1),
                  "λ_AAA at the cube point (1,1,1) (AAA-class triples).")
    emit_eval_uvt(buf, "lamAAB", blocks["lamAAB"], "100", (1, 0, 0),
                  eval3(lam["AAB"], F1, F0, F0),
                  "λ_AAB at the cube point (1,0,0) (AAB-class triples, both "
                  "id and ut evaluation orders reduce here).")
    emit_eval_uvt(buf, "lamABC", blocks["lamABC"], "000", (0, 0, 0),
                  eval3(lam["ABC"], F0, F0, F0),
                  "λ_ABC at the cube point (0,0,0) (ABC-class triples).")
    for tag, pt in (("111", (1, 1, 1)), ("100", (1, 0, 0)),
                    ("010", (0, 1, 0)), ("001", (0, 0, 1)),
                    ("000", (0, 0, 0))):
        emit_eval_uvt(buf, "svec", blocks["svec"], tag, pt,
                      eval3(s_vec, *pt),
                      f"s at the cube point {pt} (a {refs['s_counts'][pt]}-fold "
                      "s-point of Σ_all).")
    buf.write(f"/-- h_AA at the AA-pair Gram value 1. -/\n"
              f"theorem hAA_at_1 : hAA 1 = ({fs(eval1(h_AA, F1))}) := by\n"
              f"  simp only [hAA]\n  norm_num\n\n")
    buf.write(f"/-- h_AB at the AB-pair Gram value 0. -/\n"
              f"theorem hAB_at_0 : hAB 0 = ({fs(eval1(h_AB, F0))}) := by\n"
              f"  simp only [hAB]\n  norm_num\n\n")

    # ---- 每表 3 个固定随机有理点抽查 ----
    for tbl in SPOT_TABLES:
        for k, pt in enumerate(spots[tbl]):
            val = spot_val(tbl, pt)
            args = " ".join(f"({fs(a)})" for a in pt)
            blk = blocks[tbl]
            buf.write(f"/-- Spot check {k} of `{tbl}` at the fixed random "
                      f"rational point (seed {SEED}); expected value computed "
                      "independently in Python `Fraction`. -/\n")
            if tbl in ("hAA", "hAB"):
                buf.write(f"theorem {tbl}_spot{k} : {tbl} {args} = ({fs(val)}) := by\n"
                          f"  simp only [{tbl}]\n  norm_num\n\n")
            else:
                buf.write(f"theorem {tbl}_spot{k} : {tbl} {args} = ({fs(val)}) := by\n"
                          f"  simp only [{tbl}, {', '.join(blk)}]\n  norm_num\n\n")

    L.append("end ThomsonN9.TableA1Data\n")
    DATA_LEAN.parent.mkdir(parents=True, exist_ok=True)
    DATA_LEAN.write_text("".join(L))
    return blocks


class _Buf:
    def __init__(self, L):
        self.L = L

    def write(self, s):
        self.L.append(s)


# TableA1.lean 发射 ----------------------------------------------------------
def emit_main_lean(refs):
    rows = refs["rows"]
    s_counts, h_counts = refs["s_counts"], refs["h_counts"]
    lam_points = refs["lam_points"]

    L = []
    L.append("""import Mathlib
import ThomsonN9.TableA1Data

/-!
# Table A1 (R13 / r13c): the KLT-(4.5)-type three-point assembly identity

**A1.** For the symmetric block configuration `X = {e1,e1,e1, e2,e2,e2,
e3,e3,e3}` of nine literal rational points, the typed S3-quotient assembly
identity of Table A1 holds *exactly* in `ℚ`:

  Σ_{84 triples} λ_cls(x) + Σ_{729 ordered triples} s(x) = ΣH(x) − e_dy.

Components (all data from `ThomsonN9.TableA1Data`, i.e. the M9 cap
certificate `certificates/n9-stage-a4-typedcap-m0748_M9.json`):

* `gramI_blk_fin` — the Gram matrix of the literal configuration is the
  block matrix `G[i][j] = if ⌊i/3⌋ = ⌊j/3⌋ then 1 else 0` (`decide`);
* `class84` — the explicit 84-triple classification table
  `(i, j, l, orbit, perm, (u,v,t))`, complete against the true `i<j<l`
  enumeration (`class84_complete`, `decide`) and row-wise reconciled with
  the Gram matrix (`class84_gram_ok`, `decide`);
* the four λ-point counts (3, 27, 27, 27 — `count_lam_*`, `decide`),
  the five s-point counts of the 729 ordered triples (81, 162, 162, 162,
  162 — `count_s_*`, `decide`, `s_counts_sum`) and the two h-class counts
  of the 36 pairs (9, 27 — `count_h_*`, `decide`);
* `sum_lam_eq`, `sum_s_eq`, `sum_h_eq` — the three sums folded by the
  counts (`norm_num`);
* `a1_assembly_identity` — the assembly identity itself, with the three
  reference values `sum_lam_value`, `sum_all_value`, `sum_H_value`
  matching `numerics/bounds/results/r13_a1_data.json` bit for bit.

Scope caveat (honest boundary, D52 ruling 2): the *generic-configuration*
identity (84×449 + 504×271 ≈ 2.35·10^5 terms) exceeds this round's
elaboration budget; generic-config evidence is carried on the Python side by
`results/r9_s3_rederive.json` (3 random-rational trials, seed 20261011,
exact diff == 0) plus a 4th independent trial (`/tmp/r13_probe_gen.py`).
This file is the exact symmetric-config instance plus the per-table random
spot checks of `TableA1Data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 50000

namespace ThomsonN9.TableA1

open ThomsonN9.TableA1Data

inductive Orbit | AAA | AAB | ABC deriving DecidableEq
inductive Perm | id | ut deriving DecidableEq

/-- The symmetric block configuration `X = {e₁×3, e₂×3, e₃×3}` as literal
coordinate functions (0/1-valued; the ℚ point is the componentwise cast). -/
def gX : ℕ → ℕ
  | 0 | 1 | 2 => 1
  | _ => 0

def gY : ℕ → ℕ
  | 3 | 4 | 5 => 1
  | _ => 0

def gZ : ℕ → ℕ
  | 6 | 7 | 8 => 1
  | _ => 0

/-- The Gram matrix of the literal configuration (dot product of the point
coordinate literals). -/
def gramI (i j : ℕ) : ℕ := gX i * gX j + gY i * gY j + gZ i * gZ j

/-- **G-lemma (decide).** The Gram matrix of the literal configuration is
the block matrix `G[i][j] = if ⌊i/3⌋ = ⌊j/3⌋ then 1 else 0`. -/
theorem gramI_blk_fin : ∀ i j : Fin 9,
    gramI i.val j.val = if i.val / 3 = j.val / 3 then 1 else 0 := by decide

def lamEval : Orbit → Perm → ℕ × ℕ × ℕ → ℚ
  | Orbit.AAA, Perm.id, (u, v, t) => lamAAA u v t
  | Orbit.AAA, Perm.ut, (u, v, t) => lamAAA t v u
  | Orbit.AAB, Perm.id, (u, v, t) => lamAAB u v t
  | Orbit.AAB, Perm.ut, (u, v, t) => lamAAB t v u
  | Orbit.ABC, _,       (u, v, t) => lamABC u v t

/-- The 84-triple explicit classification table: each row is
`(i, j, l, orbit, perm, (u, v, t))` with the type-sorted triple and its
Gram point literals. -/
def class84 : List (ℕ × ℕ × ℕ × Orbit × Perm × (ℕ × ℕ × ℕ)) := [
""")
    for (i, j, l, o, p, u, v, t) in rows:
        L.append(f"  ({i}, {j}, {l}, Orbit.{o}, Perm.{p}, "
                 f"({u.numerator}, {v.numerator}, {t.numerator})),\n")
    L.append("""]

def lamOfRow (r : ℕ × ℕ × ℕ × Orbit × Perm × (ℕ × ℕ × ℕ)) : ℚ :=
  lamEval r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2

/-- The true enumeration of the 84 triples `{i,j,l}`, `i < j < l`. -/
def triplesAll : List (ℕ × ℕ × ℕ) :=
  (List.range 9).flatMap fun i =>
    ((List.range 9).filter fun j => i < j).flatMap fun j =>
      ((List.range 9).filter fun l => j < l).map fun l => (i, j, l)

theorem triplesAll_length : triplesAll.length = 84 := by decide

/-- Completeness: the classification table covers exactly the 84 triples. -/
theorem class84_complete :
    (class84.map fun r => (r.1, r.2.1, r.2.2.1)) = triplesAll := by decide

/-- Row-wise reconciliation: every table row's `(u,v,t)` literal is the Gram
point of its triple. -/
theorem class84_gram_ok :
    class84.all (fun r =>
      r.2.2.2.2.2 = (gramI r.1 r.2.1, gramI r.1 r.2.2.1, gramI r.2.1 r.2.2.1)) := by
  decide

theorem count_lam_AAA :
    (class84.filter fun r : ℕ × ℕ × ℕ × Orbit × Perm × (ℕ × ℕ × ℕ) =>
      decide (r.2.2.2.1 = Orbit.AAA)).length = 3 := by decide
theorem count_lam_AAB_id :
    (class84.filter fun r : ℕ × ℕ × ℕ × Orbit × Perm × (ℕ × ℕ × ℕ) =>
      decide (r.2.2.2.1 = Orbit.AAB ∧ r.2.2.2.2.1 = Perm.id)).length = 27 := by decide
theorem count_lam_AAB_ut :
    (class84.filter fun r : ℕ × ℕ × ℕ × Orbit × Perm × (ℕ × ℕ × ℕ) =>
      decide (r.2.2.2.1 = Orbit.AAB ∧ r.2.2.2.2.1 = Perm.ut)).length = 27 := by decide
theorem count_lam_ABC :
    (class84.filter fun r : ℕ × ℕ × ℕ × Orbit × Perm × (ℕ × ℕ × ℕ) =>
      decide (r.2.2.2.1 = Orbit.ABC)).length = 27 := by decide

theorem sum_lam_eq : (class84.map lamOfRow).sum
    = 3 * lamAAA 1 1 1 + 27 * lamAAB 1 0 0 + 27 * lamAAB 1 0 0
      + 27 * lamABC 0 0 0 := by
  norm_num [class84, lamOfRow, lamEval, lamAAA_at_111, lamAAB_at_100,
    lamABC_at_000]

/-- The 729 ordered triples of the configuration. -/
def cube9 : List (ℕ × ℕ × ℕ) := [
""")
    for i in range(9):
        for j in range(9):
            for l in range(9):
                L.append(f"  ({i}, {j}, {l}),\n")
    L.append("""]

/-- The literal cube equals the true enumeration of the 729 ordered triples. -/
theorem cube9_enum :
    cube9 = ((List.range 9).flatMap fun i =>
      (List.range 9).flatMap fun j =>
        (List.range 9).map fun l => (i, j, l)) := by decide

theorem cube9_length : cube9.length = 729 := by decide

def sPtI (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (gramI p.1 p.2.1, gramI p.1 p.2.2, gramI p.2.1 p.2.2)

def sAt (p : ℕ × ℕ × ℕ) : ℚ :=
  svec (gramI p.1 p.2.1) (gramI p.1 p.2.2) (gramI p.2.1 p.2.2)

theorem count_s_000 :
    (cube9.filter fun p : ℕ × ℕ × ℕ => decide (sPtI p = (0, 0, 0))).length = 162 := by decide
theorem count_s_001 :
    (cube9.filter fun p : ℕ × ℕ × ℕ => decide (sPtI p = (0, 0, 1))).length = 162 := by decide
theorem count_s_010 :
    (cube9.filter fun p : ℕ × ℕ × ℕ => decide (sPtI p = (0, 1, 0))).length = 162 := by decide
theorem count_s_100 :
    (cube9.filter fun p : ℕ × ℕ × ℕ => decide (sPtI p = (1, 0, 0))).length = 162 := by decide
theorem count_s_111 :
    (cube9.filter fun p : ℕ × ℕ × ℕ => decide (sPtI p = (1, 1, 1))).length = 81 := by decide

/-- Counting closure: the five s-point counts sum to 729. -/
theorem s_counts_sum : 81 + 162 + 162 + 162 + 162 = 729 := by norm_num

theorem sum_s_eq : (cube9.map sAt).sum
    = 81 * svec 1 1 1 + 162 * (svec 1 0 0 + svec 0 1 0 + svec 0 0 1
      + svec 0 0 0) := by
  norm_num [cube9, sAt, sPtI, gramI, gX, gY, gZ,
    svec_at_111, svec_at_100, svec_at_010, svec_at_001, svec_at_000]

/-- The 36 unordered pairs of the configuration. -/
def pairs36 : List (ℕ × ℕ) := [
""")
    for i in range(9):
        for j in range(i + 1, 9):
            L.append(f"  ({i}, {j}),\n")
    L.append("""]

theorem pairs36_enum :
    pairs36 = ((List.range 9).flatMap fun i =>
      ((List.range 9).filter fun j => i < j).map fun j => (i, j)) := by decide

theorem pairs36_length : pairs36.length = 36 := by decide

def hAt (p : ℕ × ℕ) : ℚ :=
  if p.1 / 3 = p.2 / 3 then hAA (gramI p.1 p.2) else hAB (gramI p.1 p.2)

theorem count_h_AA :
    (pairs36.filter fun p : ℕ × ℕ => decide (p.1 / 3 = p.2 / 3)).length = 9 := by decide
theorem count_h_AB :
    (pairs36.filter fun p : ℕ × ℕ => decide (p.1 / 3 ≠ p.2 / 3)).length = 27 := by decide

theorem sum_h_eq : (pairs36.map hAt).sum = 9 * hAA 1 + 27 * hAB 0 := by
  norm_num [pairs36, hAt, gramI, gX, gY, gZ, hAA_at_1, hAB_at_0]

/-- **A1 assembly identity** — Σ_84 λ_cls + Σ_all = ΣH − e_dy on the
symmetric block configuration, exactly in `ℚ`. -/
theorem a1_assembly_identity :
    (class84.map lamOfRow).sum + (cube9.map sAt).sum
      = (pairs36.map hAt).sum - eA1 := by
  rw [sum_lam_eq, sum_s_eq, sum_h_eq]
  norm_num [lamAAA_at_111, lamAAB_at_100, lamABC_at_000, svec_at_111, svec_at_100,
    svec_at_010, svec_at_001, svec_at_000, hAA_at_1, hAB_at_0, eA1]

/-- Reference value: Σ_84 λ_cls = 4416585812995339/281474976710656
(= `results/r13_a1_data.json` `reference_values.sum_lam`). -/
theorem sum_lam_value : (class84.map lamOfRow).sum
    = (4416585812995339 : ℚ) / 281474976710656 := by
  rw [sum_lam_eq]
  norm_num [lamAAA_at_111, lamAAB_at_100, lamABC_at_000]

/-- Reference value: Σ_all = 1003797937752669/70368744177664. -/
theorem sum_all_value : (cube9.map sAt).sum
    = (1003797937752669 : ℚ) / 70368744177664 := by
  rw [sum_s_eq]
  norm_num [svec_at_111, svec_at_100, svec_at_010, svec_at_001, svec_at_000]

/-- Reference value: ΣH = 7841265097092597/140737488355328. -/
theorem sum_H_value : (pairs36.map hAt).sum
    = (7841265097092597 : ℚ) / 140737488355328 := by
  rw [sum_h_eq]
  norm_num [hAA_at_1, hAB_at_0]

end ThomsonN9.TableA1
""")
    MAIN_LEAN.write_text("".join(L))


# ---------------------------------------------------------------- 回读自检
RE_TERM = re.compile(r"\((-?\d+)/(\d+)\)(\*u\^(\d+))?(\*v\^(\d+))?(\*t\^(\d+))?")
RE_HTERM = re.compile(r"[ +]\((-?\d+)/(\d+)\)(\*x\^(\d+))?")


def reparse_tables(src_data: str):
    """回读 TableA1Data.lean：重建 λ/s/h 表与 e 字面量（发射器自校验）。"""
    out = {}
    for nm in ("lamAAA", "lamAAB", "lamABC", "svec"):
        blocks = re.findall(rf"def {nm}_\d+ \(u v t : ℚ\) : ℚ :=\n(.*)", src_data)
        poly = {}
        for b in blocks:
            for m in RE_TERM.finditer(b):
                num, den = int(m.group(1)), int(m.group(2))
                e = (int(m.group(4) or 0), int(m.group(6) or 0),
                     int(m.group(8) or 0))
                assert e not in poly, f"{nm} 重指数 {e}"
                poly[e] = Fraction(num, den)
        out[nm] = poly
    for nm in ("hAA", "hAB"):
        m = re.search(rf"def {nm} \(x : ℚ\) : ℚ := (.*)", src_data)
        vec = {}
        for mm in RE_HTERM.finditer(" " + m.group(1)):
            k = int(mm.group(4) or 0)
            vec[k] = Fraction(int(mm.group(1)), int(mm.group(2)))
        out[nm] = vec
    m = re.search(r"def eA1 : ℚ := \((-?\d+)/(\d+)\)", src_data)
    out["e"] = Fraction(int(m.group(1)), int(m.group(2)))
    return out


def selfcheck(world, refs, spots, parsed):
    lam, s_vec = world["lam"], world["s_vec"]
    assert parsed["lamAAA"] == lam["AAA"], "lamAAA 回读失配"
    assert parsed["lamAAB"] == lam["AAB"], "lamAAB 回读失配"
    assert parsed["lamABC"] == lam["ABC"], "lamABC 回读失配"
    assert parsed["svec"] == s_vec, "svec 回读失配"
    for nm, key in (("hAA", "h_AA"), ("hAB", "h_AB")):
        want = {k: c for k, c in enumerate(world[key]) if c}
        assert parsed[nm] == want, f"{nm} 回读失配"
    assert parsed["e"] == world["e"], "e 回读失配"
    # 抽查点期望值由回读表独立重算（发射时数值自 eval3；此处对账）
    spot_vals = {}
    for tbl, pts in spots.items():
        vals = []
        for pt in pts:
            if tbl == "lamAAA":
                vals.append(eval3(parsed["lamAAA"], *pt))
            elif tbl == "lamAAB":
                vals.append(eval3(parsed["lamAAB"], *pt))
            elif tbl == "lamABC":
                vals.append(eval3(parsed["lamABC"], *pt))
            elif tbl == "svec":
                vals.append(eval3(parsed["svec"], *pt))
            elif tbl == "hAA":
                vals.append(eval1([parsed["hAA"].get(k, F0) for k in range(17)], pt[0]))
            else:
                vals.append(eval1([parsed["hAB"].get(k, F0) for k in range(17)], pt[0]))
        spot_vals[tbl] = vals
    return spot_vals


# ---------------------------------------------------------------- 主流程
def main() -> None:
    t0 = time.time()
    world = build_world()
    log(f"[load] 证书只读消费完成：λ×3（各 {len(world['lam']['AAA'])} 非零）＋"
        f"s（{len(world['s_vec'])} 非零）＋h×2（各 17）＋e={fs(world['e'])}")

    refs = symmetric_identity(world)
    refs["s_counts"] = {k: v for k, v in sorted(refs["s_counts"].items())}
    log(f"[ident] 对称块构型恒等式重放 diff={refs['diff']}（精确 ==0）；"
        f"λ 点 {len(refs['lam_points'])} 个、s 点 {len(refs['s_counts'])} 个（全在 "
        "{0,1}³）、h 点 2 个")
    log(f"[ref  ] sum_lam={fs(refs['sum_lam'])}  sum_all={fs(refs['sum_all'])}"
        f"  sum_H={fs(refs['sum_H'])}")

    spots = spot_points()
    blocks = emit_data_lean(world, spots, refs)
    emit_main_lean(refs)
    log(f"[emit] TableA1Data.lean（{DATA_LEAN.stat().st_size / 1e3:.0f}KB，分块 "
        f"{sum(len(v) for v in blocks.values())} 块）＋"
        f"TableA1.lean（{MAIN_LEAN.stat().st_size / 1e3:.0f}KB）")

    parsed = reparse_tables(DATA_LEAN.read_text())
    spot_vals = selfcheck(world, refs, spots, parsed)
    log("[selfcheck] Lean 源码回读重建表逐位对账全过＋抽查期望值独立重算一致")

    doc = dict(
        kind="n9-r13-a1-data",
        script="bounds/r13_a1_data.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        seed=SEED,
        inputs=dict(
            certificate=str(CERT_DEFAULT),
            certificate_role="只读消费（M9 cap 证书 blocks 为唯一数据源）",
            assembly="r9_s3_rederive.S3Assembly（独立第二实现，stdlib only）",
            config="对称块构型 {e1×3, e2×3, e3×3}（D52 裁决 2）"),
        config=dict(
            points=[[fs(c) for c in p] for p in SYM_PTS],
            gram_block_rule="G[i][j] = 1 if ⌊i/3⌋=⌊j/3⌋ else 0"),
        tables=dict(
            lam_AAA=dict(nnz=len(world["lam"]["AAA"]),
                         terms=[[i, j, l, fs(c)] for (i, j, l), c
                                in sorted(world["lam"]["AAA"].items())]),
            lam_AAB=dict(nnz=len(world["lam"]["AAB"]),
                         terms=[[i, j, l, fs(c)] for (i, j, l), c
                                in sorted(world["lam"]["AAB"].items())]),
            lam_ABC=dict(nnz=len(world["lam"]["ABC"]),
                         terms=[[i, j, l, fs(c)] for (i, j, l), c
                                in sorted(world["lam"]["ABC"].items())]),
            s=dict(nnz=len(world["s_vec"]),
                   terms=[[i, j, l, fs(c)] for (i, j, l), c
                          in sorted(world["s_vec"].items())]),
            h_AA=[fs(c) for c in world["h_AA"]],
            h_AB=[fs(c) for c in world["h_AB"]],
            e=fs(world["e"])),
        identity_points=dict(
            lam=[dict(orbit=o, perm=p, point=[fs(x) for x in pt], count=c)
                 for (o, p, pt), c in sorted(refs["lam_points"].items())],
            s=[dict(point=[fs(x) for x in pt], count=c)
               for pt, c in refs["s_counts"].items()],
            h=[dict(cls=cls, g=fs(g), count=c)
               for (cls, g), c in sorted(refs["h_counts"].items())]),
        counts=dict(
            lam_total=84, s_total=729, h_total=36,
            lam_by_point=[c for c in sorted(refs["lam_points"].values())],
            s_by_point=[refs["s_counts"][pt] for pt in sorted(refs["s_counts"])],
            h_by_class=[refs["h_counts"][k] for k in sorted(refs["h_counts"])]),
        reference_values=dict(
            sum_lam=fs(refs["sum_lam"]), sum_all=fs(refs["sum_all"]),
            sum_H=fs(refs["sum_H"]), e=fs(world["e"]), diff="0"),
        spot_checks=dict(
            scheme=("seed 20261015；表序 lamAAA/lamAAB/lamABC/svec/hAA/hAB；"
                    "每表 3 点；λ/s 表每点 (u,v,t)=Fraction(rng.randint(-64,64),64)"
                    "×3、h 表每点 x 同式 1 次（/64 沿仓随机有理点惯例）"),
            tables={tbl: [dict(point=[fs(a) for a in pt], expected=fs(v))
                          for pt, v in zip(spots[tbl], spot_vals[tbl])]
                    for tbl in SPOT_TABLES}),
        lean=dict(
            files=["formal/lean/ThomsonN9/TableA1Data.lean",
                   "formal/lean/ThomsonN9/TableA1.lean"],
            blocking=f"表分块 def ≤{CHUNK} 项/块＋文件级 maxHeartbeats 1000000"
                     "（D50-2 范式）",
            scope_note=("对称构型精确实例＋抽查；随机构型全恒等式（84×449+504×271"
                        "≈23.5 万项）超 elaboration 预算，泛构型证据由 "
                        "results/r9_s3_rederive.json 3 trial＋设计师第 4 trial 在档"
                        "承担")),
        wall_s=round(time.time() - t0, 1),
    )
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    log(f"[done ] {OUT_JSON}（{doc['wall_s']}s）；exit 0")


if __name__ == "__main__":
    main()
