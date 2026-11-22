#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r21_b5chain_data.py — R21B 表 B 第八件（链装配/节点辨识形式件）Lean
数据锚定件发射器。

【任务定位（r21b-chain-lean，D90 裁决 1／D92 裁决 1）】表 B 第八件
TableB5Chain.lean 的数据件 TableB5ChainData.lean 发射（r13_a1_data.py／
r15_b1_data.py 先例）：

  (i)  15 对 ν 容器间隙精确 ℚ 下界 def（g01..g45，node 指标 a<b 0 基；
       自 TableB1Data.lean 12 容器端点 def 源直读零手抄——regex 与
       r20_seam_probe/r21_chain_gate 门内第二实现不同字面）＋逐对
       norm_num 端点恒等定理（gXX_eq : gXX = nu_bLo − nu_aHi）；
  (ii) gMin＝15 对间隙之 min（精确 ℚ 字面＋min 树 norm_num 恒等定理）；
  (iii) r_ball = 950125/10⁸（l6_intube quadraticGrowth.rigorousRadius
       精确十进制；== r* == R_MAX/16，R21A G3 箱定律亲证口径）；
  (iv) sqrt2Up／dmaxUp／tUp——√2／√deltaMax／√(3·sqrt72Up) 的 200-bit
       整数 Newton 有理上包（r20_seam_probe.py sqrt_rat **同配方逐位
       复现**——门 G5 以 CBhi/CAhi 与 r20_l5l6_seam.json supply 精确
       Fraction 逐位对账为牙）；CBhi＝k1·dmaxUp＋tUp（k1 :=
       s1Up·u₁·sqrt72Up/l₃²）、CAhi＝(s1Up·u₁/l₃²＋2·sqrt2Up/s3Dn)·
       sqrt72Up、deltaA＝(l₃/24)/sqrt72Up（精确 Fraction）；
  (v)  rhoNeedB＝min(gMin/2, (r_ball/CBhi)²)、rhoNeedA＝min(gMin/2,
       r_ball/CAhi)——链装配推论的复合阈值 def（seam_cor_B/A 喂入
       契约）；域面 norm_num 定理六件（thresh*_lt_gMin_half、
       threshA_le_deltaA、gMin_half_le_deltaMax、deltaA_le_deltaMax、
       2·u₁·sqrt72Up·deltaMax ≤ l₃²——hdom1 内部导出用）。

【交叉对账（发射器 require 面，任一不符即 FAIL 不出件）】
  * CBhi == r20_l5l6_seam.json supply.C_B.hi.exact（逐位）；
  * CAhi == supply.C_A.delta_caliber.exact（逐位）；
  * deltaA == supply.C_A.delta_A.exact（逐位）；
  * (r_ball/CBhi)² == seam_table r_star_raw/B_global_hoelder 行
    threshold.exact（逐位——r_ball==r* 口径行）；
  * r_ball/CAhi == seam_table r_star_raw/A_narrow_linear 行
    threshold.exact（逐位）；
  * gMin ≤ 2·half_gap（tube.json /ttp_spectrum/half_gap=
    0.01850609934999997 十进制精确化；float_advisory 锚——容器包络宽
    ~1e-6 级、间隙 0.037 级，定向宽安全边 0 ≤ 2·half_gap−gMin ≤ 1e-5；
    verdict.need 同数交叉锚）；
  * 12 容器端点五链不交复验（nu1Hi<nu2Lo<… 链式）＋gMin>0。

【产出】
  * numerics/bounds/results/r21_b5chain_data.json —— 全部精确值/对账记录/
    provenance（输入 sha256；零 timestamp/wall_s/code_version——G2 逐位
    复放面）；
  * formal/lean/ThomsonN9/TableB5ChainData.lean —— 数据件（无时间戳，
    字节可复放）。

【自检】出数全程 Fraction 精确；发射后回读 Lean 源重建 15 间隙＋gMin
＋CBhi/CAhi 与源表逐位对账（发射器自校验，r13_a1 先例）。

用法（CWD 无关）：
  python3 numerics/bounds/r21_b5chain_data.py [--out-dir DIR]
  # 幂等：json/Lean 文件按数学内容确定性生成（均无时间戳，字节可复放）。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]
B1DATA = REPO / "formal" / "lean" / "ThomsonN9" / "TableB1Data.lean"
B5DATA = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Data.lean"
R20_JSON = RESULTS / "r20_l5l6_seam.json"
TUBE_JSON = RESULTS / "tube.json"
OUT_JSON = RESULTS / "r21_b5chain_data.json"
OUT_LEAN = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5ChainData.lean"

SEED = 20261021
SQ_BITS = 200                      # 有理平方根包精度（r20_seam_probe 同参）

NU_NAMES = ("nu1Lo", "nu1Hi", "nu2Lo", "nu2Hi", "nu3Lo", "nu3Hi",
            "nu4Lo", "nu4Hi", "nu5Lo", "nu5Hi", "nu6Lo", "nu6Hi")
# 15 对 (a,b, lo_b, hi_a)：node 指标 0 基（ν_{a+1}），a<b；间隙=容器 b 下端−容器 a 上端。
PAIRS = [
    (0, 1, "nu2Lo", "nu1Hi"), (0, 2, "nu3Lo", "nu1Hi"), (0, 3, "nu4Lo", "nu1Hi"),
    (0, 4, "nu5Lo", "nu1Hi"), (0, 5, "nu6Lo", "nu1Hi"),
    (1, 2, "nu3Lo", "nu2Hi"), (1, 3, "nu4Lo", "nu2Hi"), (1, 4, "nu5Lo", "nu2Hi"),
    (1, 5, "nu6Lo", "nu2Hi"),
    (2, 3, "nu4Lo", "nu3Hi"), (2, 4, "nu5Lo", "nu3Hi"), (2, 5, "nu6Lo", "nu3Hi"),
    (3, 4, "nu5Lo", "nu4Hi"), (3, 5, "nu6Lo", "nu4Hi"),
    (4, 5, "nu6Lo", "nu5Hi"),
]


def log(msg: str) -> None:
    print(f"[r21bdata] {msg}", flush=True)


def fail(msg: str) -> None:
    raise SystemExit(f"[r21bdata][FAIL] {msg}")


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


def sqrt_rat(q: Fr, side: str) -> Fr:
    """√q 有理包（r20_seam_probe.sqrt_rat **同配方逐位**：上界
    isqrt(⌊q·2^{2p}⌋+1)+1、下界 isqrt(⌊q·2^{2p}⌋)——r20 C_B.hi 逐位
    复现的关键；r21_chain_gate 门内第二实现 sqrt_env 是异构字面，紧公差
    对账——双实现并存是设计面）。"""
    p = SQ_BITS
    num, den = q.numerator, q.denominator
    if side == "lo":
        return Fr(math.isqrt((num << (2 * p)) // den), 1 << p)
    return Fr(math.isqrt((num << (2 * p)) // den + 1) + 1, 1 << p)


def parse_defs(src: str) -> dict:
    return dict(re.findall(r"^def\s+(\w+)\s*:\s*ℚ\s*:=\s*(\S+)", src, re.M))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=None,
                    help="重跑复放目录（G2 面）；缺省写仓库位")
    args = ap.parse_args()
    out_json = OUT_JSON if args.out_dir is None else Path(args.out_dir) / OUT_JSON.name
    out_lean = OUT_LEAN if args.out_dir is None else Path(args.out_dir) / OUT_LEAN.name
    if args.out_dir is not None:
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_lean.parent.mkdir(parents=True, exist_ok=True)

    b1_src = B1DATA.read_text()
    b5_src = B5DATA.read_text()
    d1 = parse_defs(b1_src)
    d5 = parse_defs(b5_src)
    for nm in ("zLo", "zHi") + NU_NAMES:
        if nm not in d1:
            fail(f"TableB1Data.lean 缺 def {nm}")
    for nm in ("l3", "u1", "s1Up", "s3Dn", "sqrt72Up", "deltaMax"):
        if nm not in d5:
            fail(f"TableB5Data.lean 缺 def {nm}")
    nu = {nm: Fr(d1[nm]) for nm in NU_NAMES}
    l3, u1 = Fr(d5["l3"]), Fr(d5["u1"])
    s1Up, s3Dn, sqrt72Up = Fr(d5["s1Up"]), Fr(d5["s3Dn"]), Fr(d5["sqrt72Up"])
    deltaMax = Fr(d5["deltaMax"])

    # ---- 五链不交复验（容器链序）＋正性
    require = fail
    for lo, hi in (("nu1Hi", "nu2Lo"), ("nu2Hi", "nu3Lo"), ("nu3Hi", "nu4Lo"),
                   ("nu4Hi", "nu5Lo"), ("nu5Hi", "nu6Lo")):
        if not (nu[lo] < nu[hi]):
            require(f"容器五链不交破损：{lo} !< {hi}")

    # ---- 15 对间隙＋gMin
    gaps = {}
    gname = {}
    for a, b, lo, hi in PAIRS:
        nm = f"g{a}{b}"
        gname[(a, b)] = nm
        gaps[nm] = (nu[lo], nu[hi], nu[lo] - nu[hi])
        if gaps[nm][2] <= 0:
            fail(f"间隙 {nm} ≤ 0（{float(gaps[nm][2])}）")
    gmin_val = min(v[2] for v in gaps.values())
    gmin_name = [k for k, v in gaps.items() if v[2] == gmin_val][0]
    log(f"15 间隙就绪；gMin = {gmin_name} = {float(gmin_val):.12f}")

    # ---- 包络与常数（r20 同配方逐位）
    k1 = s1Up * u1 * sqrt72Up / (l3 * l3)
    dmaxUp = sqrt_rat(deltaMax, "hi")
    tUp = sqrt_rat(3 * sqrt72Up, "hi")
    CBhi = k1 * dmaxUp + tUp
    sqrt2Up = sqrt_rat(Fr(2), "hi")
    CAhi = sqrt72Up * (s1Up * u1 / (l3 * l3) + 2 * sqrt2Up / s3Dn)
    deltaA = (l3 / 24) / sqrt72Up
    if not (deltaMax <= dmaxUp * dmaxUp):
        fail("√deltaMax 上包方向破损")
    if not (3 * sqrt72Up <= tUp * tUp):
        fail("√(3√72Up) 上包方向破损")
    if not (2 <= sqrt2Up * sqrt2Up):
        fail("√2 上包方向破损")

    # ---- r20 位对账（require 面）
    r20 = json.loads(R20_JSON.read_text())
    sup = r20["supply"]
    if Fr(sup["C_B"]["hi"]["exact"]) != CBhi:
        fail("CBhi ≠ r20 supply.C_B.hi.exact（逐位）")
    if Fr(sup["C_A"]["delta_caliber"]["exact"]) != CAhi:
        fail("CAhi ≠ r20 supply.C_A.delta_caliber.exact（逐位）")
    if Fr(sup["C_A"]["delta_A"]["exact"]) != deltaA:
        fail("deltaA ≠ r20 supply.C_A.delta_A.exact（逐位）")
    if Fr(sup["deltaMax"]["exact"]) != deltaMax:
        fail("deltaMax ≠ r20 supply（逐位）")
    rows = {(r["route"], r["target"]): r for r in r20["seam_table"]}
    rball = Fr(950125, 10 ** 8)
    threshB = (rball / CBhi) ** 2
    threshA = rball / CAhi
    if Fr(rows[("B_global_hoelder", "r_star_raw")]["threshold"]["exact"]) != threshB:
        fail("(r_ball/CBhi)² ≠ r20 r_star_raw/B 行 threshold.exact（逐位）")
    if Fr(rows[("A_narrow_linear", "r_star_raw")]["threshold"]["exact"]) != threshA:
        fail("r_ball/CAhi ≠ r20 r_star_raw/A 行 threshold.exact（逐位）")
    log("r20 位对账四件全中（CBhi/CAhi/deltaA＋r* 口径 B/A 阈值逐位）")

    # ---- tube.json half_gap 交叉对账（float_advisory 宽安全边定向）
    tube_src = TUBE_JSON.read_text()
    m = re.search(r'"half_gap"\s*:\s*([0-9.eE+-]+)', tube_src)
    if not m:
        fail("tube.json 缺 /ttp_spectrum/half_gap")
    half_gap_dec = Fr(m.group(1))          # 十进制字面精确化
    need_dec = None
    m2 = re.search(r'"need"\s*:\s*([0-9.eE+-]+)', tube_src)
    if m2:
        need_dec = Fr(m2.group(1))
    slack = 2 * half_gap_dec - gmin_val
    if not (Fr(0) <= slack <= Fr(1, 10 ** 5)):
        fail(f"half_gap 定向宽安全边失守：2·half_gap−gMin={float(slack):.3e}"
             "（应 ∈ [0, 1e-5]；容器包络宽 ~1e-6 级、间隙 0.037 级）")
    if need_dec is not None and need_dec != half_gap_dec:
        fail("tube.json verdict.need ≠ half_gap（同数交叉锚破损）")
    log(f"half_gap 交叉对账：2·half_gap−gMin = {float(slack):.3e} ∈ [0,1e-5] "
        "（float_advisory 定向宽安全边）")

    # ---- 复合阈值＋域面
    rhoNeedB = min(gmin_val / 2, threshB)
    rhoNeedA = min(gmin_val / 2, threshA)
    domain = {
        "threshB_lt_gMin_half": threshB < gmin_val / 2,
        "threshA_lt_gMin_half": threshA < gmin_val / 2,
        "threshA_le_deltaA": threshA <= deltaA,
        "gMin_half_le_deltaMax": gmin_val / 2 <= deltaMax,
        "deltaA_le_deltaMax": deltaA <= deltaMax,
        "two_u1_sqrt72Up_deltaMax_le_l3sq": 2 * u1 * sqrt72Up * deltaMax <= l3 * l3,
        "rhoNeedB_eq_threshB": rhoNeedB == threshB,
        "rhoNeedA_eq_threshA": rhoNeedA == threshA,
    }
    for k, v in domain.items():
        if not v:
            fail(f"域面失守：{k}")

    # ---- 发射 Lean 数据件（确定性，零时间戳）
    def lit(q: Fr) -> str:
        return fs(q)

    gap_defs = []
    gap_thms = []
    ends = {(a, b): (lo, hi) for a, b, lo, hi in PAIRS}
    for (a, b), nm in sorted(gname.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        lo, hi, val = gaps[nm]
        lo_nm, hi_nm = ends[(a, b)]
        gap_defs.append(f"/-- {nm}：ν_{a+1}–ν_{b+1} 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/")
        gap_defs.append(f"def {nm} : ℚ := {lit(val)}")
        gap_thms.append(
            f"/-- {nm} 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/")
        gap_thms.append(
            f"theorem {nm}_eq : {nm} = {lo_nm} - {hi_nm} := by "
            f"norm_num [{nm}, {lo_nm}, {hi_nm}]")
    gmin_lit = lit(gmin_val)
    min_tree = "g01"
    for nm in ("g02", "g03", "g04", "g05", "g12", "g13", "g14", "g15",
               "g23", "g24", "g25", "g34", "g35", "g45"):
        min_tree = f"min ({min_tree}) ({nm})"
    all_g = ", ".join(["g01", "g02", "g03", "g04", "g05", "g12", "g13", "g14",
                       "g15", "g23", "g24", "g25", "g34", "g35", "g45"])

    lean = f"""import Mathlib
import ThomsonN9.TableB1Data
import ThomsonN9.TableB5Data

/-!
# Table B5Chain data (R21B / r21b): the exact rational constants of the
# chain-assembly / node-identification piece

This module is deliberately self-contained: it imports only `Mathlib`,
`ThomsonN9.TableB1Data` and `ThomsonN9.TableB5Data` (both frozen,
read-only), imports no in-repo solution module, and is imported only by
`ThomsonN9/TableB5Chain.lean`.  It materialises, as explicit `ℚ`
literals, the data layer of the L2→L3→L5→L6 chain assembly
(`notes/l5l6-seam.md` §3 δ=ρ seam identification; emitter
`numerics/bounds/r21_b5chain_data.py`, seed {SEED}, heavy_solves=0;
provenance = sha256 of TableB1Data.lean / TableB5Data.lean /
r20_l5l6_seam.json / tube.json, recorded in
`results/r21_b5chain_data.json`):

* `g01..g45` — the 15 pairwise ν-container gap lower bounds (exact ℚ;
  container b lower end − container a upper end, from the TableB1Data
  container endpoints bit for bit, one `norm_num` identity theorem
  each);
* `gMin` — the minimum of the 15 gaps (exact ℚ; the
  identification-window constant: ρ < gMin/2 makes the node
  identification unique, `ident_unique` in TableB5Chain);
* `r_ball` — the L6 certified ball radius 950125/10⁸
  (= r* = l6_intube quadraticGrowth.rigorousRadius exact decimal);
* `sqrt2Up`/`dmaxUp`/`tUp` — 200-bit integer-Newton rational upper
  envelopes of √2 / √deltaMax / √(3·sqrt72Up) (same recipe as
  `r20_seam_probe.sqrt_rat`, reproduced bit for bit — `CBhi`/`CAhi` are
  cross-checked against `r20_l5l6_seam.json` supply exact Fractions);
* `CBhi` = k1·dmaxUp + tUp (route-B C_B envelope, k1 := s1Up·u₁·sqrt72Up/l₃²),
  `CAhi` = (s1Up·u₁/l₃² + 2·sqrt2Up/s3Dn)·sqrt72Up (route-A δ-caliber
  envelope), `deltaA` = (l₃/24)/sqrt72Up (route-A narrow domain);
* `rhoNeedB`/`rhoNeedA` — the seam corollary composite thresholds
  min(gMin/2, ball-gate threshold), with the six domain-face `norm_num`
  theorems.

Honest scope note (B5Chain-data boundary, D92): the identification /
conversion / assembly theorems live in `TableB5Chain.lean`; this file
is the data layer only.  The half_gap cross-check (tube.json
float_advisory decimal anchor 0.01850609934999997) is a gate-face duty,
recorded in `r21_b5chain_data.json` (directed wide-margin assertion
0 ≤ 2·half_gap − gMin ≤ 1e-5).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5ChainData

open ThomsonN9.TableB1Data
open ThomsonN9.TableB5Data

/-! ### 15 对 ν 容器间隙（node 指标 0 基：ν_(a+1)；间隙＝容器 b 下端−容器 a 上端） -/
{chr(10).join(gap_defs)}

/-! ### 端点恒等（ℚ norm_num，逐位） -/
{chr(10).join(gap_thms)}

/-! ### 辨识窗常数 gMin（15 对间隙之 min） -/
/-- gMin：15 对容器间隙下界之 min（精确 ℚ；辨识窗＝gMin/2）。 -/
def gMin : ℚ := {gmin_lit}
/-- gMin 的 min 树恒等（15 项嵌套 min，norm_num 逐位）。 -/
theorem gMin_eq : gMin = {min_tree} := by norm_num [gMin, {all_g}]
/-- gMin > 0（间隙非退化）。 -/
theorem gMin_pos : (0:ℚ) < gMin := by norm_num [gMin]

/-! ### L6 球半径 r_ball（== r* == 950125/10⁸） -/
/-- r_ball：L6 认证球半径＝r*＝950125/10⁸（l6_intube rigorousRadius 精确
十进制；== R_MAX/16，R21A G3 箱定律口径）。 -/
def r_ball : ℚ := 950125/100000000
/-- r_ball > 0。 -/
theorem r_ball_pos : (0:ℚ) < r_ball := by norm_num [r_ball]

/-! ### 平方根上包三件（200-bit Newton；r20 sqrt_rat 同配方逐位） -/
/-- √2 的 200-bit 有理上包。 -/
def sqrt2Up : ℚ := {lit(sqrt2Up)}
/-- sqrt2Up² ≥ 2。 -/
theorem sqrt2Up_sq_ge : (2:ℚ) ≤ sqrt2Up^2 := by norm_num [sqrt2Up]
/-- sqrt2Up > 0。 -/
theorem sqrt2Up_pos : (0:ℚ) < sqrt2Up := by norm_num [sqrt2Up]
/-- √deltaMax 的 200-bit 有理上包。 -/
def dmaxUp : ℚ := {lit(dmaxUp)}
/-- dmaxUp² ≥ deltaMax。 -/
theorem dmaxUp_sq_ge : deltaMax ≤ dmaxUp^2 := by
  norm_num [dmaxUp, deltaMax]
/-- dmaxUp > 0。 -/
theorem dmaxUp_pos : (0:ℚ) < dmaxUp := by norm_num [dmaxUp]
/-- √(3·sqrt72Up) 的 200-bit 有理上包。 -/
def tUp : ℚ := {lit(tUp)}
/-- tUp² ≥ 3·sqrt72Up。 -/
theorem tUp_sq_ge : 3*sqrt72Up ≤ tUp^2 := by
  norm_num [tUp, sqrt72Up]
/-- tUp > 0。 -/
theorem tUp_pos : (0:ℚ) < tUp := by norm_num [tUp]

/-! ### C_B／C_A 包络与窄域（精确 Fraction 装配） -/
/-- CBhi：路线 B 常数包＝k1·dmaxUp＋tUp（k1 := s1Up·u₁·sqrt72Up/l₃²）；
与 r20_l5l6_seam.json supply.C_B.hi 精确 Fraction 逐位一致（发射器
require 面＋门 G5 双查）。 -/
def CBhi : ℚ := {lit(CBhi)}
/-- CBhi 装配恒等。 -/
theorem CBhi_eq : CBhi = s1Up * u1
    * sqrt72Up / (l3 * l3)
    * dmaxUp + tUp := by
  norm_num [CBhi, s1Up, u1,
    sqrt72Up, l3, dmaxUp, tUp]
/-- CBhi > 0。 -/
theorem CBhi_pos : (0:ℚ) < CBhi := by norm_num [CBhi]
/-- CAhi：路线 A δ 口径常数包＝(s1Up·u₁/l₃²＋2·sqrt2Up/s3Dn)·sqrt72Up；
与 r20 supply.C_A.delta_caliber 精确 Fraction 逐位一致。 -/
def CAhi : ℚ := {lit(CAhi)}
/-- CAhi 装配恒等。 -/
theorem CAhi_eq : CAhi = (s1Up * u1
    / (l3 * l3)
    + 2 * sqrt2Up / s3Dn) * sqrt72Up := by
  norm_num [CAhi, s1Up, u1,
    sqrt72Up, s3Dn, sqrt2Up,
    l3]
/-- CAhi > 0。 -/
theorem CAhi_pos : (0:ℚ) < CAhi := by norm_num [CAhi]
/-- deltaA：路线 A 窄域半径＝(l₃/24)/sqrt72Up（精确 Fraction；与 r20
supply.C_A.delta_A 逐位一致）。 -/
def deltaA : ℚ := (l3 / 24) / sqrt72Up
/-- deltaA > 0。 -/
theorem deltaA_pos : (0:ℚ) < deltaA := by
  norm_num [deltaA, l3, sqrt72Up]

/-! ### 复合阈值（seam 推论 ρ_need） -/
/-- rhoNeedB：√δ 档复合阈值＝min(gMin/2, (r_ball/CBhi)²)（min 取球门支
——域面定理在库）。 -/
def rhoNeedB : ℚ := min (gMin/2) ((r_ball/CBhi)^2)
/-- rhoNeedA：窄域线性档复合阈值＝min(gMin/2, r_ball/CAhi)。 -/
def rhoNeedA : ℚ := min (gMin/2) (r_ball/CAhi)

/-! ### 域面六件（norm_num 精确） -/
/-- 球门阈值（B 档）＜辨识窗。 -/
theorem threshB_lt_gMin_half : (r_ball/CBhi)^2 < gMin/2 := by
  norm_num [r_ball, CBhi, gMin]
/-- 球门阈值（A 档）＜辨识窗。 -/
theorem threshA_lt_gMin_half : r_ball/CAhi < gMin/2 := by
  norm_num [r_ball, CAhi, gMin]
/-- 球门阈值（A 档）≤ 路线 A 窄域半径（δ_A 域检查）。 -/
theorem threshA_le_deltaA : r_ball/CAhi ≤ deltaA := by
  norm_num [r_ball, CAhi, deltaA, l3,
    sqrt72Up]
/-- 辨识窗半宽 ≤ deltaMax（路线 B 域检查：ρ<gMin/2 ⟹ ρ≤deltaMax）。 -/
theorem gMin_half_le_deltaMax : gMin/2 ≤ deltaMax := by
  norm_num [gMin, deltaMax]
/-- deltaA ≤ deltaMax（窄域 ⊆ 记录域）。 -/
theorem deltaA_le_deltaMax : deltaA ≤ deltaMax := by
  norm_num [deltaA, l3, sqrt72Up,
    deltaMax]
/-- 2·u₁·sqrt72Up·deltaMax ≤ l₃²（路线 A hdom1 内部导出的记录域端事实）。 -/
theorem two_u1_sqrt72Up_deltaMax_le_l3sq :
    2 * u1 * sqrt72Up
      * deltaMax ≤ l3 * l3 := by
  norm_num [u1, sqrt72Up,
    deltaMax, l3]

end ThomsonN9.TableB5ChainData
"""
    out_lean.write_text(lean)
    log(f"Lean 数据件发射：{out_lean}（{len(lean)} 字节）")

    # ---- 发射后回读自校验（r13_a1 先例）
    rd = parse_defs(out_lean.read_text())
    for nm, (lo, hi, val) in gaps.items():
        if Fr(rd[nm]) != val:
            fail(f"回读失配：{nm}")
    if Fr(rd["gMin"]) != gmin_val:
        fail("回读失配：gMin")
    if Fr(rd["CBhi"]) != CBhi or Fr(rd["CAhi"]) != CAhi:
        fail("回读失配：CBhi/CAhi")
    # rhoNeedB/rhoNeedA 系 min 表达式 def（非字面）——值面由阈值/域面定理
    # 与门 G5 承担，回读只查字面 def。
    log("回读自校验全过（15 间隙＋gMin＋CBhi/CAhi；rhoNeed* 系表达式 def "
        "不在字面回读面）")

    # ---- JSON（确定性：零 timestamp/wall_s/code_version）
    doc = {
        "kind": "n9-r21-b5chain-data",
        "task": "r21b-chain-lean",
        "seed": SEED,
        "heavy_solves": 0,
        "schema": {
            "artifact_class": "lean_data_emitter_audit",
            "note": "数据件发射器审计记录；不入 endgame.json/citedCertificates/"
                    "12 分区、不作 endgame_chain.py 输入（R11C–R21 先例）",
            "sqrt_recipe": "r20_seam_probe.sqrt_rat 同配方逐位（200-bit 整数 "
                           "Newton；r21_chain_gate 门内 sqrt_env 系异构第二实现，"
                           "紧公差对账）",
        },
        "gaps": {nm: {"exact": fs(v[2]), "float": float(v[2]),
                      "lo_end": fs(v[0]), "hi_end": fs(v[1])}
                 for nm, v in sorted(gaps.items())},
        "gMin": {"exact": fs(gmin_val), "float": float(gmin_val),
                 "attained_by": f"g{gmin_name[0]}{gmin_name[1]}"},
        "r_ball": {"exact": fs(rball), "float": float(rball),
                   "provenance": "l6_intube quadraticGrowth.rigorousRadius "
                                 "精确十进制 0.00950125 == R_MAX/16（R21A G3）"},
        "envelopes": {
            "k1": {"exact": fs(k1), "float": float(k1)},
            "sqrt2Up": {"exact": fs(sqrt2Up), "float": float(sqrt2Up)},
            "dmaxUp": {"exact": fs(dmaxUp), "float": float(dmaxUp)},
            "tUp": {"exact": fs(tUp), "float": float(tUp)},
            "CBhi": {"exact": fs(CBhi), "float": float(CBhi),
                     "r20_bit_equal": True},
            "CAhi": {"exact": fs(CAhi), "float": float(CAhi),
                     "r20_bit_equal": True},
            "deltaA": {"exact": fs(deltaA), "float": float(deltaA),
                       "r20_bit_equal": True},
        },
        "thresholds": {
            "threshB": {"exact": fs(threshB), "float": float(threshB),
                        "form": "(r_ball/CBhi)^2",
                        "r20_row": "seam_table r_star_raw/B_global_hoelder "
                                   "threshold.exact 逐位一致"},
            "threshA": {"exact": fs(threshA), "float": float(threshA),
                        "form": "r_ball/CAhi",
                        "r20_row": "seam_table r_star_raw/A_narrow_linear "
                                   "threshold.exact 逐位一致"},
            "rhoNeedB": {"exact": fs(rhoNeedB), "float": float(rhoNeedB)},
            "rhoNeedA": {"exact": fs(rhoNeedA), "float": float(rhoNeedA)},
        },
        "cross_checks": {
            "cbhi_r20_bit_equal": True,
            "cahi_r20_bit_equal": True,
            "deltaA_r20_bit_equal": True,
            "threshB_r20_bit_equal": True,
            "threshA_r20_bit_equal": True,
            "half_gap": {
                "decimal": fs(half_gap_dec),
                "float_advisory": float(half_gap_dec),
                "tube_json_path": "/ttp_spectrum/half_gap",
                "need_same_number": need_dec is not None and need_dec == half_gap_dec,
                "tier": "float_advisory",
                "note": "容器包络宽 ~1e-6 级（ν₁/ν₄/ν₅ 系 z² 包端点精确式——宽来自 "
                        "z 盒非点；ν₂/ν₆ 200-bit Newton 包宽 ~1e-60）、间隙 0.037 级",
                "directed_wide_margin": {
                    "form": "0 ≤ 2·half_gap − gMin ≤ 1e-5",
                    "value": fs(slack), "float": float(slack), "pass": True,
                },
            },
            "domain_faces": {k: bool(v) for k, v in domain.items()},
        },
        "provenance": {
            "read_only": True,
            "inputs": {
                "formal/lean/ThomsonN9/TableB1Data.lean": {"sha256": sha256_of(B1DATA)},
                "formal/lean/ThomsonN9/TableB5Data.lean": {"sha256": sha256_of(B5DATA)},
                "numerics/bounds/results/r20_l5l6_seam.json": {"sha256": sha256_of(R20_JSON)},
                "numerics/bounds/results/tube.json": {"sha256": sha256_of(TUBE_JSON)},
            },
            "frozen_anchors": {
                "endgame_json_sha256": "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f",
                "tableb5uncond_sha256": "c79fc6231d1e13b8ffd7873d1338901602ed3b70b3f057ed4eec4eb757e36d5e",
                "tableb5polar_sha256": "d8c58f7d2c56c39fbe1ae62d634fc6ea5bd585fa9f1c0b9c2e2fc909d4338516",
            },
        },
    }
    out_json.write_text(json.dumps(doc, ensure_ascii=False, indent=1,
                                   sort_keys=True) + "\n")
    log(f"JSON 发射：{out_json}（{out_json.stat().st_size} 字节）")
    log("PASS（heavySolves=0；零求解零 SDP）")


if __name__ == "__main__":
    main()
