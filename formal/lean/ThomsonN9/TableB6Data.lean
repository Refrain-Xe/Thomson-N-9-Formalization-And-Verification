import Mathlib
/-!
# Table B6 data (R15 / r15a): the splice endpoints and record
# anchors of the 12-piece endgame partition

This module is deliberately self-contained: it imports only `Mathlib`,
imports no in-repo solution module, and is imported only by
`ThomsonN9/TableB6.lean`.  It materialises, as explicit `ℚ` literals,
the arithmetic layer of the endgame splice record
(`numerics/bounds/results/endgame.json`, read-only, re-derived here
through the independent second implementation of
`numerics/bounds/r15_b6_data.py`: stdlib-Fraction parsing of the
12 partition regions (13 endpoints, 12 bounds, coverPiece semantics),
the reference energy E* and the assembled record; provenance = sha256
of endgame.json, recorded in `results/r15_b6_data.json` — the partition
constants are exact Fractions, so there is no dyadic rounding surface
here):

* `e0` … `e12` — the 13 splice endpoints, a seamless chain
  −1 = e0 ≤ e1 ≤ … ≤ e12 = 1 (12 pairwise `norm_num1` theorems;
  adjacent regions share endpoints bit for bit);
* `b0` … `b11` — the 12 recorded piece bounds, each equal bit for bit
  to the `claimed_bound` of its cited certificate (12/12 bijective
  value reconciliation against `citedCertificates`);
* `estar` — the reference energy E* = 25759986531/10^9 (three-source
  cross-checked advisory value of `thomson-workflow/data/energies.json`,
  NOT a proven optimum; all ≤/> statements below mean «consistent with
  the reference value»);
* `aR` — the assembled record min(12 piece bounds), attained literally
  by the HP piece b10 (the hole interval [−153/200, −187/250]);
* `epsIron` — the iron-rule slack 1e-6.

Proved here (`show`-unfolding + `norm_num1`; `decide` on large ℚ
comparisons does not reduce — v1 lesson, D61-2): the 12 pairwise chain
inequalities; the 12 record bounds `aR ≤ bᵢ` (up to 570-bit Fractions);
the literal identity `b10 = aR`; the iron rule `aR ≤ estar` together
with its strict form `aR < estar` (margin 0.00054… > 0); the piece
semantics — the 10 exclusion pieces obey `estar < bᵢ`, the two
TTP-covering pieces (HP index 10, cap index 11 on [−187/250, 1]) obey
`bᵢ ≤ estar + epsIron`; and three seeded random spot checks of the
minimal-index covering machine (seed 20261017, x on the 2⁻²⁰ grid).

Honest scope note (B6 arithmetic-layer boundary): the certificate
semantics «on region i the energy E ≥ b_i» (the verifyCmd layer of
typed_ladder / hermite / hp / strips / slab certificates listed in
`citedCertificates`) is NOT part of this file — that is the numeric
layer's responsibility; this file proves the arithmetic layer only
(covering / record-min / iron rule / piece semantics), and
`TableB6.lean` builds the genuine covering proof on top.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB6Data

/-- 分区端点 e0（endgame.json partition 第 1 区下端；e0=−1、e12=1，链单调无缝）。 -/
def e0 : ℚ := -1/1

/-- 分区端点 e1（endgame.json partition 第 1 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e1 : ℚ := -99/100

/-- 分区端点 e2（endgame.json partition 第 2 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e2 : ℚ := -97/100

/-- 分区端点 e3（endgame.json partition 第 3 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e3 : ℚ := -19/20

/-- 分区端点 e4（endgame.json partition 第 4 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e4 : ℚ := -91/100

/-- 分区端点 e5（endgame.json partition 第 5 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e5 : ℚ := -9/10

/-- 分区端点 e6（endgame.json partition 第 6 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e6 : ℚ := -22/25

/-- 分区端点 e7（endgame.json partition 第 7 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e7 : ℚ := -17/20

/-- 分区端点 e8（endgame.json partition 第 8 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e8 : ℚ := -41/50

/-- 分区端点 e9（endgame.json partition 第 9 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e9 : ℚ := -79/100

/-- 分区端点 e10（endgame.json partition 第 10 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e10 : ℚ := -153/200

/-- 分区端点 e11（endgame.json partition 第 11 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e11 : ℚ := -187/250

/-- 分区端点 e12（endgame.json partition 第 12 区上端；e0=−1、e12=1，链单调无缝）。 -/
def e12 : ℚ := 1/1

/-- 分区片 0 bound（== citedCertificates claimed_bound 逐位；pieces[0]=exclusion 排除片）。 -/
def b0 : ℚ := 1419245723139071/54975685305550

/-- 分区片 1 bound（== citedCertificates claimed_bound 逐位；pieces[1]=exclusion 排除片）。 -/
def b1 : ℚ := 2837059739445683/109951417862103

/-- 分区片 2 bound（== citedCertificates claimed_bound 逐位；pieces[2]=exclusion 排除片）。 -/
def b2 : ℚ := 95148034377368417075200000000000000000000000000000000000000000000000000/3689382200954663007811329305754478005508846420999294048885656184293211

/-- 分区片 3 bound（== citedCertificates claimed_bound 逐位；pieces[3]=exclusion 排除片）。 -/
def b3 : ℚ := 5667139148427148/219902686859665

/-- 分区片 4 bound（== citedCertificates claimed_bound 逐位；pieces[4]=exclusion 排除片）。 -/
def b4 : ℚ := 56294773645464181900024414062500000000000000000000000000/2184534926853278057997272238274297001333566701245806813

/-- 分区片 5 bound（== citedCertificates claimed_bound 逐位；pieces[5]=exclusion 排除片）。 -/
def b5 : ℚ := 181313976026497009/7036874433292040

/-- 分区片 6 bound（== citedCertificates claimed_bound 逐位；pieces[6]=exclusion 排除片）。 -/
def b6 : ℚ := 3601778876706306785345077514648437500000000000000000000000/139810133547249324624022947987425049230287605836864081701

/-- 分区片 7 bound（== citedCertificates claimed_bound 逐位；pieces[7]=exclusion 排除片）。 -/
def b7 : ℚ := 816392769637139312746570369204224000000000000000000000000000/31691265490905997064799249668440887530527325545844277393403

/-- 分区片 8 bound（== citedCertificates claimed_bound 逐位；pieces[8]=exclusion 排除片）。 -/
def b8 : ℚ := 24566821136999558261408693748961695746402256190776824951171875/953674662606910821016338272521529882970680171880635603760352

/-- 分区片 9 bound（== citedCertificates claimed_bound 逐位；pieces[9]=exclusion 排除片）。 -/
def b9 : ℚ := 152060258133670143773900800000000000000000000000000000000000/5902963308524955309028900129512648637307845623943222995001

/-- 分区片 10 bound（== citedCertificates claimed_bound 逐位；pieces[10]=TTP-covering 片）。 -/
def b10 : ℚ := 47517790735835014335570/1844674407417822803119

/-- 分区片 11 bound（== citedCertificates claimed_bound 逐位；pieces[11]=TTP-covering 片）。 -/
def b11 : ℚ := 22879340185047884591327492399406419521507688973060989923169472604058682918548583984375/888178445822492388747275390557723859303211430452579251742723511769167625620708441526

/-- 参考能量 E*（三源校验参考值，非已证最优；全部 ≤/> 断言语义为与参考值不矛盾）。 -/
def estar : ℚ := 25759986531/1000000000

/-- assembledRecord = min(12 分区 bound)（证书口径；HP 片 b10 字面相等）。 -/
def aR : ℚ := 47517790735835014335570/1844674407417822803119

/-- 铁律容差 ε=1e-6（所有下界 ≤ E*+ε 口径）。 -/
def epsIron : ℚ := 1/1000000


/-- 端点锚：e0 字面 == −1/1。 -/
theorem e0_val : e0 = -1/1 := rfl
/-- 端点锚：e12 字面 == 1/1。 -/
theorem e12_val : e12 = 1/1 := rfl
/-- 端点链单调第 0 对：e0 ≤ e1。 -/
theorem e0_le_e1 : e0 ≤ e1 := by
  show (-1/1:ℚ) ≤ (-99/100:ℚ)
  norm_num1

/-- 端点链单调第 1 对：e1 ≤ e2。 -/
theorem e1_le_e2 : e1 ≤ e2 := by
  show (-99/100:ℚ) ≤ (-97/100:ℚ)
  norm_num1

/-- 端点链单调第 2 对：e2 ≤ e3。 -/
theorem e2_le_e3 : e2 ≤ e3 := by
  show (-97/100:ℚ) ≤ (-19/20:ℚ)
  norm_num1

/-- 端点链单调第 3 对：e3 ≤ e4。 -/
theorem e3_le_e4 : e3 ≤ e4 := by
  show (-19/20:ℚ) ≤ (-91/100:ℚ)
  norm_num1

/-- 端点链单调第 4 对：e4 ≤ e5。 -/
theorem e4_le_e5 : e4 ≤ e5 := by
  show (-91/100:ℚ) ≤ (-9/10:ℚ)
  norm_num1

/-- 端点链单调第 5 对：e5 ≤ e6。 -/
theorem e5_le_e6 : e5 ≤ e6 := by
  show (-9/10:ℚ) ≤ (-22/25:ℚ)
  norm_num1

/-- 端点链单调第 6 对：e6 ≤ e7。 -/
theorem e6_le_e7 : e6 ≤ e7 := by
  show (-22/25:ℚ) ≤ (-17/20:ℚ)
  norm_num1

/-- 端点链单调第 7 对：e7 ≤ e8。 -/
theorem e7_le_e8 : e7 ≤ e8 := by
  show (-17/20:ℚ) ≤ (-41/50:ℚ)
  norm_num1

/-- 端点链单调第 8 对：e8 ≤ e9。 -/
theorem e8_le_e9 : e8 ≤ e9 := by
  show (-41/50:ℚ) ≤ (-79/100:ℚ)
  norm_num1

/-- 端点链单调第 9 对：e9 ≤ e10。 -/
theorem e9_le_e10 : e9 ≤ e10 := by
  show (-79/100:ℚ) ≤ (-153/200:ℚ)
  norm_num1

/-- 端点链单调第 10 对：e10 ≤ e11。 -/
theorem e10_le_e11 : e10 ≤ e11 := by
  show (-153/200:ℚ) ≤ (-187/250:ℚ)
  norm_num1

/-- 端点链单调第 11 对：e11 ≤ e12。 -/
theorem e11_le_e12 : e11 ≤ e12 := by
  show (-187/250:ℚ) ≤ (1/1:ℚ)
  norm_num1

/-- 记录装配第 0 件：AR ≤ b0（31 字符大分数 norm_num1）。 -/
theorem ar_le_b0 : aR ≤ b0 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (1419245723139071/54975685305550:ℚ)
  norm_num1

/-- 记录装配第 1 件：AR ≤ b1（32 字符大分数 norm_num1）。 -/
theorem ar_le_b1 : aR ≤ b1 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (2837059739445683/109951417862103:ℚ)
  norm_num1

/-- 记录装配第 2 件：AR ≤ b2（142 字符大分数 norm_num1）。 -/
theorem ar_le_b2 : aR ≤ b2 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (95148034377368417075200000000000000000000000000000000000000000000000000/3689382200954663007811329305754478005508846420999294048885656184293211:ℚ)
  norm_num1

/-- 记录装配第 3 件：AR ≤ b3（32 字符大分数 norm_num1）。 -/
theorem ar_le_b3 : aR ≤ b3 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (5667139148427148/219902686859665:ℚ)
  norm_num1

/-- 记录装配第 4 件：AR ≤ b4（112 字符大分数 norm_num1）。 -/
theorem ar_le_b4 : aR ≤ b4 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (56294773645464181900024414062500000000000000000000000000/2184534926853278057997272238274297001333566701245806813:ℚ)
  norm_num1

/-- 记录装配第 5 件：AR ≤ b5（35 字符大分数 norm_num1）。 -/
theorem ar_le_b5 : aR ≤ b5 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (181313976026497009/7036874433292040:ℚ)
  norm_num1

/-- 记录装配第 6 件：AR ≤ b6（116 字符大分数 norm_num1）。 -/
theorem ar_le_b6 : aR ≤ b6 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (3601778876706306785345077514648437500000000000000000000000/139810133547249324624022947987425049230287605836864081701:ℚ)
  norm_num1

/-- 记录装配第 7 件：AR ≤ b7（120 字符大分数 norm_num1）。 -/
theorem ar_le_b7 : aR ≤ b7 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (816392769637139312746570369204224000000000000000000000000000/31691265490905997064799249668440887530527325545844277393403:ℚ)
  norm_num1

/-- 记录装配第 8 件：AR ≤ b8（123 字符大分数 norm_num1）。 -/
theorem ar_le_b8 : aR ≤ b8 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (24566821136999558261408693748961695746402256190776824951171875/953674662606910821016338272521529882970680171880635603760352:ℚ)
  norm_num1

/-- 记录装配第 9 件：AR ≤ b9（119 字符大分数 norm_num1）。 -/
theorem ar_le_b9 : aR ≤ b9 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (152060258133670143773900800000000000000000000000000000000000/5902963308524955309028900129512648637307845623943222995001:ℚ)
  norm_num1

/-- 记录装配第 10 件：AR ≤ b10（46 字符大分数 norm_num1）。 -/
theorem ar_le_b10 : aR ≤ b10 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (47517790735835014335570/1844674407417822803119:ℚ)
  norm_num1

/-- 记录装配第 11 件：AR ≤ b11（171 字符大分数 norm_num1）。 -/
theorem ar_le_b11 : aR ≤ b11 := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (22879340185047884591327492399406419521507688973060989923169472604058682918548583984375/888178445822492388747275390557723859303211430452579251742723511769167625620708441526:ℚ)
  norm_num1

/-- HP 片（指标 10，[−153/200,−187/250]）bound 字面 == AR（记录在 HP 片取到）。 -/
theorem b10_eq_ar : b10 = aR := by
  show (47517790735835014335570/1844674407417822803119:ℚ) = (47517790735835014335570/1844674407417822803119:ℚ)
  norm_num1

/-- 铁律（更强版）：AR ≤ E*（比 AR ≤ E*+1e-6 强且真，margin 0.0005405579025207914 > 0）。 -/
theorem iron_rule : aR ≤ estar := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (25759986531/1000000000:ℚ)
  norm_num1

/-- 铁律严格版：AR < E*（margin 为正）。 -/
theorem margin_pos : aR < estar := by
  show (47517790735835014335570/1844674407417822803119:ℚ) < (25759986531/1000000000:ℚ)
  norm_num1

/-- 铁律容差为正（ε 版铁律的 linarith 前提）。 -/
theorem epsIron_pos : (0:ℚ) < epsIron := by
  show (0:ℚ) < 1/1000000
  norm_num1

/-- 排除片 0 铁律：E* < b0（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl0_gt : estar < b0 := by
  show (25759986531/1000000000:ℚ) < (1419245723139071/54975685305550:ℚ)
  norm_num1

/-- 排除片 1 铁律：E* < b1（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl1_gt : estar < b1 := by
  show (25759986531/1000000000:ℚ) < (2837059739445683/109951417862103:ℚ)
  norm_num1

/-- 排除片 2 铁律：E* < b2（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl2_gt : estar < b2 := by
  show (25759986531/1000000000:ℚ) < (95148034377368417075200000000000000000000000000000000000000000000000000/3689382200954663007811329305754478005508846420999294048885656184293211:ℚ)
  norm_num1

/-- 排除片 3 铁律：E* < b3（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl3_gt : estar < b3 := by
  show (25759986531/1000000000:ℚ) < (5667139148427148/219902686859665:ℚ)
  norm_num1

/-- 排除片 4 铁律：E* < b4（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl4_gt : estar < b4 := by
  show (25759986531/1000000000:ℚ) < (56294773645464181900024414062500000000000000000000000000/2184534926853278057997272238274297001333566701245806813:ℚ)
  norm_num1

/-- 排除片 5 铁律：E* < b5（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl5_gt : estar < b5 := by
  show (25759986531/1000000000:ℚ) < (181313976026497009/7036874433292040:ℚ)
  norm_num1

/-- 排除片 6 铁律：E* < b6（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl6_gt : estar < b6 := by
  show (25759986531/1000000000:ℚ) < (3601778876706306785345077514648437500000000000000000000000/139810133547249324624022947987425049230287605836864081701:ℚ)
  norm_num1

/-- 排除片 7 铁律：E* < b7（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl7_gt : estar < b7 := by
  show (25759986531/1000000000:ℚ) < (816392769637139312746570369204224000000000000000000000000000/31691265490905997064799249668440887530527325545844277393403:ℚ)
  norm_num1

/-- 排除片 8 铁律：E* < b8（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl8_gt : estar < b8 := by
  show (25759986531/1000000000:ℚ) < (24566821136999558261408693748961695746402256190776824951171875/953674662606910821016338272521529882970680171880635603760352:ℚ)
  norm_num1

/-- 排除片 9 铁律：E* < b9（coverPiece=exclusion，区域不含 TTP 须 > E*）。 -/
theorem excl9_gt : estar < b9 := by
  show (25759986531/1000000000:ℚ) < (152060258133670143773900800000000000000000000000000000000000/5902963308524955309028900129512648637307845623943222995001:ℚ)
  norm_num1

/-- TTP-covering 片 10 铁律：b10 ≤ E*+ε（证书域含 TTP，须 ≤ E*+1e-6）。 -/
theorem cover10_le_iron : b10 ≤ estar + epsIron := by
  show (47517790735835014335570/1844674407417822803119:ℚ) ≤ (25759986531/1000000000:ℚ) + 1/1000000
  norm_num1

/-- TTP-covering 片 11 铁律：b11 ≤ E*+ε（证书域含 TTP，须 ≤ E*+1e-6）。 -/
theorem cover11_le_iron : b11 ≤ estar + epsIron := by
  show (22879340185047884591327492399406419521507688973060989923169472604058682918548583984375/888178445822492388747275390557723859303211430452579251742723511769167625620708441526:ℚ) ≤ (25759986531/1000000000:ℚ) + 1/1000000
  norm_num1

/-- 抽查 0（seed 20261017，最小命中指数法）：x 落入片 11 -/
theorem cover_spot0 : e11 ≤ (127893/1048576:ℚ) ∧ (127893/1048576:ℚ) ≤ e12 := by
  refine ⟨?_, ?_⟩
  · show (-187/250:ℚ) ≤ (127893/1048576:ℚ)
    norm_num1
  · show (127893/1048576:ℚ) ≤ (1/1:ℚ)
    norm_num1
/-- 抽查 1（seed 20261017，最小命中指数法）：x 落入片 6 -/
theorem cover_spot1 : e6 ≤ (-921351/1048576:ℚ) ∧ (-921351/1048576:ℚ) ≤ e7 := by
  refine ⟨?_, ?_⟩
  · show (-22/25:ℚ) ≤ (-921351/1048576:ℚ)
    norm_num1
  · show (-921351/1048576:ℚ) ≤ (-17/20:ℚ)
    norm_num1
/-- 抽查 2（seed 20261017，最小命中指数法）：x 落入片 11 -/
theorem cover_spot2 : e11 ≤ (196977/262144:ℚ) ∧ (196977/262144:ℚ) ≤ e12 := by
  refine ⟨?_, ?_⟩
  · show (-187/250:ℚ) ≤ (196977/262144:ℚ)
    norm_num1
  · show (196977/262144:ℚ) ≤ (1/1:ℚ)
    norm_num1

end ThomsonN9.TableB6Data
