import Mathlib
/-!
# Table B1 data (R15 / r15b): the TTP nine-row Gram-node arithmetic layer

This module is deliberately self-contained: it imports only `Mathlib`,
imports no in-repo solution module, and is imported only by
`ThomsonN9/TableB1.lean`.  It materialises the atom/row layer of the
B1 package — the l4_orbit (P5) realisation certificate plus the orbit
balancing arithmetic — re-derived here through the independent second
implementation of `numerics/bounds/r15_b1_data.py` (stdlib-Fraction
symbolic engine over ℚ[z,ρ,√3]; provenance = sha256 of local_min.json
and l4_orbit.json, recorded in `results/r15_b1_data.json`):

* `rhoR`/`s3R`/`dot3` — the ρ = √(1−z²), √3 atoms and the row dot
  product (rows written in ρ/√3 atom style, same source as
  `TableB5.ttpQ` / `numerics/family.py tri_cap_prism`);
* the nine rows `rowT0..rowC2` — upper triangle (ρ,0,z),
  (−ρ/2,±√3ρ/2,z), lower triangle with z → −z, caps
  (1/2,±√3/2,0), (−1,0,0) (row order of `l4_orbit.family_points_s3`);
* the six node curves `nu1..nu6` — ν₁=−(1+z²)/2, ν₂=−ρ, ν₃=−1/2,
  ν₄=1−2z², ν₅=(3z²−1)/2, ν₆=ρ/2 (`l4_orbit.json nodes.curves_x2`)
  re-derived bit for bit;
* the container literals — `zLo`/`zHi` (the strict isolation interval
  `zStarIntervalMpmath` of `results/local_min.json`, exact rational
  endpoints), the 200-bit Newton ρ-envelope `rhoDn`/`rhoUp`, and the
  twelve ν-container endpoints (ν₁/ν₄/ν₅ exact rational endpoints from
  the z²-envelope, ν₂/ν₆ from the ρ-envelope, ν₃ the point −1/2), with
  the five-link disjointness chain as a `norm_num` theorem (⇒ the 15
  pairwise separations);
* three fixed random rational spot checks (seed 20261017, z on the
  2⁻⁴⁰ grid inside the z-box) of the six ν-containers, each proved in
  Lean through per-point Newton ρ-envelopes and cross-checked against
  the emitter's independent Fraction computation.

Honest scope note (B1 boundary, D61-3): the l4_orbit (P1)–(P4) filter
enumeration (K9 six-colour scout + interval re-verification + iso
classification) is a numerics-layer duty and is NOT part of this file;
the orbit-dimension / transverse-coordinate geometry of the original
stageb-scope §2 B1 wording is deferred to a later piece.  This piece is
the arithmetic layer: the (P5) realisation certificate, the balancing
counts, and the node separation containers.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB1Data

/-- ρ 原子：ρ = √(1−z²)（模曲线 ρ² = 1−z²）。 -/
noncomputable def rhoR (z : ℝ) : ℝ := Real.sqrt (1 - z^2)
/-- √3 原子（(√3)² = 3 消零用）。 -/
noncomputable def s3R : ℝ := Real.sqrt 3
/-- 行内积（ℝ×ℝ×ℝ 三分量）。 -/
noncomputable def dot3 (a b : ℝ × ℝ × ℝ) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- 上三角行 k=0：(ρ, 0, z)。 -/
noncomputable def rowT0 (z : ℝ) : ℝ × ℝ × ℝ := (rhoR z, 0, z)
/-- 上三角行 k=1：(−ρ/2, √3ρ/2, z)。 -/
noncomputable def rowT1 (z : ℝ) : ℝ × ℝ × ℝ := (-(rhoR z)/2, s3R * rhoR z / 2, z)
/-- 上三角行 k=2：(−ρ/2, −√3ρ/2, z)。 -/
noncomputable def rowT2 (z : ℝ) : ℝ × ℝ × ℝ := (-(rhoR z)/2, -(s3R * rhoR z / 2), z)
/-- 下三角行 k=0：(ρ, 0, −z)。 -/
noncomputable def rowB0 (z : ℝ) : ℝ × ℝ × ℝ := (rhoR z, 0, -z)
/-- 下三角行 k=1：(−ρ/2, √3ρ/2, −z)。 -/
noncomputable def rowB1 (z : ℝ) : ℝ × ℝ × ℝ := (-(rhoR z)/2, s3R * rhoR z / 2, -z)
/-- 下三角行 k=2：(−ρ/2, −√3ρ/2, −z)。 -/
noncomputable def rowB2 (z : ℝ) : ℝ × ℝ × ℝ := (-(rhoR z)/2, -(s3R * rhoR z / 2), -z)
/-- 帽行 j=0：(1/2, √3/2, 0)。 -/
noncomputable def rowC0 : ℝ × ℝ × ℝ := (1/2, s3R/2, 0)
/-- 帽行 j=1：(−1, 0, 0)。 -/
noncomputable def rowC1 : ℝ × ℝ × ℝ := (-1, 0, 0)
/-- 帽行 j=2：(1/2, −√3/2, 0)。 -/
noncomputable def rowC2 : ℝ × ℝ × ℝ := (1/2, -s3R/2, 0)

/-- 节点曲线 ν₁ = −(1+z²)/2（上下错位 6 边）。 -/
noncomputable def nu1 (z : ℝ) : ℝ := -(1 + z^2)/2
/-- 节点曲线 ν₂ = −ρ（帽棱≡1 6 边）。 -/
noncomputable def nu2 (z : ℝ) : ℝ := -(rhoR z)
/-- 节点曲线 ν₃ = −1/2（帽帽 3 边）。 -/
noncomputable def nu3 (z : ℝ) : ℝ := -1/2
/-- 节点曲线 ν₄ = 1−2z²（竖棱 3 边）。 -/
noncomputable def nu4 (z : ℝ) : ℝ := 1 - 2*z^2
/-- 节点曲线 ν₅ = (3z²−1)/2（上上/下下三角内部 6 边）。 -/
noncomputable def nu5 (z : ℝ) : ℝ := (3*z^2 - 1)/2
/-- 节点曲线 ν₆ = ρ/2（帽棱≡0,2 12 边）。 -/
noncomputable def nu6 (z : ℝ) : ℝ := rhoR z / 2

/-! ### 容器字面量（z 盒、ρ 包、六 ν 容器、抽查点） -/
/- z 盒下端（local_min.json zStarIntervalMpmath 严格隔离区间精确有理端点）。 -/
def zLo : ℚ := 175912094116210948602230246251565404236316681/250000000000000000000000000000000000000000000
/- z 盒上端（同上）。 -/
def zHi : ℚ := 351824569702148426397769753748434595763683319/500000000000000000000000000000000000000000000
/- ρ 的 200-bit Newton 有理下界包（rhoDn² ≤ 1 − zHi² ≤ ρ(z)² 于盒上）。 -/
def rhoDn : ℚ := 1141805967021713074672581461757591416599246201137984251436193/1606938044258990275541962092341162602522202993782792835301376
/- ρ 的 200-bit Newton 有理上界包（ρ(z)² ≤ 1 − zLo² ≤ rhoUp² 于盒上）。 -/
def rhoUp : ℚ := 1141807181114071074791597250713687405185622558906879142679459/1606938044258990275541962092341162602522202993782792835301376
/- ν1 容器下端。ν₁ = −(1+z²)/2（上下错位 6 边） -/
def nu1Lo : ℚ := -373780527846101896475859545040422561326456898875252340943916452473648470711253821718855761/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/- ν1 容器上端。 -/
def nu1Hi : ℚ := -93445064856350658642194375951527242099350870124512289674385202473648470711253821718855761/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/- ν2 容器下端。ν₂ = −ρ（帽棱≡1 6 边） -/
def nu2Lo : ℚ := -1141807181114071074791597250713687405185622558906879142679459/1606938044258990275541962092341162602522202993782792835301376
/- ν2 容器上端。 -/
def nu2Hi : ℚ := -1141805967021713074672581461757591416599246201137984251436193/1606938044258990275541962092341162602522202993782792835301376
/- ν3 容器下端。ν₃ = −1/2（帽帽 3 边） -/
def nu3Lo : ℚ := -1/2
/- ν3 容器上端。 -/
def nu3Hi : ℚ := -1/2
/- ν4 容器下端。ν₄ = 1−2z²（竖棱 3 边） -/
def nu4Lo : ℚ := 1219472153898103524140454959577438673543101124747659056083547526351529288746178281144239/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/- ν4 容器上端。 -/
def nu4Hi : ℚ := 304935143649341357805624048472757900649129875487710325614797526351529288746178281144239/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/- ν5 容器下端。ν₅ = (3z²−1)/2（上上/下下三角内部 6 边） -/
def nu5Lo : ℚ := 30335194569051975926583127854581726298052610373536869023155607420945412133761465156567283/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/- ν5 容器上端。 -/
def nu5Hi : ℚ := 121341583538305689427578635121267683979370696625757022831749357420945412133761465156567283/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/- ν6 容器下端。ν₆ = ρ/2（帽棱≡0,2 12 边） -/
def nu6Lo : ℚ := 1141805967021713074672581461757591416599246201137984251436193/3213876088517980551083924184682325205044405987565585670602752
/- ν6 容器上端。 -/
def nu6Hi : ℚ := 1141807181114071074791597250713687405185622558906879142679459/3213876088517980551083924184682325205044405987565585670602752
/- 抽查点 0（z = 773669865905/1099511627776，seed 20261017）。 -/
def spotZ0 : ℚ := 773669865905/1099511627776
/- 抽查点 0 的 ρ Newton 下界包。 -/
def spotRhoDn0 : ℚ := 285451688859198329546103989324218094867426095559562724878341/401734511064747568885490523085290650630550748445698208825344
/- 抽查点 0 的 ρ Newton 上界包。 -/
def spotRhoUp0 : ℚ := 1141806755436793318184415957296872379469704382238250899513365/1606938044258990275541962092341162602522202993782792835301376
/- 抽查点 1（z = 386834801797/549755813888，seed 20261017）。 -/
def spotZ1 : ℚ := 386834801797/549755813888
/- 抽查点 1 的 ρ Newton 下界包。 -/
def spotRhoDn1 : ℚ := 570903567541053435693484850583288076099322198157759505236477/803469022129495137770981046170581301261101496891396417650688
/- 抽查点 1 的 ρ Newton 上界包。 -/
def spotRhoUp1 : ℚ := 1141807135082106871386969701166576152198644396315519010472955/1606938044258990275541962092341162602522202993782792835301376
/- 抽查点 2（z = 773670030909/1099511627776，seed 20261017）。 -/
def spotZ2 : ℚ := 773670030909/1099511627776
/- 抽查点 2 的 ρ Newton 下界包。 -/
def spotRhoDn2 : ℚ := 1141806516624735942298289624052409720719225297643840773398175/1606938044258990275541962092341162602522202993782792835301376
/- 抽查点 2 的 ρ Newton 上界包。 -/
def spotRhoUp2 : ℚ := 35681453644522998196821550751637803772475790551370024168693/50216813883093446110686315385661331328818843555712276103168

/-! ### 端点事实（ℚ norm_num） -/
/- z 盒为正区间：0 < zLo ≤ zHi < 1。 -/
theorem zLo_pos : (0:ℚ) < zLo := by norm_num [zLo]
theorem zHi_pos : (0:ℚ) < zHi := by norm_num [zHi]
theorem zHi_lt_one : (zHi:ℚ) < 1 := by norm_num [zHi]
theorem zLo_le_zHi : zLo ≤ zHi := by norm_num [zLo, zHi]
/- ν₁ 容器端点 == −(1+z²)/2 在 z 盒端点的精确值（逐位）。 -/
theorem nu1Lo_eq : nu1Lo = -(1 + zHi^2)/2 := by norm_num [nu1Lo, zHi]
theorem nu1Hi_eq : nu1Hi = -(1 + zLo^2)/2 := by norm_num [nu1Hi, zLo]
/- ν₄ 容器端点 == 1−2z² 端点精确值。 -/
theorem nu4Lo_eq : nu4Lo = 1 - 2*zHi^2 := by norm_num [nu4Lo, zHi]
theorem nu4Hi_eq : nu4Hi = 1 - 2*zLo^2 := by norm_num [nu4Hi, zLo]
/- ν₅ 容器端点 == (3z²−1)/2 端点精确值。 -/
theorem nu5Lo_eq : nu5Lo = (3*zLo^2 - 1)/2 := by norm_num [nu5Lo, zLo]
theorem nu5Hi_eq : nu5Hi = (3*zHi^2 - 1)/2 := by norm_num [nu5Hi, zHi]
/- ν₂ 容器端点 == −ρ 包端点（−rhoUp/−rhoDn）。 -/
theorem nu2Lo_eq : nu2Lo = -rhoUp := by norm_num [nu2Lo, rhoUp]
theorem nu2Hi_eq : nu2Hi = -rhoDn := by norm_num [nu2Hi, rhoDn]
/- ν₃ 容器为点 −1/2。 -/
theorem nu3_pt : nu3Lo = -1/2 ∧ nu3Hi = -1/2 := by
  constructor <;> norm_num [nu3Lo, nu3Hi]
/- ν₆ 容器端点 == ρ 包端点之半。 -/
theorem nu6Lo_eq : nu6Lo = rhoDn/2 := by norm_num [nu6Lo, rhoDn]
theorem nu6Hi_eq : nu6Hi = rhoUp/2 := by norm_num [nu6Hi, rhoUp]
/- ρ Newton 包前提两件＋正性。 -/
theorem rhoDn_sq_le : rhoDn^2 ≤ 1 - zHi^2 := by norm_num [rhoDn, zHi]
theorem rhoUp_sq_ge : 1 - zLo^2 ≤ rhoUp^2 := by norm_num [rhoUp, zLo]
theorem rhoDn_pos : (0:ℚ) < rhoDn := by norm_num [rhoDn]
theorem rhoUp_pos : (0:ℚ) < rhoUp := by norm_num [rhoUp]
/- 抽查点 ρ 包前提（3×2＋正性）。 -/
theorem spotRhoDn0_sq_le : spotRhoDn0^2 ≤ 1 - spotZ0^2 := by
  norm_num [spotRhoDn0, spotZ0]
theorem spotRhoUp0_sq_ge : 1 - spotZ0^2 ≤ spotRhoUp0^2 := by
  norm_num [spotRhoUp0, spotZ0]
theorem spotRhoDn0_pos : (0:ℚ) < spotRhoDn0 := by norm_num [spotRhoDn0]
theorem spotRhoDn1_sq_le : spotRhoDn1^2 ≤ 1 - spotZ1^2 := by
  norm_num [spotRhoDn1, spotZ1]
theorem spotRhoUp1_sq_ge : 1 - spotZ1^2 ≤ spotRhoUp1^2 := by
  norm_num [spotRhoUp1, spotZ1]
theorem spotRhoDn1_pos : (0:ℚ) < spotRhoDn1 := by norm_num [spotRhoDn1]
theorem spotRhoDn2_sq_le : spotRhoDn2^2 ≤ 1 - spotZ2^2 := by
  norm_num [spotRhoDn2, spotZ2]
theorem spotRhoUp2_sq_ge : 1 - spotZ2^2 ≤ spotRhoUp2^2 := by
  norm_num [spotRhoUp2, spotZ2]
theorem spotRhoDn2_pos : (0:ℚ) < spotRhoDn2 := by norm_num [spotRhoDn2]
/- **容器五链两两不交**（⇒ 15 对节点曲线在 z 盒上两两分离）。 -/
theorem nu_chain_disjoint :
    nu1Hi < nu2Lo ∧ nu2Hi < nu3Lo ∧ nu3Hi < nu4Lo ∧ nu4Hi < nu5Lo ∧
    nu5Hi < nu6Lo := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [nu1Hi, nu2Lo, nu2Hi, nu3Lo, nu3Hi, nu4Lo, nu4Hi, nu5Lo, nu5Hi, nu6Lo]

/-! ### 抽查定理（3 点 × 六 ν 容器包含性） -/
/-- 抽查 0（seed 20261017，z = 773669865905/1099511627776 ∈ 盒）：六 ν 容器
    包含性（ν₂/ν₆ 经逐点 Newton ρ 包＋sqrt 单调；期望值＝发射器
    独立 Fraction 重算，门 G5 复放对账）。 -/
theorem spot0_containers :
    (nu1Lo:ℝ) ≤ nu1 (spotZ0:ℝ) ∧ nu1 (spotZ0:ℝ) ≤ (nu1Hi:ℝ)
    ∧ (nu2Lo:ℝ) ≤ nu2 (spotZ0:ℝ) ∧ nu2 (spotZ0:ℝ) ≤ (nu2Hi:ℝ)
    ∧ (nu3Lo:ℝ) ≤ nu3 (spotZ0:ℝ) ∧ nu3 (spotZ0:ℝ) ≤ (nu3Hi:ℝ)
    ∧ (nu4Lo:ℝ) ≤ nu4 (spotZ0:ℝ) ∧ nu4 (spotZ0:ℝ) ≤ (nu4Hi:ℝ)
    ∧ (nu5Lo:ℝ) ≤ nu5 (spotZ0:ℝ) ∧ nu5 (spotZ0:ℝ) ≤ (nu5Hi:ℝ)
    ∧ (nu6Lo:ℝ) ≤ nu6 (spotZ0:ℝ) ∧ nu6 (spotZ0:ℝ) ≤ (nu6Hi:ℝ)
 := by
  have hnn : (0:ℝ) ≤ 1 - (spotZ0:ℝ)^2 := by norm_num [spotZ0]
  have hr : (spotRhoDn0:ℝ) ≤ rhoR (spotZ0:ℝ) ∧ rhoR (spotZ0:ℝ) ≤ (spotRhoUp0:ℝ) := by
    constructor
    · have e : ((spotRhoDn0:ℝ))^2 ≤ 1 - (spotZ0:ℝ)^2 := by
        norm_num [spotRhoDn0, spotZ0]
      have hp : (0:ℝ) < (spotRhoDn0:ℝ) := by norm_num [spotRhoDn0]
      rw [show rhoR (spotZ0:ℝ) = Real.sqrt (1 - (spotZ0:ℝ)^2) from rfl]
      nlinarith [e, hp, Real.sqrt_nonneg (1 - (spotZ0:ℝ)^2),
        Real.sq_sqrt hnn]
    · rw [show rhoR (spotZ0:ℝ) = Real.sqrt (1 - (spotZ0:ℝ)^2) from rfl]
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num [spotRhoUp0, spotZ0]
  have e1 : nu1 (spotZ0:ℝ) = -(1 + (spotZ0:ℝ)^2)/2 := by unfold nu1; ring
  have e2 : nu2 (spotZ0:ℝ) = -(rhoR (spotZ0:ℝ)) := by unfold nu2; ring
  have e3 : nu3 (spotZ0:ℝ) = -1/2 := by unfold nu3; ring
  have e4 : nu4 (spotZ0:ℝ) = 1 - 2*(spotZ0:ℝ)^2 := by unfold nu4; ring
  have e5 : nu5 (spotZ0:ℝ) = (3*(spotZ0:ℝ)^2 - 1)/2 := by unfold nu5; ring
  have e6 : nu6 (spotZ0:ℝ) = rhoR (spotZ0:ℝ)/2 := by unfold nu6; ring
  have p1lo : (nu1Lo:ℝ) ≤ -(1 + (spotZ0:ℝ)^2)/2 := by norm_num [nu1Lo, spotZ0]
  have p1hi : -(1 + (spotZ0:ℝ)^2)/2 ≤ (nu1Hi:ℝ) := by norm_num [nu1Hi, spotZ0]
  have p4lo : (nu4Lo:ℝ) ≤ 1 - 2*(spotZ0:ℝ)^2 := by norm_num [nu4Lo, spotZ0]
  have p4hi : 1 - 2*(spotZ0:ℝ)^2 ≤ (nu4Hi:ℝ) := by norm_num [nu4Hi, spotZ0]
  have p5lo : (nu5Lo:ℝ) ≤ (3*(spotZ0:ℝ)^2 - 1)/2 := by norm_num [nu5Lo, spotZ0]
  have p5hi : (3*(spotZ0:ℝ)^2 - 1)/2 ≤ (nu5Hi:ℝ) := by norm_num [nu5Hi, spotZ0]
  have p3lo : (nu3Lo:ℝ) = -1/2 := by norm_num [nu3Lo]
  have p3hi : (nu3Hi:ℝ) = -1/2 := by norm_num [nu3Hi]
  have u1 : (spotRhoUp0:ℝ) ≤ (rhoUp:ℝ) := by norm_num [spotRhoUp0, rhoUp]
  have u2 : (rhoDn:ℝ) ≤ (spotRhoDn0:ℝ) := by norm_num [rhoDn, spotRhoDn0]
  have c2lo : (nu2Lo:ℝ) = -(rhoUp:ℝ) := by norm_num [nu2Lo, rhoUp]
  have c2hi : (nu2Hi:ℝ) = -(rhoDn:ℝ) := by norm_num [nu2Hi, rhoDn]
  have c6lo : (nu6Lo:ℝ) = (rhoDn:ℝ)/2 := by norm_num [nu6Lo, rhoDn]
  have c6hi : (nu6Hi:ℝ) = (rhoUp:ℝ)/2 := by norm_num [nu6Hi, rhoUp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- 抽查 1（seed 20261017，z = 386834801797/549755813888 ∈ 盒）：六 ν 容器
    包含性（ν₂/ν₆ 经逐点 Newton ρ 包＋sqrt 单调；期望值＝发射器
    独立 Fraction 重算，门 G5 复放对账）。 -/
theorem spot1_containers :
    (nu1Lo:ℝ) ≤ nu1 (spotZ1:ℝ) ∧ nu1 (spotZ1:ℝ) ≤ (nu1Hi:ℝ)
    ∧ (nu2Lo:ℝ) ≤ nu2 (spotZ1:ℝ) ∧ nu2 (spotZ1:ℝ) ≤ (nu2Hi:ℝ)
    ∧ (nu3Lo:ℝ) ≤ nu3 (spotZ1:ℝ) ∧ nu3 (spotZ1:ℝ) ≤ (nu3Hi:ℝ)
    ∧ (nu4Lo:ℝ) ≤ nu4 (spotZ1:ℝ) ∧ nu4 (spotZ1:ℝ) ≤ (nu4Hi:ℝ)
    ∧ (nu5Lo:ℝ) ≤ nu5 (spotZ1:ℝ) ∧ nu5 (spotZ1:ℝ) ≤ (nu5Hi:ℝ)
    ∧ (nu6Lo:ℝ) ≤ nu6 (spotZ1:ℝ) ∧ nu6 (spotZ1:ℝ) ≤ (nu6Hi:ℝ)
 := by
  have hnn : (0:ℝ) ≤ 1 - (spotZ1:ℝ)^2 := by norm_num [spotZ1]
  have hr : (spotRhoDn1:ℝ) ≤ rhoR (spotZ1:ℝ) ∧ rhoR (spotZ1:ℝ) ≤ (spotRhoUp1:ℝ) := by
    constructor
    · have e : ((spotRhoDn1:ℝ))^2 ≤ 1 - (spotZ1:ℝ)^2 := by
        norm_num [spotRhoDn1, spotZ1]
      have hp : (0:ℝ) < (spotRhoDn1:ℝ) := by norm_num [spotRhoDn1]
      rw [show rhoR (spotZ1:ℝ) = Real.sqrt (1 - (spotZ1:ℝ)^2) from rfl]
      nlinarith [e, hp, Real.sqrt_nonneg (1 - (spotZ1:ℝ)^2),
        Real.sq_sqrt hnn]
    · rw [show rhoR (spotZ1:ℝ) = Real.sqrt (1 - (spotZ1:ℝ)^2) from rfl]
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num [spotRhoUp1, spotZ1]
  have e1 : nu1 (spotZ1:ℝ) = -(1 + (spotZ1:ℝ)^2)/2 := by unfold nu1; ring
  have e2 : nu2 (spotZ1:ℝ) = -(rhoR (spotZ1:ℝ)) := by unfold nu2; ring
  have e3 : nu3 (spotZ1:ℝ) = -1/2 := by unfold nu3; ring
  have e4 : nu4 (spotZ1:ℝ) = 1 - 2*(spotZ1:ℝ)^2 := by unfold nu4; ring
  have e5 : nu5 (spotZ1:ℝ) = (3*(spotZ1:ℝ)^2 - 1)/2 := by unfold nu5; ring
  have e6 : nu6 (spotZ1:ℝ) = rhoR (spotZ1:ℝ)/2 := by unfold nu6; ring
  have p1lo : (nu1Lo:ℝ) ≤ -(1 + (spotZ1:ℝ)^2)/2 := by norm_num [nu1Lo, spotZ1]
  have p1hi : -(1 + (spotZ1:ℝ)^2)/2 ≤ (nu1Hi:ℝ) := by norm_num [nu1Hi, spotZ1]
  have p4lo : (nu4Lo:ℝ) ≤ 1 - 2*(spotZ1:ℝ)^2 := by norm_num [nu4Lo, spotZ1]
  have p4hi : 1 - 2*(spotZ1:ℝ)^2 ≤ (nu4Hi:ℝ) := by norm_num [nu4Hi, spotZ1]
  have p5lo : (nu5Lo:ℝ) ≤ (3*(spotZ1:ℝ)^2 - 1)/2 := by norm_num [nu5Lo, spotZ1]
  have p5hi : (3*(spotZ1:ℝ)^2 - 1)/2 ≤ (nu5Hi:ℝ) := by norm_num [nu5Hi, spotZ1]
  have p3lo : (nu3Lo:ℝ) = -1/2 := by norm_num [nu3Lo]
  have p3hi : (nu3Hi:ℝ) = -1/2 := by norm_num [nu3Hi]
  have u1 : (spotRhoUp1:ℝ) ≤ (rhoUp:ℝ) := by norm_num [spotRhoUp1, rhoUp]
  have u2 : (rhoDn:ℝ) ≤ (spotRhoDn1:ℝ) := by norm_num [rhoDn, spotRhoDn1]
  have c2lo : (nu2Lo:ℝ) = -(rhoUp:ℝ) := by norm_num [nu2Lo, rhoUp]
  have c2hi : (nu2Hi:ℝ) = -(rhoDn:ℝ) := by norm_num [nu2Hi, rhoDn]
  have c6lo : (nu6Lo:ℝ) = (rhoDn:ℝ)/2 := by norm_num [nu6Lo, rhoDn]
  have c6hi : (nu6Hi:ℝ) = (rhoUp:ℝ)/2 := by norm_num [nu6Hi, rhoUp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- 抽查 2（seed 20261017，z = 773670030909/1099511627776 ∈ 盒）：六 ν 容器
    包含性（ν₂/ν₆ 经逐点 Newton ρ 包＋sqrt 单调；期望值＝发射器
    独立 Fraction 重算，门 G5 复放对账）。 -/
theorem spot2_containers :
    (nu1Lo:ℝ) ≤ nu1 (spotZ2:ℝ) ∧ nu1 (spotZ2:ℝ) ≤ (nu1Hi:ℝ)
    ∧ (nu2Lo:ℝ) ≤ nu2 (spotZ2:ℝ) ∧ nu2 (spotZ2:ℝ) ≤ (nu2Hi:ℝ)
    ∧ (nu3Lo:ℝ) ≤ nu3 (spotZ2:ℝ) ∧ nu3 (spotZ2:ℝ) ≤ (nu3Hi:ℝ)
    ∧ (nu4Lo:ℝ) ≤ nu4 (spotZ2:ℝ) ∧ nu4 (spotZ2:ℝ) ≤ (nu4Hi:ℝ)
    ∧ (nu5Lo:ℝ) ≤ nu5 (spotZ2:ℝ) ∧ nu5 (spotZ2:ℝ) ≤ (nu5Hi:ℝ)
    ∧ (nu6Lo:ℝ) ≤ nu6 (spotZ2:ℝ) ∧ nu6 (spotZ2:ℝ) ≤ (nu6Hi:ℝ)
 := by
  have hnn : (0:ℝ) ≤ 1 - (spotZ2:ℝ)^2 := by norm_num [spotZ2]
  have hr : (spotRhoDn2:ℝ) ≤ rhoR (spotZ2:ℝ) ∧ rhoR (spotZ2:ℝ) ≤ (spotRhoUp2:ℝ) := by
    constructor
    · have e : ((spotRhoDn2:ℝ))^2 ≤ 1 - (spotZ2:ℝ)^2 := by
        norm_num [spotRhoDn2, spotZ2]
      have hp : (0:ℝ) < (spotRhoDn2:ℝ) := by norm_num [spotRhoDn2]
      rw [show rhoR (spotZ2:ℝ) = Real.sqrt (1 - (spotZ2:ℝ)^2) from rfl]
      nlinarith [e, hp, Real.sqrt_nonneg (1 - (spotZ2:ℝ)^2),
        Real.sq_sqrt hnn]
    · rw [show rhoR (spotZ2:ℝ) = Real.sqrt (1 - (spotZ2:ℝ)^2) from rfl]
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num [spotRhoUp2, spotZ2]
  have e1 : nu1 (spotZ2:ℝ) = -(1 + (spotZ2:ℝ)^2)/2 := by unfold nu1; ring
  have e2 : nu2 (spotZ2:ℝ) = -(rhoR (spotZ2:ℝ)) := by unfold nu2; ring
  have e3 : nu3 (spotZ2:ℝ) = -1/2 := by unfold nu3; ring
  have e4 : nu4 (spotZ2:ℝ) = 1 - 2*(spotZ2:ℝ)^2 := by unfold nu4; ring
  have e5 : nu5 (spotZ2:ℝ) = (3*(spotZ2:ℝ)^2 - 1)/2 := by unfold nu5; ring
  have e6 : nu6 (spotZ2:ℝ) = rhoR (spotZ2:ℝ)/2 := by unfold nu6; ring
  have p1lo : (nu1Lo:ℝ) ≤ -(1 + (spotZ2:ℝ)^2)/2 := by norm_num [nu1Lo, spotZ2]
  have p1hi : -(1 + (spotZ2:ℝ)^2)/2 ≤ (nu1Hi:ℝ) := by norm_num [nu1Hi, spotZ2]
  have p4lo : (nu4Lo:ℝ) ≤ 1 - 2*(spotZ2:ℝ)^2 := by norm_num [nu4Lo, spotZ2]
  have p4hi : 1 - 2*(spotZ2:ℝ)^2 ≤ (nu4Hi:ℝ) := by norm_num [nu4Hi, spotZ2]
  have p5lo : (nu5Lo:ℝ) ≤ (3*(spotZ2:ℝ)^2 - 1)/2 := by norm_num [nu5Lo, spotZ2]
  have p5hi : (3*(spotZ2:ℝ)^2 - 1)/2 ≤ (nu5Hi:ℝ) := by norm_num [nu5Hi, spotZ2]
  have p3lo : (nu3Lo:ℝ) = -1/2 := by norm_num [nu3Lo]
  have p3hi : (nu3Hi:ℝ) = -1/2 := by norm_num [nu3Hi]
  have u1 : (spotRhoUp2:ℝ) ≤ (rhoUp:ℝ) := by norm_num [spotRhoUp2, rhoUp]
  have u2 : (rhoDn:ℝ) ≤ (spotRhoDn2:ℝ) := by norm_num [rhoDn, spotRhoDn2]
  have c2lo : (nu2Lo:ℝ) = -(rhoUp:ℝ) := by norm_num [nu2Lo, rhoUp]
  have c2hi : (nu2Hi:ℝ) = -(rhoDn:ℝ) := by norm_num [nu2Hi, rhoDn]
  have c6lo : (nu6Lo:ℝ) = (rhoDn:ℝ)/2 := by norm_num [nu6Lo, rhoDn]
  have c6hi : (nu6Hi:ℝ) = (rhoUp:ℝ)/2 := by norm_num [nu6Hi, rhoUp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end ThomsonN9.TableB1Data
