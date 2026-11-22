import Mathlib
import ThomsonN9.TableB1Data

/-!
# Table B1 (R15 / r15b): the TTP nine-row Gram-node arithmetic layer

**B1.** For the 9-point TTP (tri-cap-prism) family `X(z)` — upper
triangle rows `(ρ,0,z)`, `(−ρ/2,±√3ρ/2,z)`, lower triangle with
`z → −z`, cap rows `(1/2,±√3/2,0)`, `(−1,0,0)`, `ρ = √(1−z²)` — this
file proves the arithmetic layer of the L4 orbit lemma exactly, with
all numeric data anchored in `ThomsonN9.TableB1Data` (the read-only
re-derivation of `results/local_min.json` + `results/l4_orbit.json`):

* **The 45 pairwise Gram identities.** For every ordered pair `i ≠ j`
  the inner product `⟪rᵢ,rⱼ⟫` equals one of the six node curves
  `ν₁..ν₆` (`gram_T0_T1` …, 36 off-diagonal theorems), and every row
  has unit norm (`gram_diag_*`, 9 theorems; `diag_norm_all` bundles
  them).  Each proof is the `TableB5.ttp_quadform` modulo-curve
  ring-certificate technique: the key identity
  `dot − ν = C₁·(√3·√3−3) + C₂·(ρ·ρ+z²−1)` with the two multipliers
  C₁, C₂ **generated exactly by the emitter's symbolic engine**
  (D61-3 v1/v2 lesson: never hand-write them — the design probe's
  hand-written ν₆ multiplier was correctly rejected by `ring`),
  discharged by `ring`, then killed by `Real.mul_self_sqrt` + `ring_nf`
  + `linarith`.

* **Classification bridge.** `nodeOfN` is the explicit arithmetic
  classification function (same-block triangle-internal / cap-cap /
  vertical / cross-misaligned / cap-prism residue classes), and
  `gram_nodeOfN` is the bridge: for every `k < l < 9` the geometric
  node of the pair `(k,l)` — the value `nuOfN (nodeOfN k l) z` —
  equals the pairwise theorem (`interval_cases` over the 36 arms,
  each arm calling that pair's own Gram theorem).  This is the formal
  link between the certificate layer and the counting layer.

* **Orbit balancing.** The six class counts over the 36 unordered
  pairs are `6/6/3/3/6/12` (`edge_counts`, `Finset.filter` + `decide`
  over `Fin 9 × Fin 9`; `edge_total` = 36), the per-vertex orbit
  profiles are `(2,1,0,1,2,2)` at each prism vertex and
  `(0,2,2,0,0,4)` at each cap vertex (`prism_profile`, `cap_profile`),
  and the Σ_y balance `Σ_v profile_v(c) = 2·mult(c)` holds for every
  class (`sigma_y_balance`) — reconciled field by field with
  `l4_orbit.json orbitBalance` (including its erratum: the six ν₂
  cap-prism edges vs the six ν₅ triangle-internal edges).

* **Node separation containers.** For every `z` in the recorded z-box
  (`zLo ≤ z ≤ zHi`, the strict isolation interval of `local_min.json`):
  each node curve lies in its rational container (`nu_containers`, 12
  conjuncts; ν₁/ν₄/ν₅ through the exact z²-envelope, ν₂/ν₆ through the
  200-bit Newton ρ-envelope via `Real.sqrt_le_sqrt` + the literal
  `Real.sqrt_le_iff` envelope), the six values are strictly ordered
  `ν₁ < ν₂ < ν₃ < ν₄ < ν₅ < ν₆` (`node_chain`), and consequently all
  15 pairs of node values are distinct (`node_values_distinct`).
  Together with the bridge this says: the Gram matrix at any z in
  the box has exactly six distinct off-diagonal values, and the
  node-class counting of the balancing layer coincides with the
  counting of distinct Gram values.

Honest scope note (B1 boundary, D61-3): the l4_orbit (P1)–(P4) filter
enumeration (K9 six-colour scout + interval re-verification + iso
classification) is a numerics-layer duty and is NOT part of this file;
the orbit-dimension / transverse-coordinate geometry of the original
stageb-scope §2 B1 wording is deferred to a later piece.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB1

open ThomsonN9.TableB1Data

/-! ### 45 逐对 Gram 定理（证书乘子＝发射器精确生成） -/
/-- 对角归一：⟪r_T0,r_T0⟫ = 1。 -/
theorem gram_diag_T0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) (rowT0 z) = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) (rowT0 z) - 1
      = (0:ℝ) * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_T1⟫ = nu5 z（ν₅ = (3z²−1)/2（上上/下下三角内部 6 边））。 -/
theorem gram_T0_T1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) (rowT1 z) = nu5 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) (rowT1 z) - nu5 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowT1 nu5 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_T2⟫ = nu5 z（ν₅ = (3z²−1)/2（上上/下下三角内部 6 边））。 -/
theorem gram_T0_T2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) (rowT2 z) = nu5 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) (rowT2 z) - nu5 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowT2 nu5 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_B0⟫ = nu4 z（ν₄ = 1−2z²（竖棱 3 边））。 -/
theorem gram_T0_B0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) (rowB0 z) = nu4 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) (rowB0 z) - nu4 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowB0 nu4 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_B1⟫ = nu1 z（ν₁ = −(1+z²)/2（上下错位 6 边））。 -/
theorem gram_T0_B1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) (rowB1 z) = nu1 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) (rowB1 z) - nu1 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowB1 nu1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_B2⟫ = nu1 z（ν₁ = −(1+z²)/2（上下错位 6 边））。 -/
theorem gram_T0_B2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) (rowB2 z) = nu1 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) (rowB2 z) - nu1 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowB2 nu1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_C0⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_T0_C0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) rowC0 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) rowC0 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowC0 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_C1⟫ = nu2 z（ν₂ = −ρ（帽棱≡1 6 边））。 -/
theorem gram_T0_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) rowC1 = nu2 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) rowC1 - nu2 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowC1 nu2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T0,r_C2⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_T0_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT0 z) rowC2 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT0 z) rowC2 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT0 rowC2 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_T1,r_T1⟫ = 1。 -/
theorem gram_diag_T1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) (rowT1 z) = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) (rowT1 z) - 1
      = (1/4:ℝ) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T1,r_T2⟫ = nu5 z（ν₅ = (3z²−1)/2（上上/下下三角内部 6 边））。 -/
theorem gram_T1_T2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) (rowT2 z) = nu5 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) (rowT2 z) - nu5 z
      = (-(1/4:ℝ)) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rowT2 nu5 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T1,r_B0⟫ = nu1 z（ν₁ = −(1+z²)/2（上下错位 6 边））。 -/
theorem gram_T1_B0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) (rowB0 z) = nu1 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) (rowB0 z) - nu1 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rowB0 nu1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T1,r_B1⟫ = nu4 z（ν₄ = 1−2z²（竖棱 3 边））。 -/
theorem gram_T1_B1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) (rowB1 z) = nu4 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) (rowB1 z) - nu4 z
      = (1/4:ℝ) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rowB1 nu4 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T1,r_B2⟫ = nu1 z（ν₁ = −(1+z²)/2（上下错位 6 边））。 -/
theorem gram_T1_B2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) (rowB2 z) = nu1 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) (rowB2 z) - nu1 z
      = (-(1/4:ℝ)) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rowB2 nu1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T1,r_C0⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_T1_C0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) rowC0 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) rowC0 - nu6 z
      = (1/4:ℝ) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rowC0 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T1,r_C1⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_T1_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) rowC1 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) rowC1 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rowC1 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T1,r_C2⟫ = nu2 z（ν₂ = −ρ（帽棱≡1 6 边））。 -/
theorem gram_T1_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT1 z) rowC2 = nu2 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT1 z) rowC2 - nu2 z
      = (-(1/4:ℝ)) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT1 rowC2 nu2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_T2,r_T2⟫ = 1。 -/
theorem gram_diag_T2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT2 z) (rowT2 z) = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT2 z) (rowT2 z) - 1
      = (1/4:ℝ) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T2,r_B0⟫ = nu1 z（ν₁ = −(1+z²)/2（上下错位 6 边））。 -/
theorem gram_T2_B0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT2 z) (rowB0 z) = nu1 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT2 z) (rowB0 z) - nu1 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT2 rowB0 nu1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T2,r_B1⟫ = nu1 z（ν₁ = −(1+z²)/2（上下错位 6 边））。 -/
theorem gram_T2_B1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT2 z) (rowB1 z) = nu1 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT2 z) (rowB1 z) - nu1 z
      = (-(1/4:ℝ)) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT2 rowB1 nu1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T2,r_B2⟫ = nu4 z（ν₄ = 1−2z²（竖棱 3 边））。 -/
theorem gram_T2_B2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT2 z) (rowB2 z) = nu4 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT2 z) (rowB2 z) - nu4 z
      = (1/4:ℝ) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT2 rowB2 nu4 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T2,r_C0⟫ = nu2 z（ν₂ = −ρ（帽棱≡1 6 边））。 -/
theorem gram_T2_C0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT2 z) rowC0 = nu2 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT2 z) rowC0 - nu2 z
      = (-(1/4:ℝ)) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT2 rowC0 nu2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T2,r_C1⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_T2_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT2 z) rowC1 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT2 z) rowC1 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT2 rowC1 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_T2,r_C2⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_T2_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowT2 z) rowC2 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowT2 z) rowC2 - nu6 z
      = (1/4:ℝ) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowT2 rowC2 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_B0,r_B0⟫ = 1。 -/
theorem gram_diag_B0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB0 z) (rowB0 z) = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB0 z) (rowB0 z) - 1
      = (0:ℝ) * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB0 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B0,r_B1⟫ = nu5 z（ν₅ = (3z²−1)/2（上上/下下三角内部 6 边））。 -/
theorem gram_B0_B1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB0 z) (rowB1 z) = nu5 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB0 z) (rowB1 z) - nu5 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB0 rowB1 nu5 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B0,r_B2⟫ = nu5 z（ν₅ = (3z²−1)/2（上上/下下三角内部 6 边））。 -/
theorem gram_B0_B2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB0 z) (rowB2 z) = nu5 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB0 z) (rowB2 z) - nu5 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB0 rowB2 nu5 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B0,r_C0⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_B0_C0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB0 z) rowC0 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB0 z) rowC0 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB0 rowC0 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B0,r_C1⟫ = nu2 z（ν₂ = −ρ（帽棱≡1 6 边））。 -/
theorem gram_B0_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB0 z) rowC1 = nu2 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB0 z) rowC1 - nu2 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB0 rowC1 nu2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B0,r_C2⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_B0_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB0 z) rowC2 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB0 z) rowC2 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB0 rowC2 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_B1,r_B1⟫ = 1。 -/
theorem gram_diag_B1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB1 z) (rowB1 z) = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB1 z) (rowB1 z) - 1
      = (1/4:ℝ) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B1,r_B2⟫ = nu5 z（ν₅ = (3z²−1)/2（上上/下下三角内部 6 边））。 -/
theorem gram_B1_B2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB1 z) (rowB2 z) = nu5 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB1 z) (rowB2 z) - nu5 z
      = (-(1/4:ℝ)) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (-(1/2:ℝ)) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB1 rowB2 nu5 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B1,r_C0⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_B1_C0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB1 z) rowC0 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB1 z) rowC0 - nu6 z
      = (1/4:ℝ) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB1 rowC0 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B1,r_C1⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_B1_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB1 z) rowC1 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB1 z) rowC1 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB1 rowC1 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B1,r_C2⟫ = nu2 z（ν₂ = −ρ（帽棱≡1 6 边））。 -/
theorem gram_B1_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB1 z) rowC2 = nu2 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB1 z) rowC2 - nu2 z
      = (-(1/4:ℝ)) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB1 rowC2 nu2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_B2,r_B2⟫ = 1。 -/
theorem gram_diag_B2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB2 z) (rowB2 z) = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB2 z) (rowB2 z) - 1
      = (1/4:ℝ) * rhoR z * rhoR z * (s3R * s3R - 3)
        + (1:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B2,r_C0⟫ = nu2 z（ν₂ = −ρ（帽棱≡1 6 边））。 -/
theorem gram_B2_C0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB2 z) rowC0 = nu2 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB2 z) rowC0 - nu2 z
      = (-(1/4:ℝ)) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB2 rowC0 nu2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B2,r_C1⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_B2_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB2 z) rowC1 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB2 z) rowC1 - nu6 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB2 rowC1 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_B2,r_C2⟫ = nu6 z（ν₆ = ρ/2（帽棱≡0,2 12 边））。 -/
theorem gram_B2_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 (rowB2 z) rowC2 = nu6 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 (rowB2 z) rowC2 - nu6 z
      = (1/4:ℝ) * rhoR z * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowB2 rowC2 nu6 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_C0,r_C0⟫ = 1。 -/
theorem gram_diag_C0 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 rowC0 rowC0 = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 rowC0 rowC0 - 1
      = (1/4:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowC0 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_C0,r_C1⟫ = nu3 z（ν₃ = −1/2（帽帽 3 边））。 -/
theorem gram_C0_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 rowC0 rowC1 = nu3 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 rowC0 rowC1 - nu3 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowC0 rowC1 nu3 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_C0,r_C2⟫ = nu3 z（ν₃ = −1/2（帽帽 3 边））。 -/
theorem gram_C0_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 rowC0 rowC2 = nu3 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 rowC0 rowC2 - nu3 z
      = (-(1/4:ℝ)) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowC0 rowC2 nu3 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_C1,r_C1⟫ = 1。 -/
theorem gram_diag_C1 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 rowC1 rowC1 = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 rowC1 rowC1 - 1
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowC1 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- ⟪r_C1,r_C2⟫ = nu3 z（ν₃ = −1/2（帽帽 3 边））。 -/
theorem gram_C1_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 rowC1 rowC2 = nu3 z := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 rowC1 rowC2 - nu3 z
      = (0:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowC1 rowC2 nu3 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-- 对角归一：⟪r_C2,r_C2⟫ = 1。 -/
theorem gram_diag_C2 (z : ℝ) (hz : z^2 ≤ 1) :
    dot3 rowC2 rowC2 = 1 := by
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith
  have hs3 : s3R * s3R = 3 := by
    unfold s3R; rw [Real.mul_self_sqrt (by norm_num)]
  have hr2 : rhoR z * rhoR z = 1 - z^2 := by
    unfold rhoR; rw [Real.mul_self_sqrt hnn]
  have key : dot3 rowC2 rowC2 - 1
      = (1/4:ℝ) * (s3R * s3R - 3)
        + (0:ℝ) * (rhoR z * rhoR z + z^2 - 1) := by
    unfold dot3 rowC2 rhoR s3R; ring
  rw [hs3, hr2] at key
  ring_nf at key
  linarith

/-! ### 行/节点索引装配与分类桥 -/
/-- 行索引装配：rowOfN k z = 第 k 行（k < 9；行序同 Data 件，
帽行为常量行）。 -/
noncomputable def rowOfN : ℕ → ℝ → ℝ × ℝ × ℝ
  | 0 => rowT0
  | 1 => rowT1
  | 2 => rowT2
  | 3 => rowB0
  | 4 => rowB1
  | 5 => rowB2
  | 6 => fun _ => rowC0
  | 7 => fun _ => rowC1
  | 8 => fun _ => rowC2
  | _ => rowT0

/-- 节点曲线索引装配：nuOfN k z = ν_(k+1)（k < 6）。 -/
noncomputable def nuOfN : ℕ → ℝ → ℝ
  | 0 => nu1
  | 1 => nu2
  | 2 => nu3
  | 3 => nu4
  | 4 => nu5
  | 5 => nu6
  | _ => nu6

/-- 算术分类函数（i = j 时为哑值 9）：同块 → 三角内部(4)/帽帽(2)；
帽-棱残差 (cap−prism)%3≡1 → ν₂(1)、≡0,2 → ν₆(5)；异侧三角 同余 →
竖棱(3)、不同余 → 上下错位(0)。与 l4_orbit.json orbitBalance 六类
计数对账（发射器几何分类 36/36 对账）。 -/
def nodeOfN : ℕ → ℕ → ℕ
  | i, j => if i = j then 9
    else if i / 3 = j / 3 then (if i / 3 = 2 then 2 else 4)
    else if i / 3 = 2 then (if (i % 3 + 3 - j % 3) % 3 = 1 then 1 else 5)
    else if j / 3 = 2 then (if (j % 3 + 3 - i % 3) % 3 = 1 then 1 else 5)
    else if i % 3 = j % 3 then 3 else 0

/-- **分类桥**：对一切 k < l < 9，第 (k,l) 对的 Gram 内积等于其算术
分类 nodeOfN 所指节点曲线（interval_cases 只生成合法 l 臂——每臂调用
该对专属 Gram 定理；证书层与计数层的正式链接）。 -/
theorem gram_nodeOfN (z : ℝ) (hz : z^2 ≤ 1) : ∀ k l : ℕ, k < 9 → l < 9 → k < l →
    dot3 (rowOfN k z) (rowOfN l z) = nuOfN (nodeOfN k l) z := by
  intro k l hk hl hkl
  interval_cases k
  · interval_cases l
    · exact gram_T0_T1 z hz
    · exact gram_T0_T2 z hz
    · exact gram_T0_B0 z hz
    · exact gram_T0_B1 z hz
    · exact gram_T0_B2 z hz
    · exact gram_T0_C0 z hz
    · exact gram_T0_C1 z hz
    · exact gram_T0_C2 z hz
  · interval_cases l
    · exact gram_T1_T2 z hz
    · exact gram_T1_B0 z hz
    · exact gram_T1_B1 z hz
    · exact gram_T1_B2 z hz
    · exact gram_T1_C0 z hz
    · exact gram_T1_C1 z hz
    · exact gram_T1_C2 z hz
  · interval_cases l
    · exact gram_T2_B0 z hz
    · exact gram_T2_B1 z hz
    · exact gram_T2_B2 z hz
    · exact gram_T2_C0 z hz
    · exact gram_T2_C1 z hz
    · exact gram_T2_C2 z hz
  · interval_cases l
    · exact gram_B0_B1 z hz
    · exact gram_B0_B2 z hz
    · exact gram_B0_C0 z hz
    · exact gram_B0_C1 z hz
    · exact gram_B0_C2 z hz
  · interval_cases l
    · exact gram_B1_B2 z hz
    · exact gram_B1_C0 z hz
    · exact gram_B1_C1 z hz
    · exact gram_B1_C2 z hz
  · interval_cases l
    · exact gram_B2_C0 z hz
    · exact gram_B2_C1 z hz
    · exact gram_B2_C2 z hz
  · interval_cases l
    · exact gram_C0_C1 z hz
    · exact gram_C0_C2 z hz
  · interval_cases l
    · exact gram_C1_C2 z hz
  · interval_cases l

/-! ### 对角归一（∀ 包装） -/
/-- 对角归一：一切 k < 9 行单位范数。 -/
theorem diag_norm_all (z : ℝ) (hz : z^2 ≤ 1) : ∀ k : ℕ, k < 9 →
    dot3 (rowOfN k z) (rowOfN k z) = 1 := by
  intro k hk
  interval_cases k
  · exact gram_diag_T0 z hz
  · exact gram_diag_T1 z hz
  · exact gram_diag_T2 z hz
  · exact gram_diag_B0 z hz
  · exact gram_diag_B1 z hz
  · exact gram_diag_B2 z hz
  · exact gram_diag_C0 z hz
  · exact gram_diag_C1 z hz
  · exact gram_diag_C2 z hz

/-! ### 轨道配平计数（Finset.filter decide） -/
/-- 六类边计数 edgeMult：6/6/3/3/6/12（l4_orbit.json tubeMults）。 -/
def edgeMult : ℕ → ℕ
  | 0 => 6 | 1 => 6 | 2 => 3 | 3 => 3 | 4 => 6 | _ => 12

/-- **六类边计数**：36 条无序对按 nodeOfN 分类的逐类计数 == 6/6/3/3/6/12。 -/
theorem edge_counts : ∀ c : Fin 6, (Finset.univ.filter (fun p : Fin 9 × Fin 9 =>
    p.1.val < p.2.val ∧ nodeOfN p.1.val p.2.val = c.val)).card
    = edgeMult c.val := by decide

/-- 36 条无序对总数。 -/
theorem edge_total : (Finset.univ.filter (fun p : Fin 9 × Fin 9 =>
    p.1.val < p.2.val)).card = 36 := by decide

/-- 多重集总和 == 36。 -/
theorem edgeMult_sum : (∑ c ∈ (Finset.univ : Finset (Fin 6)), edgeMult c.val) = 36 := by
  decide

/-- 棱顶轨道轮廓 (2,1,0,1,2,2)。 -/
def prismProf : ℕ → ℕ
  | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 2 | _ => 2
/-- 帽顶轨道轮廓 (0,2,2,0,0,4)。 -/
def capProf : ℕ → ℕ
  | 0 => 0 | 1 => 2 | 2 => 2 | 3 => 0 | 4 => 0 | _ => 4

/-- **棱顶轮廓**：六个棱顶（上/下三角）逐类邻接计数 == (2,1,0,1,2,2)。 -/
theorem prism_profile : ∀ (v : Fin 9) (c : Fin 6), v.val < 6 →
    (Finset.univ.filter (fun j : Fin 9 =>
      v.val ≠ j.val ∧ nodeOfN v.val j.val = c.val)).card
    = prismProf c.val := by decide

/-- **帽顶轮廓**：三个帽顶逐类邻接计数 == (0,2,2,0,0,4)。 -/
theorem cap_profile : ∀ (v : Fin 9) (c : Fin 6), 6 ≤ v.val →
    (Finset.univ.filter (fun j : Fin 9 =>
      v.val ≠ j.val ∧ nodeOfN v.val j.val = c.val)).card
    = capProf c.val := by decide

/-- **Σ_y 配平定理**：逐类 Σ_v profile_v(c) == 2·mult(c)（双计数恒等，
l4_orbit.json orbitBalance.perNodeSums_Sigma_y 同源）。 -/
theorem sigma_y_balance : ∀ c : Fin 6,
    (∑ v ∈ (Finset.univ : Finset (Fin 9)), (Finset.univ.filter (fun j : Fin 9 =>
      v.val ≠ j.val ∧ nodeOfN v.val j.val = c.val)).card)
    = 2 * edgeMult c.val := by decide

/-! ### 节点分离容器（z 盒上） -/
/-- **ν 容器定理**：z 盒内一切 z，六 ν 曲线各落在其有理容器内
（12 合取；ν₁/ν₄/ν₅ 走 z² 有理包端点精确式，ν₂/ν₆ 走 ρ Newton 包
（Real.sqrt_le_sqrt＋字面 sqrt_le_iff），ν₃ 为点容器）。 -/
theorem nu_containers (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    (nu1Lo:ℝ) ≤ nu1 z ∧ nu1 z ≤ (nu1Hi:ℝ)
    ∧ (nu2Lo:ℝ) ≤ nu2 z ∧ nu2 z ≤ (nu2Hi:ℝ)
    ∧ (nu3Lo:ℝ) ≤ nu3 z ∧ nu3 z ≤ (nu3Hi:ℝ)
    ∧ (nu4Lo:ℝ) ≤ nu4 z ∧ nu4 z ≤ (nu4Hi:ℝ)
    ∧ (nu5Lo:ℝ) ≤ nu5 z ∧ nu5 z ≤ (nu5Hi:ℝ)
    ∧ (nu6Lo:ℝ) ≤ nu6 z ∧ nu6 z ≤ (nu6Hi:ℝ)
 := by
  have hzLop : (0:ℝ) < (zLo:ℝ) := by norm_num [zLo]
  have hzhi : (0:ℝ) < (zHi:ℝ) := by norm_num [zHi]
  have hpos : (0:ℝ) < z := by nlinarith [h1, hzLop]
  have hzlo2 : (zLo:ℝ)^2 ≤ z^2 := by nlinarith [h1, hpos]
  have hzhi2 : z^2 ≤ (zHi:ℝ)^2 := by nlinarith [h2, hpos, hzhi]
  have hzh1 : (zHi:ℝ) < 1 := by norm_num [zHi]
  have hnn : (0:ℝ) ≤ 1 - z^2 := by nlinarith [hzhi2, hzh1]
  have hsq : 1 - z^2 ≤ 1 - (zLo:ℝ)^2 := by nlinarith [hzlo2]
  have hlit : Real.sqrt (1 - (zLo:ℝ)^2) ≤ (rhoUp:ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num [rhoUp, zLo]
  have hrUp : rhoR z ≤ (rhoUp:ℝ) := by
    calc rhoR z = Real.sqrt (1 - z^2) := rfl
      _ ≤ Real.sqrt (1 - (zLo:ℝ)^2) := Real.sqrt_le_sqrt hsq
      _ ≤ (rhoUp:ℝ) := hlit
  have hrDn : (rhoDn:ℝ) ≤ rhoR z := by
    have e : ((rhoDn:ℝ))^2 ≤ 1 - z^2 := by
      nlinarith [(show ((rhoDn:ℝ))^2 ≤ 1 - (zHi:ℝ)^2 by norm_num [rhoDn, zHi]),
        hzhi2]
    have hp : (0:ℝ) < (rhoDn:ℝ) := by norm_num [rhoDn]
    rw [show rhoR z = Real.sqrt (1 - z^2) from rfl]
    nlinarith [e, hp, Real.sqrt_nonneg (1 - z^2), Real.sq_sqrt hnn]
  have e1 : nu1 z = -(1 + z^2)/2 := by unfold nu1; ring
  have e2 : nu2 z = -(rhoR z) := by unfold nu2; ring
  have e3 : nu3 z = -1/2 := by unfold nu3; ring
  have e4 : nu4 z = 1 - 2*z^2 := by unfold nu4; ring
  have e5 : nu5 z = (3*z^2 - 1)/2 := by unfold nu5; ring
  have e6 : nu6 z = rhoR z / 2 := by unfold nu6; ring
  have c1lo : (nu1Lo:ℝ) = -(1 + (zHi:ℝ)^2)/2 := by norm_num [nu1Lo, zHi]
  have c1hi : (nu1Hi:ℝ) = -(1 + (zLo:ℝ)^2)/2 := by norm_num [nu1Hi, zLo]
  have c3lo : (nu3Lo:ℝ) = -1/2 := by norm_num [nu3Lo]
  have c3hi : (nu3Hi:ℝ) = -1/2 := by norm_num [nu3Hi]
  have c4lo : (nu4Lo:ℝ) = 1 - 2*(zHi:ℝ)^2 := by norm_num [nu4Lo, zHi]
  have c4hi : (nu4Hi:ℝ) = 1 - 2*(zLo:ℝ)^2 := by norm_num [nu4Hi, zLo]
  have c5lo : (nu5Lo:ℝ) = (3*(zLo:ℝ)^2 - 1)/2 := by norm_num [nu5Lo, zLo]
  have c5hi : (nu5Hi:ℝ) = (3*(zHi:ℝ)^2 - 1)/2 := by norm_num [nu5Hi, zHi]
  have c2lo : (nu2Lo:ℝ) = -(rhoUp:ℝ) := by norm_num [nu2Lo, rhoUp]
  have c2hi : (nu2Hi:ℝ) = -(rhoDn:ℝ) := by norm_num [nu2Hi, rhoDn]
  have c6lo : (nu6Lo:ℝ) = (rhoDn:ℝ)/2 := by norm_num [nu6Lo, rhoDn]
  have c6hi : (nu6Hi:ℝ) = (rhoUp:ℝ)/2 := by norm_num [nu6Hi, rhoUp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **节点链**：z 盒上 ν₁ < ν₂ < ν₃ < ν₄ < ν₅ < ν₆（容器＋五链不交）。 -/
theorem node_chain (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    nu1 z < nu2 z ∧ nu2 z < nu3 z ∧ nu3 z < nu4 z ∧ nu4 z < nu5 z ∧
    nu5 z < nu6 z := by
  have hc := nu_containers z h1 h2
  have d1 : (nu1Hi:ℝ) < (nu2Lo:ℝ) := by norm_num [nu1Hi, nu2Lo]
  have d2 : (nu2Hi:ℝ) < (nu3Lo:ℝ) := by norm_num [nu2Hi, nu3Lo]
  have d3 : (nu3Hi:ℝ) < (nu4Lo:ℝ) := by norm_num [nu3Hi, nu4Lo]
  have d4 : (nu4Hi:ℝ) < (nu5Lo:ℝ) := by norm_num [nu4Hi, nu5Lo]
  have d5 : (nu5Hi:ℝ) < (nu6Lo:ℝ) := by norm_num [nu5Hi, nu6Lo]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **15 对两两分离**：z 盒上任意两个不同节点曲线值不相等
（节点链的配对推论；interval_cases 30 臂）。 -/
theorem node_values_distinct (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    ∀ k l : ℕ, k < 6 → l < 6 → k ≠ l → nuOfN k z ≠ nuOfN l z := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := node_chain z h1 h2
  intro k l hk hl hne
  rcases lt_or_gt_of_ne hne with h | h
  · interval_cases k <;> interval_cases l <;> simp only [nuOfN] <;> linarith
  · interval_cases l <;> interval_cases k <;> simp only [nuOfN] <;> linarith

end ThomsonN9.TableB1
