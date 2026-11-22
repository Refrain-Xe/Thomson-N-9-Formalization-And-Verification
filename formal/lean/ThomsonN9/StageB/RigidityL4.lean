import ThomsonN9.StageB.RigidityL4Data
import ThomsonN9.StageB.ThreePoint
import ThomsonN9.TableB5Chain

/-!
# Thomson N = 9 Stage B — Module 5: Combinatorial Rigidity (`L4`) & Procrustes Ball (`L5`)

Proves `rigidity_to_ball`: any 9-point unit-sphere configuration satisfying `TubePremise` at
`ρ = 1 / 10000` has its pairwise Gram color pattern isomorphic to `TableB1.nodeOfN` (via the
kernel-verified 28-leaf sorted-row-0 `K_9` DFS in `RigidityL4Data`), and therefore lies within
Procrustes Frobenius distance `≤ 1 / 500` of `TableB5Core.ttpX z`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.RigidityL4

open Finset ThomsonN9.StageB ThomsonN9.StageB.RigidityL4Data
open ThomsonN9.TableB1 ThomsonN9.TableB1Data ThomsonN9.TableB5 ThomsonN9.TableB5Data
open ThomsonN9.TableB5Core ThomsonN9.TableB5Chain ThomsonN9.TableB5ChainData
open scoped RealInnerProductSpace Matrix

/-- Row matrix of a 9-point configuration `x : Fin 9 → R3` (definitionally identical to `CapCert.toMat`). -/
def toMat (x : Fin 9 → R3) : Matrix (Fin 9) (Fin 3) ℝ := fun i j => x i j

private lemma toMat_dot (x : Fin 9 → R3) (i j : Fin 9) :
    toMat x i ⬝ᵥ toMat x j = ⟪x i, x j⟫ := by
  rw [inner_R3_expand]
  simp [toMat, dotProduct, Fin.sum_univ_three]

private lemma toMat_unit (x : Fin 9 → R3) (hu : ∀ i, ‖x i‖ = 1) (i : Fin 9) :
    toMat x i ⬝ᵥ toMat x i = 1 := by
  rw [toMat_dot, real_inner_self_eq_norm_sq, hu i]; norm_num

/-! ## Section 1: Soundness of Scaled-Integer Interval Arithmetic (`IvZ`) -/

def _root_.ThomsonN9.StageB.RigidityL4Data.IvZ.inR (I : IvZ) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

private lemma ivAdd_sound {I J : IvZ} {x y : ℝ} (hx : I.inR x) (hy : J.inR y) :
    (ivAdd I J).inR (x + y) := by
  unfold IvZ.inR ivAdd at *; push_cast; constructor <;> linarith

private lemma ivSub_sound {I J : IvZ} {x y : ℝ} (hx : I.inR x) (hy : J.inR y) :
    (ivSub I J).inR (x - y) := by
  unfold IvZ.inR ivSub at *; push_cast; constructor <;> linarith

private lemma ivMul_sound {I J : IvZ} {x y : ℝ} (hx : I.inR x) (hy : J.inR y) :
    (ivMul I J).inR (x * y) := by
  unfold IvZ.inR ivMul at *
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  have hlo : min (min ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)))
      (min ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ))) ≤ x * y := by
    have h1 : 0 ≤ (x - I.lo) * (y - J.lo) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (I.hi - x) * (y - J.lo) := mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ (x - I.lo) * (J.hi - y) := mul_nonneg (by linarith) (by linarith)
    have h4 : 0 ≤ (I.hi - x) * (J.hi - y) := mul_nonneg (by linarith) (by linarith)
    by_cases hy0 : 0 ≤ y
    · have hmin : (I.lo : ℝ) * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy0
      by_cases hIlo : 0 ≤ (I.lo : ℝ)
      · have := mul_le_mul_of_nonneg_left hy1 hIlo
        exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (le_trans this hmin)
      · have := mul_le_mul_of_nonpos_left hy2 (le_of_not_ge hIlo)
        exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (le_trans this hmin)
    · have hmin : (I.hi : ℝ) * y ≤ x * y := mul_le_mul_of_nonpos_right hx2 (le_of_not_ge hy0)
      by_cases hIhi : 0 ≤ (I.hi : ℝ)
      · have := mul_le_mul_of_nonneg_left hy1 hIhi
        exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (le_trans this hmin)
      · have := mul_le_mul_of_nonpos_left hy2 (le_of_not_ge hIhi)
        exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (le_trans this hmin)
  have hhi : x * y ≤ max (max ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)))
      (max ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ))) := by
    by_cases hy0 : 0 ≤ y
    · have hmax : x * y ≤ (I.hi : ℝ) * y := mul_le_mul_of_nonneg_right hx2 hy0
      by_cases hIhi : 0 ≤ (I.hi : ℝ)
      · have := mul_le_mul_of_nonneg_left hy2 hIhi
        exact le_trans hmax (le_trans this (le_trans (le_max_right _ _) (le_max_right _ _)))
      · have := mul_le_mul_of_nonpos_left hy1 (le_of_not_ge hIhi)
        exact le_trans hmax (le_trans this (le_trans (le_max_left _ _) (le_max_right _ _)))
    · have hmax : x * y ≤ (I.lo : ℝ) * y := mul_le_mul_of_nonpos_right hx1 (le_of_not_ge hy0)
      by_cases hIlo : 0 ≤ (I.lo : ℝ)
      · have := mul_le_mul_of_nonneg_left hy2 hIlo
        exact le_trans hmax (le_trans this (le_trans (le_max_right _ _) (le_max_left _ _)))
      · have := mul_le_mul_of_nonpos_left hy1 (le_of_not_ge hIlo)
        exact le_trans hmax (le_trans this (le_trans (le_max_left _ _) (le_max_left _ _)))
  constructor <;> simpa only [Int.cast_min, Int.cast_max, Int.cast_mul] using (by assumption)

private lemma ivSq_sound {I : IvZ} {x : ℝ} (hx : I.inR x) :
    (ivSq I).inR (x * x) := by
  unfold IvZ.inR ivSq at *
  obtain ⟨hx1, hx2⟩ := hx
  split_ifs with h
  · constructor
    · simp only [Int.cast_zero]; exact mul_self_nonneg x
    · simp only [Int.cast_max, Int.cast_mul]
      by_cases hx0 : 0 ≤ x
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)
  · simp only [Int.cast_min, Int.cast_max, Int.cast_mul]
    have hcases : (I.lo : ℝ) > 0 ∨ (I.hi : ℝ) < 0 := by
      have : ¬ ((I.lo : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ I.hi) := h
      by_cases h1 : (I.lo : ℤ) ≤ 0
      · right; have h2 : I.hi < 0 := by omega
        exact_mod_cast h2
      · left; have h2 : 0 < I.lo := by omega
        exact_mod_cast h2
    rcases hcases with hpos | hneg
    · constructor
      · exact le_trans (min_le_left _ _) (by nlinarith)
      · exact le_trans (by nlinarith) (le_max_right _ _)
    · constructor
      · exact le_trans (min_le_right _ _) (by nlinarith)
      · exact le_trans (by nlinarith) (le_max_left _ _)

private lemma ivScale_sound (k : ℤ) {I : IvZ} {x : ℝ} (hx : I.inR x) :
    (ivScale k I).inR ((k : ℝ) * x) := by
  unfold IvZ.inR ivScale at *
  obtain ⟨hx1, hx2⟩ := hx
  split_ifs with hk
  · have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast; constructor <;> nlinarith
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast (show k ≤ 0 by omega)
    push_cast; constructor <;> nlinarith

private lemma ivConst_sound (c : ℤ) : (IvZ.mk c c).inR (c : ℝ) :=
  ⟨le_refl _, le_refl _⟩

private lemma detG_iv_sound {a b c : ℕ} {u v t : ℝ}
    (ha : (nodeIv a).inR (100000 * u)) (hb : (nodeIv b).inR (100000 * v))
    (hc : (nodeIv c).inR (100000 * t)) :
    (detG_iv a b c).inR ((100000 : ℝ) ^ 3 * detG u v t) := by
  have h := ivSub_sound (ivAdd_sound (ivConst_sound S3_iv) (ivScale_sound 2 (ivMul_sound (ivMul_sound ha hb) hc)))
    (ivScale_sound S_iv (ivAdd_sound (ivAdd_sound (ivSq_sound ha) (ivSq_sound hb)) (ivSq_sound hc)))
  have heq : ((S3_iv : ℝ) + (2 : ℤ) * ((100000 * u) * (100000 * v) * (100000 * t)))
      - (S_iv : ℝ) * (((100000 * u) * (100000 * u) + (100000 * v) * (100000 * v)) + (100000 * t) * (100000 * t)) =
      (100000 : ℝ) ^ 3 * detG u v t := by
    unfold detG S_iv S3_iv; push_cast; ring
  rw [heq] at h
  exact h

private lemma det4_iv_sound {a b c d e f : ℕ} {x01 x02 x12 x03 x13 x23 : ℝ}
    (ha : (nodeIv a).inR (100000 * x01)) (hb : (nodeIv b).inR (100000 * x02))
    (hc : (nodeIv c).inR (100000 * x12)) (hd : (nodeIv d).inR (100000 * x03))
    (he : (nodeIv e).inR (100000 * x13)) (hf : (nodeIv f).inR (100000 * x23)) :
    (det4_iv a b c d e f).inR ((100000 : ℝ) ^ 4 * det4 x01 x02 x03 x12 x13 x23) := by
  have hs2 := ivAdd_sound (ivAdd_sound (ivSq_sound ha) (ivSq_sound hb))
    (ivAdd_sound (ivAdd_sound (ivSq_sound hc) (ivSq_sound hd)) (ivAdd_sound (ivSq_sound he) (ivSq_sound hf)))
  have ht3 := ivAdd_sound (ivAdd_sound (ivMul_sound (ivMul_sound ha hb) hc) (ivMul_sound (ivMul_sound ha hd) he))
    (ivAdd_sound (ivMul_sound (ivMul_sound hb hd) hf) (ivMul_sound (ivMul_sound hc he) hf))
  have hp2 := ivAdd_sound (ivAdd_sound (ivMul_sound (ivSq_sound ha) (ivSq_sound hf))
    (ivMul_sound (ivSq_sound hb) (ivSq_sound he))) (ivMul_sound (ivSq_sound hc) (ivSq_sound hd))
  have hc4 := ivAdd_sound (ivAdd_sound (ivMul_sound (ivMul_sound ha hc) (ivMul_sound hf hd))
    (ivMul_sound (ivMul_sound ha he) (ivMul_sound hf hb))) (ivMul_sound (ivMul_sound hb hc) (ivMul_sound he hd))
  have h := ivSub_sound (ivAdd_sound (ivAdd_sound (ivSub_sound (ivConst_sound S4_iv) (ivScale_sound S2_iv hs2))
    (ivScale_sound (2 * S_iv) ht3)) hp2) (ivScale_sound 2 hc4)
  have heq : ((((S4_iv : ℝ) - (S2_iv : ℝ) * (((100000 * x01) * (100000 * x01) + (100000 * x02) * (100000 * x02))
      + (((100000 * x12) * (100000 * x12) + (100000 * x03) * (100000 * x03))
        + ((100000 * x13) * (100000 * x13) + (100000 * x23) * (100000 * x23)))))
      + ((2 * S_iv : ℤ) : ℝ) * ((((100000 * x01) * (100000 * x02) * (100000 * x12))
        + ((100000 * x01) * (100000 * x03) * (100000 * x13)))
        + (((100000 * x02) * (100000 * x03) * (100000 * x23))
          + ((100000 * x12) * (100000 * x13) * (100000 * x23)))))
      + ((((100000 * x01) * (100000 * x01) * ((100000 * x23) * (100000 * x23)))
        + ((100000 * x02) * (100000 * x02) * ((100000 * x13) * (100000 * x13))))
        + ((100000 * x12) * (100000 * x12) * ((100000 * x03) * (100000 * x03)))))
      - ((2 : ℤ) : ℝ) * ((((100000 * x01) * (100000 * x12) * ((100000 * x23) * (100000 * x03)))
        + ((100000 * x01) * (100000 * x13) * ((100000 * x23) * (100000 * x02))))
        + ((100000 * x02) * (100000 * x12) * ((100000 * x13) * (100000 * x03)))) =
      (100000 : ℝ) ^ 4 * det4 x01 x02 x03 x12 x13 x23 := by
    unfold det4 S_iv S2_iv S4_iv; push_cast; ring
  rw [heq] at h
  exact h

private lemma nodeIv_mem_of_hit {z t : ℝ} (hzLo : (TableB5Data.zLo : ℝ) ≤ z) (hzHi : z ≤ (TableB5Data.zHi : ℝ))
    {a : ℕ} (ha : a < 6) (hhit : |t - nuOfN a z| ≤ 1 / 10000) :
    (nodeIv a).inR (100000 * t) := by
  obtain ⟨hnuLo, hnuHi⟩ := nu_container_idx z hzLo hzHi a ha
  rw [abs_le] at hhit
  have hbounds : ((nodeIv a).lo : ℝ) / 100000 ≤ (nuLoIdx a : ℝ) - 1 / 10000 ∧
      (nuHiIdx a : ℝ) + 1 / 10000 ≤ ((nodeIv a).hi : ℝ) / 100000 := by
    interval_cases a
    · exact ⟨by have h : (((nodeIv 0).lo : ℚ) / 100000 : ℝ) ≤ ((nu1Lo - 1 / 10000 : ℚ) : ℝ) := by exact_mod_cast iv0_lo_ok
                simpa [nuLoIdx] using h,
             by have h : ((nu1Hi + 1 / 10000 : ℚ) : ℝ) ≤ (((nodeIv 0).hi : ℚ) / 100000 : ℝ) := by exact_mod_cast iv0_hi_ok
                simpa [nuHiIdx] using h⟩
    · exact ⟨by have h : (((nodeIv 1).lo : ℚ) / 100000 : ℝ) ≤ ((nu2Lo - 1 / 10000 : ℚ) : ℝ) := by exact_mod_cast iv1_lo_ok
                simpa [nuLoIdx] using h,
             by have h : ((nu2Hi + 1 / 10000 : ℚ) : ℝ) ≤ (((nodeIv 1).hi : ℚ) / 100000 : ℝ) := by exact_mod_cast iv1_hi_ok
                simpa [nuHiIdx] using h⟩
    · exact ⟨by have h : (((nodeIv 2).lo : ℚ) / 100000 : ℝ) ≤ ((nu3Lo - 1 / 10000 : ℚ) : ℝ) := by exact_mod_cast iv2_lo_ok
                simpa [nuLoIdx] using h,
             by have h : ((nu3Hi + 1 / 10000 : ℚ) : ℝ) ≤ (((nodeIv 2).hi : ℚ) / 100000 : ℝ) := by exact_mod_cast iv2_hi_ok
                simpa [nuHiIdx] using h⟩
    · exact ⟨by have h : (((nodeIv 3).lo : ℚ) / 100000 : ℝ) ≤ ((nu4Lo - 1 / 10000 : ℚ) : ℝ) := by exact_mod_cast iv3_lo_ok
                simpa [nuLoIdx] using h,
             by have h : ((nu4Hi + 1 / 10000 : ℚ) : ℝ) ≤ (((nodeIv 3).hi : ℚ) / 100000 : ℝ) := by exact_mod_cast iv3_hi_ok
                simpa [nuHiIdx] using h⟩
    · exact ⟨by have h : (((nodeIv 4).lo : ℚ) / 100000 : ℝ) ≤ ((nu5Lo - 1 / 10000 : ℚ) : ℝ) := by exact_mod_cast iv4_lo_ok
                simpa [nuLoIdx] using h,
             by have h : ((nu5Hi + 1 / 10000 : ℚ) : ℝ) ≤ (((nodeIv 4).hi : ℚ) / 100000 : ℝ) := by exact_mod_cast iv4_hi_ok
                simpa [nuHiIdx] using h⟩
    · exact ⟨by have h : (((nodeIv 5).lo : ℚ) / 100000 : ℝ) ≤ ((nu6Lo - 1 / 10000 : ℚ) : ℝ) := by exact_mod_cast iv5_lo_ok
                simpa [nuLoIdx] using h,
             by have h : ((nu6Hi + 1 / 10000 : ℚ) : ℝ) ≤ (((nodeIv 5).hi : ℚ) / 100000 : ℝ) := by exact_mod_cast iv5_hi_ok
                simpa [nuHiIdx] using h⟩
  unfold IvZ.inR
  constructor <;> linarith

private lemma tri_mask_bit_one {a b c : ℕ} (ha : a < 6) (hb : b < 6) (hc : c < 6)
    {x0 x1 x2 : R3} (h0 : ‖x0‖ = 1) (h1 : ‖x1‖ = 1) (h2 : ‖x2‖ = 1)
    (hia : (nodeIv a).inR (100000 * ⟪x0, x1⟫))
    (hib : (nodeIv b).inR (100000 * ⟪x0, x2⟫))
    (hic : (nodeIv c).inR (100000 * ⟪x1, x2⟫)) :
    ((triMask a b >>> c) &&& 1) = 1 := by
  have hbit : ((triMask a b >>> c) &&& 1) = 0 ∨ ((triMask a b >>> c) &&& 1) = 1 := by
    have : ((triMask a b >>> c) &&& 1) < 2 := by rw [Nat.and_one_is_mod]; omega
    omega
  rcases hbit with hzero | hone
  · exfalso
    have hsound := tri_sound_ok
    unfold checkTriSound at hsound
    have ha' := List.all_eq_true.mp hsound a (List.mem_range.mpr ha)
    have hb' := List.all_eq_true.mp ha' b (List.mem_range.mpr hb)
    have hc' := List.all_eq_true.mp hb' c (List.mem_range.mpr hc)
    simp only [hzero, beq_iff_eq, zero_ne_one, ↓reduceIte, decide_eq_true_eq] at hc'
    have hiv := detG_iv_sound hia hib hic
    have hdet := detG_nonneg_of_unit h0 h1 h2
    have hhi_neg : ((detG_iv a b c).hi : ℝ) < 0 := by exact_mod_cast hc'
    have hpos : (0 : ℝ) ≤ (100000 : ℝ) ^ 3 * detG ⟪x0, x1⟫ ⟪x0, x2⟫ ⟪x1, x2⟫ := by positivity
    linarith [hiv.2]
  · exact hone

private lemma k4_mask_bit_one {a b c d e f : ℕ}
    (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6) (he : e < 6) (hf : f < 6)
    {x0 x1 x2 x3 : R3} (h0 : ‖x0‖ = 1) (h1 : ‖x1‖ = 1) (h2 : ‖x2‖ = 1) (h3 : ‖x3‖ = 1)
    (hia : (nodeIv a).inR (100000 * ⟪x0, x1⟫))
    (hib : (nodeIv b).inR (100000 * ⟪x0, x2⟫))
    (hic : (nodeIv c).inR (100000 * ⟪x1, x2⟫))
    (hid : (nodeIv d).inR (100000 * ⟪x0, x3⟫))
    (hie : (nodeIv e).inR (100000 * ⟪x1, x3⟫))
    (hif : (nodeIv f).inR (100000 * ⟪x2, x3⟫)) :
    ((k4Mask a b c d e >>> f) &&& 1) = 1 := by
  have ht1 := tri_mask_bit_one ha hb hc h0 h1 h2 hia hib hic
  have ht2 := tri_mask_bit_one ha hd he h0 h1 h3 hia hid hie
  have ht3 := tri_mask_bit_one hb hd hf h0 h2 h3 hib hid hif
  have ht4 := tri_mask_bit_one hc he hf h1 h2 h3 hic hie hif
  have hbit : ((k4Mask a b c d e >>> f) &&& 1) = 0 ∨ ((k4Mask a b c d e >>> f) &&& 1) = 1 := by
    have : ((k4Mask a b c d e >>> f) &&& 1) < 2 := by rw [Nat.and_one_is_mod]; omega
    omega
  rcases hbit with hzero | hone
  · exfalso
    have hsound := k4_sound_ok
    unfold checkK4Sound at hsound
    have h1' := List.all_eq_true.mp hsound a (List.mem_range.mpr ha)
    have h2' := List.all_eq_true.mp h1' b (List.mem_range.mpr hb)
    have h3' := List.all_eq_true.mp h2' c (List.mem_range.mpr hc)
    simp only [ht1, beq_iff_eq, one_ne_zero, ↓reduceIte] at h3'
    have h4' := List.all_eq_true.mp h3' d (List.mem_range.mpr hd)
    have h5' := List.all_eq_true.mp h4' e (List.mem_range.mpr he)
    simp only [ht2, beq_iff_eq, one_ne_zero, ↓reduceIte] at h5'
    have h6' := List.all_eq_true.mp h5' f (List.mem_range.mpr hf)
    simp only [ht3, ht4, hzero, beq_iff_eq, one_ne_zero, zero_ne_one, Bool.or_self, ↓reduceIte,
      decide_eq_true_eq] at h6'
    have hiv := det4_iv_sound hia hib hic hid hie hif
    have hdet := det4_eq_zero_of_unit x0 x1 x2 x3 h0 h1 h2 h3
    rw [hdet, mul_zero] at hiv
    rcases h6' with hneg | hpos
    · have : ((det4_iv a b c d e f).hi : ℝ) < 0 := by exact_mod_cast hneg
      linarith [hiv.2]
    · have : (0 : ℝ) < ((det4_iv a b c d e f).lo : ℝ) := by exact_mod_cast hpos
      linarith [hiv.1]
  · exact hone

/-! ## Section 2: Soundness of `checkAll` DFS & Bit-Packing Invariant -/

private def MatchesPrefix (C : ℕ → ℕ → ℕ) (v u bits : ℕ) : Prop :=
  (∀ u' v', u' < v' → v' < 9 → (v' < v ∨ (v' = v ∧ u' < u)) → getC bits u' v' = C u' v') ∧
  (∀ k, eIdx u v ≤ k → (bits >>> (k * 3)) = 0)

private lemma eIdx_lt_of_before : ∀ u' v' u v : Fin 9,
    u'.val < v'.val → u.val < v.val →
    (v'.val < v.val ∨ (v'.val = v.val ∧ u'.val < u.val)) →
    eIdx u'.val v'.val < eIdx u.val v.val := by
  decide

private lemma eIdx_rollover : ∀ v : Fin 8, eIdx v.val v.val = eIdx 0 (v.val + 1) := by
  decide

private lemma eIdx_step (u v : ℕ) : eIdx (u + 1) v = eIdx u v + 1 := by
  unfold eIdx; omega

private lemma testBit_eq_false_of_shift_zero {n s i : ℕ} (h : n >>> s = 0) (hi : s ≤ i) :
    n.testBit i = false := by
  have h1 : (n >>> s).testBit (i - s) = false := by rw [h]; simp
  rw [Nat.testBit_shiftRight, show s + (i - s) = i by omega] at h1
  exact h1

private lemma testBit_lt_eight {c i : ℕ} (hc : c < 8) (hi : 3 ≤ i) : c.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  calc c < 8 := hc
    _ = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

private lemma getC_setC_self {bits u v c : ℕ} (hc : c < 8) (hzero : bits >>> (eIdx u v * 3) = 0) :
    getC (setC bits u v c) u v = c := by
  unfold getC setC
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 3
  · have h7 : (7 : ℕ).testBit i = true := by interval_cases i <;> decide
    have hb : bits.testBit (eIdx u v * 3 + i) = false := testBit_eq_false_of_shift_zero hzero (by omega)
    have hge : eIdx u v * 3 ≤ eIdx u v * 3 + i := by omega
    simp [h7, hb, hge, show eIdx u v * 3 + i - eIdx u v * 3 = i by omega]
  · have h7 : (7 : ℕ).testBit i = false := testBit_lt_eight (by norm_num) (by omega)
    have hc' : c.testBit i = false := testBit_lt_eight hc (by omega)
    simp [h7, hc']

private lemma getC_setC_of_lt {bits u' v' u v c : ℕ} (hlt : eIdx u' v' < eIdx u v) :
    getC (setC bits u v c) u' v' = getC bits u' v' := by
  unfold getC setC
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 3
  · have hge : ¬ (eIdx u v * 3 ≤ eIdx u' v' * 3 + i) := by omega
    simp [hge]
  · have h7 : (7 : ℕ).testBit i = false := testBit_lt_eight (by norm_num) (by omega)
    simp [h7]

private lemma setC_shift_zero {bits u v c k : ℕ} (hc : c < 8)
    (hzero : bits >>> (eIdx u v * 3) = 0) (hk : eIdx u v + 1 ≤ k) :
    setC bits u v c >>> (k * 3) = 0 := by
  unfold setC
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.zero_testBit]
  have hb : bits.testBit (k * 3 + i) = false := testBit_eq_false_of_shift_zero hzero (by omega)
  have hc' : c.testBit (k * 3 + i - eIdx u v * 3) = false := testBit_lt_eight hc (by omega)
  simp [hb, hc']

private lemma matchesPrefix_step {C : ℕ → ℕ → ℕ} {v u bits : ℕ}
    (hv : v < 9) (huv : u < v) (hC : C u v < 6) (hm : MatchesPrefix C v u bits) :
    MatchesPrefix C v (u + 1) (setC bits u v (C u v)) := by
  constructor
  · intro u' v' hu'v' hv' hbef
    rcases hbef with hlt | ⟨rfl, hu'lt⟩
    · have hidx := eIdx_lt_of_before ⟨u', by omega⟩ ⟨v', hv'⟩ ⟨u, by omega⟩ ⟨v, hv⟩ hu'v' huv (Or.inl hlt)
      rw [getC_setC_of_lt hidx]
      exact hm.1 u' v' hu'v' hv' (Or.inl hlt)
    · by_cases heq : u' = u
      · subst heq
        exact getC_setC_self (by omega) (hm.2 (eIdx u' v') (le_refl _))
      · have hu'lt' : u' < u := by omega
        have hidx := eIdx_lt_of_before ⟨u', by omega⟩ ⟨v', hv'⟩ ⟨u, by omega⟩ ⟨v', hv'⟩ hu'v' huv
          (Or.inr ⟨rfl, hu'lt'⟩)
        rw [getC_setC_of_lt hidx]
        exact hm.1 u' v' hu'v' hv' (Or.inr ⟨rfl, hu'lt'⟩)
  · intro k hk
    rw [eIdx_step] at hk
    exact setC_shift_zero (by omega) (hm.2 (eIdx u v) (le_refl _)) hk

private lemma matchesPrefix_rollover {C : ℕ → ℕ → ℕ} {v bits : ℕ} (hv : v < 8)
    (hm : MatchesPrefix C v v bits) :
    MatchesPrefix C (v + 1) 0 bits := by
  constructor
  · intro u' v' hu'v' hv' hbef
    have hbef' : v' < v ∨ (v' = v ∧ u' < v) := by omega
    exact hm.1 u' v' hu'v' hv' hbef'
  · intro k hk
    have he : eIdx 0 (v + 1) = eIdx v v := (eIdx_rollover ⟨v, hv⟩).symm
    exact hm.2 k (by rw [← he]; exact hk)

private lemma and_one_eq_one_of_testBit0 {n : ℕ} (h : n.testBit 0 = true) : (n &&& 1) = 1 := by
  rw [Nat.and_one_is_mod]
  rw [Nat.testBit_zero] at h
  have h1 : n % 2 = 1 := by simpa using h
  exact h1

private lemma filterTri_bit_one {C : ℕ → ℕ → ℕ} {bits v u : ℕ}
    (hv : v < 9) (huv : u < v) (hC_tri : ∀ a < u, ((triMask (C a u) (C a v) >>> C u v) &&& 1) = 1)
    (hm : MatchesPrefix C v u bits) :
    ∀ k ≤ u, ∀ mask, ((mask >>> C u v) &&& 1) = 1 →
      ((filterTri bits v u k mask >>> C u v) &&& 1) = 1 := by
  intro k
  induction k with
  | zero => intro _ mask hmask; exact hmask
  | succ k ih =>
    intro hk mask hmask
    unfold filterTri
    have hne : mask ≠ 0 := by
      intro hz; subst hz; simp at hmask
    simp only [beq_iff_eq, hne, ↓reduceIte]
    apply ih (by omega)
    have hgu : getC bits k u = C k u := hm.1 k u (by omega) (by omega) (Or.inl (by omega))
    have hgv : getC bits k v = C k v := hm.1 k v (by omega) hv (Or.inr ⟨rfl, by omega⟩)
    rw [hgu, hgv]
    have ht := hC_tri k (by omega)
    apply and_one_eq_one_of_testBit0
    have h1 : mask.testBit (C u v) = true := by
      have := congrArg (fun n => n.testBit 0) hmask; simpa using this
    have h2 : (triMask (C k u) (C k v)).testBit (C u v) = true := by
      have := congrArg (fun n => n.testBit 0) ht; simpa using this
    simp [Nat.testBit_and, h1, h2]

private lemma filterK4Inner_bit_one {C : ℕ → ℕ → ℕ} {bits v u a : ℕ}
    (hv : v < 9) (huv : u < v) (hau : a < u)
    (hC_k4 : ∀ b, a < b → b < u → ((k4Mask (C a b) (C a u) (C b u) (C a v) (C b v) >>> C u v) &&& 1) = 1)
    (hm : MatchesPrefix C v u bits) :
    ∀ k, a + k < u → ∀ mask, ((mask >>> C u v) &&& 1) = 1 →
      ((filterK4Inner bits v u a (C a u) (C a v) k mask >>> C u v) &&& 1) = 1 := by
  intro k
  induction k with
  | zero => intro _ mask hmask; exact hmask
  | succ k ih =>
    intro hk mask hmask
    unfold filterK4Inner
    have hne : mask ≠ 0 := by intro hz; subst hz; simp at hmask
    simp only [beq_iff_eq, hne, ↓reduceIte]
    apply ih (by omega)
    let b := a + 1 + k
    have hgab : getC bits a b = C a b := hm.1 a b (by omega) (by omega) (Or.inl (by omega))
    have hgbu : getC bits b u = C b u := hm.1 b u (by omega) (by omega) (Or.inl (by omega))
    have hgbv : getC bits b v = C b v := hm.1 b v (by omega) hv (Or.inr ⟨rfl, by omega⟩)
    rw [hgab, hgbu, hgbv]
    have hk4 := hC_k4 b (by omega) (by omega)
    apply and_one_eq_one_of_testBit0
    have h1 : mask.testBit (C u v) = true := by
      have := congrArg (fun n => n.testBit 0) hmask; simpa using this
    have h2 : (k4Mask (C a b) (C a u) (C b u) (C a v) (C b v)).testBit (C u v) = true := by
      have := congrArg (fun n => n.testBit 0) hk4; simpa using this
    simp [Nat.testBit_and, h1, h2]

private lemma filterK4_bit_one {C : ℕ → ℕ → ℕ} {bits v u : ℕ}
    (hv : v < 9) (huv : u < v)
    (hC_k4 : ∀ a b, a < b → b < u → ((k4Mask (C a b) (C a u) (C b u) (C a v) (C b v) >>> C u v) &&& 1) = 1)
    (hm : MatchesPrefix C v u bits) :
    ∀ k, k < u → ∀ mask, ((mask >>> C u v) &&& 1) = 1 →
      ((filterK4 bits v u k mask >>> C u v) &&& 1) = 1 := by
  intro k
  induction k with
  | zero => intro _ mask hmask; exact hmask
  | succ k ih =>
    intro hk mask hmask
    unfold filterK4
    have hne : mask ≠ 0 := by intro hz; subst hz; simp at hmask
    simp only [beq_iff_eq, hne, ↓reduceIte]
    apply ih (by omega)
    have hgau : getC bits k u = C k u := hm.1 k u (by omega) (by omega) (Or.inl (by omega))
    have hgav : getC bits k v = C k v := hm.1 k v (by omega) hv (Or.inr ⟨rfl, by omega⟩)
    rw [hgau, hgav]
    exact filterK4Inner_bit_one hv huv (by omega) (fun b hab hbu => hC_k4 k b hab hbu) hm
      (u - k - 1) (by omega) mask hmask

private lemma tryCols_sound {f : ℕ → Bool} {mask : ℕ} :
    ∀ n, tryCols f mask n = true → ∀ c < n, ((mask >>> c) &&& 1) = 1 → f c = true := by
  intro n
  induction n with
  | zero => intro _ c hc; omega
  | succ n ih =>
    intro h c hc hbit
    unfold tryCols at h
    simp only [Bool.and_eq_true] at h
    by_cases hcn : c = n
    · subst hcn; simpa [hbit] using h.1
    · exact ih h.2 c (by omega) hbit

private lemma initMask_bit_one {a b : ℕ} (ha : a < 6) (hb : b < 6) (hab : a ≤ b) :
    (((((63 >>> a) <<< a) &&& 63) >>> b) &&& 1) = 1 := by
  revert ha hb hab
  have h : ∀ a b : Fin 6, a.val ≤ b.val → (((((63 >>> a.val) <<< a.val) &&& 63) >>> b.val) &&& 1) = 1 := by
    decide
  intro ha hb hab
  exact h ⟨a, ha⟩ ⟨b, hb⟩ hab

private lemma fullMask_bit_one {b : ℕ} (hb : b < 6) : ((63 >>> b) &&& 1) = 1 := by
  have h : ∀ b : Fin 6, ((63 >>> b.val) &&& 1) = 1 := by decide
  exact h ⟨b, hb⟩

private theorem checkAll_sound {C : ℕ → ℕ → ℕ}
    (hC_lt : ∀ i j, i < j → j < 9 → C i j < 6)
    (hC_sort : ∀ v, 2 ≤ v → v < 9 → C 0 (v - 1) ≤ C 0 v)
    (hC_tri : ∀ a u v, a < u → u < v → v < 9 → ((triMask (C a u) (C a v) >>> C u v) &&& 1) = 1)
    (hC_k4 : ∀ a b u v, a < b → b < u → u < v → v < 9 →
      ((k4Mask (C a b) (C a u) (C b u) (C a v) (C b v) >>> C u v) &&& 1) = 1) :
    ∀ fuel v u bits, 1 ≤ v → v < 9 → u ≤ v →
      MatchesPrefix C v u bits → checkAll fuel v u bits = true →
      ∃ bits_full, MatchesPrefix C 8 8 bits_full ∧ leavesList.contains (toLeafCode bits_full) = true := by
  intro fuel
  induction fuel with
  | zero => intro v u bits _ _ _ _ hchk; simp [checkAll] at hchk
  | succ fuel ih =>
    intro v u bits hv1 hv9 huv hm hchk
    unfold checkAll at hchk
    by_cases heq : u = v
    · subst heq
      simp only [beq_self_eq_true, ↓reduceIte] at hchk
      by_cases hu8 : u = 8
      · subst hu8
        simp only [beq_self_eq_true, ↓reduceIte] at hchk
        exact ⟨bits, hm, hchk⟩
      · simp only [beq_iff_eq, hu8, ↓reduceIte] at hchk
        exact ih (u + 1) 0 bits (by omega) (by omega) (by omega) (matchesPrefix_rollover (by omega) hm) hchk
    · have huv_lt : u < v := by omega
      simp only [beq_iff_eq, heq, ↓reduceIte] at hchk
      set initMask := if u == 0 && v >= 2 then ((63 >>> getC bits 0 (v - 1)) <<< getC bits 0 (v - 1)) &&& 63 else 63
      have hinit : ((initMask >>> C u v) &&& 1) = 1 := by
        dsimp only [initMask]
        by_cases hcond : u = 0 ∧ 2 ≤ v
        · obtain ⟨rfl, hv2⟩ := hcond
          have hcond_b : ((0 == 0) && decide (v ≥ 2)) = true := by simp [hv2]
          simp only [hcond_b, ↓reduceIte]
          have hg0 : getC bits 0 (v - 1) = C 0 (v - 1) :=
            hm.1 0 (v - 1) (by omega) (by omega) (Or.inl (by omega))
          rw [hg0]
          exact initMask_bit_one (hC_lt 0 (v - 1) (by omega) (by omega))
            (hC_lt 0 v (by omega) hv9) (hC_sort v hv2 hv9)
        · have hcond_b : ((u == 0) && decide (v ≥ 2)) = false := by
            by_cases hu0 : u = 0
            · have hv2 : ¬ (2 ≤ v) := fun h => hcond ⟨hu0, h⟩
              simp [hu0, show ¬ (v ≥ 2) by omega]
            · simp [hu0]
          simp only [hcond_b, Bool.false_eq_true, ↓reduceIte]
          exact fullMask_bit_one (hC_lt u v huv_lt hv9)
      set m1 := filterTri bits v u u initMask
      have hm1_bit : ((m1 >>> C u v) &&& 1) = 1 :=
        filterTri_bit_one hv9 huv_lt (fun a ha => hC_tri a u v ha huv_lt hv9) hm u (le_refl u) initMask hinit
      have hm1_ne : m1 ≠ 0 := by intro hz; rw [hz] at hm1_bit; simp at hm1_bit
      simp only [beq_iff_eq, hm1_ne, ↓reduceIte] at hchk
      set m2 := if u >= 2 then filterK4 bits v u (u - 1) m1 else m1
      have hm2_bit : ((m2 >>> C u v) &&& 1) = 1 := by
        dsimp only [m2]
        split_ifs with hu2
        · exact filterK4_bit_one hv9 huv_lt (fun a b hab hbu => hC_k4 a b u v hab hbu huv_lt hv9)
            hm (u - 1) (by omega) m1 hm1_bit
        · exact hm1_bit
      have hm2_ne : m2 ≠ 0 := by intro hz; rw [hz] at hm2_bit; simp at hm2_bit
      simp only [beq_iff_eq, hm2_ne, ↓reduceIte] at hchk
      have hnext := tryCols_sound 6 hchk (C u v) (hC_lt u v huv_lt hv9) hm2_bit
      exact ih v (u + 1) (setC bits u v (C u v)) hv1 hv9 (by omega)
        (matchesPrefix_step hv9 huv_lt (hC_lt u v huv_lt hv9) hm) hnext

/-! ## Section 3: Base-6 Leaf Decoding, Witness Isomorphism, and Row-0 Sorting -/

private def base6Of : List ℕ → ℕ → ℕ
  | [], acc => acc
  | d :: ds, acc => base6Of ds (acc * 6 + d)

private lemma base6Of_eq (ds : List ℕ) (acc : ℕ) :
    base6Of ds acc = acc * 6 ^ ds.length + base6Of ds 0 := by
  induction ds generalizing acc with
  | nil => simp [base6Of]
  | cons d ds ih =>
    simp only [base6Of, List.length_cons, zero_mul, zero_add]
    rw [ih (acc * 6 + d), ih d]
    ring

private lemma base6Of_lt (ds : List ℕ) (hd : ∀ x ∈ ds, x < 6) :
    base6Of ds 0 < 6 ^ ds.length := by
  induction ds with
  | nil => simp [base6Of]
  | cons d ds ih =>
    simp only [base6Of, List.length_cons, zero_mul, zero_add]
    rw [base6Of_eq]
    have hd0 : d < 6 := hd d List.mem_cons_self
    have ih' := ih (fun x hx => hd x (List.mem_cons_of_mem d hx))
    calc d * 6 ^ ds.length + base6Of ds 0 < d * 6 ^ ds.length + 6 ^ ds.length := by omega
      _ = (d + 1) * 6 ^ ds.length := by ring
      _ ≤ 6 * 6 ^ ds.length := Nat.mul_le_mul_right _ (by omega)
      _ = 6 ^ (ds.length + 1) := by rw [pow_succ']

private lemma base6Of_extract (ds : List ℕ) (hd : ∀ x ∈ ds, x < 6) :
    ∀ k (hk : k < ds.length), (base6Of ds 0 / 6 ^ (ds.length - 1 - k)) % 6 = ds[k] := by
  induction ds with
  | nil => intro k hk; simp at hk
  | cons d ds ih =>
    intro k hk
    have hd0 : d < 6 := hd d List.mem_cons_self
    have hds : ∀ x ∈ ds, x < 6 := fun x hx => hd x (List.mem_cons_of_mem d hx)
    simp only [base6Of, zero_mul, zero_add, List.length_cons]
    rw [base6Of_eq]
    cases k with
    | zero =>
      simp only [Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
      have hlt := base6Of_lt ds hds
      have hpos : 0 < 6 ^ ds.length := by positivity
      rw [mul_comm d _, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, add_zero, Nat.mod_eq_of_lt hd0]
    | succ k' =>
      simp only [Nat.add_sub_cancel, List.getElem_cons_succ]
      have hk' : k' < ds.length := by simp at hk; omega
      have hpow : 6 ^ ds.length = 6 ^ (ds.length - 1 - k') * 6 ^ (k' + 1) := by
        rw [← pow_add]; congr 1; omega
      have hpos : 0 < 6 ^ (ds.length - 1 - k') := by positivity
      have hdiv : (d * 6 ^ ds.length + base6Of ds 0) / 6 ^ (ds.length - 1 - k') =
          d * 6 ^ (k' + 1) + base6Of ds 0 / 6 ^ (ds.length - 1 - k') := by
        rw [hpow, show d * (6 ^ (ds.length - 1 - k') * 6 ^ (k' + 1)) =
            6 ^ (ds.length - 1 - k') * (d * 6 ^ (k' + 1)) by ring, Nat.mul_add_div hpos]
      have hshow : ds.length - (k' + 1) = ds.length - 1 - k' := by omega
      rw [hshow, hdiv]
      have hmod6 : (d * 6 ^ (k' + 1) + base6Of ds 0 / 6 ^ (ds.length - 1 - k')) % 6 =
          (base6Of ds 0 / 6 ^ (ds.length - 1 - k')) % 6 := by
        rw [pow_succ, show d * (6 ^ k' * 6) = 6 * (d * 6 ^ k') by ring, Nat.mul_add_mod]
      rw [hmod6]
      exact ih hds k' hk'

private def lexPairs : List (ℕ × ℕ) :=
  (List.range 9).flatMap fun i => ((List.range 9).filter (i < ·)).map fun j => (i, j)

private lemma toLeafCode_eq_base6Of (bits : ℕ) :
    toLeafCode bits = base6Of (lexPairs.map fun p => getC bits p.1 p.2) 0 := by
  have h1 : lexPairs =
      [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),
       (1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),
       (2,3),(2,4),(2,5),(2,6),(2,7),(2,8),
       (3,4),(3,5),(3,6),(3,7),(3,8),
       (4,5),(4,6),(4,7),(4,8),
       (5,6),(5,7),(5,8),
       (6,7),(6,8),
       (7,8)] := by decide
  rw [h1]
  rfl

private lemma lexPairs_getElem_lexIdx :
    ∀ i j : Fin 9, i.val < j.val →
      lexIdx i.val j.val < lexPairs.length ∧ lexPairs[lexIdx i.val j.val]! = (i.val, j.val) := by
  decide

private lemma lexPairs_len : lexPairs.length = 36 := by decide

private lemma getLexEdge_toLeafCode {C : ℕ → ℕ → ℕ} {bits : ℕ}
    (hC_sym : ∀ i j, C i j = C j i)
    (hC_lt : ∀ i j, i < j → j < 9 → C i j < 6)
    (hm : MatchesPrefix C 8 8 bits) :
    ∀ i j : Fin 9, i ≠ j → getLexEdge (toLeafCode bits) i.val j.val = C i.val j.val := by
  intro i j hij
  have hget : ∀ a b, a < b → b < 9 → getC bits a b = C a b := fun a b hab hb9 =>
    hm.1 a b hab hb9 (by omega)
  have hds_lt : ∀ x ∈ (lexPairs.map fun p => getC bits p.1 p.2), x < 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hp_ok : ∀ q ∈ lexPairs, q.1 < q.2 ∧ q.2 < 9 := by decide
    obtain ⟨h1, h2⟩ := hp_ok p hp
    rw [hget p.1 p.2 h1 h2]
    exact hC_lt p.1 p.2 h1 h2
  have hlen : (lexPairs.map fun p => getC bits p.1 p.2).length = 36 := by
    rw [List.length_map, lexPairs_len]
  unfold getLexEdge
  set a := min i.val j.val
  set b := max i.val j.val
  have hab : a < b := by
    have : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  have hb9 : b < 9 := by omega
  have hidx := lexPairs_getElem_lexIdx ⟨a, by omega⟩ ⟨b, hb9⟩ hab
  rw [toLeafCode_eq_base6Of]
  have hidx_map : lexIdx a b < (lexPairs.map fun p => getC bits p.1 p.2).length := by
    rw [hlen, ← lexPairs_len]; exact hidx.1
  have hext := base6Of_extract (lexPairs.map fun p => getC bits p.1 p.2) hds_lt (lexIdx a b) hidx_map
  have hlen35 : (lexPairs.map fun p => getC bits p.1 p.2).length - 1 - lexIdx a b = 35 - lexIdx a b := by
    rw [hlen]
  rw [hlen35] at hext
  rw [hext]
  have hgetElem : (lexPairs.map fun p => getC bits p.1 p.2)[lexIdx a b]'hidx_map =
      getC bits (lexPairs[lexIdx a b]'hidx.1).1 (lexPairs[lexIdx a b]'hidx.1).2 := by
    rw [List.getElem_map]
  rw [hgetElem]
  have hpair : lexPairs[lexIdx a b]'hidx.1 = (a, b) := by
    have hbang := hidx.2
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hidx.1] at hbang
    exact hbang
  rw [hpair, hget a b hab hb9]
  rcases lt_or_gt_of_ne (fun h : i.val = j.val => hij (Fin.ext h)) with h | h
  · have ha : a = i.val := min_eq_left h.le
    have hb : b = j.val := max_eq_right h.le
    rw [ha, hb]
  · have ha : a = j.val := min_eq_right h.le
    have hb : b = i.val := max_eq_left h.le
    rw [ha, hb, hC_sym]

/-- Sort indices `1..8` by row 0 of `C` via an explicit permutation fixing `0`. -/
private lemma exists_sort_row0 (C : Fin 9 → Fin 9 → ℕ) :
    ∃ π : Equiv.Perm (Fin 9), π 0 = 0 ∧
      ∀ v : ℕ, 2 ≤ v → (hv : v < 9) → C 0 (π ⟨v - 1, by omega⟩) ≤ C 0 (π ⟨v, hv⟩) := by
  let g : Fin 8 → ℕ := fun k => C 0 k.succ
  let π8 : Equiv.Perm (Fin 8) := Tuple.sort g
  let toFun : Fin 9 → Fin 9 := fun i =>
    if h : i = 0 then 0 else (π8 (i.pred h)).succ
  let invFun : Fin 9 → Fin 9 := fun i =>
    if h : i = 0 then 0 else (π8.symm (i.pred h)).succ
  have hleft : Function.LeftInverse invFun toFun := by
    intro i
    dsimp only [toFun, invFun]
    by_cases h : i = 0
    · simp [h]
    · simp only [h, ↓reduceDIte, Fin.succ_ne_zero, Fin.pred_succ, Equiv.symm_apply_apply, Fin.succ_pred]
  have hright : Function.RightInverse invFun toFun := by
    intro i
    dsimp only [toFun, invFun]
    by_cases h : i = 0
    · simp [h]
    · simp only [h, ↓reduceDIte, Fin.succ_ne_zero, Fin.pred_succ, Equiv.apply_symm_apply, Fin.succ_pred]
  refine ⟨⟨toFun, invFun, hleft, hright⟩, by simp [toFun], ?_⟩
  intro v hv2 hv9
  have h1 : (⟨v - 1, by omega⟩ : Fin 9) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
  have h2 : (⟨v, hv9⟩ : Fin 9) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
  have hmono := Tuple.monotone_sort g
  have hle : (⟨v - 1, by omega⟩ : Fin 9).pred h1 ≤ (⟨v, hv9⟩ : Fin 9).pred h2 := by
    simp [Fin.le_def, Fin.pred]
  have hres := hmono hle
  simpa [Equiv.coe_fn_mk, toFun, h1, h2, g, Function.comp] using hres

private lemma nodeOfN_symm_fin : ∀ i j : Fin 9, nodeOfN i.val j.val = nodeOfN j.val i.val := by
  decide

/-- Build an `Equiv.Perm (Fin 9)` from a verified witness `(code, p) ∈ leafWitnesses`. -/
private lemma perm_of_witness {code : ℕ} {p : List ℕ}
    (hw : checkWitness (code, p) = true) :
    ∃ τ : Equiv.Perm (Fin 9), ∀ i j : Fin 9, i ≠ j →
      getLexEdge code (τ i).val (τ j).val = nodeOfN i.val j.val := by
  unfold checkWitness at hw
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨hlen, hsurj⟩, hedge⟩ := hw
  have hmem_lt : ∀ i : Fin 9, p.getD i.val 0 < 9 := by
    intro i
    have hi : i.val < p.length := by omega
    have hmem : p[i.val]'hi ∈ p := List.getElem_mem hi
    -- Every element of p must be < 9 because p has length 9 and contains all of 0..8
    have hnodup_range : (List.range 9).Nodup := List.nodup_range
    have hsub : List.range 9 ⊆ p := fun k hk => by
      have := List.all_eq_true.mp hsurj k hk
      simpa using this
    have hperm : List.Perm (List.range 9) p := by
      have hsub_toFinset : (List.range 9).toFinset ⊆ p.toFinset := by
        intro x hx; exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hx))
      have hcard_r : (List.range 9).toFinset.card = 9 := by
        rw [List.toFinset_card_of_nodup hnodup_range, List.length_range]
      have hcard_p : p.toFinset.card ≤ 9 := by
        calc p.toFinset.card ≤ p.length := List.toFinset_card_le p
          _ = 9 := hlen
      have heq_set : (List.range 9).toFinset = p.toFinset :=
        Finset.eq_of_subset_of_card_le hsub_toFinset (by omega)
      have hlt_all : p.Nodup := by
        have hded_len : p.dedup.length = p.length := by
          rw [← List.card_toFinset, ← heq_set, hcard_r, hlen]
        have hded : p.dedup = p := (List.dedup_sublist p).eq_of_length hded_len
        exact hded ▸ List.nodup_dedup p
      exact (List.perm_ext_iff_of_nodup hnodup_range hlt_all).mpr fun x => by
        rw [← List.mem_toFinset, ← List.mem_toFinset, heq_set]
    have hmem_r : p[i.val]'hi ∈ List.range 9 := hperm.symm.subset hmem
    rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_range.mp hmem_r
  let f : Fin 9 → Fin 9 := fun i => ⟨p.getD i.val 0, hmem_lt i⟩
  have hf_surj : Function.Surjective f := by
    intro k
    have hk : k.val ∈ p := by
      have := List.all_eq_true.mp hsurj k.val (List.mem_range.mpr k.isLt)
      simpa using this
    obtain ⟨idx, hidx, hval⟩ := List.getElem_of_mem hk
    refine ⟨⟨idx, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp only [f]
    rw [List.getD_eq_getElem _ _ hidx, hval]
  have hf_bij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hf_surj, hf_surj⟩
  refine ⟨Equiv.ofBijective f hf_bij, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h1 := List.all_eq_true.mp hedge i.val (List.mem_range.mpr i.isLt)
    have h2 := List.all_eq_true.mp h1 j.val (List.mem_range.mpr j.isLt)
    have hlt' : i.val < j.val := hlt
    simp only [hlt', ↓reduceIte, beq_iff_eq] at h2
    exact h2
  · have h1 := List.all_eq_true.mp hedge j.val (List.mem_range.mpr j.isLt)
    have h2 := List.all_eq_true.mp h1 i.val (List.mem_range.mpr i.isLt)
    have hgt' : j.val < i.val := hgt
    simp only [hgt', ↓reduceIte, beq_iff_eq] at h2
    have hsym_lex : ∀ a b : ℕ, getLexEdge code a b = getLexEdge code b a := fun a b => by
      unfold getLexEdge; rw [min_comm, max_comm]
    rw [hsym_lex, Equiv.ofBijective_apply, Equiv.ofBijective_apply]
    simpa [f, nodeOfN_symm_fin j i] using h2

/-! ## Section 4: Main Theorem `rigidity_to_ball` -/

/-- **Main Stage B L4 + L5 Rigidity-to-Ball Theorem**:
If `x : Fin 9 → R3` is a unit-sphere configuration satisfying `TubePremise (toMat x) z (1/10000)`
for some `z ∈ [zLo, zHi]`, then there exist a vertex permutation `σ : Equiv.Perm (Fin 9)` and an
orthogonal `3×3` matrix `Q ∈ orthogonalGroup (Fin 3) ℝ` such that
`frob (ttpX z - rowPerm (toMat x) σ * Q) ≤ 1 / 500`. -/
theorem rigidity_to_ball (x : Fin 9 → R3) (hu : ∀ i, ‖x i‖ = 1)
    (z : ℝ) (hzLo : (TableB5Data.zLo : ℝ) ≤ z) (hzHi : z ≤ (TableB5Data.zHi : ℝ))
    (hTube : TubePremise (toMat x) z (1 / 10000)) :
    ∃ (σ : Equiv.Perm (Fin 9)) (Q : Matrix (Fin 3) (Fin 3) ℝ),
      Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧
      frob (ttpX z - rowPerm (toMat x) σ * Q) ≤ 1 / 500 := by
  have hρid : (1 / 10000 : ℝ) < (gMin : ℝ) / 2 := by
    have h : ((1 / 10000 : ℚ) : ℝ) < ((gMin / 2 : ℚ) : ℝ) := by
      exact_mod_cast (show (1 / 10000 : ℚ) < gMin / 2 by norm_num [gMin])
    simpa using h
  have hρA : (1 / 10000 : ℝ) ≤ (deltaA : ℝ) := by
    have h : ((1 / 10000 : ℚ) : ℝ) ≤ (deltaA : ℝ) := by
      exact_mod_cast (show (1 / 10000 : ℚ) ≤ deltaA by norm_num [deltaA, l3, sqrt72Up])
    simpa using h
  -- Total coloring C0 : Fin 9 → Fin 9 → ℕ via identNode
  let C0 : Fin 9 → Fin 9 → ℕ := fun i j =>
    if h : i = j then 0 else identNode hTube i j h
  have hC0_lt : ∀ i j : Fin 9, i ≠ j → C0 i j < 6 := fun i j hij => by
    dsimp only [C0]; simp only [hij, ↓reduceDIte]; exact (identNode_spec hTube i j hij).1
  have hC0_hit : ∀ i j : Fin 9, i ≠ j →
      |⟪x i, x j⟫ - nuOfN (C0 i j) z| ≤ 1 / 10000 := fun i j hij => by
    dsimp only [C0]; simp only [hij, ↓reduceDIte]
    rw [← toMat_dot]; exact (identNode_spec hTube i j hij).2
  have hC0_sym : ∀ i j : Fin 9, C0 i j = C0 j i := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · have hji : j ≠ i := Ne.symm hij
      dsimp only [C0]; simp only [hij, hji, ↓reduceDIte]
      have hhit := (identNode_spec hTube i j hij).2
      rw [toMat_dot, real_inner_comm, ← toMat_dot] at hhit
      exact identNode_unique hTube hzLo hzHi hρid j i hji (identNode hTube i j hij)
        (identNode_spec hTube i j hij).1 hhit
  -- Sort row 0 using π : Equiv.Perm (Fin 9)
  obtain ⟨π, hπ0, hπ_sort⟩ := exists_sort_row0 C0
  let y : Fin 9 → R3 := fun i => x (π i)
  have hyu : ∀ i, ‖y i‖ = 1 := fun i => hu (π i)
  let C : ℕ → ℕ → ℕ := fun i j =>
    if h : i < 9 ∧ j < 9 then C0 (π ⟨i, h.1⟩) (π ⟨j, h.2⟩) else 0
  have hC_sym : ∀ i j, C i j = C j i := by
    intro i j; dsimp only [C]
    by_cases h : i < 9 ∧ j < 9
    · have h' : j < 9 ∧ i < 9 := ⟨h.2, h.1⟩
      simp only [h, h', ↓reduceDIte]; exact hC0_sym _ _
    · have h' : ¬ (j < 9 ∧ i < 9) := fun ⟨a, b⟩ => h ⟨b, a⟩
      simp only [h, h', ↓reduceDIte]
  have hC_lt : ∀ i j, i < j → j < 9 → C i j < 6 := fun i j hij hj9 => by
    dsimp only [C]
    have h : i < 9 ∧ j < 9 := ⟨by omega, hj9⟩
    simp only [h, ↓reduceDIte]
    exact hC0_lt _ _ (fun hc => by have := π.injective hc; simp [Fin.ext_iff] at this; omega)
  have hC_sort : ∀ v, 2 ≤ v → v < 9 → C 0 (v - 1) ≤ C 0 v := fun v hv2 hv9 => by
    dsimp only [C]
    have h1 : 0 < 9 ∧ v - 1 < 9 := ⟨by omega, by omega⟩
    have h2 : 0 < 9 ∧ v < 9 := ⟨by omega, hv9⟩
    simp only [h1, h2, ↓reduceDIte]
    have := hπ_sort v hv2 hv9
    simpa [hπ0] using this
  have hC_iv : ∀ i j : Fin 9, i ≠ j → (nodeIv (C i.val j.val)).inR (100000 * ⟪y i, y j⟫) := by
    intro i j hij
    have h : i.val < 9 ∧ j.val < 9 := ⟨i.isLt, j.isLt⟩
    have hCeq : C i.val j.val = C0 (π i) (π j) := by dsimp only [C]; simp [h]
    rw [hCeq]
    have hne : π i ≠ π j := fun hc => hij (π.injective hc)
    exact nodeIv_mem_of_hit hzLo hzHi (hC0_lt _ _ hne) (hC0_hit _ _ hne)
  have hC_tri : ∀ a u v, a < u → u < v → v < 9 →
      ((triMask (C a u) (C a v) >>> C u v) &&& 1) = 1 := by
    intro a u v hau huv hv9
    exact tri_mask_bit_one (hC_lt a u hau (by omega)) (hC_lt a v (by omega) hv9) (hC_lt u v huv hv9)
      (hyu ⟨a, by omega⟩) (hyu ⟨u, by omega⟩) (hyu ⟨v, hv9⟩)
      (hC_iv ⟨a, by omega⟩ ⟨u, by omega⟩ (by simp [Fin.ext_iff]; omega))
      (hC_iv ⟨a, by omega⟩ ⟨v, hv9⟩ (by simp [Fin.ext_iff]; omega))
      (hC_iv ⟨u, by omega⟩ ⟨v, hv9⟩ (by simp [Fin.ext_iff]; omega))
  have hC_k4 : ∀ a b u v, a < b → b < u → u < v → v < 9 →
      ((k4Mask (C a b) (C a u) (C b u) (C a v) (C b v) >>> C u v) &&& 1) = 1 := by
    intro a b u v hab hbu huv hv9
    exact k4_mask_bit_one (hC_lt a b hab (by omega)) (hC_lt a u (by omega) (by omega))
      (hC_lt b u hbu (by omega)) (hC_lt a v (by omega) hv9) (hC_lt b v (by omega) hv9) (hC_lt u v huv hv9)
      (hyu ⟨a, by omega⟩) (hyu ⟨b, by omega⟩) (hyu ⟨u, by omega⟩) (hyu ⟨v, hv9⟩)
      (hC_iv ⟨a, by omega⟩ ⟨b, by omega⟩ (by simp [Fin.ext_iff]; omega))
      (hC_iv ⟨a, by omega⟩ ⟨u, by omega⟩ (by simp [Fin.ext_iff]; omega))
      (hC_iv ⟨b, by omega⟩ ⟨u, by omega⟩ (by simp [Fin.ext_iff]; omega))
      (hC_iv ⟨a, by omega⟩ ⟨v, hv9⟩ (by simp [Fin.ext_iff]; omega))
      (hC_iv ⟨b, by omega⟩ ⟨v, hv9⟩ (by simp [Fin.ext_iff]; omega))
      (hC_iv ⟨u, by omega⟩ ⟨v, hv9⟩ (by simp [Fin.ext_iff]; omega))
  -- Run kernel-verified DFS soundness!
  have hm0 : MatchesPrefix C 1 0 0 := ⟨fun _ _ _ _ h => by omega, fun k _ => by simp⟩
  obtain ⟨bits_full, hm_full, hmem_leaves⟩ :=
    checkAll_sound hC_lt hC_sort hC_tri hC_k4 46 1 0 0 (by omega) (by omega) (by omega) hm0 l4_k9_complete
  -- Extract matching witness `(code, p) ∈ leafWitnesses`
  have hmem_list : toLeafCode bits_full ∈ leavesList := by simpa using hmem_leaves
  unfold leavesList at hmem_list
  rw [List.mem_map] at hmem_list
  obtain ⟨⟨code, p⟩, hw_mem, hcode_eq⟩ := hmem_list
  dsimp only at hcode_eq
  have hw_ok : checkWitness (code, p) = true := List.all_eq_true.mp leaves_iso_ok (code, p) hw_mem
  obtain ⟨τ, hτ⟩ := perm_of_witness hw_ok
  -- Compose σ := π * τ (so σ i = π (τ i))
  let σ : Equiv.Perm (Fin 9) := τ.trans π
  have hpat : PatternCons (toMat x) z (1 / 10000) σ := by
    intro _ i j hij
    have hτne : τ i ≠ τ j := fun hc => hij (τ.injective hc)
    have hlex := hτ i j hij
    rw [hcode_eq, getLexEdge_toLeafCode hC_sym hC_lt hm_full (τ i) (τ j) hτne] at hlex
    have hCeq : C (τ i).val (τ j).val = C0 (σ i) (σ j) := by
      dsimp only [C, σ, Equiv.trans_apply]
      have h : (τ i).val < 9 ∧ (τ j).val < 9 := ⟨(τ i).isLt, (τ j).isLt⟩
      simp [h]
    rw [hCeq] at hlex
    rw [toMat_dot, ← hlex]
    exact hC0_hit (σ i) (σ j) (fun hc => hij (σ.injective hc))
  -- Invoke `TableB5Chain.chain_convert_A` + `coeffA_le_CAhi`!
  obtain ⟨Q, hQmem, hQfrob⟩ := chain_convert_A z hzLo hzHi (1 / 10000) (by norm_num)
    (toMat x) (toMat_unit x hu) hTube σ hpat hρid hρA
  have hz1 := z_box_sq_le_one z hzLo hzHi
  have hgram : ∀ i j : Fin 9, i ≠ j →
      |rowPerm (toMat x) σ i ⬝ᵥ rowPerm (toMat x) σ j - (ttpX z) i ⬝ᵥ (ttpX z) j| ≤ 1 / 10000 := by
    intro i j hij
    rw [rowPerm_dot, ttpX_gram_nodeOfN z hz1 i j hij]
    exact hpat hTube i j hij
  have heta := eta_le_sqrt72 (ttpX z) (rowPerm (toMat x) σ) (1 / 10000)
    (ttpX_diag_one z hz1) (rowPerm_unit (toMat_unit x hu) σ) hgram (by norm_num)
  have h72 : frob (rowPerm (toMat x) σ * (rowPerm (toMat x) σ)ᵀ - (ttpX z) * (ttpX z)ᵀ) ≤
      (sqrt72Up : ℝ) * (1 / 10000) := by
    have hs := sqrt72_le_sqrt72Up
    linarith [mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 1 / 10000)]
  have hcoeff_nn : (0 : ℝ) ≤ Real.sqrt (u1 : ℝ) * (u1 : ℝ) / (l3 : ℝ) ^ 2
      + 2 * Real.sqrt 2 / Real.sqrt (l3 : ℝ) := by
    refine add_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by norm_num [u1])) (by positivity))
      (div_nonneg (by positivity) (Real.sqrt_nonneg _))
  have h1 : frob (ttpX z - rowPerm (toMat x) σ * Q) ≤ (CAhi : ℝ) * (1 / 10000) := by
    have hmul := mul_le_mul_of_nonneg_left h72 hcoeff_nn
    have hCA := coeffA_le_CAhi
    have hmul2 : ((Real.sqrt (u1 : ℝ) * (u1 : ℝ) / (l3 : ℝ) ^ 2 + 2 * Real.sqrt 2 / Real.sqrt (l3 : ℝ))
        * (sqrt72Up : ℝ)) * (1 / 10000) ≤ (CAhi : ℝ) * (1 / 10000) :=
      mul_le_mul_of_nonneg_right hCA (by norm_num)
    linarith
  have hCA_bound : (CAhi : ℝ) * (1 / 10000) ≤ 1 / 500 := by
    have h : ((CAhi * (1 / 10000 : ℚ) : ℚ) : ℝ) ≤ ((1 / 500 : ℚ) : ℝ) := by
      exact_mod_cast (show CAhi * (1 / 10000 : ℚ) ≤ 1 / 500 by norm_num [CAhi])
    simpa using h
  exact ⟨σ, Q, hQmem, le_trans h1 hCA_bound⟩

end ThomsonN9.StageB.RigidityL4
