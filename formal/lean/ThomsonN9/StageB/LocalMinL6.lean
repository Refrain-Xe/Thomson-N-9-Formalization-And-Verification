import ThomsonN9.StageB.LocalMinL6Data
import ThomsonN9.StageB.ThreePoint
import ThomsonN9.StageB.SlabCert
import ThomsonN9.TableA
import ThomsonN9.TableB5Chain

/-!
# Thomson N = 9 Stage B — Module 6: Strict Local Minimality & Uniqueness (`L6`)

Proves:
1. `exists_z_star`: existence of the exact critical parameter `z* ∈ [zStarLo, zStarHi] ⊂ [zLo, zHi] ⊂ (0, 1)`
   with `critGap z* = 0` and `coulombEnergy9 (ttpPt z*) ≤ E_ttp_hi`.
2. `ttp_critical`: exact `D₃h` force-balance criticality at `z*`.
3. `breg_ge_quad`: Bregman quadratic lower bound via `TableA.hasDerivAt_phiDeriv`.
4. `exists_gauge`: Procrustes gauge lemma (`∑ᵢ Pᵢ ⊗ g(yᵢ)` symmetric without increasing `ℓ²` distance).
5. `hessian_lower_bound`: strict coercivity of the `27 × 27` penalized Bregman Hessian certified by
   `LocalMinL6Data.H_iv_ok` and `LocalMinL6Data.H_chol_ok`.
6. `local_min_ball`: every injective unit-sphere configuration `y` with `∑ᵢ ‖y i - ttpPt z* i‖² ≤ (1/500)²`
   satisfies `coulombEnergy9 (ttpPt z*) ≤ coulombEnergy9 y`, with equality iff `y` is an `O(3)`-image of `ttpPt z*`.
7. `iso_of_orthogonal`: exact bridge from `Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ` and `frob` distance
   to `R3 ≃ₗᵢ[ℝ] R3` and `∑ᵢ ‖g (x (σ i)) - ttpPt z* i‖²`.
-/

set_option maxHeartbeats 12000000

namespace ThomsonN9.StageB.LocalMinL6

open Finset Matrix ThomsonN9.StageB ThomsonN9.StageB.LocalMinL6Data ThomsonN9.StageB.SlabCert
open ThomsonN9.TableA ThomsonN9.TableB1 ThomsonN9.TableB1Data ThomsonN9.TableB5Data
open ThomsonN9.TableB5Core ThomsonN9.TableB5Chain
open scoped RealInnerProductSpace Matrix

/-! ## Section 1: `ttpPt`, Cylindrical Equivalence, and `phiVal` -/

/-- The 9 TTP vertices in `R3`, defined directly from `TableB5Core.ttpX`. -/
noncomputable def ttpPt (z : ℝ) : Fin 9 → R3 :=
  fun i => WithLp.toLp 2 (fun j : Fin 3 => ttpX z i j)

private def toMat (x : Fin 9 → R3) : Matrix (Fin 9) (Fin 3) ℝ := fun i j => x i j

private lemma toMat_dot (x : Fin 9 → R3) (i j : Fin 9) :
    toMat x i ⬝ᵥ toMat x j = ⟪x i, x j⟫ := by
  rw [inner_R3_expand]
  simp [toMat, dotProduct, Fin.sum_univ_three]

private lemma sum_univ_nine {α : Type*} [AddCommMonoid α] (f : Fin 9 → α) :
    ∑ i : Fin 9, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  abel

private lemma nodeOfN_symm_fin : ∀ i j : Fin 9, nodeOfN i.val j.val = nodeOfN j.val i.val := by
  decide

lemma toMat_ttpPt (z : ℝ) : toMat (ttpPt z) = ttpX z := by
  ext i j; rfl

lemma ttpPt_norm (z : ℝ) (hz : z ^ 2 ≤ 1) (i : Fin 9) : ‖ttpPt z i‖ = 1 := by
  have h1 := ttpX_diag_one z hz i
  have h2 : ‖ttpPt z i‖ ^ 2 = 1 := by
    rw [norm_sq_R3_expand]
    simpa [ttpPt, dotProduct, Fin.sum_univ_three, sq] using h1
  nlinarith [norm_nonneg (ttpPt z i)]

lemma ttpPt_inner (z : ℝ) (hz : z ^ 2 ≤ 1) (i j : Fin 9) (hij : i ≠ j) :
    ⟪ttpPt z i, ttpPt z j⟫ = nuOfN (nodeOfN i.val j.val) z := by
  rw [← toMat_dot, toMat_ttpPt]
  exact ttpX_gram_nodeOfN z hz i j hij

/-- Exact trig values bridging cylindrical `triCapPrism` coordinates to `ttpPt`. -/
lemma cyl_triCapPrism_eq_ttpPt (z : ℝ) (i : Fin 9) :
    (if (i : ℕ) < 3 then !₂[Real.sqrt (1 - z ^ 2) * Real.cos (2 * Real.pi * (i : ℕ) / 3),
                            Real.sqrt (1 - z ^ 2) * Real.sin (2 * Real.pi * (i : ℕ) / 3), z]
     else if (i : ℕ) < 6 then !₂[Real.sqrt (1 - z ^ 2) * Real.cos (2 * Real.pi * ((i : ℕ) - 3) / 3),
                                 Real.sqrt (1 - z ^ 2) * Real.sin (2 * Real.pi * ((i : ℕ) - 3) / 3), -z]
     else !₂[(1 : ℝ) * Real.cos (Real.pi / 3 + 2 * Real.pi * ((i : ℕ) - 6) / 3),
             (1 : ℝ) * Real.sin (Real.pi / 3 + 2 * Real.pi * ((i : ℕ) - 6) / 3), 0] : R3) =
    ttpPt z i := by
  have hc23 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hs23 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hc43 : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
    rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_three]
  have hs43 : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.sin_add_pi, Real.sin_pi_div_three]
  have hc43' : Real.cos (Real.pi * (4 / 3)) = -(1 / 2) := by
    rw [show Real.pi * (4 / 3) = 4 * Real.pi / 3 by ring]; exact hc43
  have hs43' : Real.sin (Real.pi * (4 / 3)) = -(Real.sqrt 3 / 2) := by
    rw [show Real.pi * (4 / 3) = 4 * Real.pi / 3 by ring]; exact hs43
  have hc53 : Real.cos (5 * Real.pi / 3) = 1 / 2 := by
    rw [show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_two_pi_sub, Real.cos_pi_div_three]
  have hs53 : Real.sin (5 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    rw [show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 by ring, Real.sin_two_pi_sub, Real.sin_pi_div_three]
  have hc53' : Real.cos (Real.pi * (5 / 3)) = 1 / 2 := by
    rw [show Real.pi * (5 / 3) = 5 * Real.pi / 3 by ring]; exact hc53
  have hs53' : Real.sin (Real.pi * (5 / 3)) = -(Real.sqrt 3 / 2) := by
    rw [show Real.pi * (5 / 3) = 5 * Real.pi / 3 by ring]; exact hs53
  fin_cases i
  · ext a; fin_cases a <;>
      simp [ttpPt, ttpX, ttpRow, rhoR, s3R, Real.cos_zero, Real.sin_zero]
  · ext a; fin_cases a <;>
      simp [ttpPt, ttpX, ttpRow, rhoR, s3R, hc23, hs23] <;> ring
  · rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 3) = 4 * Real.pi / 3 by push_cast; ring, hc43, hs43]
    ext a; fin_cases a <;> simp [ttpPt, ttpX, ttpRow, rhoR, s3R] <;> ring
  · rw [show (2 * Real.pi * (((3 : ℕ) : ℝ) - 3) / 3) = 0 by push_cast; ring, Real.cos_zero, Real.sin_zero]
    ext a; fin_cases a <;> simp [ttpPt, ttpX, ttpRow, rhoR, s3R]
  · rw [show (2 * Real.pi * (((4 : ℕ) : ℝ) - 3) / 3) = 2 * Real.pi / 3 by push_cast; ring, hc23, hs23]
    ext a; fin_cases a <;> simp [ttpPt, ttpX, ttpRow, rhoR, s3R] <;> ring
  · rw [show (2 * Real.pi * (((5 : ℕ) : ℝ) - 3) / 3) = 4 * Real.pi / 3 by push_cast; ring, hc43, hs43]
    ext a; fin_cases a <;> simp [ttpPt, ttpX, ttpRow, rhoR, s3R] <;> ring
  · rw [show (Real.pi / 3 + 2 * Real.pi * (((6 : ℕ) : ℝ) - 6) / 3) = Real.pi / 3 by push_cast; ring,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    ext a; fin_cases a <;> simp [ttpPt, ttpX, ttpRow, rhoR, s3R]
  · rw [show (Real.pi / 3 + 2 * Real.pi * (((7 : ℕ) : ℝ) - 6) / 3) = Real.pi by push_cast; ring,
      Real.cos_pi, Real.sin_pi]
    ext a; fin_cases a <;> simp [ttpPt, ttpX, ttpRow, rhoR, s3R]
  · rw [show (Real.pi / 3 + 2 * Real.pi * (((8 : ℕ) : ℝ) - 6) / 3) = 5 * Real.pi / 3 by push_cast; ring,
      hc53, hs53]
    ext a; fin_cases a <;> simp [ttpPt, ttpX, ttpRow, rhoR, s3R] <;> ring

/-- Closed-form values of `phi (nuOfN k z)` for `k = 0..5` and `z ∈ (0, 1)`. -/
noncomputable def phiVal (z : ℝ) : ℕ → ℝ
  | 0 => 1 / Real.sqrt (3 + z ^ 2)
  | 1 => 1 / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2))
  | 2 => 1 / Real.sqrt 3
  | 3 => 1 / (2 * z)
  | 4 => 1 / (Real.sqrt 3 * Real.sqrt (1 - z ^ 2))
  | _ => 1 / Real.sqrt (2 - Real.sqrt (1 - z ^ 2))

lemma phi_nuOfN_eq_phiVal (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (k : ℕ) (hk : k < 6) :
    phi (nuOfN k z) = phiVal z k := by
  have h1mz : 0 ≤ 1 - z ^ 2 := by nlinarith
  interval_cases k
  · simp only [phi, nuOfN, nu1, phiVal, one_div]; congr 1; congr 1; ring
  · simp only [phi, nuOfN, nu2, rhoR, phiVal, one_div]; congr 1; congr 1; ring
  · simp only [phi, nuOfN, nu3, phiVal, one_div]; congr 1; congr 1; norm_num
  · simp only [phi, nuOfN, nu4, phiVal, one_div]; congr 1
    rw [show 2 - 2 * (1 - 2 * z ^ 2) = (2 * z) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  · simp only [phi, nuOfN, nu5, phiVal, one_div]; congr 1
    rw [show 2 - 2 * ((3 * z ^ 2 - 1) / 2) = 3 * (1 - z ^ 2) by ring, Real.sqrt_mul (by norm_num)]
  · simp only [phi, nuOfN, nu6, rhoR, phiVal, one_div]; congr 1; congr 1; ring

lemma coulombEnergy9_ttpPt (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    coulombEnergy9 (ttpPt z) =
      2 * Real.sqrt 3 / Real.sqrt (1 - z ^ 2) + Real.sqrt 3 + 3 / (2 * z)
      + 6 / Real.sqrt (3 + z ^ 2) + 12 / Real.sqrt (2 - Real.sqrt (1 - z ^ 2))
      + 6 / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) := by
  have hzsq : z ^ 2 ≤ 1 := by nlinarith
  have hnorm : ∀ i, ‖ttpPt z i‖ = 1 := ttpPt_norm z hzsq
  have hpair : ∀ i j : Fin 9, i ≠ j → ‖ttpPt z i - ttpPt z j‖⁻¹ = phiVal z (nodeOfN i.val j.val) := by
    intro i j hij
    rw [inv_norm_eq_phi (hnorm i) (hnorm j), ttpPt_inner z hzsq i j hij]
    exact phi_nuOfN_eq_phiVal z hz0 hz1 (nodeOfN i.val j.val)
      (nodeOfN_lt6 i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)))
  have hsum : coulombEnergy9 (ttpPt z) =
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phiVal z (nodeOfN i.val j.val) := by
    unfold coulombEnergy9
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      hpair i j (ne_of_lt (Finset.mem_Ioi.mp hj))
  rw [hsum]
  have hcount : ∀ f : ℕ → ℝ,
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, f (nodeOfN i.val j.val) =
        6 * f 0 + 6 * f 1 + 3 * f 2 + 3 * f 3 + 6 * f 4 + 12 * f 5 := by
    intro f
    have hI : ∀ i : Fin 9, ∑ j ∈ Finset.Ioi i, f (nodeOfN i.val j.val) =
        ∑ j : Fin 9, if i < j then f (nodeOfN i.val j.val) else 0 := fun i => by
      rw [← Finset.sum_filter]; congr 1; ext j; simp
    simp_rw [hI]
    simp only [sum_univ_nine]
    simp [nodeOfN]
    ring
  rw [hcount (phiVal z)]
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3_ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hrho_ne : Real.sqrt (1 - z ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by nlinarith))
  have hz_ne : z ≠ 0 := ne_of_gt hz0
  simp only [phiVal]
  have h2 : 3 * (1 / Real.sqrt 3) = Real.sqrt 3 := by
    rw [mul_one_div, div_eq_iff hs3_ne]; linarith
  have h4 : 6 * (1 / (Real.sqrt 3 * Real.sqrt (1 - z ^ 2))) = 2 * Real.sqrt 3 / Real.sqrt (1 - z ^ 2) := by
    field_simp; nlinarith [hs3]
  rw [h2, h4]
  ring

/-! ## Section 2: Criticality Function `critGap` & Existence of `z*` -/

/-- Exact radial-vs-axial multiplier difference `lam_z - lam_r = dE / (6z)` for the TTP family. -/
noncomputable def critGap (z : ℝ) : ℝ :=
  3 / (Real.sqrt 3 * Real.sqrt (1 - z ^ 2)) ^ 3 - 2 / (2 * z) ^ 3 - 1 / Real.sqrt (3 + z ^ 2) ^ 3
    - 1 / (Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 * Real.sqrt (1 - z ^ 2))
    + 1 / (Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3 * Real.sqrt (1 - z ^ 2))

private lemma sqrt_lo_le {a : ℝ} {q : ℚ} (hq0 : (0 : ℚ) < q) (hsq : (q : ℝ) ^ 2 ≤ a) :
    (q : ℝ) ≤ Real.sqrt a := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have ha : 0 ≤ a := le_trans (sq_nonneg _) hsq
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]

private lemma sqrt_le_hi {a : ℝ} {q : ℚ} (hq0 : (0 : ℚ) < q) (hsq : a ≤ (q : ℝ) ^ 2) :
    Real.sqrt a ≤ (q : ℝ) := by
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0.le
  exact Real.sqrt_le_iff.mpr ⟨hqR, hsq⟩

private lemma inv_pow3_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : 1 / b ^ 3 ≤ 1 / a ^ 3 :=
  one_div_le_one_div_of_le (pow_pos ha 3) (pow_le_pow_left₀ ha.le hab 3)

private lemma critGap_zStarLo_neg : critGap (zStarLo : ℝ) < 0 := by
  obtain ⟨hs3l, hs3p, hrl, hrh, hrlp, ha0h, ha0p, ha1l, ha1p, ha5h, ha5p⟩ := critLo_sq_ok
  have hs3 : (cLo_s3l : ℝ) ≤ Real.sqrt 3 := sqrt_lo_le hs3p (by exact_mod_cast hs3l)
  have hr_lo : (cLo_rl : ℝ) ≤ Real.sqrt (1 - (zStarLo : ℝ) ^ 2) := sqrt_lo_le hrlp (by exact_mod_cast hrl)
  have hrhp : (0 : ℚ) < cLo_rh := by norm_num [cLo_rh]
  have hr_hi : Real.sqrt (1 - (zStarLo : ℝ) ^ 2) ≤ (cLo_rh : ℝ) := sqrt_le_hi hrhp (by exact_mod_cast hrh)
  have ha0 : Real.sqrt (3 + (zStarLo : ℝ) ^ 2) ≤ (cLo_a0h : ℝ) := sqrt_le_hi ha0p (by exact_mod_cast ha0h)
  have ha1 : (cLo_a1l : ℝ) ≤ Real.sqrt (2 + 2 * Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) :=
    sqrt_lo_le ha1p (le_trans (by exact_mod_cast ha1l : (cLo_a1l : ℝ) ^ 2 ≤ 2 + 2 * (cLo_rl : ℝ)) (by linarith))
  have ha5 : Real.sqrt (2 - Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) ≤ (cLo_a5h : ℝ) :=
    sqrt_le_hi ha5p (le_trans (by linarith) (by exact_mod_cast ha5h : 2 - (cLo_rl : ℝ) ≤ (cLo_a5h : ℝ) ^ 2))
  have h1 : 3 / (Real.sqrt 3 * Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) ^ 3 ≤
      3 / ((cLo_s3l : ℝ) * (cLo_rl : ℝ)) ^ 3 := by
    have hp : (0 : ℝ) < ((cLo_s3l : ℝ) * (cLo_rl : ℝ)) ^ 3 := by
      have : (0 : ℝ) < (cLo_s3l : ℝ) := by exact_mod_cast hs3p
      have : (0 : ℝ) < (cLo_rl : ℝ) := by exact_mod_cast hrlp
      positivity
    refine div_le_div_of_nonneg_left (by norm_num) hp ?_
    refine pow_le_pow_left₀ (by positivity) (mul_le_mul hs3 hr_lo (by exact_mod_cast hrlp.le) (Real.sqrt_nonneg _)) 3
  have h2 : 1 / (cLo_a0h : ℝ) ^ 3 ≤ 1 / Real.sqrt (3 + (zStarLo : ℝ) ^ 2) ^ 3 :=
    inv_pow3_anti (Real.sqrt_pos.mpr (by positivity)) ha0
  have h3 : 1 / ((cLo_a5h : ℝ) ^ 3 * (cLo_rh : ℝ)) ≤
      1 / (Real.sqrt (2 - Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) ^ 3 * Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) := by
    have hr_pos : 0 < Real.sqrt (1 - (zStarLo : ℝ) ^ 2) := lt_of_lt_of_le (by exact_mod_cast hrlp) hr_lo
    have h2mr_pos : 0 < 2 - Real.sqrt (1 - (zStarLo : ℝ) ^ 2) := by
      have : (cLo_rh : ℝ) < 2 := by norm_num [cLo_rh]
      linarith
    have ha5_pos : 0 < Real.sqrt (2 - Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) := Real.sqrt_pos.mpr h2mr_pos
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (pow_le_pow_left₀ ha5_pos.le ha5 3) hr_hi hr_pos.le (by exact_mod_cast (pow_pos ha5p 3).le)
  have h4 : 1 / (Real.sqrt (2 + 2 * Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) ^ 3 * Real.sqrt (1 - (zStarLo : ℝ) ^ 2)) ≤
      1 / ((cLo_a1l : ℝ) ^ 3 * (cLo_rl : ℝ)) := by
    have hrlR : (0 : ℝ) < (cLo_rl : ℝ) := by exact_mod_cast hrlp
    have ha1R : (0 : ℝ) < (cLo_a1l : ℝ) := by exact_mod_cast ha1p
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (pow_le_pow_left₀ ha1R.le ha1 3) hr_lo hrlR.le (by positivity)
  have hneg : 3 / ((cLo_s3l : ℝ) * (cLo_rl : ℝ)) ^ 3 - 2 / (2 * (zStarLo : ℝ)) ^ 3 - 1 / (cLo_a0h : ℝ) ^ 3
      - 1 / ((cLo_a5h : ℝ) ^ 3 * (cLo_rh : ℝ)) + 1 / ((cLo_a1l : ℝ) ^ 3 * (cLo_rl : ℝ)) < 0 := by
    exact_mod_cast critLo_neg_ok
  unfold critGap
  linarith

private lemma critGap_zStarHi_pos : 0 < critGap (zStarHi : ℝ) := by
  obtain ⟨hs3h, hs3p, hrl, hrh, hrlp, ha0l, ha0p, ha1h, ha1p, ha5l, ha5p⟩ := critHi_sq_ok
  have hs3 : Real.sqrt 3 ≤ (cHi_s3h : ℝ) := sqrt_le_hi hs3p (by exact_mod_cast hs3h)
  have hr_lo : (cHi_rl : ℝ) ≤ Real.sqrt (1 - (zStarHi : ℝ) ^ 2) := sqrt_lo_le hrlp (by exact_mod_cast hrl)
  have hrhp : (0 : ℚ) < cHi_rh := by norm_num [cHi_rh]
  have hr_hi : Real.sqrt (1 - (zStarHi : ℝ) ^ 2) ≤ (cHi_rh : ℝ) := sqrt_le_hi hrhp (by exact_mod_cast hrh)
  have ha0 : (cHi_a0l : ℝ) ≤ Real.sqrt (3 + (zStarHi : ℝ) ^ 2) := sqrt_lo_le ha0p (by exact_mod_cast ha0l)
  have ha1 : Real.sqrt (2 + 2 * Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) ≤ (cHi_a1h : ℝ) :=
    sqrt_le_hi ha1p (le_trans (by linarith) (by exact_mod_cast ha1h : 2 + 2 * (cHi_rh : ℝ) ≤ (cHi_a1h : ℝ) ^ 2))
  have ha5 : (cHi_a5l : ℝ) ≤ Real.sqrt (2 - Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) :=
    sqrt_lo_le ha5p (le_trans (by exact_mod_cast ha5l : (cHi_a5l : ℝ) ^ 2 ≤ 2 - (cHi_rh : ℝ)) (by linarith))
  have h1 : 3 / ((cHi_s3h : ℝ) * (cHi_rh : ℝ)) ^ 3 ≤
      3 / (Real.sqrt 3 * Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) ^ 3 := by
    have hr_pos : 0 < Real.sqrt (1 - (zStarHi : ℝ) ^ 2) := lt_of_lt_of_le (by exact_mod_cast hrlp) hr_lo
    have hp : (0 : ℝ) < (Real.sqrt 3 * Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) ^ 3 := by positivity
    refine div_le_div_of_nonneg_left (by norm_num) hp ?_
    refine pow_le_pow_left₀ (by positivity) (mul_le_mul hs3 hr_hi hr_pos.le (by exact_mod_cast hs3p.le)) 3
  have h2 : 1 / Real.sqrt (3 + (zStarHi : ℝ) ^ 2) ^ 3 ≤ 1 / (cHi_a0l : ℝ) ^ 3 :=
    inv_pow3_anti (by exact_mod_cast ha0p) ha0
  have h3 : 1 / (Real.sqrt (2 - Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) ^ 3 * Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) ≤
      1 / ((cHi_a5l : ℝ) ^ 3 * (cHi_rl : ℝ)) := by
    have hrlR : (0 : ℝ) < (cHi_rl : ℝ) := by exact_mod_cast hrlp
    have ha5R : (0 : ℝ) < (cHi_a5l : ℝ) := by exact_mod_cast ha5p
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (pow_le_pow_left₀ ha5R.le ha5 3) hr_lo hrlR.le (by positivity)
  have h4 : 1 / ((cHi_a1h : ℝ) ^ 3 * (cHi_rh : ℝ)) ≤
      1 / (Real.sqrt (2 + 2 * Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) ^ 3 * Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) := by
    have hr_pos : 0 < Real.sqrt (1 - (zStarHi : ℝ) ^ 2) := lt_of_lt_of_le (by exact_mod_cast hrlp) hr_lo
    have ha1_pos : 0 < Real.sqrt (2 + 2 * Real.sqrt (1 - (zStarHi : ℝ) ^ 2)) := Real.sqrt_pos.mpr (by linarith)
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (pow_le_pow_left₀ ha1_pos.le ha1 3) hr_hi hr_pos.le (by exact_mod_cast (pow_pos ha1p 3).le)
  have hpos : 0 < 3 / ((cHi_s3h : ℝ) * (cHi_rh : ℝ)) ^ 3 - 2 / (2 * (zStarHi : ℝ)) ^ 3 - 1 / (cHi_a0l : ℝ) ^ 3
      - 1 / ((cHi_a5l : ℝ) ^ 3 * (cHi_rl : ℝ)) + 1 / ((cHi_a1h : ℝ) ^ 3 * (cHi_rh : ℝ)) := by
    exact_mod_cast critHi_pos_ok
  unfold critGap
  linarith

private lemma continuousOn_critGap : ContinuousOn critGap (Set.Icc (zStarLo : ℝ) (zStarHi : ℝ)) := by
  have hz_pos : ∀ z ∈ Set.Icc (zStarLo : ℝ) (zStarHi : ℝ), (0 : ℝ) < z := fun z hz => by
    have : (0 : ℝ) < (zStarLo : ℝ) := by norm_num [zStarLo]
    linarith [hz.1]
  have hrho_pos : ∀ z ∈ Set.Icc (zStarLo : ℝ) (zStarHi : ℝ), (0 : ℝ) < Real.sqrt (1 - z ^ 2) := fun z hz => by
    have hhi : (zStarHi : ℝ) < 1 := by norm_num [zStarHi]
    have h0 := hz_pos z hz
    exact Real.sqrt_pos.mpr (by nlinarith [hz.2])
  have hrho_lt2 : ∀ z ∈ Set.Icc (zStarLo : ℝ) (zStarHi : ℝ), Real.sqrt (1 - z ^ 2) < 2 := fun z hz => by
    have : 1 - z ^ 2 < 4 := by nlinarith [hz_pos z hz]
    exact (Real.sqrt_lt' (by norm_num)).mpr (by linarith)
  have hcont_rho : ContinuousOn (fun z : ℝ => Real.sqrt (1 - z ^ 2)) (Set.Icc (zStarLo : ℝ) (zStarHi : ℝ)) :=
    (continuous_const.sub (continuous_id.pow 2)).sqrt.continuousOn
  unfold critGap
  refine ((((continuousOn_const.div
      (((continuousOn_const.mul hcont_rho).pow 3)) fun z hz =>
        pow_ne_zero 3 (mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (ne_of_gt (hrho_pos z hz)))).sub
    (continuousOn_const.div ((continuousOn_const.mul continuousOn_id).pow 3) fun z hz =>
      pow_ne_zero 3 (mul_ne_zero two_ne_zero (ne_of_gt (hz_pos z hz))))).sub
    (continuousOn_const.div (((continuous_const.add (continuous_id.pow 2)).sqrt.continuousOn).pow 3) fun z _ =>
      pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr (by
        dsimp only [Pi.add_apply, Pi.pow_apply, id]; nlinarith [sq_nonneg z]))))).sub
    (continuousOn_const.div
      ((((continuousOn_const.sub hcont_rho).sqrt).pow 3).mul hcont_rho) fun z hz =>
        mul_ne_zero (pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr (by
          dsimp only [Pi.sub_apply]; have := hrho_lt2 z hz; linarith))))
          (ne_of_gt (hrho_pos z hz)))).add
    (continuousOn_const.div
      ((((continuousOn_const.add (continuousOn_const.mul hcont_rho)).sqrt).pow 3).mul hcont_rho) fun z hz =>
        mul_ne_zero (pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr (by have := hrho_pos z hz; linarith))))
          (ne_of_gt (hrho_pos z hz)))

/-- **Existence of exact critical `z*`**: lies in `[zStarLo, zStarHi] ⊂ [zLo, zHi] ⊂ (0, 1)`,
satisfies `critGap z* = 0`, and has `coulombEnergy9 (ttpPt z*) ≤ E_ttp_hi`. -/
theorem exists_z_star :
    ∃ zStar : ℝ, (zStarLo : ℝ) ≤ zStar ∧ zStar ≤ (zStarHi : ℝ) ∧
      critGap zStar = 0 ∧ coulombEnergy9 (ttpPt zStar) ≤ SlabCert.E_ttp_hi := by
  have hle : (zStarLo : ℝ) ≤ (zStarHi : ℝ) := by exact_mod_cast zStar_in_zBox.2.1.le
  have hmem : (0 : ℝ) ∈ Set.Icc (critGap (zStarLo : ℝ)) (critGap (zStarHi : ℝ)) :=
    ⟨critGap_zStarLo_neg.le, critGap_zStarHi_pos.le⟩
  obtain ⟨zStar, hzmem, hcrit⟩ := intermediate_value_Icc hle continuousOn_critGap hmem
  obtain ⟨hz1, hz2⟩ := hzmem
  have hzLo0 : (0 : ℝ) < (zStarLo : ℝ) := by norm_num [zStarLo]
  have hz0 : 0 < zStar := lt_of_lt_of_le hzLo0 hz1
  have hzlt1 : zStar < 1 := lt_of_le_of_lt hz2 (by norm_num [zStarHi])
  obtain ⟨hs3l, hs3h, hs3p, hrl, hrh, hrlp, hr0l, hr0h, hr0p, hr1l, hr1h, hr1p, hr5l, hr5h, hr5p⟩ := env_sq_ok
  have hs3_le : Real.sqrt 3 ≤ (s3Hi : ℝ) := sqrt_le_hi (by norm_num [s3Hi]) (by exact_mod_cast hs3h)
  have hrho_lo : (rhoStarLo : ℝ) ≤ Real.sqrt (1 - zStar ^ 2) :=
    sqrt_lo_le hrlp (le_trans (by exact_mod_cast hrl : (rhoStarLo : ℝ) ^ 2 ≤ 1 - (zStarHi : ℝ) ^ 2) (by nlinarith [hz0, hz2]))
  have hrho_hi : Real.sqrt (1 - zStar ^ 2) ≤ (rhoStarHi : ℝ) :=
    sqrt_le_hi (by norm_num [rhoStarHi]) (le_trans (by nlinarith [hzLo0, hz0, hz1]) (by exact_mod_cast hrh : 1 - (zStarLo : ℝ) ^ 2 ≤ (rhoStarHi : ℝ) ^ 2))
  have hr0_lo : (r0Lo : ℝ) ≤ Real.sqrt (3 + zStar ^ 2) :=
    sqrt_lo_le hr0p (le_trans (by exact_mod_cast hr0l : (r0Lo : ℝ) ^ 2 ≤ 3 + (zStarLo : ℝ) ^ 2) (by nlinarith [hzLo0, hz0, hz1]))
  have hr1_lo : (r1Lo : ℝ) ≤ Real.sqrt (2 + 2 * Real.sqrt (1 - zStar ^ 2)) :=
    sqrt_lo_le hr1p (le_trans (by exact_mod_cast hr1l : (r1Lo : ℝ) ^ 2 ≤ 2 + 2 * (rhoStarLo : ℝ)) (by linarith))
  have hr5_lo : (r5Lo : ℝ) ≤ Real.sqrt (2 - Real.sqrt (1 - zStar ^ 2)) :=
    sqrt_lo_le hr5p (le_trans (by exact_mod_cast hr5l : (r5Lo : ℝ) ^ 2 ≤ 2 - (rhoStarHi : ℝ)) (by linarith))
  have hE : coulombEnergy9 (ttpPt zStar) ≤ SlabCert.E_ttp_hi := by
    rw [coulombEnergy9_ttpPt zStar hz0 hzlt1]
    have t1 : 2 * Real.sqrt 3 / Real.sqrt (1 - zStar ^ 2) ≤ 2 * (s3Hi : ℝ) / (rhoStarLo : ℝ) :=
      div_le_div₀ (by norm_num [s3Hi]) (by linarith) (by exact_mod_cast hrlp) hrho_lo
    have t3 : 3 / (2 * zStar) ≤ 3 / (2 * (zStarLo : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num [zStarLo]) (by linarith)
    have t4 : 6 / Real.sqrt (3 + zStar ^ 2) ≤ 6 / (r0Lo : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hr0p) hr0_lo
    have t5 : 12 / Real.sqrt (2 - Real.sqrt (1 - zStar ^ 2)) ≤ 12 / (r5Lo : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hr5p) hr5_lo
    have t6 : 6 / Real.sqrt (2 + 2 * Real.sqrt (1 - zStar ^ 2)) ≤ 6 / (r1Lo : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hr1p) hr1_lo
    have hq : 2 * (s3Hi : ℝ) / (rhoStarLo : ℝ) + (s3Hi : ℝ) + 3 / (2 * (zStarLo : ℝ))
        + 6 / (r0Lo : ℝ) + 12 / (r5Lo : ℝ) + 6 / (r1Lo : ℝ) ≤ (E_ttp_hi_q : ℝ) := by
      exact_mod_cast E_hi_env_ok
    have heq_E : (E_ttp_hi_q : ℝ) = SlabCert.E_ttp_hi := by
      unfold E_ttp_hi_q SlabCert.E_ttp_hi SlabCertData.E_ttp_hi_num SlabCertData.E_ttp_hi_den
      norm_num
    linarith
  exact ⟨zStar, hz1, hz2, hcrit, hE⟩

/-! ## Section 3: Exact `D₃h` Force-Balance Criticality at `z*` -/

noncomputable def lamP (z : ℝ) : ℝ :=
  2 / (Real.sqrt 3 * Real.sqrt (1 - z ^ 2)) ^ 3 - 1 / (2 * z) ^ 3 - 2 / Real.sqrt (3 + z ^ 2) ^ 3

noncomputable def lamC (z : ℝ) : ℝ :=
  2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3
    - 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3
    - 1 / Real.sqrt 3 ^ 3

noncomputable def lamOf (z : ℝ) (i : Fin 9) : ℝ :=
  if i.val < 6 then lamP z else lamC z

lemma ttp_critical {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (hcrit : critGap z = 0) (i : Fin 9) :
    ∑ j ∈ Finset.univ.erase i, phi ⟪ttpPt z i, ttpPt z j⟫ ^ 3 • ttpPt z j =
      lamOf z i • ttpPt z i := by
  have hzsq : z ^ 2 ≤ 1 := by nlinarith
  have hrho_pos : 0 < Real.sqrt (1 - z ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hrho_ne : Real.sqrt (1 - z ^ 2) ≠ 0 := ne_of_gt hrho_pos
  have hcrit' :
      -(1 / (Real.sqrt 3 * Real.sqrt (1 - z ^ 2)) ^ 3) + 1 / (2 * z) ^ 3 - 1 / Real.sqrt (3 + z ^ 2) ^ 3
        + (1 / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 - 1 / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3)
          / Real.sqrt (1 - z ^ 2) = lamP z := by
    unfold critGap at hcrit
    unfold lamP
    have hmul : (1 / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 - 1 / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3)
        / Real.sqrt (1 - z ^ 2) =
        1 / (Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 * Real.sqrt (1 - z ^ 2))
        - 1 / (Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3 * Real.sqrt (1 - z ^ 2)) := by
      field_simp
    linear_combination -hcrit + hmul
  have hmul_rho :
      Real.sqrt (1 - z ^ 2) * (-(1 / (Real.sqrt 3 * Real.sqrt (1 - z ^ 2)) ^ 3) + 1 / (2 * z) ^ 3
        - 1 / Real.sqrt (3 + z ^ 2) ^ 3)
      + (1 / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 - 1 / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3) =
      lamP z * Real.sqrt (1 - z ^ 2) := by
    have := congrArg (Real.sqrt (1 - z ^ 2) * ·) hcrit'
    field_simp at this ⊢
    linarith
  have hterm : ∀ j ∈ Finset.univ.erase i,
      phi ⟪ttpPt z i, ttpPt z j⟫ ^ 3 = phiVal z (nodeOfN i.val j.val) ^ 3 := by
    intro j hj
    have hne : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    rw [ttpPt_inner z hzsq i j hne,
      phi_nuOfN_eq_phiVal z hz0 hz1 (nodeOfN i.val j.val)
        (nodeOfN_lt6 i.val j.val i.isLt j.isLt (fun h => hne (Fin.ext h)))]
  have hrew : ∑ j ∈ Finset.univ.erase i, phi ⟪ttpPt z i, ttpPt z j⟫ ^ 3 • ttpPt z j =
      ∑ j : Fin 9, if j = i then 0 else phiVal z (nodeOfN i.val j.val) ^ 3 • ttpPt z j := by
    have heq : Finset.univ.erase i = Finset.univ.filter (fun j => j ≠ i) := by ext j; simp
    have hite : ∑ j : Fin 9, (if j = i then (0 : R3) else phiVal z (nodeOfN i.val j.val) ^ 3 • ttpPt z j) =
        ∑ j : Fin 9, if j ≠ i then phiVal z (nodeOfN i.val j.val) ^ 3 • ttpPt z j else 0 :=
      Finset.sum_congr rfl fun j _ => by by_cases h : j = i <;> simp [h]
    rw [hite, ← Finset.sum_filter, ← heq]
    exact Finset.sum_congr rfl fun j hj => by rw [hterm j hj]
  rw [hrew]
  ext a
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hsum_apply : (∑ j : Fin 9, if j = i then (0 : R3) else phiVal z (nodeOfN i.val j.val) ^ 3 • ttpPt z j) a =
      ∑ j : Fin 9, if j = i then (0 : ℝ) else phiVal z (nodeOfN i.val j.val) ^ 3 * ttpPt z j a := by
    have hfold : ∀ s : Finset (Fin 9), (∑ j ∈ s, if j = i then (0 : R3) else phiVal z (nodeOfN i.val j.val) ^ 3 • ttpPt z j) a =
        ∑ j ∈ s, if j = i then (0 : ℝ) else phiVal z (nodeOfN i.val j.val) ^ 3 * ttpPt z j a := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx, PiLp.add_apply, ih]
        split_ifs <;> simp
    exact hfold Finset.univ
  rw [hsum_apply]
  have hlamP : lamP z = 2 * phiVal z 4 ^ 3 - phiVal z 3 ^ 3 - 2 * phiVal z 0 ^ 3 := by
    unfold lamP phiVal; simp only [_root_.one_div_pow]; ring
  have hlamC : lamC z = 2 * Real.sqrt (1 - z ^ 2) * phiVal z 5 ^ 3 -
      2 * Real.sqrt (1 - z ^ 2) * phiVal z 1 ^ 3 - phiVal z 2 ^ 3 := by
    unfold lamC phiVal; simp only [_root_.one_div_pow]; ring
  have hmul_phi :
      Real.sqrt (1 - z ^ 2) * (-(phiVal z 4 ^ 3) + phiVal z 3 ^ 3 - phiVal z 0 ^ 3)
      + (phiVal z 5 ^ 3 - phiVal z 1 ^ 3) =
      (2 * phiVal z 4 ^ 3 - phiVal z 3 ^ 3 - 2 * phiVal z 0 ^ 3) * Real.sqrt (1 - z ^ 2) := by
    rw [← hlamP, ← hmul_rho]; unfold phiVal; simp only [_root_.one_div_pow]
  fin_cases i <;> fin_cases a <;>
    simp only [sum_univ_nine, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
      ttpPt, ttpX, ttpRow, rhoR, s3R, Matrix.of_apply, lamOf, hlamP, hlamC, nodeOfN,
      ↓reduceIte, zero_add, add_zero] <;>
    (try norm_num) <;>
    (try ring) <;>
    (try linear_combination hmul_phi) <;>
    (try linear_combination -hmul_phi / 2) <;>
    (try linear_combination (Real.sqrt 3 / 2) * hmul_phi) <;>
    (try linear_combination -(Real.sqrt 3 / 2) * hmul_phi)

/-! ## Section 4: Bregman Convexity Lower Bound (`breg_ge_quad`) -/

private lemma sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih]

private lemma phiDeriv_zero_eq (t : ℝ) : phiDeriv 0 t = phi t := by
  unfold phiDeriv phi dfactorialOdd
  simp [one_div]

private lemma phiDeriv_one_eq {t : ℝ} (ht : t < 1) : phiDeriv 1 t = phi t ^ 3 := by
  unfold phiDeriv phi
  have hpos : 0 < 2 - 2 * t := by linarith
  have hsq : Real.sqrt ((2 - 2 * t) ^ 3) = Real.sqrt (2 - 2 * t) ^ 3 := sqrt_pow_eq hpos.le 3
  have h1 : (dfactorialOdd 1 : ℝ) = 1 := by norm_num [dfactorialOdd]
  have hpow : (2 * 1 + 1 : ℕ) = 3 := rfl
  rw [hpow, hsq, h1]
  field_simp

private lemma phiDeriv_two_eq {t : ℝ} (ht : t < 1) : phiDeriv 2 t = 3 * phi t ^ 5 := by
  unfold phiDeriv phi
  have hpos : 0 < 2 - 2 * t := by linarith
  have hsq : Real.sqrt ((2 - 2 * t) ^ 5) = Real.sqrt (2 - 2 * t) ^ 5 := sqrt_pow_eq hpos.le 5
  have h3 : (dfactorialOdd 2 : ℝ) = 3 := by norm_num [dfactorialOdd]
  have hpow : (2 * 2 + 1 : ℕ) = 5 := rfl
  rw [hpow, hsq, h3]
  field_simp

private lemma phi_mono {a b : ℝ} (hab : a ≤ b) (hb : b < 1) : phi a ≤ phi b := by
  unfold phi
  exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (by linarith))

/-- **Bregman quadratic lower bound**: for `|τ| ≤ τ_max` and `t0 + τ_max < 1`:
`phi (t0 + τ) - phi t0 - phi t0 ^ 3 * τ ≥ (3 / 2) * phi (t0 - τ_max) ^ 5 * τ ^ 2`. -/
lemma breg_ge_quad {t0 τ τ_max : ℝ} (hτm : 0 ≤ τ_max) (habs : |τ| ≤ τ_max) (hlt : t0 + τ_max < 1) :
    (3 / 2 : ℝ) * phi (t0 - τ_max) ^ 5 * τ ^ 2 ≤ phi (t0 + τ) - phi t0 - phi t0 ^ 3 * τ := by
  let c : ℝ := phi (t0 - τ_max) ^ 5
  let g : ℝ → ℝ := fun s => phi (t0 + s) - phi t0 - phi t0 ^ 3 * s - (3 / 2) * c * s ^ 2
  let g' : ℝ → ℝ := fun s => phi (t0 + s) ^ 3 - phi t0 ^ 3 - 3 * c * s
  have hg_deriv : ∀ s ∈ Set.Icc (-τ_max) τ_max, HasDerivAt g (g' s) s := by
    intro s hs
    have hlt_s : t0 + s < 1 := by linarith [hs.2]
    have hd0 : HasDerivAt (fun x => phiDeriv 0 (t0 + x)) (phiDeriv 1 (t0 + s) * 1) s :=
      (hasDerivAt_phiDeriv 0 (t0 + s) hlt_s).comp s ((hasDerivAt_id s).const_add t0)
    have hd_phi : HasDerivAt (fun x => phi (t0 + x)) (phi (t0 + s) ^ 3) s := by
      have heq : (fun x => phi (t0 + x)) = (fun x => phiDeriv 0 (t0 + x)) := by
        ext x; exact (phiDeriv_zero_eq _).symm
      rw [phiDeriv_one_eq hlt_s, mul_one] at hd0
      rw [heq]
      exact hd0
    have hd_lin : HasDerivAt (fun x => phi t0 ^ 3 * x) (phi t0 ^ 3 * 1) s :=
      (hasDerivAt_id s).const_mul _
    have hd_sq : HasDerivAt (fun x => (3 / 2 : ℝ) * c * x ^ 2) ((3 / 2 : ℝ) * c * (2 * s ^ 1)) s :=
      ((hasDerivAt_pow 2 s).const_mul _).congr_deriv (by ring)
    exact (((hd_phi.sub (hasDerivAt_const s _)).sub hd_lin).sub hd_sq).congr_deriv (by dsimp only [g']; ring)
  have hg'_deriv : ∀ s ∈ Set.Icc (-τ_max) τ_max, HasDerivAt g' (3 * phi (t0 + s) ^ 5 - 3 * c) s := by
    intro s hs
    have hlt_s : t0 + s < 1 := by linarith [hs.2]
    have hd1 : HasDerivAt (fun x => phiDeriv 1 (t0 + x)) (phiDeriv 2 (t0 + s) * 1) s :=
      (hasDerivAt_phiDeriv 1 (t0 + s) hlt_s).comp s ((hasDerivAt_id s).const_add t0)
    have hd_phi3 : HasDerivAt (fun x => phi (t0 + x) ^ 3) (3 * phi (t0 + s) ^ 5) s := by
      have hev : ∀ᶠ x in nhds s, phi (t0 + x) ^ 3 = phiDeriv 1 (t0 + x) := by
        have hopen : IsOpen {x : ℝ | t0 + x < 1} := isOpen_lt (continuous_const.add continuous_id) continuous_const
        filter_upwards [hopen.mem_nhds hlt_s] with x hx
        exact (phiDeriv_one_eq hx).symm
      rw [phiDeriv_two_eq hlt_s, mul_one] at hd1
      exact hd1.congr_of_eventuallyEq hev
    have hd_lin : HasDerivAt (fun x => 3 * c * x) (3 * c * 1) s := (hasDerivAt_id s).const_mul _
    exact ((hd_phi3.sub (hasDerivAt_const s _)).sub hd_lin).congr_deriv (by ring)
  have hg'_mono : MonotoneOn g' (Set.Icc (-τ_max) τ_max) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun s hs => (hg'_deriv s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hg'_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    have hmem := interior_subset hs
    rw [(hg'_deriv s hmem).deriv]
    have hle : phi (t0 - τ_max) ≤ phi (t0 + s) := phi_mono (by linarith [hmem.1]) (by linarith [hmem.2])
    have hnn : 0 ≤ phi (t0 - τ_max) := by unfold phi; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hpow := pow_le_pow_left₀ hnn hle 5
    dsimp only [c]; linarith
  have hg'0 : g' 0 = 0 := by dsimp only [g']; ring
  have hg0 : g 0 = 0 := by dsimp only [g]; ring
  rw [abs_le] at habs
  have hres : 0 ≤ g τ := by
    by_cases hτ : 0 ≤ τ
    · have hmono : MonotoneOn g (Set.Icc 0 τ_max) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
          (fun s hs => (hg_deriv s ⟨by linarith [hs.1], hs.2⟩).continuousAt.continuousWithinAt)
          (fun s hs => (hg_deriv s ⟨by linarith [(interior_subset hs).1], (interior_subset hs).2⟩).differentiableAt.differentiableWithinAt) ?_
        intro s hs
        have hm := interior_subset hs
        rw [(hg_deriv s ⟨by linarith [hm.1], hm.2⟩).deriv, ← hg'0]
        exact hg'_mono ⟨by linarith, hτm⟩ ⟨by linarith [hm.1], hm.2⟩ hm.1
      rw [← hg0]
      exact hmono ⟨le_refl _, hτm⟩ ⟨hτ, habs.2⟩ hτ
    · push_neg at hτ
      have hanti : AntitoneOn g (Set.Icc (-τ_max) 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          (fun s hs => (hg_deriv s ⟨hs.1, by linarith [hs.2]⟩).continuousAt.continuousWithinAt)
          (fun s hs => (hg_deriv s ⟨(interior_subset hs).1, by linarith [(interior_subset hs).2]⟩).differentiableAt.differentiableWithinAt) ?_
        intro s hs
        have hm := interior_subset hs
        rw [(hg_deriv s ⟨hm.1, by linarith [hm.2]⟩).deriv, ← hg'0]
        exact hg'_mono ⟨hm.1, by linarith [hm.2]⟩ ⟨by linarith, hτm⟩ hm.2
      rw [← hg0]
      exact hanti ⟨habs.1, hτ.le⟩ ⟨by linarith, le_refl _⟩ hτ.le
  dsimp only [g, c] at hres
  linarith

/-! ## Section 5: Procrustes Gauge Lemma (`exists_gauge`) -/

private noncomputable def planeRot (u v : R3) (c s : ℝ) : R3 →L[ℝ] R3 :=
  ContinuousLinearMap.id ℝ R3
    + (c - 1) • ((innerSL ℝ u).smulRight u + (innerSL ℝ v).smulRight v)
    + s • ((innerSL ℝ u).smulRight v - (innerSL ℝ v).smulRight u)

private lemma planeRot_apply (u v : R3) (c s : ℝ) (w : R3) :
    planeRot u v c s w = w + ((c - 1) * ⟪u, w⟫ - s * ⟪v, w⟫) • u
      + ((c - 1) * ⟪v, w⟫ + s * ⟪u, w⟫) • v := by
  simp [planeRot]; module

private lemma norm_planeRot (u v : R3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (w : R3) : ‖planeRot u v c s w‖ = ‖w‖ := by
  rw [planeRot_apply]
  set p := (c - 1) * ⟪u, w⟫ - s * ⟪v, w⟫ with hp
  set q := (c - 1) * ⟪v, w⟫ + s * ⟪u, w⟫ with hq
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hu2 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hv2 : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have h1 : ‖w + p • u + q • v‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hu2, hv2, huv, hvu]
    rw [real_inner_comm u w, real_inner_comm v w]
    have h2 : p ^ 2 + q ^ 2 = ((c - 1) ^ 2 + s ^ 2) * (⟪u, w⟫ ^ 2 + ⟪v, w⟫ ^ 2) := by
      rw [hp, hq]; ring
    have h3 : p * ⟪u, w⟫ + q * ⟪v, w⟫ = (c - 1) * (⟪u, w⟫ ^ 2 + ⟪v, w⟫ ^ 2) := by
      rw [hp, hq]; ring
    nlinarith [h2, h3]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

private def IsoSet : Set (R3 →L[ℝ] R3) := {A | ∀ x, ‖A x‖ = ‖x‖}

private lemma isoSet_isCompact : IsCompact IsoSet := by
  have hclosed : IsClosed IsoSet := by
    have : IsoSet = ⋂ x : R3, {A : R3 →L[ℝ] R3 | ‖A x‖ = ‖x‖} := by ext A; simp [IsoSet]
    rw [this]
    exact isClosed_iInter fun x => isClosed_eq ((ContinuousLinearMap.apply ℝ R3 x).continuous.norm) continuous_const
  have hbdd : Bornology.IsBounded IsoSet := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun A hA => ?_⟩
    rw [mem_closedBall_zero_iff]
    exact A.opNorm_le_bound zero_le_one fun x => by simp [hA x]
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

private noncomputable def procScore {n : ℕ} (P y : Fin n → R3) (A : R3 →L[ℝ] R3) : ℝ :=
  ∑ i, ⟪P i, A (y i)⟫

private lemma eq_zero_of_mul_le_sq_mul {α β : ℝ} (h : ∀ t : ℝ, t * β ≤ t ^ 2 * α) : β = 0 := by
  set d := 1 + |α|
  have hd0 : 0 < d := by positivity
  set t := β / d
  have htd : t * d = β := by dsimp only [t]; field_simp
  have h1 := h t
  rw [← htd] at h1
  have h3 : 1 ≤ d - α := by have := le_abs_self α; linarith
  have h4 : t ^ 2 ≤ 0 := by nlinarith [sq_nonneg t]
  have h5 : t = 0 := by nlinarith [sq_nonneg t]
  rw [← htd, h5, zero_mul]

/-- **Procrustes Gauge Lemma**: finds `g : R3 ≃ₗᵢ[ℝ] R3` making `∑ᵢ Pᵢ ⊗ g(yᵢ)` symmetric
without increasing `∑ᵢ ‖g (y i) - P i‖²`. -/
theorem exists_gauge {n : ℕ} (P y : Fin n → R3) :
    ∃ g : R3 ≃ₗᵢ[ℝ] R3,
      (∀ a b : Fin 3, ∑ i, P i a * g (y i) b = ∑ i, P i b * g (y i) a) ∧
      ∑ i, ‖g (y i) - P i‖ ^ 2 ≤ ∑ i, ‖y i - P i‖ ^ 2 := by
  have hcont : Continuous (procScore P y) :=
    continuous_finsetSum _ fun i _ => continuous_const.inner (ContinuousLinearMap.apply ℝ R3 (y i)).continuous
  have hid_mem : ContinuousLinearMap.id ℝ R3 ∈ IsoSet := fun _ => rfl
  obtain ⟨A, hA, hmax⟩ := isoSet_isCompact.exists_isMaxOn ⟨_, hid_mem⟩ hcont.continuousOn
  let g : R3 ≃ₗᵢ[ℝ] R3 :=
    LinearIsometry.toLinearIsometryEquiv { toLinearMap := A.toLinearMap, norm_map' := hA } rfl
  refine ⟨g, fun a b => ?_, ?_⟩
  · by_cases hab : a = b
    · rw [hab]
    · let u : R3 := EuclideanSpace.single a 1
      let v : R3 := EuclideanSpace.single b 1
      have hu : ‖u‖ = 1 := by simp [u]
      have hv : ‖v‖ = 1 := by simp [v]
      have huv : ⟪u, v⟫ = 0 := by simp [u, v, EuclideanSpace.inner_single_left, hab]
      set α := ∑ i, (⟪u, A (y i)⟫ * ⟪P i, u⟫ + ⟪v, A (y i)⟫ * ⟪P i, v⟫)
      set β := ∑ i, (⟪u, A (y i)⟫ * ⟪P i, v⟫ - ⟪v, A (y i)⟫ * ⟪P i, u⟫)
      have hβ0 : β = 0 := eq_zero_of_mul_le_sq_mul (α := α) fun t => by
        have hd : 0 < 1 + t ^ 2 := by positivity
        set c := (1 - t ^ 2) / (1 + t ^ 2)
        set s := 2 * t / (1 + t ^ 2)
        have hcs : c ^ 2 + s ^ 2 = 1 := by dsimp only [c, s]; field_simp; ring
        have hcomp : (planeRot u v c s).comp A ∈ IsoSet := fun w => by
          rw [ContinuousLinearMap.comp_apply, norm_planeRot u v hu hv huv c s hcs, hA w]
        have h1 := hmax hcomp
        change procScore P y ((planeRot u v c s).comp A) ≤ procScore P y A at h1
        have h2 : procScore P y ((planeRot u v c s).comp A) = procScore P y A + (c - 1) * α + s * β := by
          unfold procScore
          simp only [ContinuousLinearMap.comp_apply, planeRot_apply, inner_add_right, real_inner_smul_right,
            α, β, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [h2] at h1
        have h4 : c - 1 = -(2 * t ^ 2) / (1 + t ^ 2) := by dsimp only [c]; field_simp; ring
        have h5 : (-(2 * t ^ 2) / (1 + t ^ 2)) * α + (2 * t / (1 + t ^ 2)) * β =
            2 / (1 + t ^ 2) * (t * β - t ^ 2 * α) := by ring
        have h6 : 0 < 2 / (1 + t ^ 2) := by positivity
        dsimp only [s] at h1
        rw [h4, add_assoc, h5] at h1
        nlinarith [h1, h6]
      dsimp only [β, u, v] at hβ0
      simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
        RCLike.conj_to_real, one_mul] at hβ0
      rw [Finset.sum_sub_distrib] at hβ0
      have e1 : ∑ i, P i a * g (y i) b = ∑ i, A (y i) b * P i a :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have e2 : ∑ i, P i b * g (y i) a = ∑ i, A (y i) a * P i b :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e1, e2]; linarith
  · have hid := hmax hid_mem
    change procScore P y (ContinuousLinearMap.id ℝ R3) ≤ procScore P y A at hid
    have key : ∀ B ∈ IsoSet, ∑ i, ‖B (y i) - P i‖ ^ 2 = ∑ i, (‖y i‖ ^ 2 + ‖P i‖ ^ 2) - 2 * procScore P y B := by
      intro B hB
      unfold procScore
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_sub_sq_real, hB (y i), real_inner_comm]; ring
    have k1 := key A hA
    have k2 := key (ContinuousLinearMap.id ℝ R3) hid_mem
    have hgA : ∀ i, g (y i) = A (y i) := fun _ => rfl
    simp_rw [hgA]
    simp only [ContinuousLinearMap.id_apply] at k2
    linarith

/-! ## Section 6: Scale-`10^6` Interval Soundness & `27 × 27` Penalized Hessian Coercivity -/

def _root_.ThomsonN9.StageB.LocalMinL6Data.Iv6.inR (I : Iv6) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ 1000000 * x ∧ 1000000 * x ≤ (I.hi : ℝ)

private lemma i6Add_sound {I J : Iv6} {x y : ℝ} (hx : I.inR x) (hy : J.inR y) :
    (i6Add I J).inR (x + y) := by
  unfold Iv6.inR i6Add at *; push_cast; constructor <;> linarith

private lemma i6Neg_sound {I : Iv6} {x : ℝ} (hx : I.inR x) : (i6Neg I).inR (-x) := by
  unfold Iv6.inR i6Neg at *; push_cast; constructor <;> linarith

private lemma i6Div2_sound {I : Iv6} {x : ℝ} (hx : I.inR x) : (i6Div2 I).inR (x / 2) := by
  unfold Iv6.inR i6Div2 at *
  have h1 : 2 * Int.ediv I.lo 2 ≤ I.lo := by
    change 2 * (I.lo / 2) ≤ I.lo
    have he := Int.mul_ediv_add_emod I.lo 2
    have hm := Int.emod_nonneg I.lo (by norm_num : (2 : ℤ) ≠ 0)
    linarith
  have h2 : I.hi ≤ 2 * Int.ediv (I.hi + 1) 2 := by
    change I.hi ≤ 2 * ((I.hi + 1) / 2)
    have he := Int.mul_ediv_add_emod (I.hi + 1) 2
    have hm := Int.emod_lt_of_pos (I.hi + 1) (by norm_num : (0 : ℤ) < 2)
    linarith
  have h1R : (2 : ℝ) * (Int.ediv I.lo 2 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast h1
  have h2R : (I.hi : ℝ) ≤ (2 : ℝ) * (Int.ediv (I.hi + 1) 2 : ℝ) := by exact_mod_cast h2
  constructor <;> linarith

private lemma i6Scale_sound (k : ℤ) {I : Iv6} {x : ℝ} (hx : I.inR x) :
    (i6Scale k I).inR ((k : ℝ) * x) := by
  unfold Iv6.inR i6Scale at *
  split_ifs with hk
  · have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast; constructor <;> nlinarith
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast (show k ≤ 0 by omega)
    push_cast; constructor <;> nlinarith

private lemma i6Mul_sound {I J : Iv6} {x y : ℝ} (hx : I.inR x) (hy : J.inR y) :
    (i6Mul I J).inR (x * y) := by
  unfold Iv6.inR i6Mul at *
  set X := 1000000 * x
  set Y := 1000000 * y
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  set lo := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  set hi := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  have hlo_le : (lo : ℝ) ≤ X * Y := by
    have hlo' : (lo : ℝ) = min (min ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)))
        (min ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ))) := by
      dsimp only [lo]; push_cast; rfl
    rw [hlo']
    by_cases hy0 : 0 ≤ Y
    · have hmin : (I.lo : ℝ) * Y ≤ X * Y := mul_le_mul_of_nonneg_right hx1 hy0
      by_cases hIlo : 0 ≤ (I.lo : ℝ)
      · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
          (le_trans (mul_le_mul_of_nonneg_left hy1 hIlo) hmin)
      · exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _))
          (le_trans (mul_le_mul_of_nonpos_left hy2 (le_of_not_ge hIlo)) hmin)
    · have hmin : (I.hi : ℝ) * Y ≤ X * Y := mul_le_mul_of_nonpos_right hx2 (le_of_not_ge hy0)
      by_cases hIhi : 0 ≤ (I.hi : ℝ)
      · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
          (le_trans (mul_le_mul_of_nonneg_left hy1 hIhi) hmin)
      · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
          (le_trans (mul_le_mul_of_nonpos_left hy2 (le_of_not_ge hIhi)) hmin)
  have hhi_ge : X * Y ≤ (hi : ℝ) := by
    have hhi' : (hi : ℝ) = max (max ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)))
        (max ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ))) := by
      dsimp only [hi]; push_cast; rfl
    rw [hhi']
    by_cases hy0 : 0 ≤ Y
    · have hmax : X * Y ≤ (I.hi : ℝ) * Y := mul_le_mul_of_nonneg_right hx2 hy0
      by_cases hIhi : 0 ≤ (I.hi : ℝ)
      · exact le_trans hmax (le_trans (mul_le_mul_of_nonneg_left hy2 hIhi)
          (le_trans (le_max_right _ _) (le_max_right _ _)))
      · exact le_trans hmax (le_trans (mul_le_mul_of_nonpos_left hy1 (le_of_not_ge hIhi))
          (le_trans (le_max_left _ _) (le_max_right _ _)))
    · have hmax : X * Y ≤ (I.lo : ℝ) * Y := mul_le_mul_of_nonpos_right hx1 (le_of_not_ge hy0)
      by_cases hIlo : 0 ≤ (I.lo : ℝ)
      · exact le_trans hmax (le_trans (mul_le_mul_of_nonneg_left hy2 hIlo)
          (le_trans (le_max_right _ _) (le_max_left _ _)))
      · exact le_trans hmax (le_trans (mul_le_mul_of_nonpos_left hy1 (le_of_not_ge hIlo))
          (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hdiv1 : S6 * Int.ediv lo S6 ≤ lo := by
    change S6 * (lo / S6) ≤ lo
    have he := Int.mul_ediv_add_emod lo S6
    have hm := Int.emod_nonneg lo (b := S6) (by norm_num [S6])
    linarith
  have hdiv2 : hi ≤ S6 * (-Int.ediv (-hi) S6) := by
    change hi ≤ S6 * (-((-hi) / S6))
    have he := Int.mul_ediv_add_emod (-hi) S6
    have hm := Int.emod_nonneg (-hi) (b := S6) (by norm_num [S6])
    linarith
  have hdiv1R : (1000000 : ℝ) * (Int.ediv lo S6 : ℝ) ≤ (lo : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hdiv1
    rw [Int.cast_mul, show (S6 : ℝ) = 1000000 by norm_num [S6]] at h
    exact h
  have hdiv2R : (hi : ℝ) ≤ (1000000 : ℝ) * ((-Int.ediv (-hi) S6 : ℤ) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hdiv2
    rw [Int.cast_mul, show (S6 : ℝ) = 1000000 by norm_num [S6]] at h
    exact h
  have hXY : X * Y = 1000000 * (1000000 * (x * y)) := by dsimp only [X, Y]; ring
  constructor <;> nlinarith

private lemma i6Zero_sound : (Iv6.mk 0 0).inR 0 := by unfold Iv6.inR; norm_num

/-- Exact shifted Bregman curvature coefficient `(99/100) * (3/2) * phi (nuOfN k z - 1/200)^5`. -/
noncomputable def ac5Val (z : ℝ) (k : ℕ) : ℝ :=
  (99 / 100 : ℝ) * ((3 / 2 : ℝ) * phi (nuOfN k z - 1 / 200) ^ 5)

/-- Exact `27`-vector coordinate `d (p/3) (p%3)`. -/
def vec27 (d : Fin 9 → R3) (p : Fin 27) : ℝ :=
  d ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩

private noncomputable def rotVecReal (z : ℝ) (a b : Fin 3) (p : Fin 27) : ℝ :=
  let i : Fin 9 := ⟨p.val / 3, by omega⟩
  let c : Fin 3 := ⟨p.val % 3, by omega⟩
  if c = b then ttpPt z i a else if c = a then -ttpPt z i b else 0

/-- Exact `27 × 27` penalized Bregman Hessian entry `H_true z p q`. -/
noncomputable def H_true (z : ℝ) (p q : Fin 27) : ℝ :=
  let i : Fin 9 := ⟨p.val / 3, by omega⟩
  let a : Fin 3 := ⟨p.val % 3, by omega⟩
  let j : Fin 9 := ⟨q.val / 3, by omega⟩
  let b : Fin 3 := ⟨q.val % 3, by omega⟩
  let diagLam := if p = q then -(lamOf z i / 2) else 0
  let offPhi := if i ≠ j ∧ a = b then phiVal z (nodeOfN i.val j.val) ^ 3 / 2 else 0
  let bregDiag :=
    if i = j then
      ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * (ttpPt z k a * ttpPt z k b)
    else
      ac5Val z (nodeOfN i.val j.val) * (ttpPt z j a * ttpPt z i b)
  let normPen := if i = j then 10 * (ttpPt z i a * ttpPt z i b) else 0
  let rot01 := 5 * (rotVecReal z 0 1 p * rotVecReal z 0 1 q)
  let rot02 := 5 * (rotVecReal z 0 2 p * rotVecReal z 0 2 q)
  let rot12 := 5 * (rotVecReal z 1 2 p * rotVecReal z 1 2 q)
  ((diagLam + offPhi) + (bregDiag + normPen)) + ((rot01 + rot02) + rot12)

/-- Exact penalized Bregman quadratic form in vector form. -/
noncomputable def Q_pen (z : ℝ) (d : Fin 9 → R3) : ℝ :=
  -(1 / 2 : ℝ) * ∑ i : Fin 9, lamOf z i * ‖d i‖ ^ 2
  + ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phiVal z (nodeOfN i.val j.val) ^ 3 * ⟪d i, d j⟫
  + ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ac5Val z (nodeOfN i.val j.val) *
      (⟪ttpPt z i, d j⟫ + ⟪d i, ttpPt z j⟫) ^ 2
  + 10 * ∑ i : Fin 9, ⟪ttpPt z i, d i⟫ ^ 2
  + 5 * ((∑ i : Fin 9, (ttpPt z i 0 * d i 1 - ttpPt z i 1 * d i 0)) ^ 2
       + (∑ i : Fin 9, (ttpPt z i 0 * d i 2 - ttpPt z i 2 * d i 0)) ^ 2
       + (∑ i : Fin 9, (ttpPt z i 1 * d i 2 - ttpPt z i 2 * d i 1)) ^ 2)

private lemma sum27_eq_sum9_3 (f : Fin 9 → Fin 3 → ℝ) :
    ∑ p : Fin 27, f ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ = ∑ i : Fin 9, ∑ a : Fin 3, f i a := by
  let e : Fin 27 ≃ Fin 9 × Fin 3 :=
    { toFun := fun p => (⟨p.val / 3, by omega⟩, ⟨p.val % 3, by omega⟩)
      invFun := fun ia => ⟨3 * ia.1.val + ia.2.val, by omega⟩
      left_inv := fun p => Fin.ext (by dsimp; omega)
      right_inv := fun ⟨i, a⟩ => Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext (by dsimp; omega)) }
  rw [← Finset.sum_product']
  exact Equiv.sum_comp e (fun ia : Fin 9 × Fin 3 => f ia.1 ia.2)

private lemma sum27_vec27_sq (d : Fin 9 → R3) :
    ∑ p : Fin 27, vec27 d p ^ 2 = ∑ i : Fin 9, ‖d i‖ ^ 2 := by
  have h := sum27_eq_sum9_3 (fun i a => d i a ^ 2)
  rw [show (∑ p : Fin 27, vec27 d p ^ 2) = ∑ p : Fin 27, d ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ ^ 2 from rfl, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sq_R3_expand, Fin.sum_univ_three]

private lemma Q_pen_eq_quad27 (z : ℝ) (d : Fin 9 → R3) :
    Q_pen z d = ∑ p : Fin 27, ∑ q : Fin 27, H_true z p q * vec27 d p * vec27 d q := by
  -- Split each of the 7 additive pieces of `H_true` cleanly!
  have hsum_split : ∀ (A B : Fin 27 → Fin 27 → ℝ),
      ∑ p : Fin 27, ∑ q : Fin 27, (A p q + B p q) * vec27 d p * vec27 d q =
        (∑ p : Fin 27, ∑ q : Fin 27, A p q * vec27 d p * vec27 d q) +
        (∑ p : Fin 27, ∑ q : Fin 27, B p q * vec27 d p * vec27 d q) := by
    intro A B
    simp_rw [add_mul, Finset.sum_add_distrib]
  -- Piece 1: diagLam
  have hP1 : ∑ p : Fin 27, ∑ q : Fin 27,
      (if p = q then -(lamOf z ⟨p.val / 3, by omega⟩ / 2) else 0) * vec27 d p * vec27 d q =
      -(1 / 2 : ℝ) * ∑ i : Fin 9, lamOf z i * ‖d i‖ ^ 2 := by
    have h1 : ∀ p : Fin 27, ∑ q : Fin 27,
        (if p = q then -(lamOf z ⟨p.val / 3, by omega⟩ / 2) else 0) * vec27 d p * vec27 d q =
        -(lamOf z ⟨p.val / 3, by omega⟩ / 2) * vec27 d p ^ 2 := by
      intro p
      rw [Finset.sum_eq_single p]
      · simp [sq]; ring
      · intro q _ hqp; simp [Ne.symm hqp]
      · intro h; exact absurd (Finset.mem_univ p) h
    simp_rw [h1]
    have hstep1 := sum27_eq_sum9_3 (fun i a => -(lamOf z i / 2) * d i a ^ 2)
    rw [show (∑ p : Fin 27, -(lamOf z ⟨p.val / 3, by omega⟩ / 2) * vec27 d p ^ 2) =
        ∑ p : Fin 27, (-(lamOf z ⟨p.val / 3, by omega⟩ / 2) * d ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ ^ 2) from rfl,
      hstep1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_sq_R3_expand, Fin.sum_univ_three]; ring
  -- Piece 2: offPhi
  have hP2 : ∑ p : Fin 27, ∑ q : Fin 27,
      (if (⟨p.val / 3, by omega⟩ : Fin 9) ≠ ⟨q.val / 3, by omega⟩ ∧
          (⟨p.val % 3, by omega⟩ : Fin 3) = ⟨q.val % 3, by omega⟩
       then phiVal z (nodeOfN (p.val / 3) (q.val / 3)) ^ 3 / 2 else 0) * vec27 d p * vec27 d q =
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phiVal z (nodeOfN i.val j.val) ^ 3 * ⟪d i, d j⟫ := by
    have h2 : ∑ p : Fin 27, ∑ q : Fin 27,
        (if (⟨p.val / 3, by omega⟩ : Fin 9) ≠ ⟨q.val / 3, by omega⟩ ∧
            (⟨p.val % 3, by omega⟩ : Fin 3) = ⟨q.val % 3, by omega⟩
         then phiVal z (nodeOfN (p.val / 3) (q.val / 3)) ^ 3 / 2 else 0) * vec27 d p * vec27 d q =
        ∑ i : Fin 9, ∑ a : Fin 3, ∑ j : Fin 9, ∑ b : Fin 3,
          (if i ≠ j ∧ a = b then phiVal z (nodeOfN i.val j.val) ^ 3 / 2 else 0) * d i a * d j b := by
      have hinner : ∀ p : Fin 27, ∑ q : Fin 27,
          (if (⟨p.val / 3, by omega⟩ : Fin 9) ≠ ⟨q.val / 3, by omega⟩ ∧
              (⟨p.val % 3, by omega⟩ : Fin 3) = ⟨q.val % 3, by omega⟩
           then phiVal z (nodeOfN (p.val / 3) (q.val / 3)) ^ 3 / 2 else 0) * vec27 d p * vec27 d q =
          ∑ j : Fin 9, ∑ b : Fin 3,
            (if (⟨p.val / 3, by omega⟩ : Fin 9) ≠ j ∧ (⟨p.val % 3, by omega⟩ : Fin 3) = b
             then phiVal z (nodeOfN (p.val / 3) j.val) ^ 3 / 2 else 0) * vec27 d p * d j b :=
        fun p => sum27_eq_sum9_3 (fun j b =>
          (if (⟨p.val / 3, by omega⟩ : Fin 9) ≠ j ∧ (⟨p.val % 3, by omega⟩ : Fin 3) = b
           then phiVal z (nodeOfN (p.val / 3) j.val) ^ 3 / 2 else 0) * vec27 d p * d j b)
      simp_rw [hinner]
      exact sum27_eq_sum9_3 (fun i a => ∑ j : Fin 9, ∑ b : Fin 3,
        (if i ≠ j ∧ a = b then phiVal z (nodeOfN i.val j.val) ^ 3 / 2 else 0) * d i a * d j b)
    rw [h2]
    have hcol : ∀ i : Fin 9, ∑ a : Fin 3, ∑ j : Fin 9, ∑ b : Fin 3,
        (if i ≠ j ∧ a = b then phiVal z (nodeOfN i.val j.val) ^ 3 / 2 else 0) * d i a * d j b =
        ∑ j : Fin 9, if i ≠ j then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0 := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp
      · simp only [ne_eq, hij, not_false_eq_true, true_and, ↓reduceIte]
        have hb : ∀ a : Fin 3, ∑ b : Fin 3,
            (if a = b then phiVal z (nodeOfN i.val j.val) ^ 3 / 2 else 0) * d i a * d j b =
            (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * (d i a * d j a) := by
          intro a
          rw [Finset.sum_eq_single a]
          · simp; ring
          · intro b _ hba; simp [Ne.symm hba]
          · intro h; exact absurd (Finset.mem_univ a) h
        simp_rw [hb, ← Finset.mul_sum]
        congr 1
        rw [inner_R3_expand, Fin.sum_univ_three]
    simp_rw [hcol]
    -- Convert off-diagonal symmetric sum into upper-triangle sum!
    have hsym : ∀ i j : Fin 9,
        (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ =
        (phiVal z (nodeOfN j.val i.val) ^ 3 / 2) * ⟪d j, d i⟫ := fun i j => by
      rw [nodeOfN_symm_fin i j, real_inner_comm]
    have hsp : ∀ i j : Fin 9,
        (if i ≠ j then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0) =
        (if i < j then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0) +
        (if j < i then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0) := by
      intro i j
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h, ne_of_lt h, not_lt.mpr h.le]
      · simp
      · simp [h, ne_of_gt h, not_lt.mpr h.le]
    trans (∑ i : Fin 9, ∑ j : Fin 9,
      ((if i < j then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0) +
       (if j < i then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0)))
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsp i j
    · simp_rw [Finset.sum_add_distrib]
      have hU : ∑ i : Fin 9, ∑ j : Fin 9,
          (if i < j then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0) =
          ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ :=
        Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_filter]; congr 1; ext j; simp
      have hL : ∑ i : Fin 9, ∑ j : Fin 9,
          (if j < i then (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ else 0) =
          ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (phiVal z (nodeOfN i.val j.val) ^ 3 / 2) * ⟪d i, d j⟫ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter]
        have heq : Finset.univ.filter (fun j : Fin 9 => i < j) = Finset.Ioi i := by ext j; simp
        rw [heq]
        exact Finset.sum_congr rfl fun j _ => hsym j i
      rw [hU, hL, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
  -- Piece 3: bregDiag (sum of (⟪P i, d j⟫ + ⟪d i, P j⟫)^2 over i < j)
  have hP3 : ∑ p : Fin 27, ∑ q : Fin 27,
      (if (⟨p.val / 3, by omega⟩ : Fin 9) = ⟨q.val / 3, by omega⟩ then
        ∑ k : Fin 9, if k = ⟨p.val / 3, by omega⟩ then 0
          else ac5Val z (nodeOfN (p.val / 3) k.val) *
            (ttpPt z k ⟨p.val % 3, by omega⟩ * ttpPt z k ⟨q.val % 3, by omega⟩)
       else
        ac5Val z (nodeOfN (p.val / 3) (q.val / 3)) *
          (ttpPt z ⟨q.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
           ttpPt z ⟨p.val / 3, by omega⟩ ⟨q.val % 3, by omega⟩)) * vec27 d p * vec27 d q =
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ac5Val z (nodeOfN i.val j.val) *
        (⟪ttpPt z i, d j⟫ + ⟪d i, ttpPt z j⟫) ^ 2 := by
    have h2 : ∑ p : Fin 27, ∑ q : Fin 27,
        (if (⟨p.val / 3, by omega⟩ : Fin 9) = ⟨q.val / 3, by omega⟩ then
          ∑ k : Fin 9, if k = ⟨p.val / 3, by omega⟩ then 0
            else ac5Val z (nodeOfN (p.val / 3) k.val) *
              (ttpPt z k ⟨p.val % 3, by omega⟩ * ttpPt z k ⟨q.val % 3, by omega⟩)
         else
          ac5Val z (nodeOfN (p.val / 3) (q.val / 3)) *
            (ttpPt z ⟨q.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
             ttpPt z ⟨p.val / 3, by omega⟩ ⟨q.val % 3, by omega⟩)) * vec27 d p * vec27 d q =
        ∑ i : Fin 9, ∑ a : Fin 3, ∑ j : Fin 9, ∑ b : Fin 3,
          (if i = j then
            ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * (ttpPt z k a * ttpPt z k b)
           else
            ac5Val z (nodeOfN i.val j.val) * (ttpPt z j a * ttpPt z i b)) * d i a * d j b := by
      have hinner : ∀ p : Fin 27,
          ∑ q : Fin 27,
            (if (⟨p.val / 3, by omega⟩ : Fin 9) = ⟨q.val / 3, by omega⟩ then
              ∑ k : Fin 9, if k = ⟨p.val / 3, by omega⟩ then 0
                else ac5Val z (nodeOfN (p.val / 3) k.val) *
                  (ttpPt z k ⟨p.val % 3, by omega⟩ * ttpPt z k ⟨q.val % 3, by omega⟩)
             else
              ac5Val z (nodeOfN (p.val / 3) (q.val / 3)) *
                (ttpPt z ⟨q.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
                 ttpPt z ⟨p.val / 3, by omega⟩ ⟨q.val % 3, by omega⟩)) * vec27 d p * vec27 d q =
          ∑ j : Fin 9, ∑ b : Fin 3,
            (if (⟨p.val / 3, by omega⟩ : Fin 9) = j then
              ∑ k : Fin 9, if k = ⟨p.val / 3, by omega⟩ then 0
                else ac5Val z (nodeOfN (p.val / 3) k.val) *
                  (ttpPt z k ⟨p.val % 3, by omega⟩ * ttpPt z k b)
             else
              ac5Val z (nodeOfN (p.val / 3) j.val) *
                (ttpPt z j ⟨p.val % 3, by omega⟩ *
                 ttpPt z ⟨p.val / 3, by omega⟩ b)) * vec27 d p * d j b :=
        fun p => sum27_eq_sum9_3 (fun j b =>
          (if (⟨p.val / 3, by omega⟩ : Fin 9) = j then
            ∑ k : Fin 9, if k = ⟨p.val / 3, by omega⟩ then 0
              else ac5Val z (nodeOfN (p.val / 3) k.val) *
                (ttpPt z k ⟨p.val % 3, by omega⟩ * ttpPt z k b)
           else
            ac5Val z (nodeOfN (p.val / 3) j.val) *
              (ttpPt z j ⟨p.val % 3, by omega⟩ *
               ttpPt z ⟨p.val / 3, by omega⟩ b)) * vec27 d p * d j b)
      simp_rw [hinner]
      exact sum27_eq_sum9_3 (fun i a => ∑ j : Fin 9, ∑ b : Fin 3,
        (if i = j then
          ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * (ttpPt z k a * ttpPt z k b)
         else
          ac5Val z (nodeOfN i.val j.val) * (ttpPt z j a * ttpPt z i b)) * d i a * d j b)
    rw [h2]
    have hreord : ∀ i : Fin 9, ∑ a : Fin 3, ∑ j : Fin 9, ∑ b : Fin 3,
        (if i = j then
          ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * (ttpPt z k a * ttpPt z k b)
         else
          ac5Val z (nodeOfN i.val j.val) * (ttpPt z j a * ttpPt z i b)) * d i a * d j b =
        (∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * ⟪ttpPt z k, d i⟫ ^ 2) +
        (∑ j : Fin 9, if j = i then 0 else ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫)) := by
      intro i
      rw [Finset.sum_comm]
      have hpair_j : ∀ j : Fin 9, ∑ a : Fin 3, ∑ b : Fin 3,
          (if i = j then
            ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * (ttpPt z k a * ttpPt z k b)
           else
            ac5Val z (nodeOfN i.val j.val) * (ttpPt z j a * ttpPt z i b)) * d i a * d j b =
          if j = i then
            ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * ⟪ttpPt z k, d i⟫ ^ 2
          else
            ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) := by
        intro j
        by_cases hji : j = i
        · subst hji; simp only [↓reduceIte]
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]; conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hkj : k = j
          · simp [hkj]
          · simp only [hkj, ↓reduceIte, inner_R3_expand, Fin.sum_univ_three]; ring
        · have hij : i ≠ j := Ne.symm hji
          simp only [hij, hji, ↓reduceIte, inner_R3_expand, Fin.sum_univ_three]; ring
      simp_rw [hpair_j]
      have hsplit_j : ∀ j : Fin 9,
          (if j = i then
            ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * ⟪ttpPt z k, d i⟫ ^ 2
           else ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫)) =
          (if j = i then
            ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * ⟪ttpPt z k, d i⟫ ^ 2 else 0) +
          (if j = i then 0 else ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫)) := by
        intro j; split_ifs <;> ring
      trans (∑ j : Fin 9,
        ((if j = i then
          ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * ⟪ttpPt z k, d i⟫ ^ 2 else 0) +
         (if j = i then 0 else ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫))))
      · exact Finset.sum_congr rfl fun j _ => hsplit_j j
      · rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
    simp_rw [hreord, Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    have hcomb : ∀ i : Fin 9,
        (∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * ⟪ttpPt z k, d i⟫ ^ 2) +
        (∑ j : Fin 9, if j = i then 0 else ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫)) =
        ∑ j : Fin 9, if i ≠ j then
          ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0 := by
      intro i
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hji : j = i
      · subst hji; simp
      · have hij : i ≠ j := Ne.symm hji
        simp only [hji, hij, ne_eq, not_false_eq_true, ↓reduceIte]; ring
    simp_rw [hcomb]
    -- Split i ≠ j into i < j and j < i, then combine swapped terms into (L_ij)^2!
    have hsp : ∀ i j : Fin 9,
        (if i ≠ j then ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0) =
        (if i < j then ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0) +
        (if j < i then ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0) := by
      intro i j; rcases lt_trichotomy i j with h | rfl | h
      · simp [h, ne_of_lt h, not_lt.mpr h.le]
      · simp
      · simp [h, ne_of_gt h, not_lt.mpr h.le]
    trans (∑ i : Fin 9, ∑ j : Fin 9,
      ((if i < j then ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0) +
       (if j < i then ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0)))
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsp i j
    · simp_rw [Finset.sum_add_distrib]
      have hU : ∑ i : Fin 9, ∑ j : Fin 9,
          (if i < j then ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0) =
          ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
            ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) :=
        Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_filter]; congr 1; ext j; simp
      have hL : ∑ i : Fin 9, ∑ j : Fin 9,
          (if j < i then ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z j, d i⟫ ^ 2 + ⟪ttpPt z j, d i⟫ * ⟪ttpPt z i, d j⟫) else 0) =
          ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
            ac5Val z (nodeOfN i.val j.val) * (⟪ttpPt z i, d j⟫ ^ 2 + ⟪ttpPt z i, d j⟫ * ⟪ttpPt z j, d i⟫) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter]
        have heq : Finset.univ.filter (fun j : Fin 9 => i < j) = Finset.Ioi i := by ext j; simp
        rw [heq]
        exact Finset.sum_congr rfl fun j _ => by rw [nodeOfN_sym j.val i.val j.isLt i.isLt]
      rw [hU, hL, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm (d i) (ttpPt z j)]; ring
  -- Piece 4: normPen
  have hP4 : ∑ p : Fin 27, ∑ q : Fin 27,
      (if (⟨p.val / 3, by omega⟩ : Fin 9) = ⟨q.val / 3, by omega⟩
       then 10 * (ttpPt z ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
                  ttpPt z ⟨p.val / 3, by omega⟩ ⟨q.val % 3, by omega⟩) else 0) * vec27 d p * vec27 d q =
      10 * ∑ i : Fin 9, ⟪ttpPt z i, d i⟫ ^ 2 := by
    have h2 : ∑ p : Fin 27, ∑ q : Fin 27,
        (if (⟨p.val / 3, by omega⟩ : Fin 9) = ⟨q.val / 3, by omega⟩
         then 10 * (ttpPt z ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
                    ttpPt z ⟨p.val / 3, by omega⟩ ⟨q.val % 3, by omega⟩) else 0) * vec27 d p * vec27 d q =
        ∑ i : Fin 9, ∑ a : Fin 3, ∑ j : Fin 9, ∑ b : Fin 3,
          (if i = j then 10 * (ttpPt z i a * ttpPt z i b) else 0) * d i a * d j b := by
      have hinner : ∀ p : Fin 27,
          ∑ q : Fin 27,
            (if (⟨p.val / 3, by omega⟩ : Fin 9) = ⟨q.val / 3, by omega⟩
             then 10 * (ttpPt z ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
                        ttpPt z ⟨p.val / 3, by omega⟩ ⟨q.val % 3, by omega⟩) else 0) * vec27 d p * vec27 d q =
          ∑ j : Fin 9, ∑ b : Fin 3,
            (if (⟨p.val / 3, by omega⟩ : Fin 9) = j
             then 10 * (ttpPt z ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
                        ttpPt z ⟨p.val / 3, by omega⟩ b) else 0) * vec27 d p * d j b :=
        fun p => sum27_eq_sum9_3 (fun j b =>
          (if (⟨p.val / 3, by omega⟩ : Fin 9) = j
           then 10 * (ttpPt z ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ *
                      ttpPt z ⟨p.val / 3, by omega⟩ b) else 0) * vec27 d p * d j b)
      simp_rw [hinner]
      exact sum27_eq_sum9_3 (fun i a => ∑ j : Fin 9, ∑ b : Fin 3,
        (if i = j then 10 * (ttpPt z i a * ttpPt z i b) else 0) * d i a * d j b)
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · simp only [↓reduceIte, inner_R3_expand, Fin.sum_univ_three]; ring
    · intro j _ hji; simp [Ne.symm hji]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Piece 5: rotPen helper for any a ≠ b : Fin 3
  have hRot : ∀ a b : Fin 3, a ≠ b →
      ∑ p : Fin 27, ∑ q : Fin 27, (5 * (rotVecReal z a b p * rotVecReal z a b q)) * vec27 d p * vec27 d q =
        5 * (∑ i : Fin 9, (ttpPt z i a * d i b - ttpPt z i b * d i a)) ^ 2 := by
    intro a b hab
    have hfac : ∑ p : Fin 27, ∑ q : Fin 27,
        (5 * (rotVecReal z a b p * rotVecReal z a b q)) * vec27 d p * vec27 d q =
        5 * (∑ p : Fin 27, rotVecReal z a b p * vec27 d p) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hfac]; congr 2
    have hrot_sum := sum27_eq_sum9_3 (fun i c =>
      (if c = b then ttpPt z i a else if c = a then -ttpPt z i b else 0) * d i c)
    rw [show (∑ p : Fin 27, rotVecReal z a b p * vec27 d p) =
        ∑ p : Fin 27, (if (⟨p.val % 3, by omega⟩ : Fin 3) = b then ttpPt z ⟨p.val / 3, by omega⟩ a
                       else if (⟨p.val % 3, by omega⟩ : Fin 3) = a then -ttpPt z ⟨p.val / 3, by omega⟩ b
                       else 0) * d ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ from rfl,
      hrot_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    fin_cases a <;> fin_cases b <;> first | (exact absurd rfl hab) | (simp [Fin.sum_univ_three]; ring)
  unfold H_true
  simp_rw [hsum_split]
  rw [hP1, hP2, hP3, hP4, hRot 0 1 (by decide), hRot 0 2 (by decide), hRot 1 2 (by decide)]
  unfold Q_pen
  ring

private lemma ivHentry_sound {z : ℝ} (hzLo : (zStarLo : ℝ) ≤ z) (hzHi : z ≤ (zStarHi : ℝ))
    (p q : Fin 27) : (ivHentry p.val q.val).inR (H_true z p q) := by
  have hzLo0 : (0 : ℝ) < (zStarLo : ℝ) := by norm_num [zStarLo]
  have hz0 : 0 < z := lt_of_lt_of_le hzLo0 hzLo
  obtain ⟨hs3l, hs3h, hs3p, hrl, hrh, hrlp, hr0l, hr0h, hr0p, hr1l, hr1h, hr1p, hr5l, hr5h, hr5p⟩ := env_sq_ok
  obtain ⟨h0l, h0h, h0p, h1l, h1h, h1p, h2l, h2h, h2p, h3l, h3h, h3p, h4l, h4h, h4p, h5l, h5h, h5p⟩ := sr_sq_ok
  have hs3_lo : (s3Lo : ℝ) ≤ Real.sqrt 3 := sqrt_lo_le hs3p (by exact_mod_cast hs3l)
  have hs3_hi : Real.sqrt 3 ≤ (s3Hi : ℝ) := sqrt_le_hi (by norm_num [s3Hi]) (by exact_mod_cast hs3h)
  have hrho_lo : (rhoStarLo : ℝ) ≤ Real.sqrt (1 - z ^ 2) :=
    sqrt_lo_le hrlp (le_trans (by exact_mod_cast hrl : (rhoStarLo : ℝ) ^ 2 ≤ 1 - (zStarHi : ℝ) ^ 2) (by nlinarith [hz0, hzHi]))
  have hrho_hi : Real.sqrt (1 - z ^ 2) ≤ (rhoStarHi : ℝ) :=
    sqrt_le_hi (by norm_num [rhoStarHi]) (le_trans (by nlinarith [hzLo0, hz0, hzLo]) (by exact_mod_cast hrh : 1 - (zStarLo : ℝ) ^ 2 ≤ (rhoStarHi : ℝ) ^ 2))
  have hr0_lo : (r0Lo : ℝ) ≤ Real.sqrt (3 + z ^ 2) :=
    sqrt_lo_le hr0p (le_trans (by exact_mod_cast hr0l : (r0Lo : ℝ) ^ 2 ≤ 3 + (zStarLo : ℝ) ^ 2) (by nlinarith [hzLo0, hz0, hzLo]))
  have hr0_hi : Real.sqrt (3 + z ^ 2) ≤ (r0Hi : ℝ) :=
    sqrt_le_hi (by norm_num [r0Hi]) (le_trans (by nlinarith [hz0, hzHi]) (by exact_mod_cast hr0h : 3 + (zStarHi : ℝ) ^ 2 ≤ (r0Hi : ℝ) ^ 2))
  have hr1_lo : (r1Lo : ℝ) ≤ Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) :=
    sqrt_lo_le hr1p (le_trans (by exact_mod_cast hr1l : (r1Lo : ℝ) ^ 2 ≤ 2 + 2 * (rhoStarLo : ℝ)) (by linarith))
  have hr1_hi : Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ≤ (r1Hi : ℝ) :=
    sqrt_le_hi (by norm_num [r1Hi]) (le_trans (by linarith) (by exact_mod_cast hr1h : 2 + 2 * (rhoStarHi : ℝ) ≤ (r1Hi : ℝ) ^ 2))
  have hr5_lo : (r5Lo : ℝ) ≤ Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) :=
    sqrt_lo_le hr5p (le_trans (by exact_mod_cast hr5l : (r5Lo : ℝ) ^ 2 ≤ 2 - (rhoStarHi : ℝ)) (by linarith))
  have hr5_hi : Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ≤ (r5Hi : ℝ) :=
    sqrt_le_hi (by norm_num [r5Hi]) (le_trans (by linarith) (by exact_mod_cast hr5h : 2 - (rhoStarLo : ℝ) ≤ (r5Hi : ℝ) ^ 2))
  have hsc := iv_scalars_ok
  have h_ivZ : ivZ.inR z := by
    unfold Iv6.inR
    have h1 : (ivZ.lo : ℝ) / 1000000 ≤ (zStarLo : ℝ) := by exact_mod_cast hsc.1
    have h2 : (zStarHi : ℝ) ≤ (ivZ.hi : ℝ) / 1000000 := by exact_mod_cast hsc.2.1
    constructor <;> linarith
  have h_ivRho : ivRho.inR (Real.sqrt (1 - z ^ 2)) := by
    unfold Iv6.inR
    have h1 : (ivRho.lo : ℝ) / 1000000 ≤ (rhoStarLo : ℝ) := by exact_mod_cast hsc.2.2.1
    have h2 : (rhoStarHi : ℝ) ≤ (ivRho.hi : ℝ) / 1000000 := by exact_mod_cast hsc.2.2.2.1
    constructor <;> linarith
  have h_ivS3 : ivS3.inR (Real.sqrt 3) := by
    unfold Iv6.inR
    have h1 : (ivS3.lo : ℝ) / 1000000 ≤ (s3Lo : ℝ) := by exact_mod_cast hsc.2.2.2.2.1
    have h2 : (s3Hi : ℝ) ≤ (ivS3.hi : ℝ) / 1000000 := by exact_mod_cast hsc.2.2.2.2.2.1
    constructor <;> linarith
  have h_ivS3Rho : ivS3Rho.inR (Real.sqrt 3 * Real.sqrt (1 - z ^ 2)) := by
    unfold Iv6.inR
    have h1 : (ivS3Rho.lo : ℝ) / 1000000 ≤ (s3Lo : ℝ) * (rhoStarLo : ℝ) := by exact_mod_cast hsc.2.2.2.2.2.2.1
    have h2 : (s3Hi : ℝ) * (rhoStarHi : ℝ) ≤ (ivS3Rho.hi : ℝ) / 1000000 := by exact_mod_cast hsc.2.2.2.2.2.2.2.1
    have hm1 : (s3Lo : ℝ) * (rhoStarLo : ℝ) ≤ Real.sqrt 3 * Real.sqrt (1 - z ^ 2) :=
      mul_le_mul hs3_lo hrho_lo (by exact_mod_cast hrlp.le) (Real.sqrt_nonneg _)
    have hm2 : Real.sqrt 3 * Real.sqrt (1 - z ^ 2) ≤ (s3Hi : ℝ) * (rhoStarHi : ℝ) :=
      mul_le_mul hs3_hi hrho_hi (Real.sqrt_nonneg _) (by norm_num [s3Hi])
    constructor <;> linarith
  have h_ivP : ∀ i : Fin 9, ∀ a : Fin 3, (ivP i.val a.val).inR (ttpPt z i a) := by
    intro i a
    have h500 : (Iv6.mk 500000 500000).inR (1 / 2) := by unfold Iv6.inR; norm_num
    have hm1 : (Iv6.mk (-1000000) (-1000000)).inR (-1) := by unfold Iv6.inR; norm_num
    fin_cases i <;> fin_cases a <;>
      simp only [ivP, ttpPt, ttpX, ttpRow, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
    · exact h_ivRho
    · exact i6Zero_sound
    · exact h_ivZ
    · simpa [neg_div] using i6Neg_sound (i6Div2_sound h_ivRho)
    · exact i6Div2_sound h_ivS3Rho
    · exact h_ivZ
    · simpa [neg_div] using i6Neg_sound (i6Div2_sound h_ivRho)
    · simpa [neg_div] using i6Neg_sound (i6Div2_sound h_ivS3Rho)
    · exact h_ivZ
    · exact h_ivRho
    · exact i6Zero_sound
    · exact i6Neg_sound h_ivZ
    · simpa [neg_div] using i6Neg_sound (i6Div2_sound h_ivRho)
    · exact i6Div2_sound h_ivS3Rho
    · exact i6Neg_sound h_ivZ
    · simpa [neg_div] using i6Neg_sound (i6Div2_sound h_ivRho)
    · simpa [neg_div] using i6Neg_sound (i6Div2_sound h_ivS3Rho)
    · exact i6Neg_sound h_ivZ
    · exact h500
    · exact i6Div2_sound h_ivS3
    · exact i6Zero_sound
    · exact hm1
    · exact i6Zero_sound
    · exact i6Zero_sound
    · exact h500
    · simpa [neg_div] using i6Neg_sound (i6Div2_sound h_ivS3)
    · exact i6Zero_sound
  have hscP := hsc.2.2.2.2.2.2.2.2
  have h_ivPhi3 : ∀ k < 6, (ivPhi3 k).inR (phiVal z k ^ 3) := by
    intro k hk
    interval_cases k
    · simp only [Iv6.inR, phiVal]
      have h1 : ((ivPhi3 0).lo : ℝ) / 1000000 ≤ 1 / (r0Hi : ℝ) ^ 3 := by exact_mod_cast hscP.1
      have h2 : 1 / (r0Lo : ℝ) ^ 3 ≤ ((ivPhi3 0).hi : ℝ) / 1000000 := by exact_mod_cast hscP.2.1
      have ha := inv_pow3_anti (by exact_mod_cast hr0p) hr0_lo
      have hb := inv_pow3_anti (Real.sqrt_pos.mpr (by positivity)) hr0_hi
      rw [_root_.one_div_pow]; constructor <;> linarith
    · simp only [Iv6.inR, phiVal]
      have h1 : ((ivPhi3 1).lo : ℝ) / 1000000 ≤ 1 / (r1Hi : ℝ) ^ 3 := by exact_mod_cast hscP.2.2.1
      have h2 : 1 / (r1Lo : ℝ) ^ 3 ≤ ((ivPhi3 1).hi : ℝ) / 1000000 := by exact_mod_cast hscP.2.2.2.1
      have ha := inv_pow3_anti (by exact_mod_cast hr1p) hr1_lo
      have hb := inv_pow3_anti (Real.sqrt_pos.mpr (by linarith [Real.sqrt_nonneg (1 - z ^ 2)])) hr1_hi
      rw [_root_.one_div_pow]; constructor <;> linarith
    · simp only [Iv6.inR, phiVal]
      have h1 : ((ivPhi3 2).lo : ℝ) / 1000000 ≤ 1 / (s3Hi : ℝ) ^ 3 := by exact_mod_cast hscP.2.2.2.2.1
      have h2 : 1 / (s3Lo : ℝ) ^ 3 ≤ ((ivPhi3 2).hi : ℝ) / 1000000 := by exact_mod_cast hscP.2.2.2.2.2.1
      have ha := inv_pow3_anti (by exact_mod_cast hs3p) hs3_lo
      have hb := inv_pow3_anti (Real.sqrt_pos.mpr (by norm_num)) hs3_hi
      rw [_root_.one_div_pow]; constructor <;> linarith
    · simp only [Iv6.inR, phiVal]
      have h1 : ((ivPhi3 3).lo : ℝ) / 1000000 ≤ 1 / (2 * (zStarHi : ℝ)) ^ 3 := by exact_mod_cast hscP.2.2.2.2.2.2.1
      have h2 : 1 / (2 * (zStarLo : ℝ)) ^ 3 ≤ ((ivPhi3 3).hi : ℝ) / 1000000 := by exact_mod_cast hscP.2.2.2.2.2.2.2.1
      have ha := inv_pow3_anti (by norm_num [zStarLo]) (by linarith : 2 * (zStarLo : ℝ) ≤ 2 * z)
      have hb := inv_pow3_anti (by linarith) (by linarith : 2 * z ≤ 2 * (zStarHi : ℝ))
      rw [_root_.one_div_pow]; constructor <;> linarith
    · simp only [Iv6.inR, phiVal]
      have h1 : ((ivPhi3 4).lo : ℝ) / 1000000 ≤ 1 / ((s3Hi : ℝ) * (rhoStarHi : ℝ)) ^ 3 := by
        exact_mod_cast hscP.2.2.2.2.2.2.2.2.1
      have h2 : 1 / ((s3Lo : ℝ) * (rhoStarLo : ℝ)) ^ 3 ≤ ((ivPhi3 4).hi : ℝ) / 1000000 := by
        exact_mod_cast hscP.2.2.2.2.2.2.2.2.2.1
      have hm1 : (s3Lo : ℝ) * (rhoStarLo : ℝ) ≤ Real.sqrt 3 * Real.sqrt (1 - z ^ 2) :=
        mul_le_mul hs3_lo hrho_lo (by exact_mod_cast hrlp.le) (Real.sqrt_nonneg _)
      have hm2 : Real.sqrt 3 * Real.sqrt (1 - z ^ 2) ≤ (s3Hi : ℝ) * (rhoStarHi : ℝ) :=
        mul_le_mul hs3_hi hrho_hi (Real.sqrt_nonneg _) (by norm_num [s3Hi])
      have ha := inv_pow3_anti (mul_pos (by exact_mod_cast hs3p) (by exact_mod_cast hrlp)) hm1
      have hb := inv_pow3_anti (mul_pos (Real.sqrt_pos.mpr (by norm_num))
        (lt_of_lt_of_le (by exact_mod_cast hrlp) hrho_lo)) hm2
      rw [_root_.one_div_pow]; constructor <;> linarith
    · simp only [Iv6.inR, phiVal]
      have h1 : ((ivPhi3 5).lo : ℝ) / 1000000 ≤ 1 / (r5Hi : ℝ) ^ 3 := by
        exact_mod_cast hscP.2.2.2.2.2.2.2.2.2.2.1
      have h2 : 1 / (r5Lo : ℝ) ^ 3 ≤ ((ivPhi3 5).hi : ℝ) / 1000000 := by
        exact_mod_cast hscP.2.2.2.2.2.2.2.2.2.2.2.1
      have h2mr_pos : 0 < 2 - Real.sqrt (1 - z ^ 2) := by
        have : (rhoStarHi : ℝ) < 2 := by norm_num [rhoStarHi]
        linarith
      have ha := inv_pow3_anti (by exact_mod_cast hr5p) hr5_lo
      have hb := inv_pow3_anti (Real.sqrt_pos.mpr h2mr_pos) hr5_hi
      rw [_root_.one_div_pow]; constructor <;> linarith
  have hscA := hscP.2.2.2.2.2.2.2.2.2.2.2.2
  have h_ivAC5 : ∀ k < 6, (ivAC5 k).inR (ac5Val z k) := by
    have hstep : ∀ {k : ℕ} {srL srH : ℚ} (d2 : ℝ),
        (0 : ℚ) < srL → (0 : ℚ) < srH →
        (srL : ℝ) ≤ Real.sqrt d2 → Real.sqrt d2 ≤ (srH : ℝ) →
        2 - 2 * (nuOfN k z - 1 / 200) = d2 →
        ((ivAC5 k).lo : ℚ) / 1000000 ≤ 99 / 100 * (3 / (2 * srH ^ 5)) →
        99 / 100 * (3 / (2 * srL ^ 5)) ≤ ((ivAC5 k).hi : ℚ) / 1000000 →
        (ivAC5 k).inR (ac5Val z k) := by
      intro k srL srH d2 hpL hpH hL hH hd2 hq1 hq2
      have hLpos : (0 : ℝ) < (srL : ℝ) := by exact_mod_cast hpL
      have hHpos : (0 : ℝ) < (srH : ℝ) := by exact_mod_cast hpH
      have hspos : 0 < Real.sqrt d2 := lt_of_lt_of_le hLpos hL
      have hphi5 : phi (nuOfN k z - 1 / 200) ^ 5 = 1 / Real.sqrt d2 ^ 5 := by
        unfold phi; rw [hd2, inv_eq_one_div, _root_.one_div_pow]
      have hinv1 : 1 / (srH : ℝ) ^ 5 ≤ 1 / Real.sqrt d2 ^ 5 :=
        one_div_le_one_div_of_le (pow_pos hspos 5) (pow_le_pow_left₀ hspos.le hH 5)
      have hinv2 : 1 / Real.sqrt d2 ^ 5 ≤ 1 / (srL : ℝ) ^ 5 :=
        one_div_le_one_div_of_le (pow_pos hLpos 5) (pow_le_pow_left₀ hLpos.le hL 5)
      have hr1 : (((ivAC5 k).lo : ℚ) / 1000000 : ℝ) ≤ (99 / 100 * (3 / (2 * srH ^ 5)) : ℚ) := by exact_mod_cast hq1
      have hr2 : ((99 / 100 * (3 / (2 * srL ^ 5)) : ℚ) : ℝ) ≤ (((ivAC5 k).hi : ℚ) / 1000000 : ℚ) := by exact_mod_cast hq2
      push_cast at hr1 hr2
      unfold Iv6.inR ac5Val
      rw [hphi5]
      have ha : 3 / (2 * (srH : ℝ) ^ 5) = 3 / 2 * (1 / (srH : ℝ) ^ 5) := by ring
      have hb : 3 / (2 * (srL : ℝ) ^ 5) = 3 / 2 * (1 / (srL : ℝ) ^ 5) := by ring
      rw [ha] at hr1; rw [hb] at hr2
      constructor <;> linarith
    intro k hk
    interval_cases k
    · have hlR : ((srLo_0 ^ 2 : ℚ) : ℝ) ≤ ((3 + zStarLo ^ 2 + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h0l
      have hhR : ((3 + zStarHi ^ 2 + 1 / 100 : ℚ) : ℝ) ≤ ((srHi_0 ^ 2 : ℚ) : ℝ) := by exact_mod_cast h0h
      push_cast at hlR hhR
      exact hstep (3 + z ^ 2 + 1 / 100) h0p (by norm_num [srHi_0])
        (sqrt_lo_le h0p (by nlinarith [hzLo0, hz0, hzLo]))
        (sqrt_le_hi (by norm_num [srHi_0]) (by nlinarith [hz0, hzHi]))
        (by simp only [nuOfN, nu1]; ring) hscA.1 hscA.2.1
    · have hlR : ((srLo_1 ^ 2 : ℚ) : ℝ) ≤ ((2 + 2 * rhoStarLo + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h1l
      have hhR : ((2 + 2 * rhoStarHi + 1 / 100 : ℚ) : ℝ) ≤ ((srHi_1 ^ 2 : ℚ) : ℝ) := by exact_mod_cast h1h
      push_cast at hlR hhR
      exact hstep (2 + 2 * Real.sqrt (1 - z ^ 2) + 1 / 100) h1p (by norm_num [srHi_1])
        (sqrt_lo_le h1p (by linarith))
        (sqrt_le_hi (by norm_num [srHi_1]) (by linarith))
        (by simp only [nuOfN, nu2, rhoR]; ring) hscA.2.2.1 hscA.2.2.2.1
    · have hlR : ((srLo_2 ^ 2 : ℚ) : ℝ) ≤ ((3 + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h2l
      have hhR : ((3 + 1 / 100 : ℚ) : ℝ) ≤ ((srHi_2 ^ 2 : ℚ) : ℝ) := by exact_mod_cast h2h
      push_cast at hlR hhR
      exact hstep (3 + 1 / 100) h2p (by norm_num [srHi_2])
        (sqrt_lo_le h2p hlR) (sqrt_le_hi (by norm_num [srHi_2]) hhR)
        (by simp only [nuOfN, nu3]; ring) hscA.2.2.2.2.1 hscA.2.2.2.2.2.1
    · have hlR : ((srLo_3 ^ 2 : ℚ) : ℝ) ≤ ((4 * zStarLo ^ 2 + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h3l
      have hhR : ((4 * zStarHi ^ 2 + 1 / 100 : ℚ) : ℝ) ≤ ((srHi_3 ^ 2 : ℚ) : ℝ) := by exact_mod_cast h3h
      push_cast at hlR hhR
      exact hstep (4 * z ^ 2 + 1 / 100) h3p (by norm_num [srHi_3])
        (sqrt_lo_le h3p (by nlinarith [hzLo0, hz0, hzLo]))
        (sqrt_le_hi (by norm_num [srHi_3]) (by nlinarith [hz0, hzHi]))
        (by simp only [nuOfN, nu4]; ring) hscA.2.2.2.2.2.2.1 hscA.2.2.2.2.2.2.2.1
    · have hlR : ((srLo_4 ^ 2 : ℚ) : ℝ) ≤ ((3 * (1 - zStarHi ^ 2) + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h4l
      have hhR : ((3 * (1 - zStarLo ^ 2) + 1 / 100 : ℚ) : ℝ) ≤ ((srHi_4 ^ 2 : ℚ) : ℝ) := by exact_mod_cast h4h
      push_cast at hlR hhR
      exact hstep (3 * (1 - z ^ 2) + 1 / 100) h4p (by norm_num [srHi_4])
        (sqrt_lo_le h4p (by nlinarith [hz0, hzHi]))
        (sqrt_le_hi (by norm_num [srHi_4]) (by nlinarith [hzLo0, hz0, hzLo]))
        (by simp only [nuOfN, nu5]; ring) hscA.2.2.2.2.2.2.2.2.1 hscA.2.2.2.2.2.2.2.2.2.1
    · have hlR : ((srLo_5 ^ 2 : ℚ) : ℝ) ≤ ((2 - rhoStarHi + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h5l
      have hhR : ((2 - rhoStarLo + 1 / 100 : ℚ) : ℝ) ≤ ((srHi_5 ^ 2 : ℚ) : ℝ) := by exact_mod_cast h5h
      push_cast at hlR hhR
      exact hstep (2 - Real.sqrt (1 - z ^ 2) + 1 / 100) h5p (by norm_num [srHi_5])
        (sqrt_lo_le h5p (by linarith))
        (sqrt_le_hi (by norm_num [srHi_5]) (by linarith))
        (by simp only [nuOfN, nu6, rhoR]; ring) hscA.2.2.2.2.2.2.2.2.2.2.1 hscA.2.2.2.2.2.2.2.2.2.2.2.1
  have hscL := hscA.2.2.2.2.2.2.2.2.2.2.2.2
  have h_ivLamP : ivLamP.inR (lamP z) := by
    unfold Iv6.inR lamP
    have hq1 : (ivLamP.lo : ℝ) / 1000000 ≤
        2 / ((s3Hi : ℝ) * (rhoStarHi : ℝ)) ^ 3 - 1 / (2 * (zStarLo : ℝ)) ^ 3 - 2 / (r0Lo : ℝ) ^ 3 := by
      exact_mod_cast hscL.1
    have hq2 : 2 / ((s3Lo : ℝ) * (rhoStarLo : ℝ)) ^ 3 - 1 / (2 * (zStarHi : ℝ)) ^ 3 - 2 / (r0Hi : ℝ) ^ 3 ≤
        (ivLamP.hi : ℝ) / 1000000 := by exact_mod_cast hscL.2.1
    have hm1 : (s3Lo : ℝ) * (rhoStarLo : ℝ) ≤ Real.sqrt 3 * Real.sqrt (1 - z ^ 2) :=
      mul_le_mul hs3_lo hrho_lo (by exact_mod_cast hrlp.le) (Real.sqrt_nonneg _)
    have hm2 : Real.sqrt 3 * Real.sqrt (1 - z ^ 2) ≤ (s3Hi : ℝ) * (rhoStarHi : ℝ) :=
      mul_le_mul hs3_hi hrho_hi (Real.sqrt_nonneg _) (by norm_num [s3Hi])
    have e4a := inv_pow3_anti (mul_pos (by exact_mod_cast hs3p) (by exact_mod_cast hrlp)) hm1
    have e4b := inv_pow3_anti (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (lt_of_lt_of_le (by exact_mod_cast hrlp) hrho_lo)) hm2
    have e3a := inv_pow3_anti (by norm_num [zStarLo]) (by linarith : 2 * (zStarLo : ℝ) ≤ 2 * z)
    have e3b := inv_pow3_anti (by linarith) (by linarith : 2 * z ≤ 2 * (zStarHi : ℝ))
    have e0a := inv_pow3_anti (by exact_mod_cast hr0p) hr0_lo
    have e0b := inv_pow3_anti (Real.sqrt_pos.mpr (by positivity)) hr0_hi
    have hdiv2 : ∀ u : ℝ, 2 / u = 2 * (1 / u) := fun u => by ring
    rw [hdiv2, hdiv2] at hq1 hq2 ⊢
    constructor <;> linarith
  have h_ivLamC : ivLamC.inR (lamC z) := by
    unfold Iv6.inR lamC
    have hq1 : (ivLamC.lo : ℝ) / 1000000 ≤
        2 * (rhoStarLo : ℝ) / (r5Hi : ℝ) ^ 3 - 2 * (rhoStarHi : ℝ) / (r1Lo : ℝ) ^ 3 - 1 / (s3Lo : ℝ) ^ 3 := by
      exact_mod_cast hscL.2.2.1
    have hq2 : 2 * (rhoStarHi : ℝ) / (r5Lo : ℝ) ^ 3 - 2 * (rhoStarLo : ℝ) / (r1Hi : ℝ) ^ 3 - 1 / (s3Hi : ℝ) ^ 3 ≤
        (ivLamC.hi : ℝ) / 1000000 := by exact_mod_cast hscL.2.2.2
    have h2mr_pos : 0 < 2 - Real.sqrt (1 - z ^ 2) := by
      have : (rhoStarHi : ℝ) < 2 := by norm_num [rhoStarHi]
      linarith
    have e5a := inv_pow3_anti (by exact_mod_cast hr5p) hr5_lo
    have e5b := inv_pow3_anti (Real.sqrt_pos.mpr h2mr_pos) hr5_hi
    have e1a := inv_pow3_anti (by exact_mod_cast hr1p) hr1_lo
    have e1b := inv_pow3_anti (Real.sqrt_pos.mpr (by linarith [Real.sqrt_nonneg (1 - z ^ 2)])) hr1_hi
    have e2a := inv_pow3_anti (by exact_mod_cast hs3p) hs3_lo
    have e2b := inv_pow3_anti (Real.sqrt_pos.mpr (by norm_num)) hs3_hi
    have hrho_nn : (0 : ℝ) ≤ (rhoStarLo : ℝ) := by exact_mod_cast hrlp.le
    have t5a : 2 * (rhoStarLo : ℝ) / (r5Hi : ℝ) ^ 3 ≤ 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 := by
      rw [show 2 * (rhoStarLo : ℝ) / (r5Hi : ℝ) ^ 3 = (2 * (rhoStarLo : ℝ)) * (1 / (r5Hi : ℝ) ^ 3) by ring,
          show 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 =
            (2 * Real.sqrt (1 - z ^ 2)) * (1 / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3) by ring]
      exact mul_le_mul (by linarith) e5b (by norm_num [r5Hi]) (by linarith)
    have t5b : 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 ≤ 2 * (rhoStarHi : ℝ) / (r5Lo : ℝ) ^ 3 := by
      rw [show 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3 =
            (2 * Real.sqrt (1 - z ^ 2)) * (1 / Real.sqrt (2 - Real.sqrt (1 - z ^ 2)) ^ 3) by ring,
          show 2 * (rhoStarHi : ℝ) / (r5Lo : ℝ) ^ 3 = (2 * (rhoStarHi : ℝ)) * (1 / (r5Lo : ℝ) ^ 3) by ring]
      exact mul_le_mul (by linarith) e5a (by positivity) (by norm_num [rhoStarHi])
    have t1a : 2 * (rhoStarLo : ℝ) / (r1Hi : ℝ) ^ 3 ≤ 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3 := by
      rw [show 2 * (rhoStarLo : ℝ) / (r1Hi : ℝ) ^ 3 = (2 * (rhoStarLo : ℝ)) * (1 / (r1Hi : ℝ) ^ 3) by ring,
          show 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3 =
            (2 * Real.sqrt (1 - z ^ 2)) * (1 / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3) by ring]
      exact mul_le_mul (by linarith) e1b (by norm_num [r1Hi]) (by linarith)
    have t1b : 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3 ≤ 2 * (rhoStarHi : ℝ) / (r1Lo : ℝ) ^ 3 := by
      rw [show 2 * Real.sqrt (1 - z ^ 2) / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3 =
            (2 * Real.sqrt (1 - z ^ 2)) * (1 / Real.sqrt (2 + 2 * Real.sqrt (1 - z ^ 2)) ^ 3) by ring,
          show 2 * (rhoStarHi : ℝ) / (r1Lo : ℝ) ^ 3 = (2 * (rhoStarHi : ℝ)) * (1 / (r1Lo : ℝ) ^ 3) by ring]
      exact mul_le_mul (by linarith) e1a (by positivity) (by norm_num [rhoStarHi])
    constructor <;> linarith
  have h_ivRot : ∀ (a b : Fin 3) (r : Fin 27), (ivRotVec a.val b.val r.val).inR (rotVecReal z a b r) := by
    intro a b r
    unfold ivRotVec rotVecReal
    by_cases h1 : (⟨r.val % 3, by omega⟩ : Fin 3) = b
    · have h1' : (r.val % 3 == b.val) = true := by simp [← h1]
      simp only [h1, h1', ↓reduceIte]
      exact h_ivP ⟨r.val / 3, by omega⟩ a
    · have h1' : (r.val % 3 == b.val) = false := by
        simp only [beq_eq_false_iff_ne]; intro hc; exact h1 (Fin.ext hc)
      simp only [h1, h1', Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (⟨r.val % 3, by omega⟩ : Fin 3) = a
      · have h2' : (r.val % 3 == a.val) = true := by simp [← h2]
        simp only [h2, h2', ↓reduceIte]
        exact i6Neg_sound (h_ivP ⟨r.val / 3, by omega⟩ b)
      · have h2' : (r.val % 3 == a.val) = false := by
          simp only [beq_eq_false_iff_ne]; intro hc; exact h2 (Fin.ext hc)
        simp only [h2, h2', Bool.false_eq_true, ↓reduceIte]
        exact i6Zero_sound
  -- Assemble all 7 additive pieces of `ivHentry p.val q.val` vs `H_true z p q`!
  unfold ivHentry H_true
  set i : Fin 9 := ⟨p.val / 3, by omega⟩
  set a : Fin 3 := ⟨p.val % 3, by omega⟩
  set j : Fin 9 := ⟨q.val / 3, by omega⟩
  set b : Fin 3 := ⟨q.val % 3, by omega⟩
  have h1 : (if p.val == q.val then i6Neg (i6Div2 (if i.val < 6 then ivLamP else ivLamC)) else ⟨0, 0⟩).inR
      (if p = q then -(lamOf z i / 2) else 0) := by
    by_cases hpq : p = q
    · subst hpq; simp only [beq_self_eq_true, ↓reduceIte, lamOf]
      split_ifs
      · exact i6Neg_sound (i6Div2_sound h_ivLamP)
      · exact i6Neg_sound (i6Div2_sound h_ivLamC)
    · have hpq' : (p.val == q.val) = false := by simp [Fin.ext_iff] at hpq; simp [hpq]
      simp only [hpq, hpq', Bool.false_eq_true, ↓reduceIte]; exact i6Zero_sound
  have h2 : (if (i.val != j.val && (a.val == b.val)) = true then i6Div2 (ivPhi3 (nodeOfN i.val j.val)) else ⟨0, 0⟩).inR
      (if i ≠ j ∧ a = b then phiVal z (nodeOfN i.val j.val) ^ 3 / 2 else 0) := by
    by_cases hc : i ≠ j ∧ a = b
    · have hc' : (i.val != j.val && (a.val == b.val)) = true := by
        simp [Fin.ext_iff] at hc; simp [hc.1, hc.2]
      rw [if_pos hc', if_pos hc]
      exact i6Div2_sound (h_ivPhi3 _ (nodeOfN_lt6 i.val j.val i.isLt j.isLt (fun h => hc.1 (Fin.ext h))))
    · have hc' : (i.val != j.val && (a.val == b.val)) = false := by
        simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne]
        by_cases hne : i = j
        · left; exact congrArg Fin.val hne
        · right; intro heq; exact hc ⟨hne, Fin.ext heq⟩
      simp only [hc, hc', Bool.false_eq_true, ↓reduceIte]; exact i6Zero_sound
  have h3 : (if i.val == j.val then
        (List.range 9).foldl (fun acc k =>
          if k == i.val then acc
          else i6Add acc (i6Mul (ivAC5 (nodeOfN i.val k)) (i6Mul (ivP k a.val) (ivP k b.val)))) ⟨0, 0⟩
      else i6Mul (ivAC5 (nodeOfN i.val j.val)) (i6Mul (ivP j.val a.val) (ivP i.val b.val))).inR
      (if i = j then
        ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * (ttpPt z k a * ttpPt z k b)
       else ac5Val z (nodeOfN i.val j.val) * (ttpPt z j a * ttpPt z i b)) := by
    by_cases hij : i = j
    · have hij' : (i.val == j.val) = true := by simp [hij]
      rw [if_pos hij', if_pos hij]
      have hfold : ∀ (l : List ℕ) (hl : ∀ k ∈ l, k < 9) (acc : Iv6) (s : ℝ),
          acc.inR s →
          (l.foldl (fun acc k =>
            if k == i.val then acc
            else i6Add acc (i6Mul (ivAC5 (nodeOfN i.val k)) (i6Mul (ivP k a.val) (ivP k b.val)))) acc).inR
            (s + (l.map fun k => if hk : k < 9 then
              (if k = i.val then 0 else ac5Val z (nodeOfN i.val k) * (ttpPt z ⟨k, hk⟩ a * ttpPt z ⟨k, hk⟩ b))
              else 0).sum) := by
        intro l
        induction l with
        | nil => intro _ acc s hs; simpa using hs
        | cons k ks ih =>
          intro hl acc s hs
          have hk9 : k < 9 := hl k List.mem_cons_self
          have hks : ∀ x ∈ ks, x < 9 := fun x hx => hl x (List.mem_cons_of_mem k hx)
          simp only [List.foldl_cons, List.map_cons, List.sum_cons, hk9, ↓reduceDIte]
          by_cases hkj : k = i.val
          · have hkj' : (k == i.val) = true := by simp [hkj]
            simp only [hkj, hkj', ↓reduceIte, zero_add]
            simpa using ih hks acc s hs
          · have hkj' : (k == i.val) = false := by simp [hkj]
            simp only [hkj, hkj', Bool.false_eq_true, ↓reduceIte]
            have hterm : (i6Mul (ivAC5 (nodeOfN i.val k)) (i6Mul (ivP k a.val) (ivP k b.val))).inR
                (ac5Val z (nodeOfN i.val k) * (ttpPt z ⟨k, hk9⟩ a * ttpPt z ⟨k, hk9⟩ b)) :=
              i6Mul_sound (h_ivAC5 _ (nodeOfN_lt6 i.val k i.isLt hk9 (Ne.symm hkj)))
                (i6Mul_sound (h_ivP ⟨k, hk9⟩ a) (h_ivP ⟨k, hk9⟩ b))
            have hnext := ih hks _ (s + ac5Val z (nodeOfN i.val k) * (ttpPt z ⟨k, hk9⟩ a * ttpPt z ⟨k, hk9⟩ b))
              (i6Add_sound hs hterm)
            simpa [add_assoc] using hnext
      have hres := hfold (List.range 9) (fun k hk => List.mem_range.mp hk) ⟨0, 0⟩ 0 i6Zero_sound
      have heq_sum : (0 : ℝ) + ((List.range 9).map fun k => if hk : k < 9 then
          (if k = i.val then 0 else ac5Val z (nodeOfN i.val k) * (ttpPt z ⟨k, hk⟩ a * ttpPt z ⟨k, hk⟩ b))
          else 0).sum =
          ∑ k : Fin 9, if k = i then 0 else ac5Val z (nodeOfN i.val k.val) * (ttpPt z k a * ttpPt z k b) := by
        rw [zero_add, sum_univ_nine]
        simp [List.range_succ, Fin.ext_iff]
        ring
      rw [heq_sum] at hres
      exact hres
    · have hij' : (i.val == j.val) = false := by simp [Fin.ext_iff] at hij; simp [hij]
      simp only [hij, hij', Bool.false_eq_true, ↓reduceIte]
      exact i6Mul_sound (h_ivAC5 _ (nodeOfN_lt6 i.val j.val i.isLt j.isLt (by simp [Fin.ext_iff] at hij; exact hij)))
        (i6Mul_sound (h_ivP j a) (h_ivP i b))
  have h4 : (if i.val == j.val then i6Scale 10 (i6Mul (ivP i.val a.val) (ivP i.val b.val)) else ⟨0, 0⟩).inR
      (if i = j then 10 * (ttpPt z i a * ttpPt z i b) else 0) := by
    by_cases hij : i = j
    · have hij' : (i.val == j.val) = true := by simp [hij]
      simp only [hij, hij', ↓reduceIte]
      simpa using i6Scale_sound 10 (i6Mul_sound (h_ivP j a) (h_ivP j b))
    · have hij' : (i.val == j.val) = false := by simp [Fin.ext_iff] at hij; simp [hij]
      simp only [hij, hij', Bool.false_eq_true, ↓reduceIte]; exact i6Zero_sound
  have h5 : (i6Scale 5 (i6Mul (ivRotVec 0 1 p.val) (ivRotVec 0 1 q.val))).inR
      (5 * (rotVecReal z 0 1 p * rotVecReal z 0 1 q)) := by
    simpa using i6Scale_sound 5 (i6Mul_sound (h_ivRot 0 1 p) (h_ivRot 0 1 q))
  have h6 : (i6Scale 5 (i6Mul (ivRotVec 0 2 p.val) (ivRotVec 0 2 q.val))).inR
      (5 * (rotVecReal z 0 2 p * rotVecReal z 0 2 q)) := by
    simpa using i6Scale_sound 5 (i6Mul_sound (h_ivRot 0 2 p) (h_ivRot 0 2 q))
  have h7 : (i6Scale 5 (i6Mul (ivRotVec 1 2 p.val) (ivRotVec 1 2 q.val))).inR
      (5 * (rotVecReal z 1 2 p * rotVecReal z 1 2 q)) := by
    simpa using i6Scale_sound 5 (i6Mul_sound (h_ivRot 1 2 p) (h_ivRot 1 2 q))
  exact i6Add_sound (i6Add_sound (i6Add_sound h1 h2) (i6Add_sound h3 h4)) (i6Add_sound (i6Add_sound h5 h6) h7)

private lemma cs_27 (v : Fin 27 → ℝ) : (∑ p : Fin 27, |v p|) ^ 2 ≤ 27 * ∑ p : Fin 27, v p ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 27))) (f := fun p => |v p|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
  exact_mod_cast h

/-- **Strict `27 × 27` Hessian Coercivity**: for any `z ∈ [zStarLo, zStarHi]` and ANY `d : Fin 9 → R3`,
`Q_pen z d ≥ (37 / 1000) * ∑ i, ‖d i‖ ^ 2`. -/
theorem hessian_lower_bound {z : ℝ} (hzLo : (zStarLo : ℝ) ≤ z) (hzHi : z ≤ (zStarHi : ℝ))
    (d : Fin 9 → R3) :
    (37 / 1000 : ℝ) * ∑ i : Fin 9, ‖d i‖ ^ 2 ≤ Q_pen z d := by
  rw [Q_pen_eq_quad27, ← sum27_vec27_sq]
  let v : Fin 27 → ℝ := vec27 d
  let Cdot : Fin 27 → Fin 27 → ℝ := fun p q =>
    (∑ k : Fin 27, ((get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ))) / 1000000000000
  have hchol_nn : 0 ≤ ∑ p : Fin 27, ∑ q : Fin 27, Cdot p q * v p * v q := by
    have hrew : ∑ p : Fin 27, ∑ q : Fin 27, Cdot p q * v p * v q =
        (∑ k : Fin 27, (∑ p : Fin 27, (get27 C_27 p.val k.val : ℝ) * v p) ^ 2) / 1000000000000 := by
      dsimp only [Cdot]
      have hterm : ∀ p q : Fin 27,
          (∑ k : Fin 27, (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ)) / 1000000000000 * v p * v q =
          (∑ k : Fin 27, (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) * v p * v q) / 1000000000000 := by
        intro p q
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        congr 1
        simp_rw [Finset.sum_mul]
      simp_rw [hterm, ← Finset.sum_div]
      congr 1
      have hsq : ∀ k : Fin 27, (∑ p : Fin 27, (get27 C_27 p.val k.val : ℝ) * v p) ^ 2 =
          ∑ p : Fin 27, ∑ q : Fin 27, (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) * v p * v q := by
        intro k
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
      simp_rw [hsq]
      calc ∑ p : Fin 27, ∑ q : Fin 27, ∑ k : Fin 27,
              (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) * v p * v q
          = ∑ p : Fin 27, ∑ k : Fin 27, ∑ q : Fin 27,
              (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) * v p * v q :=
            Finset.sum_congr rfl fun p _ => Finset.sum_comm
        _ = ∑ k : Fin 27, ∑ p : Fin 27, ∑ q : Fin 27,
              (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) * v p * v q :=
            Finset.sum_comm
    rw [hrew]
    exact div_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (by norm_num)
  have herr : ∀ p q : Fin 27,
      |H_true z p q - ((if p = q then (1 / 25 : ℝ) else 0) + Cdot p q)| ≤ 6 / 100000 := by
    intro p q
    have hiv := ivHentry_sound hzLo hzHi p q
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp H_iv_ok p.val (List.mem_range.mpr p.isLt))
      q.val (List.mem_range.mpr q.isLt)
    simp only [decide_eq_true_eq] at h1
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp H_chol_ok p.val (List.mem_range.mpr p.isLt))
      q.val (List.mem_range.mpr q.isLt)
    simp only [decide_eq_true_eq] at h2
    have hdot_eq : (((List.range 27).foldl (fun acc k => acc + get27 C_27 p.val k * get27 C_27 q.val k) 0 : ℤ) : ℝ) =
        ∑ k : Fin 27, (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) := by
      have hfold : ∀ (l : List ℕ) (hl : ∀ k ∈ l, k < 27) (acc : ℤ),
          ((l.foldl (fun a k => a + get27 C_27 p.val k * get27 C_27 q.val k) acc : ℤ) : ℝ) =
            (acc : ℝ) + (l.map fun k => (get27 C_27 p.val k : ℝ) * (get27 C_27 q.val k : ℝ)).sum := by
        intro l
        induction l with
        | nil => intro _ acc; simp
        | cons k ks ih =>
          intro hl acc
          simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih (fun x hx => hl x (List.mem_cons_of_mem k hx))]
          push_cast; ring
      rw [hfold (List.range 27) (fun k hk => List.mem_range.mp hk) 0]
      simp only [Int.cast_zero, zero_add]
      symm
      rw [Fin.sum_univ_def]
      have hfin : (List.finRange 27).map (fun k : Fin 27 => (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ)) =
          ((List.finRange 27).map Fin.val).map (fun k : ℕ => (get27 C_27 p.val k : ℝ) * (get27 C_27 q.val k : ℝ)) := by
        rw [List.map_map]; rfl
      have hfr : (List.finRange 27).map Fin.val = List.range 27 := by decide
      rw [hfin, hfr]
    have h1a : ((get27 H_rat p.val q.val : ℝ) - 50) ≤ ((ivHentry p.val q.val).lo : ℝ) := by exact_mod_cast h1.1
    have h1b : ((ivHentry p.val q.val).hi : ℝ) ≤ ((get27 H_rat p.val q.val : ℝ) + 50) := by exact_mod_cast h1.2
    have hdiag_eq : ((if p.val == q.val then (40000 : ℤ) else 0 : ℤ) : ℝ) =
        if p = q then 40000 else 0 := by
      by_cases hpq : p = q
      · subst hpq; simp
      · have hpq' : (p.val == q.val) = false := by simp [Fin.ext_iff] at hpq; simp [hpq]
        simp [hpq, hpq']
    have h2a : (1000000 : ℝ) * ((get27 H_rat p.val q.val : ℝ) - (if p = q then 40000 else 0)) - 10000000 ≤
        ∑ k : Fin 27, (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) := by
      have h2' : ((S6 * (get27 H_rat p.val q.val - if p.val == q.val then 40000 else 0) - 10000000 : ℤ) : ℝ) ≤
          (((List.range 27).foldl (fun acc k => acc + get27 C_27 p.val k * get27 C_27 q.val k) 0 : ℤ) : ℝ) := by
        exact_mod_cast h2.1
      rw [hdot_eq] at h2'
      simp only [S6, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, hdiag_eq] at h2'; linarith
    have h2b : ∑ k : Fin 27, (get27 C_27 p.val k.val : ℝ) * (get27 C_27 q.val k.val : ℝ) ≤
        (1000000 : ℝ) * ((get27 H_rat p.val q.val : ℝ) - (if p = q then 40000 else 0)) + 10000000 := by
      have h2' : (((List.range 27).foldl (fun acc k => acc + get27 C_27 p.val k * get27 C_27 q.val k) 0 : ℤ) : ℝ) ≤
          ((S6 * (get27 H_rat p.val q.val - if p.val == q.val then 40000 else 0) + 10000000 : ℤ) : ℝ) := by
        exact_mod_cast h2.2
      rw [hdot_eq] at h2'
      simp only [S6, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, hdiag_eq] at h2'; linarith
    unfold Iv6.inR at hiv
    dsimp only [Cdot]
    rw [abs_le]
    by_cases hpq : p = q
    · subst hpq; simp only [↓reduceIte] at h2a h2b ⊢; constructor <;> linarith
    · simp only [hpq, ↓reduceIte] at h2a h2b ⊢; constructor <;> linarith
  have hdiag : ∑ p : Fin 27, ∑ q : Fin 27, (if p = q then (1 / 25 : ℝ) else 0) * v p * v q =
      (1 / 25 : ℝ) * ∑ p : Fin 27, v p ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single p]
    · simp [sq]; ring
    · intro q _ hqp; simp [Ne.symm hqp]
    · intro h; exact absurd (Finset.mem_univ p) h
  have hdiff_bound : -(27 * (6 / 100000 : ℝ)) * ∑ p : Fin 27, v p ^ 2 ≤
      ∑ p : Fin 27, ∑ q : Fin 27,
        (H_true z p q - ((if p = q then (1 / 25 : ℝ) else 0) + Cdot p q)) * v p * v q := by
    have habs : |∑ p : Fin 27, ∑ q : Fin 27,
        (H_true z p q - ((if p = q then (1 / 25 : ℝ) else 0) + Cdot p q)) * v p * v q| ≤
        (6 / 100000 : ℝ) * (∑ p : Fin 27, |v p|) ^ 2 := by
      calc |∑ p : Fin 27, ∑ q : Fin 27,
              (H_true z p q - ((if p = q then (1 / 25 : ℝ) else 0) + Cdot p q)) * v p * v q|
          ≤ ∑ p : Fin 27, |∑ q : Fin 27,
              (H_true z p q - ((if p = q then (1 / 25 : ℝ) else 0) + Cdot p q)) * v p * v q| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p : Fin 27, ∑ q : Fin 27,
              |(H_true z p q - ((if p = q then (1 / 25 : ℝ) else 0) + Cdot p q)) * v p * v q| :=
            Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p : Fin 27, ∑ q : Fin 27, (6 / 100000 : ℝ) * |v p| * |v q| := by
            refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
            rw [abs_mul, abs_mul]
            have := herr p q
            have hnn : 0 ≤ |v p| * |v q| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
            nlinarith
        _ = (6 / 100000 : ℝ) * (∑ p : Fin 27, |v p|) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun q _ => by ring
    have hcs := cs_27 v
    have h1 := (abs_le.mp habs).1
    nlinarith
  have hsplit : ∑ p : Fin 27, ∑ q : Fin 27, H_true z p q * v p * v q =
      (∑ p : Fin 27, ∑ q : Fin 27, (if p = q then (1 / 25 : ℝ) else 0) * v p * v q) +
      (∑ p : Fin 27, ∑ q : Fin 27, Cdot p q * v p * v q) +
      (∑ p : Fin 27, ∑ q : Fin 27,
        (H_true z p q - ((if p = q then (1 / 25 : ℝ) else 0) + Cdot p q)) * v p * v q) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hSnn : 0 ≤ ∑ p : Fin 27, v p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  linarith [hsplit, hdiag, hchol_nn, hdiff_bound]

/-! ## Section 7: Strict Local Minimality on the `1/500`-Ball & `O(3)` Matrix Bridge -/

private lemma coulombEnergy9_isometry (g : R3 ≃ₗᵢ[ℝ] R3) (y : Fin 9 → R3) :
    coulombEnergy9 (fun i => g (y i)) = coulombEnergy9 y := by
  unfold coulombEnergy9
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_sub, LinearIsometryEquiv.norm_map]

private lemma c5_le_one {z : ℝ} (hzLo : (zStarLo : ℝ) ≤ z) (hzHi : z ≤ (zStarHi : ℝ))
    (k : ℕ) (hk : k < 6) : (3 / 2 : ℝ) * phi (nuOfN k z - 1 / 200) ^ 5 ≤ 1 := by
  have hzLo0 : (0 : ℝ) < (zStarLo : ℝ) := by norm_num [zStarLo]
  have hz0 : 0 < z := lt_of_lt_of_le hzLo0 hzLo
  obtain ⟨_, _, _, hrl, hrh, hrlp, _, _, _, _, _, _, _, _, _⟩ := env_sq_ok
  obtain ⟨h0l, _, h0p, h1l, _, h1p, h2l, _, h2p, h3l, _, h3p, h4l, _, h4p, h5l, _, h5p⟩ := sr_sq_ok
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := c5_le_one_ok
  have hrho_lo : (rhoStarLo : ℝ) ≤ Real.sqrt (1 - z ^ 2) :=
    sqrt_lo_le hrlp (le_trans (by exact_mod_cast hrl : (rhoStarLo : ℝ) ^ 2 ≤ 1 - (zStarHi : ℝ) ^ 2) (by nlinarith [hz0, hzHi]))
  have hrho_hi : Real.sqrt (1 - z ^ 2) ≤ (rhoStarHi : ℝ) :=
    sqrt_le_hi (by norm_num [rhoStarHi]) (le_trans (by nlinarith [hzLo0, hz0, hzLo]) (by exact_mod_cast hrh : 1 - (zStarLo : ℝ) ^ 2 ≤ (rhoStarHi : ℝ) ^ 2))
  have hstep : ∀ {srL : ℚ} (d2 : ℝ), (0 : ℚ) < srL → (srL : ℝ) ≤ Real.sqrt d2 →
      2 - 2 * (nuOfN k z - 1 / 200) = d2 → (3 : ℚ) / (2 * srL ^ 5) ≤ 1 →
      (3 / 2 : ℝ) * phi (nuOfN k z - 1 / 200) ^ 5 ≤ 1 := by
    intro srL d2 hpL hL hd2 hq
    have hLpos : (0 : ℝ) < (srL : ℝ) := by exact_mod_cast hpL
    have hphi5 : phi (nuOfN k z - 1 / 200) ^ 5 = 1 / Real.sqrt d2 ^ 5 := by
      unfold phi; rw [hd2, inv_eq_one_div, _root_.one_div_pow]
    have hinv : 1 / Real.sqrt d2 ^ 5 ≤ 1 / (srL : ℝ) ^ 5 :=
      one_div_le_one_div_of_le (pow_pos hLpos 5) (pow_le_pow_left₀ hLpos.le hL 5)
    have hqR : (3 : ℝ) / (2 * (srL : ℝ) ^ 5) ≤ 1 := by exact_mod_cast hq
    rw [hphi5]
    have ha : (3 : ℝ) / (2 * (srL : ℝ) ^ 5) = 3 / 2 * (1 / (srL : ℝ) ^ 5) := by ring
    linarith
  interval_cases k
  · have hlR : ((srLo_0 ^ 2 : ℚ) : ℝ) ≤ ((3 + zStarLo ^ 2 + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h0l
    push_cast at hlR
    exact hstep (3 + z ^ 2 + 1 / 100) h0p (sqrt_lo_le h0p (by nlinarith [hzLo0, hz0, hzLo]))
      (by simp only [nuOfN, nu1]; ring) c0
  · have hlR : ((srLo_1 ^ 2 : ℚ) : ℝ) ≤ ((2 + 2 * rhoStarLo + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h1l
    push_cast at hlR
    exact hstep (2 + 2 * Real.sqrt (1 - z ^ 2) + 1 / 100) h1p (sqrt_lo_le h1p (by linarith))
      (by simp only [nuOfN, nu2, rhoR]; ring) c1
  · have hlR : ((srLo_2 ^ 2 : ℚ) : ℝ) ≤ ((3 + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h2l
    push_cast at hlR
    exact hstep (3 + 1 / 100) h2p (sqrt_lo_le h2p hlR) (by simp only [nuOfN, nu3]; ring) c2
  · have hlR : ((srLo_3 ^ 2 : ℚ) : ℝ) ≤ ((4 * zStarLo ^ 2 + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h3l
    push_cast at hlR
    exact hstep (4 * z ^ 2 + 1 / 100) h3p (sqrt_lo_le h3p (by nlinarith [hzLo0, hz0, hzLo]))
      (by simp only [nuOfN, nu4]; ring) c3
  · have hlR : ((srLo_4 ^ 2 : ℚ) : ℝ) ≤ ((3 * (1 - zStarHi ^ 2) + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h4l
    push_cast at hlR
    exact hstep (3 * (1 - z ^ 2) + 1 / 100) h4p (sqrt_lo_le h4p (by nlinarith [hz0, hzHi]))
      (by simp only [nuOfN, nu5]; ring) c4
  · have hlR : ((srLo_5 ^ 2 : ℚ) : ℝ) ≤ ((2 - rhoStarHi + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast h5l
    push_cast at hlR
    exact hstep (2 - Real.sqrt (1 - z ^ 2) + 1 / 100) h5p (sqrt_lo_le h5p (by linarith))
      (by simp only [nuOfN, nu6, rhoR]; ring) c5

/-- **Main Stage B L6 Strict Local Minimality Theorem**:
At the exact critical parameter `zStar ∈ [zStarLo, zStarHi]`, every injective unit-sphere
configuration `y` within `∑ i, ‖y i - ttpPt zStar i‖² ≤ (1/500)²` has
`coulombEnergy9 (ttpPt zStar) ≤ coulombEnergy9 y`, with equality iff `y` is an `O(3)`-image of `ttpPt zStar`. -/
theorem local_min_ball {zStar : ℝ} (hzLo : (zStarLo : ℝ) ≤ zStar) (hzHi : zStar ≤ (zStarHi : ℝ))
    (hcrit : critGap zStar = 0)
    {y : Fin 9 → R3} (hyu : ∀ i, ‖y i‖ = 1) (hyinj : Function.Injective y)
    (hclose : ∑ i : Fin 9, ‖y i - ttpPt zStar i‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2) :
    coulombEnergy9 (ttpPt zStar) ≤ coulombEnergy9 y ∧
      (coulombEnergy9 y = coulombEnergy9 (ttpPt zStar) →
        ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, y i = g (ttpPt zStar i)) := by
  have hz0 : 0 < zStar := lt_of_lt_of_le (by norm_num [zStarLo]) hzLo
  have hz1 : zStar < 1 := lt_of_le_of_lt hzHi (by norm_num [zStarHi])
  have hzsq : zStar ^ 2 ≤ 1 := by nlinarith
  let P : Fin 9 → R3 := ttpPt zStar
  have hPu : ∀ i, ‖P i‖ = 1 := ttpPt_norm zStar hzsq
  -- Apply Procrustes gauge lemma!
  obtain ⟨g, hgauge, hclose_g⟩ := exists_gauge P y
  let y' : Fin 9 → R3 := fun i => g (y i)
  let d : Fin 9 → R3 := fun i => y' i - P i
  have hy'u : ∀ i, ‖y' i‖ = 1 := fun i => by dsimp only [y']; rw [LinearIsometryEquiv.norm_map]; exact hyu i
  have hEy' : coulombEnergy9 y' = coulombEnergy9 y := coulombEnergy9_isometry g y
  have hS_le : ∑ i : Fin 9, ‖d i‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := hclose_g.trans hclose
  have hd_le : ∀ i : Fin 9, ‖d i‖ ≤ 1 / 500 := by
    intro i
    have h1 : ‖d i‖ ^ 2 ≤ ∑ j : Fin 9, ‖d j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin 9 => ‖d j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact le_of_sq_le_sq (h1.trans hS_le) (by norm_num)
  -- Exact unit-sphere radial identity: ⟪P i, d i⟫ = -‖d i‖² / 2
  have hrad : ∀ i : Fin 9, ⟪P i, d i⟫ = -(‖d i‖ ^ 2 / 2) := by
    intro i
    have h1 : ‖P i + d i‖ ^ 2 = 1 := by
      have : P i + d i = y' i := by dsimp only [d]; abel
      rw [this, hy'u i]; norm_num
    rw [norm_add_sq_real, hPu i] at h1
    linarith
  -- Gauge antisymmetry vanishes identically on `d`
  have hrot0 : ∀ a b : Fin 3, ∑ i : Fin 9, (P i a * d i b - P i b * d i a) = 0 := by
    intro a b
    have hg := hgauge a b
    have h1 : ∑ i : Fin 9, (P i a * d i b - P i b * d i a) =
        (∑ i : Fin 9, P i a * y' i b) - (∑ i : Fin 9, P i b * y' i a) := by
      simp_rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [d, y']; simp only [PiLp.sub_apply]; ring
    rw [h1]; linarith
  -- Exact pairwise inner product expansion: ⟪y' i, y' j⟫ = t0 + L + q
  have hdot_exp : ∀ i j : Fin 9,
      ⟪y' i, y' j⟫ = ⟪P i, P j⟫ + ((⟪P i, d j⟫ + ⟪d i, P j⟫) + ⟪d i, d j⟫) := by
    intro i j
    have hyi : y' i = P i + d i := by dsimp only [d]; abel
    have hyj : y' j = P j + d j := by dsimp only [d]; abel
    rw [hyi, hyj, inner_add_left, inner_add_right, inner_add_right]; ring
  -- Criticality linear term identity: ∑_{i<j} phi(t0)^3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) = -(1/2) ∑_i lam_i ‖d i‖²
  have hlin_id :
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
        -(1 / 2 : ℝ) * ∑ i : Fin 9, lamOf zStar i * ‖d i‖ ^ 2 := by
    have hsym_f : ∀ i j : Fin 9,
        phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
        phi ⟪P j, P i⟫ ^ 3 * (⟪P j, d i⟫ + ⟪d j, P i⟫) := fun i j => by
      rw [real_inner_comm (P i) (P j), real_inner_comm (P i) (d j), real_inner_comm (d i) (P j)]; ring
    have hdouble : 2 * (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫)) =
        ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) := by
      have hrow : ∀ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
          (∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫)) +
          (∑ j ∈ Finset.Iio i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫)) := by
        intro i
        rw [← Finset.sum_union]
        · congr 1; ext j; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
            Finset.mem_Ioi, Finset.mem_Iio]
          exact ⟨fun h => lt_or_gt_of_ne h.symm, fun h => h.elim ne_of_gt ne_of_lt⟩
        · rw [Finset.disjoint_left]; intro j h1 h2; simp at h1 h2; omega
      simp_rw [hrow, Finset.sum_add_distrib]
      have hflip : ∑ i : Fin 9, ∑ j ∈ Finset.Iio i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
          ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) := by
        have e1 : ∀ i : Fin 9, ∑ j ∈ Finset.Iio i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
            ∑ j : Fin 9, if j < i then phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) else 0 := fun i => by
          rw [← Finset.sum_filter]; congr 1; ext j; simp
        have e2 : ∀ i : Fin 9, ∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
            ∑ j : Fin 9, if i < j then phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) else 0 := fun i => by
          rw [← Finset.sum_filter]; congr 1; ext j; simp
        simp_rw [e1, e2]; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
          by_cases h : j < i <;> simp [h, hsym_f i j]
      linarith
    have hsplit : ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
        2 * ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * ⟪d i, P j⟫ := by
      have h1 : ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫) =
          (∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * ⟪P i, d j⟫) +
          (∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * ⟪d i, P j⟫) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      have hswap : ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * ⟪P i, d j⟫ =
          ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * ⟪d i, P j⟫ := by
        have e1 : ∀ (F : Fin 9 → Fin 9 → ℝ), ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, F i j =
            ∑ i : Fin 9, ∑ j : Fin 9, if i ≠ j then F i j else 0 := fun F =>
          Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_filter]; congr 1; ext j; simp [ne_comm]
        rw [e1, e1, Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
          by_cases h : i ≠ j
          · simp [h, h.symm, real_inner_comm (P i) (P j), real_inner_comm (P i) (d j)]
          · simp [h, show ¬ (j ≠ i) by omega]
      linarith
    have hcrit_sum : ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * ⟪d i, P j⟫ =
        -(1 / 2 : ℝ) * ∑ i : Fin 9, lamOf zStar i * ‖d i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hinner : ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 * ⟪d i, P j⟫ =
          ⟪d i, ∑ j ∈ Finset.univ.erase i, phi ⟪P i, P j⟫ ^ 3 • P j⟫ := by
        rw [inner_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [real_inner_smul_right]
      rw [hinner, ttp_critical hz0 hz1 hcrit i, real_inner_smul_right, real_inner_comm, hrad i]
      ring
    linarith
  -- Pairwise Bregman + Young lower bound
  have hpair_breg : ∀ i : Fin 9, ∀ j ∈ Finset.Ioi i,
      ac5Val zStar (nodeOfN i.val j.val) * (⟪P i, d j⟫ + ⟪d i, P j⟫) ^ 2
        - 100 * ((1 / 500 : ℝ) ^ 2 / 2 * (‖d i‖ ^ 2 + ‖d j‖ ^ 2)) ≤
      phi ⟪y' i, y' j⟫ - phi ⟪P i, P j⟫ - phi ⟪P i, P j⟫ ^ 3 * ((⟪P i, d j⟫ + ⟪d i, P j⟫) + ⟪d i, d j⟫) := by
    intro i j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    have ht0 : ⟪P i, P j⟫ = nuOfN (nodeOfN i.val j.val) zStar := ttpPt_inner zStar hzsq i j hij
    set L := ⟪P i, d j⟫ + ⟪d i, P j⟫
    set q := ⟪d i, d j⟫
    have hL_abs : |L| ≤ ‖d i‖ + ‖d j‖ := by
      have h1 : |⟪P i, d j⟫| ≤ ‖P i‖ * ‖d j‖ := abs_real_inner_le_norm _ _
      have h2 : |⟪d i, P j⟫| ≤ ‖d i‖ * ‖P j‖ := abs_real_inner_le_norm _ _
      rw [hPu i, one_mul] at h1; rw [hPu j, mul_one] at h2
      exact (abs_add_le _ _).trans (by linarith)
    have hq_abs : |q| ≤ ‖d i‖ * ‖d j‖ := abs_real_inner_le_norm _ _
    have htau_abs : |L + q| ≤ 1 / 200 := by
      have h1 : ‖d i‖ ≤ 1 / 500 := hd_le i
      have h2 : ‖d j‖ ≤ 1 / 500 := hd_le j
      have hprod : ‖d i‖ * ‖d j‖ ≤ (1 / 500 : ℝ) * (1 / 500) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      exact (abs_add_le L q).trans (by linarith)
    have ht0_lt : ⟪P i, P j⟫ + 1 / 200 < 1 := by
      rw [ht0]
      have hk := nodeOfN_lt6 i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
      have hzBox : (TableB5Data.zLo : ℝ) ≤ zStar ∧ zStar ≤ (TableB5Data.zHi : ℝ) :=
        ⟨le_trans (by exact_mod_cast zStar_in_zBox.1) hzLo, le_trans hzHi (by exact_mod_cast zStar_in_zBox.2.2)⟩
      have hnu := (nu_container_idx zStar hzBox.1 hzBox.2 _ hk).2
      have hhi_lt : (nuHiIdx (nodeOfN i.val j.val) : ℝ) < 1 / 2 := by
        have hq : nuHiIdx (nodeOfN i.val j.val) < (1 / 2 : ℚ) := by
          generalize nodeOfN i.val j.val = k at hk ⊢
          interval_cases k <;> simp only [nuHiIdx] <;>
            norm_num [nu1Hi, nu2Hi, nu3Hi, nu4Hi, nu5Hi, nu6Hi]
        have hqR : ((nuHiIdx (nodeOfN i.val j.val) : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hq
        simpa using hqR
      linarith
    have hbreg := breg_ge_quad (t0 := ⟪P i, P j⟫) (τ := L + q) (τ_max := 1 / 200) (by norm_num) htau_abs ht0_lt
    rw [← hdot_exp i j] at hbreg
    -- Young's inequality: (L + q)^2 ≥ (99/100) * L^2 - 100 * q^2!
    have hyoung : (99 / 100 : ℝ) * L ^ 2 - 100 * q ^ 2 ≤ (L + q) ^ 2 := by
      have hsq : 0 ≤ ((1 / 10 : ℝ) * L + 10 * q) ^ 2 + q ^ 2 := by positivity
      linarith
    have hc_nn : 0 ≤ (3 / 2 : ℝ) * phi (⟪P i, P j⟫ - 1 / 200) ^ 5 := by
      unfold phi; positivity
    have hc_le1 : (3 / 2 : ℝ) * phi (⟪P i, P j⟫ - 1 / 200) ^ 5 ≤ 1 := by
      rw [ht0]
      exact c5_le_one hzLo hzHi _ (nodeOfN_lt6 i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)))
    have hq2 : q ^ 2 ≤ (1 / 500 : ℝ) ^ 2 / 2 * (‖d i‖ ^ 2 + ‖d j‖ ^ 2) := by
      have h1 : q ^ 2 ≤ (‖d i‖ * ‖d j‖) ^ 2 := by
        rw [← sq_abs q]; exact pow_le_pow_left₀ (abs_nonneg _) hq_abs 2
      have h2 : ‖d i‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hd_le i) 2
      have h3 : ‖d j‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hd_le j) 2
      nlinarith [sq_nonneg ‖d i‖, sq_nonneg ‖d j‖]
    have hstep1 := mul_le_mul_of_nonneg_left hyoung hc_nn
    have hstep2 : (3 / 2 : ℝ) * phi (⟪P i, P j⟫ - 1 / 200) ^ 5 * (100 * q ^ 2) ≤
        100 * ((1 / 500 : ℝ) ^ 2 / 2 * (‖d i‖ ^ 2 + ‖d j‖ ^ 2)) := by
      nlinarith [sq_nonneg q]
    have hac : ac5Val zStar (nodeOfN i.val j.val) * L ^ 2 =
        (3 / 2 : ℝ) * phi (⟪P i, P j⟫ - 1 / 200) ^ 5 * ((99 / 100 : ℝ) * L ^ 2) := by
      unfold ac5Val; rw [ht0]; ring
    linarith
  -- Sum the Bregman lower bound over all 36 pairs and assemble with `Q_pen`!
  have hsum_d2 : ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (‖d i‖ ^ 2 + ‖d j‖ ^ 2) = 8 * ∑ i : Fin 9, ‖d i‖ ^ 2 := by
    have h1 : ∀ f : Fin 9 → ℝ, ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (f i + f j) = 8 * ∑ i : Fin 9, f i := by
      intro f
      have hI : ∀ i : Fin 9, ∑ j ∈ Finset.Ioi i, (f i + f j) =
          ∑ j : Fin 9, if i < j then f i + f j else 0 := fun i => by
        rw [← Finset.sum_filter]; congr 1; ext j; simp
      simp_rw [hI]
      simp only [sum_univ_nine]
      simp; ring
    exact h1 (fun i => ‖d i‖ ^ 2)
  have hnorm_pen : 10 * ∑ i : Fin 9, ⟪P i, d i⟫ ^ 2 ≤ (10 / 4 : ℝ) * (1 / 500 : ℝ) ^ 2 * ∑ i : Fin 9, ‖d i‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hrad i]
    have h1 : ‖d i‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hd_le i) 2
    nlinarith [sq_nonneg ‖d i‖]
  have hE_diff : coulombEnergy9 y' - coulombEnergy9 P =
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (phi ⟪y' i, y' j⟫ - phi ⟪P i, P j⟫) := by
    unfold coulombEnergy9
    simp_rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [inv_norm_eq_phi (hy'u i) (hy'u j), inv_norm_eq_phi (hPu i) (hPu j)]
  have hphi_eq_val : ∀ i : Fin 9, ∀ j ∈ Finset.Ioi i,
      phi ⟪P i, P j⟫ ^ 3 = phiVal zStar (nodeOfN i.val j.val) ^ 3 := by
    intro i j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    rw [ttpPt_inner zStar hzsq i j hij,
      phi_nuOfN_eq_phiVal zStar hz0 hz1 _ (nodeOfN_lt6 i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)))]
  have hsum_breg := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (hj : j ∈ Finset.Ioi i) => hpair_breg i j hj
  have hE_ge_Q : Q_pen zStar d - (10 * ∑ i : Fin 9, ⟪P i, d i⟫ ^ 2)
      - 100 * ((1 / 500 : ℝ) ^ 2 / 2 * (8 * ∑ i : Fin 9, ‖d i‖ ^ 2)) ≤
      coulombEnergy9 y' - coulombEnergy9 P := by
    rw [hE_diff]
    have hsplit : ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (phi ⟪y' i, y' j⟫ - phi ⟪P i, P j⟫) =
        (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * (⟪P i, d j⟫ + ⟪d i, P j⟫))
        + (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * ⟪d i, d j⟫)
        + (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
            (phi ⟪y' i, y' j⟫ - phi ⟪P i, P j⟫ - phi ⟪P i, P j⟫ ^ 3 * ((⟪P i, d j⟫ + ⟪d i, P j⟫) + ⟪d i, d j⟫))) := by
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hq_rew : ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phi ⟪P i, P j⟫ ^ 3 * ⟪d i, d j⟫ =
        ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, phiVal zStar (nodeOfN i.val j.val) ^ 3 * ⟪d i, d j⟫ :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => by rw [hphi_eq_val i j hj]
    have hsub_sum : ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
        (ac5Val zStar (nodeOfN i.val j.val) * (⟪P i, d j⟫ + ⟪d i, P j⟫) ^ 2
          - 100 * ((1 / 500 : ℝ) ^ 2 / 2 * (‖d i‖ ^ 2 + ‖d j‖ ^ 2))) =
        (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ac5Val zStar (nodeOfN i.val j.val) * (⟪P i, d j⟫ + ⟪d i, P j⟫) ^ 2)
        - 100 * ((1 / 500 : ℝ) ^ 2 / 2 * (8 * ∑ i : Fin 9, ‖d i‖ ^ 2)) := by
      simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_d2]
    unfold Q_pen
    rw [hrot0 0 1, hrot0 0 2, hrot0 1 2]
    rw [hsplit, hlin_id, hq_rew]
    rw [hsub_sum] at hsum_breg
    linarith
  have hH := hessian_lower_bound hzLo hzHi d
  have hSnn : 0 ≤ ∑ i : Fin 9, ‖d i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcoerc : (1 / 30 : ℝ) * ∑ i : Fin 9, ‖d i‖ ^ 2 ≤ coulombEnergy9 y - coulombEnergy9 P := by
    rw [← hEy']
    linarith [hE_ge_Q, hH, hnorm_pen, hSnn]
  refine ⟨by linarith, fun heq => ⟨g.symm, fun i => ?_⟩⟩
  have hS0 : ∑ j : Fin 9, ‖d j‖ ^ 2 = 0 := by linarith
  have hi0 : ‖d i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hS0 i (Finset.mem_univ i)
  have hdi : d i = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hi0)
  have hgy : g (y i) = P i := sub_eq_zero.mp hdi
  dsimp only [P] at hgy
  rw [← hgy]; simp

/-- Bridge an orthogonal `3×3` matrix `Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ` to a linear isometry
`g : R3 ≃ₗᵢ[ℝ] R3` matching right multiplication `(rowPerm (toMat x) σ * Q)`. -/
theorem iso_of_orthogonal (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ (x : Fin 9 → R3) (σ : Equiv.Perm (Fin 9)) (z : ℝ),
      ∑ i : Fin 9, ‖g (x (σ i)) - ttpPt z i‖ ^ 2 = frob (ttpX z - rowPerm (toMat x) σ * Q) ^ 2 := by
  have hQQ : Q * Qᵀ = 1 := by simpa [Matrix.star_eq_conjTranspose] using hQ.2
  have hQtQ : Qᵀ * Q = 1 := by simpa [Matrix.star_eq_conjTranspose] using hQ.1
  let lm : R3 →ₗ[ℝ] R3 :=
    { toFun := fun v => WithLp.toLp 2 (Qᵀ *ᵥ v.ofLp)
      map_add' := fun u v => by ext a; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
      map_smul' := fun c v => by ext a; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring }
  have hnorm : ∀ v : R3, ‖lm v‖ = ‖v‖ := by
    intro v
    have hsq : ‖lm v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sq_R3_expand, norm_sq_R3_expand]
      have h1 : (lm v 0) ^ 2 + (lm v 1) ^ 2 + (lm v 2) ^ 2 = (Qᵀ *ᵥ v.ofLp) ⬝ᵥ (Qᵀ *ᵥ v.ofLp) := by
        simp [lm, dotProduct, Fin.sum_univ_three, sq]
      have h2 : (Qᵀ *ᵥ v.ofLp) ⬝ᵥ (Qᵀ *ᵥ v.ofLp) = ((Q * Qᵀ) *ᵥ v.ofLp) ⬝ᵥ v.ofLp := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
      rw [h1, h2, hQQ, Matrix.one_mulVec]
      simp [dotProduct, Fin.sum_univ_three, sq]
    nlinarith [norm_nonneg (lm v), norm_nonneg v]
  let g : R3 ≃ₗᵢ[ℝ] R3 :=
    LinearIsometry.toLinearIsometryEquiv { toLinearMap := lm, norm_map' := hnorm } rfl
  refine ⟨g, fun x σ z => ?_⟩
  unfold frob
  rw [Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sq_R3_expand, Fin.sum_univ_three]
  have hent : ∀ a : Fin 3, g (x (σ i)) a = (rowPerm (toMat x) σ * Q) i a := fun a => by
    simp [g, lm, Matrix.mulVec, Matrix.mul_apply, rowPerm, toMat, dotProduct, Fin.sum_univ_three]
    ring
  simp only [Matrix.sub_apply, ttpPt, PiLp.sub_apply, WithLp.ofLp_toLp, ← hent]
  ring

end ThomsonN9.StageB.LocalMinL6
