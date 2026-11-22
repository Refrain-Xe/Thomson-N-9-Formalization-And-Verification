import Mathlib

/-!
# Thomson problem for N = 9: the fixed challenge statements

Minimise the Coulomb energy `E(x) = ∑_{i<j} 1 / ‖x i - x j‖` over configurations of `N` pairwise
distinct points on the unit sphere `S² ⊂ ℝ³`.

For `N = 9` the (numerically known) minimiser is the D3h tricapped trigonal prism, which has one
free parameter `z` (the height of the two triangular faces); numerically `z ≈ 0.70365`,
`E ≈ 25.759986531` (reproduced by `numerics/optimize.py` and `numerics/family.py`).

**Provenance.** The definitions `R3`, `SphereConfig`, `coulombEnergy`, `cyl`, `triCapPrism` and the
auxiliary lemmas below through `triCapPrism_mem` are taken verbatim (up to the namespace) from
`references/thomson-n7-lean/formal/lean/ComparatorChallenges/ThomsonN7.lean`, where they were fully
proved (no `sorry`) as part of the N = 7 package; that file is also where the numerical constants
above come from. The four challenge statements at the end are new for this repository and are all
left as `sorry`: they are the fixed target of the project. `scripts/check.sh` builds this file and
counts exactly four `declaration uses sorry` warnings here.

This file is the trusted statement file: once `ThomsonN9/Solution.lean` proves the four theorems,
`scripts/compare_statements.py` (and, later, the Lean Comparator) checks that the solution's
statements match these byte for byte in fully elaborated form.
-/

open Real

namespace ThomsonN9

/-- Euclidean 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- `n` pairwise distinct points on the unit sphere of `ℝ³`.
Injectivity is essential: with `1 / 0 = 0` in Lean, coincident points would otherwise be free. -/
def SphereConfig (n : ℕ) : Set (Fin n → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}

/-- Coulomb (Riesz `s = 1`) energy `∑_{i<j} 1 / ‖x i - x j‖`. -/
noncomputable def coulombEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹

/-- The point with cylindrical coordinates `(ρ, θ, h)`. -/
noncomputable def cyl (ρ θ h : ℝ) : R3 := !₂[ρ * cos θ, ρ * sin θ, h]

/-- The D3h tricapped trigonal prism with prism height parameter `z` (for `z ∈ (0,1)`):
indices `0..2` are the top triangle (height `z`, angles `2πk/3`), indices `3..5` the bottom triangle
(height `-z`, same angles), and indices `6..8` the three equatorial caps at angles `π/3 + 2πk/3`. -/
noncomputable def triCapPrism (z : ℝ) : Fin 9 → R3 := fun i =>
  if (i : ℕ) < 3 then cyl (√(1 - z ^ 2)) (2 * π * (i : ℕ) / 3) z
  else if (i : ℕ) < 6 then cyl (√(1 - z ^ 2)) (2 * π * ((i : ℕ) - 3) / 3) (-z)
  else cyl 1 (π / 3 + 2 * π * ((i : ℕ) - 6) / 3) 0

/-! ## Auxiliary facts (already proved; they show the definitions are well-posed) -/

lemma norm_sq_cyl_sub (ρ θ h ρ' θ' h' : ℝ) :
    ‖cyl ρ θ h - cyl ρ' θ' h'‖ ^ 2 = ρ ^ 2 + ρ' ^ 2 - 2 * ρ * ρ' * cos (θ - θ') + (h - h') ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, cos_sub]
  nlinarith [sin_sq_add_cos_sq θ, sin_sq_add_cos_sq θ']

lemma norm_sq_cyl (ρ θ h : ℝ) : ‖cyl ρ θ h‖ ^ 2 = ρ ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, mul_pow]
  nlinarith [sin_sq_add_cos_sq θ]

lemma int_eq_zero_of_cos_eq_one (m : ℕ) (hm : 0 < m) (d : ℤ) (hd : |d| < m)
    (h : cos (2 * π * d / m) = 1) : d = 0 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (n : ℝ) * m = d := by
    field_simp at hn
    nlinarith [Real.pi_pos]
  have h2 : n * (m : ℤ) = d := by exact_mod_cast h1
  have hm2 : (0 : ℤ) < m := by exact_mod_cast hm
  rw [abs_lt] at hd
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · nlinarith
  · subst hn0; simpa using h2.symm
  · nlinarith

lemma cos_sub_eq_one_of_cyl_eq {ρ θ θ' h : ℝ} (hρ : 0 < ρ)
    (H : cyl ρ θ h = cyl ρ θ' h) : cos (θ - θ') = 1 := by
  have := norm_sq_cyl_sub ρ θ h ρ θ' h
  rw [H, sub_self, norm_zero] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  nlinarith

lemma tri_idx_inj {i j : ℕ} (hd : |(i : ℤ) - j| < 3)
    (H : cos (2 * π * ((i : ℝ) - j) / 3) = 1) : i = j := by
  have := int_eq_zero_of_cos_eq_one 3 (by norm_num) ((i : ℤ) - j) (by exact_mod_cast hd)
    (by convert H using 2; push_cast; ring)
  omega

lemma tri_top {z : ℝ} {i : Fin 9} (hi : (i : ℕ) < 3) :
    triCapPrism z i = cyl (√(1 - z ^ 2)) (2 * π * (i : ℕ) / 3) z := by
  simp [triCapPrism, hi]

lemma tri_bot {z : ℝ} {i : Fin 9} (hi : 3 ≤ (i : ℕ)) (hi' : (i : ℕ) < 6) :
    triCapPrism z i = cyl (√(1 - z ^ 2)) (2 * π * ((i : ℕ) - 3) / 3) (-z) := by
  have h3 : ¬ (i : ℕ) < 3 := by omega
  simp [triCapPrism, h3, hi']

lemma tri_cap {z : ℝ} {i : Fin 9} (hi : 6 ≤ (i : ℕ)) :
    triCapPrism z i = cyl 1 (π / 3 + 2 * π * ((i : ℕ) - 6) / 3) 0 := by
  have h3 : ¬ (i : ℕ) < 3 := by omega
  have h6 : ¬ (i : ℕ) < 6 := by omega
  simp [triCapPrism, h3, h6]

lemma tri_cases (i : Fin 9) : (i : ℕ) < 3 ∨ (3 ≤ (i : ℕ) ∧ (i : ℕ) < 6) ∨ 6 ≤ (i : ℕ) := by
  omega

theorem triCapPrism_injective {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    Function.Injective (triCapPrism z) := by
  obtain ⟨hz0, hz1⟩ := hz
  have hr : 0 < √(1 - z ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  intro i j hij
  have h2 := congrArg (fun v : R3 => v 2) hij
  rcases tri_cases i with hi | ⟨hi, hi'⟩ | hi <;> rcases tri_cases j with hj | ⟨hj, hj'⟩ | hj
  · rw [tri_top hi, tri_top hj] at hij
    refine Fin.ext (tri_idx_inj (by rw [abs_lt]; constructor <;> omega) ?_)
    have := cos_sub_eq_one_of_cyl_eq hr hij
    convert this using 2; ring
  · simp [tri_top hi, tri_bot hj hj', cyl] at h2; linarith
  · simp [tri_top hi, tri_cap hj, cyl] at h2; linarith
  · simp [tri_top hj, tri_bot hi hi', cyl] at h2; linarith
  · rw [tri_bot hi hi', tri_bot hj hj'] at hij
    refine Fin.ext (tri_idx_inj (by rw [abs_lt]; constructor <;> omega) ?_)
    have := cos_sub_eq_one_of_cyl_eq hr hij
    convert this using 2; ring
  · simp [tri_bot hi hi', tri_cap hj, cyl] at h2; linarith
  · simp [tri_top hj, tri_cap hi, cyl] at h2; linarith
  · simp [tri_bot hj hj', tri_cap hi, cyl] at h2; linarith
  · rw [tri_cap hi, tri_cap hj] at hij
    refine Fin.ext (tri_idx_inj (by rw [abs_lt]; constructor <;> omega) ?_)
    have := cos_sub_eq_one_of_cyl_eq one_pos hij
    convert this using 2; ring

/-- The tricapped prism is an admissible configuration for every `z ∈ (0,1)`. -/
theorem triCapPrism_mem : ∀ z ∈ Set.Ioo (0 : ℝ) 1, triCapPrism z ∈ SphereConfig 9 := by
  intro z hz
  refine ⟨fun i => ?_, triCapPrism_injective hz⟩
  obtain ⟨hz0, hz1⟩ := hz
  have hr : √(1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by nlinarith)
  have : ‖triCapPrism z i‖ ^ 2 = 1 := by
    rcases tri_cases i with hi | ⟨hi, hi'⟩ | hi
    · rw [tri_top hi, norm_sq_cyl, hr]; ring
    · rw [tri_bot hi hi', norm_sq_cyl, hr]; ring
    · rw [tri_cap hi, norm_sq_cyl]; norm_num
  nlinarith [norm_nonneg (triCapPrism z i)]


/-! ## Challenge statements (to be proved) -/

/-- **Milestone M0 (weak lower bound, N = 9).** Every configuration of 9 distinct points on the
unit sphere has Coulomb energy at least `36 / 2 = 18`: there are `(9 choose 2) = 36` pairs and
each pair is at distance at most `2`. This is the trivial baseline that any real lower bound must
beat. -/
theorem thomson_nine_M0 :
    ∀ x ∈ SphereConfig 9, (36 / 2 : ℝ) ≤ coulombEnergy x := by
  sorry

/-- **Milestone M1 (first nontrivial lower bound, N = 9).** Every configuration of 9 distinct
points on the unit sphere has Coulomb energy at least `189 / 8 = 23.625`. This is the stage-one
target of `notes/strategy.md` (a two-point / averaging style bound, before the three-point
semidefinite machinery); it is still `23.625 < 25.759986531…` below the conjectured optimum. -/
theorem thomson_nine_M1 :
    ∀ x ∈ SphereConfig 9, (189 / 8 : ℝ) ≤ coulombEnergy x := by
  sorry

/-- **Main target (Thomson, N = 9).** Some D3h tricapped trigonal prism (numerically
`z ≈ 0.70365`, energy `≈ 25.759986531`) is a global minimiser among 9-point configurations. -/
theorem thomson_nine :
    ∃ z ∈ Set.Ioo (0 : ℝ) 1,
      ∀ x ∈ SphereConfig 9, coulombEnergy (triCapPrism z) ≤ coulombEnergy x := by
  sorry

/-- **Uniqueness (N = 9).** Any global minimiser is a tricapped trigonal prism up to an orthogonal
transformation of `ℝ³` and a relabelling of the points. -/
theorem thomson_nine_unique :
    ∀ x ∈ SphereConfig 9, (∀ y ∈ SphereConfig 9, coulombEnergy x ≤ coulombEnergy y) →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 9)) (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) 1),
        ∀ i, x i = g (triCapPrism z (σ i)) := by
  sorry

end ThomsonN9
