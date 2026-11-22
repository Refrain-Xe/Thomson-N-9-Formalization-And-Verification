import Mathlib
import ThomsonN9.M1Data
import ThomsonN9.StageB.SlabCert
import ThomsonN9.StageB.CapCert
import ThomsonN9.StageB.RigidityL4
import ThomsonN9.StageB.LocalMinL6

/-!
# Thomson problem for N = 9 — full formal solution

This file contains kernel-checked proofs of all four challenge statements fixed in
`ComparatorChallenges/ThomsonN9.lean`:

* `thomson_nine_M0` : every 9-point configuration of distinct points on the unit sphere has
  Coulomb energy at least `36 / 2 = 18` (trivial baseline).
* `thomson_nine_M1` : every such configuration has Coulomb energy at least `189 / 8 = 23.625`
  (first nontrivial bound).
* `thomson_nine` : some D3h tricapped trigonal prism `triCapPrism z` (`z ∈ (0, 1)`) is a global
  minimiser of the Coulomb energy among all 9-point configurations on the unit sphere `S²`.
* `thomson_nine_unique` : every global minimiser is isometric to `triCapPrism z` up to an
  orthogonal transformation of `ℝ³` and a relabelling of the 9 points.

As in the N = 7 package (`references/thomson-n7-lean`, whose solution and challenge files share
their prefix line for line), the definitions `R3`, `SphereConfig`, `coulombEnergy`, `cyl`,
`triCapPrism` and the auxiliary lemmas through `triCapPrism_mem` below are a verbatim copy of
lines 26–149 of `ComparatorChallenges/ThomsonN9.lean`; `scripts/check.sh` compares the two
modules' fully-elaborated statements, declaration by declaration.

**The full Stage B proof pipeline (`thomson_nine`, `thomson_nine_unique`).**
Let `z* ∈ [zStarLo, zStarHi] ⊂ (0, 1)` be the unique stationary height of the tricapped trigonal
prism (`StageB.LocalMinL6.exists_z_star`), certified via IVT to satisfy `E(triCapPrism z*) ≤ E_ttp_hi`.
Given any `x ∈ SphereConfig 9` with `E(x) ≤ E_ttp_hi`:
1. *Slab exclusion (`StageB.SlabCert.slab_exclusion`).* A 3-point symmetric-strip SDP certificate
   rules out any pair with `⟪x i, x j⟫ ≤ -9/10`, forcing all pairs into the cap `[-9/10, 1]`.
2. *Cap certificate & L3 tube forcing (`StageB.CapCert.cap_tube_forcing`).* An S3-invariant degree-18
   3-point SDP polynomial certificate (verified over 19 2D-Kronecker slices) plus a 7-piece
   Bernstein polynomial certificate forces every pairwise dot product within `1/10000` of one of
   the six TTP node curves `ν₀(z*), …, ν₅(z*)`.
3. *Combinatorial & metric rigidity (`StageB.RigidityL4.rigidity_to_ball`).* A certified 6-colour
   graph-search tree + Gram-matrix Procrustes bound aligns `x` by a permutation `σ` and an orthogonal
   matrix `Q` into the Frobenius ball `‖ttpX z* - rowPerm x σ * Q‖_F ≤ 1/500`.
4. *Local strict minimality (`StageB.LocalMinL6.local_min_ball`).* Procrustes rotational gauge
   fixing, exact Bregman-Young remainder bounds, and an integer Cholesky lower bound on the
   projected 27×27 Hessian prove `E(triCapPrism z*) ≤ E(x)` with equality iff `x` is orthogonally
   and permutationally equivalent to `triCapPrism z*`.

**The M0 proof.** Let `x ∈ SphereConfig 9`. Every pair `i < j` contributes at least `2⁻¹ = 1/2`
to `coulombEnergy x`: the points are distinct (`Function.Injective x`), hence `0 < ‖x i - x j‖`
(`norm_sub_pos_iff`), and both lie on the unit sphere, so the triangle inequality
(`norm_sub_le`) gives `‖x i - x j‖ ≤ ‖x i‖ + ‖x j‖ = 1 + 1 = 2`; antitonicity of inversion on
positives (`inv_anti₀`) then yields `2⁻¹ ≤ ‖x i - x j‖⁻¹`. Summing over all ordered pairs and
counting them, `∑ i : Fin 9, #(Ioi i) = 8 + 7 + ⋯ + 0 = 36` (a `decide`-checked arithmetic fact),
gives `coulombEnergy x ≥ 36 • 2⁻¹ = 36 / 2`.

**The M1 proof** (all rational data come from the generated module `ThomsonN9/M1Data.lean`,
built from the frozen LP artifact `results/lp_m1_light.json`). Let `f(t) = Σ_k c_k P_k(t)` be
the degree-8 polynomial minorant of the pair kernel `φ(t) = 1/√(2-2t)` on `[-1,1]` (with
`c_k = 0` off `k ∈ {0,1,2,3,7}` and `c_k ≥ 0` there), so that `p(t) = 1 - f(t)²(2-2t) ≥ 0` on
`[-1,1]` — certified in `M1Data` by a half-line Lukács sum-of-squares identity for
`(1+u)^15 · p((1-u)/(1+u))` after the Möbius change of variable `u = (1-t)/(1+t)`.

*Pair step.* For `i ≠ j` write `t = x i 0 * x j 0 + x i 1 * x j 1 + x i 2 * x j 2` (the inner
product, and `2 - 2t = ‖x i - x j‖²`). Then `t ∈ [-1,1]`, so `f(t)² · ‖x i - x j‖² ≤ 1`, i.e.
`f(t) ≤ ‖x i - x j‖⁻¹`; summing, `coulombEnergy x ≥ Σ_{i<j} f(t_ij)`.

*Kernel step.* For each `k ∈ {1,2,3,7}` the full double sum `Σ_{i,j} P_k(t_ij)` is nonnegative:
`M1Data.sphereKk` writes `(2k+1)·P_k(x·y)` as the bilinear form `Σ_{l,j'} (R⁻¹)_{l j'} h_l(x)
h_{j'}(y)` on the sphere (the two correction terms vanish because the points are on the unit
sphere), and summing over the pair `(i, j)` and re-associating (`double_sum_factor`) exhibits
it as `uᵀ R⁻¹ u` with `u_l = Σ_i h_l(x_i)`; `M1Data.quadKkS` rewrites this quadratic form as a
sum of squares with positive weights (`R⁻¹ = Sᵀ D⁻¹ S` from the LDLᵀ factorisation of the Gram
matrix `R = ∫ h h / 4π`).

*Assembly.* Since `f(t_ij) = c₀ + Σ_{k≥1} c_k P_k(t_ij)` and `c_k ≥ 0`, we get
`Σ_{i,j} f(t_ij) ≥ 81 c₀`; the diagonal contributes `t_ii = 1`, so `Σ_i f(t_ii) = 9 f(1)`; and
by symmetry (`sum_Ioi_half`) the pair sum is half the off-diagonal total. Hence
`coulombEnergy x ≥ (81 c₀ - 9 f(1)) / 2 = B`, and `189 / 8 < B` is an exact rational
comparison (`M1Data.B_lower`).
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

/-! ## Milestone M0 (proved here) -/

/-- **Milestone M0 (weak lower bound, N = 9).** Every configuration of 9 distinct points on the
unit sphere has Coulomb energy at least `36 / 2 = 18`: there are `(9 choose 2) = 36` pairs and
each pair is at distance at most `2`. This is the trivial baseline that any real lower bound must
beat. -/
theorem thomson_nine_M0 :
    ∀ x ∈ SphereConfig 9, (36 / 2 : ℝ) ≤ coulombEnergy x := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  -- Step 1: every pair `(i, j)` with `i < j` contributes at least `2⁻¹ = 1/2`. The two points
  -- are distinct (`Function.Injective x`), hence at positive distance (`norm_sub_pos_iff`),
  -- and both lie on the unit sphere, so `norm_sub_le` gives `‖x i - x j‖ ≤ 1 + 1 = 2`;
  -- `inv_anti₀` turns this into `2⁻¹ ≤ ‖x i - x j‖⁻¹`.
  have key : ∀ i : Fin 9, ∀ j ∈ Finset.Ioi i, (2 : ℝ)⁻¹ ≤ ‖x i - x j‖⁻¹ := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hne : x i ≠ x j := fun he => (ne_of_lt hij) (hx2 he)
    have hpos : 0 < ‖x i - x j‖ := norm_sub_pos_iff.mpr hne
    have hle : ‖x i - x j‖ ≤ 2 := by
      have h := norm_sub_le (x i) (x j)
      rw [hx1 i, hx1 j] at h
      linarith
    exact inv_anti₀ hpos hle
  -- Step 2: the number of ordered pairs `i < j` is `∑ i : Fin 9, #(Ioi i) = 8 + 7 + ⋯ + 0 = 36`
  -- (binomial coefficient `(9 choose 2)`), checked by `decide` on the Fin 9 fold.
  have hcount : ∑ i : Fin 9, ((Finset.Ioi i).card : ℝ) = 36 := by
    have h : ∑ i : Fin 9, (Finset.Ioi i).card = 36 := by decide
    exact_mod_cast h
  have hinner : ∀ i : Fin 9,
      ∑ j ∈ Finset.Ioi i, (2 : ℝ)⁻¹ = ((Finset.Ioi i).card : ℝ) * (2 : ℝ)⁻¹ := by
    intro i
    simp [Finset.sum_const]
  -- Step 3: sum the per-pair bound over all 36 pairs.
  show (36 / 2 : ℝ) ≤ ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹
  calc (36 / 2 : ℝ) = 36 * (2 : ℝ)⁻¹ := by norm_num
    _ = (∑ i : Fin 9, ((Finset.Ioi i).card : ℝ)) * (2 : ℝ)⁻¹ := by rw [hcount]
    _ = ∑ i : Fin 9, ((Finset.Ioi i).card : ℝ) * (2 : ℝ)⁻¹ := by rw [Finset.sum_mul]
    _ = ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (2 : ℝ)⁻¹ := by simp only [← hinner]
    _ ≤ ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => key i j hj

/-! ## Shared helpers for M1 -/

/-- Coordinate inner product on `ℝ³` realised as `EuclideanSpace ℝ (Fin 3)`. -/
private def dot (v w : R3) : ℝ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

/-- The squared norm is the sum of squared coordinates. -/
private lemma norm_sq_coords (v : R3) :
    ‖v‖ ^ 2 = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three, pow_two]

private lemma norm_sub_sq_coords (v w : R3) :
    ‖v - w‖ ^ 2 = (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) + (w 0 * w 0 + w 1 * w 1 + w 2 * w 2)
      - 2 * dot v w := by
  rw [norm_sq_coords]
  simp only [PiLp.sub_apply, Fin.sum_univ_three, pow_two]
  unfold dot
  ring

private lemma norm_add_sq_coords (v w : R3) :
    ‖v + w‖ ^ 2 = (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) + (w 0 * w 0 + w 1 * w 1 + w 2 * w 2)
      + 2 * dot v w := by
  rw [norm_sq_coords]
  simp only [PiLp.add_apply, Fin.sum_univ_three, pow_two]
  unfold dot
  ring

/-- For a symmetric pair functional on `Fin 9`, the upper-triangle sum is half of the
off-diagonal total. -/
private lemma sum_Ioi_half {g : Fin 9 → Fin 9 → ℝ} (hsym : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j ∈ Finset.Ioi i, g i j = (∑ i, ∑ j, g i j - ∑ i, g i i) / 2 := by
  have hpart : ∀ i : Fin 9, ∑ j : Fin 9, g i j
      = (∑ j ∈ Finset.Ioi i, g i j) + (∑ j ∈ Finset.Iio i, g i j) + g i i := by
    intro i
    have hdisj1 : Disjoint (Finset.Ioi i) (Finset.Iio i ∪ ({i} : Finset (Fin 9))) := by
      rw [Finset.disjoint_right]
      intro x hx h2
      rcases Finset.mem_union.mp hx with h | h
      · simp only [Finset.mem_Iio] at h; simp only [Finset.mem_Ioi] at h2; omega
      · simp only [Finset.mem_singleton] at h; subst h
        simp only [Finset.mem_Ioi] at h2; omega
    have hdisj2 : Disjoint (Finset.Iio i) ({i} : Finset (Fin 9)) := by
      rw [Finset.disjoint_right]
      intro x hx h2
      simp only [Finset.mem_singleton] at hx
      simp only [Finset.mem_Iio] at h2
      subst hx
      omega
    have huniv : (Finset.univ : Finset (Fin 9))
        = Finset.Ioi i ∪ (Finset.Iio i ∪ ({i} : Finset (Fin 9))) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_Iio,
        Finset.mem_singleton, iff_true]
      rcases lt_trichotomy j i with h | h | h <;> simp [h]
    rw [huniv, Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_singleton]
    ring
  have htot : ∑ i, ∑ j, g i j
      = (∑ i, ∑ j ∈ Finset.Ioi i, g i j) + (∑ i, ∑ j ∈ Finset.Iio i, g i j) + ∑ i, g i i := by
    rw [Finset.sum_congr rfl (fun i _ => hpart i)]
    simp only [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htri : (∑ i, ∑ j ∈ Finset.Iio i, g i j) = (∑ i, ∑ j ∈ Finset.Ioi i, g i j) := by
    have eIio : ∀ i : Fin 9, (∑ j ∈ Finset.Iio i, g i j)
        = ∑ j : Fin 9, if j < i then g i j else 0 := by
      intro i
      have hf : Finset.Iio i = (Finset.univ : Finset (Fin 9)).filter (fun j => j < i) := by
        ext j; simp [Finset.mem_filter, Finset.mem_Iio]
      rw [hf, Finset.sum_filter]
    have eIoi : ∀ i : Fin 9, (∑ j ∈ Finset.Ioi i, g i j)
        = ∑ j : Fin 9, if i < j then g i j else 0 := by
      intro i
      have hf : Finset.Ioi i = (Finset.univ : Finset (Fin 9)).filter (fun j => i < j) := by
        ext j; simp [Finset.mem_filter, Finset.mem_Ioi]
      rw [hf, Finset.sum_filter]
    have hL : (∑ i, ∑ j ∈ Finset.Iio i, g i j)
        = ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
            if p.2 < p.1 then g p.1 p.2 else 0 :=
      calc (∑ i, ∑ j ∈ Finset.Iio i, g i j)
          = ∑ i, ∑ j : Fin 9, if j < i then g i j else 0 :=
              Finset.sum_congr rfl (fun i _ => eIio i)
        _ = ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
              if p.2 < p.1 then g p.1 p.2 else 0 :=
              (Finset.sum_product (Finset.univ : Finset (Fin 9))
                (Finset.univ : Finset (Fin 9))
                (fun p => if p.2 < p.1 then g p.1 p.2 else 0)).symm
    have hR : (∑ i, ∑ j ∈ Finset.Ioi i, g i j)
        = ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
            if p.2 < p.1 then g p.1 p.2 else 0 :=
      calc (∑ i, ∑ j ∈ Finset.Ioi i, g i j)
          = ∑ i, ∑ j : Fin 9, if i < j then g i j else 0 :=
              Finset.sum_congr rfl (fun i _ => eIoi i)
        _ = ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
              if p.1 < p.2 then g p.1 p.2 else 0 :=
              (Finset.sum_product (Finset.univ : Finset (Fin 9))
                (Finset.univ : Finset (Fin 9))
                (fun p => if p.1 < p.2 then g p.1 p.2 else 0)).symm
        _ = ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
              if p.2 < p.1 then g p.1 p.2 else 0 := by
              refine Finset.sum_nbij (fun p => (p.2, p.1))
                (fun a _ => Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
                (fun a _ b _ h => Prod.swap_injective h)
                (fun b _ => ⟨(b.2, b.1),
                  Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, Prod.mk.eta⟩)
                (fun a _ => by rw [hsym a.2 a.1])
    rw [hL, hR]
  rw [htot, htri]
  ring

/-- Re-association of a quadruple sum: the pair-indexed double sum of the bilinear form
`Mr l j' • gb i l • gb j j'` factors into `Σ_{l,j'} Mr l j' • (Σ_i gb i l) • (Σ_j gb j j')`. -/
private lemma double_sum_factor {nk : ℕ} (Mr : Fin nk → Fin nk → ℝ) (gb : Fin 9 → Fin nk → ℝ) :
    ∑ i, ∑ j, ∑ l, ∑ j', Mr l j' * gb i l * gb j j'
      = ∑ l, ∑ j', Mr l j' * (∑ i, gb i l) * (∑ i, gb i j') := by
  have e1 : ∀ (F : (Fin 9 × Fin 9) → (Fin nk × Fin nk) → ℝ),
      (∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
        ∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ, F p q)
      = (∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ,
        ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ, F p q) :=
    fun F => Finset.sum_comm
  have hA : ∀ i j : Fin 9, (∑ l, ∑ j', Mr l j' * gb i l * gb j j')
      = ∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ,
          Mr q.1 q.2 * gb i q.1 * gb j q.2 :=
    fun i j => (Finset.sum_product (Finset.univ : Finset (Fin nk))
      (Finset.univ : Finset (Fin nk)) (fun q => Mr q.1 q.2 * gb i q.1 * gb j q.2)).symm
  have hper : ∀ q : Fin nk × Fin nk,
      (∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
        Mr q.1 q.2 * gb p.1 q.1 * gb p.2 q.2)
      = Mr q.1 q.2 * ((∑ i : Fin 9, gb i q.1) * ∑ j : Fin 9, gb j q.2) := by
    intro q
    calc (∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
            Mr q.1 q.2 * gb p.1 q.1 * gb p.2 q.2)
        = Mr q.1 q.2 * (∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
              gb p.1 q.1 * gb p.2 q.2) := by
          simp only [mul_assoc]
          rw [← Finset.mul_sum]
      _ = Mr q.1 q.2 * ((∑ i : Fin 9, gb i q.1) * ∑ j : Fin 9, gb j q.2) := by
          rw [Finset.sum_product]
          simp only [Prod.fst, Prod.snd]
          rw [← Finset.sum_mul_sum]
  calc ∑ i, ∑ j, ∑ l, ∑ j', Mr l j' * gb i l * gb j j'
      = ∑ i, ∑ j, ∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ,
          Mr q.1 q.2 * gb i q.1 * gb j q.2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hA i j))
    _ = ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
          ∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ,
          Mr q.1 q.2 * gb p.1 q.1 * gb p.2 q.2 :=
        (Finset.sum_product (Finset.univ : Finset (Fin 9)) (Finset.univ : Finset (Fin 9))
          (fun p => ∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ,
            Mr q.1 q.2 * gb p.1 q.1 * gb p.2 q.2)).symm
    _ = ∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ,
          ∑ p ∈ (Finset.univ : Finset (Fin 9)) ×ˢ Finset.univ,
          Mr q.1 q.2 * gb p.1 q.1 * gb p.2 q.2 := e1 _
    _ = ∑ q ∈ (Finset.univ : Finset (Fin nk)) ×ˢ Finset.univ,
          Mr q.1 q.2 * ((∑ i : Fin 9, gb i q.1) * ∑ j : Fin 9, gb j q.2) :=
        Finset.sum_congr rfl (fun q _ => hper q)
    _ = ∑ l, ∑ j', Mr l j' * (∑ i, gb i l) * (∑ i, gb i j') := by
        rw [Finset.sum_product]
        simp only [Prod.fst, Prod.snd]
        exact Finset.sum_congr rfl (fun l _ =>
          Finset.sum_congr rfl (fun j' _ => by ring))

/-- A constant factors out of a double sum. -/
private lemma sum_c_mul (c : ℝ) (F : Fin 9 → Fin 9 → ℝ) :
    ∑ i, ∑ j, c * F i j = c * ∑ i, ∑ j, F i j := by
  calc ∑ i, ∑ j, c * F i j
      = ∑ i, c * ∑ j, F i j :=
        Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ c).symm)
    _ = c * ∑ i, ∑ j, F i j := (Finset.mul_sum _ _ c).symm

/-- Kernel positivity: if `(2k+1)·Pt(t_ij)` admits the per-pair reproducing-kernel
representation (on the sphere) as the bilinear form `Σ Mr_lj' • gb_i l • gb_j j'`, and that
quadratic form is a nonnegative combination of squares at the aggregated vector
`u_l = Σ_i gb_i l`, then `Σ_{i,j} Pt(t_ij) ≥ 0`. -/
private lemma kern_nonneg {nk : ℕ} {T : Fin 9 → Fin 9 → ℝ} (Mr : Fin nk → Fin nk → ℝ)
    (Pt : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (gb : Fin 9 → Fin nk → ℝ)
    (pw : ∀ i j : Fin 9, c * Pt (T i j) = ∑ l, ∑ j', Mr l j' * gb i l * gb j j')
    (qd : 0 ≤ ∑ l, ∑ j', Mr l j' * (∑ i, gb i l) * (∑ i, gb i j')) :
    0 ≤ ∑ i, ∑ j, Pt (T i j) := by
  have h1 : (∑ i, ∑ j, c * Pt (T i j))
      = ∑ l, ∑ j', Mr l j' * (∑ i, gb i l) * (∑ i, gb i j') := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => pw i j)),
      double_sum_factor]
  have hm1 : c * ∑ i, ∑ j, Pt (T i j) = ∑ i, c * ∑ j, Pt (T i j) :=
    Finset.mul_sum _ _ c
  have hm2 : ∀ i : Fin 9, c * ∑ j, Pt (T i j) = ∑ j, c * Pt (T i j) :=
    fun i => Finset.mul_sum _ _ c
  have h2 : c * ∑ i, ∑ j, Pt (T i j)
      = ∑ l, ∑ j', Mr l j' * (∑ i, gb i l) * (∑ i, gb i j') := by
    rw [hm1, Finset.sum_congr rfl (fun i _ => hm2 i)]
    exact h1
  have hS : ∑ i, ∑ j, Pt (T i j)
      = (∑ l, ∑ j', Mr l j' * (∑ i, gb i l) * (∑ i, gb i j')) / c := by
    rw [eq_div_iff hc.ne']
    rw [mul_comm]
    exact h2
  rw [hS]
  exact div_nonneg qd hc.le

/-! ## Milestone M1 (proved here) -/

/-- Nonnegativity of the certificate polynomial `p(t) = 1 - f(t)²(2-2t)` on `[-1,1]`:
on `(-1,1]` this is the Möbius image of the half-line Lukács sum-of-squares identity for
`PuR u = (1+u)^15 · p((1-u)/(1+u))` (all weights nonnegative), and `p(-1) ≥ 0` is direct. -/
private lemma pR_nonneg {t : ℝ} (hm : -1 ≤ t) (h1 : t ≤ 1) : 0 ≤ ThomsonN9.M1.pR t := by
  rcases eq_or_lt_of_le hm with rfl | hlt
  · exact ThomsonN9.M1.pR_m1_nonneg
  · have h1p : (0 : ℝ) < 1 + t := by linarith
    have hu0 : (0 : ℝ) ≤ (1 - t) / (1 + t) := div_nonneg (by linarith) (by linarith)
    have h1u : (1 - t) / (1 + t) ≠ -1 := by
      intro he
      linarith
    have hsub : (1 - (1 - t) / (1 + t)) / (1 + (1 - t) / (1 + t)) = t := by
      field_simp
      ring
    have hM := ThomsonN9.M1.moebius_id h1u
    rw [hsub] at hM
    have h15 : (0 : ℝ) < (1 + (1 - t) / (1 + t)) ^ 15 := by positivity
    have hdiv : ThomsonN9.M1.pR t
        = ThomsonN9.M1.PuR ((1 - t) / (1 + t)) / (1 + (1 - t) / (1 + t)) ^ 15 := by
      rw [eq_div_iff h15.ne']
      linear_combination hM
    rw [hdiv]
    exact div_nonneg (ThomsonN9.M1.PuR_nonneg hu0) h15.le

/-- **Milestone M1 (first nontrivial lower bound, N = 9).** Every configuration of 9 distinct
points on the unit sphere has Coulomb energy at least `189 / 8 = 23.625`. This is the stage-one
target of `notes/strategy.md` (a two-point / averaging style bound, before the three-point
semidefinite machinery); it is still `23.625 < 25.759986531…` below the conjectured optimum. -/
theorem thomson_nine_M1 :
    ∀ x ∈ SphereConfig 9, (189 / 8 : ℝ) ≤ coulombEnergy x := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  -- coordinate facts
  have hn : ∀ i : Fin 9, x i 0 * x i 0 + x i 1 * x i 1 + x i 2 * x i 2 = 1 := by
    intro i
    have h := norm_sq_coords (x i)
    rw [hx1 i, one_pow] at h
    exact h.symm
  have hz : ∀ i : Fin 9, x i 0 * x i 0 + x i 1 * x i 1 + x i 2 * x i 2 - 1 = 0 := by
    intro i
    have := hn i
    linarith
  have hsq : ∀ i j : Fin 9, ‖x i - x j‖ ^ 2 = 2 - 2 * dot (x i) (x j) := by
    intro i j
    have h := norm_sub_sq_coords (x i) (x j)
    rw [hn i, hn j] at h
    linarith
  have hplus : ∀ i j : Fin 9, ‖x i + x j‖ ^ 2 = 2 + 2 * dot (x i) (x j) := by
    intro i j
    have h := norm_add_sq_coords (x i) (x j)
    rw [hn i, hn j] at h
    linarith
  -- the pair step: f(t_ij) ≤ 1/d_ij for i ≠ j
  have pairwise : ∀ i j : Fin 9, i ≠ j →
      ThomsonN9.M1.fR (dot (x i) (x j)) ≤ (‖x i - x j‖)⁻¹ := by
    intro i j hij
    have hne : x i ≠ x j := fun he => hij (hx2 he)
    have hd : (0 : ℝ) < ‖x i - x j‖ := norm_sub_pos_iff.mpr hne
    have hT1 : dot (x i) (x j) ≤ 1 := by
      have h : (0 : ℝ) ≤ ‖x i - x j‖ ^ 2 := sq_nonneg _
      rw [hsq i j] at h
      linarith
    have hTm1 : -1 ≤ dot (x i) (x j) := by
      have h : (0 : ℝ) ≤ ‖x i + x j‖ ^ 2 := sq_nonneg _
      rw [hplus i j] at h
      linarith
    have hp := pR_nonneg hTm1 hT1
    have hp' : (0 : ℝ) ≤ 1 - 2 * (1 - dot (x i) (x j))
        * (ThomsonN9.M1.fR (dot (x i) (x j))) ^ 2 := hp
    have hf : (ThomsonN9.M1.fR (dot (x i) (x j))) ^ 2 * ‖x i - x j‖ ^ 2 ≤ 1 := by
      rw [hsq i j]
      have hring : (ThomsonN9.M1.fR (dot (x i) (x j))) ^ 2 * (2 - 2 * dot (x i) (x j))
          = 2 * (1 - dot (x i) (x j)) * (ThomsonN9.M1.fR (dot (x i) (x j))) ^ 2 := by
        ring
      linarith
    have hfd : ThomsonN9.M1.fR (dot (x i) (x j)) * ‖x i - x j‖ ≤ 1 := by
      have h2 : (ThomsonN9.M1.fR (dot (x i) (x j)) * ‖x i - x j‖) ^ 2
          ≤ (1 : ℝ) ^ 2 := by
        rw [mul_pow]
        linarith
      exact (abs_le_of_sq_le_sq' h2 zero_le_one).2
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hd).mpr hfd
  -- the kernel step: Σ_{i,j} P_k(t_ij) ≥ 0 for k ∈ {1,2,3,7}
  have kern1 : (0 : ℝ) ≤ ∑ i, ∑ j, ThomsonN9.M1.P1R (dot (x i) (x j)) := by
    refine kern_nonneg (fun l j' => ((ThomsonN9.M1.M1R l j' : ℚ) : ℝ))
      ThomsonN9.M1.P1R ((2*1+1 : ℚ) : ℝ) (by norm_num)
      (fun i l => ThomsonN9.M1.h1T l (x i 0) (x i 1) (x i 2)) ?_ ?_
    · intro i j
      have h1 := ThomsonN9.M1.sphereK1S (x i 0) (x i 1) (x i 2) (x j 0) (x j 1) (x j 2)
      simp only [hz i, hz j, zero_mul, add_zero] at h1
      exact h1
    · rw [ThomsonN9.M1.quadK1S
        (fun l => ∑ i, ThomsonN9.M1.h1T l (x i 0) (x i 1) (x i 2))]
      exact ThomsonN9.M1.quadK1_nonneg
        (fun l => ∑ i, ThomsonN9.M1.h1T l (x i 0) (x i 1) (x i 2))
  have kern2 : (0 : ℝ) ≤ ∑ i, ∑ j, ThomsonN9.M1.P2R (dot (x i) (x j)) := by
    refine kern_nonneg (fun l j' => ((ThomsonN9.M1.M2R l j' : ℚ) : ℝ))
      ThomsonN9.M1.P2R ((2*2+1 : ℚ) : ℝ) (by norm_num)
      (fun i l => ThomsonN9.M1.h2T l (x i 0) (x i 1) (x i 2)) ?_ ?_
    · intro i j
      have h1 := ThomsonN9.M1.sphereK2S (x i 0) (x i 1) (x i 2) (x j 0) (x j 1) (x j 2)
      simp only [hz i, hz j, zero_mul, add_zero] at h1
      exact h1
    · rw [ThomsonN9.M1.quadK2S
        (fun l => ∑ i, ThomsonN9.M1.h2T l (x i 0) (x i 1) (x i 2))]
      exact ThomsonN9.M1.quadK2_nonneg
        (fun l => ∑ i, ThomsonN9.M1.h2T l (x i 0) (x i 1) (x i 2))
  have kern3 : (0 : ℝ) ≤ ∑ i, ∑ j, ThomsonN9.M1.P3R (dot (x i) (x j)) := by
    refine kern_nonneg (fun l j' => ((ThomsonN9.M1.M3R l j' : ℚ) : ℝ))
      ThomsonN9.M1.P3R ((2*3+1 : ℚ) : ℝ) (by norm_num)
      (fun i l => ThomsonN9.M1.h3T l (x i 0) (x i 1) (x i 2)) ?_ ?_
    · intro i j
      have h1 := ThomsonN9.M1.sphereK3S (x i 0) (x i 1) (x i 2) (x j 0) (x j 1) (x j 2)
      simp only [hz i, hz j, zero_mul, add_zero] at h1
      exact h1
    · rw [ThomsonN9.M1.quadK3S
        (fun l => ∑ i, ThomsonN9.M1.h3T l (x i 0) (x i 1) (x i 2))]
      exact ThomsonN9.M1.quadK3_nonneg
        (fun l => ∑ i, ThomsonN9.M1.h3T l (x i 0) (x i 1) (x i 2))
  have kern7 : (0 : ℝ) ≤ ∑ i, ∑ j, ThomsonN9.M1.P7R (dot (x i) (x j)) := by
    refine kern_nonneg (fun l j' => ((ThomsonN9.M1.M7R l j' : ℚ) : ℝ))
      ThomsonN9.M1.P7R ((2*7+1 : ℚ) : ℝ) (by norm_num)
      (fun i l => ThomsonN9.M1.h7T l (x i 0) (x i 1) (x i 2)) ?_ ?_
    · intro i j
      have h1 := ThomsonN9.M1.sphereK7S (x i 0) (x i 1) (x i 2) (x j 0) (x j 1) (x j 2)
      simp only [hz i, hz j, zero_mul, add_zero] at h1
      exact h1
    · rw [ThomsonN9.M1.quadK7S
        (fun l => ∑ i, ThomsonN9.M1.h7T l (x i 0) (x i 1) (x i 2))]
      exact ThomsonN9.M1.quadK7_nonneg
        (fun l => ∑ i, ThomsonN9.M1.h7T l (x i 0) (x i 1) (x i 2))
  -- assembly: Σ_{i,j} f(t_ij) ≥ 81 c₀
  have fsumleg : ∀ i j : Fin 9, ThomsonN9.M1.fR (dot (x i) (x j))
      = ThomsonN9.M1.c0R + ThomsonN9.M1.c1R * ThomsonN9.M1.P1R (dot (x i) (x j))
        + ThomsonN9.M1.c2R * ThomsonN9.M1.P2R (dot (x i) (x j))
        + ThomsonN9.M1.c3R * ThomsonN9.M1.P3R (dot (x i) (x j))
        + ThomsonN9.M1.c7R * ThomsonN9.M1.P7R (dot (x i) (x j)) :=
    fun i j => ThomsonN9.M1.fR_eq_legendre (dot (x i) (x j))
  have hconst : ∑ i : Fin 9, ∑ j : Fin 9, ThomsonN9.M1.c0R = 81 * ThomsonN9.M1.c0R := by
    simp [Finset.sum_const]
    ring
  have hsplit : ∑ i, ∑ j, ThomsonN9.M1.fR (dot (x i) (x j))
      = (∑ i : Fin 9, ∑ j : Fin 9, ThomsonN9.M1.c0R)
        + ThomsonN9.M1.c1R * (∑ i, ∑ j, ThomsonN9.M1.P1R (dot (x i) (x j)))
        + ThomsonN9.M1.c2R * (∑ i, ∑ j, ThomsonN9.M1.P2R (dot (x i) (x j)))
        + ThomsonN9.M1.c3R * (∑ i, ∑ j, ThomsonN9.M1.P3R (dot (x i) (x j)))
        + ThomsonN9.M1.c7R * (∑ i, ∑ j, ThomsonN9.M1.P7R (dot (x i) (x j))) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => fsumleg i j))]
    simp only [Finset.sum_add_distrib]
    rw [sum_c_mul, sum_c_mul, sum_c_mul, sum_c_mul]
  have hfsum : (81 : ℝ) * ThomsonN9.M1.c0R ≤ ∑ i, ∑ j, ThomsonN9.M1.fR (dot (x i) (x j)) := by
    rw [hsplit, hconst]
    have n1 : (0 : ℝ) ≤ ThomsonN9.M1.c1R * ∑ i, ∑ j, ThomsonN9.M1.P1R (dot (x i) (x j)) :=
      mul_nonneg ThomsonN9.M1.c1R_nonneg kern1
    have n2 : (0 : ℝ) ≤ ThomsonN9.M1.c2R * ∑ i, ∑ j, ThomsonN9.M1.P2R (dot (x i) (x j)) :=
      mul_nonneg ThomsonN9.M1.c2R_nonneg kern2
    have n3 : (0 : ℝ) ≤ ThomsonN9.M1.c3R * ∑ i, ∑ j, ThomsonN9.M1.P3R (dot (x i) (x j)) :=
      mul_nonneg ThomsonN9.M1.c3R_nonneg kern3
    have n7 : (0 : ℝ) ≤ ThomsonN9.M1.c7R * ∑ i, ∑ j, ThomsonN9.M1.P7R (dot (x i) (x j)) :=
      mul_nonneg ThomsonN9.M1.c7R_nonneg kern7
    linarith
  -- the diagonal: t_ii = 1 and f(1) = fOneR
  have hdiag : ∑ i, ThomsonN9.M1.fR (dot (x i) (x i)) = 9 * ThomsonN9.M1.fOneR := by
    have hii : ∀ i : Fin 9, dot (x i) (x i) = 1 := by
      intro i
      have := hn i
      unfold dot
      linarith
    rw [Finset.sum_congr rfl (fun i _ => by rw [hii i])]
    rw [ThomsonN9.M1.fR_one]
    simp [Finset.sum_const]
  -- final chain
  have hfin : ((81 : ℝ) * ThomsonN9.M1.c0R - 9 * ThomsonN9.M1.fOneR) / 2 ≤ coulombEnergy x := by
    unfold coulombEnergy
    calc ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹
        ≥ ∑ i, ∑ j ∈ Finset.Ioi i, ThomsonN9.M1.fR (dot (x i) (x j)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
            pairwise i j (ne_of_lt (Finset.mem_Ioi.mp hj))
      _ = (∑ i, ∑ j, ThomsonN9.M1.fR (dot (x i) (x j))
            - ∑ i, ThomsonN9.M1.fR (dot (x i) (x i))) / 2 :=
          sum_Ioi_half (fun i j => congrArg ThomsonN9.M1.fR (by unfold dot; ring))
      _ ≥ ((81 : ℝ) * ThomsonN9.M1.c0R - 9 * ThomsonN9.M1.fOneR) / 2 := by
          rw [hdiag]
          linarith
  calc (189 / 8 : ℝ) ≤ ThomsonN9.M1.BR := le_of_lt ThomsonN9.M1.B_lower
    _ = (81 * ThomsonN9.M1.c0R - 9 * ThomsonN9.M1.fOneR) / 2 := ThomsonN9.M1.B_assembly.symm
    _ ≤ coulombEnergy x := hfin

/-! ## Full Stage B proofs of `thomson_nine` and `thomson_nine_unique` -/

private lemma triCapPrism_eq_ttpPt (z : ℝ) :
    triCapPrism z = StageB.LocalMinL6.ttpPt z := by
  funext i
  exact StageB.LocalMinL6.cyl_triCapPrism_eq_ttpPt z i

private lemma coulombEnergy_eq_9 (x : Fin 9 → R3) :
    coulombEnergy x = StageB.coulombEnergy9 x := rfl

private lemma coulombEnergy_isometry (g : R3 ≃ₗᵢ[ℝ] R3) (x : Fin 9 → R3) :
    coulombEnergy (fun i => g (x i)) = coulombEnergy x := by
  unfold coulombEnergy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_sub, g.norm_map]

private lemma coulombEnergy_perm (x : Fin 9 → R3) (σ : Equiv.Perm (Fin 9)) :
    coulombEnergy (fun i => x (σ i)) = coulombEnergy x :=
  StageB.SlabCert.coulombEnergy9_perm x σ

private lemma low_energy_to_ball {zStar : ℝ}
    (hzLo : (StageB.LocalMinL6Data.zStarLo : ℝ) ≤ zStar)
    (hzHi : zStar ≤ (StageB.LocalMinL6Data.zStarHi : ℝ))
    {x : Fin 9 → R3} (hx : x ∈ SphereConfig 9)
    (hE : coulombEnergy x ≤ StageB.SlabCert.E_ttp_hi) :
    ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 9)),
      ∑ i : Fin 9, ‖g (x (σ i)) - StageB.LocalMinL6.ttpPt zStar i‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := by
  obtain ⟨hu, hinj⟩ := hx
  have hcap : ∀ i j : Fin 9, i ≠ j → (-9 / 10 : ℝ) ≤ @inner ℝ R3 _ (x i) (x j) := by
    intro i j hij
    by_contra hlt
    have hle : @inner ℝ R3 _ (x i) (x j) ≤ -9 / 10 := (not_le.mp hlt).le
    have hgt := StageB.SlabCert.slab_exclusion x hu hinj ⟨i, j, hij, hle⟩
    rw [coulombEnergy_eq_9] at hE
    linarith
  have hzBoxLo : (TableB5Data.zLo : ℝ) ≤ zStar :=
    le_trans (by exact_mod_cast StageB.LocalMinL6Data.zStar_in_zBox.1) hzLo
  have hzBoxHi : zStar ≤ (TableB5Data.zHi : ℝ) :=
    le_trans hzHi (by exact_mod_cast StageB.LocalMinL6Data.zStar_in_zBox.2.2)
  have hE_cap : StageB.coulombEnergy9 x ≤ StageB.CapCert.E_ttp_hi := by
    have hEq : StageB.SlabCert.E_ttp_hi = StageB.CapCert.E_ttp_hi := by
      unfold StageB.SlabCert.E_ttp_hi StageB.CapCert.E_ttp_hi
      norm_num [StageB.SlabCertData.E_ttp_hi_num, StageB.SlabCertData.E_ttp_hi_den,
        StageB.CapCertHarmData.E_ttp_hi_num, StageB.CapCertHarmData.E_ttp_hi_den]
    rw [← hEq, ← coulombEnergy_eq_9]
    exact hE
  have hTube : TableB5Chain.TubePremise (StageB.CapCert.toMat x) zStar (1 / 10000) :=
    StageB.CapCert.cap_tube_forcing x hu hinj hcap hE_cap zStar hzBoxLo hzBoxHi
  obtain ⟨σ, Q, hQ, hfrob⟩ :=
    StageB.RigidityL4.rigidity_to_ball x hu zStar hzBoxLo hzBoxHi hTube
  obtain ⟨g, hg⟩ := StageB.LocalMinL6.iso_of_orthogonal Q hQ
  refine ⟨g, σ, ?_⟩
  rw [hg x σ zStar]
  have hfrob_nn : 0 ≤ TableB5Core.frob
      (TableB5Core.ttpX zStar - TableB5Chain.rowPerm (StageB.CapCert.toMat x) σ * Q) :=
    Real.sqrt_nonneg _
  exact pow_le_pow_left₀ hfrob_nn hfrob 2

/-- **Main target (Thomson, N = 9).** Some D3h tricapped trigonal prism (numerically
`z ≈ 0.70365`, energy `≈ 25.759986531`) is a global minimiser among 9-point configurations. -/
theorem thomson_nine :
    ∃ z ∈ Set.Ioo (0 : ℝ) 1,
      ∀ x ∈ SphereConfig 9, coulombEnergy (triCapPrism z) ≤ coulombEnergy x := by
  obtain ⟨zStar, hzLo, hzHi, hcrit, hE_star⟩ := StageB.LocalMinL6.exists_z_star
  have hz0 : (0 : ℝ) < zStar :=
    lt_of_lt_of_le (by norm_num [StageB.LocalMinL6Data.zStarLo]) hzLo
  have hz1 : zStar < 1 :=
    lt_of_le_of_lt hzHi (by norm_num [StageB.LocalMinL6Data.zStarHi])
  refine ⟨zStar, ⟨hz0, hz1⟩, fun x hx => ?_⟩
  by_cases hE : coulombEnergy x ≤ StageB.SlabCert.E_ttp_hi
  · obtain ⟨g, σ, hclose⟩ := low_energy_to_ball hzLo hzHi hx hE
    let y : Fin 9 → R3 := fun i => g (x (σ i))
    have hyu : ∀ i, ‖y i‖ = 1 := fun i => by simp [y, hx.1 (σ i)]
    have hyinj : Function.Injective y := g.injective.comp (hx.2.comp σ.injective)
    have hloc := (StageB.LocalMinL6.local_min_ball hzLo hzHi hcrit hyu hyinj hclose).1
    have hEy : coulombEnergy y = coulombEnergy x := by
      dsimp only [y]
      rw [coulombEnergy_isometry g (fun i => x (σ i)), coulombEnergy_perm x σ]
    rw [triCapPrism_eq_ttpPt, coulombEnergy_eq_9, ← hEy, coulombEnergy_eq_9]
    exact hloc
  · have hgt : StageB.SlabCert.E_ttp_hi < coulombEnergy x := not_le.mp hE
    rw [triCapPrism_eq_ttpPt, coulombEnergy_eq_9]
    linarith

/-- **Uniqueness (N = 9).** Any global minimiser is a tricapped trigonal prism up to an orthogonal
transformation of `ℝ³` and a relabelling of the points. -/
theorem thomson_nine_unique :
    ∀ x ∈ SphereConfig 9, (∀ y ∈ SphereConfig 9, coulombEnergy x ≤ coulombEnergy y) →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 9)) (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) 1),
        ∀ i, x i = g (triCapPrism z (σ i)) := by
  intro x hx hmin
  obtain ⟨zStar, hzLo, hzHi, hcrit, hE_star⟩ := StageB.LocalMinL6.exists_z_star
  have hz0 : (0 : ℝ) < zStar :=
    lt_of_lt_of_le (by norm_num [StageB.LocalMinL6Data.zStarLo]) hzLo
  have hz1 : zStar < 1 :=
    lt_of_le_of_lt hzHi (by norm_num [StageB.LocalMinL6Data.zStarHi])
  have hzIoo : zStar ∈ Set.Ioo (0 : ℝ) 1 := ⟨hz0, hz1⟩
  have hEx_le_star : coulombEnergy x ≤ coulombEnergy (triCapPrism zStar) :=
    hmin (triCapPrism zStar) (triCapPrism_mem zStar hzIoo)
  have hEx_le_hi : coulombEnergy x ≤ StageB.SlabCert.E_ttp_hi := by
    rw [triCapPrism_eq_ttpPt] at hEx_le_star
    simp_rw [coulombEnergy_eq_9] at hEx_le_star ⊢
    linarith
  obtain ⟨g₁, σ, hclose⟩ := low_energy_to_ball hzLo hzHi hx hEx_le_hi
  let y : Fin 9 → R3 := fun i => g₁ (x (σ i))
  have hyu : ∀ i, ‖y i‖ = 1 := fun i => by simp [y, hx.1 (σ i)]
  have hyinj : Function.Injective y := g₁.injective.comp (hx.2.comp σ.injective)
  obtain ⟨hloc_le, hloc_eq⟩ := StageB.LocalMinL6.local_min_ball hzLo hzHi hcrit hyu hyinj hclose
  have hEy : coulombEnergy y = coulombEnergy x := by
    dsimp only [y]
    rw [coulombEnergy_isometry g₁ (fun i => x (σ i)), coulombEnergy_perm x σ]
  have hEq : StageB.coulombEnergy9 y = StageB.coulombEnergy9 (StageB.LocalMinL6.ttpPt zStar) := by
    rw [triCapPrism_eq_ttpPt] at hEx_le_star
    simp_rw [coulombEnergy_eq_9] at hEx_le_star hEy
    linarith
  obtain ⟨g₂, hg₂⟩ := hloc_eq hEq
  refine ⟨g₂.trans g₁.symm, σ.symm, zStar, hzIoo, fun i => ?_⟩
  have hi := hg₂ (σ.symm i)
  simp only [y, Equiv.apply_symm_apply] at hi
  rw [triCapPrism_eq_ttpPt]
  have hstep : g₁.symm (g₁ (x i)) = g₁.symm (g₂ (StageB.LocalMinL6.ttpPt zStar (σ.symm i))) :=
    congrArg g₁.symm hi
  simpa [LinearIsometryEquiv.trans_apply] using hstep

/-- **Strengthened joint global optimality and `O(3) × S₉` uniqueness (Theorem 1.1).**
There exists a single stationary prism half-height `zStar ∈ [zStarLo, zStarHi] ⊂ (0, 1)`
(width `10⁻¹⁸`, `critGap zStar = 0`) that globally minimizes `coulombEnergy` on `SphereConfig 9`
and characterizes all global minimizers up to linear isometry and point relabeling. -/
theorem thomson_nine_main :
    ∃ zStar ∈ Set.Icc (StageB.LocalMinL6Data.zStarLo : ℝ) (StageB.LocalMinL6Data.zStarHi : ℝ),
      StageB.LocalMinL6.critGap zStar = 0 ∧
      (∀ x ∈ SphereConfig 9, coulombEnergy (triCapPrism zStar) ≤ coulombEnergy x) ∧
      (∀ x ∈ SphereConfig 9,
        coulombEnergy x = coulombEnergy (triCapPrism zStar) ↔
          ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 9)),
            ∀ i, x i = g (triCapPrism zStar (σ i))) := by
  obtain ⟨zStar, hzLo, hzHi, hcrit, hE_star⟩ := StageB.LocalMinL6.exists_z_star
  refine ⟨zStar, ⟨hzLo, hzHi⟩, hcrit, ?_, ?_⟩
  · intro x hx
    by_cases hE : coulombEnergy x ≤ StageB.SlabCert.E_ttp_hi
    · obtain ⟨g, σ, hclose⟩ := low_energy_to_ball hzLo hzHi hx hE
      let y : Fin 9 → R3 := fun i => g (x (σ i))
      have hyu : ∀ i, ‖y i‖ = 1 := fun i => by simp [y, hx.1 (σ i)]
      have hyinj : Function.Injective y := g.injective.comp (hx.2.comp σ.injective)
      have hloc := (StageB.LocalMinL6.local_min_ball hzLo hzHi hcrit hyu hyinj hclose).1
      have hEy : coulombEnergy y = coulombEnergy x := by
        dsimp only [y]
        rw [coulombEnergy_isometry g (fun i => x (σ i)), coulombEnergy_perm x σ]
      rw [triCapPrism_eq_ttpPt, coulombEnergy_eq_9, ← hEy, coulombEnergy_eq_9]
      exact hloc
    · have hgt : StageB.SlabCert.E_ttp_hi < coulombEnergy x := not_le.mp hE
      rw [triCapPrism_eq_ttpPt, coulombEnergy_eq_9]
      linarith
  · intro x hx
    constructor
    · intro hEq_E
      have hEx_le_hi : coulombEnergy x ≤ StageB.SlabCert.E_ttp_hi := by
        rw [hEq_E, triCapPrism_eq_ttpPt, coulombEnergy_eq_9]
        exact hE_star
      obtain ⟨g₁, σ, hclose⟩ := low_energy_to_ball hzLo hzHi hx hEx_le_hi
      let y : Fin 9 → R3 := fun i => g₁ (x (σ i))
      have hyu : ∀ i, ‖y i‖ = 1 := fun i => by simp [y, hx.1 (σ i)]
      have hyinj : Function.Injective y := g₁.injective.comp (hx.2.comp σ.injective)
      obtain ⟨_, hloc_eq⟩ := StageB.LocalMinL6.local_min_ball hzLo hzHi hcrit hyu hyinj hclose
      have hEy : coulombEnergy y = coulombEnergy x := by
        dsimp only [y]
        rw [coulombEnergy_isometry g₁ (fun i => x (σ i)), coulombEnergy_perm x σ]
      have hEq : StageB.coulombEnergy9 y = StageB.coulombEnergy9 (StageB.LocalMinL6.ttpPt zStar) := by
        rw [← coulombEnergy_eq_9, hEy, hEq_E, triCapPrism_eq_ttpPt, coulombEnergy_eq_9]
      obtain ⟨g₂, hg₂⟩ := hloc_eq hEq
      refine ⟨g₂.trans g₁.symm, σ.symm, fun i => ?_⟩
      have hi := hg₂ (σ.symm i)
      simp only [y, Equiv.apply_symm_apply] at hi
      rw [triCapPrism_eq_ttpPt]
      have hstep : g₁.symm (g₁ (x i)) = g₁.symm (g₂ (StageB.LocalMinL6.ttpPt zStar (σ.symm i))) :=
        congrArg g₁.symm hi
      simpa [LinearIsometryEquiv.trans_apply] using hstep
    · rintro ⟨g, σ, hx_eq⟩
      have hfun : x = fun i => g (triCapPrism zStar (σ i)) := funext hx_eq
      rw [hfun, coulombEnergy_isometry g (fun i => triCapPrism zStar (σ i)),
        coulombEnergy_perm (triCapPrism zStar) σ]

end ThomsonN9
