import Mathlib

/-!
# Thomson N = 9 Stage B — Module 1: Three-Point Positivity & Assembly Identities

Provides:
1. Unit-sphere inner product / distance identities (`norm_sub_sq_unit`, `inv_norm_eq_phi`),
   3×3 Gram nonnegativity (`detG_nonneg_of_unit`), and 4×4 Gram singularity in `ℝ³`
   (`det4_eq_zero_of_unit`).
2. Generic Bachoc–Vallentin three-point positivity (`Q3`, `sum_cholesky_Y3_nonneg_center`,
   `sum_cholesky_Y3_nonneg_finset`) via complex de Moivre, valid for any center set `S`,
   any harmonic order `k : ℕ`, and any block size `m : ℕ`.
3. Exact 9-point combinatorial assembly identities:
   * `cap_assembly_9` — untyped `S₃`-symmetric 3-point identity (`n = 9`).
   * `slab_assembly_9` — typed `(2, 7)` pole-ring 3-point identity (`P = {0,1}`, `R = {2..8}`).
   * `exists_swap_to_01` — moves any pair `(i, j)` with `i ≠ j` to `(0, 1)`.
-/

set_option maxHeartbeats 2000000

namespace ThomsonN9.StageB

open Finset Real
open scoped RealInnerProductSpace Matrix

/-- Euclidean 3-space (definitionally equal to `ThomsonN9.R3`). -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Coulomb energy of a 9-point configuration (definitionally equal to `ThomsonN9.coulombEnergy`). -/
noncomputable def coulombEnergy9 (x : Fin 9 → R3) : ℝ :=
  ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹

/-- Pair Coulomb potential in inner-product variable `t = ⟪x, y⟫`: `φ(t) = 1 / √(2 - 2t)`. -/
noncomputable def phi (t : ℝ) : ℝ := (Real.sqrt (2 - 2 * t))⁻¹

lemma inner_R3_expand (x y : R3) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three, mul_comm]

lemma norm_sq_R3_expand (x : R3) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_R3_expand]; ring

lemma norm_sub_sq_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ^ 2 = 2 - 2 * ⟪x, y⟫ := by
  rw [norm_sub_sq_real, hx, hy]; ring

lemma inv_norm_eq_phi {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖⁻¹ = phi ⟪x, y⟫ := by
  unfold phi
  rw [← norm_sub_sq_unit hx hy, Real.sqrt_sq (norm_nonneg _)]

lemma neg_one_le_inner_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ ⟪x, y⟫ := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one, abs_le] at h
  exact h.1

lemma inner_le_one_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ ≤ 1 := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one, abs_le] at h
  exact h.2

lemma inner_lt_one_of_ne_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : x ≠ y) :
    ⟪x, y⟫ < 1 := by
  have hpos : 0 < ‖x - y‖ ^ 2 := by
    have : 0 < ‖x - y‖ := norm_sub_pos_iff.mpr hne
    positivity
  rw [norm_sub_sq_unit hx hy] at hpos
  linarith

/-! ## Gram determinants `detG` (3×3) and `det4` (4×4) on `S² ⊂ ℝ³` -/

/-- `3×3` unit Gram determinant `1 + 2uvt - u² - v² - t²`. -/
def detG (u v t : ℝ) : ℝ := 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2

/-- `4×4` unit Gram determinant. -/
def det4 (g01 g02 g03 g12 g13 g23 : ℝ) : ℝ :=
  1 - (g01 ^ 2 + g02 ^ 2 + g03 ^ 2 + g12 ^ 2 + g13 ^ 2 + g23 ^ 2)
    + 2 * (g01 * g02 * g12 + g01 * g03 * g13 + g02 * g03 * g23 + g12 * g13 * g23)
    + ((g01 * g23) ^ 2 + (g02 * g13) ^ 2 + (g03 * g12) ^ 2)
    - 2 * (g01 * g02 * g13 * g23 + g01 * g03 * g12 * g23 + g02 * g03 * g12 * g13)

theorem detG_nonneg_of_unit {x y z : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ detG ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ := by
  have h1 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by rw [← norm_sq_R3_expand, hx]; norm_num
  have h2 : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1 := by rw [← norm_sq_R3_expand, hy]; norm_num
  have h3 : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 1 := by rw [← norm_sq_R3_expand, hz]; norm_num
  have key : detG ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ =
      (x 0 * (y 1 * z 2 - y 2 * z 1) + x 1 * (y 2 * z 0 - y 0 * z 2)
        + x 2 * (y 0 * z 1 - y 1 * z 0)) ^ 2 := by
    simp only [detG, inner_R3_expand]
    have hx1 : (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)
        * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) = 1 := by rw [h1, h2, h3]; norm_num
    linear_combination
      - hx1
      + (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) ^ 2 * h1
      + (x 0 * z 0 + x 1 * z 1 + x 2 * z 2) ^ 2 * h2
      + (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) ^ 2 * h3
  rw [key]
  positivity

theorem det4_eq_zero_of_unit (x0 x1 x2 x3 : R3)
    (h0 : ‖x0‖ = 1) (h1 : ‖x1‖ = 1) (h2 : ‖x2‖ = 1) (h3 : ‖x3‖ = 1) :
    det4 ⟪x0, x1⟫ ⟪x0, x2⟫ ⟪x0, x3⟫ ⟪x1, x2⟫ ⟪x1, x3⟫ ⟪x2, x3⟫ = 0 := by
  let vec : Fin 4 → R3 := ![x0, x1, x2, x3]
  let A : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j =>
    if h : j.val < 3 then vec i ⟨j.val, h⟩ else 0
  have hAdet : A.det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero (3 : Fin 4) (fun i => by simp [A])
  have hGdet : (A * Aᵀ).det = 0 := by
    rw [Matrix.det_mul, hAdet, zero_mul]
  have hGentry : ∀ i j : Fin 4, (A * Aᵀ) i j = ⟪vec i, vec j⟫ := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, A,
      Matrix.of_apply, inner_R3_expand]
    norm_num
  have hGdiag : ∀ i : Fin 4, (A * Aᵀ) i i = 1 := by
    intro i
    rw [hGentry, real_inner_self_eq_norm_sq]
    fin_cases i <;> simp [vec, h0, h1, h2, h3]
  have hGsym : ∀ i j : Fin 4, (A * Aᵀ) j i = (A * Aᵀ) i j := by
    intro i j
    rw [hGentry, hGentry, real_inner_comm]
  have hexp : (A * Aᵀ).det =
      det4 ((A * Aᵀ) 0 1) ((A * Aᵀ) 0 2) ((A * Aᵀ) 0 3)
           ((A * Aᵀ) 1 2) ((A * Aᵀ) 1 3) ((A * Aᵀ) 2 3) := by
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove,
      det4, hGdiag 0, hGdiag 1, hGdiag 2, hGdiag 3,
      hGsym 0 1, hGsym 0 2, hGsym 0 3, hGsym 1 2, hGsym 1 3, hGsym 2 3]
    ring
  rw [hexp, hGentry 0 1, hGentry 0 2, hGentry 0 3, hGentry 1 2, hGentry 1 3, hGentry 2 3] at hGdet
  simpa [vec] using hGdet

/-! ## Bachoc–Vallentin three-point positivity (`Q3`, `Y3`, Cholesky rank-1 form) -/

/-- Chebyshev–Gegenbauer 3-point polynomial `Q_k(u, v, t)`. -/
def Q3 : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | k + 2, u, v, t =>
      2 * (t - u * v) * Q3 (k + 1) u v t - (1 - u ^ 2) * (1 - v ^ 2) * Q3 k u v t

theorem Q3_eq_re (u v t : ℝ) (z z' : ℂ)
    (hu : 1 - u ^ 2 = Complex.normSq z) (hv : 1 - v ^ 2 = Complex.normSq z')
    (ht : t - u * v = (z * (starRingEnd ℂ) z').re) (k : ℕ) :
    Q3 k u v t = ((z * (starRingEnd ℂ) z') ^ k).re := by
  set w : ℂ := z * (starRingEnd ℂ) z' with hw
  have hnw : Complex.normSq w = (1 - u ^ 2) * (1 - v ^ 2) := by
    rw [hw, map_mul, Complex.normSq_conj, hu, hv]
  have hrec : w * w = (2 * w.re : ℝ) * w - (Complex.normSq w : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have key : ∀ k, Q3 k u v t = (w ^ k).re ∧ Q3 (k + 1) u v t = (w ^ (k + 1)).re := by
    intro k
    induction k with
    | zero => simp [Q3, ht]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h2 : w ^ (k + 2) = ((2 * w.re : ℝ) : ℂ) * w ^ (k + 1) - (Complex.normSq w : ℝ) * w ^ k := by
        have : w ^ (k + 2) = w ^ k * (w * w) := by ring
        rw [this, hrec]; ring
      show Q3 (k + 2) u v t = (w ^ (k + 2)).re
      rw [h2, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hnw, ← ih.1, ← ih.2, ← ht]
      simp only [Q3]
  exact (key k).1

lemma Q3_symm (k : ℕ) (u v t : ℝ) : Q3 k u v t = Q3 k v u t := by
  have key : ∀ n, Q3 n u v t = Q3 n v u t ∧ Q3 (n + 1) u v t = Q3 (n + 1) v u t := by
    intro n
    induction n with
    | zero => simp [Q3, mul_comm]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [Q3, ih.1, ih.2]
      ring
  exact (key k).1

/-- Orthonormal tangent frame `(e1, e2)` perpendicular to a unit vector `ξ ∈ S²`. -/
lemma exists_ortho_frame (ξ : R3) (hξ : ‖ξ‖ = 1) :
    ∃ e1 e2 : R3,
      ∀ y z : R3, ⟪y, z⟫ - ⟪ξ, y⟫ * ⟪ξ, z⟫ = ⟪e1, y⟫ * ⟪e1, z⟫ + ⟪e2, y⟫ * ⟪e2, z⟫ := by
  have hsq : ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 = 1 := by rw [← norm_sq_R3_expand, hξ]; norm_num
  have hbuild : ∀ (a0 a1 a2 b0 b1 b2 : ℝ),
      a0 * a0 + b0 * b0 = 1 - ξ 0 * ξ 0 →
      a0 * a1 + b0 * b1 = -(ξ 0 * ξ 1) →
      a0 * a2 + b0 * b2 = -(ξ 0 * ξ 2) →
      a1 * a1 + b1 * b1 = 1 - ξ 1 * ξ 1 →
      a1 * a2 + b1 * b2 = -(ξ 1 * ξ 2) →
      a2 * a2 + b2 * b2 = 1 - ξ 2 * ξ 2 →
      ∃ e1 e2 : R3,
        ∀ y z : R3, ⟪y, z⟫ - ⟪ξ, y⟫ * ⟪ξ, z⟫ = ⟪e1, y⟫ * ⟪e1, z⟫ + ⟪e2, y⟫ * ⟪e2, z⟫ := by
    intro a0 a1 a2 b0 b1 b2 h00 h01 h02 h11 h12 h22
    let e1 : R3 := WithLp.toLp 2 (fun i : Fin 3 => match i with | 0 => a0 | 1 => a1 | 2 => a2)
    let e2 : R3 := WithLp.toLp 2 (fun i : Fin 3 => match i with | 0 => b0 | 1 => b1 | 2 => b2)
    refine ⟨e1, e2, fun y z => ?_⟩
    simp only [inner_R3_expand]
    change y 0 * z 0 + y 1 * z 1 + y 2 * z 2 -
        (ξ 0 * y 0 + ξ 1 * y 1 + ξ 2 * y 2) * (ξ 0 * z 0 + ξ 1 * z 1 + ξ 2 * z 2) =
      (a0 * y 0 + a1 * y 1 + a2 * y 2) * (a0 * z 0 + a1 * z 1 + a2 * z 2) +
      (b0 * y 0 + b1 * y 1 + b2 * y 2) * (b0 * z 0 + b1 * z 1 + b2 * z 2)
    linear_combination
      -(y 0 * z 0) * h00 - (y 0 * z 1 + y 1 * z 0) * h01 - (y 0 * z 2 + y 2 * z 0) * h02
      - (y 1 * z 1) * h11 - (y 1 * z 2 + y 2 * z 1) * h12 - (y 2 * z 2) * h22
  by_cases hc : ξ 2 ^ 2 ≤ 1 / 2
  · set r := Real.sqrt (ξ 0 ^ 2 + ξ 1 ^ 2)
    have hr2 : r ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 := Real.sq_sqrt (by positivity)
    have hrpos : 0 < ξ 0 ^ 2 + ξ 1 ^ 2 := by linarith
    have hrne : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrpos)
    refine hbuild (-ξ 1 / r) (ξ 0 / r) 0 (-ξ 0 * ξ 2 / r) (-ξ 1 * ξ 2 / r) r ?_ ?_ ?_ ?_ ?_ ?_
    · field_simp; rw [hr2]; linear_combination (ξ 0 ^ 2) * hsq
    · field_simp; rw [hr2]; linear_combination (ξ 0 * ξ 1) * hsq
    · field_simp; ring
    · field_simp; rw [hr2]; linear_combination (ξ 1 ^ 2) * hsq
    · field_simp; ring
    · nlinarith [hr2, hsq]
  · set r := Real.sqrt (ξ 1 ^ 2 + ξ 2 ^ 2)
    have hr2 : r ^ 2 = ξ 1 ^ 2 + ξ 2 ^ 2 := Real.sq_sqrt (by positivity)
    have hrpos : 0 < ξ 1 ^ 2 + ξ 2 ^ 2 := by nlinarith
    have hrne : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrpos)
    refine hbuild 0 (-ξ 2 / r) (ξ 1 / r) r (-ξ 0 * ξ 1 / r) (-ξ 0 * ξ 2 / r) ?_ ?_ ?_ ?_ ?_ ?_
    · nlinarith [hr2, hsq]
    · field_simp; ring
    · field_simp; ring
    · field_simp; rw [hr2]; linear_combination (ξ 1 ^ 2) * hsq
    · field_simp; rw [hr2]; linear_combination (ξ 1 * ξ 2) * hsq
    · field_simp; rw [hr2]; linear_combination (ξ 2 ^ 2) * hsq

/-- General rank-1 Bachoc–Vallentin positivity at a single center `ξ ∈ S²` for ANY weight `g : ℝ → ℝ`. -/
theorem sum_Y3_sq_nonneg_center {n : ℕ} (k : ℕ) (ξ : R3) (hξ : ‖ξ‖ = 1)
    (x : Fin n → R3) (hx : ∀ j, ‖x j‖ = 1) (g : ℝ → ℝ) :
    0 ≤ ∑ j : Fin n, ∑ l : Fin n,
      g ⟪ξ, x j⟫ * g ⟪ξ, x l⟫ * Q3 k ⟪ξ, x j⟫ ⟪ξ, x l⟫ ⟪x j, x l⟫ := by
  obtain ⟨e1, e2, hframe⟩ := exists_ortho_frame ξ hξ
  let a : Fin n → ℝ := fun j => ⟪e1, x j⟫
  let b : Fin n → ℝ := fun j => ⟪e2, x j⟫
  let z : Fin n → ℂ := fun j => ⟨a j, b j⟩
  have hu : ∀ j, 1 - ⟪ξ, x j⟫ ^ 2 = Complex.normSq (z j) := by
    intro j
    have hf := hframe (x j) (x j)
    rw [real_inner_self_eq_norm_sq, hx j] at hf
    simp only [z, a, b, Complex.normSq_apply]
    linarith
  have ht : ∀ j l, ⟪x j, x l⟫ - ⟪ξ, x j⟫ * ⟪ξ, x l⟫ = (z j * (starRingEnd ℂ) (z l)).re := by
    intro j l
    have hf := hframe (x j) (x l)
    simp only [z, a, b, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    linarith
  have hQ : ∀ j l, Q3 k ⟪ξ, x j⟫ ⟪ξ, x l⟫ ⟪x j, x l⟫ =
      ((z j) ^ k).re * ((z l) ^ k).re + ((z j) ^ k).im * ((z l) ^ k).im := by
    intro j l
    rw [Q3_eq_re _ _ _ (z j) (z l) (hu j) (hu l) (ht j l) k]
    rw [mul_pow, Complex.mul_re, ← map_pow, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [hQ]
  have hsq : ∑ j : Fin n, ∑ l : Fin n,
      g ⟪ξ, x j⟫ * g ⟪ξ, x l⟫ * (((z j) ^ k).re * ((z l) ^ k).re + ((z j) ^ k).im * ((z l) ^ k).im) =
      (∑ j : Fin n, g ⟪ξ, x j⟫ * ((z j) ^ k).re) ^ 2 + (∑ j : Fin n, g ⟪ξ, x j⟫ * ((z j) ^ k).im) ^ 2 := by
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsq]
  positivity

/-- General rank-1 Bachoc–Vallentin positivity summed over any center subset `S ⊆ Fin n`. -/
theorem sum_Y3_sq_nonneg_finset {n : ℕ} (k : ℕ) (S : Finset (Fin n))
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (g : ℝ → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j : Fin n, ∑ l : Fin n,
      g ⟪x i, x j⟫ * g ⟪x i, x l⟫ * Q3 k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ :=
  Finset.sum_nonneg fun i _ => sum_Y3_sq_nonneg_center k (x i) (hx i) x hx g

/-- Rank-1 Cholesky Bachoc–Vallentin positivity at a SINGLE fixed center `ξ ∈ S²`. -/
theorem sum_cholesky_Y3_nonneg_center {n m : ℕ} (k : ℕ) (ξ : R3) (hξ : ‖ξ‖ = 1)
    (x : Fin n → R3) (hx : ∀ j, ‖x j‖ = 1) (w : Fin m → ℝ) :
    0 ≤ ∑ j : Fin n, ∑ l : Fin n,
      (∑ a : Fin m, w a * ⟪ξ, x j⟫ ^ (a : ℕ)) *
      (∑ b : Fin m, w b * ⟪ξ, x l⟫ ^ (b : ℕ)) *
      Q3 k ⟪ξ, x j⟫ ⟪ξ, x l⟫ ⟪x j, x l⟫ :=
  sum_Y3_sq_nonneg_center k ξ hξ x hx (fun u => ∑ a : Fin m, w a * u ^ (a : ℕ))

/-- Rank-1 Cholesky Bachoc–Vallentin positivity summed over any center subset `S ⊆ Fin n`. -/
theorem sum_cholesky_Y3_nonneg_finset {n m : ℕ} (k : ℕ) (S : Finset (Fin n))
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (w : Fin m → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j : Fin n, ∑ l : Fin n,
      (∑ a : Fin m, w a * ⟪x i, x j⟫ ^ (a : ℕ)) *
      (∑ b : Fin m, w b * ⟪x i, x l⟫ ^ (b : ℕ)) *
      Q3 k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ :=
  Finset.sum_nonneg fun i _ => sum_cholesky_Y3_nonneg_center k (x i) (hx i) x hx w

/-! ## Exact 9-point combinatorial assembly identities -/

/-- `S₃`-symmetrization of a 3-argument function. -/
noncomputable def sym3 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (f u v t + f u t v + f v u t + f v t u + f t u v + f t v u) / 6

/-- Sum over all unordered pairs `i < j` in `Fin 9`. -/
def sumPairs9 (f : Fin 9 → Fin 9 → ℝ) : ℝ :=
  ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, f i j

/-- Sum over all unordered triples `i < j < l` in `Fin 9`. -/
def sumTriples9 (f : Fin 9 → Fin 9 → Fin 9 → ℝ) : ℝ :=
  ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ∑ l ∈ Finset.Ioi j, f i j l

private lemma sum_erase_eq_ite {α : Type*} [Fintype α] [DecidableEq α] (i : α) (f : α → ℝ) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j : α, if i ≠ j then f j else 0 := by
  have heq : Finset.univ.erase i = Finset.univ.filter (fun j => i ≠ j) := by
    ext j; simp [ne_comm]
  rw [heq, Finset.sum_filter]

private lemma sum_erase2_eq_ite {α : Type*} [Fintype α] [DecidableEq α] (i j : α) (f : α → ℝ) :
    ∑ l ∈ (Finset.univ.erase i).erase j, f l = ∑ l : α, if i ≠ l ∧ j ≠ l then f l else 0 := by
  have heq : (Finset.univ.erase i).erase j = Finset.univ.filter (fun l => i ≠ l ∧ j ≠ l) := by
    ext l; simp [ne_comm, and_comm]
  rw [heq, Finset.sum_filter]

private lemma sum_Ioi_eq_ite (i : Fin 9) (f : Fin 9 → ℝ) :
    ∑ j ∈ Finset.Ioi i, f j = ∑ j : Fin 9, if i < j then f j else 0 := by
  have heq : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    ext j; simp
  rw [heq, Finset.sum_filter]

private lemma sum_Iio_eq_ite (i : Fin 9) (f : Fin 9 → ℝ) :
    ∑ j ∈ Finset.Iio i, f j = ∑ j : Fin 9, if j < i then f j else 0 := by
  have heq : Finset.Iio i = Finset.univ.filter (fun j => j < i) := by
    ext j; simp
  rw [heq, Finset.sum_filter]

/-- Exact untyped `S₃` 9-point assembly identity:
for any symmetric matrix `t : Fin 9 → Fin 9 → ℝ` with unit diagonal `t i i = 1`,
`H : ℝ → ℝ`, `e : ℝ`, `s : ℝ → ℝ → ℝ → ℝ`, defining
  `slack(u,v,t) = (H u + H v + H t)/3 - e/36 - 7*sym3 s u v t - (g u + g v + g t)/3 - s 1 1 1 / 8`
where `g x = s 1 x x + s x 1 x + s x x 1`, we have:
  `∑_{i<j} H(t i j) - e = (3/7) * ∑_{i<j<l} slack(t i j, t i l, t j l) + (1/2) * ∑_{i,j,l} s(t i j, t i l, t j l)`. -/
theorem cap_assembly_9 (t : Fin 9 → Fin 9 → ℝ)
    (ht_diag : ∀ i, t i i = 1) (ht_sym : ∀ i j, t i j = t j i)
    (H : ℝ → ℝ) (e : ℝ) (s : ℝ → ℝ → ℝ → ℝ) :
    let g : ℝ → ℝ := fun x => s 1 x x + s x 1 x + s x x 1
    let slack : ℝ → ℝ → ℝ → ℝ := fun u v w =>
      (H u + H v + H w) / 3 - e / 36 - 7 * sym3 s u v w
        - (g u + g v + g w) / 3 - s 1 1 1 / 8
    sumPairs9 (fun i j => H (t i j)) - e =
      (3 / 7 : ℝ) * sumTriples9 (fun i j l => slack (t i j) (t i l) (t j l))
      + (1 / 2 : ℝ) * ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, s (t i j) (t i l) (t j l) := by
  intro g slack
  have h1 : ∀ f : Fin 9 → Fin 9 → ℝ, (∀ i j, f i j = f j i) →
      ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, f i j = 2 * sumPairs9 f := by
    intro f hf
    unfold sumPairs9
    have h_eq : ∀ i : Fin 9, ∑ j ∈ Finset.univ.erase i, f i j =
        ∑ j ∈ Finset.Ioi i, f i j + ∑ j ∈ Finset.Iio i, f i j := by
      intro i
      rw [← Finset.sum_union]
      · congr 1; ext j
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
          Finset.mem_Ioi, Finset.mem_Iio]
        exact ⟨fun h => lt_or_gt_of_ne h.symm, fun h => h.elim ne_of_gt ne_of_lt⟩
      · rw [Finset.disjoint_left]; intro j hj1 hj2; simp at hj1 hj2; omega
    simp_rw [h_eq, Finset.sum_add_distrib]
    have h_flip : ∑ i : Fin 9, ∑ j ∈ Finset.Iio i, f i j =
        ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, f i j := by
      simp_rw [sum_Iio_eq_ite, sum_Ioi_eq_ite]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      by_cases h : j < i
      · simp [h, hf j i]
      · simp [h]
    linarith
  have hdist_eq : ∀ F : Fin 9 → Fin 9 → Fin 9 → ℝ,
      ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j, F i j l =
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if i ≠ j ∧ i ≠ l ∧ j ≠ l then F i j l else 0 := by
    intro F
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_erase_eq_ite]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ne_eq, not_false_eq_true, ↓reduceIte, sum_erase2_eq_ite]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hil : i = l <;> by_cases hjl : j = l <;> simp [hil, hjl]
  have h2 : ∀ F : Fin 9 → Fin 9 → Fin 9 → ℝ,
      (∀ i j l, F i j l = F i l j) → (∀ i j l, F i j l = F j i l) →
      ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j, F i j l =
        6 * sumTriples9 F := by
    intro F hF23 hF12
    have hF13 : ∀ i j l, F i j l = F l j i := fun i j l => by
      rw [hF12, hF23, hF12]
    have hRHS : sumTriples9 F =
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9,
          if i < j ∧ j < l then F i j l else 0 := by
      unfold sumTriples9
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_Ioi_eq_ite]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j
      · simp only [hij, ↓reduceIte, sum_Ioi_eq_ite]
        refine Finset.sum_congr rfl fun l _ => by simp
      · simp [hij]
    rw [hdist_eq, hRHS]
    have hpart : ∀ i j l : Fin 9,
        (if i ≠ j ∧ i ≠ l ∧ j ≠ l then F i j l else 0) =
          (if i < j ∧ j < l then F i j l else 0)
          + (if i < l ∧ l < j then F i j l else 0)
          + (if j < i ∧ i < l then F i j l else 0)
          + (if j < l ∧ l < i then F i j l else 0)
          + (if l < i ∧ i < j then F i j l else 0)
          + (if l < j ∧ j < i then F i j l else 0) := by
      intro i j l
      by_cases h1 : i < j <;> by_cases h2 : j < l <;> by_cases h3 : i < l <;>
        by_cases h4 : j < i <;> by_cases h5 : l < j <;> by_cases h6 : l < i <;>
        simp only [h1, h2, h3, h4, h5, h6, and_true, and_false, ↓reduceIte, add_zero, zero_add] <;>
        first
        | omega
        | (have : i ≠ j ∧ i ≠ l ∧ j ≠ l := by omega
           simp [this])
        | (have : ¬ (i ≠ j ∧ i ≠ l ∧ j ≠ l) := by omega
           simp [this])
    have hsum_part :
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then F i j l else 0) =
        (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if i < j ∧ j < l then F i j l else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if i < l ∧ l < j then F i j l else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if j < i ∧ i < l then F i j l else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if j < l ∧ l < i then F i j l else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if l < i ∧ i < j then F i j l else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if l < j ∧ j < i then F i j l else 0) := by
      trans (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9,
        ((if i < j ∧ j < l then F i j l else 0)
          + (if i < l ∧ l < j then F i j l else 0)
          + (if j < i ∧ i < l then F i j l else 0)
          + (if j < l ∧ l < i then F i j l else 0)
          + (if l < i ∧ i < j then F i j l else 0)
          + (if l < j ∧ j < i then F i j l else 0)))
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun l _ => hpart i j l
      · simp only [Finset.sum_add_distrib]
    rw [hsum_part]
    have p1 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i < l ∧ l < j then F i j l else 0) =
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i < j ∧ j < l then F i j l else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hF23]
    have p2 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if j < i ∧ i < l then F i j l else 0) =
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i < j ∧ j < l then F i j l else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hF12]
    have p3 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if j < l ∧ l < i then F i j l else 0) =
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i < j ∧ j < l then F i j l else 0) := by
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hF12, hF23]
    have p4 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if l < i ∧ i < j then F i j l else 0) =
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i < j ∧ j < l then F i j l else 0) := by
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hF23, hF12]
    have p5 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if l < j ∧ j < i then F i j l else 0) =
        ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i < j ∧ j < l then F i j l else 0) := by
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hF13]
    linarith
  have hsplit : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, s (t i j) (t i l) (t j l) =
      9 * s 1 1 1
      + 2 * sumPairs9 (fun i j => g (t i j))
      + 6 * sumTriples9 (fun i j l => sym3 s (t i j) (t i l) (t j l)) := by
    have hcell : ∀ i j l : Fin 9,
        s (t i j) (t i l) (t j l) =
          (if i = j ∧ j = l then s 1 1 1 else 0)
          + (if i = j ∧ j ≠ l then s 1 (t i l) (t i l) else 0)
          + (if i = l ∧ i ≠ j then s (t i j) 1 (t i j) else 0)
          + (if j = l ∧ i ≠ j then s (t i j) (t i j) 1 else 0)
          + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then s (t i j) (t i l) (t j l) else 0) := by
      intro i j l
      by_cases hij : i = j <;> by_cases hil : i = l <;> by_cases hjl : j = l
      · subst hij; subst hil; simp [ht_diag]
      · subst hij; subst hil; exact absurd rfl hjl
      · subst hij; simp [ht_diag, hjl]
      · subst hij; simp [ht_diag, hjl]
      · subst hil; exact absurd hjl.symm hij
      · subst hil; simp [ht_diag, hij, hjl, ht_sym j i]
      · subst hjl; simp [ht_diag, hij]
      · simp [hij, hil, hjl]
    have hsum_cell : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, s (t i j) (t i l) (t j l) =
        (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if i = j ∧ j = l then s 1 1 1 else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if i = j ∧ j ≠ l then s 1 (t i l) (t i l) else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if i = l ∧ i ≠ j then s (t i j) 1 (t i j) else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if j = l ∧ i ≠ j then s (t i j) (t i j) 1 else 0)
        + (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, if i ≠ j ∧ i ≠ l ∧ j ≠ l then s (t i j) (t i l) (t j l) else 0) := by
      trans (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9,
        ((if i = j ∧ j = l then s 1 1 1 else 0)
          + (if i = j ∧ j ≠ l then s 1 (t i l) (t i l) else 0)
          + (if i = l ∧ i ≠ j then s (t i j) 1 (t i j) else 0)
          + (if j = l ∧ i ≠ j then s (t i j) (t i j) 1 else 0)
          + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then s (t i j) (t i l) (t j l) else 0)))
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun l _ => hcell i j l
      · simp only [Finset.sum_add_distrib]
    rw [hsum_cell]
    have hA : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i = j ∧ j = l then s 1 1 1 else 0) = 9 * s 1 1 1 := by
      have hinner : ∀ i : Fin 9, (∑ j : Fin 9, ∑ l : Fin 9, if i = j ∧ j = l then s 1 1 1 else 0) = s 1 1 1 := by
        intro i
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single i]
          · simp
          · intro l _ hl; simp [Ne.symm hl]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro j _ hj; refine Finset.sum_eq_zero fun l _ => by simp [Ne.symm hj]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hinner]
      simp [Finset.sum_const, Finset.card_univ]
    have hB1 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i = j ∧ j ≠ l then s 1 (t i l) (t i l) else 0) =
        2 * sumPairs9 (fun i j => s 1 (t i j) (t i j)) := by
      rw [← h1 _ (fun i j => by rw [ht_sym])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_ite]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hil : i = l
      · subst hil
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hij : i = j <;> simp [hij, Ne.symm]
      · simp only [hil, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [Finset.sum_eq_single i]
        · simp [hil]
        · intro j _ hj; simp [Ne.symm hj]
        · intro h; exact absurd (Finset.mem_univ _) h
    have hB2 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i = l ∧ i ≠ j then s (t i j) 1 (t i j) else 0) =
        2 * sumPairs9 (fun i j => s (t i j) 1 (t i j)) := by
      rw [← h1 _ (fun i j => by rw [ht_sym])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_ite]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp
      · simp only [hij, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [Finset.sum_eq_single i]
        · simp
        · intro l _ hl; simp [Ne.symm hl]
        · intro h; exact absurd (Finset.mem_univ _) h
    have hB3 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if j = l ∧ i ≠ j then s (t i j) (t i j) 1 else 0) =
        2 * sumPairs9 (fun i j => s (t i j) (t i j) 1) := by
      rw [← h1 _ (fun i j => by rw [ht_sym])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_ite]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp
      · simp only [hij, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hl; simp [Ne.symm hl]
        · intro h; exact absurd (Finset.mem_univ _) h
    have hDist : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9,
        (if i ≠ j ∧ i ≠ l ∧ j ≠ l then s (t i j) (t i l) (t j l) else 0) =
        6 * sumTriples9 (fun i j l => sym3 s (t i j) (t i l) (t j l)) := by
      have hsym_eq : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9,
          (if i ≠ j ∧ i ≠ l ∧ j ≠ l then s (t i j) (t i l) (t j l) else 0) =
          ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9,
          (if i ≠ j ∧ i ≠ l ∧ j ≠ l then sym3 s (t i j) (t i l) (t j l) else 0) := by
        have havg : ∀ f : Fin 9 → Fin 9 → Fin 9 → ℝ,
            ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) =
            ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then
              (f i j l + f i l j + f j i l + f j l i + f l i j + f l j i) / 6 else 0) := by
          intro f
          have e12 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j i l else 0) =
              ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) := by
            rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
            split_ifs with ha hb hc
            · rfl
            · exfalso; exact hb ⟨ha.1.symm, ha.2.2, ha.2.1⟩
            · exfalso; exact ha ⟨hc.1.symm, hc.2.2, hc.2.1⟩
            · rfl
          have e23 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i l j else 0) =
              ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
            split_ifs with ha hb hc
            · rfl
            · exfalso; exact hb ⟨ha.2.1, ha.1, ha.2.2.symm⟩
            · exfalso; exact ha ⟨hc.2.1, hc.1, hc.2.2.symm⟩
            · rfl
          have e123 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0) =
              ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) := by
            rw [Finset.sum_comm]; conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
            split_ifs with ha hb hc
            · rfl
            · exfalso; exact hb ⟨ha.2.2, ha.1.symm, ha.2.1.symm⟩
            · exfalso; exact ha ⟨hc.2.1.symm, hc.2.2.symm, hc.1⟩
            · rfl
          have e132 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f l i j else 0) =
              ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) := by
            conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
            split_ifs with ha hb hc
            · rfl
            · exfalso; exact hb ⟨ha.2.1.symm, ha.2.2.symm, ha.1⟩
            · exfalso; exact ha ⟨hc.2.2, hc.1.symm, hc.2.1.symm⟩
            · rfl
          have e13 : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f l j i else 0) =
              ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) := by
            conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
            split_ifs with ha hb hc
            · rfl
            · exfalso; exact hb ⟨ha.2.2.symm, ha.2.1.symm, ha.1.symm⟩
            · exfalso; exact ha ⟨hc.2.2.symm, hc.2.1.symm, hc.1.symm⟩
            · rfl
          have hite : ∀ i j l : Fin 9,
              (if i ≠ j ∧ i ≠ l ∧ j ≠ l then (f i j l + f i l j + f j i l + f j l i + f l i j + f l j i) / 6 else 0) =
              ((if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i l j else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j i l else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f l i j else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f l j i else 0)) / 6 := by
            intro i j l; split_ifs <;> ring
          trans (∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9,
              ((if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i l j else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j i l else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f l i j else 0)
              + (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f l j i else 0)) / 6)
          · simp only [← Finset.sum_div, Finset.sum_add_distrib]
            linarith
          · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun l _ => (hite i j l).symm
        rw [havg (fun i j l => s (t i j) (t i l) (t j l))]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        split_ifs
        · unfold sym3; simp only [ht_sym j i, ht_sym l i, ht_sym l j]; ring
        · rfl
      rw [hsym_eq, ← hdist_eq]
      exact h2 (fun i j l => sym3 s (t i j) (t i l) (t j l))
        (fun i j l => by unfold sym3; simp only [ht_sym l j]; ring)
        (fun i j l => by unfold sym3; simp only [ht_sym j i]; ring)
    have hgsum : sumPairs9 (fun i j => g (t i j)) =
        sumPairs9 (fun i j => s 1 (t i j) (t i j))
        + sumPairs9 (fun i j => s (t i j) 1 (t i j))
        + sumPairs9 (fun i j => s (t i j) (t i j) 1) := by
      simp only [sumPairs9, g, Finset.sum_add_distrib]
    linarith
  have hcard_erase2 : ∀ i j : Fin 9, j ≠ i → ((Finset.univ.erase i).erase j).card = 7 := by
    intro i j hji
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hcard_erase1 : ∀ i : Fin 9, (Finset.univ.erase i).card = 8 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hConst6 : 6 * sumTriples9 (fun _ _ _ => (1 : ℝ)) = 504 := by
    have h6 := h2 (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    rw [← h6]
    trans (∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, (7 : ℝ))
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.sum_const, hcard_erase2 i j (Finset.mem_erase.mp hj).1]; norm_num
    · trans (∑ _i : Fin 9, (56 : ℝ))
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, hcard_erase1 i]; norm_num
      · simp; norm_num
  have hConst : sumTriples9 (fun _ _ _ => (1 : ℝ)) = 84 := by linarith
  have hEdge : ∀ f : ℝ → ℝ,
      sumTriples9 (fun i j l => f (t i j) + f (t i l) + f (t j l)) =
        7 * sumPairs9 (fun i j => f (t i j)) := by
    intro f
    have h6 := h2 (fun i j l => f (t i j) + f (t i l) + f (t j l))
      (fun i j l => by rw [ht_sym l j]; ring)
      (fun i j l => by rw [ht_sym j i]; ring)
    have hsum1 : ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j, f (t i j) =
        14 * sumPairs9 (fun i j => f (t i j)) := by
      have hinner : ∀ i : Fin 9, ∀ j ∈ Finset.univ.erase i,
          ∑ _l ∈ (Finset.univ.erase i).erase j, f (t i j) = 7 * f (t i j) := by
        intro i j hj
        rw [Finset.sum_const, hcard_erase2 i j (Finset.mem_erase.mp hj).1]; simp
      trans (∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, 7 * f (t i j))
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => hinner i j hj
      · simp_rw [← Finset.mul_sum]
        rw [h1 (fun i j => f (t i j)) (fun i j => by rw [ht_sym])]
        ring
    have hsum_eq : ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j,
        (f (t i j) + f (t i l) + f (t j l)) =
        3 * ∑ i : Fin 9, ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j, f (t i j) := by
      simp_rw [Finset.sum_add_distrib, hdist_eq]
      have e_il : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f (t i l) else 0) =
          ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f (t i j) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        split_ifs with ha hb hc
        · rfl
        · exfalso; exact hb ⟨ha.2.1, ha.1, ha.2.2.symm⟩
        · exfalso; exact ha ⟨hc.2.1, hc.1, hc.2.2.symm⟩
        · rfl
      have e_jl : ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f (t j l) else 0) =
          ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f (t i j) else 0) := by
        rw [Finset.sum_comm]; conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
        split_ifs with ha hb hc
        · rfl
        · exfalso; exact hb ⟨ha.2.2, ha.1.symm, ha.2.1.symm⟩
        · exfalso; exact ha ⟨hc.2.1.symm, hc.2.2.symm, hc.1⟩
        · rfl
      linarith
    linarith
  have hConstMul : ∀ c : ℝ, sumTriples9 (fun _ _ _ => c) = c * sumTriples9 (fun _ _ _ => (1 : ℝ)) := by
    intro c
    unfold sumTriples9
    simp only [Finset.mul_sum, mul_one]
  have hSlack : sumTriples9 (fun i j l => slack (t i j) (t i l) (t j l)) =
      sumTriples9 (fun i j l => H (t i j) + H (t i l) + H (t j l)) / 3
      - (e / 36) * sumTriples9 (fun _ _ _ => (1 : ℝ))
      - 7 * sumTriples9 (fun i j l => sym3 s (t i j) (t i l) (t j l))
      - sumTriples9 (fun i j l => g (t i j) + g (t i l) + g (t j l)) / 3
      - (s 1 1 1 / 8) * sumTriples9 (fun _ _ _ => (1 : ℝ)) := by
    rw [← hConstMul (e / 36), ← hConstMul (s 1 1 1 / 8)]
    unfold sumTriples9
    simp only [slack, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.mul_sum]
  rw [hSlack, hEdge H, hEdge g, hConst, hsplit]
  ring

/-- Pole subset `P = {0, 1}` in `Fin 9`. -/
def poleSet : Finset (Fin 9) := {0, 1}

/-- Ring subset `R = {2, 3, 4, 5, 6, 7, 8}` in `Fin 9`. -/
def ringSet : Finset (Fin 9) := {2, 3, 4, 5, 6, 7, 8}

/-- Helper: `Fin 9` partitions disjointly into `poleSet ∪ ringSet`. -/
lemma poleSet_union_ringSet : poleSet ∪ ringSet = Finset.univ := by decide

lemma disjoint_poleSet_ringSet : Disjoint poleSet ringSet := by decide

lemma sum_univ_pole_ring (f : Fin 9 → ℝ) :
    ∑ i : Fin 9, f i = ∑ p ∈ poleSet, f p + ∑ r ∈ ringSet, f r := by
  rw [← poleSet_union_ringSet, Finset.sum_union disjoint_poleSet_ringSet]

private lemma card_ringSet_split :
    ∀ r ∈ ringSet, (ringSet.filter (r < ·)).card + (ringSet.filter (· < r)).card = 6 := by
  decide

private lemma card_ringSet_triple_split :
    ∀ r1 ∈ ringSet, ∀ r2 ∈ ringSet.filter (r1 < ·),
      (ringSet.filter (r2 < ·)).card + (ringSet.filter (fun r => r1 < r ∧ r < r2)).card
        + (ringSet.filter (· < r1)).card = 5 := by
  decide

private lemma Ioi_eq_ringSet_filter :
    ∀ r1 ∈ ringSet, Finset.Ioi r1 = ringSet.filter (r1 < ·) := by
  decide

/-- Exact `(2, 7)` typed pole-ring 9-point assembly identity matching `sym_strip_sdpa.py`:
For symmetric `t : Fin 9 → Fin 9 → ℝ` with `t i i = 1`, pair minorants `h_A, h_B, h_C`,
splitting polynomials `psi_Ba, psi_Cb`, constants `e, c_a, c_b, c_g`, and `(u↔v)`-symmetric
harmonic triple polynomials `s_P, s_R` (`s_P u v w = s_P v u w`, `s_R u v w = s_R v u w`),
if `e + 2 * s_P 1 1 1 + 7 * s_R 1 1 1 = 7 * c_a + 42 * c_b + 35 * c_g`, then:
  `h_A (t 0 1) + ∑_{p∈P, r∈R} h_B (t p r) + ∑_{r1<r2∈R} h_C (t r1 r2) - e`
  `= ∑_{r∈R} lam_A(t 0 1, t 0 r, t 1 r)`
  `+ ∑_{p∈P, r1<r2∈R} lam_B(t p r1, t p r2, t r1 r2)`
  `+ ∑_{r1<r2<r3∈R} lam_G(t r1 r2, t r1 r3, t r2 r3)`
  `+ ∑_{i∈P, j, l} s_P(t i j, t i l, t j l) + ∑_{i∈R, j, l} s_R(t i j, t i l, t j l)`. -/
theorem slab_assembly_9 (t : Fin 9 → Fin 9 → ℝ)
    (ht_diag : ∀ i, t i i = 1) (ht_sym : ∀ i j, t i j = t j i)
    (h_A h_B h_C psi_Ba psi_Cb : ℝ → ℝ)
    (e c_a c_b c_g : ℝ)
    (s_P s_R : ℝ → ℝ → ℝ → ℝ)
    (hsP_uv : ∀ u v w, s_P u v w = s_P v u w)
    (hsR_uv : ∀ u v w, s_R u v w = s_R v u w)
    (hnorm : e + 2 * s_P 1 1 1 + 7 * s_R 1 1 1 = 7 * c_a + 42 * c_b + 35 * c_g) :
    let gP : ℝ → ℝ := fun x => s_P 1 x x + s_P x 1 x + s_P x x 1
    let gR : ℝ → ℝ := fun x => s_R 1 x x + s_R x 1 x + s_R x x 1
    let lam_A : ℝ → ℝ → ℝ → ℝ := fun u v w =>
      h_A u / 7 + psi_Ba v + psi_Ba w - c_a
      - 2 * gP u / 7 - 2 * (s_P u v w + s_P u w v) - 2 * s_R v w u
    let lam_B : ℝ → ℝ → ℝ → ℝ := fun u v w =>
      (h_B u - psi_Ba u + h_B v - psi_Ba v) / 6 + psi_Cb w - c_b
      - (gP u + gP v + gR u + gR v) / 6 - 2 * s_P u v w - 2 * (s_R u w v + s_R v w u)
    let lam_G : ℝ → ℝ → ℝ → ℝ := fun u v w =>
      (h_C u - 2 * psi_Cb u + h_C v - 2 * psi_Cb v + h_C w - 2 * psi_Cb w) / 5 - c_g
      - 2 * (gR u + gR v + gR w) / 5 - 2 * (s_R u v w + s_R u w v + s_R v w u)
    (h_A (t 0 1)
      + ∑ p ∈ poleSet, ∑ r ∈ ringSet, h_B (t p r)
      + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), h_C (t r1 r2) - e) =
      (∑ r ∈ ringSet, lam_A (t 0 1) (t 0 r) (t 1 r))
      + (∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
          lam_B (t p r1) (t p r2) (t r1 r2))
      + (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
          lam_G (t r1 r2) (t r1 r3) (t r2 r3))
      + (∑ i ∈ poleSet, ∑ j : Fin 9, ∑ l : Fin 9, s_P (t i j) (t i l) (t j l))
      + (∑ i ∈ ringSet, ∑ j : Fin 9, ∑ l : Fin 9, s_R (t i j) (t i l) (t j l)) := by
  intro gP gR lam_A lam_B lam_G
  have hSP_split :
      ∑ i ∈ poleSet, ∑ j : Fin 9, ∑ l : Fin 9, s_P (t i j) (t i l) (t j l) =
      2 * s_P 1 1 1 + 2 * gP (t 0 1)
      + ∑ p ∈ poleSet, ∑ r ∈ ringSet, gP (t p r)
      + ∑ r ∈ ringSet, 2 * (s_P (t 0 1) (t 0 r) (t 1 r) + s_P (t 0 1) (t 1 r) (t 0 r))
      + ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_P (t p r1) (t p r2) (t r1 r2) := by
    simp only [sum_univ_pole_ring, Finset.sum_add_distrib]
    have hP_sum : ∀ f : Fin 9 → ℝ, ∑ p ∈ poleSet, f p = f 0 + f 1 := by
      intro f; simp [poleSet]
    simp only [hP_sum, ht_diag, ht_sym 1 0, gP]
    have hRR : ∀ p : Fin 9,
        ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, s_P (t p r1) (t p r2) (t r1 r2) =
        ∑ r ∈ ringSet, s_P (t p r) (t p r) 1
        + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_P (t p r1) (t p r2) (t r1 r2) := by
      intro p
      have hcell : ∀ r1 r2 : Fin 9,
          s_P (t p r1) (t p r2) (t r1 r2) =
            (if r1 = r2 then s_P (t p r1) (t p r1) 1 else 0)
            + (if r1 < r2 then s_P (t p r1) (t p r2) (t r1 r2) else 0)
            + (if r2 < r1 then s_P (t p r1) (t p r2) (t r1 r2) else 0) := by
        intro r1 r2
        rcases lt_trichotomy r1 r2 with h | rfl | h
        · simp [h, ne_of_lt h, not_lt.mpr (le_of_lt h)]
        · simp [ht_diag]
        · simp [h, ne_of_gt h, not_lt.mpr (le_of_lt h)]
      have hsum_c : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, s_P (t p r1) (t p r2) (t r1 r2) =
          (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, if r1 = r2 then s_P (t p r1) (t p r1) 1 else 0)
          + (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, if r1 < r2 then s_P (t p r1) (t p r2) (t r1 r2) else 0)
          + (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, if r2 < r1 then s_P (t p r1) (t p r2) (t r1 r2) else 0) := by
        trans (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet,
          ((if r1 = r2 then s_P (t p r1) (t p r1) 1 else 0)
            + (if r1 < r2 then s_P (t p r1) (t p r2) (t r1 r2) else 0)
            + (if r2 < r1 then s_P (t p r1) (t p r2) (t r1 r2) else 0)))
        · exact Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => hcell r1 r2
        · simp only [Finset.sum_add_distrib]
      rw [hsum_c]
      have hD : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, (if r1 = r2 then s_P (t p r1) (t p r1) 1 else 0) =
          ∑ r ∈ ringSet, s_P (t p r) (t p r) 1 := by
        refine Finset.sum_congr rfl fun r1 hr1 => ?_
        simp [Finset.sum_ite_eq, hr1]
      have hU : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, (if r1 < r2 then s_P (t p r1) (t p r2) (t r1 r2) else 0) =
          ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), s_P (t p r1) (t p r2) (t r1 r2) := by
        refine Finset.sum_congr rfl fun r1 _ => (Finset.sum_filter _ _).symm
      have hL : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, (if r2 < r1 then s_P (t p r1) (t p r2) (t r1 r2) else 0) =
          ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), s_P (t p r1) (t p r2) (t r1 r2) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r2 _ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr rfl fun r1 _ => ?_
        rw [hsP_uv, ht_sym r1 r2]
      simp_rw [← Finset.mul_sum]
      linarith
    rw [hRR 0, hRR 1]
    have hsym_p0 : ∀ r : Fin 9, s_P (t 0 r) (t 0 1) (t r 1) = s_P (t 0 1) (t 0 r) (t 1 r) := by
      intro r; rw [hsP_uv, ht_sym r 1]
    have hsym_p1 : ∀ r : Fin 9, s_P (t 1 r) (t 0 1) (t r 0) = s_P (t 0 1) (t 1 r) (t 0 r) := by
      intro r; rw [hsP_uv, ht_sym r 0]
    have hrt1 : ∀ r : Fin 9, t r 1 = t 1 r := fun r => ht_sym r 1
    have hrt0 : ∀ r : Fin 9, t r 0 = t 0 r := fun r => ht_sym r 0
    simp_rw [hsym_p0, hsym_p1, hrt1, hrt0, ← Finset.mul_sum, Finset.sum_add_distrib]
    rw [hsP_uv (t 0 1) 1 (t 0 1)]
    ring
  have hSR_split :
      ∑ i ∈ ringSet, ∑ j : Fin 9, ∑ l : Fin 9, s_R (t i j) (t i l) (t j l) =
      7 * s_R 1 1 1
      + ∑ p ∈ poleSet, ∑ r ∈ ringSet, gR (t p r)
      + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * gR (t r1 r2)
      + ∑ r ∈ ringSet, 2 * s_R (t 0 r) (t 1 r) (t 0 1)
      + ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
          2 * (s_R (t p r1) (t r1 r2) (t p r2) + s_R (t p r2) (t r1 r2) (t p r1))
      + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
          2 * (s_R (t r1 r2) (t r1 r3) (t r2 r3) + s_R (t r1 r2) (t r2 r3) (t r1 r3)
                + s_R (t r1 r3) (t r2 r3) (t r1 r2)) := by
    simp only [sum_univ_pole_ring, Finset.sum_add_distrib]
    have hP_sum : ∀ f : Fin 9 → ℝ, ∑ p ∈ poleSet, f p = f 0 + f 1 := by intro f; simp [poleSet]
    have hRRR :
        ∑ r ∈ ringSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, s_R (t r r1) (t r r2) (t r1 r2) =
        7 * s_R 1 1 1
        + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * gR (t r1 r2)
        + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
            2 * (s_R (t r1 r2) (t r1 r3) (t r2 r3) + s_R (t r1 r2) (t r2 r3) (t r1 r3)
                  + s_R (t r1 r3) (t r2 r3) (t r1 r2)) := by
      have hcell : ∀ a b c : Fin 9,
          s_R (t a b) (t a c) (t b c) =
            (if a = b ∧ b = c then s_R 1 1 1 else 0)
            + (if a = b ∧ b ≠ c then s_R 1 (t a c) (t a c) else 0)
            + (if a = c ∧ a ≠ b then s_R (t a b) 1 (t a b) else 0)
            + (if b = c ∧ a ≠ b then s_R (t a b) (t a b) 1 else 0)
            + (if a ≠ b ∧ a ≠ c ∧ b ≠ c then s_R (t a b) (t a c) (t b c) else 0) := by
        intro a b c
        by_cases h1 : a = b <;> by_cases h2 : a = c <;> by_cases h3 : b = c
        · subst h1; subst h2; simp [ht_diag]
        · subst h1; subst h2; exact absurd rfl h3
        · subst h1; simp [ht_diag, h3]
        · subst h1; simp [ht_diag, h3]
        · subst h2; exact absurd h3.symm h1
        · subst h2; simp [ht_diag, h1, h3, ht_sym b a]
        · subst h3; simp [ht_diag, h1]
        · simp [h1, h2, h3]
      have hsum_c : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, s_R (t a b) (t a c) (t b c) =
          (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if a = b ∧ b = c then s_R 1 1 1 else 0)
          + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if a = b ∧ b ≠ c then s_R 1 (t a c) (t a c) else 0)
          + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if a = c ∧ a ≠ b then s_R (t a b) 1 (t a b) else 0)
          + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if b = c ∧ a ≠ b then s_R (t a b) (t a b) 1 else 0)
          + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if a ≠ b ∧ a ≠ c ∧ b ≠ c then s_R (t a b) (t a c) (t b c) else 0) := by
        trans (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
          ((if a = b ∧ b = c then s_R 1 1 1 else 0)
            + (if a = b ∧ b ≠ c then s_R 1 (t a c) (t a c) else 0)
            + (if a = c ∧ a ≠ b then s_R (t a b) 1 (t a b) else 0)
            + (if b = c ∧ a ≠ b then s_R (t a b) (t a b) 1 else 0)
            + (if a ≠ b ∧ a ≠ c ∧ b ≠ c then s_R (t a b) (t a c) (t b c) else 0)))
        · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => hcell a b c
        · simp only [Finset.sum_add_distrib]
      rw [hsum_c]
      have hA : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
          (if a = b ∧ b = c then s_R 1 1 1 else 0) = 7 * s_R 1 1 1 := by
        have hcardR : ringSet.card = 7 := by decide
        trans (∑ a ∈ ringSet, s_R 1 1 1)
        · refine Finset.sum_congr rfl fun a ha => ?_
          trans (∑ b ∈ ringSet, if a = b then s_R 1 1 1 else 0)
          · refine Finset.sum_congr rfl fun b hb => by by_cases hab : a = b <;> simp [hab, hb]
          · simp [Finset.sum_ite_eq, ha]
        · rw [Finset.sum_const, hcardR]; norm_num
      have hpair : ∀ F : Fin 9 → Fin 9 → ℝ, (∀ x y, F x y = F y x) →
          ∑ a ∈ ringSet, ∑ b ∈ ringSet, (if a ≠ b then F a b else 0) =
          ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * F r1 r2 := by
        intro F hF
        have hsp : ∀ a b : Fin 9, (if a ≠ b then F a b else 0) =
            (if a < b then F a b else 0) + (if b < a then F a b else 0) := by
          intro a b
          rcases lt_trichotomy a b with h | rfl | h
          · simp [h, ne_of_lt h, not_lt.mpr (le_of_lt h)]
          · simp
          · simp [h, ne_of_gt h, not_lt.mpr (le_of_lt h)]
        have hsum_sp : ∑ a ∈ ringSet, ∑ b ∈ ringSet, (if a ≠ b then F a b else 0) =
            (∑ a ∈ ringSet, ∑ b ∈ ringSet, if a < b then F a b else 0)
            + (∑ a ∈ ringSet, ∑ b ∈ ringSet, if b < a then F a b else 0) := by
          trans (∑ a ∈ ringSet, ∑ b ∈ ringSet,
            ((if a < b then F a b else 0) + (if b < a then F a b else 0)))
          · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsp a b
          · simp only [Finset.sum_add_distrib]
        rw [hsum_sp]
        have h1' : ∑ a ∈ ringSet, ∑ b ∈ ringSet, (if a < b then F a b else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), F r1 r2 :=
          Finset.sum_congr rfl fun r1 _ => (Finset.sum_filter _ _).symm
        have h2' : ∑ a ∈ ringSet, ∑ b ∈ ringSet, (if b < a then F a b else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), F r1 r2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r1 _ => ?_
          rw [← Finset.sum_filter]
          exact Finset.sum_congr rfl fun r2 _ => hF r2 r1
        simp_rw [← Finset.mul_sum]; linarith
      have hB1 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
          (if a = b ∧ b ≠ c then s_R 1 (t a c) (t a c) else 0) =
          ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_R 1 (t r1 r2) (t r1 r2) := by
        rw [← hpair (fun x y => s_R 1 (t x y) (t x y)) (fun x y => by rw [ht_sym])]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c hc => ?_
        by_cases hac : a = c
        · subst hac
          simp only [ne_eq, not_true_eq_false, ↓reduceIte]
          refine Finset.sum_eq_zero fun b _ => ?_
          by_cases hab : a = b <;> simp [hab, Ne.symm]
        · simp only [hac, ne_eq, not_false_eq_true, ↓reduceIte]
          rw [Finset.sum_eq_single a]
          · simp [hac]
          · intro b _ hb; simp [Ne.symm hb]
          · intro h; exact absurd ha h
      have hB2 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
          (if a = c ∧ a ≠ b then s_R (t a b) 1 (t a b) else 0) =
          ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_R (t r1 r2) 1 (t r1 r2) := by
        rw [← hpair (fun x y => s_R (t x y) 1 (t x y)) (fun x y => by rw [ht_sym])]
        refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
        by_cases hab : a = b
        · subst hab; simp
        · simp only [hab, ne_eq, not_false_eq_true, ↓reduceIte]
          rw [Finset.sum_eq_single a]
          · simp
          · intro c _ hc; simp [Ne.symm hc]
          · intro h; exact absurd ha h
      have hB3 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
          (if b = c ∧ a ≠ b then s_R (t a b) (t a b) 1 else 0) =
          ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_R (t r1 r2) (t r1 r2) 1 := by
        rw [← hpair (fun x y => s_R (t x y) (t x y) 1) (fun x y => by rw [ht_sym])]
        refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
        by_cases hab : a = b
        · subst hab; simp
        · simp only [hab, ne_eq, not_false_eq_true, ↓reduceIte]
          rw [Finset.sum_eq_single b]
          · simp
          · intro c _ hc; simp [Ne.symm hc]
          · intro h; exact absurd hb h
      have hDist : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
          (if a ≠ b ∧ a ≠ c ∧ b ≠ c then s_R (t a b) (t a c) (t b c) else 0) =
          ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
            2 * (s_R (t r1 r2) (t r1 r3) (t r2 r3) + s_R (t r1 r2) (t r2 r3) (t r1 r3)
                  + s_R (t r1 r3) (t r2 r3) (t r1 r2)) := by
        have hpart : ∀ a b c : Fin 9,
            (if a ≠ b ∧ a ≠ c ∧ b ≠ c then s_R (t a b) (t a c) (t b c) else 0) =
              (if a < b ∧ b < c then s_R (t a b) (t a c) (t b c) else 0)
              + (if a < c ∧ c < b then s_R (t a b) (t a c) (t b c) else 0)
              + (if b < a ∧ a < c then s_R (t a b) (t a c) (t b c) else 0)
              + (if b < c ∧ c < a then s_R (t a b) (t a c) (t b c) else 0)
              + (if c < a ∧ a < b then s_R (t a b) (t a c) (t b c) else 0)
              + (if c < b ∧ b < a then s_R (t a b) (t a c) (t b c) else 0) := by
          intro a b c
          by_cases h1 : a < b <;> by_cases h2 : b < c <;> by_cases h3 : a < c <;>
            by_cases h4 : b < a <;> by_cases h5 : c < b <;> by_cases h6 : c < a <;>
            simp only [h1, h2, h3, h4, h5, h6, and_true, and_false, ↓reduceIte, add_zero, zero_add] <;>
            first
            | omega
            | (have : a ≠ b ∧ a ≠ c ∧ b ≠ c := by omega
               simp [this])
            | (have : ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c) := by omega
               simp [this])
        have hsum_p : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
            (if a ≠ b ∧ a ≠ c ∧ b ≠ c then s_R (t a b) (t a c) (t b c) else 0) =
            (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if a < b ∧ b < c then s_R (t a b) (t a c) (t b c) else 0)
            + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if a < c ∧ c < b then s_R (t a b) (t a c) (t b c) else 0)
            + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if b < a ∧ a < c then s_R (t a b) (t a c) (t b c) else 0)
            + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if b < c ∧ c < a then s_R (t a b) (t a c) (t b c) else 0)
            + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if c < a ∧ a < b then s_R (t a b) (t a c) (t b c) else 0)
            + (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, if c < b ∧ b < a then s_R (t a b) (t a c) (t b c) else 0) := by
          trans (∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet,
            ((if a < b ∧ b < c then s_R (t a b) (t a c) (t b c) else 0)
              + (if a < c ∧ c < b then s_R (t a b) (t a c) (t b c) else 0)
              + (if b < a ∧ a < c then s_R (t a b) (t a c) (t b c) else 0)
              + (if b < c ∧ c < a then s_R (t a b) (t a c) (t b c) else 0)
              + (if c < a ∧ a < b then s_R (t a b) (t a c) (t b c) else 0)
              + (if c < b ∧ b < a then s_R (t a b) (t a c) (t b c) else 0)))
          · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
              Finset.sum_congr rfl fun c _ => hpart a b c
          · simp only [Finset.sum_add_distrib]
        rw [hsum_p]
        have hord : ∀ F : Fin 9 → Fin 9 → Fin 9 → ℝ,
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, ∑ r3 ∈ ringSet, (if r1 < r2 ∧ r2 < r3 then F r1 r2 r3 else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), F r1 r2 r3 := by
          intro F
          refine Finset.sum_congr rfl fun r1 _ => ?_
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun r2 _ => ?_
          by_cases h12 : r1 < r2
          · simp only [h12, ↓reduceIte, true_and, Finset.sum_filter]
          · simp [h12]
        have q1 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, (if a < c ∧ c < b then s_R (t a b) (t a c) (t b c) else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), s_R (t r1 r2) (t r1 r3) (t r2 r3) := by
          rw [← hord]; refine Finset.sum_congr rfl fun a _ => ?_; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
          split_ifs
          · rw [hsR_uv, ht_sym c b]
          · rfl
        have q2 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, (if b < a ∧ a < c then s_R (t a b) (t a c) (t b c) else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), s_R (t r1 r2) (t r2 r3) (t r1 r3) := by
          rw [← hord]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => Finset.sum_congr rfl fun r3 _ => ?_
          split_ifs
          · rw [ht_sym r2 r1]
          · rfl
        have q3 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, (if c < a ∧ a < b then s_R (t a b) (t a c) (t b c) else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), s_R (t r1 r2) (t r2 r3) (t r1 r3) := by
          rw [← hord]; conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => Finset.sum_congr rfl fun r3 _ => ?_
          split_ifs
          · rw [hsR_uv, ht_sym r2 r1, ht_sym r3 r1]
          · rfl
        have q4 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, (if b < c ∧ c < a then s_R (t a b) (t a c) (t b c) else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), s_R (t r1 r3) (t r2 r3) (t r1 r2) := by
          rw [← hord]; rw [Finset.sum_comm]; conv_lhs => arg 2; ext r1; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => Finset.sum_congr rfl fun r3 _ => ?_
          split_ifs
          · rw [ht_sym r3 r1, ht_sym r3 r2]
          · rfl
        have q5 : ∑ a ∈ ringSet, ∑ b ∈ ringSet, ∑ c ∈ ringSet, (if c < b ∧ b < a then s_R (t a b) (t a c) (t b c) else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), s_R (t r1 r3) (t r2 r3) (t r1 r2) := by
          rw [← hord]; conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
          rw [Finset.sum_comm]; conv_lhs => arg 2; ext r1; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => Finset.sum_congr rfl fun r3 _ => ?_
          split_ifs
          · rw [hsR_uv, ht_sym r3 r2, ht_sym r3 r1, ht_sym r2 r1]
          · rfl
        rw [hord, q1, q2, q3, q4, q5]
        simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
        ring
      have h2g : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * gR (t r1 r2) =
          (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_R 1 (t r1 r2) (t r1 r2))
          + (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_R (t r1 r2) 1 (t r1 r2))
          + (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_R (t r1 r2) (t r1 r2) 1) := by
        simp only [gR, mul_add, Finset.sum_add_distrib]
      linarith
    have hPR_RP :
        (∑ r ∈ ringSet, ∑ p ∈ poleSet, ∑ r2 ∈ ringSet, s_R (t r p) (t r r2) (t p r2))
        + (∑ r ∈ ringSet, ∑ r1 ∈ ringSet, ∑ p ∈ poleSet, s_R (t r r1) (t r p) (t r1 p)) =
        (∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R 1 (t p r) (t p r))
        + (∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R (t p r) 1 (t p r))
        + (∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
            2 * (s_R (t p r1) (t r1 r2) (t p r2) + s_R (t p r2) (t r1 r2) (t p r1))) := by
      have hflip : ∑ r ∈ ringSet, ∑ r1 ∈ ringSet, ∑ p ∈ poleSet, s_R (t r r1) (t r p) (t r1 p) =
          ∑ r ∈ ringSet, ∑ p ∈ poleSet, ∑ r2 ∈ ringSet, s_R (t r p) (t r r2) (t p r2) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r2 _ => ?_
        rw [hsR_uv, ht_sym r2 p]
      rw [hflip, Finset.sum_comm]
      have hinner : ∀ p ∈ poleSet,
          ∑ r ∈ ringSet, ∑ r2 ∈ ringSet, s_R (t r p) (t r r2) (t p r2) =
          ∑ r ∈ ringSet, s_R (t p r) 1 (t p r)
          + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
              (s_R (t p r1) (t r1 r2) (t p r2) + s_R (t p r2) (t r1 r2) (t p r1)) := by
        intro p _
        have hcell : ∀ r r2 : Fin 9,
            s_R (t r p) (t r r2) (t p r2) =
              (if r = r2 then s_R (t p r) 1 (t p r) else 0)
              + (if r < r2 then s_R (t p r) (t r r2) (t p r2) else 0)
              + (if r2 < r then s_R (t p r) (t r r2) (t p r2) else 0) := by
          intro r r2
          rcases lt_trichotomy r r2 with h | rfl | h
          · simp [h, ne_of_lt h, not_lt.mpr (le_of_lt h), ht_sym r p]
          · simp [ht_diag, ht_sym r p]
          · simp [h, ne_of_gt h, not_lt.mpr (le_of_lt h), ht_sym r p]
        have hsum_c : ∑ r ∈ ringSet, ∑ r2 ∈ ringSet, s_R (t r p) (t r r2) (t p r2) =
            (∑ r ∈ ringSet, ∑ r2 ∈ ringSet, if r = r2 then s_R (t p r) 1 (t p r) else 0)
            + (∑ r ∈ ringSet, ∑ r2 ∈ ringSet, if r < r2 then s_R (t p r) (t r r2) (t p r2) else 0)
            + (∑ r ∈ ringSet, ∑ r2 ∈ ringSet, if r2 < r then s_R (t p r) (t r r2) (t p r2) else 0) := by
          trans (∑ r ∈ ringSet, ∑ r2 ∈ ringSet,
            ((if r = r2 then s_R (t p r) 1 (t p r) else 0)
              + (if r < r2 then s_R (t p r) (t r r2) (t p r2) else 0)
              + (if r2 < r then s_R (t p r) (t r r2) (t p r2) else 0)))
          · exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r2 _ => hcell r r2
          · simp only [Finset.sum_add_distrib]
        rw [hsum_c]
        have hD : ∑ r ∈ ringSet, ∑ r2 ∈ ringSet, (if r = r2 then s_R (t p r) 1 (t p r) else 0) =
            ∑ r ∈ ringSet, s_R (t p r) 1 (t p r) :=
          Finset.sum_congr rfl fun r hr => by simp [Finset.sum_ite_eq, hr]
        have hU : ∑ r ∈ ringSet, ∑ r2 ∈ ringSet, (if r < r2 then s_R (t p r) (t r r2) (t p r2) else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), s_R (t p r1) (t r1 r2) (t p r2) :=
          Finset.sum_congr rfl fun r1 _ => (Finset.sum_filter _ _).symm
        have hL : ∑ r ∈ ringSet, ∑ r2 ∈ ringSet, (if r2 < r then s_R (t p r) (t r r2) (t p r2) else 0) =
            ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), s_R (t p r2) (t r1 r2) (t p r1) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r1 _ => ?_
          rw [← Finset.sum_filter]
          exact Finset.sum_congr rfl fun r2 _ => by rw [ht_sym r2 r1]
        simp_rw [Finset.sum_add_distrib]
        linarith
      have hsum_eq : ∑ p ∈ poleSet, ∑ r ∈ ringSet, ∑ r2 ∈ ringSet, s_R (t r p) (t r r2) (t p r2) =
          (∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R (t p r) 1 (t p r))
          + ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
              (s_R (t p r1) (t r1 r2) (t p r2) + s_R (t p r2) (t r1 r2) (t p r1)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl hinner
      have hu : ∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R 1 (t p r) (t p r) =
          ∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R (t p r) 1 (t p r) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => hsR_uv _ _ _
      simp_rw [← Finset.mul_sum]
      linarith
    have hPP : ∑ r ∈ ringSet, ∑ p1 ∈ poleSet, ∑ p2 ∈ poleSet, s_R (t r p1) (t r p2) (t p1 p2) =
        ∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R (t p r) (t p r) 1
        + ∑ r ∈ ringSet, 2 * s_R (t 0 r) (t 1 r) (t 0 1) := by
      simp_rw [hP_sum, ht_diag, ht_sym 1 0]
      have hsym_r : ∀ r : Fin 9, s_R (t r 1) (t r 0) (t 0 1) = s_R (t 0 r) (t 1 r) (t 0 1) := by
        intro r; rw [hsR_uv, ht_sym r 0, ht_sym r 1]
      have hsym_r2 : ∀ r : Fin 9, s_R (t r 0) (t r 1) (t 0 1) = s_R (t 0 r) (t 1 r) (t 0 1) := by
        intro r; rw [ht_sym r 0, ht_sym r 1]
      have hrt0 : ∀ r : Fin 9, t r 0 = t 0 r := fun r => ht_sym r 0
      have hrt1 : ∀ r : Fin 9, t r 1 = t 1 r := fun r => ht_sym r 1
      simp_rw [hsym_r, hsym_r2, hrt0, hrt1, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hgPR : ∑ p ∈ poleSet, ∑ r ∈ ringSet, gR (t p r) =
        (∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R 1 (t p r) (t p r))
        + (∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R (t p r) 1 (t p r))
        + (∑ p ∈ poleSet, ∑ r ∈ ringSet, s_R (t p r) (t p r) 1) := by
      simp only [gR, Finset.sum_add_distrib]
    linarith
  have hcardR : ringSet.card = 7 := by decide
  have hB_edges : ∀ F : Fin 9 → ℝ,
      ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), (F r1 + F r2) = 6 * ∑ r ∈ ringSet, F r := by
    intro F
    have hpair : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), (F r1 + F r2) =
        ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, (if r1 < r2 then F r1 else 0)
        + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, (if r1 < r2 then F r2 else 0) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    rw [hpair]
    have h2' : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, (if r1 < r2 then F r2 else 0) =
        ∑ r ∈ ringSet, ∑ r1 ∈ ringSet.filter (· < r), F r := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm
    have h1' : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, (if r1 < r2 then F r1 else 0) =
        ∑ r ∈ ringSet, ∑ r2 ∈ ringSet.filter (r < ·), F r :=
      Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm
    rw [h1', h2', ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.sum_const, Finset.sum_const]
    have hc := card_ringSet_split r hr
    have hcR : ((ringSet.filter (r < ·)).card : ℝ) + ((ringSet.filter (· < r)).card : ℝ) = 6 := by
      exact_mod_cast hc
    simp only [nsmul_eq_mul]
    rw [← add_mul, hcR]
  have hG_edges : ∀ F : Fin 9 → Fin 9 → ℝ, (∀ x y, F x y = F y x) →
      ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
        (F r1 r2 + F r1 r3 + F r2 r3) =
      5 * ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), F r1 r2 := by
    intro F hF
    have h1' : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ _r3 ∈ ringSet.filter (r2 < ·), F r1 r2 =
        ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ((ringSet.filter (r2 < ·)).card : ℝ) * F r1 r2 := by
      refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2' : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), F r1 r3 =
        ∑ r1 ∈ ringSet, ∑ r3 ∈ ringSet.filter (r1 < ·), ((ringSet.filter (fun r2 => r1 < r2 ∧ r2 < r3)).card : ℝ) * F r1 r3 := by
      refine Finset.sum_congr rfl fun r1 _ => ?_
      trans (∑ r2 ∈ ringSet, ∑ r3 ∈ ringSet, if r1 < r2 ∧ r2 < r3 then F r1 r3 else 0)
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun r2 _ => ?_
        by_cases h12 : r1 < r2
        · simp only [h12, ↓reduceIte, true_and, Finset.sum_filter]
        · simp [h12]
      · rw [Finset.sum_comm, Finset.sum_filter]
        refine Finset.sum_congr rfl fun r3 _ => ?_
        by_cases h13 : r1 < r3
        · simp only [h13, ↓reduceIte]
          trans (∑ _r2 ∈ ringSet.filter (fun r2 => r1 < r2 ∧ r2 < r3), F r1 r3)
          · rw [Finset.sum_filter]
          · rw [Finset.sum_const, nsmul_eq_mul]
        · simp only [h13, ↓reduceIte]
          refine Finset.sum_eq_zero fun r2 _ => ?_
          have : ¬ (r1 < r2 ∧ r2 < r3) := fun ⟨a, b⟩ => h13 (lt_trans a b)
          simp [this]
    have h3' : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·), F r2 r3 =
        ∑ r2 ∈ ringSet, ∑ r3 ∈ ringSet.filter (r2 < ·), ((ringSet.filter (· < r2)).card : ℝ) * F r2 r3 := by
      trans (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet, ∑ r3 ∈ ringSet.filter (r2 < ·), if r1 < r2 then F r2 r3 else 0)
      · refine Finset.sum_congr rfl fun r1 _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun r2 _ => by by_cases h : r1 < r2 <;> simp [h]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r2 _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r3 _ => ?_
        trans (∑ _r1 ∈ ringSet.filter (· < r2), F r2 r3)
        · rw [Finset.sum_filter]
        · rw [Finset.sum_const, nsmul_eq_mul]
    simp_rw [Finset.sum_add_distrib]
    rw [h1', h2', h3', Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r1 hr1 => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r2 hr2 => ?_
    have hc := card_ringSet_triple_split r1 hr1 r2 hr2
    have hcR : ((ringSet.filter (r2 < ·)).card : ℝ)
        + ((ringSet.filter (fun r => r1 < r ∧ r < r2)).card : ℝ)
        + ((ringSet.filter (· < r1)).card : ℝ) = 5 := by exact_mod_cast hc
    rw [← add_mul, ← add_mul, hcR]
  have hC_B : ∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ _r2 ∈ ringSet.filter (r1 < ·), (1 : ℝ) = 42 := by
    have h21 : ∑ r1 ∈ ringSet, ∑ _r2 ∈ ringSet.filter (r1 < ·), (1 : ℝ) = 21 := by
      have : (∑ r1 ∈ ringSet, (ringSet.filter (r1 < ·)).card : ℕ) = 21 := by decide
      simpa [Finset.sum_const] using congrArg (Nat.cast (R := ℝ)) this
    rw [poleSet, Finset.sum_pair (by decide : (0 : Fin 9) ≠ 1), h21]; norm_num
  have hC_G : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ _r3 ∈ ringSet.filter (r2 < ·), (1 : ℝ) = 35 := by
    have : (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), (ringSet.filter (r2 < ·)).card : ℕ) = 35 := by decide
    simpa [Finset.sum_const] using congrArg (Nat.cast (R := ℝ)) this
  have hSumA : ∑ r ∈ ringSet, lam_A (t 0 1) (t 0 r) (t 1 r) =
      h_A (t 0 1) + ∑ p ∈ poleSet, ∑ r ∈ ringSet, psi_Ba (t p r) - 7 * c_a - 2 * gP (t 0 1)
      - ∑ r ∈ ringSet, 2 * (s_P (t 0 1) (t 0 r) (t 1 r) + s_P (t 0 1) (t 1 r) (t 0 r))
      - ∑ r ∈ ringSet, 2 * s_R (t 0 r) (t 1 r) (t 0 1) := by
    simp only [lam_A, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, hcardR,
      nsmul_eq_mul, poleSet, Finset.sum_pair (by decide : (0 : Fin 9) ≠ 1)]
    ring
  have hSumB : ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
      lam_B (t p r1) (t p r2) (t r1 r2) =
      ∑ p ∈ poleSet, ∑ r ∈ ringSet, (h_B (t p r) - psi_Ba (t p r))
      + 2 * ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), psi_Cb (t r1 r2)
      - 42 * c_b
      - ∑ p ∈ poleSet, ∑ r ∈ ringSet, (gP (t p r) + gR (t p r))
      - ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * s_P (t p r1) (t p r2) (t r1 r2)
      - ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
          2 * (s_R (t p r1) (t r1 r2) (t p r2) + s_R (t p r2) (t r1 r2) (t p r1)) := by
    have hpsi : ∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), psi_Cb (t r1 r2) =
        2 * ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), psi_Cb (t r1 r2) := by
      rw [poleSet, Finset.sum_pair (by decide : (0 : Fin 9) ≠ 1)]; ring
    have hcb : ∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ _r2 ∈ ringSet.filter (r1 < ·), c_b = 42 * c_b := by
      have hfac : ∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ _r2 ∈ ringSet.filter (r1 < ·), c_b =
          c_b * ∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ _r2 ∈ ringSet.filter (r1 < ·), (1 : ℝ) := by
        simp only [Finset.mul_sum, mul_one]
      rw [hfac, hC_B]; ring
    have hB1 : ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
        (h_B (t p r1) - psi_Ba (t p r1) + h_B (t p r2) - psi_Ba (t p r2)) / 6 =
        ∑ p ∈ poleSet, ∑ r ∈ ringSet, (h_B (t p r) - psi_Ba (t p r)) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have := hB_edges (fun r => h_B (t p r) - psi_Ba (t p r))
      simp_rw [← Finset.sum_div]
      have hre : ∀ r1 r2 : Fin 9,
          h_B (t p r1) - psi_Ba (t p r1) + h_B (t p r2) - psi_Ba (t p r2) =
          (h_B (t p r1) - psi_Ba (t p r1)) + (h_B (t p r2) - psi_Ba (t p r2)) := fun _ _ => by ring
      simp_rw [hre]; linarith
    have hB2 : ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
        (gP (t p r1) + gP (t p r2) + gR (t p r1) + gR (t p r2)) / 6 =
        ∑ p ∈ poleSet, ∑ r ∈ ringSet, (gP (t p r) + gR (t p r)) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have := hB_edges (fun r => gP (t p r) + gR (t p r))
      simp_rw [← Finset.sum_div]
      have hre : ∀ r1 r2 : Fin 9,
          gP (t p r1) + gP (t p r2) + gR (t p r1) + gR (t p r2) =
          (gP (t p r1) + gR (t p r1)) + (gP (t p r2) + gR (t p r2)) := fun _ _ => by ring
      simp_rw [hre]; linarith
    dsimp only [lam_B]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hB1 hB2
    rw [hB1, hB2, hpsi, hcb]
  have hSumG : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
      lam_G (t r1 r2) (t r1 r3) (t r2 r3) =
      ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), (h_C (t r1 r2) - 2 * psi_Cb (t r1 r2))
      - 35 * c_g
      - ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * gR (t r1 r2)
      - ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
          2 * (s_R (t r1 r2) (t r1 r3) (t r2 r3) + s_R (t r1 r2) (t r2 r3) (t r1 r3)
                + s_R (t r1 r3) (t r2 r3) (t r1 r2)) := by
    have hcg : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ _r3 ∈ ringSet.filter (r2 < ·), c_g = 35 * c_g := by
      have hfac : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ _r3 ∈ ringSet.filter (r2 < ·), c_g =
          c_g * ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ _r3 ∈ ringSet.filter (r2 < ·), (1 : ℝ) := by
        simp only [Finset.mul_sum, mul_one]
      rw [hfac, hC_G]; ring
    have hG1 : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
        (h_C (t r1 r2) - 2 * psi_Cb (t r1 r2) + h_C (t r1 r3) - 2 * psi_Cb (t r1 r3)
          + h_C (t r2 r3) - 2 * psi_Cb (t r2 r3)) / 5 =
        ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), (h_C (t r1 r2) - 2 * psi_Cb (t r1 r2)) := by
      have := hG_edges (fun x y => h_C (t x y) - 2 * psi_Cb (t x y)) (fun x y => by rw [ht_sym])
      simp_rw [← Finset.sum_div]
      have hre : ∀ r1 r2 r3 : Fin 9,
          h_C (t r1 r2) - 2 * psi_Cb (t r1 r2) + h_C (t r1 r3) - 2 * psi_Cb (t r1 r3)
            + h_C (t r2 r3) - 2 * psi_Cb (t r2 r3) =
          (h_C (t r1 r2) - 2 * psi_Cb (t r1 r2)) + (h_C (t r1 r3) - 2 * psi_Cb (t r1 r3))
            + (h_C (t r2 r3) - 2 * psi_Cb (t r2 r3)) := fun _ _ _ => by ring
      simp_rw [hre]; linarith
    have hG2 : ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
        2 * (gR (t r1 r2) + gR (t r1 r3) + gR (t r2 r3)) / 5 =
        ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), 2 * gR (t r1 r2) := by
      have := hG_edges (fun x y => 2 * gR (t x y)) (fun x y => by rw [ht_sym])
      simp_rw [← Finset.sum_div]
      have hre : ∀ r1 r2 r3 : Fin 9,
          2 * (gR (t r1 r2) + gR (t r1 r3) + gR (t r2 r3)) =
          2 * gR (t r1 r2) + 2 * gR (t r1 r3) + 2 * gR (t r2 r3) := fun _ _ _ => by ring
      simp_rw [hre]; linarith
    dsimp only [lam_G]
    simp_rw [Finset.sum_sub_distrib]
    simp_rw [Finset.sum_sub_distrib] at hG1
    rw [hG1, hG2, hcg]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hSumA hSumB hSumG hSP_split hSR_split ⊢
  linarith

/-- Any pair `(i₀, j₀)` with `i₀ ≠ j₀` can be moved to `(0, 1)` by a permutation of `Fin 9`. -/
theorem exists_swap_to_01 (i₀ j₀ : Fin 9) (hne : i₀ ≠ j₀) :
    ∃ σ : Equiv.Perm (Fin 9), σ 0 = i₀ ∧ σ 1 = j₀ := by
  let τ₁ : Equiv.Perm (Fin 9) := Equiv.swap 0 i₀
  let j₁ : Fin 9 := τ₁.symm j₀
  have hj₁ : j₁ ≠ 0 := by
    intro h
    apply hne
    have := congrArg τ₁ h
    simpa [j₁, τ₁] using this.symm
  let τ₂ : Equiv.Perm (Fin 9) := Equiv.swap 1 j₁
  refine ⟨τ₁ * τ₂, ?_, ?_⟩
  · simp [Equiv.Perm.mul_apply, τ₂, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 9) ≠ 1) hj₁.symm, τ₁]
  · simp [Equiv.Perm.mul_apply, τ₂, j₁]

/-- Decompose `sumPairs9 f` into pole-pole `(0,1)`, pole-ring, and ring-ring sums. -/
theorem sumPairs9_pole_ring (f : Fin 9 → Fin 9 → ℝ) :
    sumPairs9 f =
      f 0 1
      + ∑ p ∈ poleSet, ∑ r ∈ ringSet, f p r
      + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), f r1 r2 := by
  unfold sumPairs9
  rw [sum_univ_pole_ring]
  have hP : ∑ p ∈ poleSet, ∑ j ∈ Finset.Ioi p, f p j =
      f 0 1 + ∑ p ∈ poleSet, ∑ r ∈ ringSet, f p r := by
    have h0 : Finset.Ioi (0 : Fin 9) = insert 1 ringSet := by decide
    have h1 : Finset.Ioi (1 : Fin 9) = ringSet := by decide
    have h1not : (1 : Fin 9) ∉ ringSet := by decide
    simp [poleSet, h0, h1, h1not]
    ring
  rw [hP]
  have hR : ∑ r1 ∈ ringSet, ∑ j ∈ Finset.Ioi r1, f r1 j =
      ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), f r1 r2 :=
    Finset.sum_congr rfl fun r1 hr1 => by rw [Ioi_eq_ringSet_filter r1 hr1]
  rw [hR]

end ThomsonN9.StageB
