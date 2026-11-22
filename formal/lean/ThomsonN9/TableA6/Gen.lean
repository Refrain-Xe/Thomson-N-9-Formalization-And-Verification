/-
TableA6/Gen.lean —— A6 件通用代数层（无数据）：由两步重构
（step1：L·diag(d) = M；step2：M·Lᵀ = S）导出二次型 v(y)ᵀ S v(y) 的
平方和表示 Σ_j d_j·(Σ_k L[k][j]·y^k)²。纯矩阵代数链
（dotProduct/mulVec/vecMul/transpose/diagonal），无数据展开——
(ii) 的 ring 平坦形（D50-2）之代数化替身。
-/
import Mathlib

open Matrix

set_option maxHeartbeats 60000000

/-- 通用：S = (L·diag d)·Lᵀ ⟹ vᵀ S v = Σ_j d_j·(Σ_k L[k][j]·y^k)²。 -/
theorem quad_of_recon {n : ℕ} (S M L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (h1 : L * Matrix.diagonal d = M) (h2 : M * Lᵀ = S) (y : ℝ) :
    (fun k : Fin n => y ^ (k : ℕ)) ⬝ᵥ (S *ᵥ (fun k : Fin n => y ^ (k : ℕ)))
      = ∑ j : Fin n, d j * (∑ k : Fin n, L k j * y ^ (k : ℕ)) ^ 2 := by
  set v : Fin n → ℝ := fun k => y ^ (k : ℕ) with hv
  have hS : L * Matrix.diagonal d * Lᵀ = S := by rw [h1, h2]
  have hvl : v ᵥ* L = Lᵀ *ᵥ v := (Matrix.mulVec_transpose L v).symm
  have hd : (Lᵀ *ᵥ v) ᵥ* Matrix.diagonal d = fun j => (Lᵀ *ᵥ v) j * d j := by
    funext j; exact Matrix.vecMul_diagonal (Lᵀ *ᵥ v) d j
  have hw : ∀ j : Fin n, (Lᵀ *ᵥ v) j = ∑ k : Fin n, L k j * y ^ (k : ℕ) := by
    intro j
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hv]
  calc (fun k : Fin n => y ^ (k : ℕ)) ⬝ᵥ (S *ᵥ (fun k : Fin n => y ^ (k : ℕ)))
      = v ⬝ᵥ (S *ᵥ v) := rfl
    _ = v ⬝ᵥ ((L * Matrix.diagonal d * Lᵀ) *ᵥ v) := by rw [hS]
    _ = v ⬝ᵥ ((L * Matrix.diagonal d) *ᵥ (Lᵀ *ᵥ v)) := by rw [← Matrix.mulVec_mulVec]
    _ = (v ᵥ* (L * Matrix.diagonal d)) ⬝ᵥ (Lᵀ *ᵥ v) := by rw [Matrix.dotProduct_mulVec]
    _ = ((v ᵥ* L) ᵥ* Matrix.diagonal d) ⬝ᵥ (Lᵀ *ᵥ v) := by rw [← Matrix.vecMul_vecMul]
    _ = ((Lᵀ *ᵥ v) ᵥ* Matrix.diagonal d) ⬝ᵥ (Lᵀ *ᵥ v) := by rw [hvl]
    _ = (fun j => (Lᵀ *ᵥ v) j * d j) ⬝ᵥ (Lᵀ *ᵥ v) := by rw [hd]
    _ = ∑ j : Fin n, d j * ((Lᵀ *ᵥ v) j) ^ 2 := by
        simp only [dotProduct]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j : Fin n, d j * (∑ k : Fin n, L k j * y ^ (k : ℕ)) ^ 2 := by
        simp only [hw]

/-- 通用：平方和为零 ⟹ 逐 entries 为零（提取器·单形）。 -/
theorem entries_of_sumsq {n : ℕ} (f : Fin n → Fin n → ℝ)
    (h : ∑ k, ∑ l, (f k l)^2 = 0) : ∀ k l, f k l = 0 := by
  intro k l
  have h0 : ∀ i : Fin n, ∑ l : Fin n, (f i l)^2 = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun p (_ : p ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_nonneg fun l _ => sq_nonneg (f p l))).mp h i (Finset.mem_univ i)
  have h1 : ∀ i : Fin n, ∀ j : Fin n, (f i j)^2 = 0 := fun i j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f i j))).mp (h0 i) j
      (Finset.mem_univ j)
  exact pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num) |>.mp (h1 k l)

/-- 通用：双重和（f²+g²）为零 ⟹ 逐 entries f=0 ∧ g=0（合并平方和提取器）。 -/
theorem entries_of_sumsq2 {n : ℕ} (f g : Fin n → Fin n → ℝ)
    (h : ∑ k, ∑ l, ((f k l)^2 + (g k l)^2) = 0) :
    ∀ k l, f k l = 0 ∧ g k l = 0 := by
  intro k l
  have hpos : ∀ p : Fin n × Fin n, 0 ≤ (f p.1 p.2)^2 + (g p.1 p.2)^2 :=
    fun p => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have h0 : ∀ i : Fin n, ∑ l : Fin n, ((f i l)^2 + (g i l)^2) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun p (_ : p ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_nonneg fun q _ => hpos (p, q))).mp h i (Finset.mem_univ i)
  have h1 : ∀ i j : Fin n, (f i j)^2 + (g i j)^2 = 0 := fun i j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpos (i, j))).mp (h0 i) j
    (Finset.mem_univ j)
  have ha : 0 ≤ (f k l)^2 := sq_nonneg _
  have hb : 0 ≤ (g k l)^2 := sq_nonneg _
  have hz := h1 k l
  constructor
  · exact pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num) |>.mp
      (le_antisymm (by linarith) ha)
  · exact pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num) |>.mp
      (le_antisymm (by linarith) hb)
