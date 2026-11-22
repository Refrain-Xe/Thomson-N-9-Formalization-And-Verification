import Mathlib
import ThomsonN9.TableB5

/-!
# Table B5Core (R16A / r16a): the pure-algebra core of the B5 analytic body, steps 1–2

This file is the first piece of the B5 analytic body (`d_P(X,Y) ≤ C·δ`,
the `l4_procrustes.py` proof) — the **pure algebra layer of steps 1–2**:

* **Step 1 (E decomposition).**  With `D := Y − X`, the Gram difference
  `E := Y*Yᵀ − X*Xᵀ` satisfies the three-cross identity
  `E = X*Dᵀ + D*Xᵀ + D*Dᵀ` (`E_decomp`, matrix-level ring); the diagonal of
  `E` vanishes identically under two-sided row normalisation
  (`E_diag_zero`, elementwise premise substitution); and the Frobenius bound
  `η = ‖E‖_F ≤ √72·δ` holds when every off-diagonal entry of `E` is bounded
  by `δ` (`frob_le_of_off_diag` — 72 = 81 − 9 off-diagonal slots, each ≤ δ,
  Cauchy–Schwarz assembly with `Real.sqrt 72` exact; TTP-facing corollary
  `eta_le_sqrt72`).

* **Step 2 (projection split).**  With `S := XᵀX` invertible,
  `A := S⁻¹*Xᵀ*D` and `D_⊥ := D − X*A` satisfy `Xᵀ*D_⊥ = 0` (`proj_orth`);
  `P₀ := X*S⁻¹*Xᵀ` is idempotent (`P0_mul_self`) and symmetric
  (`P0_transpose`); and the generic invertibility bridge
  quadratic-form sandwich ⇒ `Matrix.PosDef` ⇒ `IsUnit S` (`sandwich_isUnit`,
  probe-verified route via `Matrix.PosDef.of_dotProduct_mulVec_pos` /
  `Matrix.PosDef.isUnit`) instantiates to the TTP matrix:
  `ttpX_quadform` (the matrix quadratic form `v ⬝ᵥ ((ttpXᵀ*ttpX)*ᵥ v)`
  equals `TableB5.ttpQ`, ext/elementwise ring) merged with
  `TableB5.ttp_sandwich_lo` gives `ttpX_isUnit` on the recorded z-box.

**Statement-face decisions (fixed for B5b/B5c; see notes/tableb-lean.md §4):**

1. Index types `Fin 9` (rows) × `Fin 3` (columns) for the TTP instantiation
   (`ttpX`); generic lemmas stay polymorphic in `{m n}`.
2. Frobenius norm via the own definition `frob M := Real.sqrt (∑ i j, (M i j)^2)`
   (the Mathlib Frobenius norm instances are `local instance`s —
   `Matrix.frobeniusNormedAddCommGroup` is not globally registered — so the
   instance-`‖·‖` path is avoided; numerically identical to
   `Matrix.frobenius_norm_def`, Analysis/Matrix/Normed.lean:561).
3. Row normalisation `∀ i, X i ⬝ᵥ X i = 1` (dotProduct calibre); Gram
   difference as the literal expression `Y * Yᵀ - X * Xᵀ`; the O(3) face is
   reserved for B5c in witness form `∃ Q, Q * Qᵀ = 1 ∧ …` (not in this file).

Zero numeric data literals (all constants come from `ThomsonN9.TableB5Data`
via `ThomsonN9.TableB5`) — hence no Data file for this piece.

Honest scope note (B5a boundary): steps 3–6 (trace inequality, norm
compression, polar decomposition, final assembly `d_P ≤ C·δ`) are NOT part of
this file; they are B5b/B5c.  The probe evidence for the three pre-work APIs
(① posDef_iff_isUnit usage-level, ② sandwich⇒PosDef⇒IsUnit bridge,
⑤ Frobenius orthogonal invariance absence) is recorded in notes/tableb-lean.md
§4 with /tmp logs.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5Core

open Matrix
open ThomsonN9.TableB5Data

/-! ### Frobenius 范数口径（陈述面决策 2） -/

/-- Frobenius 范数自有 def：`frob M = √(∑ i j (M i j)²)`（与 Mathlib 的
`Matrix.frobenius_norm_def` 数值一致；不走 local instance 的 ‖·‖ 路径）。 -/
noncomputable def frob {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (M i j)^2)

/-- `frob` 非负（`Real.sqrt_nonneg` 直出）。 -/
theorem frob_nonneg {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    0 ≤ frob M := Real.sqrt_nonneg _

/-! ### 步骤 1（E 分解层） -/

/-- Gram 对称性：`(XᵀX)ᵀ = XᵀX`（`Matrix.transpose_mul` 纯环）。 -/
theorem gram_transpose {m n : Type} [Fintype m] [Fintype n] (X : Matrix m n ℝ) :
    (Xᵀ * X)ᵀ = Xᵀ * X := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Gram 差逐元口径：`(Y*Yᵀ − X*Xᵀ) i j = Y i ⬝ᵥ Y j − X i ⬝ᵥ X j`
（dotProduct 口径对接，B5b 块分解面的入口引理）。 -/
theorem gramDiff_entry {m n : Type} [Fintype m] [Fintype n] (X Y : Matrix m n ℝ)
    (i j : m) :
    (Y * Yᵀ - X * Xᵀ) i j = Y i ⬝ᵥ Y j - X i ⬝ᵥ X j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply, dotProduct]

/-- Gram 差对称性：`(Y*Yᵀ − X*Xᵀ)ᵀ = Y*Yᵀ − X*Xᵀ`（η 的对称面）。 -/
theorem gramDiff_transpose {m n : Type} [Fintype m] [Fintype n] (X Y : Matrix m n ℝ) :
    (Y * Yᵀ - X * Xᵀ)ᵀ = Y * Yᵀ - X * Xᵀ := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]

/-- **步骤 1-(i) E 三交叉分解**：`D := Y − X ⇒ E := Y*Yᵀ − X*Xᵀ = X*Dᵀ + D*Xᵀ + D*Dᵀ`
（矩阵层 ring 恒等式：conv 展开＋add_mul/mul_add 分布＋abel 收尾——
§2.3 摩擦 2 的 simp only＋abel 口径，矩阵级优先）。 -/
theorem E_decomp {m n : Type} [Fintype m] [Fintype n] (X Y : Matrix m n ℝ) :
    Y * Yᵀ - X * Xᵀ = X * (Y - X)ᵀ + (Y - X) * Xᵀ + (Y - X) * (Y - X)ᵀ := by
  have hYX : X + (Y - X) = Y := by abel
  have hT : (X + (Y - X))ᵀ = Xᵀ + (Y - X)ᵀ := Matrix.transpose_add X (Y - X)
  conv_lhs => rw [← hYX]
  simp only [hT, Matrix.add_mul, Matrix.mul_add]
  abel

/-- **步骤 1-(ii) E 对角恒 0**：X/Y 双侧行单位（∀ i, X i ⬝ᵥ X i = 1 同 Y）
⇒ Gram 差对角元逐个为 0（行单位前提的 elementwise 代入）。 -/
theorem E_diag_zero {m n : Type} [Fintype m] [Fintype n] (X Y : Matrix m n ℝ)
    (hX : ∀ i, X i ⬝ᵥ X i = 1) (hY : ∀ i, Y i ⬝ᵥ Y i = 1) (i : m) :
    (Y * Yᵀ - X * Xᵀ) i i = 0 := by
  rw [gramDiff_entry X Y i i, hY i, hX i]; ring

/-- **步骤 1-(iii) η ≤ √72·δ（抽象版）**：9×9 阵对角恒 0＋非对角元逐个 ≤ δ
⇒ `frob E ≤ Real.sqrt 72 * δ`（72 = 81 − 9：每行对角元 0（`Finset.sum_erase`
直消）＋其余 8 个元各 ≤ δ²（`pow_le_pow_left`），9 行合计 72δ²，再
`Real.sqrt_le_sqrt`＋`Real.sqrt_mul`/`Real.sqrt_sq` 拼装）。 -/
theorem frob_le_of_off_diag (E : Matrix (Fin 9) (Fin 9) ℝ) (δ : ℝ)
    (hdiag : ∀ i, E i i = 0) (hoff : ∀ i j, i ≠ j → |E i j| ≤ δ) (hδ : 0 ≤ δ) :
    frob E ≤ Real.sqrt 72 * δ := by
  have hrow : ∀ i, ∑ j, (E i j)^2 ≤ 8 * δ^2 := by
    intro i
    have hsplit : ∑ j ∈ (Finset.univ.erase i), (E i j)^2 = ∑ j, (E i j)^2 :=
      Finset.sum_erase (Finset.univ : Finset (Fin 9)) (f := fun j => (E i j)^2)
        (a := i) (by rw [hdiag i]; ring)
    rw [← hsplit]
    calc ∑ j ∈ Finset.univ.erase i, (E i j)^2
        ≤ ∑ j ∈ Finset.univ.erase i, δ^2 :=
          Finset.sum_le_sum fun j hj => by
            have hne : i ≠ j := ((Finset.mem_erase.mp hj).1).symm
            have h1 : |E i j| ≤ δ := hoff i j hne
            have h2 : (0:ℝ) ≤ |E i j| := abs_nonneg (E i j)
            have e : (E i j)^2 = |E i j| * |E i j| := by
              rw [← sq_abs (E i j), sq]
            rw [e]
            nlinarith [h1, h2, hδ]
      _ = (Finset.univ.erase i).card • δ^2 := Finset.sum_const _
      _ = 8 * δ^2 := by
          simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  have htot : ∑ i, ∑ j, (E i j)^2 ≤ 72 * δ^2 := by
    calc ∑ i, ∑ j, (E i j)^2 ≤ ∑ i, 8 * δ^2 :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = 9 * (8 * δ^2) := by simp
      _ = 72 * δ^2 := by ring
  unfold frob
  refine (Real.sqrt_le_sqrt htot).trans ?_
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 72) (δ^2), Real.sqrt_sq hδ]

/-- **步骤 1-(iii) TTP 面推论 η ≤ √72·δ**：X/Y 双侧行单位＋固定标号 Gram 扰动
`|Y i ⬝ᵥ Y j − X i ⬝ᵥ X j| ≤ δ`（∀ i ≠ j，对称化口径）⇒
`frob (Y*Yᵀ − X*Xᵀ) ≤ √72·δ`（l4_procrustes.py 步骤 1 的收口）。 -/
theorem eta_le_sqrt72 (X Y : Matrix (Fin 9) (Fin 3) ℝ) (δ : ℝ)
    (hX : ∀ i, X i ⬝ᵥ X i = 1) (hY : ∀ i, Y i ⬝ᵥ Y i = 1)
    (hgram : ∀ i j, i ≠ j → |Y i ⬝ᵥ Y j - X i ⬝ᵥ X j| ≤ δ) (hδ : 0 ≤ δ) :
    frob (Y * Yᵀ - X * Xᵀ) ≤ Real.sqrt 72 * δ :=
  frob_le_of_off_diag (Y * Yᵀ - X * Xᵀ) δ (E_diag_zero X Y hX hY)
    (fun i j hij => by rw [gramDiff_entry X Y i j]; exact hgram i j hij) hδ

/-! ### 步骤 2（投影分解层） -/

/-- **步骤 2-(iv) 投影正交性**：S := XᵀX 可逆（`IsUnit`）时
`D_⊥ := D − X*((XᵀX)⁻¹*Xᵀ*D)` 满足 `Xᵀ*D_⊥ = 0`（矩阵消去：
`Matrix.isUnit_iff_isUnit_det`＋`Matrix.mul_nonsing_inv_cancel_left` 归一）。 -/
theorem proj_orth (X D : Matrix (Fin 9) (Fin 3) ℝ) (hS : IsUnit (Xᵀ * X)) :
    Xᵀ * (D - X * ((Xᵀ * X)⁻¹ * Xᵀ * D)) = 0 := by
  have hdet : IsUnit (Xᵀ * X).det := (Matrix.isUnit_iff_isUnit_det (Xᵀ * X)).mp hS
  have key : Xᵀ * (X * (((Xᵀ * X)⁻¹ * Xᵀ) * D)) = Xᵀ * D := by
    rw [show ((Xᵀ * X)⁻¹ * Xᵀ) * D = (Xᵀ * X)⁻¹ * (Xᵀ * D) from by
          rw [Matrix.mul_assoc],
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv_cancel_left (Xᵀ * X) (Xᵀ * D) hdet]
  rw [Matrix.mul_sub, key, sub_self]

/-- **步骤 2-(v) P₀ 幂等**：S := XᵀX 可逆时 `P₀ := X*S⁻¹*Xᵀ` 满足
`P₀*P₀ = P₀`（核心 `P₀*X = X`：`Matrix.nonsing_inv_mul` 归一）。 -/
theorem P0_mul_self (X : Matrix (Fin 9) (Fin 3) ℝ) (hS : IsUnit (Xᵀ * X)) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹ * Xᵀ) = X * (Xᵀ * X)⁻¹ * Xᵀ := by
  have hdet : IsUnit (Xᵀ * X).det := (Matrix.isUnit_iff_isUnit_det (Xᵀ * X)).mp hS
  have e1 : (Xᵀ * X)⁻¹ * (Xᵀ * X) = 1 :=
    Matrix.nonsing_inv_mul (Xᵀ * X) hdet
  have hPX : (X * (Xᵀ * X)⁻¹ * Xᵀ) * X = X := by
    rw [Matrix.mul_assoc (X * (Xᵀ * X)⁻¹) Xᵀ X,
        Matrix.mul_assoc X (Xᵀ * X)⁻¹ (Xᵀ * X), e1, Matrix.mul_one]
  rw [show (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹ * Xᵀ)
        = ((X * (Xᵀ * X)⁻¹ * Xᵀ) * X) * (Xᵀ * X)⁻¹ * Xᵀ from by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc],
      hPX]

/-- **步骤 2-(v) P₀ 对称**：`(X*S⁻¹*Xᵀ)ᵀ = X*S⁻¹*Xᵀ`（`S⁻¹` 对称经
`Matrix.transpose_nonsing_inv`＋`gram_transpose`，纯环）。 -/
theorem P0_transpose (X : Matrix (Fin 9) (Fin 3) ℝ) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ)ᵀ = X * (Xᵀ * X)⁻¹ * Xᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, gram_transpose, Matrix.mul_assoc]

/-- **步骤 2-(vi) S 可逆前提桥（通用引理）**：S 实对称＋二次型夹逼
`∀ v, l*(v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)`（l > 0）⇒ `IsUnit S`
（探针②走通路线：`Matrix.PosDef.of_dotProduct_mulVec_pos`＋
`Matrix.dotProduct_star_self_pos_iff`＋`Matrix.PosDef.isUnit`；
ℝ 面经 `conjTranspose_eq_transpose_of_trivial`＋`star_trivial` 归位）。 -/
theorem sandwich_isUnit {n : Type} [Fintype n] [DecidableEq n] {S : Matrix n n ℝ}
    (hSym : Sᵀ = S) {l : ℝ} (hl : 0 < l)
    (h : ∀ v : n → ℝ, l * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)) :
    IsUnit S := by
  have hHer : S.IsHermitian := by
    rw [IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hSym]
  refine (Matrix.PosDef.of_dotProduct_mulVec_pos hHer fun v hv => ?_).isUnit
  have hpos : (0:ℝ) < v ⬝ᵥ v := by
    simpa only [star_trivial] using Matrix.dotProduct_star_self_pos_iff.mpr hv
  simpa only [star_trivial] using lt_of_lt_of_le (mul_pos hl hpos) (h v)

/-! ### 步骤 2-(vii) TTP 实例化层 -/

/-- Fin 3 三向量点积展开（`![a₀,a₁,a₂] ⬝ᵥ v = a₀v₀+a₁v₁+a₂v₂`，
ttpX 行展开的入口小件）。 -/
theorem rowDot (a0 a1 a2 : ℝ) (v : Fin 3 → ℝ) :
    (![a0, a1, a2] : Fin 3 → ℝ) ⬝ᵥ v = a0 * v 0 + a1 * v 1 + a2 * v 2 := by
  rw [dotProduct, Fin.sum_univ_three]
  simp

/-- 矩阵二次型＝行点积平方和：`v ⬝ᵥ ((MᵀM) *ᵥ v) = ∑ i (M i ⬝ᵥ v)²`
（`mulVec_mulVec`＋`dotProduct_mulVec`＋`vecMul_transpose` 搬运；
B5b 的 Frobenius↔trace 面共用底座）。 -/
theorem quadsum_eq {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ)
    (v : n → ℝ) :
    v ⬝ᵥ ((Mᵀ * M) *ᵥ v) = ∑ i, (M i ⬝ᵥ v)^2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (M i ⬝ᵥ v) * (M i ⬝ᵥ v) = (M i ⬝ᵥ v)^2
  ring

/-- TTP 九行构型的 ℕ 索引行函数（上三角 3＋下三角 3＋帽 3，行序同
TableB5.ttpQ 九项/表 B1 family_points_s3；ℕ 索引为 `Fin.sum_univ_eq_sum_range`
展开面设计——探针⑥⑧）。 -/
noncomputable def ttpRow (z : ℝ) : ℕ → Fin 3 → ℝ
  | 0 => ![Real.sqrt (1-z^2), 0, z]
  | 1 => ![-(Real.sqrt (1-z^2))/2, Real.sqrt 3 * Real.sqrt (1-z^2)/2, z]
  | 2 => ![-(Real.sqrt (1-z^2))/2, -(Real.sqrt 3 * Real.sqrt (1-z^2)/2), z]
  | 3 => ![Real.sqrt (1-z^2), 0, -z]
  | 4 => ![-(Real.sqrt (1-z^2))/2, Real.sqrt 3 * Real.sqrt (1-z^2)/2, -z]
  | 5 => ![-(Real.sqrt (1-z^2))/2, -(Real.sqrt 3 * Real.sqrt (1-z^2)/2), -z]
  | 6 => ![1/2, Real.sqrt 3/2, 0]
  | 7 => ![-1, 0, 0]
  | _ => ![1/2, -(Real.sqrt 3/2), 0]

/-- TTP 九行矩阵（陈述面决策 1：行 `Fin 9` 列 `Fin 3` 显式 def）。 -/
noncomputable def ttpX (z : ℝ) : Matrix (Fin 9) (Fin 3) ℝ :=
  Matrix.of fun i j => ttpRow z i.val j

/-- **步骤 2-(vii) 矩阵二次型桥**：TTP 矩阵的二次型
`v ⬝ᵥ ((ttpXᵀ*ttpX) *ᵥ v) == TableB5.ttpQ z (v 0) (v 1) (v 2)`
（quadsum_eq 行展开＋`Fin.sum_univ_eq_sum_range`＋`Finset.sum_range_succ`
九项显式化＋rowDot 逐行＋ring 收口——对勾恒等式，无 z 盒前提）。 -/
theorem ttpX_quadform (z : ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (((ttpX z)ᵀ * ttpX z) *ᵥ v) = TableB5.ttpQ z (v 0) (v 1) (v 2) := by
  rw [quadsum_eq]
  show ∑ i : Fin 9, (ttpRow z i.val ⬝ᵥ v)^2 = TableB5.ttpQ z (v 0) (v 1) (v 2)
  rw [Fin.sum_univ_eq_sum_range (fun k => (ttpRow z k ⬝ᵥ v)^2) 9]
  simp only [Finset.sum_range_succ]
  simp only [ttpRow, rowDot]
  unfold TableB5.ttpQ
  ring

/-- **步骤 2-(vii) TTP 可逆推论**：z 盒内（TableB5Data.zLo ≤ z ≤ zHi），
Gram 阵 `S = ttpXᵀ*ttpX` 可逆（sandwich_isUnit＋ttpX_quadform＋
TableB5.ttp_sandwich_lo 合并——l₃ 夹逼经二次型口径直入）。 -/
theorem ttpX_isUnit (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    IsUnit ((ttpX z)ᵀ * ttpX z) := by
  refine sandwich_isUnit (gram_transpose (ttpX z)) (l := (l3:ℝ)) ?_ ?_
  · exact (by norm_num [l3] : (0:ℝ) < (l3:ℝ))
  · intro v
    have hq := TableB5.ttp_sandwich_lo z (v 0) (v 1) (v 2) h1 h2
    rw [ttpX_quadform, dotProduct, Fin.sum_univ_three]
    nlinarith [hq]

end ThomsonN9.TableB5Core
