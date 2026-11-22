import Mathlib
import ThomsonN9.TableB5
import ThomsonN9.TableB5Core

/-!
# Table B5Trace (R17A / r17a): the trace layer of the B5 analytic body, steps 3–4

This file is the second piece of the B5 analytic body (`d_P(X,Y) ≤ C·δ`,
the `l4_procrustes.py` proof) — the **trace / norm-compression layer of
steps 3–4**, on top of `TableB5Core` (B5a, steps 1–2):

* **Step 3 (mixed block).**  With `S := XᵀX` invertible,
  `A := S⁻¹*(Xᵀ*D)`, `D_∥ := X*A`, `D_⊥ := D − X*A` (D := Y − X):
  the mixed-block identity `P₀*E*(1−P₀) = X*D_⊥ᵀ + D_∥*D_⊥ᵀ`
  (`mixed_block`, matrix-level rewrites on `P₀*X = X` / `Xᵀ*(1−P₀) = 0` /
  `P₀*D = D_∥`); the Frobenius↔trace bridge `(frob M)^2 = (M*Mᵀ).trace`
  (`frob_sq_eq_trace`, entrywise sum transport under the own `frob` def of
  D68-2) and the `X*D_⊥ᵀ` face `frob_sq_mul_transpose`; Frobenius-Pythagoras
  in both forms (`tr(A*Bᵀ) = 0` / `Aᵀ*B = 0` ⇒ `frob(A+B)² = frob A² +
  frob B²`); the PSD trace monotonicity family T1/T2 (`trace_mul_nonneg`,
  `trace_ge_smul` — proof verbatim from the R15C probe
  /tmp/r15c_probe3_trace.lean, re-verified in-context by the R17A probe
  /tmp/r17a_probe3_trace_step34.lean) plus the upper-bound flip
  `trace_le_smul`; and the **headline theorem of step 3**
  (`step3_bound`): under the quadratic-form lower sandwich
  `∀ v, λ₃*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((XᵀX)*ᵥ v)`,
  `(σ₃ − frob D_∥) * frob D_⊥ ≤ frob (Y*Yᵀ − X*Xᵀ)` with `σ₃ = √λ₃`.

* **Step 4 (parallel block).**  With `B := A + Aᵀ + A*Aᵀ`: the three
  B-identities (`B_eq_factor` `B = (1+A)*(1+A)ᵀ − 1`;
  `XTEX_eq_SBS` `Xᵀ*E*X = S*B*S`; `B_eq_inv`
  `B = S⁻¹*(Xᵀ*E*X)*S⁻¹`); the inverse-compression family
  (`vecNorm_inv_mulVec_le` `‖S⁻¹*ᵥv‖ ≤ ‖v‖/λ₃` via the own `vecNorm`
  def + self-built sum-level Cauchy–Schwarz; `frob_inv_mul_inv_le`
  `frob (S⁻¹*M*S⁻¹) ≤ frob M/λ₃²` by the T2-flip trace route); the
  Frobenius↔operator-norm comparison face in sandwich form
  (`frob_mul_le_of_vecNorm` column-norm compression — R17A probe route
  (a), pure sum transport, zero `WithLp`; `vecNorm_transpose_mulVec_le`
  dual-sandwich bound `‖Xᵀ*ᵥu‖ ≤ √λ₁*‖u‖`; `frob_XTEX_le`
  `frob (Xᵀ*E*X) ≤ λ₁*η`); and the **headline theorem of step 4**
  (`step4_bound`): `frob B ≤ λ₁ * frob (Y*Yᵀ − X*Xᵀ) / λ₃²` (β-face).

Correspondence to `l4_procrustes.py` (proof steps, docstring lines):
step 3 = `P₀E(I−P₀) = XD_⊥ᵀ + D_∥D_⊥ᵀ`, `‖XD_⊥ᵀ‖²_F = tr(S·D_⊥ᵀD_⊥) ≥
λ₃‖D_⊥‖²_F ⇒ (σ₃ − ‖D_∥‖_F)·‖D_⊥‖_F ≤ η`; step 4 = `XᵀEX = S·B·S`,
`B = S⁻¹(XᵀEX)S⁻¹`, `‖B‖_F ≤ ‖XᵀEX‖_F/λ₃² ≤ λ₁η/λ₃² = β`.  Steps 5–6
(polar decomposition, final assembly `d_P ≤ C·δ`) are NOT in this file
(B5c boundary).

**Statement-face decisions (inherited D68 + §5 increments):** generic
lemmas stay polymorphic in `{m n}`; `frob`/`vecNorm` own defs (D68-2 /
D72-①③); hypotheses in dotProduct quadratic-form sandwich calibre
(`∀ v, … ≤ v ⬝ᵥ (S *ᵥ v)` — the λ-sandwich of `TableB5.ttp_sandwich_lo/hi`
instantiates directly, see the `ttpX_*` corollaries).  Zero numeric data
literals (all constants live in `ThomsonN9.TableB5Data` via `TableB5`) —
no Data file for this piece.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5Trace

open scoped MatrixOrder
open Matrix
open ThomsonN9.TableB5Data
open ThomsonN9.TableB5Core

/-! ### 向量 ℓ2 范数口径（D72-③：自有 vecNorm def＋sum 级 Cauchy–Schwarz） -/

/-- 向量 ℓ2 范数自有 def：`vecNorm v = √(∑ i (v i)²)`（纯函数 `n → ℝ` 的 Pi
实例是 sup 范数，不走实例路径——与 D68-2 frob 自有 def 同哲学）。 -/
noncomputable def vecNorm {n : Type} [Fintype n] (v : n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^2)

/-- `vecNorm` 非负（`Real.sqrt_nonneg` 直出）。 -/
theorem vecNorm_nonneg {n : Type} [Fintype n] (v : n → ℝ) : 0 ≤ vecNorm v :=
  Real.sqrt_nonneg _

/-- `vecNorm` 平方展开：`(vecNorm v)² = ∑ i (v i)²`。 -/
theorem vecNorm_sq {n : Type} [Fintype n] (v : n → ℝ) :
    (vecNorm v)^2 = ∑ i, v i ^2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- 自身点积＝vecNorm 平方：`v ⬝ᵥ v = (vecNorm v)²`。 -/
theorem dotProduct_self_eq {n : Type} [Fintype n] (v : n → ℝ) :
    v ⬝ᵥ v = (vecNorm v)^2 := by
  rw [vecNorm_sq]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `vecNorm` 的数乘缩放：`vecNorm (c • v) = |c| * vecNorm v`。 -/
theorem vecNorm_smul {n : Type} [Fintype n] (c : ℝ) (v : n → ℝ) :
    vecNorm (c • v) = |c| * vecNorm v := by
  have hper : ∀ i, (c • v) i ^2 = c^2 * (v i)^2 := by
    intro i; rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  have hsum : (∑ i, (c • v) i ^2) = c^2 * ∑ i, v i ^2 := by
    rw [Finset.sum_congr rfl fun i _ => hper i, ← Finset.mul_sum]
  unfold vecNorm
  rw [hsum, Real.sqrt_mul (sq_nonneg c) _,
      ← sq_abs, Real.sqrt_sq (abs_nonneg c)]

/-- **sum 级 Cauchy–Schwarz（自建）**：`(∑ x i * y i)² ≤ (∑ x i²)(∑ y i²)`
（判别式路线：`∑ (c·x − b·y)² ≥ 0` 展开＋nlinarith 收口，c = ∑y² 分离零例）。 -/
theorem sum_mul_sq_le_sum_sq_mul_sum_sq {n : Type} [Fintype n] (x y : n → ℝ) :
    (∑ i, x i * y i)^2 ≤ (∑ i, (x i)^2) * (∑ i, (y i)^2) := by
  by_cases hc : (∑ i, (y i)^2) = 0
  · have hy0 : ∀ i, y i = 0 := by
      intro i
      have h2 : (y i)^2 = 0 := Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (y i)) |>.mp hc i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp h2
    have hxy0 : ∑ i, x i * y i = 0 := Finset.sum_eq_zero fun i _ => by
      rw [hy0 i, mul_zero]
    rw [hxy0, hc]
    norm_num
  · have hnn : (0:ℝ) ≤ ∑ i, (y i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hcpos : (0:ℝ) < ∑ i, (y i)^2 := lt_of_le_of_ne hnn (Ne.symm hc)
    have h0 : (0:ℝ) ≤ ∑ i,
        ((∑ i, (y i)^2) * x i - (∑ i, x i * y i) * y i)^2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hper : ∀ i, ((∑ i, (y i)^2) * x i - (∑ i, x i * y i) * y i)^2
        = (∑ i, (y i)^2) * (∑ i, (y i)^2) * (x i)^2
          - 2 * (∑ i, (y i)^2) * (∑ i, x i * y i) * (x i * y i)
          + (∑ i, x i * y i) * (∑ i, x i * y i) * (y i)^2 := by
      intro i; ring
    have pull1 : (∑ i, (∑ i, (y i)^2) * (∑ i, (y i)^2) * (x i)^2)
        = (∑ i, (y i)^2) * (∑ i, (y i)^2) * (∑ i, (x i)^2) := by
      rw [← Finset.mul_sum]
    have pull2 : (∑ i, 2 * (∑ i, (y i)^2) * (∑ i, x i * y i) * (x i * y i))
        = 2 * (∑ i, (y i)^2) * (∑ i, x i * y i) * (∑ i, x i * y i) := by
      rw [← Finset.mul_sum]
    have pull3 : (∑ i, (∑ i, x i * y i) * (∑ i, x i * y i) * (y i)^2)
        = (∑ i, x i * y i) * (∑ i, x i * y i) * (∑ i, (y i)^2) := by
      rw [← Finset.mul_sum]
    have hexp : ∑ i,
        ((∑ i, (y i)^2) * x i - (∑ i, x i * y i) * y i)^2
        = (∑ i, (y i)^2) * ((∑ i, (y i)^2) * (∑ i, (x i)^2)
            - (∑ i, x i * y i) * (∑ i, x i * y i)) := by
      rw [Finset.sum_congr rfl fun i _ => hper i, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, pull1, pull2, pull3]
      ring
    have hprod : (0:ℝ) ≤ (∑ i, (y i)^2) * ((∑ i, (y i)^2) * (∑ i, (x i)^2)
        - (∑ i, x i * y i) * (∑ i, x i * y i)) := by rw [← hexp]; exact h0
    have hkey : (∑ i, x i * y i) * (∑ i, x i * y i)
        ≤ (∑ i, (y i)^2) * (∑ i, (x i)^2) := by
      nlinarith [hprod, hcpos]
    calc (∑ i, x i * y i)^2 = (∑ i, x i * y i) * (∑ i, x i * y i) := by ring
      _ ≤ (∑ i, (y i)^2) * (∑ i, (x i)^2) := hkey
      _ = (∑ i, (x i)^2) * (∑ i, (y i)^2) := by ring

/-- **CS 推论**：`|x ⬝ᵥ y| ≤ vecNorm x * vecNorm y`。 -/
theorem abs_dotProduct_le {n : Type} [Fintype n] (x y : n → ℝ) :
    |x ⬝ᵥ y| ≤ vecNorm x * vecNorm y := by
  have h4 : (vecNorm x * vecNorm y)^2 = (∑ i, (x i)^2) * (∑ i, (y i)^2) := by
    rw [mul_pow, vecNorm_sq, vecNorm_sq]
  have h2 : (x ⬝ᵥ y)^2 ≤ (vecNorm x * vecNorm y)^2 := by
    rw [h4]
    exact sum_mul_sq_le_sum_sq_mul_sum_sq x y
  have hb : (0:ℝ) ≤ vecNorm x * vecNorm y :=
    mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  rcases lt_or_ge 0 (x ⬝ᵥ y) with hpx | hpx
  · rw [abs_of_pos hpx]
    nlinarith [h2, hb]
  · rw [abs_of_nonpos hpx]
    nlinarith [h2, hb]

/-! ### Frobenius↔trace 桥（D72-①：自有 frob def 下 entrywise sum 搬运） -/

/-- **Frobenius↔trace 桥·主形**：`(frob M)² = (M * Mᵀ).trace`
（trace=∑diag 展开面；数值上与 `Matrix.frobenius_norm_def` 一致）。 -/
theorem frob_sq_eq_trace {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    (frob M)^2 = (M * Mᵀ).trace := by
  have hnn : (0:ℝ) ≤ ∑ i, ∑ j, (M i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (M i j)
  have h1 : ∀ i, (M * Mᵀ) i i = ∑ j, (M i j)^2 := by
    intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (∑ i, ∑ j, (M i j)^2) = (∑ i, (M * Mᵀ) i i) :=
    Finset.sum_congr rfl fun i _ => (h1 i).symm
  calc (frob M)^2 = (∑ i, ∑ j, (M i j)^2) := by
        unfold frob; rw [Real.sq_sqrt hnn]
    _ = (∑ i, (M * Mᵀ) i i) := h2
    _ = (M * Mᵀ).trace := rfl

/-- **Frobenius↔trace 桥·变体**：`(frob M)² = (Mᵀ * M).trace`
（trace_mul_comm 循环移位）。 -/
theorem frob_sq_eq_trace' {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    (frob M)^2 = (Mᵀ * M).trace := by
  rw [frob_sq_eq_trace, Matrix.trace_mul_comm]

/-- `frob` 转置不变：`frob Mᵀ = frob M`（sum_comm）。 -/
theorem frob_transpose_eq {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    frob Mᵀ = frob M := by
  unfold frob
  apply congrArg Real.sqrt
  have e1 : (∑ i, ∑ j, (Mᵀ i j)^2) = (∑ i, ∑ j, (M j i)^2) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Matrix.transpose_apply]
  rw [e1, Finset.sum_comm]

/-- **步骤 3 的 ‖X*D_⊥ᵀ‖²_F 面**：`(frob (X * Mᵀ))² = ((Xᵀ*X) * (Mᵀ*M)).trace`
（(M*Mᵀ)ᵀ 展开经 transpose_mul＋trace 循环）。 -/
theorem frob_sq_mul_transpose {m n : Type} [Fintype m] [Fintype n]
    (X M : Matrix m n ℝ) :
    (frob (X * Mᵀ))^2 = ((Xᵀ * X) * (Mᵀ * M)).trace := by
  rw [frob_sq_eq_trace]
  have hT : (X * Mᵀ) * (X * Mᵀ)ᵀ = X * Mᵀ * M * Xᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
  have hEq : Xᵀ * (X * Mᵀ * M) = (Xᵀ * X) * (Mᵀ * M) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [hT, Matrix.trace_mul_comm (X * Mᵀ * M) Xᵀ, hEq]

/-! ### Frobenius 三角族（步骤 3 的内积界/三角/反向三角/次乘性） -/

/-- trace＝矩阵内积：`(A * Bᵀ).trace = ∑ i, A i ⬝ᵥ B i`。 -/
theorem trace_mul_transpose_eq_inner {m n : Type} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) : (A * Bᵀ).trace = ∑ i, A i ⬝ᵥ B i := by
  have hent : ∀ i, (A * Bᵀ) i i = A i ⬝ᵥ B i := fun i => rfl
  calc (A * Bᵀ).trace = ∑ i, (A * Bᵀ) i i := rfl
    _ = ∑ i, A i ⬝ᵥ B i := Finset.sum_congr rfl fun i _ => hent i

/-- **矩阵内积界（两级 CS）**：`∑ i (A i ⬝ᵥ B i) ≤ frob A * frob B`。 -/
theorem frob_inner_le {m n : Type} [Fintype m] [Fintype n] (A B : Matrix m n ℝ) :
    (∑ i, A i ⬝ᵥ B i) ≤ frob A * frob B := by
  have h1 : (∑ i, A i ⬝ᵥ B i) ≤ (∑ i, vecNorm (A i) * vecNorm (B i)) := by
    refine Finset.sum_le_sum fun i _ => le_trans (le_abs_self _) ?_
    exact abs_dotProduct_le (A i) (B i)
  have hL : vecNorm (fun i => vecNorm (A i)) = frob A := by
    calc vecNorm (fun i => vecNorm (A i))
        = Real.sqrt (∑ i, (vecNorm (A i))^2) := rfl
      _ = Real.sqrt (∑ i, ∑ j, (A i j)^2) := by
          apply congrArg Real.sqrt
          exact Finset.sum_congr rfl fun i _ => vecNorm_sq (A i)
      _ = frob A := rfl
  have hR : vecNorm (fun i => vecNorm (B i)) = frob B := by
    calc vecNorm (fun i => vecNorm (B i))
        = Real.sqrt (∑ i, (vecNorm (B i))^2) := rfl
      _ = Real.sqrt (∑ i, ∑ j, (B i j)^2) := by
          apply congrArg Real.sqrt
          exact Finset.sum_congr rfl fun i _ => vecNorm_sq (B i)
      _ = frob B := rfl
  have h2 : (∑ i, vecNorm (A i) * vecNorm (B i)) ≤ frob A * frob B := by
    rw [← hL, ← hR]
    refine le_trans (le_abs_self _) ?_
    have hsq : (∑ i, vecNorm (A i) * vecNorm (B i))^2
        ≤ (vecNorm (fun i => vecNorm (A i))
            * vecNorm (fun i => vecNorm (B i)))^2 := by
      have h4 : (vecNorm (fun i => vecNorm (A i))
          * vecNorm (fun i => vecNorm (B i)))^2
          = (∑ i, (vecNorm (A i))^2) * (∑ i, (vecNorm (B i))^2) := by
        rw [mul_pow, vecNorm_sq, vecNorm_sq]
      rw [h4]
      exact sum_mul_sq_le_sum_sq_mul_sum_sq _ _
    have hb : (0:ℝ) ≤ vecNorm (fun i => vecNorm (A i))
        * vecNorm (fun i => vecNorm (B i)) :=
      mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
    rcases lt_or_ge 0 (∑ i, vecNorm (A i) * vecNorm (B i)) with hp | hp
    · rw [abs_of_pos hp]; nlinarith [hsq, hb]
    · rw [abs_of_nonpos hp]; nlinarith [hsq, hb]
  exact le_trans h1 h2

/-- `frob` 取负不变：`frob (-M) = frob M`（neg_sq 逐元）。 -/
theorem frob_neg {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    frob (-M) = frob M := by
  unfold frob
  apply congrArg Real.sqrt
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [Matrix.neg_apply, neg_sq]

/-- **三角不等式**：`frob (A + B) ≤ frob A + frob B`（trace 面：交叉项
`(A*Bᵀ).trace = ∑ A i ⬝ᵥ B i ≤ frob A * frob B`）。 -/
theorem frob_add_le {m n : Type} [Fintype m] [Fintype n] (A B : Matrix m n ℝ) :
    frob (A + B) ≤ frob A + frob B := by
  have hexp : (A + B) * (A + B)ᵀ = A * Aᵀ + A * Bᵀ + (B * Aᵀ + B * Bᵀ) := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  have hBA : (B * Aᵀ).trace = (A * Bᵀ).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hin : (A * Bᵀ).trace = ∑ i, A i ⬝ᵥ B i := trace_mul_transpose_eq_inner A B
  have hcross : (∑ i, A i ⬝ᵥ B i) ≤ frob A * frob B := frob_inner_le A B
  have hTA : (A * Aᵀ).trace = (frob A)^2 := (frob_sq_eq_trace A).symm
  have hTB : (B * Bᵀ).trace = (frob B)^2 := (frob_sq_eq_trace B).symm
  have key : (frob (A + B))^2 ≤ (frob A + frob B)^2 := by
    rw [frob_sq_eq_trace, hexp]
    simp only [Matrix.trace_add]
    rw [hin, hBA, hin]
    nlinarith [hcross, hTA, hTB, mul_nonneg (frob_nonneg A) (frob_nonneg B)]
  calc frob (A + B) = Real.sqrt ((frob (A + B))^2) :=
        (Real.sqrt_sq (frob_nonneg _)).symm
    _ ≤ Real.sqrt ((frob A + frob B)^2) := Real.sqrt_le_sqrt key
    _ = frob A + frob B := Real.sqrt_sq (add_nonneg (frob_nonneg _) (frob_nonneg _))

/-- **反向三角**：`frob A - frob B ≤ frob (A + B)`。 -/
theorem frob_sub_frob_le_add {m n : Type} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) : frob A - frob B ≤ frob (A + B) := by
  have hAB : (A + B) + (-B) = A := by abel
  have h1 : frob A ≤ frob (A + B) + frob B := by
    calc frob A = frob ((A + B) + (-B)) := by rw [hAB]
      _ ≤ frob (A + B) + frob (-B) := frob_add_le _ _
      _ = frob (A + B) + frob B := by rw [frob_neg]
  linarith

/-- **frob 次乘性**：`frob (M * N) ≤ frob M * frob N`（逐元 CS＋
Fintype.sum_mul_sum）。 -/
theorem frob_mul_le {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
    (M : Matrix m n ℝ) (N : Matrix n k ℝ) :
    frob (M * N) ≤ frob M * frob N := by
  have hent : ∀ i k', ((M * N) i k')^2
      ≤ (∑ j, (M i j)^2) * (∑ j, (N j k')^2) := by
    intro i k'
    rw [Matrix.mul_apply]
    exact sum_mul_sq_le_sum_sq_mul_sum_sq (fun j => M i j) (fun j => N j k')
  have h1 : (∑ i, ∑ k', ((M * N) i k')^2)
      ≤ (∑ i, ∑ k', (∑ j, (M i j)^2) * (∑ j, (N j k')^2)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k' _ => hent i k'
  have hSMS : (∑ i, ∑ k', (∑ j, (M i j)^2) * (∑ j, (N j k')^2))
      = (∑ i, ∑ j, (M i j)^2) * (∑ j, ∑ k', (N j k')^2) := by
    have hc2 : (∑ k', ∑ j, (N j k')^2) = (∑ j, ∑ k', (N j k')^2) :=
      Finset.sum_comm
    calc (∑ i, ∑ k', (∑ j, (M i j)^2) * (∑ j, (N j k')^2))
        = (∑ i, ∑ j, (M i j)^2) * (∑ k', ∑ j, (N j k')^2) :=
          (Fintype.sum_mul_sum (fun i => ∑ j, (M i j)^2)
            (fun k' => ∑ j, (N j k')^2)).symm
      _ = (∑ i, ∑ j, (M i j)^2) * (∑ j, ∑ k', (N j k')^2) := by rw [hc2]
  have hsum : (∑ i, ∑ k', ((M * N) i k')^2)
      ≤ (∑ i, ∑ j, (M i j)^2) * (∑ j, ∑ k', (N j k')^2) :=
    le_trans h1 (le_of_eq hSMS)
  have hnnM : (0:ℝ) ≤ ∑ i, ∑ j, (M i j)^2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnnN : (0:ℝ) ≤ ∑ j, ∑ k', (N j k')^2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc frob (M * N) = Real.sqrt (∑ i, ∑ k', ((M * N) i k')^2) := rfl
    _ ≤ Real.sqrt ((∑ i, ∑ j, (M i j)^2) * (∑ j, ∑ k', (N j k')^2)) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (∑ i, ∑ j, (M i j)^2) * Real.sqrt (∑ j, ∑ k', (N j k')^2) :=
        Real.sqrt_mul hnnM _
    _ = frob M * frob N := rfl

/-- **列压缩主件（D72-②路线 (a)：列范数分解，纯 sum 搬运零 WithLp）**：
`(∀ u, vecNorm (M *ᵥ u) ≤ c * vecNorm u) ⇒ frob (M * N) ≤ c * frob N`
（transpose 面：`(Nᵀ*Mᵀ) k i = (M *ᵥ (列k N)) i` 的 mulVec 展开面）。 -/
theorem frob_mul_le_of_vecNorm {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
    (M : Matrix m n ℝ) (N : Matrix n k ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ u : n → ℝ, vecNorm (M *ᵥ u) ≤ c * vecNorm u) :
    frob (M * N) ≤ c * frob N := by
  have hfrobT : frob (M * N) = frob (Nᵀ * Mᵀ) := by
    calc frob (M * N) = frob ((M * N)ᵀ) := (frob_transpose_eq _).symm
      _ = frob (Nᵀ * Mᵀ) := by rw [Matrix.transpose_mul]
  have hent : ∀ k' i, (Nᵀ * Mᵀ) k' i = (M *ᵥ (fun j => N j k')) i := by
    intro k' i
    rw [Matrix.mul_apply]
    show (∑ j, N j k' * M i j) = (∑ j, M i j * N j k')
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcol : ∀ k', (∑ i, ((Nᵀ * Mᵀ) k' i)^2) ≤ c^2 * (∑ j, (N j k')^2) := by
    intro k'
    have hu := h (fun j => N j k')
    have hsumEq : (∑ i, ((M *ᵥ (fun j => N j k')) i)^2)
        = (∑ i, ((Nᵀ * Mᵀ) k' i)^2) :=
      Finset.sum_congr rfl fun i _ => by rw [hent k' i]
    have hsqm : (vecNorm (M *ᵥ (fun j => N j k'))) * (vecNorm (M *ᵥ (fun j => N j k')))
        ≤ (c * vecNorm (fun j => N j k')) * (c * vecNorm (fun j => N j k')) :=
      mul_self_le_mul_self (vecNorm_nonneg _) hu
    rw [← pow_two, ← pow_two, vecNorm_sq, hsumEq] at hsqm
    have hsq' : (c * vecNorm (fun j => N j k'))^2 = c^2 * (∑ j, (N j k')^2) := by
      rw [mul_pow, vecNorm_sq]
    rw [hsq'] at hsqm
    exact hsqm
  have h1 : (∑ k', ∑ i, ((Nᵀ * Mᵀ) k' i)^2) ≤ (∑ k', c^2 * (∑ j, (N j k')^2)) :=
    Finset.sum_le_sum fun k' _ => hcol k'
  have e3 := Finset.mul_sum (Finset.univ) (fun k' => ∑ j, (N j k')^2) (c^2)
  have hc3 : (∑ k', ∑ j, (N j k')^2) = (∑ j, ∑ k', (N j k')^2) :=
    Finset.sum_comm
  have h3 : (∑ k', c^2 * (∑ j, (N j k')^2)) = c^2 * (∑ j, ∑ k', (N j k')^2) := by
    calc (∑ k', c^2 * (∑ j, (N j k')^2)) = c^2 * (∑ k', ∑ j, (N j k')^2) := e3.symm
      _ = c^2 * (∑ j, ∑ k', (N j k')^2) := by rw [hc3]
  have hsum : (∑ k', ∑ i, ((Nᵀ * Mᵀ) k' i)^2) ≤ c^2 * (∑ j, ∑ k', (N j k')^2) :=
    le_trans h1 (le_of_eq h3)
  have hnnN : (0:ℝ) ≤ ∑ j, ∑ k', (N j k')^2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc frob (M * N) = frob (Nᵀ * Mᵀ) := hfrobT
    _ = Real.sqrt (∑ k', ∑ i, ((Nᵀ * Mᵀ) k' i)^2) := rfl
    _ ≤ Real.sqrt (c^2 * (∑ j, ∑ k', (N j k')^2)) := Real.sqrt_le_sqrt hsum
    _ = c * Real.sqrt (∑ j, ∑ k', (N j k')^2) := by
        rw [Real.sqrt_mul (sq_nonneg c) _, Real.sqrt_sq hc]
    _ = c * frob N := rfl

/-! ### Frobenius-Pythagoras（两种口径） -/

/-- **Frobenius-Pythagoras·trace 形**：`tr(A*Bᵀ) = 0 ⇒
`frob(A+B)² = frob A² + frob B²`（混合块正交性的工作口径）。 -/
theorem frob_sq_add_of_trace {m n : Type} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) (h : (A * Bᵀ).trace = 0) :
    (frob (A + B))^2 = (frob A)^2 + (frob B)^2 := by
  rw [frob_sq_eq_trace (A + B), frob_sq_eq_trace A, frob_sq_eq_trace B]
  have hexp : (A + B) * (A + B)ᵀ = A * Aᵀ + A * Bᵀ + (B * Aᵀ + B * Bᵀ) := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  have hBA : (B * Aᵀ).trace = (A * Bᵀ).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hexp]
  simp only [Matrix.trace_add]
  rw [hBA]
  linarith [h]

/-- **Frobenius-Pythagoras·矩阵形（任务书口径）**：`Aᵀ*B = 0 ⇒ 同`
（经 trace_mul_comm 归到 trace 形）。 -/
theorem frob_sq_add_of_mul {m n : Type} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) (h : Aᵀ * B = 0) :
    (frob (A + B))^2 = (frob A)^2 + (frob B)^2 := by
  have key : Bᵀ * A = (Aᵀ * B)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hT2 : ((Aᵀ * B)ᵀ).trace = (Aᵀ * B).trace :=
    Matrix.trace_transpose (Aᵀ * B)
  have h0 : (A * Bᵀ).trace = 0 := by
    rw [Matrix.trace_mul_comm A Bᵀ, key, hT2, h, Matrix.trace_zero]
  exact frob_sq_add_of_trace A B h0

/-! ### PSD trace 族（T1/T2＋翻转；T1/T2 全证明照搬 /tmp/r15c_probe3_trace.lean） -/

/-- **T1 双 PSD 乘积 trace 非负**：`A B 双 Matrix.PosSemidef ⇒ 0 ≤ (A*B).trace`
（CStarAlgebra.nonneg_iff_eq_star_mul_self＋trace 循环移位＋
posSemidef_conjTranspose_mul_self＋trace_nonneg——R15C 探针路线照搬）。 -/
theorem trace_mul_nonneg {n : Type} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨D, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have hcycle : ((Cᴴ * C) * (Dᴴ * D)).trace = ((D * Cᴴ)ᴴ * (D * Cᴴ)).trace := by
    have h1 : ((Cᴴ * C) * (Dᴴ * D)).trace = (Cᴴ * (C * (Dᴴ * D))).trace := by
      rw [Matrix.mul_assoc]
    have h2 : (Cᴴ * (C * (Dᴴ * D))).trace = ((C * (Dᴴ * D)) * Cᴴ).trace :=
      Matrix.trace_mul_comm _ _
    have h3 : ((C * (Dᴴ * D)) * Cᴴ).trace = ((C * Dᴴ) * (D * Cᴴ)).trace := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc]
    have h4 : ((C * Dᴴ) * (D * Cᴴ)).trace = ((D * Cᴴ)ᴴ * (D * Cᴴ)).trace := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [h1, h2, h3, h4]
  show 0 ≤ ((Cᴴ * C) * (Dᴴ * D)).trace
  rw [hcycle]
  exact Matrix.PosSemidef.trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self _)

/-- **T2 线性推论**：`(A − t•1).PosSemidef ⇒ t * B.trace ≤ (A*B).trace`
（l4_procrustes.py 步骤 3 使用的形态）。 -/
theorem trace_ge_smul {n : Type} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (t : ℝ)
    (hA : (A - t • (1 : Matrix n n ℝ)).PosSemidef) (hB : B.PosSemidef) :
    t * B.trace ≤ (A * B).trace := by
  have hsplit : (A * B).trace
      = ((A - t • (1 : Matrix n n ℝ)) * B).trace + t * B.trace := by
    have h : A * B = (A - t • (1 : Matrix n n ℝ)) * B + t • B := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_add_cancel]
    rw [h, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [hsplit]
  exact le_add_of_nonneg_left (trace_mul_nonneg hA hB)

/-- **T2 翻转（上界形）**：`(c•1 − A).PosSemidef ⇒ (A*B).trace ≤ c * B.trace`
（步骤 4 逆压缩的 trace 路线用）。 -/
theorem trace_le_smul {n : Type} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (c : ℝ) (hA : ((c • 1 : Matrix n n ℝ) - A).PosSemidef)
    (hB : B.PosSemidef) : (A * B).trace ≤ c * B.trace := by
  have hsplit : (A * B).trace + (((c • 1 : Matrix n n ℝ) - A) * B).trace
      = c * B.trace := by
    have h : A * B + ((c • 1 : Matrix n n ℝ) - A) * B = c • B := by
      rw [← Matrix.add_mul, add_comm A ((c • 1 : Matrix n n ℝ) - A),
          sub_add_cancel, Matrix.smul_mul, Matrix.one_mul]
    have htr : (A * B + ((c • 1 : Matrix n n ℝ) - A) * B).trace
        = c * B.trace := by
      rw [h, Matrix.trace_smul, smul_eq_mul]
    rw [Matrix.trace_add] at htr
    linarith [htr]
  linarith [trace_mul_nonneg hA hB, hsplit]

/-- **二次型下夹逼 ⇒ PSD**：S 对称＋`∀ v, l*(v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)` ⇒
`(S − l•1).PosSemidef`（dotProduct 口径桥；ℝ 面 star_trivial 归位）。 -/
theorem posSemidef_of_lo {n : Type} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hSym : Sᵀ = S) {l : ℝ}
    (h : ∀ v : n → ℝ, l * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)) :
    (S - l • (1 : Matrix n n ℝ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · have hHer : (S - l • (1 : Matrix n n ℝ)).IsHermitian := by
      rw [IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hSym]
    exact hHer
  · intro v
    have e : ((S - l • (1 : Matrix n n ℝ)) *ᵥ v) = (S *ᵥ v) - l • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hpos : (0:ℝ) ≤ v ⬝ᵥ ((S - l • (1 : Matrix n n ℝ)) *ᵥ v) := by
      rw [e, dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg]
      exact h v
    simpa only [star_trivial] using hpos

/-- **ᵀ 形 PSD 构造子**：`(Aᵀ * A).PosSemidef`（posSemidef_conjTranspose_
mul_self 的 ℝ 面实转换）。 -/
theorem posSemidef_transpose_mul_self {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℝ) : (Aᵀ * A).PosSemidef := by
  have h : (Aᵀ * A) = (Aᴴ * A) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact h ▸ Matrix.posSemidef_conjTranspose_mul_self A

/-! ### 步骤 3 层（混合块：P₀ 恒等式＋块分解＋头条定理一） -/

/-- **P₀ 左吸收**：S := XᵀX 可逆时 `(X*S⁻¹*Xᵀ) * X = X`（S⁻¹*S 归一）。 -/
theorem P0_mul_X {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) * X = X := by
  have hdet : IsUnit (Xᵀ * X).det := (Matrix.isUnit_iff_isUnit_det _).mp hS
  have hSS' : (Xᵀ * X)⁻¹ * (Xᵀ * X) = 1 := Matrix.nonsing_inv_mul (Xᵀ * X) hdet
  calc (X * (Xᵀ * X)⁻¹ * Xᵀ) * X = (X * (Xᵀ * X)⁻¹) * (Xᵀ * X) := by
        rw [← Matrix.mul_assoc]
    _ = X * ((Xᵀ * X)⁻¹ * (Xᵀ * X)) := Matrix.mul_assoc _ _ _
    _ = X := by rw [hSS', Matrix.mul_one]

/-- **P₀ 对称（泛型版）**：`(X*S⁻¹*Xᵀ)ᵀ = X*S⁻¹*Xᵀ`。 -/
theorem P0_transpose {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℝ) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ)ᵀ = X * (Xᵀ * X)⁻¹ * Xᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, gram_transpose, Matrix.mul_assoc]

/-- **P₀ 右吸收**：`Xᵀ * (X*S⁻¹*Xᵀ) = Xᵀ`（S*S⁻¹ 归一）。 -/
theorem XT_mul_P0 {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    Xᵀ * (X * (Xᵀ * X)⁻¹ * Xᵀ) = Xᵀ := by
  have hdet : IsUnit (Xᵀ * X).det := (Matrix.isUnit_iff_isUnit_det _).mp hS
  have hSS : (Xᵀ * X) * (Xᵀ * X)⁻¹ = 1 := Matrix.mul_nonsing_inv (Xᵀ * X) hdet
  have hEq : Xᵀ * (X * (Xᵀ * X)⁻¹ * Xᵀ) = ((Xᵀ * X) * (Xᵀ * X)⁻¹) * Xᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  calc Xᵀ * (X * (Xᵀ * X)⁻¹ * Xᵀ) = ((Xᵀ * X) * (Xᵀ * X)⁻¹) * Xᵀ := hEq
    _ = Xᵀ := by rw [hSS, Matrix.one_mul]

/-- **P₀ 幂等（泛型版，B5a P0_mul_self 的 {m n} 版）**。 -/
theorem P0_mul_self {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹ * Xᵀ) = X * (Xᵀ * X)⁻¹ * Xᵀ := by
  have hPX : (X * (Xᵀ * X)⁻¹ * Xᵀ) * X = X := P0_mul_X X hS
  rw [show (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹ * Xᵀ)
        = ((X * (Xᵀ * X)⁻¹ * Xᵀ) * X) * (Xᵀ * X)⁻¹ * Xᵀ from by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc],
    hPX]

/-- **P₀*D ＝ D_∥**：`P₀ * D = X * (S⁻¹ * (Xᵀ * D))`（纯结合律）。 -/
theorem P0_mul_D {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X D : Matrix m n ℝ) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) * D = X * ((Xᵀ * X)⁻¹ * (Xᵀ * D)) := by
  rw [← Matrix.mul_assoc, Matrix.mul_assoc]

/-- **步骤 3-(viii) 混合块恒等式**：`P₀*E*(1−P₀) = X*D_⊥ᵀ + D_∥*D_⊥ᵀ`
（E := Y*Yᵀ − X*Xᵀ；矩阵级：E_decomp 三项分配＋P₀ 左吸收＋Xᵀ 右零＋DᵀQ 转置）。 -/
theorem mixed_block {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = X * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ
        + (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
  have hP0X : (X * (Xᵀ * X)⁻¹ * Xᵀ) * X = X := P0_mul_X X hS
  have hP0T : (X * (Xᵀ * X)⁻¹ * Xᵀ)ᵀ = X * (Xᵀ * X)⁻¹ * Xᵀ := P0_transpose X
  have hP0D : (X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y - X)
      = X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) := P0_mul_D X (Y - X)
  have hXTQ : Xᵀ * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, XT_mul_P0 X hS, sub_self]
  have hDTQ : (Y - X)ᵀ * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
    have hDP : (Y - X)ᵀ * (X * (Xᵀ * X)⁻¹ * Xᵀ)
        = ((X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y - X))ᵀ := by
      rw [Matrix.transpose_mul, hP0T]
    rw [Matrix.mul_sub, Matrix.mul_one, hDP, hP0D, ← Matrix.transpose_sub]
  rw [E_decomp X Y]
  simp only [Matrix.mul_add, Matrix.add_mul]
  have h1 : (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Y - X)ᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = X * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
    rw [← Matrix.mul_assoc, hP0X, Matrix.mul_assoc, hDTQ]
  have h2 : (X * (Xᵀ * X)⁻¹ * Xᵀ) * ((Y - X) * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = 0 := by
    rw [← Matrix.mul_assoc, hP0D, Matrix.mul_assoc, hXTQ, Matrix.mul_zero]
  have h3 : (X * (Xᵀ * X)⁻¹ * Xᵀ) * ((Y - X) * (Y - X)ᵀ)
        * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP0D, Matrix.mul_assoc, hDTQ,
        ← Matrix.mul_assoc]
  rw [h1, h2, h3, add_zero]


/-- **步骤 3 收口·头条定理一**：S := XᵀX 可逆＋二次型下夹逼
`∀ v, λ₃*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((XᵀX)*ᵥ v)`（λ₃ > 0）⇒
`(√λ₃ − frob D_∥) * frob D_⊥ ≤ frob (Y*Yᵀ − X*Xᵀ)`
（σ₃ = √λ₃ 口径；对应 l4_procrustes.py 步骤 3 的
`(σ₃ − ‖D_∥‖_F)·‖D_⊥‖_F ≤ ‖E‖_F = η`）。 -/
theorem step3_bound {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X))
    {lam3 : ℝ} (hlam3 : 0 < lam3)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)) :
    (Real.sqrt lam3 - frob (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))
      * frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ frob (Y * Yᵀ - X * Xᵀ) := by
  set P := X * (Xᵀ * X)⁻¹ * Xᵀ with hP
  set E1 := Y * Yᵀ - X * Xᵀ with hE1
  set A1 := (Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)) with hA1
  set Dpar := X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) with hDpar
  set Dp := (Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) with hDp
  have hPSD : ((Xᵀ * X) - lam3 • (1 : Matrix n n ℝ)).PosSemidef :=
    posSemidef_of_lo (gram_transpose X) hlo
  have hBPSD : (Dpᵀ * Dp).PosSemidef := by
    rw [hDp]; exact posSemidef_transpose_mul_self _
  have hlow : lam3 * (Dpᵀ * Dp).trace ≤ ((Xᵀ * X) * (Dpᵀ * Dp)).trace :=
    trace_ge_smul lam3 hPSD hBPSD
  have htr2 : (Dpᵀ * Dp).trace = (frob Dp)^2 := (frob_sq_eq_trace' _).symm
  have hXDsq : (frob (X * Dpᵀ))^2 = ((Xᵀ * X) * (Dpᵀ * Dp)).trace :=
    frob_sq_mul_transpose X Dp
  have hkey2 : lam3 * (frob Dp)^2 ≤ (frob (X * Dpᵀ))^2 := by
    rw [hXDsq, ← htr2]
    exact hlow
  have hsqcore : (Real.sqrt lam3 * frob Dp)^2 ≤ (frob (X * Dpᵀ))^2 := by
    rw [mul_pow, Real.sq_sqrt hlam3.le]
    exact hkey2
  have hs3 : Real.sqrt lam3 * frob Dp ≤ frob (X * Dpᵀ) := by
    have hnn : (0:ℝ) ≤ Real.sqrt lam3 * frob Dp :=
      mul_nonneg (Real.sqrt_nonneg _) (frob_nonneg _)
    calc Real.sqrt lam3 * frob Dp
        = Real.sqrt ((Real.sqrt lam3 * frob Dp)^2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((frob (X * Dpᵀ))^2) := Real.sqrt_le_sqrt hsqcore
      _ = frob (X * Dpᵀ) := Real.sqrt_sq (frob_nonneg _)
  have hP0sq : P * (1 - P) = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, P0_mul_self X hS, sub_self]
  have hP0Q : (1 - P) * P = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, P0_mul_self X hS, sub_self]
  have hP0T : Pᵀ = P := by rw [hP]; exact P0_transpose X
  have hOne : P + (1 - P) = (1 : Matrix m m ℝ) := by abel
  have hEdef : E1 * P + E1 * (1 - P) = E1 := by
    rw [← Matrix.mul_add, hOne, Matrix.mul_one]
  have hQdef : E1 * (1 - P) = P * (E1 * (1 - P)) + (1 - P) * (E1 * (1 - P)) := by
    calc E1 * (1 - P) = (P + (1 - P)) * (E1 * (1 - P)) := by rw [hOne, one_mul]
      _ = P * (E1 * (1 - P)) + (1 - P) * (E1 * (1 - P)) := Matrix.add_mul _ _ _
  have hQT : (1 - P)ᵀ = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hP0T]
  have hcross1 : ((E1 * P) * (E1 * (1 - P))ᵀ).trace = 0 := by
    have hT2 : (E1 * (1 - P))ᵀ = (1 - P) * E1ᵀ := by
      rw [Matrix.transpose_mul, hQT]
    have hassoc : (E1 * P) * ((1 - P) * E1ᵀ)
        = E1 * ((P * (1 - P)) * E1ᵀ) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc P (1 - P) E1ᵀ]
    have hprod : (E1 * P) * ((1 - P) * E1ᵀ) = 0 := by
      rw [hassoc, hP0sq, Matrix.zero_mul, Matrix.mul_zero]
    rw [hT2, hprod, Matrix.trace_zero]
  have hpy1 : (frob E1)^2 = (frob (E1 * P))^2 + (frob (E1 * (1 - P)))^2 := by
    rw [← frob_sq_add_of_trace _ _ hcross1, hEdef]
  have hcross2 : ((P * (E1 * (1 - P))) * ((1 - P) * (E1 * (1 - P)))ᵀ).trace
      = 0 := by
    have hT2 : ((1 - P) * (E1 * (1 - P)))ᵀ = (E1 * (1 - P))ᵀ * (1 - P) := by
      rw [Matrix.transpose_mul, hQT]
    have hprod : ((E1 * (1 - P))ᵀ * (1 - P)) * (P * (E1 * (1 - P))) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P) P (E1 * (1 - P)),
          hP0Q, Matrix.zero_mul, Matrix.mul_zero]
    have hcycle : ((P * (E1 * (1 - P))) * ((E1 * (1 - P))ᵀ * (1 - P))).trace
        = (((E1 * (1 - P))ᵀ * (1 - P)) * (P * (E1 * (1 - P)))).trace :=
      Matrix.trace_mul_comm _ _
    rw [hT2, hcycle, hprod, Matrix.trace_zero]
  have hpy2 : (frob (E1 * (1 - P)))^2
      = (frob (P * (E1 * (1 - P))))^2 + (frob ((1 - P) * (E1 * (1 - P))))^2 := by
    rw [← frob_sq_add_of_trace _ _ hcross2, ← hQdef]
  have hmix : P * (E1 * (1 - P)) = X * Dpᵀ + Dpar * Dpᵀ := by
    rw [hP, hE1, hDpar, hDp, ← Matrix.mul_assoc]
    exact mixed_block X Y hS
  have hEQ : (frob (P * (E1 * (1 - P))))^2 ≤ (frob E1)^2 := by
    linarith [hpy1, hpy2, sq_nonneg (frob ((1 - P) * (E1 * (1 - P)))),
      sq_nonneg (frob (E1 * P))]
  have hEge : frob (P * (E1 * (1 - P))) ≤ frob E1 := by
    calc frob (P * (E1 * (1 - P)))
        = Real.sqrt ((frob (P * (E1 * (1 - P))))^2) :=
          (Real.sqrt_sq (frob_nonneg _)).symm
      _ ≤ Real.sqrt ((frob E1)^2) := Real.sqrt_le_sqrt hEQ
      _ = frob E1 := Real.sqrt_sq (frob_nonneg _)
  have hrev : frob (X * Dpᵀ) - frob (Dpar * Dpᵀ) ≤ frob (X * Dpᵀ + Dpar * Dpᵀ) :=
    frob_sub_frob_le_add _ _
  have hsub : frob (Dpar * Dpᵀ) ≤ frob Dpar * frob Dp := by
    calc frob (Dpar * Dpᵀ) ≤ frob Dpar * frob (Dpᵀ) := frob_mul_le _ _
      _ = frob Dpar * frob Dp := by rw [frob_transpose_eq]
  rw [← hmix] at hrev
  have hexp : (Real.sqrt lam3 - frob Dpar) * frob Dp
      = Real.sqrt lam3 * frob Dp - frob Dpar * frob Dp := by ring
  linarith [hEge, hrev, hsub, hs3]

/-! ### 步骤 4 层（平行块：B 三恒等式＋逆压缩＋头条定理二） -/

/-- **Xᵀ*D ＝ S*A'**：`(Xᵀ*X) * ((Xᵀ*X)⁻¹ * (Xᵀ*D)) = Xᵀ*D`
（mul_nonsing_inv_cancel_left 归一）。 -/
theorem XT_D_eq {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X D : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    (Xᵀ * X) * ((Xᵀ * X)⁻¹ * (Xᵀ * D)) = Xᵀ * D := by
  have hdet : IsUnit (Xᵀ * X).det := (Matrix.isUnit_iff_isUnit_det _).mp hS
  exact Matrix.mul_nonsing_inv_cancel_left (Xᵀ * X) (Xᵀ * D) hdet

/-- **步骤 4-(ix) B 恒等式一**：`A + Aᵀ + A*Aᵀ = (1+A)*(1+A)ᵀ − 1`
（A := (XᵀX)⁻¹*(XᵀD)；矩阵级分配＋abel）。 -/
theorem B_eq_factor {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))
        + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ
        + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))
          * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ
      = (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ - 1 := by
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  abel

/-- **步骤 4-(x) B 恒等式二**：`Xᵀ*E*X = S*(A+Aᵀ+A*Aᵀ)*S`
（E 三交叉分解逐块分配＋Xᵀ*D = S*A' 归一）。 -/
theorem XTEX_eq_SBS {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    Xᵀ * (Y * Yᵀ - X * Xᵀ) * X
      = (Xᵀ * X) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))
          + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ
          + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))
            * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) * (Xᵀ * X) := by
  set S := Xᵀ * X with hSdef
  set A1 := (Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)) with hA1
  have hSA1 : S * A1 = Xᵀ * (Y - X) := XT_D_eq X (Y - X) hS
  have hDTX : (Y - X)ᵀ * X = A1ᵀ * S := by
    rw [hA1]
    have e4 : (Xᵀ * (Y - X))ᵀ = (Y - X)ᵀ * X := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have e1 := XT_D_eq X (Y - X) hS
    calc (Y - X)ᵀ * X = (Xᵀ * (Y - X))ᵀ := e4.symm
      _ = ((Xᵀ * X) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by rw [e1]
      _ = ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ * (Xᵀ * X)ᵀ := Matrix.transpose_mul _ _
      _ = ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ * (Xᵀ * X) := by rw [gram_transpose]
  have p1 : Xᵀ * (X * (Y - X)ᵀ) * X = S * A1ᵀ * S := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hDTX, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc]
  have p2 : Xᵀ * ((Y - X) * Xᵀ) * X = S * A1 * S := by
    rw [← Matrix.mul_assoc, hSA1, Matrix.mul_assoc]
  have hAA : S * (A1 * A1ᵀ) * S = S * A1 * (A1ᵀ * S) := by
    rw [Matrix.mul_assoc S (A1 * A1ᵀ) S,
        Matrix.mul_assoc A1 A1ᵀ S,
        ← Matrix.mul_assoc S A1 (A1ᵀ * S)]
  have p3 : Xᵀ * ((Y - X) * (Y - X)ᵀ) * X = S * A1 * (A1ᵀ * S) := by
    calc Xᵀ * ((Y - X) * (Y - X)ᵀ) * X
        = (Xᵀ * (Y - X)) * ((Y - X)ᵀ * X) := by
          rw [← Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (S * A1) * ((Y - X)ᵀ * X) := by rw [← hSA1]
      _ = (S * A1) * (A1ᵀ * S) := by rw [hDTX]
      _ = S * A1 * (A1ᵀ * S) := rfl
  rw [E_decomp X Y, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_mul, p1, p2, p3]
  simp only [Matrix.mul_add, Matrix.add_mul]
  rw [hAA]
  abel

/-- **步骤 4-(xi) B 恒等式三**：`B = S⁻¹*(Xᵀ*E*X)*S⁻¹`
（B 恒等式二＋S⁻¹*S 双侧归一）。 -/
theorem B_eq_inv {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))
        + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ
        + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))
          * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)
      = (Xᵀ * X)⁻¹ * (Xᵀ * (Y * Yᵀ - X * Xᵀ) * X) * (Xᵀ * X)⁻¹ := by
  have hdet : IsUnit (Xᵀ * X).det := (Matrix.isUnit_iff_isUnit_det _).mp hS
  have hSS' : (Xᵀ * X)⁻¹ * (Xᵀ * X) = 1 := Matrix.nonsing_inv_mul (Xᵀ * X) hdet
  have hSS : (Xᵀ * X) * (Xᵀ * X)⁻¹ = 1 := Matrix.mul_nonsing_inv (Xᵀ * X) hdet
  have hcalc : ∀ (Z : Matrix n n ℝ),
      ((Xᵀ * X)⁻¹) * (((Xᵀ * X) * Z) * (Xᵀ * X)) * (Xᵀ * X)⁻¹ = Z := by
    intro Z
    calc (Xᵀ * X)⁻¹ * (((Xᵀ * X) * Z) * (Xᵀ * X)) * (Xᵀ * X)⁻¹
        = (((Xᵀ * X)⁻¹ * ((Xᵀ * X) * Z)) * (Xᵀ * X)) * (Xᵀ * X)⁻¹ := by
          rw [← Matrix.mul_assoc (Xᵀ * X)⁻¹ ((Xᵀ * X) * Z) (Xᵀ * X)]
      _ = ((((Xᵀ * X)⁻¹ * (Xᵀ * X)) * Z) * (Xᵀ * X)) * (Xᵀ * X)⁻¹ := by
          rw [← Matrix.mul_assoc (Xᵀ * X)⁻¹ (Xᵀ * X) Z]
      _ = ((1 * Z) * (Xᵀ * X)) * (Xᵀ * X)⁻¹ := by rw [hSS']
      _ = (Z * (Xᵀ * X)) * (Xᵀ * X)⁻¹ := by rw [Matrix.one_mul]
      _ = Z * ((Xᵀ * X) * (Xᵀ * X)⁻¹) := by rw [Matrix.mul_assoc]
      _ = Z * 1 := by rw [hSS]
      _ = Z := Matrix.mul_one _
  rw [XTEX_eq_SBS X Y hS, hcalc _]

/-- **逆压缩·向量层（C1）**：S 对称可逆＋二次型下夹逼（λ₃ > 0）⇒
`vecNorm (S⁻¹ *ᵥ v) ≤ vecNorm v / λ₃`（vecNorm＋Cauchy–Schwarz 路线，
特征值无关）。 -/
theorem vecNorm_inv_mulVec_le {n : Type} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℝ) (hS : IsUnit S) (hSym : Sᵀ = S) {lam3 : ℝ}
    (hlam3 : 0 < lam3)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)) (v : n → ℝ) :
    vecNorm (S⁻¹ *ᵥ v) ≤ vecNorm v / lam3 := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hinv : S *ᵥ (S⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hdet, Matrix.one_mulVec]
  by_cases hw0 : S⁻¹ *ᵥ v = 0
  · have hz : vecNorm (S⁻¹ *ᵥ v) = 0 := by
      rw [hw0]; show Real.sqrt (∑ i : n, (0 : ℝ) ^2) = 0; simp
    rw [hz]
    exact div_nonneg (vecNorm_nonneg v) hlam3.le
  · have hW : lam3 * ((vecNorm (S⁻¹ *ᵥ v))^2) ≤ (S⁻¹ *ᵥ v) ⬝ᵥ v := by
      have h1 := hlo (S⁻¹ *ᵥ v)
      rw [hinv, dotProduct_self_eq] at h1
      exact h1
    have hCS : (S⁻¹ *ᵥ v) ⬝ᵥ v
        ≤ vecNorm (S⁻¹ *ᵥ v) * vecNorm v := by
      refine le_trans (le_abs_self _) ?_
      exact abs_dotProduct_le (S⁻¹ *ᵥ v) v
    have hpos : (0:ℝ) < vecNorm (S⁻¹ *ᵥ v) := by
      by_contra hcon
      push_neg at hcon
      apply hw0
      have h2 : ∑ i, ((S⁻¹ *ᵥ v) i)^2 = 0 := by
        have h3 := vecNorm_sq (S⁻¹ *ᵥ v)
        rw [le_antisymm hcon (vecNorm_nonneg _)] at h3
        linarith
      funext i
      have h4 : ((S⁻¹ *ᵥ v) i)^2 = 0 := Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg ((S⁻¹ *ᵥ v) i)) |>.mp h2 i (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h4
    rw [le_div_iff₀ hlam3]
    nlinarith [hW, hCS, hpos, hlam3, mul_pos hpos hlam3]

/-- **对偶夹逼界（步骤 4 的 λ₁ 面）**：上夹逼
`∀ v, v ⬝ᵥ ((XᵀX)*ᵥ v) ≤ λ₁*(v ⬝ᵥ v)`（λ₁ ≥ 0）⇒
`vecNorm (Xᵀ *ᵥ u) ≤ √λ₁ * vecNorm u`（对偶见证 w = (1/‖Xᵀu‖)•Xᵀu 的
CS 一击，零 sup/算子范数 API）。 -/
theorem vecNorm_transpose_mulVec_le {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] (X : Matrix m n ℝ) {lam1 : ℝ} (hlam1 : 0 ≤ lam1)
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v))
    (u : m → ℝ) :
    vecNorm (Xᵀ *ᵥ u) ≤ Real.sqrt lam1 * vecNorm u := by
  have hadj : ∀ w : n → ℝ, w ⬝ᵥ (Xᵀ *ᵥ u) = (X *ᵥ w) ⬝ᵥ u := by
    intro w
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hsq : ∀ w : n → ℝ, (vecNorm (X *ᵥ w))^2 ≤ lam1 * (vecNorm w)^2 := by
    intro w
    have h1 := hhi w
    rw [TableB5Core.quadsum_eq X w, dotProduct_self_eq] at h1
    have e1 : ∀ i, (X *ᵥ w) i = X i ⬝ᵥ w := fun i => rfl
    have hL : ∑ i, (X i ⬝ᵥ w)^2 = (vecNorm (X *ᵥ w))^2 := by
      calc ∑ i, (X i ⬝ᵥ w)^2 = ∑ i, ((X *ᵥ w) i)^2 :=
            Finset.sum_congr rfl fun i _ => by rw [e1]
        _ = (vecNorm (X *ᵥ w))^2 := (vecNorm_sq _).symm
    rw [hL] at h1
    exact h1
  by_cases hu : Xᵀ *ᵥ u = 0
  · have hz : vecNorm (Xᵀ *ᵥ u) = 0 := by
      rw [hu]; simp [vecNorm]
    rw [hz]
    exact mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg _)
  · have hpos : (0:ℝ) < vecNorm (Xᵀ *ᵥ u) := by
      by_contra hcon
      push_neg at hcon
      apply hu
      have h2 : ∑ i, ((Xᵀ *ᵥ u) i)^2 = 0 := by
        have h3 := vecNorm_sq (Xᵀ *ᵥ u)
        rw [le_antisymm hcon (vecNorm_nonneg _)] at h3
        linarith
      funext i
      have h4 : ((Xᵀ *ᵥ u) i)^2 = 0 := Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg ((Xᵀ *ᵥ u) i)) |>.mp h2 i (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h4
    set w := ((vecNorm (Xᵀ *ᵥ u))⁻¹) • (Xᵀ *ᵥ u) with hw
    have hw1 : vecNorm w = 1 := by
      rw [hw, vecNorm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀
        (ne_of_gt hpos)]
    have hw2 : w ⬝ᵥ (Xᵀ *ᵥ u) = vecNorm (Xᵀ *ᵥ u) := by
      have e1 : (Xᵀ *ᵥ u) ⬝ᵥ (Xᵀ *ᵥ u) = (vecNorm (Xᵀ *ᵥ u))^2 :=
        dotProduct_self_eq _
      calc w ⬝ᵥ (Xᵀ *ᵥ u)
          = ((vecNorm (Xᵀ *ᵥ u))⁻¹) • ((Xᵀ *ᵥ u) ⬝ᵥ (Xᵀ *ᵥ u)) := by
            rw [hw, smul_dotProduct]
        _ = ((vecNorm (Xᵀ *ᵥ u))⁻¹) • ((vecNorm (Xᵀ *ᵥ u))^2) := by rw [e1]
        _ = vecNorm (Xᵀ *ᵥ u) := by
            rw [smul_eq_mul, pow_two, ← mul_assoc,
                inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    have hw3 := hadj w
    have hw4 := abs_dotProduct_le (X *ᵥ w) u
    have hw5' : (vecNorm (X *ᵥ w))^2 ≤ lam1 := by
      have hw5 := hsq w
      rw [hw1, one_pow, mul_one] at hw5
      exact hw5
    have hbound : vecNorm (X *ᵥ w) ≤ Real.sqrt lam1 := by
      have hs2 : (vecNorm (X *ᵥ w))^2 ≤ (Real.sqrt lam1)^2 := by
        rw [Real.sq_sqrt hlam1]; exact hw5'
      calc vecNorm (X *ᵥ w) = Real.sqrt ((vecNorm (X *ᵥ w))^2) :=
            (Real.sqrt_sq (vecNorm_nonneg _)).symm
        _ ≤ Real.sqrt ((Real.sqrt lam1)^2) := Real.sqrt_le_sqrt hs2
        _ = Real.sqrt lam1 := Real.sqrt_sq (Real.sqrt_nonneg _)
    have hkey : vecNorm (Xᵀ *ᵥ u) ≤ vecNorm (X *ᵥ w) * vecNorm u := by
      have e1 : w ⬝ᵥ (Xᵀ *ᵥ u) ≤ vecNorm (X *ᵥ w) * vecNorm u := by
        rw [hadj w]
        exact le_trans (le_abs_self _) hw4
      rw [hw2] at e1
      exact e1
    calc vecNorm (Xᵀ *ᵥ u) ≤ vecNorm (X *ᵥ w) * vecNorm u := hkey
      _ ≤ Real.sqrt lam1 * vecNorm u :=
          mul_le_mul_of_nonneg_right hbound (vecNorm_nonneg _)

/-- **步骤 4 中间步**：`frob (Xᵀ*E*X) ≤ λ₁ * frob E`（列压缩＋对偶夹逼，
Frobenius↔L2op 比较件的自有 def 面）。 -/
theorem frob_XTEX_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X : Matrix m n ℝ) (E : Matrix m m ℝ) {lam1 : ℝ}
    (hlam1 : 0 ≤ lam1)
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v)) :
    frob (Xᵀ * E * X) ≤ lam1 * frob E := by
  have hXT := vecNorm_transpose_mulVec_le X hlam1 hhi
  have h1 : frob (Xᵀ * (E * X)) ≤ Real.sqrt lam1 * frob (E * X) :=
    frob_mul_le_of_vecNorm Xᵀ (E * X) (Real.sqrt lam1) (Real.sqrt_nonneg _) hXT
  have h2 : frob (E * X) ≤ Real.sqrt lam1 * frob E := by
    have hEXT : (E * X)ᵀ = Xᵀ * Eᵀ := Matrix.transpose_mul E X
    calc frob (E * X) = frob ((E * X)ᵀ) := (frob_transpose_eq _).symm
      _ = frob (Xᵀ * Eᵀ) := by rw [hEXT]
      _ ≤ Real.sqrt lam1 * frob Eᵀ :=
          frob_mul_le_of_vecNorm Xᵀ Eᵀ (Real.sqrt lam1) (Real.sqrt_nonneg _) hXT
      _ = Real.sqrt lam1 * frob E := by rw [frob_transpose_eq]
  calc frob (Xᵀ * E * X) = frob (Xᵀ * (E * X)) := by rw [Matrix.mul_assoc]
    _ ≤ Real.sqrt lam1 * frob (E * X) := h1
    _ ≤ Real.sqrt lam1 * (Real.sqrt lam1 * frob E) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = lam1 * frob E := by
        rw [← mul_assoc, ← pow_two, Real.sq_sqrt hlam1]

/-- **逆压缩·Frobenius 层（C2）**：S 对称可逆＋二次型下夹逼（λ₃ > 0）⇒
`frob (S⁻¹*M*S⁻¹) ≤ frob M / λ₃²`（向量层压缩 C1＋列压缩主件两次：
S⁻¹*(M*S⁻¹) 与 (M*S⁻¹)ᵀ = S⁻¹*Mᵀ，零 trace 循环）。 -/
theorem frob_inv_mul_inv_le {n : Type} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℝ) (hS : IsUnit S) (hSym : Sᵀ = S) {lam3 : ℝ}
    (hlam3 : 0 < lam3)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v))
    (M : Matrix n n ℝ) :
    frob (S⁻¹ * M * S⁻¹) ≤ frob M / lam3^2 := by
  have hA : ∀ u : n → ℝ, vecNorm (S⁻¹ *ᵥ u) ≤ (lam3)⁻¹ * vecNorm u := by
    intro u
    rw [← div_eq_inv_mul]
    exact vecNorm_inv_mulVec_le S hS hSym hlam3 hlo u
  have hc : (0:ℝ) ≤ (lam3)⁻¹ := inv_nonneg.mpr hlam3.le
  have h2 : frob (M * S⁻¹) ≤ (lam3)⁻¹ * frob M := by
    have hEq : frob (M * S⁻¹) = frob (S⁻¹ * Mᵀ) := by
      calc frob (M * S⁻¹) = frob ((M * S⁻¹)ᵀ) := (frob_transpose_eq _).symm
        _ = frob ((S⁻¹)ᵀ * Mᵀ) := by rw [Matrix.transpose_mul]
        _ = frob (S⁻¹ * Mᵀ) := by rw [Matrix.transpose_nonsing_inv, hSym]
    rw [hEq]
    calc frob (S⁻¹ * Mᵀ) ≤ (lam3)⁻¹ * frob Mᵀ :=
          frob_mul_le_of_vecNorm S⁻¹ Mᵀ ((lam3)⁻¹) hc hA
      _ = (lam3)⁻¹ * frob M := by rw [frob_transpose_eq]
  calc frob (S⁻¹ * M * S⁻¹) = frob (S⁻¹ * (M * S⁻¹)) := by rw [Matrix.mul_assoc]
    _ ≤ (lam3)⁻¹ * frob (M * S⁻¹) :=
        frob_mul_le_of_vecNorm S⁻¹ (M * S⁻¹) ((lam3)⁻¹) hc hA
    _ ≤ (lam3)⁻¹ * ((lam3)⁻¹ * frob M) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = frob M / lam3^2 := by
        rw [div_eq_inv_mul, ← mul_assoc, ← mul_inv, ← pow_two]

/-- **步骤 4 收口·头条定理二**：S := XᵀX 可逆＋下/上二次型夹逼（λ₃ > 0,
λ₁ ≥ 0）⇒ `frob B ≤ λ₁ * frob (Y*Yᵀ − X*Xᵀ) / λ₃²`
（B := A+Aᵀ+A*Aᵀ，β := λ₁η/λ₃² 口径；对应 l4_procrustes.py 步骤 4）。 -/
theorem step4_bound {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X))
    {lam3 lam1 : ℝ} (hlam3 : 0 < lam3) (hlam1 : 0 ≤ lam1)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v)) :
    frob ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))
        + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ
        + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))
          * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)
      ≤ lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 := by
  have hComp : frob ((Xᵀ * X)⁻¹ * (Xᵀ * (Y * Yᵀ - X * Xᵀ) * X) * (Xᵀ * X)⁻¹)
      ≤ frob (Xᵀ * (Y * Yᵀ - X * Xᵀ) * X) / lam3^2 :=
    frob_inv_mul_inv_le (Xᵀ * X) hS (gram_transpose X) hlam3 hlo _
  have hMid : frob (Xᵀ * (Y * Yᵀ - X * Xᵀ) * X)
      ≤ lam1 * frob (Y * Yᵀ - X * Xᵀ) :=
    frob_XTEX_le X (Y * Yᵀ - X * Xᵀ) hlam1 hhi
  rw [B_eq_inv X Y hS]
  exact le_trans hComp (div_le_div_of_nonneg_right hMid (sq_nonneg lam3))

/-! ### TTP 实例化层（TableB5 常数接线；l3/u1 来自 TableB5Data） -/

/-- TTP 矩阵二次型下夹逼·向量口径：z 盒内 `l₃*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((ttpXᵀ*ttpX)*ᵥ v)`
（TableB5.ttp_sandwich_lo＋B5a ttpX_quadform 合并）。 -/
theorem ttpX_quadform_lo (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (v : Fin 3 → ℝ) :
    (l3:ℝ) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((ttpX z)ᵀ * ttpX z) *ᵥ v) := by
  have hvv : v ⬝ᵥ v = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
    rw [dotProduct, Fin.sum_univ_three]; ring
  rw [hvv, TableB5Core.ttpX_quadform z v]
  exact TableB5.ttp_sandwich_lo z (v 0) (v 1) (v 2) h1 h2

/-- TTP 矩阵二次型上夹逼·向量口径：z 盒内
`v ⬝ᵥ ((ttpXᵀ*ttpX)*ᵥ v) ≤ u₁*(v ⬝ᵥ v)`。 -/
theorem ttpX_quadform_hi (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (v : Fin 3 → ℝ) :
    v ⬝ᵥ (((ttpX z)ᵀ * ttpX z) *ᵥ v) ≤ (u1:ℝ) * (v ⬝ᵥ v) := by
  have hvv : v ⬝ᵥ v = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
    rw [dotProduct, Fin.sum_univ_three]; ring
  rw [TableB5Core.ttpX_quadform z v, hvv]
  exact TableB5.ttp_sandwich_hi z (v 0) (v 1) (v 2) h1 h2

/-- **TTP 实例化·头条一**：z 盒内对一切行构型 Y，
`(√l₃ − frob D_∥)*frob D_⊥ ≤ frob (Y*Yᵀ − ttpX*ttpXᵀ)`。 -/
theorem ttpX_step3 (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ) :
    (Real.sqrt (l3:ℝ) - frob (ttpX z * (((ttpX z)ᵀ * ttpX z)⁻¹
          * ((ttpX z)ᵀ * (Y - ttpX z)))))
      * frob ((Y - ttpX z) - ttpX z * (((ttpX z)ᵀ * ttpX z)⁻¹
          * ((ttpX z)ᵀ * (Y - ttpX z))))
      ≤ frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) :=
  step3_bound (ttpX z) Y (ttpX_isUnit z h1 h2)
    (by norm_num [l3] : (0:ℝ) < (l3:ℝ)) (ttpX_quadform_lo z h1 h2)

/-- **TTP 实例化·头条二**：z 盒内对一切行构型 Y，
`frob B ≤ u₁ * frob (Y*Yᵀ − ttpX*ttpXᵀ) / l₃²`。 -/
theorem ttpX_step4 (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ) :
    frob ((((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z))
          + (((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z)))ᵀ
          + ((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z))
            * (((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z)))ᵀ))
      ≤ (u1:ℝ) * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2 :=
  step4_bound (ttpX z) Y (ttpX_isUnit z h1 h2)
    (by norm_num [l3] : (0:ℝ) < (l3:ℝ)) (by norm_num [u1] : (0:ℝ) ≤ (u1:ℝ))
    (ttpX_quadform_lo z h1 h2) (ttpX_quadform_hi z h1 h2)

end ThomsonN9.TableB5Trace
