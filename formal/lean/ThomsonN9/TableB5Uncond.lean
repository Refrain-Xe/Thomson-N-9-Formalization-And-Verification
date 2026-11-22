import Mathlib
import ThomsonN9.TableB5
import ThomsonN9.TableB5Core
import ThomsonN9.TableB5Trace
import ThomsonN9.TableB5Polar

/-!
# Table B5Uncond (R19A / r19a): the unconditional step-6 assembly —
# two-tier unconditional d_P bounds (global ½-Hölder + narrow-domain linear)

This file is the seventh piece of Table B — the **unconditionalisation of
B5c step 6** (D82 rulings 1/2/3).  It replaces the reflection-family-fragile
implicit premise `frob D_∥ ≤ σ₁β` (D77-2: not a consequence of the theorem's
premises — the written chain of `l4_procrustes.py` step 6 breaks there) by
two unconditional tiers, both **carrying no `hdpar` premise**:

* **Route B (global ½-Hölder tier).**  `step6_uncond_hoelder`: under the
  λ-sandwich (`lam3 > 0`, `hlo`, `hhi`) and the *true domain* condition
  `β := λ₁η/λ₃² ≤ 1/2` (η := frob (Y*Yᵀ − X*Xᵀ); `frob B ≤ β` supplied by
  the in-library `step4_bound`), there is `Q ∈ Matrix.orthogonalGroup` with
  `frob (X − Y*Q) ≤ √λ₁·β + √(3·η)`.  The `√(3η)` face is the seven-step
  chain `t² = tr(D_⊥D_⊥ᵀ) = tr(E(1−P₀)) ≤ 3η` (block identity 2 + trace
  cycling + P₀-idempotence + trace-CS + op(1−P₀) ≤ 1).  The corollary
  `step6_hoelder_Cform` converts to the δ-calibre
  `d_P ≤ C_B·√δ` with `C_B = k1·√δ_max + √(3·√72Up)`,
  `k1 := s1Up·u₁·√72Up/l₃²` — **valid on the whole recorded δ ≤ δ_max
  domain** (the β ≤ 1/2 premise is *derived* from `TableB5.delta_max_valid`,
  not carried).

* **Route A (σ₃(Y)-bootstrap narrow-domain linear tier).**  With
  `A := (XᵀX)⁻¹(Xᵀ(Y−X))`, `B := A+Aᵀ+AAᵀ`, `t := frob D_⊥`,
  `c := √(λ₃(1−β))`: the frob-symmetric face `frob (Aᵀ+A+AᵀA) = frob B`
  (probe-2 A2), the row-CS lower bound `(1−β)(v⬝ᵥv) ≤ ‖((1+A)*ᵥv)²‖` (A4),
  the assembly + reverse triangle `c·‖v‖ − ‖D_⊥*ᵥv‖ ≤ ‖((X(1+A)+D_⊥)*ᵥv)‖`
  (A7, giving λ₃(Y) ≥ (c−t)² on quadratic forms), `‖Y·D_⊥ᵀ‖_F ≤ η` (A8,
  block identity 1 + op(1−P₀) ≤ 1), the λ₃(Y)-compression
  `λ₃(Y)·t² ≤ ‖Y·D_⊥ᵀ‖²_F` (A9, `trace_ge_smul` with S_Y := YᵀY), and the
  closure disambiguation (A10): under the narrow domain `η ≤ λ₃/24`
  (c_lo := √(λ₃/2) envelope calibre, D79-5) the ½-Hölder face forces
  `t ≤ √(3η) ≤ c/2`, so `(c−t)t ≤ η` and a contradiction argument against
  `t > 2η/c` close `t ≤ 2η/c ≤ 2√2·η/√λ₃`.  `step6_uncond_linear` assembles
  (A11): `d_P ≤ (√λ₁·λ₁/λ₃² + 2√2/√λ₃)·η` — **linear in η, narrow domain,
  no `hdpar`**.

* **TTP instantiation.**  `ttpX_step6_hoelder` / `ttpX_step6_linear` wire
  the z-box (`zLo ≤ z ≤ zHi`) through `ttpX_quadform_lo/hi` with the
  `(l3:ℝ)`/`(u1:ℝ)` literals.

Layer 1 (shared faces, D82-1): the two block identities
`E(1−P₀) = Y·D_⊥ᵀ` and `(1−P₀)E(1−P₀) = D_⊥·D_⊥ᵀ` (R18B probe 1, abstract
P₀-face versions + the concrete bridge via the in-library P₀ hexahedron
`P0_mul_X`/`P0_transpose`/`XT_mul_P0`/`P0_mul_self`/`P0_mul_D` of
`TableB5Trace`); the op(1−P₀) ≤ 1 quadratic-form face (symmetric idempotent
⟹ ‖(1−P₀)*ᵥu‖ ≤ ‖u‖); and the trace-CS face
`|tr M| ≤ √(Fintype.card n)·frob M` (sum-level CS with ones; the sharp
`√card` calibre makes the 9-row instantiation exactly `3`, matching the
R18B P4 constant audit `C_B = k1√δ_max + √(3√72)`).

The R18A conditional layer (`TableB5Polar.step6_final`, three explicit
premises) is kept untouched as a rollback intermediate (D78-4/D82-1).

**Statement-face decisions (D83, recorded in notes/tableb-lean.md §7):**
route-B/A head statements specialise the row type to `Fin 9` (the "3" of
`√(3η)` is `√(Fintype.card (Fin 9))`; generic lemmas stay polymorphic);
all constants are expressed through `TableB5Data` defs (`l3`/`u1`/`s1Up`/
`sqrt72Up`/`deltaMax`) — zero numeric data literals, no Data file.  The
machine-checkable no-`hdpar` calibre (D82-3): the statement spans of the
two unconditional head theorems and their TTP instantiations contain no
`frob (X * ((Xᵀ * X)⁻¹ …` pattern (no D_∥-norm premise of any shape).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5Uncond

open Matrix
open ThomsonN9.TableB5Data
open ThomsonN9.TableB5Core
open ThomsonN9.TableB5Trace
open ThomsonN9.TableB5Polar

/-! ### 层 1：共享面（块恒等式双例＋op(1−P₀) ≤ 1＋trace-CS＋½-Hölder 面） -/

/-- **块恒等式例 1·抽象 P₀ 面**（R18B 探针 1 例 1 源转录，D82-1）：
P₀ 对称＋P₀*X = X＋P₀*D_⊥ = 0＋D_∥ = X*A＋Y = X + D_∥ + D_⊥ ⇒
`E*(1−P₀) = Y*D_⊥ᵀ`（E := Y*Yᵀ − X*Xᵀ；幂等性不需要）。 -/
theorem E_mul_one_sub_P0_of {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    {X Y Dpar Dperp : Matrix m n ℝ} {A : Matrix n n ℝ} {P0 : Matrix m m ℝ}
    (hP0T : P0ᵀ = P0) (hP0X : P0 * X = X) (hP0Dperp : P0 * Dperp = 0)
    (hDpar : Dpar = X * A) (hY : Y = X + Dpar + Dperp) :
    (Y * Yᵀ - X * Xᵀ) * (1 - P0) = Y * Dperpᵀ := by
  have hXt : Xᵀ * P0 = Xᵀ := by
    have h := congrArg Matrix.transpose hP0X
    rwa [Matrix.transpose_mul, hP0T] at h
  have hXT : Xᵀ * (1 - P0) = 0 := by
    calc Xᵀ * (1 - P0) = Xᵀ * 1 - Xᵀ * P0 := Matrix.mul_sub _ _ _
      _ = Xᵀ - Xᵀ * P0 := by rw [Matrix.mul_one]
      _ = Xᵀ - Xᵀ := by rw [hXt]
      _ = 0 := by rw [sub_self]
  have hP0Dpar : P0 * Dpar = Dpar := by
    rw [hDpar, ← Matrix.mul_assoc, hP0X]
  have hP0Y : P0 * Y = X + Dpar := by
    rw [hY, Matrix.mul_add, Matrix.mul_add, hP0X, hP0Dpar, hP0Dperp]
    simp
  have hYm : (1 - P0) * Y = Dperp := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP0Y, hY]
    simp
  have h1mT : (1 - P0)ᵀ = 1 - P0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hP0T]
  have hYT : Yᵀ * (1 - P0) = Dperpᵀ := by
    rw [← h1mT, ← Matrix.transpose_mul, hYm]
  calc (Y * Yᵀ - X * Xᵀ) * (1 - P0)
      = Y * (Yᵀ * (1 - P0)) - X * (Xᵀ * (1 - P0)) := by
          rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Y * Dperpᵀ - X * (0 : Matrix n m ℝ) := by rw [hYT, hXT]
    _ = Y * Dperpᵀ := by simp

/-- **块恒等式例 2·抽象 P₀ 面**（R18B 探针 1 例 2 源转录）：
同前提 ⇒ `(1−P₀)*E*(1−P₀) = D_⊥*D_⊥ᵀ`（路线 B 的 t² trace 面）。 -/
theorem one_sub_P0_E_one_sub_P0_of {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m]
    {X Y Dpar Dperp : Matrix m n ℝ} {A : Matrix n n ℝ} {P0 : Matrix m m ℝ}
    (hP0T : P0ᵀ = P0) (hP0X : P0 * X = X) (hP0Dperp : P0 * Dperp = 0)
    (hDpar : Dpar = X * A) (hY : Y = X + Dpar + Dperp) :
    (1 - P0) * (Y * Yᵀ - X * Xᵀ) * (1 - P0) = Dperp * Dperpᵀ := by
  have hP0Dpar : P0 * Dpar = Dpar := by
    rw [hDpar, ← Matrix.mul_assoc, hP0X]
  have hP0Y : P0 * Y = X + Dpar := by
    rw [hY, Matrix.mul_add, Matrix.mul_add, hP0X, hP0Dpar, hP0Dperp]
    simp
  have hYm : (1 - P0) * Y = Dperp := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP0Y, hY]
    simp
  have hXm : (1 - P0) * X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP0X]
    simp
  have h1mT : (1 - P0)ᵀ = 1 - P0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hP0T]
  have hYT : Yᵀ * (1 - P0) = Dperpᵀ := by
    rw [← h1mT, ← Matrix.transpose_mul, hYm]
  have e1 : (1 - P0) * (Y * Yᵀ) * (1 - P0)
      = ((1 - P0) * Y) * (Yᵀ * (1 - P0)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc]
  have e2 : (1 - P0) * (X * Xᵀ) * (1 - P0)
      = ((1 - P0) * X) * (Xᵀ * (1 - P0)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc]
  calc (1 - P0) * (Y * Yᵀ - X * Xᵀ) * (1 - P0)
      = (1 - P0) * (Y * Yᵀ) * (1 - P0) - (1 - P0) * (X * Xᵀ) * (1 - P0) := by
          rw [Matrix.mul_sub (1 - P0) (Y * Yᵀ) (X * Xᵀ), Matrix.sub_mul]
    _ = ((1 - P0) * Y) * (Yᵀ * (1 - P0)) - ((1 - P0) * X) * (Xᵀ * (1 - P0)) := by
          rw [e1, e2]
    _ = Dperp * Dperpᵀ - (0 : Matrix m n ℝ) * (Xᵀ * (1 - P0)) := by rw [hYm, hYT, hXm]
    _ = Dperp * Dperpᵀ := by simp

/-- **块恒等式例 1·具体 P₀ 面**：S := XᵀX 可逆 ⇒
`E*(1−P₀) = Y*D_⊥ᵀ`（P₀ := X*(XᵀX)⁻¹*Xᵀ 字面；五前提由在库 P₀ 桥
P0_transpose/P0_mul_X/P0_mul_D 免费供给——探针 1 例 3 的 48 行前提桥
大部分在库，D82 设计注记）。 -/
theorem block_id1 {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    (Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = Y * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
  have hP0Dperp : (X * (Xᵀ * X)⁻¹ * Xᵀ)
        * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) = 0 := by
    have h1 : (X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y - X)
        = X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) := P0_mul_D X (Y - X)
    have h2 : (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
        = X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) := by
      rw [← Matrix.mul_assoc, P0_mul_X X hS]
    rw [Matrix.mul_sub, h1, h2, sub_self]
  have hY : Y = X + (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      + ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by abel
  exact E_mul_one_sub_P0_of (P0_transpose X) (P0_mul_X X hS) hP0Dperp rfl hY

/-- **块恒等式例 2·具体 P₀ 面**：S := XᵀX 可逆 ⇒
`(1−P₀)*E*(1−P₀) = D_⊥*D_⊥ᵀ`。 -/
theorem block_id2 {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    (1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
  have hP0Dperp : (X * (Xᵀ * X)⁻¹ * Xᵀ)
        * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) = 0 := by
    have h1 : (X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y - X)
        = X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) := P0_mul_D X (Y - X)
    have h2 : (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
        = X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) := by
      rw [← Matrix.mul_assoc, P0_mul_X X hS]
    rw [Matrix.mul_sub, h1, h2, sub_self]
  have hY : Y = X + (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      + ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by abel
  exact one_sub_P0_E_one_sub_P0_of (P0_transpose X) (P0_mul_X X hS) hP0Dperp rfl hY

/-- **op(1−P₀) ≤ 1 二次型面**（对称幂等 ⇒ ‖(1−P₀)*ᵥu‖ ≤ ‖u‖；
u ⬝ᵥ (P₀*ᵥu) = ‖P₀*ᵥu‖² 经幂等＋伴随搬移——R18B §ii.3 未跑面的实现，
~20 行，D83-①）。 -/
theorem vecNorm_one_sub_P0_le {m : Type} [Fintype m] [DecidableEq m]
    {P0 : Matrix m m ℝ} (hSym : P0ᵀ = P0) (hIdem : P0 * P0 = P0) (u : m → ℝ) :
    vecNorm ((1 - P0) *ᵥ u) ≤ vecNorm u := by
  have hkey : u ⬝ᵥ (P0 *ᵥ u) = (vecNorm (P0 *ᵥ u))^2 := by
    have hid : P0 *ᵥ u = (P0 * P0) *ᵥ u := by rw [hIdem]
    conv_lhs => rw [hid]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.vecMul_transpose, hSym, dotProduct_self_eq]
  have hw : (P0 *ᵥ u) ⬝ᵥ (P0 *ᵥ u) = (vecNorm (P0 *ᵥ u))^2 := dotProduct_self_eq _
  have hcomm : (P0 *ᵥ u) ⬝ᵥ u = u ⬝ᵥ (P0 *ᵥ u) := dotProduct_comm _ _
  have hexp : (vecNorm ((1 - P0) *ᵥ u))^2
      = (vecNorm u)^2 - (vecNorm (P0 *ᵥ u))^2 := by
    rw [← dotProduct_self_eq ((1 - P0) *ᵥ u), ← dotProduct_self_eq u,
        ← dotProduct_self_eq (P0 *ᵥ u)]
    have hsplit : ((1 - P0) *ᵥ u) = u - P0 *ᵥ u := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hsplit, sub_dotProduct, dotProduct_sub, dotProduct_sub, hcomm]
    linarith [hkey, hw]
  have hnn : (0:ℝ) ≤ vecNorm ((1 - P0) *ᵥ u) := vecNorm_nonneg _
  have hsub : (vecNorm u)^2 - (vecNorm (P0 *ᵥ u))^2 ≤ (vecNorm u)^2 := by
    linarith [sq_nonneg (vecNorm (P0 *ᵥ u))]
  calc vecNorm ((1 - P0) *ᵥ u) = Real.sqrt ((vecNorm ((1 - P0) *ᵥ u))^2) :=
        (Real.sqrt_sq hnn).symm
    _ = Real.sqrt ((vecNorm u)^2 - (vecNorm (P0 *ᵥ u))^2) := by rw [hexp]
    _ ≤ Real.sqrt ((vecNorm u)^2) := Real.sqrt_le_sqrt hsub
    _ = vecNorm u := Real.sqrt_sq (vecNorm_nonneg _)

/-- **frob (E*(1−P₀)) ≤ frob E**（op ≤ 1 面接在库 frob_mul_le_of_vecNorm，
c := 1：转置归 (1−P₀)*Eᵀ 左因子——R18B §iv.1 七步链第 6 步）。 -/
theorem frob_E_one_sub_P0_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    frob ((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))
      ≤ frob (Y * Yᵀ - X * Xᵀ) := by
  have hT : (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)ᵀ = 1 - X * (Xᵀ * X)⁻¹ * Xᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, P0_transpose X]
  have hle : frob ((1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ)ᵀ)
      ≤ 1 * frob (Y * Yᵀ - X * Xᵀ)ᵀ := by
    refine frob_mul_le_of_vecNorm _ _ 1 (by norm_num) ?_
    intro u
    simpa using vecNorm_one_sub_P0_le (P0_transpose X) (P0_mul_self X hS) u
  calc frob ((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))
      = frob ((1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ)ᵀ) := by
          calc frob ((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))
              = frob (((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))ᵀ) :=
                (frob_transpose_eq _).symm
            _ = frob ((1 - X * (Xᵀ * X)⁻¹ * Xᵀ)ᵀ * (Y * Yᵀ - X * Xᵀ)ᵀ) :=
                by rw [Matrix.transpose_mul]
            _ = frob ((1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ)ᵀ) :=
                by rw [hT]
    _ ≤ 1 * frob (Y * Yᵀ - X * Xᵀ)ᵀ := hle
    _ = frob (Y * Yᵀ - X * Xᵀ) := by rw [one_mul, frob_transpose_eq]

/-- **A8：‖Y*D_⊥ᵀ‖_F ≤ η**（块恒等式例 1＋op ≤ 1 面；路线 A 的
λ₃(Y) 压缩供给面）。 -/
theorem frob_YDperpT_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    frob (Y * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ)
      ≤ frob (Y * Yᵀ - X * Xᵀ) := by
  rw [← block_id1 X Y hS]
  exact frob_E_one_sub_P0_le X Y hS

/-- **trace-CS 面**（R18B §iv.1 七步链第 5 步）：`|tr M| ≤ √(Fintype.card n)·frob M`
（sum 级 CS 取 y := 1；√card 口径使 9 行实例恰为 3——D83-②）。 -/
theorem abs_trace_le_sqrt_card_frob {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) :
    |M.trace| ≤ Real.sqrt (Fintype.card n) * frob M := by
  have htr : M.trace = ∑ i, M i i := rfl
  have hnn : (0:ℝ) ≤ ∑ i, ∑ j, (M i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (M i j)
  have hone2 : (∑ i : n, ((1:ℝ))^2) = (Fintype.card n : ℝ) := by
    simp [Finset.sum_const]
  have hcs : (∑ i : n, M i i * (1:ℝ))^2
      ≤ (∑ i, (M i i)^2) * (∑ i : n, ((1:ℝ))^2) :=
    @ThomsonN9.TableB5Trace.sum_mul_sq_le_sum_sq_mul_sum_sq n _
      (fun i => M i i) (fun _ => (1:ℝ))
  have hleft : (∑ i : n, M i i * (1:ℝ)) = ∑ i, M i i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hleft, hone2] at hcs
  have hdsum : (∑ i, (M i i)^2) ≤ (frob M)^2 := by
    have h1 : ∀ i : n, (M i i)^2 ≤ ∑ j, (M i j)^2 := fun i =>
      Finset.single_le_sum (fun j _ => sq_nonneg (M i j)) (Finset.mem_univ i)
    have h2 : (∑ i, ∑ j, (M i j)^2) ≤ (frob M)^2 := by
      have heq : (frob M)^2 = (∑ i, ∑ j, (M i j)^2) := by
        show (Real.sqrt (∑ i, ∑ j, (M i j)^2))^2 = ∑ i, ∑ j, (M i j)^2
        exact Real.sq_sqrt hnn
      rw [heq]
    exact le_trans (Finset.sum_le_sum fun i _ => h1 i) h2
  have hkey : (M.trace)^2 ≤ (Fintype.card n : ℝ) * (frob M)^2 := by
    rw [htr]
    calc (∑ i, M i i)^2 ≤ (∑ i, (M i i)^2) * (Fintype.card n : ℝ) := hcs
      _ ≤ (Fintype.card n : ℝ) * (frob M)^2 := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hdsum (Nat.cast_nonneg _)
  refine le_of_sq_le_sq (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (frob_nonneg _)) ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc |M.trace|^2 = (M.trace)^2 := by rw [sq_abs]
    _ ≤ (Fintype.card n : ℝ) * (frob M)^2 := hkey

/-- **½-Hölder 面（七步链第 1–4 步）**：`t² = frob D_⊥² ≤ √(Fintype.card m)·η`
（块恒等式例 2＋trace 循环＋(1−P₀) 幂等＋trace-CS＋op ≤ 1）。 -/
theorem dperp_sq_le_hoelder {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) (hS : IsUnit (Xᵀ * X)) :
    frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))^2
      ≤ Real.sqrt (Fintype.card m) * frob (Y * Yᵀ - X * Xᵀ) := by
  have h1 : frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))^2
      = ((((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ)).trace :=
    frob_sq_eq_trace _
  have h2 : ((((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ)).trace
      = ((1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ)
          * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)).trace := by
    rw [block_id2 X Y hS]
  have h3 : ((1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ)
          * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)).trace
      = (((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))
          * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)).trace := by
    rw [show (1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (Y * Yᵀ - X * Xᵀ)
          * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
        = (1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * ((Y * Yᵀ - X * Xᵀ)
            * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)) from by
        rw [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
  have h4 : ((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))
          * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
      = (Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ) := by
    have hIdem : (1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
        = 1 - X * (Xᵀ * X)⁻¹ * Xᵀ := by
      rw [show (1 - X * (Xᵀ * X)⁻¹ * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)
            = 1 - (X * (Xᵀ * X)⁻¹ * Xᵀ) - (X * (Xᵀ * X)⁻¹ * Xᵀ)
                + (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹ * Xᵀ) from by
            noncomm_ring,
        P0_mul_self X hS]
      abel
    rw [Matrix.mul_assoc, hIdem]
  rw [h1, h2, h3, h4]
  have h5 := abs_trace_le_sqrt_card_frob
    ((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))
  have h6 : frob ((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))
      ≤ frob (Y * Yᵀ - X * Xᵀ) := frob_E_one_sub_P0_le X Y hS
  have hnn : (0:ℝ) ≤ Real.sqrt (Fintype.card m) := Real.sqrt_nonneg _
  calc (((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))).trace
      ≤ |(((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ))).trace| := le_abs_self _
    _ ≤ Real.sqrt (Fintype.card m)
        * frob ((Y * Yᵀ - X * Xᵀ) * (1 - X * (Xᵀ * X)⁻¹ * Xᵀ)) := h5
    _ ≤ Real.sqrt (Fintype.card m) * frob (Y * Yᵀ - X * Xᵀ) :=
        mul_le_mul_of_nonneg_left h6 hnn

/-- **½-Hölder 面·9 行实例**（√(Fintype.card (Fin 9)) = 3）：
`frob D_⊥ ≤ √(3·η)`（七步链收口——路线 B 头条的 t 项）。 -/
theorem dperp_le_sqrt3 {n : Type} [Fintype n] [DecidableEq n]
    (X Y : Matrix (Fin 9) n ℝ) (hS : IsUnit (Xᵀ * X)) :
    frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ)) := by
  have hc : (Fintype.card (Fin 9) : ℝ) = 9 := by simp
  have h3 : Real.sqrt ((3:ℝ)^2) = 3 := Real.sqrt_sq (by norm_num)
  have h9 : (3:ℝ)^2 = 9 := by norm_num
  have hs9 : Real.sqrt (Fintype.card (Fin 9)) = 3 := by
    rw [show Real.sqrt (Fintype.card (Fin 9)) = Real.sqrt (9:ℝ) by rw [hc], ← h9]
    exact h3
  have h2 := dperp_sq_le_hoelder X Y hS
  rw [hs9] at h2
  have hnn : (0:ℝ) ≤ frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) :=
    frob_nonneg _
  calc frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      = Real.sqrt (frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))^2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ)) := Real.sqrt_le_sqrt h2

/-! ### 层 2：路线 B 头条（无条件·全域 ½-Hölder 档） -/

/-- **路线 B 头条（无条件·全域，D82-3：无 hdpar）**：λ 夹逼
（lam3 > 0/hlo/hhi）＋域 `β := λ₁η/λ₃² ≤ 1/2`（frob B ≤ β 由在库
step4_bound 供给）⇒ `∃ Q ∈ Matrix.orthogonalGroup, frob (X−Y*Q) ≤
√λ₁·β + √(3·η)`（在库 step5_bound＋t² = tr(D_⊥D_⊥ᵀ) = tr(E(1−P₀)) ≤
3η 七步链）。 -/
theorem step6_uncond_hoelder {n : Type} [Fintype n] [DecidableEq n]
    (X Y : Matrix (Fin 9) n ℝ) {lam3 lam1 : ℝ}
    (hlam3 : 0 < lam3) (hlam1 : 0 ≤ lam1)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v))
    (hdom1 : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 ≤ 1 / 2) :
    ∃ Q ∈ Matrix.orthogonalGroup n ℝ,
      frob (X - Y * Q)
        ≤ Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)
          + Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ)) := by
  have hS : IsUnit (Xᵀ * X) := sandwich_isUnit (gram_transpose X) hlam3 hlo
  have hβ0 : (0:ℝ) ≤ lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 :=
    div_nonneg (mul_nonneg hlam1 (frob_nonneg _)) (sq_nonneg lam3)
  have hfrobB := step4_bound X Y hS hlam3 hlam1 hlo hhi
  obtain ⟨Q, hQmem, hQle⟩ := step5_bound X Y hlam1 hβ0 hdom1 hhi hfrobB
  refine ⟨Q, hQmem, ?_⟩
  have hd := dperp_le_sqrt3 X Y hS
  linarith [hQle, hd]

/-- **路线 B 推论·C_B·√δ 形（无条件·记录域全体）**：记录谱包络
（l₃ ≤ λ₃ ≤ λ₁ ≤ u₁）＋δ 域（0 ≤ δ、η ≤ √72·δ、δ ≤ δ_max）⇒
`d_P ≤ C_B·√δ`，`C_B := k1·√δ_max + √(3·√72Up)`、`k1 := s1Up·u₁·√72Up/l₃²`
（β ≤ 1/2 前提由 TableB5.delta_max_valid **内部导出**——记录域全体
无条件，R18B P4 常数审计口径）。 -/
theorem step6_hoelder_Cform {n : Type} [Fintype n] [DecidableEq n]
    (X Y : Matrix (Fin 9) n ℝ) {lam3 lam1 delta : ℝ}
    (hlam3 : 0 < lam3) (h3 : (l3:ℝ) ≤ lam3) (h1 : lam1 ≤ (u1:ℝ))
    (hord : lam3 ≤ lam1)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v))
    (hd0 : 0 ≤ delta) (heta : frob (Y * Yᵀ - X * Xᵀ) ≤ Real.sqrt 72 * delta)
    (hdel : delta ≤ (deltaMax:ℝ)) :
    ∃ Q ∈ Matrix.orthogonalGroup n ℝ,
      frob (X - Y * Q)
        ≤ ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * Real.sqrt (deltaMax:ℝ)
            + Real.sqrt (3 * (sqrt72Up:ℝ))) * Real.sqrt delta := by
  have hlam1 : (0:ℝ) ≤ lam1 :=
    le_trans (le_trans (by norm_num [l3] : (0:ℝ) ≤ (l3:ℝ)) h3) hord
  have heta0 : (0:ℝ) ≤ frob (Y * Yᵀ - X * Xᵀ) := frob_nonneg _
  have hdom := TableB5.delta_max_valid lam3 lam1
    (frob (Y * Yᵀ - X * Xᵀ)) delta heta0 heta hdel h3 h1 hord
  have hdom1 : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 ≤ 1 / 2 :=
    le_trans hdom (min_le_left _ _)
  obtain ⟨Q, hQmem, hQle⟩ :=
    step6_uncond_hoelder X Y hlam3 hlam1 hlo hhi hdom1
  refine ⟨Q, hQmem, ?_⟩
  -- (1) η ≤ sqrt72Up·δ（√72 ≤ sqrt72Up 安全向）
  have hetas : frob (Y * Yᵀ - X * Xᵀ) ≤ (sqrt72Up:ℝ) * delta :=
    le_trans heta (mul_le_mul_of_nonneg_right TableB5.sqrt72_le_sqrt72Up hd0)
  -- (2) √λ₁·β ≤ k1·δ
  have hs1 : Real.sqrt lam1 ≤ (s1Up:ℝ) :=
    le_trans (Real.sqrt_le_sqrt h1) TableB5.sqrt_u1_le_s1Up
  have hl3pos : (0:ℝ) < (l3:ℝ) := by norm_num [l3]
  have hl3sq : (l3:ℝ)^2 ≤ lam3^2 := by nlinarith [h3, hlam3, hl3pos]
  have hu1nn : (0:ℝ) ≤ (u1:ℝ) := by norm_num [u1]
  have hs72nn : (0:ℝ) ≤ (sqrt72Up:ℝ) := by norm_num [sqrt72Up]
  have hb : lam1 * frob (Y * Yᵀ - X * Xᵀ)
      ≤ (u1:ℝ) * ((sqrt72Up:ℝ) * delta) := by
    have e1 : lam1 * frob (Y * Yᵀ - X * Xᵀ)
        ≤ (u1:ℝ) * frob (Y * Yᵀ - X * Xᵀ) :=
      mul_le_mul_of_nonneg_right h1 heta0
    have e2 : (u1:ℝ) * frob (Y * Yᵀ - X * Xᵀ)
        ≤ (u1:ℝ) * ((sqrt72Up:ℝ) * delta) :=
      mul_le_mul_of_nonneg_left hetas hu1nn
    linarith
  have hbeta : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2
      ≤ (u1:ℝ) * ((sqrt72Up:ℝ) * delta) / (l3:ℝ)^2 := by
    rw [div_le_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hlam3))
      (by nlinarith [hl3pos] : (0:ℝ) < (l3:ℝ)^2)]
    have e1 : lam1 * frob (Y * Yᵀ - X * Xᵀ) * (l3:ℝ)^2
        ≤ (u1:ℝ) * ((sqrt72Up:ℝ) * delta) * (l3:ℝ)^2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    have e2 : (u1:ℝ) * ((sqrt72Up:ℝ) * delta) * (l3:ℝ)^2
        ≤ (u1:ℝ) * ((sqrt72Up:ℝ) * delta) * lam3^2 :=
      mul_le_mul_of_nonneg_left hl3sq
        (mul_nonneg hu1nn (mul_nonneg hs72nn hd0))
    linarith
  have hnum : (0:ℝ) ≤ (u1:ℝ) * ((sqrt72Up:ℝ) * delta) :=
    mul_nonneg hu1nn (mul_nonneg hs72nn hd0)
  have hterm1 : Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)
      ≤ (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * delta := by
    have e1 : Real.sqrt lam1 * ((u1:ℝ) * ((sqrt72Up:ℝ) * delta) / (l3:ℝ)^2)
        ≤ (s1Up:ℝ) * ((u1:ℝ) * ((sqrt72Up:ℝ) * delta) / (l3:ℝ)^2) :=
      mul_le_mul_of_nonneg_right hs1
        (div_nonneg hnum (sq_nonneg _))
    have e2 : (s1Up:ℝ) * ((u1:ℝ) * ((sqrt72Up:ℝ) * delta) / (l3:ℝ)^2)
        = (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * delta := by ring
    calc Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)
        ≤ Real.sqrt lam1 * ((u1:ℝ) * ((sqrt72Up:ℝ) * delta) / (l3:ℝ)^2) :=
          mul_le_mul_of_nonneg_left hbeta (Real.sqrt_nonneg _)
      _ ≤ (s1Up:ℝ) * ((u1:ℝ) * ((sqrt72Up:ℝ) * delta) / (l3:ℝ)^2) := e1
      _ = (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * delta := e2
  -- (3) √(3η) ≤ √(3·sqrt72Up)·√δ
  have hterm2 : Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ))
      ≤ Real.sqrt (3 * (sqrt72Up:ℝ)) * Real.sqrt delta := by
    have hle : 3 * frob (Y * Yᵀ - X * Xᵀ)
        ≤ 3 * ((sqrt72Up:ℝ) * delta) :=
      mul_le_mul_of_nonneg_left hetas (by norm_num)
    have hr : 3 * ((sqrt72Up:ℝ) * delta) = 3 * (sqrt72Up:ℝ) * delta := by ring
    have hsplit : Real.sqrt (3 * (sqrt72Up:ℝ) * delta)
        = Real.sqrt (3 * (sqrt72Up:ℝ)) * Real.sqrt delta := by
      rw [Real.sqrt_mul (by norm_num [sqrt72Up] : (0:ℝ) ≤ 3 * (sqrt72Up:ℝ)) delta]
    calc Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ))
        ≤ Real.sqrt (3 * ((sqrt72Up:ℝ) * delta)) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (3 * (sqrt72Up:ℝ) * delta) := by rw [hr]
      _ = Real.sqrt (3 * (sqrt72Up:ℝ)) * Real.sqrt delta := hsplit
  -- (4) δ ≤ √δ_max·√δ（k1·δ ≤ k1·√δ_max·√δ）
  have hdeltaMax : (0:ℝ) ≤ (deltaMax:ℝ) := by norm_num [deltaMax]
  have hk1 : (0:ℝ) ≤ (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 := by
    have hs1nn : (0:ℝ) ≤ (s1Up:ℝ) := by norm_num [s1Up]
    exact div_nonneg (mul_nonneg (mul_nonneg hs1nn hu1nn) hs72nn) (sq_nonneg _)
  have hd : delta ≤ Real.sqrt (deltaMax:ℝ) * Real.sqrt delta := by
    have hsd : Real.sqrt delta ≤ Real.sqrt (deltaMax:ℝ) :=
      Real.sqrt_le_sqrt hdel
    have hself : Real.sqrt delta * Real.sqrt delta = delta := by
      rw [← Real.sqrt_mul hd0, Real.sqrt_mul_self hd0]
    have hdm : Real.sqrt delta * Real.sqrt delta
        ≤ Real.sqrt (deltaMax:ℝ) * Real.sqrt delta :=
      mul_le_mul_of_nonneg_right hsd (Real.sqrt_nonneg delta)
    rw [hself] at hdm
    exact hdm
  have hterm1b : (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * delta
      ≤ (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * Real.sqrt (deltaMax:ℝ)
        * Real.sqrt delta := by
    calc (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * delta
        = delta * ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2) := by ring
      _ ≤ (Real.sqrt (deltaMax:ℝ) * Real.sqrt delta)
          * ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2) :=
          mul_le_mul_of_nonneg_right hd hk1
      _ = (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * Real.sqrt (deltaMax:ℝ)
          * Real.sqrt delta := by ring
  rw [show ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * Real.sqrt (deltaMax:ℝ)
        + Real.sqrt (3 * (sqrt72Up:ℝ))) * Real.sqrt delta
      = ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2
          * Real.sqrt (deltaMax:ℝ)) * Real.sqrt delta
        + Real.sqrt (3 * (sqrt72Up:ℝ)) * Real.sqrt delta from by ring]
  linarith [hQle, hterm1, hterm1b, hterm2]

/-! ### 层 3：路线 A 链（无条件·窄域线性档：σ₃(Y) 自举） -/

/-- **二次恒等式·纯环（探针 2 例 a 源转录）**：`‖((1+A)ᵀ*ᵥv)‖² = v ⬝ᵥ ((1+B)*ᵥv)`
（B := A+Aᵀ+A*Aᵀ；(1+A)(1+A)ᵀ = 1+B 的 dotProduct 面）。 -/
theorem quad_id_transpose {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hB : B = A + Aᵀ + A*Aᵀ) (v : n → ℝ) :
    ((1 + A)ᵀ *ᵥ v) ⬝ᵥ ((1 + A)ᵀ *ᵥ v) = v ⬝ᵥ ((1 + B) *ᵥ v) := by
  have hAB : (1 + A) * (1 + A)ᵀ = 1 + B := by
    rw [hB, Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hAB]

/-- **行-CS 下界（探针 2 例 b 源转录，经在库 abs_quadform_le_frob）**：
`frob B ≤ β`（β ≥ 0）⇒ `(1−β)*(v ⬝ᵥ v) ≤ ‖((1+A)ᵀ*ᵥv)‖²`。 -/
theorem quadform_lo_transpose {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hB : B = A + Aᵀ + A*Aᵀ) {β : ℝ} (hβ : 0 ≤ β)
    (hBf : frob B ≤ β) (v : n → ℝ) :
    (1 - β) * (v ⬝ᵥ v) ≤ ((1 + A)ᵀ *ᵥ v) ⬝ᵥ ((1 + A)ᵀ *ᵥ v) := by
  rw [quad_id_transpose A B hB v]
  have hsplit : v ⬝ᵥ ((1 + B) *ᵥ v) = (v ⬝ᵥ v) + v ⬝ᵥ (B *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
  rw [hsplit]
  have h2 := abs_quadform_le_frob B v
  obtain ⟨hlo, _⟩ := abs_le.mp h2
  have hs : (0:ℝ) ≤ v ⬝ᵥ v := by
    rw [dotProduct_self_eq]; exact sq_nonneg _
  have hstep : frob B * (v ⬝ᵥ v) ≤ β * (v ⬝ᵥ v) :=
    mul_le_mul_of_nonneg_right hBf hs
  linarith [hlo, hstep]

/-- **A2 frob 对称面（真新面，探针 2 已走通 40 行）**：
`frob (Aᵀ+A+Aᵀ*A) = frob (A+Aᵀ+A*Aᵀ)`（B' := Aᵀ+A+AᵀA ≠ Bᵀ——B 本身
对称，frob_transpose_eq 单发不可达；走 tr((NNᵀ)²) = tr((NᵀN)²) 循环移位
＋frob(M−1)² = tr(M²)−2·tr M+card 线性拆开）。 -/
theorem frob_B_prime_eq {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    frob (Aᵀ + A + Aᵀ*A) = frob (A + Aᵀ + A*Aᵀ) := by
  set N : Matrix n n ℝ := 1 + A with hNdef
  have hTT : (N*Nᵀ)ᵀ = N*Nᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hSS : (Nᵀ*N)ᵀ = Nᵀ*N := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have htr : ((N*Nᵀ)*(N*Nᵀ)).trace = ((Nᵀ*N)*(Nᵀ*N)).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  have htrN : (Nᵀ*N).trace = (N*Nᵀ).trace := Matrix.trace_mul_comm Nᵀ N
  have key : ∀ M : Matrix n n ℝ, Mᵀ = M →
      frob (M - 1)^2 = (M*M).trace - M.trace - M.trace + (Fintype.card n : ℝ) := by
    intro M hM
    have hexp : (M - 1)*(M - 1)ᵀ = M*M - M - M + 1 := by
      rw [Matrix.transpose_sub, hM, Matrix.transpose_one]; noncomm_ring
    have h1 : frob (M - 1)^2 = ((M - 1)*(M - 1)ᵀ).trace := by
      rw [frob_sq_eq_trace]
    rw [h1, hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_one]
  have h1B : 1 + (A + Aᵀ + A*Aᵀ) = N*Nᵀ := by
    rw [hNdef, Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  have h1B' : 1 + (Aᵀ + A + Aᵀ*A) = Nᵀ*N := by
    rw [hNdef, Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  have hBminus : A + Aᵀ + A*Aᵀ = N*Nᵀ - 1 := by
    rw [← h1B]; abel
  have hB'minus : Aᵀ + A + Aᵀ*A = Nᵀ*N - 1 := by
    rw [← h1B']; abel
  have e1 : frob (A + Aᵀ + A*Aᵀ)^2
      = ((N*Nᵀ)*(N*Nᵀ)).trace - (N*Nᵀ).trace - (N*Nᵀ).trace
        + (Fintype.card n : ℝ) := by
    rw [hBminus, key (N*Nᵀ) hTT]
  have e2 : frob (Aᵀ + A + Aᵀ*A)^2
      = ((Nᵀ*N)*(Nᵀ*N)).trace - (Nᵀ*N).trace - (Nᵀ*N).trace
        + (Fintype.card n : ℝ) := by
    rw [hB'minus, key (Nᵀ*N) hSS]
  have hnn1 : (0:ℝ) ≤ frob (A + Aᵀ + A*Aᵀ) := frob_nonneg _
  have hnn2 : (0:ℝ) ≤ frob (Aᵀ + A + Aᵀ*A) := frob_nonneg _
  nlinarith [e1, e2, htr, htrN]

/-- **A4 行-CS 下界·非转置面**：`frob (A+Aᵀ+A*Aᵀ) ≤ β`（β ≥ 0）⇒
`(1−β)*(v ⬝ᵥ v) ≤ ‖((1+A)*ᵥv)‖²`（经 A2 frob 对称面转置归位）。 -/
theorem quadform_one_add_A_lo {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hBf : frob (A + Aᵀ + A*Aᵀ) ≤ β) (v : n → ℝ) :
    (1 - β) * (v ⬝ᵥ v) ≤ ((1 + A) *ᵥ v) ⬝ᵥ ((1 + A) *ᵥ v) := by
  have h := quadform_lo_transpose (Aᵀ) (Aᵀ + A + Aᵀ*A) (by
      rw [Matrix.transpose_transpose]) hβ (by
      rw [frob_B_prime_eq A]; exact hBf) v
  have heq : ((1 + Aᵀ)ᵀ *ᵥ v) = ((1 + A) *ᵥ v) := by
    congr 1
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_transpose]
  rwa [heq] at h

/-- **A6 算子面**：`vecNorm (M *ᵥ v) ≤ frob M * vecNorm v`
（逐行 CS＋frob 平方装配；‖Y*ᵥv‖ 与 ‖D_⊥*ᵥv‖ 的两用底座）。 -/
theorem vecNorm_mulVec_le_frob {m n : Type} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (v : n → ℝ) :
    vecNorm (M *ᵥ v) ≤ frob M * vecNorm v := by
  have hent : ∀ i : m, ((M *ᵥ v) i) = (M i) ⬝ᵥ v := fun _ => rfl
  have hcs : ∀ i : m, ((M i) ⬝ᵥ v)^2
      ≤ (vecNorm (M i))^2 * (vecNorm v)^2 := by
    intro i
    have h := abs_dotProduct_le (M i) v
    have hnn1 : (0:ℝ) ≤ vecNorm (M i) * vecNorm v :=
      mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
    have hnd : (0:ℝ) ≤ |(M i) ⬝ᵥ v| := abs_nonneg _
    have habs : ((M i) ⬝ᵥ v)^2 = |(M i) ⬝ᵥ v|^2 := (sq_abs _).symm
    rw [habs]
    calc |(M i) ⬝ᵥ v|^2 ≤ (vecNorm (M i) * vecNorm v)^2 := by
          nlinarith [h, hnn1, hnd]
      _ = (vecNorm (M i))^2 * (vecNorm v)^2 := by rw [mul_pow]
  have hL : (∑ i, (vecNorm (M i))^2) = (frob M)^2 := by
    have h0 : (0:ℝ) ≤ ∑ i, ∑ j, (M i j)^2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (∑ i, (vecNorm (M i))^2) = ∑ i, ∑ j, (M i j)^2 :=
          Finset.sum_congr rfl fun i _ => vecNorm_sq (M i)
      _ = (frob M)^2 := by
          have heq : (frob M)^2 = ∑ i, ∑ j, (M i j)^2 := by
            show (Real.sqrt (∑ i, ∑ j, (M i j)^2))^2 = ∑ i, ∑ j, (M i j)^2
            exact Real.sq_sqrt h0
          rw [heq]
  have hsum2 : (vecNorm (M *ᵥ v))^2 ≤ (frob M)^2 * (vecNorm v)^2 := by
    have hcalc : (vecNorm (M *ᵥ v))^2
        ≤ (∑ i, (vecNorm (M i))^2) * (vecNorm v)^2 := by
      rw [vecNorm_sq (M *ᵥ v)]
      calc ∑ i, ((M *ᵥ v) i)^2 = ∑ i, ((M i) ⬝ᵥ v)^2 :=
            Finset.sum_congr rfl fun i _ => by rw [hent i]
        _ ≤ ∑ i, (vecNorm (M i))^2 * (vecNorm v)^2 :=
            Finset.sum_le_sum fun i _ => hcs i
        _ = (∑ i, (vecNorm (M i))^2) * (vecNorm v)^2 := by rw [← Finset.sum_mul]
    rw [hL] at hcalc
    exact hcalc
  have hnn1 : (0:ℝ) ≤ vecNorm (M *ᵥ v) := vecNorm_nonneg _
  have hnn2 : (0:ℝ) ≤ frob M * vecNorm v :=
    mul_nonneg (frob_nonneg _) (vecNorm_nonneg _)
  refine le_of_sq_le_sq hnn1 hnn2 ?_
  rw [mul_pow]
  exact hsum2

/-- **逆向三角（自建底座，探针 2 源转录）**：`vecNorm u − vecNorm w ≤ vecNorm (u+w)`。 -/
theorem vecNorm_sub_le {n : Type} [Fintype n] (u w : n → ℝ) :
    vecNorm u - vecNorm w ≤ vecNorm (u + w) := by
  by_cases hle : vecNorm u ≤ vecNorm w
  · linarith [vecNorm_nonneg (u + w)]
  · have hcs := abs_dotProduct_le u w
    obtain ⟨hlo, hhi⟩ := abs_le.mp hcs
    have hexp : vecNorm (u + w)^2 = (u ⬝ᵥ u) + 2*(u ⬝ᵥ w) + (w ⬝ᵥ w) := by
      rw [← dotProduct_self_eq (u + w)]
      simp [dotProduct_add, add_dotProduct, dotProduct_comm]
      ring
    have hkey : (vecNorm u - vecNorm w)^2 ≤ vecNorm (u + w)^2 := by
      rw [hexp, dotProduct_self_eq u, dotProduct_self_eq w]
      nlinarith [hlo, hhi]
    have hpos : (0:ℝ) < vecNorm u - vecNorm w := by
      have : vecNorm w < vecNorm u := lt_of_not_ge hle
      linarith
    have hnn : (0:ℝ) ≤ vecNorm (u + w) := vecNorm_nonneg _
    nlinarith [hkey, hpos, hnn]

/-- **A7 组装例·Y 面（探针 2 已走通 53 行）**：
√(λ₃(1−β))·‖v‖ − ‖D_⊥*ᵥv‖ ≤ ‖((X*(1+A)+D_⊥)*ᵥv)‖
（A4 非转置面＋A5 σ₃(X) 面＋逆向三角）。 -/
theorem assembly_Y_lower {n : Type} [Fintype n] [DecidableEq n]
    {X Dperp : Matrix (Fin 9) n ℝ} {A : Matrix n n ℝ} {lam3 β : ℝ}
    (hl3 : 0 < lam3) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hX : ∀ w : n → ℝ, lam3 * (w ⬝ᵥ w) ≤ vecNorm (X *ᵥ w)^2)
    (hBf : frob (A + Aᵀ + A*Aᵀ) ≤ β) (v : n → ℝ) :
    Real.sqrt (lam3 * (1 - β)) * vecNorm v - vecNorm (Dperp *ᵥ v)
      ≤ vecNorm ((X * (1 + A) + Dperp) *ᵥ v) := by
  have h1 : (1 - β) * (v ⬝ᵥ v) ≤ ((1 + A) *ᵥ v) ⬝ᵥ ((1 + A) *ᵥ v) :=
    quadform_one_add_A_lo A hβ hBf v
  have hstep1 : Real.sqrt (1 - β) * vecNorm v ≤ vecNorm ((1 + A) *ᵥ v) := by
    have hsq1 : Real.sqrt (1 - β)^2 = 1 - β :=
      Real.sq_sqrt (by linarith)
    have hnn1 : (0:ℝ) ≤ Real.sqrt (1 - β) * vecNorm v :=
      mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg v)
    have h2 : (Real.sqrt (1 - β) * vecNorm v)^2 ≤ vecNorm ((1 + A) *ᵥ v)^2 := by
      rw [← dotProduct_self_eq ((1 + A) *ᵥ v)]
      have hexp : (Real.sqrt (1 - β) * vecNorm v)^2
          = Real.sqrt (1 - β)^2 * (v ⬝ᵥ v) := by
        rw [mul_pow, dotProduct_self_eq]
      rw [hexp, hsq1]
      exact h1
    have hnn2 : (0:ℝ) ≤ vecNorm ((1 + A) *ᵥ v) := vecNorm_nonneg _
    nlinarith [h2, hnn1, hnn2, hsq1]
  have hs2 : Real.sqrt lam3^2 = lam3 := Real.sq_sqrt hl3.le
  have hXw : ∀ w : n → ℝ, Real.sqrt lam3 * vecNorm w ≤ vecNorm (X *ᵥ w) := by
    intro w
    have h := hX w
    rw [dotProduct_self_eq w] at h
    have hnn1 : (0:ℝ) ≤ Real.sqrt lam3 * vecNorm w :=
      mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg w)
    have hnn2 : (0:ℝ) ≤ vecNorm (X *ᵥ w) := vecNorm_nonneg _
    nlinarith [h, hnn1, hnn2]
  have hsplit : (X * (1 + A) + Dperp) *ᵥ v
      = (X *ᵥ ((1 + A) *ᵥ v)) + (Dperp *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [hsplit]
  have htri := vecNorm_sub_le (X *ᵥ ((1 + A) *ᵥ v)) (Dperp *ᵥ v)
  have hsq : Real.sqrt lam3 * Real.sqrt (1 - β) = Real.sqrt (lam3 * (1 - β)) := by
    rw [Real.sqrt_mul hl3.le]
  calc Real.sqrt (lam3 * (1 - β)) * vecNorm v - vecNorm (Dperp *ᵥ v)
      = Real.sqrt lam3 * (Real.sqrt (1 - β) * vecNorm v) - vecNorm (Dperp *ᵥ v) := by
          rw [← hsq]; ring
    _ ≤ Real.sqrt lam3 * vecNorm ((1 + A) *ᵥ v) - vecNorm (Dperp *ᵥ v) := by
          refine sub_le_sub (mul_le_mul_of_nonneg_left hstep1
            (Real.sqrt_nonneg _)) le_rfl
    _ ≤ vecNorm (X *ᵥ ((1 + A) *ᵥ v)) - vecNorm (Dperp *ᵥ v) := by
          linarith [hXw ((1 + A) *ᵥ v)]
    _ ≤ vecNorm (X *ᵥ ((1 + A) *ᵥ v) + Dperp *ᵥ v) := htri

/-- **A9 λ₃(Y) 压缩**：二次型口径 `lamY`（∀ v, lamY·(v⬝ᵥv) ≤ v⬝ᵥ((YᵀY)*ᵥv)）⇒
`lamY * (frob D_⊥)² ≤ (frob (Y*D_⊥ᵀ))²`（trace_ge_smul＋S_Y := YᵀY PSD
＋frob_sq_mul_transpose——λ₃(Y) 以二次型口径假设引入，D82-1）。 -/
theorem lamY_dperp_sq_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (Y Dperp : Matrix m n ℝ) {lamY : ℝ}
    (hY : ∀ v : n → ℝ, lamY * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Yᵀ * Y) *ᵥ v)) :
    lamY * (frob Dperp)^2 ≤ (frob (Y * Dperpᵀ))^2 := by
  have hPSD1 : ((Yᵀ * Y) - lamY • (1 : Matrix n n ℝ)).PosSemidef :=
    posSemidef_of_lo (gram_transpose Y) hY
  have hPSD2 : (Dperpᵀ * Dperp).PosSemidef := posSemidef_transpose_mul_self Dperp
  have h1 := trace_ge_smul lamY hPSD1 hPSD2
  have h2 : (Dperpᵀ * Dperp).trace = (frob Dperp)^2 := (frob_sq_eq_trace' _).symm
  have h3 : (frob (Y * Dperpᵀ))^2 = ((Yᵀ * Y) * (Dperpᵀ * Dperp)).trace :=
    frob_sq_mul_transpose Y Dperp
  rw [← h2, h3]
  exact h1

/-- **A10 闭环消歧**：λ₃ 夹逼＋frob B ≤ β（0 ≤ β ≤ 1/2）＋域
`η ≤ λ₃/24`（c_lo := √(λ₃/2) 包络口径，D79-5）⇒
`frob D_⊥ ≤ 2√2·η/√λ₃`（½-Hölder 面 t ≤ √(3η) ≤ c/2 消歧＋
A7/A8/A9 合并 (c−t)·t ≤ η＋反证 t > 2η/c 矛盾）。 -/
theorem dperp_le_linear {n : Type} [Fintype n] [DecidableEq n]
    (X Y : Matrix (Fin 9) n ℝ) {lam3 β : ℝ}
    (hlam3 : 0 < lam3) (hβ0 : 0 ≤ β) (hβ12 : β ≤ 1 / 2)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v))
    (hBf : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ
        + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β)
    (heta24 : frob (Y * Yᵀ - X * Xᵀ) ≤ lam3 / 24) :
    frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ 2 * Real.sqrt 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt lam3 := by
  have hS : IsUnit (Xᵀ * X) := sandwich_isUnit (gram_transpose X) hlam3 hlo
  have hYeq : X * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      + ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) = Y := by
    rw [Matrix.mul_add, Matrix.mul_one]; abel
  have hX : ∀ w : n → ℝ, lam3 * (w ⬝ᵥ w) ≤ vecNorm (X *ᵥ w)^2 := by
    intro w
    have h1 := hlo w
    rw [TableB5Core.quadsum_eq X w] at h1
    have h2 : (∑ i, (X i ⬝ᵥ w)^2) = vecNorm (X *ᵥ w)^2 := by
      rw [vecNorm_sq (X *ᵥ w)]
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [← h2]; exact h1
  -- c² = λ₃(1−β) ≥ λ₃/2
  have hc2 : (Real.sqrt (lam3 * (1 - β)))^2 = lam3 * (1 - β) :=
    Real.sq_sqrt (mul_nonneg hlam3.le (by linarith))
  have hclolo : lam3 / 2 ≤ lam3 * (1 - β) := by
    have hhalf : (1:ℝ)/2 ≤ 1 - β := by linarith
    have h2 : lam3 * ((1:ℝ)/2) ≤ lam3 * (1 - β) :=
      mul_le_mul_of_nonneg_left hhalf hlam3.le
    linarith
  -- t ≤ √(3η) ≤ c/2（消歧）
  have hhalf := dperp_le_sqrt3 X Y hS
  have h3eta : 3 * frob (Y * Yᵀ - X * Xᵀ)
      ≤ (Real.sqrt (lam3 * (1 - β)))^2 / 4 := by
    have e1 : 3 * frob (Y * Yᵀ - X * Xᵀ) ≤ 3 * (lam3 / 24) :=
      mul_le_mul_of_nonneg_left heta24 (by norm_num)
    have e2 : lam3 / 8 ≤ lam3 * (1 - β) / 4 := by
      have h8 : lam3 * 4 ≤ (lam3 * (1 - β)) * 8 := by
        nlinarith [hclolo, hlam3.le]
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 8) (by norm_num : (0:ℝ) < 4)]
      linarith [h8]
    have e3 : 3 * (lam3 / 24) = lam3 / 8 := by ring
    rw [hc2]
    linarith [e1, e2, e3]
  have htc2 : frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ Real.sqrt (lam3 * (1 - β)) / 2 := by
    have h1 : Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ))
        ≤ Real.sqrt ((Real.sqrt (lam3 * (1 - β)))^2 / 4) :=
      Real.sqrt_le_sqrt h3eta
    have h2 : Real.sqrt ((Real.sqrt (lam3 * (1 - β)))^2 / 4)
        = Real.sqrt (lam3 * (1 - β)) / 2 := by
      have hnn : (0:ℝ) ≤ Real.sqrt (lam3 * (1 - β)) := Real.sqrt_nonneg _
      have he : (Real.sqrt (lam3 * (1 - β)) / 2)^2
          = (Real.sqrt (lam3 * (1 - β)))^2 / 4 := by ring
      rw [← he, Real.sqrt_sq (by positivity)]
    linarith [hhalf, h1, h2]
  -- c > 0 与 c−t ≥ c/2 > 0
  have hcpos : (0:ℝ) < Real.sqrt (lam3 * (1 - β)) :=
    Real.sqrt_pos.mpr (mul_pos hlam3 (by linarith))
  have hctpos : (0:ℝ) < Real.sqrt (lam3 * (1 - β))
      - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by
    linarith
  -- A7 组装：∀v, c·‖v‖ − ‖D_⊥*ᵥv‖ ≤ ‖Y*ᵥv‖
  have hasm : ∀ v : n → ℝ,
      Real.sqrt (lam3 * (1 - β)) * vecNorm v
        - vecNorm (((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) *ᵥ v)
        ≤ vecNorm ((X * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          + ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) *ᵥ v) :=
    fun v => assembly_Y_lower hlam3 hβ0 (by linarith) hX hBf v
  have hYv : ∀ v : n → ℝ, vecNorm (Y *ᵥ v)
      = vecNorm ((X * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          + ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) *ᵥ v) := by
    intro v
    rw [hYeq]
  have key4 : ∀ v : n → ℝ,
      (Real.sqrt (lam3 * (1 - β))
          - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) * vecNorm v
        ≤ vecNorm (Y *ᵥ v) := by
    intro v
    have h1 := hasm v
    rw [← hYv v] at h1
    have h2 := vecNorm_mulVec_le_frob
      ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) v
    linarith
  -- λ₃(Y) 二次型口径：(c−t)²
  have hqf : ∀ v : n → ℝ,
      (Real.sqrt (lam3 * (1 - β))
          - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))^2 * (v ⬝ᵥ v)
        ≤ v ⬝ᵥ ((Yᵀ * Y) *ᵥ v) := by
    intro v
    have h1 := key4 v
    have hnn1 : (0:ℝ) ≤ (Real.sqrt (lam3 * (1 - β))
        - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) * vecNorm v :=
      mul_nonneg hctpos.le (vecNorm_nonneg v)
    have hnn2 : (0:ℝ) ≤ vecNorm (Y *ᵥ v) := vecNorm_nonneg _
    have hsq : ((Real.sqrt (lam3 * (1 - β))
          - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) * vecNorm v)^2
        ≤ (vecNorm (Y *ᵥ v))^2 := by
      nlinarith [h1, hnn1, hnn2]
    rw [mul_pow, vecNorm_sq] at hsq
    have hconv : (∑ i, (Y i ⬝ᵥ v)^2) = (vecNorm (Y *ᵥ v))^2 := by
      rw [vecNorm_sq (Y *ᵥ v)]
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [TableB5Core.quadsum_eq Y v, hconv,
      show (v ⬝ᵥ v) = ∑ i, v i ^2 from by
        rw [← vecNorm_sq v, ← dotProduct_self_eq v]]
    exact hsq
  -- A9+A8 合并：(c−t)·t ≤ η
  have h6 := lamY_dperp_sq_le Y
    ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) hqf
  have h8pre := frob_YDperpT_le X Y hS
  have htnn : (0:ℝ) ≤ frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) :=
    frob_nonneg _
  have hetann : (0:ℝ) ≤ frob (Y * Yᵀ - X * Xᵀ) := frob_nonneg _
  have hctnn : (0:ℝ) ≤ Real.sqrt (lam3 * (1 - β))
      - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := hctpos.le
  have h8 : (Real.sqrt (lam3 * (1 - β))
        - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))
      * frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ frob (Y * Yᵀ - X * Xᵀ) := by
    refine le_of_sq_le_sq (mul_nonneg hctnn htnn) hetann ?_
    have he : ((Real.sqrt (lam3 * (1 - β))
        - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))
      * frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))^2
      = (Real.sqrt (lam3 * (1 - β))
          - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))^2
        * (frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))^2 := by ring
    rw [he]
    have e1 : (frob (Y * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ))^2
        ≤ (frob (Y * Yᵀ - X * Xᵀ))^2 := by
      nlinarith [h8pre, hetann,
        frob_nonneg (Y * ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ)]
    nlinarith [h6, e1]
  -- 反证收口：t ≤ 2η/c
  have hfinal1 : frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt (lam3 * (1 - β)) := by
    by_contra hcon
    push_neg at hcon
    have hct : Real.sqrt (lam3 * (1 - β)) / 2
        ≤ Real.sqrt (lam3 * (1 - β))
          - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by
      linarith [htc2]
    have ht0 : (0:ℝ) < frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by
      have hz : (0:ℝ) ≤ 2 * frob (Y * Yᵀ - X * Xᵀ)
          / Real.sqrt (lam3 * (1 - β)) :=
        div_nonneg (mul_nonneg (by norm_num) hetann) hcpos.le
      linarith
    have key : frob (Y * Yᵀ - X * Xᵀ)
        < (Real.sqrt (lam3 * (1 - β))
            - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))
          * frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by
      have e1 : Real.sqrt (lam3 * (1 - β)) / 2
          * (2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt (lam3 * (1 - β)))
          = frob (Y * Yᵀ - X * Xᵀ) := by
        field_simp
      have e2 : (Real.sqrt (lam3 * (1 - β)) / 2)
          * frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
          ≤ (Real.sqrt (lam3 * (1 - β))
              - frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))
            * frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) :=
        mul_le_mul_of_nonneg_right hct ht0.le
      have e3 : Real.sqrt (lam3 * (1 - β)) / 2
          * (2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt (lam3 * (1 - β)))
          < (Real.sqrt (lam3 * (1 - β)) / 2)
              * frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) :=
        mul_lt_mul_of_pos_left hcon (by positivity)
      rw [e1] at e3
      linarith
    linarith [h8]
  -- 2η/c ≤ 2√2·η/√λ₃（c ≥ √(λ₃/2) = √λ₃/√2）
  have hkey2 : Real.sqrt lam3
      ≤ Real.sqrt 2 * Real.sqrt (lam3 * (1 - β)) := by
    have hcfinal : Real.sqrt lam3 / Real.sqrt 2
        ≤ Real.sqrt (lam3 * (1 - β)) := by
      have h2 : Real.sqrt lam3 / Real.sqrt 2 = Real.sqrt (lam3 / 2) :=
        (Real.sqrt_div hlam3.le 2).symm
      rw [h2]
      exact Real.sqrt_le_sqrt hclolo
    have hrt2 : (0:ℝ) < Real.sqrt 2 := by norm_num
    calc Real.sqrt lam3
        = Real.sqrt 2 * (Real.sqrt lam3 / Real.sqrt 2) := by field_simp
      _ ≤ Real.sqrt 2 * Real.sqrt (lam3 * (1 - β)) :=
          mul_le_mul_of_nonneg_left hcfinal hrt2.le
  have hlast : 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt (lam3 * (1 - β))
      ≤ 2 * Real.sqrt 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt lam3 := by
    have hslt3 : (0:ℝ) < Real.sqrt lam3 := Real.sqrt_pos.mpr hlam3
    rw [div_le_div_iff₀ hcpos hslt3]
    refine le_trans (mul_le_mul_of_nonneg_left hkey2
      (mul_nonneg (by norm_num) hetann)) ?_
    exact le_of_eq (by ring)
  linarith [hfinal1, hlast]

/-- **路线 A 线性头条（无条件·窄域，D82-3：无 hdpar）**：λ 夹逼＋域
`β := λ₁η/λ₃² ≤ 1/2`＋窄域 `η ≤ λ₃/24` ⇒
`∃ Q ∈ Matrix.orthogonalGroup, frob (X−Y*Q) ≤ (√λ₁·λ₁/λ₃² + 2√2/√λ₃)·η`
（step4_bound＋step5_bound＋A10 闭环消歧的终装配 A11）。 -/
theorem step6_uncond_linear {n : Type} [Fintype n] [DecidableEq n]
    (X Y : Matrix (Fin 9) n ℝ) {lam3 lam1 : ℝ}
    (hlam3 : 0 < lam3) (hlam1 : 0 ≤ lam1)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v))
    (hdom1 : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 ≤ 1 / 2)
    (heta24 : frob (Y * Yᵀ - X * Xᵀ) ≤ lam3 / 24) :
    ∃ Q ∈ Matrix.orthogonalGroup n ℝ,
      frob (X - Y * Q)
        ≤ (Real.sqrt lam1 * lam1 / lam3^2 + 2 * Real.sqrt 2 / Real.sqrt lam3)
          * frob (Y * Yᵀ - X * Xᵀ) := by
  have hS : IsUnit (Xᵀ * X) := sandwich_isUnit (gram_transpose X) hlam3 hlo
  have hβ0 : (0:ℝ) ≤ lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 :=
    div_nonneg (mul_nonneg hlam1 (frob_nonneg _)) (sq_nonneg lam3)
  have hfrobB := step4_bound X Y hS hlam3 hlam1 hlo hhi
  obtain ⟨Q, hQmem, hQle⟩ := step5_bound X Y hlam1 hβ0 hdom1 hhi hfrobB
  have hdp := dperp_le_linear X Y hlam3 hβ0 hdom1 hlo hfrobB heta24
  refine ⟨Q, hQmem, ?_⟩
  calc frob (X - Y * Q)
      ≤ Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)
        + frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := hQle
    _ ≤ Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)
        + 2 * Real.sqrt 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt lam3 := by
        linarith [hdp]
    _ = (Real.sqrt lam1 * lam1 / lam3^2 + 2 * Real.sqrt 2 / Real.sqrt lam3)
          * frob (Y * Yᵀ - X * Xᵀ) := by ring

/-! ### 层 4：TTP 实例化（l3/u1 字面接线，D82-3：无 hdpar） -/

/-- **TTP 实例化·路线 B 头条**：z 盒 [zLo, zHi]＋η 域前提（β := u₁η/l₃² ≤ 1/2）
⇒ `∃ Q ∈ orthogonalGroup (Fin 3) ℝ, frob (ttpX z − Y*Q) ≤
√u₁·β + √(3·η)`（在库 ttpX_quadform_lo/hi 供给）。 -/
theorem ttpX_step6_hoelder (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hdom1 : (u1:ℝ) * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2
      ≤ 1 / 2) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      frob (ttpX z - Y * Q)
        ≤ Real.sqrt (u1:ℝ)
            * ((u1:ℝ) * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2)
          + Real.sqrt (3 * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ)) :=
  step6_uncond_hoelder (ttpX z) Y (by norm_num [l3] : (0:ℝ) < (l3:ℝ))
    (by norm_num [u1] : (0:ℝ) ≤ (u1:ℝ))
    (ttpX_quadform_lo z h1 h2) (ttpX_quadform_hi z h1 h2) hdom1

/-- **TTP 实例化·路线 A 线性头条**：z 盒＋β 域＋窄域 `η ≤ l₃/24` ⇒
`∃ Q ∈ orthogonalGroup (Fin 3) ℝ, frob (ttpX z − Y*Q) ≤
(√u₁·u₁/l₃² + 2√2/√l₃)·η`。 -/
theorem ttpX_step6_linear (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hdom1 : (u1:ℝ) * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2
      ≤ 1 / 2)
    (heta24 : frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) ≤ (l3:ℝ) / 24) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      frob (ttpX z - Y * Q)
        ≤ (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
            + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ))
          * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) :=
  step6_uncond_linear (ttpX z) Y (by norm_num [l3] : (0:ℝ) < (l3:ℝ))
    (by norm_num [u1] : (0:ℝ) ≤ (u1:ℝ))
    (ttpX_quadform_lo z h1 h2) (ttpX_quadform_hi z h1 h2) hdom1 heta24

end ThomsonN9.TableB5Uncond
