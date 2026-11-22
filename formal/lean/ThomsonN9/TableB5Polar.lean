import Mathlib
import ThomsonN9.TableB5
import ThomsonN9.TableB5Core
import ThomsonN9.TableB5Trace

/-!
# Table B5Polar (R18A / r18a): the polar-decomposition layer of the B5 body, steps 5–6

This file is the third piece of the B5 analytic body (`d_P(X,Y) ≤ C·δ`,
the `l4_procrustes.py` proof) — the **polar-decomposition / assembly layer of
steps 5–6**, on top of `TableB5Core` (B5a, steps 1–2) and `TableB5Trace`
(B5b, steps 3–4).  Eight layers:

* **L1 quadratic-form ⇔ PSD bridge + row-CS.**  `quadform_nonneg_of_
  posSemidef` (R17B Q1 example-2 calibre) and the **row-CS quadratic bound**
  `abs_quadform_le_frob` `|v ⬝ᵥ (B*ᵥv)| ≤ frob B * (v ⬝ᵥ v)` (B5b
  `abs_dotProduct_le` assembly), with the `1 + B` lower-sandwich corollary
  `quadform_one_add_lo`.
* **L2 W construction.**  With `A := (XᵀX)⁻¹*(Xᵀ*(Y−X))` and
  `B := A+Aᵀ+A*Aᵀ`: `B_symm`, `one_add_B_eq` (`1+B = (1+A)*(1+A)ᵀ`),
  `one_add_B_posSemidef`, the CFC.sqrt supply family `W_symm` /
  `W_posSemidef` / `W_mul_W` / `W_quadform_nonneg` (`W := CFC.sqrt (1+B)`),
  and the **sqrt monotonicity lemma `sqrt_quadform_lo`** (D78-3 route:
  spectral mapping + CFC order — quadratic sandwich `c²·(v ⬝ᵥ v) ≤
  v ⬝ᵥ (M*ᵥv)` ⇒ `c·(v ⬝ᵥ v) ≤ v ⬝ᵥ ((CFC.sqrt M)*ᵥv)`; the direct
  `CFC.sqrt_le_sqrt` route is blocked on ℝ matrices by the ℂ-only
  `NonUnitalCStarAlgebra` instance), instantiated to `W_quadform_lo`
  (`W ⪰ √(1−β)·1`), `W_isUnit`, `W_quadform_ge_half`.
* **L3 R orthogonal.**  `W_mul_R`, the Q3 core `R_mul_RT`, the
  `Matrix.orthogonalGroup` membership face `R_mem_orthogonalGroup` (main
  calibre), the double-equation face `R_eq_pair`, and the inverse
  membership `Rinv_mem_orthogonalGroup` (witness `Q := R⁻¹`).
* **L4 orthogonal right-multiplication invariance.**
  `frob_mul_right_orthogonal` : `frob (M*Q) = frob M`.
* **L5 the W−I Frobenius bound (D77 supplement line).**
  `Wp1_sq_quadform` (quadratic face `(W+1)² ⪰ 9/4·1`: expansion +
  Cauchy–Schwarz + `W ⪰ 1/2·1`), `Wp1_sq_posSemidef`, commutative-ring
  identities `Wm1_Wp1`/`Wm1_Wp1'`/`B_eq_WW_sub_one`/`B_sq_trace` (probe ③:
  single-generator polynomial identity, `noncomm_ring`), `Wm1_sq_
  posSemidef`, the **headline** `frob_Wm1_le` : `frob (W−1) ≤
  (2/3)*frob (A+Aᵀ+A*Aᵀ)` (B5b `trace_ge_smul` with A := (W+1)²,
  t := 9/4, B' := (W−1)²).
* **L6 step 5 headline.**  `vecNorm_X_mulVec_le` (σ₁ face), the column
  compression `frob_X_one_sub_W_le`, the ring identity `YQ_eq`
  (probe ④), and **`step5_bound`** : `∃ Q ∈ Matrix.orthogonalGroup n ℝ,
  frob (X − Y*Q) ≤ √λ₁*β + frob D_⊥` under the written domain
  `0 ≤ β ≤ 1/2` (β ≤ 3/4 derived internally — no domain weakening).
* **L7 step 6 conditional assembly (D77 ruling 2).**  `smul_beta_le_half`
  (domain ⇒ σ₁β ≤ √λ₃/2), the conditional perpendicular bound `dperp_le`
  (from B5b `step3_bound`), and **`step6_final`** : under the **explicit**
  premise `frob D_∥ ≤ σ₁β` (NOT derivable in the reflection family —
  D77-2), `∃ Q ∈ orthogonalGroup, frob (X−Y*Q) ≤ (σ₁λ₁/λ₃² + 2/√λ₃)*η`
  with the written domain carried explicitly.
* **L8 TTP instantiation.**  `ttpX_step5` / `ttpX_step6_final` (z-box
  wiring via `l3`/`u1`; premises carried explicitly per D77-2 — no fake
  closure, no unconditional `C·δ` claim).

Correspondence to `l4_procrustes.py` (docstring steps): step 5 = right
polar decomposition `1+A = W·R`, `‖X−YR‖ ≤ σ₁β + ‖D_⊥‖`; step 6 =
conditional assembly `‖D_⊥‖ ≤ η/(σ₃−σ₁β) ≤ 2η/σ₃`.  The unconditional
`d_P ≤ C·δ` is **not** claimed (written-chain gap ②, D77-2: the
conditional layer is independently valid).

**Statement-face decisions (inherited D68/D73 + §6 increments):** generic
lemmas polymorphic in `{m n}`; own `frob`/`vecNorm` defs; quadratic-form
hypotheses in dotProduct·mulVec calibre; β-face with the written domain
`β ≤ 1/2`; `B` as the literal `A+Aᵀ+A*Aᵀ` (D73-3); ASCII `have` names.
Zero numeric data literals (constants live in `ThomsonN9.TableB5Data` via
`TableB5`) — no Data file for this piece.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5Polar

open scoped MatrixOrder
open Matrix
open ThomsonN9.TableB5Data
open ThomsonN9.TableB5Core
open ThomsonN9.TableB5Trace

/-! ### 层 1：二次型 ⇔ PSD 桥＋行-CS 二次型界（R17B Q1 例 2 口径） -/

/-- **PSD ⇒ 二次型非负桥**（R17B Q1 例 2 口径的 PSD→二次型方向）。 -/
theorem quadform_nonneg_of_posSemidef {n : Type} [Fintype n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) (v : n → ℝ) :
    0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  simpa only [star_trivial] using
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 v

/-- **行-CS 二次型界**：`|v ⬝ᵥ (B*ᵥv)| ≤ frob B * (v ⬝ᵥ v)`
（(B*ᵥv) i = B i ⬝ᵥ v 的逐行 B5b `abs_dotProduct_le`＋frob 平方装配）。 -/
theorem abs_quadform_le_frob {n : Type} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℝ) (v : n → ℝ) :
    |v ⬝ᵥ (B *ᵥ v)| ≤ frob B * (v ⬝ᵥ v) := by
  have h1 : |v ⬝ᵥ (B *ᵥ v)| ≤ vecNorm v * vecNorm (B *ᵥ v) :=
    abs_dotProduct_le v (B *ᵥ v)
  have hent : ∀ i : n, ((B *ᵥ v) i) = (B i) ⬝ᵥ v := fun _ => rfl
  have hcs : ∀ i : n, ((B i) ⬝ᵥ v)^2 ≤ (vecNorm (B i))^2 * (vecNorm v)^2 := by
    intro i
    have h := abs_dotProduct_le (B i) v
    have hnn1 : (0:ℝ) ≤ vecNorm (B i) * vecNorm v :=
      mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
    have hnd : (0:ℝ) ≤ |(B i) ⬝ᵥ v| := abs_nonneg _
    have habs : ((B i) ⬝ᵥ v)^2 = |(B i) ⬝ᵥ v|^2 := (sq_abs _).symm
    rw [habs]
    calc |(B i) ⬝ᵥ v|^2 ≤ (vecNorm (B i) * vecNorm v)^2 := by
          nlinarith [h, hnn1, hnd]
      _ = (vecNorm (B i))^2 * (vecNorm v)^2 := by rw [mul_pow]
  have hL : (∑ i, (vecNorm (B i))^2) = (frob B)^2 := by
    have h0 : (0:ℝ) ≤ ∑ i, ∑ j, (B i j)^2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (∑ i, (vecNorm (B i))^2) = ∑ i, ∑ j, (B i j)^2 :=
          Finset.sum_congr rfl fun i _ => vecNorm_sq (B i)
      _ = (frob B)^2 := by unfold frob; rw [Real.sq_sqrt h0]
  have hsum2 : (vecNorm (B *ᵥ v))^2 ≤ (frob B)^2 * (v ⬝ᵥ v) := by
    have hcalc : (vecNorm (B *ᵥ v))^2
        ≤ (∑ i, (vecNorm (B i))^2) * (vecNorm v)^2 := by
      rw [vecNorm_sq (B *ᵥ v)]
      calc ∑ i, ((B *ᵥ v) i)^2 = ∑ i, ((B i) ⬝ᵥ v)^2 :=
            Finset.sum_congr rfl fun i _ => by rw [hent i]
        _ ≤ ∑ i, (vecNorm (B i))^2 * (vecNorm v)^2 :=
            Finset.sum_le_sum fun i _ => hcs i
        _ = (∑ i, (vecNorm (B i))^2) * (vecNorm v)^2 := by rw [← Finset.sum_mul]
    calc (vecNorm (B *ᵥ v))^2 ≤ (∑ i, (vecNorm (B i))^2) * (vecNorm v)^2 := hcalc
      _ = (frob B)^2 * (vecNorm v)^2 := by rw [hL]
      _ = (frob B)^2 * (v ⬝ᵥ v) := by rw [dotProduct_self_eq]
  rw [dotProduct_self_eq] at hsum2
  have hnnB : (0:ℝ) ≤ frob B := frob_nonneg B
  have hnnv : (0:ℝ) ≤ vecNorm v := vecNorm_nonneg v
  have hfinal : vecNorm (B *ᵥ v) ≤ frob B * vecNorm v := by
    have hnn1 : (0:ℝ) ≤ vecNorm (B *ᵥ v) := vecNorm_nonneg _
    have hprod : (vecNorm (B *ᵥ v))^2 ≤ (frob B * vecNorm v)^2 := by
      rw [mul_pow]
      nlinarith [hsum2, hnnB, hnnv]
    nlinarith [hprod, hnn1, mul_nonneg hnnB hnnv]
  calc |v ⬝ᵥ (B *ᵥ v)| ≤ vecNorm v * vecNorm (B *ᵥ v) := h1
    _ ≤ vecNorm v * (frob B * vecNorm v) := mul_le_mul_of_nonneg_left hfinal hnnv
    _ = frob B * (v ⬝ᵥ v) := by rw [dotProduct_self_eq]; ring

/-- **1+B 二次型下夹逼**：`frob B ≤ β`（β ≥ 0）⇒
`∀ v, (1−β)*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((1+B)*ᵥ v)`（行-CS 界的 1+B 分配面）。 -/
theorem quadform_one_add_lo {n : Type} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hfrobB : frob B ≤ β) (v : n → ℝ) :
    (1 - β) * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((1 + B) *ᵥ v) := by
  have h := abs_quadform_le_frob B v
  have e : v ⬝ᵥ ((1 + B) *ᵥ v) = (v ⬝ᵥ v) + v ⬝ᵥ (B *ᵥ v) := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec]
  have hu : (0:ℝ) ≤ v ⬝ᵥ v := by
    rw [dotProduct_self_eq]; exact sq_nonneg _
  have hn : -(frob B * (v ⬝ᵥ v)) ≤ v ⬝ᵥ (B *ᵥ v) := by
    have habs := neg_abs_le (v ⬝ᵥ (B *ᵥ v))
    linarith
  have h1 : (1 - β) * (v ⬝ᵥ v) ≤ (1 - frob B) * (v ⬝ᵥ v) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  have h2 : (1 - frob B) * (v ⬝ᵥ v) ≤ (v ⬝ᵥ v) + v ⬝ᵥ (B *ᵥ v) := by
    have hexp : (1 - frob B) * (v ⬝ᵥ v) = (v ⬝ᵥ v) - frob B * (v ⬝ᵥ v) := by ring
    linarith [hexp, hn]
  rw [e]
  exact le_trans h1 h2

/-! ### 层 2：W 构造层（CFC.sqrt 供给＋sqrt 单调性 D78-3 路线） -/

/-- **sqrt 单调性·二次型口径（D78-3）**：M 对称＋二次型下夹逼
`c²*(v ⬝ᵥ v) ≤ v ⬝ᵥ (M*ᵥ v)`（c ≥ 0）⇒
`c*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((CFC.sqrt M)*ᵥ v)`。
路线＝谱下界（特征向量路线，R17B Q2 'key' 面逐字）＋sqrt 谱映射
（sqrt_eq_cfc＋cfc_nnreal_eq_real＋cfc_map_spectrum）＋
algebraMap_le_of_le_spectrum（谱下界 ⇒ CStar 序）＋MatrixOrder 序→二次型桥。
（`CFC.sqrt_le_sqrt` 直接路线被 ℝ 矩阵的 NonUnitalCStarAlgebra 实例缺失
阻断——该实例仅 Matrix n n ℂ 有，CStarAlgebra/Matrix.lean:308。） -/
theorem sqrt_quadform_lo {n : Type} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hSym : Mᵀ = M) {c : ℝ} (hc : 0 ≤ c)
    (hlo : ∀ v : n → ℝ, c^2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v)) :
    ∀ v : n → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((CFC.sqrt M) *ᵥ v) := by
  have hMnn : 0 ≤ M := by
    have h0 : (M - (0:ℝ) • (1 : Matrix n n ℝ)).PosSemidef :=
      posSemidef_of_lo hSym (fun v => by
        have h := hlo v
        have hc2 : (0:ℝ) ≤ c^2 * (v ⬝ᵥ v) := by
          have h1 : (0:ℝ) ≤ v ⬝ᵥ v := by
            rw [dotProduct_self_eq]; exact sq_nonneg _
          exact mul_nonneg (sq_nonneg c) h1
        simp only [zero_mul]
        linarith)
    simpa using h0.nonneg
  have hMHer : M.IsHermitian := by
    rw [IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hSym]
  have hspecM : ∀ μ ∈ spectrum ℝ M, c^2 ≤ μ := by
    intro μ hμ
    rw [← Matrix.spectrum_toLpLin (𝕜 := ℝ) (p := 2)] at hμ
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
    obtain ⟨v, hv1, hv2⟩ := hμ.exists_hasEigenvector
    have heq : (Matrix.toLpLin 2 2 M) v = μ • v := by simpa using hv1
    set w : n → ℝ := (v : n → ℝ) with hw
    have hw0 : w ≠ 0 := by
      intro hc0
      apply hv2
      have h0 : (WithLp.ofLp v : n → ℝ) = 0 := by rw [← hw]; exact hc0
      exact (WithLp.ofLp_eq_zero _).mp h0
    have e1 : (inner ℝ v ((Matrix.toLpLin 2 2 M) v) : ℝ) = w ⬝ᵥ (M *ᵥ w) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]
      rw [← hw]
    have e2 : (inner ℝ v v : ℝ) = w ⬝ᵥ w := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp
      rw [← hw]
    have conv : w ⬝ᵥ (M *ᵥ w) = μ * (w ⬝ᵥ w) := by
      rw [← e1, heq, real_inner_smul_right, e2]
    have hnn : 0 ≤ w ⬝ᵥ w := by rw [← e2]; exact real_inner_self_nonneg
    have hnz : w ⬝ᵥ w ≠ 0 := fun hc0 => hw0 (dotProduct_self_eq_zero.mp hc0)
    have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnn (Ne.symm hnz)
    have h1 := hlo w
    rw [conv] at h1
    exact (mul_le_mul_iff_of_pos_right hpos).mp h1
  have hspecW : ∀ x ∈ spectrum ℝ (CFC.sqrt M), c ≤ x := by
    intro x hx
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt M hMnn] at hx
    have hmap : spectrum ℝ
        (cfc (fun x : ℝ => ((NNReal.sqrt x.toNNReal : NNReal) : ℝ)) M)
        = (fun x : ℝ => ((NNReal.sqrt x.toNNReal : NNReal) : ℝ)) '' spectrum ℝ M :=
      cfc_map_spectrum (f := fun x : ℝ => ((NNReal.sqrt x.toNNReal : NNReal) : ℝ))
        (ha := hMHer) (hf := by fun_prop)
    rw [hmap] at hx
    obtain ⟨μ, hμ, hxμ⟩ := hx
    have hμ0 : 0 ≤ μ := le_trans (sq_nonneg c) (hspecM μ hμ)
    have hcoe : (((μ.toNNReal : NNReal) : ℝ)) = μ := Real.coe_toNNReal _ hμ0
    have hxval : x = Real.sqrt μ := by
      rw [← hxμ]
      show ((NNReal.sqrt μ.toNNReal : NNReal) : ℝ) = Real.sqrt μ
      rw [Real.coe_sqrt, hcoe]
    have h1 : Real.sqrt (c^2) ≤ Real.sqrt μ := Real.sqrt_le_sqrt (hspecM μ hμ)
    have h2 : Real.sqrt (c^2) = c := Real.sqrt_sq hc
    rw [h2] at h1
    rw [hxval]
    exact h1
  have hle : algebraMap ℝ (Matrix n n ℝ) c ≤ CFC.sqrt M :=
    algebraMap_le_of_le_spectrum hspecW
  have hsmul : algebraMap ℝ (Matrix n n ℝ) c = c • (1 : Matrix n n ℝ) := by
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
  rw [hsmul] at hle
  have hZpsd : (CFC.sqrt M - c • (1 : Matrix n n ℝ)).PosSemidef :=
    (Matrix.le_iff).mp hle
  intro v
  have h0 := quadform_nonneg_of_posSemidef hZpsd v
  have hsplit : v ⬝ᵥ ((CFC.sqrt M - c • (1 : Matrix n n ℝ)) *ᵥ v)
      = v ⬝ᵥ ((CFC.sqrt M) *ᵥ v) - c * (v ⬝ᵥ v) := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hsplit] at h0
  linarith

/-- **B 对称**：`(A+Aᵀ+A*Aᵀ)ᵀ = A+Aᵀ+A*Aᵀ`（B_eq_factor 转置面）。
A := (XᵀX)⁻¹*(Xᵀ*(Y−X)) 字面。 -/
theorem B_symm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)ᵀ = (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) := by
  rw [B_eq_factor X Y, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **1+B = (1+A)*(1+A)ᵀ**（B_eq_factor 改写＋abel）。 -/
theorem one_add_B_eq {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    (1 : Matrix n n ℝ) + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) = (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
  rw [B_eq_factor X Y]
  abel

/-- **1+B 半正定**（(1+A)*(1+A)ᵀ 面＋posSemidef_transpose_mul_self）。 -/
theorem one_add_B_posSemidef {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    ((1 : Matrix n n ℝ) + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)).PosSemidef := by
  rw [one_add_B_eq X Y]
  have h := posSemidef_transpose_mul_self ((1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ)
  rwa [Matrix.transpose_transpose] at h

/-- **1+B 对称**（B_symm 直出）。 -/
theorem one_add_B_symm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    ((1 : Matrix n n ℝ) + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))ᵀ = (1 : Matrix n n ℝ) + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) := by
  rw [Matrix.transpose_add, Matrix.transpose_one, B_symm X Y]

/-- **W 对称**（CFC.sqrt 自伴面，cfcₙ_star 路线，R17B Q2 例 1 同式）。 -/
theorem W_symm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))ᵀ = (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) := by
  have hH : (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))ᴴ = (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) := by
    rw [← Matrix.star_eq_conjTranspose]
    have h := cfcₙ_star (f := NNReal.sqrt) (a := (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) : Matrix n n ℝ))
    have hstar : (fun x : NNReal ↦ star (NNReal.sqrt x)) = NNReal.sqrt := by
      funext x; simp
    rw [hstar] at h
    exact h.symm
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hH

/-- **W 半正定**（CFC.sqrt_nonneg＋nonneg_iff_posSemidef）。 -/
theorem W_posSemidef {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

/-- **W*W = 1+B**（CFC.sqrt_mul_sqrt_self＋one_add_B_posSemidef 供非负前提）。 -/
theorem W_mul_W {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) * (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) = (1 : Matrix n n ℝ) + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) :=
  CFC.sqrt_mul_sqrt_self _ (one_add_B_posSemidef X Y).nonneg

/-- **W 二次型非负**（quadform_nonneg_of_posSemidef×W_posSemidef）。 -/
theorem W_quadform_nonneg {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) (v : n → ℝ) :
    0 ≤ v ⬝ᵥ ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) *ᵥ v) :=
  quadform_nonneg_of_posSemidef (W_posSemidef X Y) v

/-- **1+B 二次型下夹逼·实例面**（quadform_one_add_lo 的 B 字面实例）。 -/
theorem one_add_B_quadform_lo {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) (v : n → ℝ) :
    (1 - β) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((1 : Matrix n n ℝ) + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)) *ᵥ v) :=
  quadform_one_add_lo _ hβ0 hfrobB v

/-- **W ⪰ √(1−β)·1·二次型口径**（sqrt_quadform_lo 实例化，β < 1）。 -/
theorem W_quadform_lo {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) (v : n → ℝ) :
    Real.sqrt (1 - β) * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) *ᵥ v) := by
  refine sqrt_quadform_lo (one_add_B_symm X Y) (Real.sqrt_nonneg _) ?_ v
  intro u
  have h1 := one_add_B_quadform_lo X Y hβ0 hfrobB u
  have h2 : (Real.sqrt (1 - β))^2 = 1 - β := Real.sq_sqrt (by linarith)
  rw [h2]
  exact h1

/-- **W 可逆**（W ⪰ √(1−β)·1 且 √(1−β) > 0 ⇒ PosDef ⇒ IsUnit，
B5Core.sandwich_isUnit 桥）。 -/
theorem W_isUnit {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) :
    IsUnit (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) := by
  refine sandwich_isUnit (W_symm X Y) (l := Real.sqrt (1 - β)) ?_
    (W_quadform_lo X Y hβ0 hβ1 hfrobB)
  exact Real.sqrt_pos.mpr (by linarith)

/-- **W ⪰ 1/2·1·二次型口径**（√(1−β) ≥ 1/2 ⟸ β ≤ 3/4）。 -/
theorem W_quadform_ge_half {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ34 : β ≤ 3 / 4)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) (v : n → ℝ) :
    (1 / 2) * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) *ᵥ v) := by
  have h1 := W_quadform_lo X Y hβ0 (by linarith) hfrobB v
  have h2 : (1:ℝ)/2 ≤ Real.sqrt (1 - β) := by
    have hq : ((1:ℝ)/2)^2 = 1/4 := by norm_num
    have hq2 : ((1:ℝ)/2)^2 ≤ 1 - β := by rw [hq]; linarith
    have h3 := Real.sqrt_le_sqrt hq2
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)] at h3
  have hu : (0:ℝ) ≤ v ⬝ᵥ v := by
    rw [dotProduct_self_eq]; exact sq_nonneg _
  exact le_trans (mul_le_mul_of_nonneg_right h2 hu) h1

/-! ### 层 3：R 正交层（W⁻¹*(1+A) 的 orthogonalGroup membership） -/

/-- **W*(W⁻¹*(1+A)) = 1+A**（mul_nonsing_inv 归一）。 -/
theorem W_mul_R {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ)
    (hunit : IsUnit (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))) :
    (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) = 1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) := by
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hunit), Matrix.one_mul]

/-- **W*W = (1+A)*(1+A)ᵀ**（W_mul_W＋B_eq_factor 改写）。 -/
theorem WW_eq_one_add_A_AT {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) * (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) = (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))ᵀ := by
  rw [W_mul_W X Y, B_eq_factor X Y]
  abel

/-- **R*Rᵀ = 1 核心**（R := W⁻¹*(1+A)；R17B Q3 核心引理同式：
transpose_mul 开转置＋transpose_nonsing_inv 搬 (W⁻¹)ᵀ=(Wᵀ)⁻¹＋hWW 消去）。 -/
theorem R_mul_RT {n : Type} [Fintype n] [DecidableEq n]
    {A W : Matrix n n ℝ} (hW : Wᵀ = W)
    (hWW : W * W = (1 + A) * (1 + A)ᵀ) (hunit : IsUnit W) :
    (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ = 1 := by
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hunit
  have h1 : W * W⁻¹ = 1 := by simp [Matrix.mul_nonsing_inv W hdet]
  have h2 : W⁻¹ * W = 1 := by simp [Matrix.nonsing_inv_mul W hdet]
  have hT : (W⁻¹ * (1 + A))ᵀ = (1 + A)ᵀ * W⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hW]
  calc (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ
      = W⁻¹ * ((1 + A) * ((1 + A)ᵀ * W⁻¹)) := by rw [hT, mul_assoc]
    _ = W⁻¹ * (((1 + A) * (1 + A)ᵀ) * W⁻¹) := by
        conv_lhs => arg 2; rw [← mul_assoc]
    _ = W⁻¹ * ((W * W) * W⁻¹) := by rw [← hWW]
    _ = W⁻¹ * (W * (W * W⁻¹)) := by rw [mul_assoc]
    _ = W⁻¹ * (W * 1) := by rw [h1]
    _ = W⁻¹ * W := by rw [mul_one]
    _ = 1 := h2

/-- **R membership 口径（主口径）**：R ∈ Matrix.orthogonalGroup n ℝ。 -/
theorem R_mem_orthogonalGroup {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) :
    ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) ∈ Matrix.orthogonalGroup n ℝ := by
  have hiff : ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))ᵀ = 1 :=
    R_mul_RT (W_symm X Y) (WW_eq_one_add_A_AT X Y) (W_isUnit X Y hβ0 hβ1 hfrobB)
  exact (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mpr hiff

/-- **R 双等式口径**：R*Rᵀ = 1 ∧ Rᵀ*R = 1
（membership 一次供给两侧，Submonoid 结构内置双侧性）。 -/
theorem R_eq_pair {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) :
    ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))ᵀ = 1
      ∧ ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))ᵀ * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) = 1 := by
  have hmem := R_mem_orthogonalGroup X Y hβ0 hβ1 hfrobB
  exact ⟨(Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp hmem,
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hmem⟩

/-- **R⁻¹ membership（步骤 5 的右乘见证 Q := R⁻¹）**：
Rᵀ*R = 1 ⇒ R⁻¹ ∈ orthogonalGroup（(R⁻¹)ᵀ = (Rᵀ)⁻¹＋mul_inv_rev 消去）。 -/
theorem Rinv_mem_orthogonalGroup {n : Type} [Fintype n] [DecidableEq n]
    {R : Matrix n n ℝ} (hpair : R * Rᵀ = 1 ∧ Rᵀ * R = 1) :
    R⁻¹ ∈ Matrix.orthogonalGroup n ℝ := by
  have hunit : IsUnit R := IsUnit.of_mul_eq_one _ hpair.1
  have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hunit
  have hdetT : IsUnit Rᵀ.det := by
    rw [Matrix.det_transpose]; exact hdet
  have hT : (R⁻¹)ᵀ = (Rᵀ)⁻¹ := Matrix.transpose_nonsing_inv R
  refine (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mpr ?_
  show R⁻¹ * (R⁻¹)ᵀ = 1
  rw [hT, ← Matrix.mul_inv_rev Rᵀ R, hpair.2, inv_one]

/-! ### 层 4：frob 正交右乘不变性 -/

/-- **frob (M*Q) = frob M**（Q ∈ orthogonalGroup；trace 路线：
(M*Q)*(M*Q)ᵀ = M*(Q*Qᵀ)*Mᵀ = M*Mᵀ＋frob_sq_eq_trace＋非负开方）。 -/
theorem frob_mul_right_orthogonal {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℝ) {Q : Matrix n n ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup n ℝ) :
    frob (M * Q) = frob M := by
  have hQQT : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp hQ
  have hcalc : ((M * Q) * (Qᵀ * Mᵀ)) = M * (Q * Qᵀ) * Mᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have hexp : (M * Q) * (M * Q)ᵀ = M * Mᵀ := by
    rw [Matrix.transpose_mul]
    calc (M * Q) * (Qᵀ * Mᵀ) = M * (Q * Qᵀ) * Mᵀ := hcalc
      _ = M * (1 : Matrix n n ℝ) * Mᵀ := by rw [hQQT]
      _ = M * Mᵀ := by rw [Matrix.mul_one]
  have hsq : (frob (M * Q))^2 = (frob M)^2 := by
    rw [frob_sq_eq_trace, frob_sq_eq_trace, hexp]
  nlinarith [frob_nonneg (M * Q), frob_nonneg M, hsq]

/-! ### 层 5：W−I Frobenius 界（D77 补线） -/

/-- **平方保序小件**：x, y ≥ 0 且 x² ≤ y² ⇒ x ≤ y
（by_contra＋x+y > 0 分支＋平方差证书）。 -/
theorem le_of_sq_le_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^2 ≤ y^2) :
    x ≤ y := by
  by_contra hcon
  have h2 : (0:ℝ) < x - y := by linarith
  have h3 : (0:ℝ) < x + y := by
    rcases lt_or_eq_of_le (by linarith : (0:ℝ) ≤ x + y) with h | h0
    · exact h
    · exfalso; linarith
  have h4 : (0:ℝ) < (x - y) * (x + y) := mul_pos h2 h3
  have h5 : (x - y) * (x + y) = x^2 - y^2 := by ring
  rw [h5] at h4
  linarith

/-- **(W+1)² 二次型面头条前提**：`W ⪰ 1/2·1`（二次型）⇒
`∀ v, (9/4)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (((W+1)*(W+1))*ᵥ v)`
（展开 ‖(W+1)v‖² = ‖Wv‖²+2t+‖v‖²＋Cauchy–Schwarz
`(v ⬝ᵥ (W*ᵥv))² ≤ ‖W*ᵥv‖²·(v ⬝ᵥ v)`＋x := t/‖v‖² ≥ 1/2 ⇒
≥ (x+1)²‖v‖² ≥ (3/2)²‖v‖²；代数证书
4u·(A+2t−5/4·u) = 4(Au−t²)+(2t−u)(2t+5u)）。 -/
theorem Wp1_sq_quadform {n : Type} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℝ) (hW : Wᵀ = W)
    (hge : ∀ v : n → ℝ, (1 / 2) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (W *ᵥ v)) (v : n → ℝ) :
    (9 / 4) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((W + 1) * (W + 1)) *ᵥ v) := by
  have hmat : (W + 1) * (W + 1) = W * W + W + W + 1 := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.mul_one, Matrix.one_mul]
    abel
  have e1 : ((W + 1) * (W + 1)) *ᵥ v
      = (W * W) *ᵥ v + (W *ᵥ v) + ((W *ᵥ v) + v) := by
    rw [hmat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
        Matrix.one_mulVec]
    abel
  have e2 : (W * W) *ᵥ v = W *ᵥ (W *ᵥ v) := (Matrix.mulVec_mulVec v W W).symm
  have e3 : v ⬝ᵥ (W *ᵥ (W *ᵥ v)) = (vecNorm (W *ᵥ v))^2 := by
    have h1 : v ⬝ᵥ (W *ᵥ (W *ᵥ v)) = (v ᵥ* W) ⬝ᵥ (W *ᵥ v) :=
      Matrix.dotProduct_mulVec v W (W *ᵥ v)
    have hc : v ᵥ* W = W *ᵥ v := by
      rw [← Matrix.vecMul_transpose, hW]
    rw [h1, hc, dotProduct_self_eq]
  have hexp : v ⬝ᵥ (((W + 1) * (W + 1)) *ᵥ v)
      = (vecNorm (W *ᵥ v))^2 + 2 * (v ⬝ᵥ (W *ᵥ v)) + (v ⬝ᵥ v) := by
    rw [e1, e2, dotProduct_add, dotProduct_add, dotProduct_add, e3]
    ring
  have hcs : (v ⬝ᵥ (W *ᵥ v))^2
      ≤ (vecNorm (W *ᵥ v))^2 * (v ⬝ᵥ v) := by
    have hnn : (0:ℝ) ≤ vecNorm (W *ᵥ v) * vecNorm v :=
      mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
    have hnd : (0:ℝ) ≤ |v ⬝ᵥ (W *ᵥ v)| := abs_nonneg _
    have hsum : (0:ℝ) ≤ vecNorm (W *ᵥ v) * vecNorm v + |v ⬝ᵥ (W *ᵥ v)| := by
      linarith
    have h := abs_dotProduct_le v (W *ᵥ v)
    have hkey : |v ⬝ᵥ (W *ᵥ v)|^2 ≤ (vecNorm (W *ᵥ v) * vecNorm v)^2 := by
      nlinarith [h, hnn, hnd, hsum]
    calc (v ⬝ᵥ (W *ᵥ v))^2 = |v ⬝ᵥ (W *ᵥ v)|^2 := by rw [sq_abs]
      _ ≤ (vecNorm (W *ᵥ v) * vecNorm v)^2 := hkey
      _ = (vecNorm (W *ᵥ v))^2 * (v ⬝ᵥ v) := by
          rw [mul_pow, dotProduct_self_eq]
  set u := (v ⬝ᵥ v) with hu
  set t := (v ⬝ᵥ (W *ᵥ v)) with ht
  set A := (vecNorm (W *ᵥ v))^2 with hA
  have hu0 : (0:ℝ) ≤ u := by rw [hu, dotProduct_self_eq]; exact sq_nonneg _
  have ht2 : (1/2) * u ≤ t := by rw [hu, ht]; exact hge v
  have hA0 : (0:ℝ) ≤ A := by rw [hA]; exact sq_nonneg _
  have hcs' : A * u ≥ t * t := by rw [← pow_two t]; exact hcs
  rw [hexp]
  by_cases hu1 : u = 0
  · rw [hu1]
    have ht0 : (0:ℝ) ≤ t := by linarith
    simp only [mul_zero, zero_add]
    linarith
  · have hupos : (0:ℝ) < u := lt_of_le_of_ne hu0 (fun h => hu1 h.symm)
    have hexp2 : 4*u*(A + 2*t - (5/4)*u)
        = 4*(A*u - t*t) + (2*t - u)*(2*t + 5*u) := by ring
    have h5 : (0:ℝ) ≤ 2*t + 5*u := by linarith
    have h2 : (0:ℝ) ≤ 2*t - u := by linarith
    have hcert : (0:ℝ) ≤ 4*u*(A + 2*t - (5/4)*u) := by
      rw [hexp2]
      exact add_nonneg (by linarith [hcs'] : (0:ℝ) ≤ 4*(A*u - t*t))
        (mul_nonneg h2 h5)
    rcases lt_or_ge (A + 2*t - (5/4)*u) 0 with hneg | hnn
    · exact absurd hcert (by
        have hn2 : (0:ℝ) > 4*u*(A + 2*t - (5/4)*u) :=
          mul_neg_of_pos_of_neg (by linarith : (0:ℝ) < 4*u) hneg
        linarith)
    · linarith

/-- **(W+1)² 对称**。 -/
theorem Wp1_sq_symm {n : Type} [Fintype n] [DecidableEq n]
    {W : Matrix n n ℝ} (hW : Wᵀ = W) :
    ((W + 1) * (W + 1))ᵀ = (W + 1) * (W + 1) := by
  rw [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one, hW]

/-- **(W+1)² ⪰ 9/4·1·PSD 口径**（posSemidef_of_lo×Wp1_sq_quadform）。 -/
theorem Wp1_sq_posSemidef {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ34 : β ≤ 3 / 4)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) :
    (((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) + 1) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) + 1)
      - ((9/4 : ℝ)) • (1 : Matrix n n ℝ)).PosSemidef :=
  posSemidef_of_lo (Wp1_sq_symm (W_symm X Y))
    (Wp1_sq_quadform _ (W_symm X Y) (W_quadform_ge_half X Y hβ0 hβ34 hfrobB))

/-- **(W−1)(W+1) = W*W − 1**（单生成元交换环·探针③）。 -/
theorem Wm1_Wp1 {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) :
    (W - 1) * (W + 1) = W * W - 1 := by
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- **(W+1)(W−1) = W*W − 1**（同上反向）。 -/
theorem Wm1_Wp1' {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) :
    (W + 1) * (W - 1) = W * W - 1 := by
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- **B = W*W − 1**（W_mul_W＋add_sub_cancel）。 -/
theorem B_eq_WW_sub_one {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) :
    (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) = (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) * (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1 := by
  rw [W_mul_W X Y]
  abel

/-- **B² 的 trace 面**：`tr((W+1)²(W−1)²) = tr(B*B)`
（(W+1)²(W−1)² = (W²−1)² 单生成元多项式恒等式，noncomm_ring＋B 换元）。 -/
theorem B_sq_trace {n : Type} [Fintype n] [DecidableEq n] {W B : Matrix n n ℝ}
    (hB : B = W * W - 1) :
    (((W + 1) * (W + 1)) * ((W - 1) * (W - 1))).trace = (B * B).trace := by
  rw [hB]
  noncomm_ring

/-- **(W−1)² PSD**（posSemidef_transpose_mul_self×W 对称）。 -/
theorem Wm1_sq_posSemidef {n : Type} [Fintype n] [DecidableEq n]
    {W : Matrix n n ℝ} (hW : Wᵀ = W) :
    ((W - 1) * (W - 1)).PosSemidef := by
  have h := posSemidef_transpose_mul_self (W - 1)
  rwa [Matrix.transpose_sub, Matrix.transpose_one, hW] at h

/-- **W−I Frobenius 界头条（D77 补线）**：
`frob (W−1) ≤ (2/3)*frob (A+Aᵀ+A*Aᵀ)`
（(W+1)² ⪰ 9/4·1（Wp1_sq_posSemidef）＋trace_ge_smul 取 A := (W+1)²、
t := 9/4、B' := (W−1)²（PSD）＋B² trace 面（B_sq_trace）＋
B/(W−1) 对称的 frob_sq 双口径＋le_of_sq_le_sq 收口）。 -/
theorem frob_Wm1_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ34 : β ≤ 3 / 4)
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) :
    frob ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1) ≤ (2/3) * frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) := by
  have hWsymm : (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))ᵀ = (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) := W_symm X Y
  have hBsymm : (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)ᵀ = (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) := B_symm X Y
  have hpsd1 := Wp1_sq_posSemidef X Y hβ0 hβ34 hfrobB
  have hpsd2 := Wm1_sq_posSemidef hWsymm
  have hT2 : (9/4) * (((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1)).trace
      ≤ ((((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) + 1) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) + 1)) * (((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1))).trace :=
    trace_ge_smul (9/4) hpsd1 hpsd2
  have htr : ((((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) + 1) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) + 1)) * (((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1))).trace
      = ((((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) * (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)).trace := B_sq_trace (B_eq_WW_sub_one X Y)
  have htrB : ((((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) * (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)).trace = (frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))^2 := by
    rw [frob_sq_eq_trace, hBsymm]
  have htrW : (((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1)).trace = (frob ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1))^2 := by
    rw [frob_sq_eq_trace', Matrix.transpose_sub, Matrix.transpose_one, hWsymm]
  have hchain : (9/4) * (frob ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1))^2 ≤ (frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))^2 := by
    rw [← htrW, ← htrB]
    linarith [hT2, htr]
  refine le_of_sq_le_sq (frob_nonneg _) (mul_nonneg (by norm_num) (frob_nonneg _)) ?_
  rw [mul_pow, show ((2:ℝ)/3)^2 = 4/9 from by norm_num]
  linarith [hchain]

/-! ### 层 6：步骤 5 头条（∃ Q ∈ orthogonalGroup 的旋转规范） -/

/-- **σ₁ 二次型面**：上夹逼 `v ⬝ᵥ ((XᵀX)*ᵥv) ≤ λ₁(v ⬝ᵥv)` ⇒
`vecNorm (X*ᵥu) ≤ √λ₁ * vecNorm u`（quadsum_eq＋le_of_sq_le_sq）。 -/
theorem vecNorm_X_mulVec_le {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m n ℝ) {lam1 : ℝ} (hlam1 : 0 ≤ lam1)
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v)) (u : n → ℝ) :
    vecNorm (X *ᵥ u) ≤ Real.sqrt lam1 * vecNorm u := by
  have h2 : (vecNorm (X *ᵥ u))^2 ≤ lam1 * (vecNorm u)^2 := by
    have hent : ∀ i : m, ((X *ᵥ u) i) = (X i) ⬝ᵥ u := fun _ => rfl
    rw [vecNorm_sq (X *ᵥ u),
      show ∑ i, ((X *ᵥ u) i)^2 = ∑ i, ((X i) ⬝ᵥ u)^2 from
        Finset.sum_congr rfl fun i _ => by rw [hent i],
      ← TableB5Core.quadsum_eq X u, ← dotProduct_self_eq]
    exact hhi u
  have hsqrt : (Real.sqrt lam1 * vecNorm u)^2 = lam1 * (vecNorm u)^2 := by
    rw [mul_pow, Real.sq_sqrt hlam1]
  refine le_of_sq_le_sq (vecNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (vecNorm_nonneg _)) ?_
  rw [hsqrt]
  exact h2

/-- **列压缩**：`frob (X*(1−W)) ≤ √λ₁ * frob (1−W)`
（frob_mul_le_of_vecNorm＋vecNorm_X_mulVec_le）。 -/
theorem frob_X_one_sub_W_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {lam1 : ℝ} (hlam1 : 0 ≤ lam1)
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v)) :
    frob (X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))))) ≤ Real.sqrt lam1 * frob (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))) :=
  frob_mul_le_of_vecNorm X (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))) (Real.sqrt lam1)
    (Real.sqrt_nonneg _) (vecNorm_X_mulVec_le X hlam1 hhi)

/-- **Y*Q = X*W + D_⊥*Q 恒等式**（探针④面：W*R = 1+A'、R*Q = 1 ⇒
`(X + X*A' + D_⊥)*Q = X*W + D_⊥*Q`）。 -/
theorem YQ_eq {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℝ) {A W R Q : Matrix n n ℝ}
    (hWR : W * R = 1 + A) (hRQ : R * Q = 1) (Dp : Matrix m n ℝ) :
    (X + X * A + Dp) * Q = X * W + Dp * Q := by
  have hAQ : (1 + A) * Q = W := by
    rw [← hWR, Matrix.mul_assoc, hRQ, Matrix.mul_one]
  rw [Matrix.add_mul, Matrix.add_mul,
    show X * Q + (X * A) * Q = X * (1 + A) * Q from by
      rw [← Matrix.add_mul, show X + X * A = X * (1 + A) from by
            rw [Matrix.mul_add, Matrix.mul_one]],
    Matrix.mul_assoc, hAQ]

/-- **步骤 5 头条**：上夹逼 λ₁＋域 `0 ≤ β ≤ 1/2`＋`frob B ≤ β` ⇒
`∃ Q ∈ Matrix.orthogonalGroup n ℝ, frob (X − Y*Q) ≤ √λ₁*β + frob D_⊥`
（R := W⁻¹*(1+A) membership＋Q := R⁻¹ 见证＋YQ 恒等式＋列压缩＋
正交右乘不变＋W−I Frobenius 界；β ≤ 3/4 由 β ≤ 1/2 内部导出——
D77-1 书面域 β ≤ 1/2 之下补线全链无域弱化）。 -/
theorem step5_bound {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X Y : Matrix m n ℝ) {lam1 β : ℝ} (hlam1 : 0 ≤ lam1) (hβ0 : 0 ≤ β)
    (hβ12 : β ≤ 1 / 2)
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v))
    (hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β) :
    ∃ Q ∈ Matrix.orthogonalGroup n ℝ,
      frob (X - Y * Q) ≤ Real.sqrt lam1 * β + frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by
  have hβ34 : β ≤ 3 / 4 := by linarith
  have hβ1 : β < 1 := by linarith
  have hRpair := R_eq_pair X Y hβ0 hβ1 hfrobB
  have hunitR : IsUnit ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) :=
    IsUnit.of_mul_eq_one _ hRpair.1
  have hdetR : IsUnit ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunitR
  have hRQ : ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdetR
  refine ⟨((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹, Rinv_mem_orthogonalGroup hRpair, ?_⟩
  have hWmulR : (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) = 1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) :=
    W_mul_R X Y (W_isUnit X Y hβ0 hβ1 hfrobB)
  have hY : X + X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) = Y := by abel
  have hYQ : Y * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹
      = X * (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) + ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹ := by
    conv_lhs => arg 1; rw [← hY]
    exact YQ_eq X hWmulR hRQ ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
  have hX1 : X - X * (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) = X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))) := by
    rw [show X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))) = X - X * (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) from by
        rw [Matrix.mul_sub, Matrix.mul_one]]
  have hsplit : X - Y * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹
      = X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))))
        + (-(((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹)) := by
    rw [hYQ, sub_add_eq_sub_sub, hX1, sub_eq_add_neg]
  rw [hsplit]
  calc frob (X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))) + (-(((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹)))
      ≤ frob (X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))))
          + frob (-(((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹)) := frob_add_le _ _
    _ = frob (X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))))
          + frob (((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) * ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))⁻¹ * (1 + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))))⁻¹) := by rw [frob_neg]
    _ = frob (X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))))) + frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) :=
        congrArg (fun t => frob (X * (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))))) + t)
          (frob_mul_right_orthogonal ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) (Rinv_mem_orthogonalGroup hRpair))
    _ ≤ Real.sqrt lam1 * frob (1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)))) + frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) :=
        add_le_add_left (frob_X_one_sub_W_le X Y hlam1 hhi) _
    _ = Real.sqrt lam1 * frob ((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1) + frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by
        rw [show 1 - (CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) = -((CFC.sqrt (1 + (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ))) - 1) from by rw [neg_sub], frob_neg]
    _ ≤ Real.sqrt lam1 * ((2/3) * frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)) + frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) :=
        add_le_add_left
          (mul_le_mul_of_nonneg_left (frob_Wm1_le X Y hβ0 hβ34 hfrobB)
            (Real.sqrt_nonneg _)) _
    _ ≤ Real.sqrt lam1 * β + frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by
        have hfb : (2/3) * frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ) ≤ β := by linarith
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left hfb (Real.sqrt_nonneg _)) _

/-! ### 层 7：步骤 6 条件装配（D77 裁决 2：前提显式，不做假闭合） -/

/-- **域条件引理**：`β ≤ √λ₃/(2√λ₁)`（λ₁,λ₃ > 0）⇒ `√λ₁*β ≤ √λ₃/2`
（乘除消去：√λ₁·(√λ₃/(2√λ₁)) = √λ₃/2）。 -/
theorem smul_beta_le_half {lam3 lam1 β : ℝ} (hlam1 : 0 < lam1)
    (hlam3 : 0 < lam3) (hβ0 : 0 ≤ β)
    (hdom : β ≤ Real.sqrt lam3 / (2 * Real.sqrt lam1)) :
    Real.sqrt lam1 * β ≤ Real.sqrt lam3 / 2 := by
  have hne : Real.sqrt lam1 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam1)
  calc Real.sqrt lam1 * β
      ≤ Real.sqrt lam1 * (Real.sqrt lam3 / (2 * Real.sqrt lam1)) :=
        mul_le_mul_of_nonneg_left hdom (Real.sqrt_nonneg _)
    _ = Real.sqrt lam3 / 2 := by
        field_simp

/-- **条件垂直界**：下夹逼 λ₃＋显式前提 `frob D_∥ ≤ σ₁β`（D77-2：
反射族下不可消去——前提条件化）＋`σ₁β ≤ √λ₃/2` ⇒
`frob D_⊥ ≤ frob (Y*Yᵀ−X*Xᵀ) / (√λ₃ − σ₁β)`
（B5b step3_bound＋le_div_iff₀＋div_le_div_of_nonneg_left）。 -/
theorem dperp_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) {lam3 lam1 β : ℝ}
    (hlam3 : 0 < lam3)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v))
    (hdpar : frob (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) ≤ Real.sqrt lam1 * β)
    (hsub : Real.sqrt lam1 * β ≤ Real.sqrt lam3 / 2) :
    frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ frob (Y * Yᵀ - X * Xᵀ) / (Real.sqrt lam3 - Real.sqrt lam1 * β) := by
  have hS : IsUnit (Xᵀ * X) := sandwich_isUnit (gram_transpose X) hlam3 hlo
  have hE := step3_bound X Y hS hlam3 hlo
  have hs3 : (0:ℝ) < Real.sqrt lam3 := Real.sqrt_pos.mpr hlam3
  have hEta : (0:ℝ) ≤ frob (Y * Yᵀ - X * Xᵀ) := frob_nonneg _
  have hc : (0:ℝ) < Real.sqrt lam3 - Real.sqrt lam1 * β := by linarith
  have ha : (0:ℝ) < Real.sqrt lam3 - frob (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) := by linarith
  have key : frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ frob (Y * Yᵀ - X * Xᵀ) / (Real.sqrt lam3 - frob (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) := by
    rw [le_div_iff₀ ha, mul_comm]
    exact hE
  calc frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ frob (Y * Yᵀ - X * Xᵀ) / (Real.sqrt lam3 - frob (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))) := key
    _ ≤ frob (Y * Yᵀ - X * Xᵀ) / (Real.sqrt lam3 - Real.sqrt lam1 * β) :=
        div_le_div_of_nonneg_left hEta hc (by linarith)

/-- **步骤 6 条件终定理（头条）**：域条件
`β := λ₁η/λ₃² ≤ min(1/2, √λ₃/(2√λ₁))`（两分立面分立携带）＋
**显式前提** `frob D_∥ ≤ σ₁β`（D77-2：反射族 Y := X·Q̃ 下不成立——
η=0、β=0 域内而 frob D_∥ > 0——条件层独立有效，不做假闭合）⇒
`∃ Q ∈ orthogonalGroup, frob (X−Y*Q) ≤ (σ₁λ₁/λ₃² + 2/√λ₃)*η`
（step4_bound 供 frob B ≤ β＋step5_bound＋dperp_le＋分母 ≥ √λ₃/2 收口）。 -/
theorem step6_final {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (X Y : Matrix m n ℝ) {lam3 lam1 : ℝ}
    (hlam3 : 0 < lam3) (hlam1 : 0 < lam1)
    (hlo : ∀ v : n → ℝ, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≤ lam1 * (v ⬝ᵥ v))
    (hdpar : frob (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
      ≤ Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2))
    (hdom1 : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 ≤ 1 / 2)
    (hdom2 : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2
      ≤ Real.sqrt lam3 / (2 * Real.sqrt lam1)) :
    ∃ Q ∈ Matrix.orthogonalGroup n ℝ,
      frob (X - Y * Q)
        ≤ (Real.sqrt lam1 * lam1 / lam3^2 + 2 / Real.sqrt lam3)
          * frob (Y * Yᵀ - X * Xᵀ) := by
  have hS : IsUnit (Xᵀ * X) := sandwich_isUnit (gram_transpose X) hlam3 hlo
  have hβ0 : (0:ℝ) ≤ lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 :=
    div_nonneg (mul_nonneg hlam1.le (frob_nonneg _)) (sq_nonneg lam3)
  have hfrobB : frob (((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ + ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))) * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))ᵀ)
      ≤ lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 :=
    step4_bound X Y hS hlam3 hlam1.le hlo hhi
  obtain ⟨Q, hQmem, hQle⟩ := step5_bound X Y hlam1.le hβ0 hdom1 hhi hfrobB
  have hsub := smul_beta_le_half hlam1 hlam3 hβ0 hdom2
  have hdp := dperp_le X Y hlam3 hlo hdpar hsub
  have hs3 : (0:ℝ) < Real.sqrt lam3 := Real.sqrt_pos.mpr hlam3
  have hEta : (0:ℝ) ≤ frob (Y * Yᵀ - X * Xᵀ) := frob_nonneg _
  have hden : Real.sqrt lam3 / 2
      ≤ Real.sqrt lam3 - Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2) := by
    linarith
  have h2 : frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X)))) ≤ 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt lam3 := by
    calc frob ((Y - X) - X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))
        ≤ frob (Y * Yᵀ - X * Xᵀ)
            / (Real.sqrt lam3
              - Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)) := hdp
      _ ≤ frob (Y * Yᵀ - X * Xᵀ) / (Real.sqrt lam3 / 2) :=
          div_le_div_of_nonneg_left hEta (by linarith) hden
      _ = 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt lam3 := by
          have hne : Real.sqrt lam3 ≠ 0 := ne_of_gt hs3
          field_simp
  refine ⟨Q, hQmem, ?_⟩
  have hR1 : Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)
      = (Real.sqrt lam1 * lam1 / lam3^2) * frob (Y * Yᵀ - X * Xᵀ) := by ring
  rw [show (Real.sqrt lam1 * lam1 / lam3^2 + 2 / Real.sqrt lam3)
        * frob (Y * Yᵀ - X * Xᵀ)
      = Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2)
          + 2 * frob (Y * Yᵀ - X * Xᵀ) / Real.sqrt lam3 from by
      rw [hR1]; ring]
  linarith [hQle, h2]

/-! ### 层 8：TTP 实例化层（l3/u1 接线；前提显式携带——D77-2） -/

/-- **TTP 实例化·步骤 5 头条**：z 盒内对一切行构型 Y＋域 `0 ≤ β ≤ 1/2`＋
`frob B ≤ β` ⇒ `∃ Q ∈ orthogonalGroup (Fin 3) ℝ,
frob (ttpX z − Y*Q) ≤ √u₁*β + frob D_⊥`。 -/
theorem ttpX_step5 (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ12 : β ≤ 1 / 2)
    (hfrobB : frob ((((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z))) + (((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z)))ᵀ + (((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z))) * (((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z)))ᵀ) ≤ β) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      frob (ttpX z - Y * Q) ≤ Real.sqrt (u1:ℝ) * β + frob ((Y - ttpX z) - ttpX z * (((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z)))) :=
  step5_bound (ttpX z) Y (by norm_num [u1] : (0:ℝ) ≤ (u1:ℝ)) hβ0 hβ12
    (ttpX_quadform_hi z h1 h2) hfrobB

/-- **TTP 实例化·步骤 6 条件终定理**：z 盒内＋显式前提
`frob D_∥ ≤ √u₁*(u₁η/l₃²)`（D77-2 条件化，不伪造消去）＋域条件两
分立面 ⇒ `∃ Q, frob (ttpX z − Y*Q) ≤ (√u₁*u₁/l₃² + 2/√l₃)*η`。 -/
theorem ttpX_step6_final (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hdpar : frob (ttpX z * (((ttpX z)ᵀ * ttpX z)⁻¹ * ((ttpX z)ᵀ * (Y - ttpX z))))
      ≤ Real.sqrt (u1:ℝ)
          * ((u1:ℝ) * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2))
    (hdom1 : (u1:ℝ) * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2
      ≤ 1 / 2)
    (hdom2 : (u1:ℝ) * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2
      ≤ Real.sqrt (l3:ℝ) / (2 * Real.sqrt (u1:ℝ))) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      frob (ttpX z - Y * Q)
        ≤ (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2 + 2 / Real.sqrt (l3:ℝ))
          * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ) :=
  step6_final (ttpX z) Y (by norm_num [l3] : (0:ℝ) < (l3:ℝ))
    (by norm_num [u1] : (0:ℝ) < (u1:ℝ))
    (ttpX_quadform_lo z h1 h2) (ttpX_quadform_hi z h1 h2) hdpar hdom1 hdom2

end ThomsonN9.TableB5Polar
