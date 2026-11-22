import Mathlib

/-!
# Table A (Stage B structure-theorem layer): item A4 (R13 / r13a)

This module is deliberately self-contained: it imports only `Mathlib`, it does
not import any in-repo solution module (in particular not `ThomsonN9.Solution`
nor `ThomsonN9.TableA`), and it is not imported by any in-repo module — the
root module `ThomsonN9.lean`, `ThomsonN9/Solution.lean`,
`ThomsonN9/M1Data.lean`, `scripts/check.sh` and `lakefile.toml` are untouched,
so this file cannot interfere with the parallel r13b/r13c work (file-face
zero overlap).

It materialises the S₃-quotient expansion structure core of item A4 in
`notes/stageb-scope.md` (`numerics/bounds/r9_s3_rederive.py` full-chain
second implementation; `numerics/bounds/typed_ladder.py:275-285`):

* **Q-kernel recursion.** `Q : ℕ → ℚ → ℚ → ℚ → ℚ` with
  `Q₀ = 1`, `Q₁ = t − u·v`,
  `Q_{j+2} = 2(t−u·v)·Q_{j+1} − (1−u²−v²+u²v²)·Q_j`
  (`numerics/bounds/sdp_bound.py:176` `build_Q`: `Q_0=1, Q_1=t−uv,
  Q_{k+2}=2(t−uv)Q_{k+1}−(1−u²)(1−v²)Q_k`, where
  `(1−u²)(1−v²) = 1−u²−v²+u²v²`).

* **Symmetry theorem.** `Q_symm : ∀ m u v t, Q m u v t = Q m v u t`
  (induction on `m` with `Nat.strongRecOn`; the step is `ring`). This is the
  structural fact audited as `Q_uv_symmetric_all_k` in
  `numerics/bounds/results/r9_s3_rederive.json` (`structural_checks`).

* **Explicit shapes `k ≤ 5`** (`Q_zero` … `Q_five`, `simp only [Q]; ring`):
  the fully expanded polynomial forms of `Q₀,…,Q₅`, matching the `K = 6`
  recursion of the M9/M7 certificates (`params.K = 6`).

* **Y-column count.** `ycol_count : ∑ k ∈ Finset.range 6, (9−k)^2 = 271`
  (`decide`): with `M = 9`, `K = 6` the unsymmetrised kernel columns are
  `Y[k,a,b] = u^a v^b · Q_k` with `a, b < 9 − k`, i.e. `271` columns in total
  (`sizes.Y_cols = 271`, `structural_checks.Y_cols_equals_271` in
  `numerics/bounds/results/r9_s3_rederive.json`).

* **Stretch: one nontrivial K-column expansion.** `Kcol 2 3 1 u v t
  = −2·(Y + Y^{(u,t,v)} + Y^{(v,t,u)})` expanded into an explicit polynomial
  (`Kcol_two_three_one`, `simp only [Kcol, Ycol, Q]; ring`), mirroring the
  F-block column construction `K_cols = −2(Y + Y^{(u,t,v)} + Y^{(v,t,u)})`
  (`numerics/bounds/typed_ladder.py`, `QuotientMaps.__init__`).
  The full 271-column symbolic assembly is deliberately *not* in this file
  (the numerical face is carried by r13c A1 plus the Python second
  implementation).
-/

namespace ThomsonN9.TableA4

/-! ### A4: the Q-kernel recursion and its symmetry -/

/-- **Q 核递推**：`Q₀ = 1`、`Q₁ = t − u·v`、
`Q_{j+2} = 2(t−u·v)·Q_{j+1} − (1−u²−v²+u²v²)·Q_j`. -/
def Q : ℕ → ℚ → ℚ → ℚ → ℚ
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | j + 2, u, v, t =>
    2 * (t - u * v) * Q (j + 1) u v t - (1 - u * u - v * v + u * u * v * v) * Q j u v t

/-- **A4 对称性定理**：`Q_k` 对 `(u, v)` 对称（`r9_s3_rederive.json`
`structural_checks.Q_uv_symmetric_all_k` 的 Lean 内核版）. -/
theorem Q_symm : ∀ (m : ℕ) (u v t : ℚ), Q m u v t = Q m v u t := by
  intro m u v t
  induction m using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | n
    · rfl
    · show (t - u * v : ℚ) = t - v * u
      ring
    · simp only [Q]
      rw [ih (n + 1) (by omega), ih n (by omega)]
      ring

/-! ### A4: explicit shapes `k ≤ 5` -/

theorem Q_zero (u v t : ℚ) : Q 0 u v t = 1 := rfl

theorem Q_one (u v t : ℚ) : Q 1 u v t = t - u * v := rfl

theorem Q_two (u v t : ℚ) :
    Q 2 u v t = 2 * t ^ 2 - 4 * u * v * t + u ^ 2 * v ^ 2 + u ^ 2 + v ^ 2 - 1 := by
  simp only [Q]; ring

theorem Q_three (u v t : ℚ) :
    Q 3 u v t = -3 * t + 4 * t ^ 3 + 3 * v ^ 2 * t + 3 * u * v - 12 * u * v * t ^ 2
      - 3 * u * v ^ 3 + 3 * u ^ 2 * t + 9 * u ^ 2 * v ^ 2 * t - 3 * u ^ 3 * v
      - u ^ 3 * v ^ 3 := by
  simp only [Q]; ring

theorem Q_four (u v t : ℚ) :
    Q 4 u v t = 1 - 8 * t ^ 2 + 8 * t ^ 4 - 2 * v ^ 2 + 8 * v ^ 2 * t ^ 2 + v ^ 4
      + 16 * u * v * t - 32 * u * v * t ^ 3 - 16 * u * v ^ 3 * t - 2 * u ^ 2
      + 8 * u ^ 2 * t ^ 2 - 4 * u ^ 2 * v ^ 2 + 40 * u ^ 2 * v ^ 2 * t ^ 2
      + 6 * u ^ 2 * v ^ 4 - 16 * u ^ 3 * v * t - 16 * u ^ 3 * v ^ 3 * t + u ^ 4
      + 6 * u ^ 4 * v ^ 2 + u ^ 4 * v ^ 4 := by
  simp only [Q]; ring

theorem Q_five (u v t : ℚ) :
    Q 5 u v t = 5 * t - 20 * t ^ 3 + 16 * t ^ 5 - 10 * v ^ 2 * t + 20 * v ^ 2 * t ^ 3
      + 5 * v ^ 4 * t - 5 * u * v + 60 * u * v * t ^ 2 - 80 * u * v * t ^ 4
      + 10 * u * v ^ 3 - 60 * u * v ^ 3 * t ^ 2 - 5 * u * v ^ 5 - 10 * u ^ 2 * t
      + 20 * u ^ 2 * t ^ 3 - 40 * u ^ 2 * v ^ 2 * t + 140 * u ^ 2 * v ^ 2 * t ^ 3
      + 50 * u ^ 2 * v ^ 4 * t + 10 * u ^ 3 * v - 60 * u ^ 3 * v * t ^ 2
      - 100 * u ^ 3 * v ^ 3 * t ^ 2 - 10 * u ^ 3 * v ^ 5 + 5 * u ^ 4 * t
      + 50 * u ^ 4 * v ^ 2 * t + 25 * u ^ 4 * v ^ 4 * t - 5 * u ^ 5 * v
      - 10 * u ^ 5 * v ^ 3 - u ^ 5 * v ^ 5 := by
  simp only [Q]; ring

/-! ### A4: the Y-column count (`271`) -/

/-- **Y 列计数**：`K = 6` 个核层、`M = 9` 时未对称化核列
`Y[k,a,b] = u^a v^b Q_k`（`a, b < 9 − k`）共
`∑_{k<6} (9−k)² = 81+64+49+36+25+16 = 271` 列
（`r9_s3_rederive.json` `sizes.Y_cols = 271`）. -/
theorem ycol_count : ∑ k ∈ Finset.range 6, (9 - k) ^ 2 = 271 := by decide

/-! ### A4 (stretch): one nontrivial K-column expansion identity -/

/-- 未对称化核列 `Y[k,a,b] = u^a v^b · Q_k(u,v,t)` 的求值形状. -/
def Ycol (k a b : ℕ) (u v t : ℚ) : ℚ := u ^ a * v ^ b * Q k u v t

/-- F 块列：`K_col = −2·(Y + Y^{(u,t,v)} + Y^{(v,t,u)})`，其中
`Y^{(u,t,v)}` 即多项式 `p ↦ p(u,t,v)`（typed_ladder.py `QuotientMaps` 的
`Y3_cols = ring.perm(c, 3)`、`Y5_cols = ring.perm(c, 5)`）. -/
def Kcol (k a b : ℕ) (u v t : ℚ) : ℚ :=
  -2 * (Ycol k a b u v t + u ^ a * t ^ b * Q k u t v + v ^ a * t ^ b * Q k v t u)

/-- **stretch 展开恒等式**：非平凡列 `(k,a,b) = (2,3,1)` 的
`K_col = −2(Y + Y^{(u,t,v)} + Y^{(v,t,u)})` 完全展开为显式多项式. -/
theorem Kcol_two_three_one (u v t : ℚ) :
    Kcol 2 3 1 u v t =
      2 * v ^ 3 * t - 2 * v ^ 3 * t ^ 3 - 2 * v ^ 5 * t - 2 * v ^ 5 * t ^ 3
        + 8 * u * v ^ 4 * t ^ 2 - 4 * u ^ 2 * v ^ 3 * t + 2 * u ^ 3 * t
        - 2 * u ^ 3 * t ^ 3 + 2 * u ^ 3 * v - 4 * u ^ 3 * v * t ^ 2
        - 4 * u ^ 3 * v ^ 2 * t - 2 * u ^ 3 * v ^ 3 + 8 * u ^ 4 * v * t ^ 2
        + 8 * u ^ 4 * v ^ 2 * t - 2 * u ^ 5 * t - 2 * u ^ 5 * t ^ 3 - 2 * u ^ 5 * v
        - 2 * u ^ 5 * v ^ 3 := by
  simp only [Kcol, Ycol, Q]; ring

end ThomsonN9.TableA4
