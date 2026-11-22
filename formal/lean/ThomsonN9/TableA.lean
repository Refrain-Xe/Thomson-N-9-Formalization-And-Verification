import Mathlib

/-!
# Table A (Stage B structure-theorem layer): first two items (R12 / r12b)

This module is deliberately self-contained: it imports only `Mathlib`, it does
not import any in-repo solution module (in particular not `ThomsonN9.Solution`),
and it is not imported by any in-repo module — the root module
`ThomsonN9.lean`, `ThomsonN9/Solution.lean`, `scripts/check.sh` and
`lakefile.toml` are untouched, so this file cannot interfere with the parallel
r12a work on the M1 Lean chain.

It materialises the first two items of Table A in `notes/stageb-scope.md`:

* **A5 (L2 forcing identity).** `l2_eps_forcing_identity`: with the four exact
  rational constants of `numerics/bounds/results/l2_rigorous.json`
  (M9 caliber, cap certificate `n9-stage-a4-typedcap-m0748_M9.json`),
  `(1 + R2max) * (E* - certified) = eps_forcing` holds *on the nose* in `ℚ`.
  The JSON field `eps_forcing.identity_check.holds = true` is the Python-side
  (exact `Fraction`) first proof; here the identity is re-proved so that the
  Lean kernel checks it. The four ℚ literals are byte-identical to the JSON
  strings `E_star.value`, `certificate_rebuild.certified_recomputed`,
  `certificate_rebuild.R2max_exact`, `eps_forcing.exact`; the acceptance gate
  `numerics/bounds/r12_tablea_gate.py` re-reads the JSON, recomputes the
  identity with `fractions.Fraction`, extracts the ℚ literals from this file
  by regex and compares the two sides exactly.

* **A2′ (Lemma 4.1 positivity core).** `phiDeriv m t = (2m-1)!!/√((2-2t)^(2m+1))`
  is the m-th derivative of `φ t = (2-2t)^(-1/2)` (notation of
  `numerics/bounds/r9_v2iv_reverify.py:inv_sqrt_pow_iv/dfactorial_odd`).
  `hasDerivAt_phiDeriv` is the induction core of the formula (the derivative of
  `phiDeriv m` at `t` is `phiDeriv (m+1) t`), and `phiDeriv_pos` its strict
  positivity on `t < 1`. These are the two facts that make the Hermite
  interpolation remainder `φ - H = φ^(m)(ξ)/m! · ∏ (t - ν_k)^2` nonnegative
  (Lemma 4.1). The ξ-existence statement of the interpolation error formula is
  deliberately *not* in this file (it is a later Table A / Table B item).
-/

namespace ThomsonN9.TableA

open Real

/-! ### A2′: the odd double factorial and the derivative family of φ -/

/-- `(2m−1)!! = 1·3·⋯·(2m−1)` (`m = 0` → `1`), by recursion. -/
def dfactorialOdd : ℕ → ℚ
  | 0 => 1
  | m + 1 => (2 * m + 1) * dfactorialOdd m

lemma dfactorialOdd_succ (m : ℕ) : dfactorialOdd (m + 1) = (2 * m + 1) * dfactorialOdd m :=
  rfl

lemma dfactorialOdd_pos (m : ℕ) : 0 < dfactorialOdd m := by
  induction m with
  | zero => exact zero_lt_one
  | succ m ih =>
    exact mul_pos (by exact_mod_cast (by omega : (0 : ℕ) < 2 * m + 1)) ih

/-- `φ^{(m)}(t) = (2m−1)!! / √((2−2t)^(2m+1))` — the `m`-th derivative of
`φ t = (2−2t)^(−1/2)` (Lemma 4.1 positivity core, Table A2′). -/
noncomputable def phiDeriv (m : ℕ) (t : ℝ) : ℝ :=
  (dfactorialOdd m : ℝ) / Real.sqrt ((2 - 2 * t) ^ (2 * m + 1))

/-- A2′ (a): strict positivity of `φ^{(m)}` on `t < 1`. -/
theorem phiDeriv_pos (m : ℕ) (t : ℝ) (ht : t < 1) : 0 < phiDeriv m t := by
  have hu : (0 : ℝ) < 2 - 2 * t := by nlinarith
  have h1 : (0 : ℝ) < Real.sqrt ((2 - 2 * t) ^ (2 * m + 1)) :=
    Real.sqrt_pos.2 (by positivity)
  unfold phiDeriv
  exact div_pos (by exact_mod_cast dfactorialOdd_pos m) h1

/-- A2′ (b): the induction core of the derivative formula — `φ^{(m+1)}` is the
derivative of `φ^{(m)}` at every `t < 1`. -/
theorem hasDerivAt_phiDeriv (m : ℕ) (t : ℝ) (ht : t < 1) :
    HasDerivAt (phiDeriv m) (phiDeriv (m + 1) t) t := by
  have hu : (0 : ℝ) < 2 - 2 * t := by nlinarith
  have huden : (0 : ℝ) < (2 - 2 * t) ^ (2 * m + 1) := by positivity
  have hd2 : HasDerivAt (fun s => 2 - 2 * s) (-2 : ℝ) t := by
    simpa using (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id' t)).const_sub (2 : ℝ)
  have hpow := hd2.pow (2 * m + 1)
  rw [show (2 * m + 1 - 1 : ℕ) = 2 * m from by omega] at hpow
  have hs := hpow.sqrt (ne_of_gt huden)
  simp only [Pi.pow_apply] at hs
  have hc : HasDerivAt (fun _ : ℝ => (dfactorialOdd m : ℝ)) 0 t := hasDerivAt_const _ _
  -- simplify the derivative formula of the denominator √((2−2t)^(2m+1))
  have g0 : Real.sqrt ((2 - 2 * t) ^ (2 * m + 1)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 huden)
  have u0 : (2 : ℝ) - 2 * t ≠ 0 := ne_of_gt hu
  have h5 : (((2 * m + 1 : ℕ) : ℝ) * (2 - 2 * t) ^ (2 * m) * -2) /
      (2 * Real.sqrt ((2 - 2 * t) ^ (2 * m + 1))) =
      -(((2 * m + 1 : ℕ) : ℝ) * (2 - 2 * t) ^ (2 * m)) /
        Real.sqrt ((2 - 2 * t) ^ (2 * m + 1)) := by
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero g0) g0]
    ring
  have hdiv := hc.div (hs.congr_deriv h5) g0
  refine hdiv.congr_deriv ?_
  -- value identity, in the unfolded shapes
  have e1 : (2 - 2 * t) ^ (2 * m + 1) = (2 - 2 * t) ^ (2 * m) * (2 - 2 * t) :=
    pow_succ _ (2 * m)
  have e3 : (2 * (m + 1) + 1 : ℕ) = 2 * m + 3 := by omega
  have hn : (2 * m + 3 : ℕ) = 2 + (2 * m + 1) := by omega
  have e2 : Real.sqrt ((2 - 2 * t) ^ (2 * m + 3)) =
      (2 - 2 * t) * Real.sqrt ((2 - 2 * t) ^ (2 * m + 1)) := by
    have h4 : (2 - 2 * t) ^ (2 * m + 3) = (2 - 2 * t) ^ 2 * (2 - 2 * t) ^ (2 * m + 1) := by
      rw [hn, pow_add]
    rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 - 2 * t)]
  have hg2 : (2 - 2 * t) ^ (2 * m) * (2 - 2 * t) =
      Real.sqrt ((2 - 2 * t) ^ (2 * m + 1)) * Real.sqrt ((2 - 2 * t) ^ (2 * m + 1)) := by
    rw [← e1, Real.mul_self_sqrt huden.le]
  have hcast : ((2 * m + 1 : ℕ) : ℝ) * ((dfactorialOdd m : ℚ) : ℝ) =
      ((dfactorialOdd (m + 1) : ℚ) : ℝ) := by
    norm_num [dfactorialOdd_succ]
  simp only [phiDeriv, e3]
  rw [← hcast, e2, mul_div_assoc', div_eq_div_iff (pow_ne_zero 2 g0) (mul_ne_zero u0 g0)]
  rw [sub_mul, mul_assoc, zero_mul, zero_sub, div_mul_eq_mul_div, ← mul_assoc,
    ← mul_div_assoc', div_self g0, mul_one]
  linear_combination ((2 * m + 1 : ℕ) : ℝ) * ((dfactorialOdd m : ℚ) : ℝ) * hg2

/-! ### A5: the L2 forcing identity (exact rational arithmetic) -/

/-- **A5 (L2 forcing identity).** With `E* = 25759986531/10^9` (decimal caliber,
D28 ruling 3), `certified` the exactly recomputed certified bound,
`R2max` the exact R2 weighted-ℓ¹ constant and `ε_forcing` the exact forcing
slack, all four taken verbatim from `numerics/bounds/results/l2_rigorous.json`
(M9 caliber), the forcing identity
`(1 + R2max) * (E* - certified) = ε_forcing` holds exactly in `ℚ`. -/
theorem l2_eps_forcing_identity :
    (1 + (13061183578204185028042533804651605715226289625871361755884583812810354220763 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000) *
      ((25759986531 : ℚ) / 1000000000 -
        (22879340185047884591327492399406419521507688973060989923169472604058682918548583984375 : ℚ) / 888178445822492388747275390557723859303211430452579251742723511769167625620708441526) =
      (62308232016279826168812154155836080188260221347417966571668186047549261057992006380543153 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000 := by
  norm_num

end ThomsonN9.TableA
