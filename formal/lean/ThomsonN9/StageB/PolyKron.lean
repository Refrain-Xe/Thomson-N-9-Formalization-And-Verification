import Mathlib
import ThomsonN9.StageB.ThreePoint

/-!
# Thomson N = 9 Stage B — Module 2: Kronecker Polynomials, Zero-Δ Cholesky SOS, & Bernstein 1D

Provides the core kernel-verified certificate engine (zero `Δ` matrices, zero `LDLᵀ` inside Lean):
1. 1D integer polynomials (`peval`, `padd`, `pmul`, `ppow`) and exact Bernstein positivity
   (`BPiece`, `BPiece.check`, `BPiece.nonneg`).
2. 1D zero-Δ Cholesky SOS (`chol1DEv`, `chol1DPoly`, `peval_chol1DPoly`) for `H(t) ≤ (1 + R2) φ(t)`
   in the rationalized variable `y = √((1 - t) / 2)`.
3. 3D sparse integer polynomials (`Poly3`), fast GMP Kronecker evaluation `kev3 w D` using
   `Nat.shiftLeft 1`, exact zero-Δ Cholesky 3D blocks (`CholPlainBlk`, `CholStdBlk`),
   exact zero-Δ Cholesky harmonic blocks (`CholHarmBlk`), `HasPolyRep3` closure lemmas,
   and the master base-`2^w` uniqueness theorem `eq_zero_of_kev3_zero`.
-/

set_option maxHeartbeats 2000000

namespace ThomsonN9.StageB.PolyKron

open Finset ThomsonN9.StageB
open scoped RealInnerProductSpace

/-! ## Section 1: 1D Integer Polynomials & Exact Bernstein Positivity -/

def peval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: as, y => (a : ℝ) + y * peval as y

def pevalZ : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: as, y => a + y * pevalZ as y

def l1List (p : List ℤ) : ℕ :=
  p.foldl (fun acc a => acc + a.natAbs) 0

def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

def pscale (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

def pneg (p : List ℤ) : List ℤ := p.map (- ·)

def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, q => padd (pscale a q) (0 :: pmul as q)

def ppow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => pmul p (ppow p n)

lemma cast_pevalZ (p : List ℤ) (y : ℤ) : ((pevalZ p y : ℤ) : ℝ) = peval p (y : ℝ) := by
  induction p with
  | nil => simp [pevalZ, peval]
  | cons a as ih => simp only [pevalZ, peval]; push_cast; rw [ih]

lemma peval_padd (p q : List ℤ) (y : ℝ) : peval (padd p q) y = peval p y + peval q y := by
  induction p generalizing q with
  | nil => simp [padd, peval]
  | cons a as ih =>
    cases q with
    | nil => simp [padd, peval]
    | cons b bs => simp only [padd, peval, ih]; push_cast; ring

lemma peval_pscale (c : ℤ) (p : List ℤ) (y : ℝ) : peval (pscale c p) y = (c : ℝ) * peval p y := by
  induction p with
  | nil => simp [pscale, peval]
  | cons a as ih =>
    simp only [pscale, List.map_cons, peval]
    change (c * a : ℤ) + y * peval (pscale c as) y = (c : ℝ) * ((a : ℝ) + y * peval as y)
    rw [ih]; push_cast; ring

lemma peval_pneg (p : List ℤ) (y : ℝ) : peval (pneg p) y = -peval p y := by
  induction p with
  | nil => simp [pneg, peval]
  | cons a as ih =>
    simp only [pneg, List.map_cons, peval]
    change (-a : ℤ) + y * peval (pneg as) y = -((a : ℝ) + y * peval as y)
    rw [ih]; push_cast; ring

lemma peval_pmul (p q : List ℤ) (y : ℝ) : peval (pmul p q) y = peval p y * peval q y := by
  induction p with
  | nil => simp [pmul, peval]
  | cons a as ih =>
    simp only [pmul, peval_padd, peval_pscale, peval, ih]; push_cast; ring

lemma peval_ppow (p : List ℤ) (n : ℕ) (y : ℝ) : peval (ppow p n) y = peval p y ^ n := by
  induction n with
  | zero => simp [ppow, peval]
  | succ n ih => simp only [ppow, peval_pmul, ih, pow_succ]; ring

lemma peval_eq_zero_of_all (p : List ℤ) (h : p.all (· == 0) = true) (y : ℝ) : peval p y = 0 := by
  induction p with
  | nil => simp [peval]
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [peval, h.1, ih h.2]

/-- Direct real weighted ℓ¹ bound `∑_j |a_j| * w^j`. -/
def pevalAbsR : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: as, w => |(a : ℝ)| + w * pevalAbsR as w

lemma abs_peval_le_pevalAbsR (p : List ℤ) {y w : ℝ} (hy0 : 0 ≤ y) (hyw : y ≤ w) :
    |peval p y| ≤ pevalAbsR p w := by
  induction p with
  | nil => simp [peval, pevalAbsR]
  | cons a as ih =>
    simp only [peval, pevalAbsR]
    have h1 : |(a : ℝ) + y * peval as y| ≤ |(a : ℝ)| + |y * peval as y| := abs_add_le _ _
    have h2 : |y * peval as y| = y * |peval as y| := by rw [abs_mul, abs_of_nonneg hy0]
    have h3 : y * |peval as y| ≤ w * pevalAbsR as w :=
      mul_le_mul hyw ih (abs_nonneg _) (le_trans hy0 hyw)
    linarith

lemma pevalAbsR_nonneg (p : List ℤ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ pevalAbsR p w := by
  induction p with
  | nil => simp [pevalAbsR]
  | cons a as ih => simp only [pevalAbsR]; positivity

/-- 1D zero-Δ Cholesky SOS: sum of squares of 1D integer polynomials. -/
def chol1DEv (cols : List (List ℤ)) (y : ℝ) : ℝ :=
  (cols.map fun col => peval col y ^ 2).sum

def chol1DPoly (cols : List (List ℤ)) : List ℤ :=
  cols.foldl (fun acc col => padd acc (pmul col col)) []

lemma chol1DEv_nonneg (cols : List (List ℤ)) (y : ℝ) : 0 ≤ chol1DEv cols y := by
  unfold chol1DEv
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨col, _, rfl⟩ := hx
  exact sq_nonneg _

lemma peval_chol1DPoly_aux (cols : List (List ℤ)) (acc : List ℤ) (y : ℝ) :
    peval (cols.foldl (fun a c => padd a (pmul c c)) acc) y =
      peval acc y + (cols.map fun c => peval c y ^ 2).sum := by
  induction cols generalizing acc with
  | nil => simp
  | cons col cs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, peval_padd, peval_pmul]
    ring

lemma peval_chol1DPoly (cols : List (List ℤ)) (y : ℝ) :
    peval (chol1DPoly cols) y = chol1DEv cols y := by
  unfold chol1DPoly chol1DEv
  rw [peval_chol1DPoly_aux]
  simp [peval]

/-- Bernstein sum `∑_i β_i a^i b^(n-i)`. -/
def bernSum (a b : List ℤ) (n : ℕ) : ℕ → List ℕ → List ℤ
  | _, [] => []
  | i, β :: bs =>
    padd (pscale (β : ℤ) (pmul (ppow a i) (ppow b (n - i)))) (bernSum a b n (i + 1) bs)

lemma bernSum_nonneg (a b : List ℤ) (n : ℕ) (y : ℝ) (ha : 0 ≤ peval a y) (hb : 0 ≤ peval b y)
    (bs : List ℕ) : ∀ i : ℕ, 0 ≤ peval (bernSum a b n i bs) y := by
  induction bs with
  | nil => intro i; simp [bernSum, peval]
  | cons β bs ih =>
    intro i
    simp only [bernSum, peval_padd, peval_pscale, peval_pmul, peval_ppow]
    exact add_nonneg (mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)))
      (ih (i + 1))

structure BPiece where
  u1 : ℤ
  u2 : ℕ
  w1 : ℤ
  w2 : ℕ
  Lam : ℕ
  β : List ℕ

def BPiece.diff (P : List ℤ) (c : BPiece) : List ℤ :=
  padd (pscale (c.Lam : ℤ) P)
    (pneg (bernSum [-c.u1, (c.u2 : ℤ)] [c.w1, -(c.w2 : ℤ)] (c.β.length - 1) 0 c.β))

def BPiece.check (P : List ℤ) (c : BPiece) : Bool :=
  0 < c.Lam && 0 < c.u2 && 0 < c.w2 && (c.diff P).all (· == 0)

theorem BPiece.nonneg (P : List ℤ) (c : BPiece) (hc : c.check P = true) {y : ℝ}
    (h0 : (c.u1 : ℝ) ≤ c.u2 * y) (h1 : (c.w2 : ℝ) * y ≤ c.w1) : 0 ≤ peval P y := by
  simp only [BPiece.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hL, -⟩, -⟩, hz⟩ := hc
  have h := peval_eq_zero_of_all _ hz y
  simp only [BPiece.diff, peval_padd, peval_pscale, peval_pneg] at h
  have ha : 0 ≤ peval [-c.u1, (c.u2 : ℤ)] y := by simp only [peval]; push_cast; linarith
  have hb : 0 ≤ peval [c.w1, -(c.w2 : ℤ)] y := by simp only [peval]; push_cast; linarith
  have hs := bernSum_nonneg _ _ (c.β.length - 1) y ha hb c.β 0
  have hLam : (0 : ℝ) < c.Lam := by exact_mod_cast hL
  have h2 : 0 ≤ (c.Lam : ℝ) * peval P y := by push_cast at h; linarith
  exact nonneg_of_mul_nonneg_right h2 hLam

/-! ## Section 2: 3D Sparse Polynomials & Master Base-`2^w` Kronecker Uniqueness -/

/-- Helper lemma: shifting an additive `List.foldl` accumulator over `ℕ`. -/
lemma foldl_add_shift {α : Type*} (g : α → ℕ) (l : List α) (acc : ℕ) :
    l.foldl (fun a x => a + g x) acc = acc + l.foldl (fun a x => a + g x) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (acc + g x), ih (g x)]
    omega

/-- Sparse 3-variable integer polynomial as a list of `(coeff, a, b, d)` meaning `c * u^a * v^b * t^d`. -/
abbrev Poly3 := List (ℤ × ℕ × ℕ × ℕ)

/-- Evaluate a sparse 3D polynomial at `(u, v, t) ∈ ℝ³`. -/
def ev3 (p : Poly3) (u v t : ℝ) : ℝ :=
  (p.map fun x => (x.1 : ℝ) * u ^ x.2.1 * v ^ x.2.2.1 * t ^ x.2.2.2).sum

/-- Fast GMP Kronecker evaluation of `p` at `(2^eu, 2^ev, 2^et)` using `Nat.shiftLeft 1`. -/
def kev3Shift (eu ev et : ℕ) (p : Poly3) : ℤ :=
  p.foldl (fun acc x => acc + x.1 * ((Nat.shiftLeft 1 (eu * x.2.1 + ev * x.2.2.1 + et * x.2.2.2) : ℕ) : ℤ)) 0

/-- Fast GMP Kronecker evaluation of `p` at `(2^w, 2^(w*D), 2^(w*D*D))` using `Nat.shiftLeft 1`. -/
def kev3 (w D : ℕ) (p : Poly3) : ℤ :=
  p.foldl (fun acc x => acc + x.1 * ((Nat.shiftLeft 1 (w * (x.2.1 + D * x.2.2.1 + D * D * x.2.2.2)) : ℕ) : ℤ)) 0

lemma nat_shiftLeft_one_cast_int (k : ℕ) : ((Nat.shiftLeft 1 k : ℕ) : ℤ) = (2 : ℤ) ^ k := by
  change ((1 <<< k : ℕ) : ℤ) = (2 : ℤ) ^ k
  rw [Nat.shiftLeft_eq, one_mul]; push_cast; rfl

lemma nat_shiftLeft_one_cast_real (k : ℕ) : ((Nat.shiftLeft 1 k : ℕ) : ℝ) = (2 : ℝ) ^ k := by
  change ((1 <<< k : ℕ) : ℝ) = (2 : ℝ) ^ k
  rw [Nat.shiftLeft_eq, one_mul]; push_cast; rfl

lemma cast_kev3Shift_aux (eu ev et : ℕ) (p : Poly3) (acc : ℤ) :
    ((p.foldl (fun a x => a + x.1 * ((Nat.shiftLeft 1 (eu * x.2.1 + ev * x.2.2.1 + et * x.2.2.2) : ℕ) : ℤ)) acc : ℤ) : ℝ) =
      (acc : ℝ) + ev3 p ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
  induction p generalizing acc with
  | nil => simp [ev3]
  | cons x xs ih =>
    simp only [List.foldl_cons, ev3, List.map_cons, List.sum_cons, ih]
    push_cast
    rw [nat_shiftLeft_one_cast_real]
    have hexp : (2 : ℝ) ^ (eu * x.2.1 + ev * x.2.2.1 + et * x.2.2.2) =
        ((2 : ℝ) ^ eu) ^ x.2.1 * ((2 : ℝ) ^ ev) ^ x.2.2.1 * ((2 : ℝ) ^ et) ^ x.2.2.2 := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    rw [hexp]; ring

lemma cast_kev3Shift (eu ev et : ℕ) (p : Poly3) :
    ((kev3Shift eu ev et p : ℤ) : ℝ) = ev3 p ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
  unfold kev3Shift
  rw [cast_kev3Shift_aux]
  simp

lemma cast_kev3_aux (w D : ℕ) (p : Poly3) (acc : ℤ) :
    ((p.foldl (fun a x => a + x.1 * ((Nat.shiftLeft 1 (w * (x.2.1 + D * x.2.2.1 + D * D * x.2.2.2)) : ℕ) : ℤ)) acc : ℤ) : ℝ) =
      (acc : ℝ) + ev3 p ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
  induction p generalizing acc with
  | nil => simp [ev3]
  | cons x xs ih =>
    simp only [List.foldl_cons, ev3, List.map_cons, List.sum_cons, ih]
    push_cast
    rw [nat_shiftLeft_one_cast_real]
    have hexp : (2 : ℝ) ^ (w * (x.2.1 + D * x.2.2.1 + D * D * x.2.2.2)) =
        ((2 : ℝ) ^ w) ^ x.2.1 * ((2 : ℝ) ^ (w * D)) ^ x.2.2.1 * ((2 : ℝ) ^ (w * D * D)) ^ x.2.2.2 := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1; ring
    rw [hexp]; ring

lemma cast_kev3 (w D : ℕ) (p : Poly3) :
    ((kev3 w D p : ℤ) : ℝ) = ev3 p ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
  unfold kev3
  rw [cast_kev3_aux]
  simp

/-- ℓ¹ coefficient bound of a sparse 3D polynomial. -/
def l1Poly3 (p : Poly3) : ℕ :=
  p.foldl (fun acc x => acc + x.1.natAbs) 0

lemma abs_peval_le_l1List (p : List ℤ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |peval p y| ≤ (l1List p : ℝ) := by
  have haux : ∀ (l : List ℤ), |peval l y| ≤ (l.foldl (fun acc a => acc + a.natAbs) 0 : ℕ) := by
    intro l
    induction l with
    | nil => simp [peval]
    | cons a as ih =>
      simp only [peval, List.foldl_cons, zero_add]
      rw [foldl_add_shift Int.natAbs as a.natAbs]
      push_cast
      have h1 : |(a : ℝ) + y * peval as y| ≤ |(a : ℝ)| + |y * peval as y| := abs_add_le _ _
      have h2 : |y * peval as y| = y * |peval as y| := by rw [abs_mul, abs_of_nonneg hy0]
      have h3 : y * |peval as y| ≤ 1 * |peval as y| := mul_le_mul_of_nonneg_right hy1 (abs_nonneg _)
      have h4 : |(a : ℝ)| = (a.natAbs : ℝ) := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; rfl
      linarith
  exact haux p

lemma abs_ev3_le_l1Poly3 (p : Poly3) {u v t : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1) (ht : |t| ≤ 1) :
    |ev3 p u v t| ≤ (l1Poly3 p : ℝ) := by
  unfold l1Poly3
  induction p with
  | nil => simp [ev3]
  | cons x xs ih =>
    simp only [ev3, List.map_cons, List.sum_cons, List.foldl_cons, zero_add]
    rw [foldl_add_shift (fun y : ℤ × ℕ × ℕ × ℕ => y.1.natAbs) xs x.1.natAbs]
    push_cast
    have htri := abs_add_le ((x.1 : ℝ) * u ^ x.2.1 * v ^ x.2.2.1 * t ^ x.2.2.2) (ev3 xs u v t)
    have hm : |(x.1 : ℝ) * u ^ x.2.1 * v ^ x.2.2.1 * t ^ x.2.2.2| ≤ (x.1.natAbs : ℝ) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
      have h1 : |u| ^ x.2.1 ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
      have h2 : |v| ^ x.2.2.1 ≤ 1 := pow_le_one₀ (abs_nonneg _) hv
      have h3 : |t| ^ x.2.2.2 ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
      have ha : |(x.1 : ℝ)| = (x.1.natAbs : ℝ) := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; rfl
      rw [ha]
      have hp12 : |u| ^ x.2.1 * |v| ^ x.2.2.1 ≤ 1 := by nlinarith [pow_nonneg (abs_nonneg u) x.2.1]
      have hp123 : |u| ^ x.2.1 * |v| ^ x.2.2.1 * |t| ^ x.2.2.2 ≤ 1 := by
        nlinarith [pow_nonneg (abs_nonneg t) x.2.2.2, pow_nonneg (abs_nonneg u) x.2.1, pow_nonneg (abs_nonneg v) x.2.2.1]
      nlinarith [Nat.cast_nonneg (α := ℝ) x.1.natAbs]
    change |_ + ev3 xs u v t| ≤ _
    linarith

/-- A real function `f : ℝ → ℝ → ℝ → ℝ` has an integer polynomial representation with
coordinate degrees `≤ (da, db, dc)` and total coefficient ℓ¹ norm `≤ L`. -/
def HasPolyRep3 (da db dc L : ℕ) (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ c : Fin (da + 1) → Fin (db + 1) → Fin (dc + 1) → ℤ,
    (∀ u v t : ℝ, f u v t =
      ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1),
        (c a b d : ℝ) * u ^ (a : ℕ) * v ^ (b : ℕ) * t ^ (d : ℕ)) ∧
    (∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c a b d).natAbs) ≤ L

lemma HasPolyRep3.congr {da db dc L : ℕ} {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) (heq : ∀ u v t, f u v t = g u v t) :
    HasPolyRep3 da db dc L g := by
  obtain ⟨c, hfev, hcl1⟩ := hf
  exact ⟨c, fun u v t => (heq u v t).symm.trans (hfev u v t), hcl1⟩

/-- Core 1D base-`B` uniqueness: if `∑_{k < N} r_k * B^k = 0` and `∑ |r_k| < B` (with `B ≥ 2`),
then `r_k = 0` for all `k`! -/
lemma base_eval_eq_zero_imp {N B : ℕ} (hB : 2 ≤ B) (r : Fin N → ℤ)
    (hsum : (∑ k : Fin N, (r k : ℝ) * (B : ℝ) ^ (k : ℕ)) = 0)
    (hl1 : (∑ k : Fin N, (r k).natAbs) < B) :
    ∀ k : Fin N, r k = 0 := by
  have hsumZ : (∑ k : Fin N, r k * (B : ℤ) ^ (k : ℕ)) = 0 := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    exact hsum
  by_contra hne
  push Not at hne
  let S : Finset (Fin N) := Finset.univ.filter (fun k => r k ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨k0, hk0⟩ := hne
    exact ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0⟩⟩
  let k1 : Fin N := S.max' hS
  have hk1_mem : k1 ∈ S := Finset.max'_mem S hS
  have hk1_ne : r k1 ≠ 0 := (Finset.mem_filter.mp hk1_mem).2
  have hk1_max : ∀ k : Fin N, k1 < k → r k = 0 := by
    intro k hk
    by_contra h
    have hmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    exact absurd (Finset.le_max' S k hmem) (not_le.mpr hk)
  have hsplit : r k1 * (B : ℤ) ^ (k1 : ℕ) =
      -(∑ k ∈ Finset.univ.filter (· < k1), r k * (B : ℤ) ^ (k : ℕ)) := by
    have hall : ∑ k : Fin N, r k * (B : ℤ) ^ (k : ℕ) =
        r k1 * (B : ℤ) ^ (k1 : ℕ) + ∑ k ∈ Finset.univ.filter (· < k1), r k * (B : ℤ) ^ (k : ℕ) := by
      have hpart : ∀ k : Fin N, r k * (B : ℤ) ^ (k : ℕ) =
          (if k = k1 then r k * (B : ℤ) ^ (k : ℕ) else 0)
          + (if k < k1 then r k * (B : ℤ) ^ (k : ℕ) else 0) := by
        intro k
        rcases lt_trichotomy k k1 with h | rfl | h
        · simp [h, ne_of_lt]
        · simp
        · simp [hk1_max k h, ne_of_gt h, not_lt.mpr (le_of_lt h)]
      conv_lhs => arg 2; ext k; rw [hpart k]
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_filter]
    linarith
  have hBpos : (0 : ℤ) < B := by omega
  have h1 : (B : ℤ) ^ (k1 : ℕ) ≤ |r k1 * (B : ℤ) ^ (k1 : ℕ)| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hBpos) _)]
    have habs : (1 : ℤ) ≤ |r k1| := Int.one_le_abs hk1_ne
    nlinarith [pow_pos hBpos (k1 : ℕ)]
  have h2 : |r k1 * (B : ℤ) ^ (k1 : ℕ)| ≤
      ∑ k ∈ Finset.univ.filter (· < k1), |r k| * (B : ℤ) ^ (k : ℕ) := by
    rw [hsplit, abs_neg]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hBpos) _)]
  by_cases hk0 : (k1 : ℕ) = 0
  · have hemp : Finset.univ.filter (· < k1) = ∅ := by
      ext k; simp [Fin.lt_def, hk0]
    rw [hemp, Finset.sum_empty] at h2
    have hpos : (0 : ℤ) < (B : ℤ) ^ (k1 : ℕ) := pow_pos hBpos _
    linarith
  · have h3 : ∑ k ∈ Finset.univ.filter (· < k1), |r k| * (B : ℤ) ^ (k : ℕ) ≤
        (∑ k ∈ Finset.univ.filter (· < k1), |r k|) * (B : ℤ) ^ ((k1 : ℕ) - 1) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hlt : (k : ℕ) < (k1 : ℕ) := (Finset.mem_filter.mp hk).2
      have hle : (k : ℕ) ≤ (k1 : ℕ) - 1 := by omega
      have hpow : (B : ℤ) ^ (k : ℕ) ≤ (B : ℤ) ^ ((k1 : ℕ) - 1) :=
        pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ B) hle
      exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    have h4 : (∑ k ∈ Finset.univ.filter (· < k1), |r k|) < (B : ℤ) := by
      have hsub : (∑ k ∈ Finset.univ.filter (· < k1), (r k).natAbs) ≤
          ∑ k : Fin N, (r k).natAbs :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      have hltN : (∑ k ∈ Finset.univ.filter (· < k1), (r k).natAbs) < B := lt_of_le_of_lt hsub hl1
      have hcast : (∑ k ∈ Finset.univ.filter (· < k1), |r k|) =
          ((∑ k ∈ Finset.univ.filter (· < k1), (r k).natAbs : ℕ) : ℤ) := by
        push_cast; rfl
      rw [hcast]; exact_mod_cast hltN
    have hpow_eq : (B : ℤ) * (B : ℤ) ^ ((k1 : ℕ) - 1) = (B : ℤ) ^ (k1 : ℕ) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    have h5 : (∑ k ∈ Finset.univ.filter (· < k1), |r k|) * (B : ℤ) ^ ((k1 : ℕ) - 1) < (B : ℤ) ^ (k1 : ℕ) := by
      rw [← hpow_eq]
      exact mul_lt_mul_of_pos_right h4 (pow_pos hBpos _)
    linarith

/-- **Master 3D Kronecker Uniqueness Theorem**:
If `f` has a degree-`< D` integer polynomial representation with `ℓ¹` bound `L < 2^w` (`w ≥ 1`)
and vanishes at the Kronecker point `(2^w, 2^(w*D), 2^(w*D*D))`, then `f ≡ 0` on ALL of `ℝ³`! -/
theorem eq_zero_of_kev3_zero {da db dc D w L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hw : 1 ≤ w) (hda : da < D) (hdb : db < D) (hdc : dc < D)
    (hrep : HasPolyRep3 da db dc L f)
    (hL : L < 2 ^ w)
    (hzero : f ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) = 0) :
    ∀ u v t : ℝ, f u v t = 0 := by
  obtain ⟨c, hfev, hcl1⟩ := hrep
  let r : Fin (D * D * D) → ℤ := fun k =>
    let a := k.val % D
    let b := (k.val / D) % D
    let d := k.val / (D * D)
    if ha : a ≤ da then if hb : b ≤ db then if hd : d ≤ dc then
      c ⟨a, Nat.lt_succ_of_le ha⟩ ⟨b, Nat.lt_succ_of_le hb⟩ ⟨d, Nat.lt_succ_of_le hd⟩
    else 0 else 0 else 0
  have hDpos : 0 < D := by omega
  let idx : Fin (da + 1) × Fin (db + 1) × Fin (dc + 1) → Fin (D * D * D) := fun ⟨a, b, d⟩ =>
    ⟨a.val + D * b.val + D * D * d.val, by
      have ha' : a.val < D := by omega
      have hb' : b.val < D := by omega
      have hd' : d.val < D := by omega
      nlinarith⟩
  have hidx_a : ∀ p, (idx p).val % D = p.1.val := by
    intro ⟨a, b, d⟩
    have ha' : a.val < D := by omega
    have h1 : a.val + D * b.val + D * D * d.val = a.val + D * (b.val + D * d.val) := by ring
    simp only [idx, h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']
  have hidx_b : ∀ p, ((idx p).val / D) % D = p.2.1.val := by
    intro ⟨a, b, d⟩
    have ha' : a.val < D := by omega
    have hb' : b.val < D := by omega
    have h1 : a.val + D * b.val + D * D * d.val = a.val + D * (b.val + D * d.val) := by ring
    simp only [idx, h1, Nat.add_mul_div_left _ _ hDpos, Nat.div_eq_of_lt ha', zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
  have hidx_d : ∀ p, (idx p).val / (D * D) = p.2.2.val := by
    intro ⟨a, b, d⟩
    have ha' : a.val < D := by omega
    have hb' : b.val < D := by omega
    have hDD : 0 < D * D := Nat.mul_pos hDpos hDpos
    have hlt : a.val + D * b.val < D * D := by nlinarith
    simp only [idx, Nat.add_mul_div_left _ _ hDD, Nat.div_eq_of_lt hlt, zero_add]
  have hidx_inj : Function.Injective idx := by
    intro p1 p2 h
    have h1 : p1.1.val = p2.1.val := by rw [← hidx_a p1, h, hidx_a p2]
    have h2 : p1.2.1.val = p2.2.1.val := by rw [← hidx_b p1, h, hidx_b p2]
    have h3 : p1.2.2.val = p2.2.2.val := by rw [← hidx_d p1, h, hidx_d p2]
    ext
    · exact h1
    · exact h2
    · exact h3
  have hr_idx : ∀ a b d, r (idx (a, b, d)) = c a b d := by
    intro a b d
    simp only [r, hidx_a, hidx_b, hidx_d, Nat.le_of_lt_succ a.isLt, Nat.le_of_lt_succ b.isLt,
      Nat.le_of_lt_succ d.isLt, ↓reduceDIte]
  have hr_out : ∀ k : Fin (D * D * D), k ∉ Finset.univ.image idx → r k = 0 := by
    intro k hk
    by_contra hne
    simp only [r] at hne
    split_ifs at hne with ha hb hd
    · apply hk
      rw [Finset.mem_image]
      refine ⟨(⟨k.val % D, Nat.lt_succ_of_le ha⟩, ⟨(k.val / D) % D, Nat.lt_succ_of_le hb⟩,
               ⟨k.val / (D * D), Nat.lt_succ_of_le hd⟩), Finset.mem_univ _, ?_⟩
      ext
      simp only [idx]
      have h1 := Nat.div_add_mod k.val D
      have h2 := Nat.div_add_mod (k.val / D) D
      have h3 : k.val / (D * D) = (k.val / D) / D := by rw [Nat.div_div_eq_div_mul]
      rw [h3]
      nlinarith
    · exact absurd rfl hne
    · exact absurd rfl hne
    · exact absurd rfl hne
  have hsum_r : (∑ k : Fin (D * D * D), (r k : ℝ) * ((2 ^ w : ℕ) : ℝ) ^ (k : ℕ)) = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image idx))]
    · rw [Finset.sum_image (fun p1 _ p2 _ h => hidx_inj h)]
      have hprod : ∑ p : Fin (da + 1) × Fin (db + 1) × Fin (dc + 1),
            (r (idx p) : ℝ) * ((2 ^ w : ℕ) : ℝ) ^ ((idx p) : ℕ) =
          ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1),
            (c a b d : ℝ) * ((2 : ℝ) ^ w) ^ (a : ℕ) * ((2 : ℝ) ^ (w * D)) ^ (b : ℕ) *
              ((2 : ℝ) ^ (w * D * D)) ^ (d : ℕ) := by
        simp_rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
        rw [hr_idx]
        simp only [idx, Nat.cast_pow, Nat.cast_ofNat]
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
        simp only [mul_assoc, ← pow_add]
        congr 2; ring
      rw [hprod, ← hfev]
      exact hzero
    · intro k _ hk; simp [hr_out k hk]
  have hl1_r : (∑ k : Fin (D * D * D), (r k).natAbs) < 2 ^ w := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image idx))]
    · rw [Finset.sum_image (fun p1 _ p2 _ h => hidx_inj h)]
      have hprod : ∑ p : Fin (da + 1) × Fin (db + 1) × Fin (dc + 1), (r (idx p)).natAbs =
          ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c a b d).natAbs := by
        simp_rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
        rw [hr_idx]
      rw [hprod]
      exact lt_of_le_of_lt hcl1 hL
    · intro k _ hk; simp [hr_out k hk]
  have hB2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hall0 := base_eval_eq_zero_imp hB2 r hsum_r hl1_r
  intro u v t
  rw [hfev]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
  have hc0 : c a b d = 0 := by rw [← hr_idx a b d]; exact hall0 (idx (a, b, d))
  simp [hc0]

/-! ## Section 3: `HasPolyRep3` Closure Lemmas -/

private lemma natAbs_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℤ) :
    (∑ i ∈ s, F i).natAbs ≤ ∑ i ∈ s, (F i).natAbs := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

private lemma sum_conv_collapse (n1 n2 : ℕ) (F : Fin (n1 + 1) → Fin (n2 + 1) → ℝ) :
    ∑ s : Fin (n1 + n2 + 1), ∑ i1 : Fin (n1 + 1), ∑ i2 : Fin (n2 + 1),
        (if i1.val + i2.val = s.val then F i1 i2 else 0) =
    ∑ i1 : Fin (n1 + 1), ∑ i2 : Fin (n2 + 1), F i1 i2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i2 _ => ?_
  have hlt : i1.val + i2.val < n1 + n2 + 1 := by omega
  rw [Finset.sum_eq_single ⟨i1.val + i2.val, hlt⟩]
  · simp
  · intro s _ hne; simp [Fin.ext_iff] at hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma HasPolyRep3.widen {da db dc da' db' dc' L L' : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (h : HasPolyRep3 da db dc L f) (ha : da ≤ da') (hb : db ≤ db') (hc : dc ≤ dc') (hL : L ≤ L') :
    HasPolyRep3 da' db' dc' L' f := by
  obtain ⟨c, hfev, hcl1⟩ := h
  let c' : Fin (da' + 1) → Fin (db' + 1) → Fin (dc' + 1) → ℤ := fun a b d =>
    if ha1 : a.val ≤ da then if hb1 : b.val ≤ db then if hc1 : d.val ≤ dc then
      c ⟨a.val, Nat.lt_succ_of_le ha1⟩ ⟨b.val, Nat.lt_succ_of_le hb1⟩ ⟨d.val, Nat.lt_succ_of_le hc1⟩
    else 0 else 0 else 0
  have hsum_eq : ∀ (G : ℕ → ℕ → ℕ → ℤ → ℝ), (∀ a b d, G a b d 0 = 0) →
      ∑ a : Fin (da' + 1), ∑ b : Fin (db' + 1), ∑ d : Fin (dc' + 1), G a.val b.val d.val (c' a b d) =
      ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), G a.val b.val d.val (c a b d) := by
    intro G hG0
    have h1 : ∀ (n m : ℕ) (hnm : n ≤ m) (F : ℕ → ℝ),
        (∀ i, n < i → F i = 0) → ∑ i : Fin (m + 1), F i.val = ∑ i : Fin (n + 1), F i.val := by
      intro n m hnm F hF
      rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
      symm
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hnm)) fun i hi1 hi2 => ?_
      exact hF i (by simp only [Finset.mem_range] at hi1 hi2; omega)
    rw [h1 da da' ha (fun a => ∑ b : Fin (db' + 1), ∑ d : Fin (dc' + 1),
          G a b.val d.val (if ha1 : a ≤ da then if hb1 : b.val ≤ db then if hc1 : d.val ≤ dc then
            c ⟨a, Nat.lt_succ_of_le ha1⟩ ⟨b.val, Nat.lt_succ_of_le hb1⟩ ⟨d.val, Nat.lt_succ_of_le hc1⟩
            else 0 else 0 else 0)) (fun a ha1 => by
              refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
              simp [Nat.not_le.mpr ha1, hG0])]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha1 : a.val ≤ da := Nat.le_of_lt_succ a.isLt
    simp only [ha1, ↓reduceDIte]
    rw [h1 db db' hb (fun b => ∑ d : Fin (dc' + 1),
          G a.val b d.val (if hb1 : b ≤ db then if hc1 : d.val ≤ dc then
            c a ⟨b, Nat.lt_succ_of_le hb1⟩ ⟨d.val, Nat.lt_succ_of_le hc1⟩
            else 0 else 0)) (fun b hb1 => by
              refine Finset.sum_eq_zero fun d _ => ?_
              simp [Nat.not_le.mpr hb1, hG0])]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb1 : b.val ≤ db := Nat.le_of_lt_succ b.isLt
    simp only [hb1, ↓reduceDIte]
    rw [h1 dc dc' hc (fun d => G a.val b.val d (if hc1 : d ≤ dc then c a b ⟨d, Nat.lt_succ_of_le hc1⟩ else 0))
      (fun d hc1 => by simp [Nat.not_le.mpr hc1, hG0])]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [Nat.le_of_lt_succ d.isLt]
  refine ⟨c', fun u v t => ?_, ?_⟩
  · rw [hfev]
    exact (hsum_eq (fun a b d v' => (v' : ℝ) * u ^ a * v ^ b * t ^ d) (fun _ _ _ => by simp)).symm
  · have hnat : ((∑ a : Fin (da' + 1), ∑ b : Fin (db' + 1), ∑ d : Fin (dc' + 1), (c' a b d).natAbs : ℕ) : ℝ) =
        ((∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c a b d).natAbs : ℕ) : ℝ) := by
      push_cast
      exact hsum_eq (fun _ _ _ v' => (v'.natAbs : ℝ)) (fun _ _ _ => by simp)
    have hnat' : (∑ a : Fin (da' + 1), ∑ b : Fin (db' + 1), ∑ d : Fin (dc' + 1), (c' a b d).natAbs) =
        ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c a b d).natAbs := by
      exact_mod_cast hnat
    omega

lemma HasPolyRep3.zero (da db dc : ℕ) : HasPolyRep3 da db dc 0 (fun _ _ _ => 0) :=
  ⟨fun _ _ _ => 0, fun _ _ _ => by simp, by simp⟩

lemma HasPolyRep3.const (k : ℤ) : HasPolyRep3 0 0 0 k.natAbs (fun _ _ _ => (k : ℝ)) :=
  ⟨fun _ _ _ => k, fun _ _ _ => by simp, by simp⟩

lemma HasPolyRep3.add {da db dc L1 L2 : ℕ} {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L1 f) (hg : HasPolyRep3 da db dc L2 g) :
    HasPolyRep3 da db dc (L1 + L2) (fun u v t => f u v t + g u v t) := by
  obtain ⟨c1, hf1, hl1⟩ := hf
  obtain ⟨c2, hg1, hl2⟩ := hg
  refine ⟨fun a b d => c1 a b d + c2 a b d, fun u v t => ?_, ?_⟩
  · dsimp only
    rw [hf1, hg1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast; ring
  · dsimp only
    have htri : ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c1 a b d + c2 a b d).natAbs ≤
        (∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c1 a b d).natAbs) +
        (∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c2 a b d).natAbs) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun d _ => Int.natAbs_add_le _ _
    omega

lemma HasPolyRep3.neg {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) : HasPolyRep3 da db dc L (fun u v t => -f u v t) := by
  obtain ⟨c, hfev, hcl1⟩ := hf
  refine ⟨fun a b d => -c a b d, fun u v t => ?_, ?_⟩
  · dsimp only
    rw [hfev, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => by push_cast; ring
  · simpa [Int.natAbs_neg] using hcl1

lemma HasPolyRep3.sub {da db dc L1 L2 : ℕ} {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L1 f) (hg : HasPolyRep3 da db dc L2 g) :
    HasPolyRep3 da db dc (L1 + L2) (fun u v t => f u v t - g u v t) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma HasPolyRep3.smul_int (k : ℤ) {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) :
    HasPolyRep3 da db dc (k.natAbs * L) (fun u v t => (k : ℝ) * f u v t) := by
  obtain ⟨c, hfev, hcl1⟩ := hf
  refine ⟨fun a b d => k * c a b d, fun u v t => ?_, ?_⟩
  · dsimp only
    rw [hfev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by push_cast; ring
  · dsimp only
    simp_rw [Int.natAbs_mul, ← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ hcl1

lemma HasPolyRep3.mul {da1 db1 dc1 L1 da2 db2 dc2 L2 : ℕ} {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da1 db1 dc1 L1 f) (hg : HasPolyRep3 da2 db2 dc2 L2 g) :
    HasPolyRep3 (da1 + da2) (db1 + db2) (dc1 + dc2) (L1 * L2) (fun u v t => f u v t * g u v t) := by
  obtain ⟨c1, hf1, hl1⟩ := hf
  obtain ⟨c2, hg1, hl2⟩ := hg
  let c : Fin (da1 + da2 + 1) → Fin (db1 + db2 + 1) → Fin (dc1 + dc2 + 1) → ℤ := fun a b d =>
    ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
      ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
        ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1), if d1.val + d2.val = d.val then
          c1 a1 b1 d1 * c2 a2 b2 d2
        else 0
      else 0
    else 0
  refine ⟨c, fun u v t => ?_, ?_⟩
  · dsimp only
    rw [hf1, hg1]
    simp only [c, Int.cast_sum, Int.cast_ite, Int.cast_zero, Int.cast_mul]
    have hpull : ∀ (a : Fin (da1 + da2 + 1)) (b : Fin (db1 + db2 + 1)) (d : Fin (dc1 + dc2 + 1)),
        (∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
          ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
            ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1), if d1.val + d2.val = d.val then
              (c1 a1 b1 d1 : ℝ) * (c2 a2 b2 d2 : ℝ) else 0 else 0 else 0) *
          u ^ (a : ℕ) * v ^ (b : ℕ) * t ^ (d : ℕ) =
        ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
          ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
            ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1), if d1.val + d2.val = d.val then
              ((c1 a1 b1 d1 : ℝ) * u ^ (a1 : ℕ) * v ^ (b1 : ℕ) * t ^ (d1 : ℕ)) *
              ((c2 a2 b2 d2 : ℝ) * u ^ (a2 : ℕ) * v ^ (b2 : ℕ) * t ^ (d2 : ℕ))
            else 0 else 0 else 0 := by
      intro a b d
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun a2 _ => ?_
      split_ifs with ha
      · refine Finset.sum_congr rfl fun b1 _ => Finset.sum_congr rfl fun b2 _ => ?_
        split_ifs with hb
        · refine Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => ?_
          split_ifs with hd
          · rw [← ha, ← hb, ← hd, pow_add, pow_add, pow_add]; ring
          · rfl
        · rfl
      · rfl
    simp_rw [hpull]
    have hstep1 : ∀ (a : Fin (da1 + da2 + 1)) (b : Fin (db1 + db2 + 1)),
        (∑ d : Fin (dc1 + dc2 + 1),
          ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
            ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
              ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1), if d1.val + d2.val = d.val then
                ((c1 a1 b1 d1 : ℝ) * u ^ (a1 : ℕ) * v ^ (b1 : ℕ) * t ^ (d1 : ℕ)) *
                ((c2 a2 b2 d2 : ℝ) * u ^ (a2 : ℕ) * v ^ (b2 : ℕ) * t ^ (d2 : ℕ))
              else 0 else 0 else 0) =
        ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
          ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
            ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1),
              ((c1 a1 b1 d1 : ℝ) * u ^ (a1 : ℕ) * v ^ (b1 : ℕ) * t ^ (d1 : ℕ)) *
              ((c2 a2 b2 d2 : ℝ) * u ^ (a2 : ℕ) * v ^ (b2 : ℕ) * t ^ (d2 : ℕ))
          else 0 else 0 := by
      intro a b
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a1 _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a2 _ => ?_
      by_cases ha : a1.val + a2.val = a.val
      · simp only [ha, ↓reduceIte]
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b1 _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b2 _ => ?_
        by_cases hb : b1.val + b2.val = b.val
        · simp only [hb, ↓reduceIte]; exact sum_conv_collapse dc1 dc2 _
        · simp [hb]
      · simp [ha]
    simp_rw [hstep1]
    have hstep2 : ∀ (a : Fin (da1 + da2 + 1)),
        (∑ b : Fin (db1 + db2 + 1),
          ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
            ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
              ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1),
                ((c1 a1 b1 d1 : ℝ) * u ^ (a1 : ℕ) * v ^ (b1 : ℕ) * t ^ (d1 : ℕ)) *
                ((c2 a2 b2 d2 : ℝ) * u ^ (a2 : ℕ) * v ^ (b2 : ℕ) * t ^ (d2 : ℕ))
            else 0 else 0) =
        ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
          ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1),
            ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1),
              ((c1 a1 b1 d1 : ℝ) * u ^ (a1 : ℕ) * v ^ (b1 : ℕ) * t ^ (d1 : ℕ)) *
              ((c2 a2 b2 d2 : ℝ) * u ^ (a2 : ℕ) * v ^ (b2 : ℕ) * t ^ (d2 : ℕ))
        else 0 := by
      intro a
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a1 _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a2 _ => ?_
      by_cases ha : a1.val + a2.val = a.val
      · simp only [ha, ↓reduceIte]; exact sum_conv_collapse db1 db2 _
      · simp [ha]
    simp_rw [hstep2, sum_conv_collapse da1 da2]
    simp_rw [← Finset.sum_mul_sum]
  · have hle : ∑ a : Fin (da1 + da2 + 1), ∑ b : Fin (db1 + db2 + 1), ∑ d : Fin (dc1 + dc2 + 1), (c a b d).natAbs ≤
        (∑ a1 : Fin (da1 + 1), ∑ b1 : Fin (db1 + 1), ∑ d1 : Fin (dc1 + 1), (c1 a1 b1 d1).natAbs) *
        (∑ a2 : Fin (da2 + 1), ∑ b2 : Fin (db2 + 1), ∑ d2 : Fin (dc2 + 1), (c2 a2 b2 d2).natAbs) := by
      have hterm : ∀ a b d, (c a b d).natAbs ≤
          ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
            ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
              ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1), if d1.val + d2.val = d.val then
                (c1 a1 b1 d1).natAbs * (c2 a2 b2 d2).natAbs
              else 0 else 0 else 0 := by
        intro a b d
        dsimp only [c]
        refine le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun a1 _ => le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun a2 _ => ?_))
        split_ifs
        · refine le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun b1 _ => le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun b2 _ => ?_))
          split_ifs
          · refine le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun d1 _ => le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun d2 _ => ?_))
            split_ifs
            · exact le_of_eq (Int.natAbs_mul _ _)
            · simp
          · simp
        · simp
      have hcast_le : ((∑ a : Fin (da1 + da2 + 1), ∑ b : Fin (db1 + db2 + 1), ∑ d : Fin (dc1 + dc2 + 1), (c a b d).natAbs : ℕ) : ℝ) ≤
          ((∑ a1 : Fin (da1 + 1), ∑ b1 : Fin (db1 + 1), ∑ d1 : Fin (dc1 + 1), (c1 a1 b1 d1).natAbs : ℕ) : ℝ) *
          ((∑ a2 : Fin (da2 + 1), ∑ b2 : Fin (db2 + 1), ∑ d2 : Fin (dc2 + 1), (c2 a2 b2 d2).natAbs : ℕ) : ℝ) := by
        have hstep0 : ∑ a : Fin (da1 + da2 + 1), ∑ b : Fin (db1 + db2 + 1), ∑ d : Fin (dc1 + dc2 + 1), (c a b d).natAbs ≤
            ∑ a : Fin (da1 + da2 + 1), ∑ b : Fin (db1 + db2 + 1), ∑ d : Fin (dc1 + dc2 + 1),
              ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
                ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
                  ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1), if d1.val + d2.val = d.val then
                    (c1 a1 b1 d1).natAbs * (c2 a2 b2 d2).natAbs
                  else 0 else 0 else 0 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun d _ => hterm a b d
        refine le_trans (Nat.cast_le.mpr hstep0) ?_
        push_cast
        have hR : ∀ (a : Fin (da1 + da2 + 1)) (b : Fin (db1 + db2 + 1)),
            (∑ d : Fin (dc1 + dc2 + 1),
              ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
                ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
                  ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1), if d1.val + d2.val = d.val then
                    ((c1 a1 b1 d1).natAbs : ℝ) * ((c2 a2 b2 d2).natAbs : ℝ)
                  else 0 else 0 else 0) =
            ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
              ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
                ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1),
                  ((c1 a1 b1 d1).natAbs : ℝ) * ((c2 a2 b2 d2).natAbs : ℝ)
              else 0 else 0 := by
          intro a b
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a1 _ => ?_
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a2 _ => ?_
          by_cases ha : a1.val + a2.val = a.val
          · simp only [ha, ↓reduceIte]
            rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b1 _ => ?_
            rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b2 _ => ?_
            by_cases hb : b1.val + b2.val = b.val
            · simp only [hb, ↓reduceIte]; exact sum_conv_collapse dc1 dc2 _
            · simp [hb]
          · simp [ha]
        simp_rw [hR]
        have hR2 : ∀ (a : Fin (da1 + da2 + 1)),
            (∑ b : Fin (db1 + db2 + 1),
              ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
                ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1), if b1.val + b2.val = b.val then
                  ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1),
                    ((c1 a1 b1 d1).natAbs : ℝ) * ((c2 a2 b2 d2).natAbs : ℝ)
                else 0 else 0) =
            ∑ a1 : Fin (da1 + 1), ∑ a2 : Fin (da2 + 1), if a1.val + a2.val = a.val then
              ∑ b1 : Fin (db1 + 1), ∑ b2 : Fin (db2 + 1),
                ∑ d1 : Fin (dc1 + 1), ∑ d2 : Fin (dc2 + 1),
                  ((c1 a1 b1 d1).natAbs : ℝ) * ((c2 a2 b2 d2).natAbs : ℝ)
            else 0 := by
          intro a
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a1 _ => ?_
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a2 _ => ?_
          by_cases ha : a1.val + a2.val = a.val
          · simp only [ha, ↓reduceIte]; exact sum_conv_collapse db1 db2 _
          · simp [ha]
        simp_rw [hR2, sum_conv_collapse da1 da2]
        apply le_of_eq
        simp_rw [← Finset.sum_mul_sum]
      exact_mod_cast hcast_le
    exact le_trans hle (Nat.mul_le_mul hl1 hl2)

lemma HasPolyRep3.perm_vut {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) : HasPolyRep3 db da dc L (fun u v t => f v u t) := by
  obtain ⟨c, hfev, hcl1⟩ := hf
  refine ⟨fun b a d => c a b d, fun u v t => ?_, ?_⟩
  · dsimp only; rw [hfev, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by ring
  · rw [Finset.sum_comm]; exact hcl1

lemma HasPolyRep3.perm_utv {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) : HasPolyRep3 da dc db L (fun u v t => f u t v) := by
  obtain ⟨c, hfev, hcl1⟩ := hf
  refine ⟨fun a d b => c a b d, fun u v t => ?_, ?_⟩
  · dsimp only; rw [hfev]
    refine Finset.sum_congr rfl fun a _ => ?_; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => by ring
  · refine le_trans (le_of_eq ?_) hcl1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma HasPolyRep3.perm_vtu {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) : HasPolyRep3 dc da db L (fun u v t => f v t u) :=
  hf.perm_utv.perm_vut

lemma HasPolyRep3.perm_tuv {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) : HasPolyRep3 db dc da L (fun u v t => f t u v) :=
  hf.perm_vut.perm_utv

lemma HasPolyRep3.perm_tvu {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) : HasPolyRep3 dc db da L (fun u v t => f t v u) :=
  hf.perm_vut.perm_utv.perm_vut

lemma HasPolyRep3.diag_uu1 {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) :
    HasPolyRep3 (da + db) 0 0 L (fun u _ _ => f u u 1) := by
  obtain ⟨c, hfev, hcl1⟩ := hf
  let c' : Fin (da + db + 1) → Fin 1 → Fin 1 → ℤ := fun s _ _ =>
    ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), if a.val + b.val = s.val then ∑ d : Fin (dc + 1), c a b d else 0
  have hfin01R : ∀ (g : Fin (0 + 1) → ℝ), ∑ i : Fin (0 + 1), g i = g 0 := fun g => Fin.sum_univ_one g
  have hfin01N : ∀ (g : Fin (0 + 1) → ℕ), ∑ i : Fin (0 + 1), g i = g 0 := fun g => Fin.sum_univ_one g
  refine ⟨c', fun u _ _ => ?_, ?_⟩
  · dsimp only
    rw [hfev]
    simp_rw [one_pow, mul_one]
    simp only [hfin01R, Fin.val_zero, pow_zero, mul_one]
    have hpull : ∀ s : Fin (da + db + 1),
        (∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d : ℝ) else 0) * u ^ (s : ℕ) =
        ∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d : ℝ) * u ^ (a : ℕ) * u ^ (b : ℕ) else 0 := by
      intro s
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rw [← h, pow_add]
        refine Finset.sum_congr rfl fun d _ => by ring
      · simp
    have hstep : ∑ s : Fin (da + db + 1),
          (∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
            if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d : ℝ) else 0) * u ^ (s : ℕ) =
        ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1),
          (c a b d : ℝ) * u ^ (a : ℕ) * u ^ (b : ℕ) := by
      trans (∑ s : Fin (da + db + 1), ∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
        if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d : ℝ) * u ^ (a : ℕ) * u ^ (b : ℕ) else 0)
      · exact Finset.sum_congr rfl fun s _ => hpull s
      · exact sum_conv_collapse da db _
    rw [← hstep]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [c', Int.cast_sum, Int.cast_ite, Int.cast_zero]
  · simp_rw [hfin01N]
    dsimp only [c']
    have hterm : ∀ s : Fin (da + db + 1),
        (∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), c a b d else 0).natAbs ≤
        ∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d).natAbs else 0 := by
      intro s
      refine le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun a _ => le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun b _ => ?_))
      split_ifs
      · exact natAbs_sum_le _ _
      · simp
    have hstep0 : ∑ s : Fin (da + db + 1),
        (∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), c a b d else 0).natAbs ≤
        ∑ s : Fin (da + db + 1), ∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d).natAbs else 0 :=
      Finset.sum_le_sum fun s _ => hterm s
    have hcast_eq : ((∑ s : Fin (da + db + 1), ∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d).natAbs else 0 : ℕ) : ℝ) =
        ((∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c a b d).natAbs : ℕ) : ℝ) := by
      push_cast
      exact sum_conv_collapse da db (fun a b => ∑ d : Fin (dc + 1), ((c a b d).natAbs : ℝ))
    have hnat_eq : (∑ s : Fin (da + db + 1), ∑ a : Fin (da + 1), ∑ b : Fin (db + 1),
          if a.val + b.val = s.val then ∑ d : Fin (dc + 1), (c a b d).natAbs else 0) =
        ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c a b d).natAbs := by
      exact_mod_cast hcast_eq
    omega

lemma HasPolyRep3.diag_1uu {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) :
    HasPolyRep3 (db + dc) 0 0 L (fun u _ _ => f 1 u u) :=
  hf.perm_tuv.diag_uu1

lemma HasPolyRep3.diag_u1u {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) :
    HasPolyRep3 (da + dc) 0 0 L (fun u _ _ => f u 1 u) :=
  hf.perm_utv.diag_uu1

lemma HasPolyRep3.of_poly3 {da db dc : ℕ} (p : Poly3)
    (hdeg : p.all (fun x => decide (x.2.1 ≤ da ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ dc)) = true) :
    HasPolyRep3 da db dc (l1Poly3 p) (ev3 p) := by
  unfold l1Poly3
  induction p with
  | nil => exact (HasPolyRep3.zero da db dc).congr fun _ _ _ => by simp [ev3]
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hdeg
    obtain ⟨⟨ha, hb, hc⟩, hxs⟩ := hdeg
    have hterm : HasPolyRep3 da db dc x.1.natAbs
        (fun u v t => (x.1 : ℝ) * u ^ x.2.1 * v ^ x.2.2.1 * t ^ x.2.2.2) := by
      refine ⟨fun a b d => if a.val = x.2.1 ∧ b.val = x.2.2.1 ∧ d.val = x.2.2.2 then x.1 else 0,
        fun u v t => ?_, ?_⟩
      · rw [Finset.sum_eq_single ⟨x.2.1, Nat.lt_succ_of_le ha⟩]
        · rw [Finset.sum_eq_single ⟨x.2.2.1, Nat.lt_succ_of_le hb⟩]
          · rw [Finset.sum_eq_single ⟨x.2.2.2, Nat.lt_succ_of_le hc⟩]
            · simp
            · intro d _ hd; simp [Fin.ext_iff] at hd; simp [hd]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro b _ hb'; refine Finset.sum_eq_zero fun d _ => ?_
            simp [Fin.ext_iff] at hb'; simp [hb']
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro a _ ha'; refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
          simp [Fin.ext_iff] at ha'; simp [ha']
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_single ⟨x.2.1, Nat.lt_succ_of_le ha⟩]
        · rw [Finset.sum_eq_single ⟨x.2.2.1, Nat.lt_succ_of_le hb⟩]
          · rw [Finset.sum_eq_single ⟨x.2.2.2, Nat.lt_succ_of_le hc⟩]
            · simp
            · intro d _ hd; simp [Fin.ext_iff] at hd; simp [hd]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro b _ hb'; refine Finset.sum_eq_zero fun d _ => ?_
            simp [Fin.ext_iff] at hb'; simp [hb']
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro a _ ha'; refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
          simp [Fin.ext_iff] at ha'; simp [ha']
        · intro h; exact absurd (Finset.mem_univ _) h
    simp only [List.foldl_cons, zero_add]
    rw [foldl_add_shift (fun y : ℤ × ℕ × ℕ × ℕ => y.1.natAbs) xs x.1.natAbs]
    exact (hterm.add (ih hxs)).congr fun u v t => by simp [ev3]

lemma HasPolyRep3.of_peval_u (p : List ℤ) :
    HasPolyRep3 p.length 0 0 (l1List p) (fun u _ _ => peval p u) := by
  unfold l1List
  induction p with
  | nil => exact (HasPolyRep3.zero 0 0 0).congr fun _ _ _ => by simp [peval]
  | cons a as ih =>
    simp only [List.length_cons, List.foldl_cons, zero_add]
    rw [foldl_add_shift Int.natAbs as a.natAbs]
    have hu : HasPolyRep3 1 0 0 1 (fun u _ _ => u) := by
      have h1 : HasPolyRep3 1 0 0 (l1Poly3 [(1, 1, 0, 0)]) (ev3 [(1, 1, 0, 0)]) :=
        HasPolyRep3.of_poly3 [(1, 1, 0, 0)] (by decide)
      exact h1.congr fun u _ _ => by simp [ev3]
    have hmul := (hu.mul ih).widen (by omega : 1 + as.length ≤ as.length + 1) (le_refl 0) (le_refl 0)
      (le_of_eq (one_mul _))
    have hconst := (HasPolyRep3.const a).widen (Nat.zero_le (as.length + 1)) (le_refl 0) (le_refl 0) (le_refl _)
    exact (hconst.add hmul).congr fun u _ _ => by simp [peval]

lemma HasPolyRep3.of_peval_v (p : List ℤ) :
    HasPolyRep3 0 p.length 0 (l1List p) (fun _ v _ => peval p v) :=
  (HasPolyRep3.of_peval_u p).perm_vut

lemma HasPolyRep3.of_peval_t (p : List ℤ) :
    HasPolyRep3 0 0 p.length (l1List p) (fun _ _ t => peval p t) :=
  (HasPolyRep3.of_peval_u p).perm_tuv

/-! ## Section 4: Zero-Δ Cholesky 3D SOS Blocks (Plain & `S₃` Standard Irrep) -/

/-- A plain zero-Δ Cholesky SOS block `mult * mp(u,v,t) * ∑_q (∑_i col[i] * basis[i](u,v,t))²`. -/
structure CholPlainBlk where
  mult : ℕ
  mp : Poly3
  basis : Array Poly3
  cols : Array (List (ℕ × ℤ))

def linEv (basis : Array Poly3) (col : List (ℕ × ℤ)) (u v t : ℝ) : ℝ :=
  (col.map fun x => (x.2 : ℝ) * ev3 (basis.getD x.1 []) u v t).sum

def cholPlainEv (blk : CholPlainBlk) (u v t : ℝ) : ℝ :=
  (blk.mult : ℝ) * ev3 blk.mp u v t *
    (blk.cols.toList.map fun col => linEv blk.basis col u v t ^ 2).sum

lemma cholPlainEv_nonneg (blk : CholPlainBlk) {u v t : ℝ} (hmp : 0 ≤ ev3 blk.mp u v t) :
    0 ≤ cholPlainEv blk u v t := by
  unfold cholPlainEv
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hmp) ?_
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨col, _, rfl⟩ := hx
  exact sq_nonneg _

def cholPlainKev (w D : ℕ) (blk : CholPlainBlk) : ℤ :=
  let bvals := blk.basis.map (kev3 w D)
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2 * bvals.getD x.1 0) 0
    acc + s * s) 0
  (blk.mult : ℤ) * kev3 w D blk.mp * sumSq

def cholPlainKevShift (eu ev et : ℕ) (blk : CholPlainBlk) : ℤ :=
  let bvals := blk.basis.map (kev3Shift eu ev et)
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2 * bvals.getD x.1 0) 0
    acc + s * s) 0
  (blk.mult : ℤ) * kev3Shift eu ev et blk.mp * sumSq

/-- An `S₃` standard-irrep zero-Δ Cholesky SOS block:
`mp(u,v,t) * ∑_q ((∑_i col[i] * e1[i])² + 3 * (∑_i col[i] * e2[i])²)`. -/
structure CholStdBlk where
  mp : Poly3
  e1 : Array Poly3
  e2 : Array Poly3
  cols : Array (List (ℕ × ℤ))

def cholStdEv (blk : CholStdBlk) (u v t : ℝ) : ℝ :=
  ev3 blk.mp u v t *
    (blk.cols.toList.map fun col =>
      linEv blk.e1 col u v t ^ 2 + 3 * linEv blk.e2 col u v t ^ 2).sum

lemma cholStdEv_nonneg (blk : CholStdBlk) {u v t : ℝ} (hmp : 0 ≤ ev3 blk.mp u v t) :
    0 ≤ cholStdEv blk u v t := by
  unfold cholStdEv
  refine mul_nonneg hmp ?_
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨col, _, rfl⟩ := hx
  positivity

def cholStdKev (w D : ℕ) (blk : CholStdBlk) : ℤ :=
  let v1 := blk.e1.map (kev3 w D)
  let v2 := blk.e2.map (kev3 w D)
  let sumSq := blk.cols.foldl (fun acc col =>
    let s1 := col.foldl (fun a x => a + x.2 * v1.getD x.1 0) 0
    let s2 := col.foldl (fun a x => a + x.2 * v2.getD x.1 0) 0
    acc + s1 * s1 + 3 * (s2 * s2)) 0
  kev3 w D blk.mp * sumSq

lemma cast_linKev (w D : ℕ) (basis : Array Poly3) (col : List (ℕ × ℤ)) :
    ((col.foldl (fun a x => a + x.2 * (basis.map (kev3 w D)).getD x.1 0) 0 : ℤ) : ℝ) =
      linEv basis col ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
  have haux : ∀ (l : List (ℕ × ℤ)) (acc : ℤ),
      ((l.foldl (fun a x => a + x.2 * (basis.map (kev3 w D)).getD x.1 0) acc : ℤ) : ℝ) =
        (acc : ℝ) + linEv basis l ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
    intro l
    induction l with
    | nil => intro acc; simp [linEv]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, linEv, List.map_cons, List.sum_cons, ih]
      push_cast
      have hget : (((basis.map (kev3 w D)).getD x.1 0 : ℤ) : ℝ) =
          ev3 (basis.getD x.1 []) ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
        by_cases h : x.1 < basis.size
        · have h1 : x.1 < (basis.map (kev3 w D)).size := by simpa using h
          simp only [Array.getD, h, h1, ↓reduceDIte]
          change (((basis.map (kev3 w D))[x.1]'h1 : ℤ) : ℝ) =
            ev3 (basis[x.1]'h) ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D))
          rw [Array.getElem_map, cast_kev3]
        · have h1 : ¬ x.1 < (basis.map (kev3 w D)).size := by simpa using h
          simp only [Array.getD, h, h1, ↓reduceDIte, ev3, List.map_nil, List.sum_nil, Int.cast_zero]
      rw [hget]; ring
  rw [haux]; simp

lemma cast_linKevShift (eu ev et : ℕ) (basis : Array Poly3) (col : List (ℕ × ℤ)) :
    ((col.foldl (fun a x => a + x.2 * (basis.map (kev3Shift eu ev et)).getD x.1 0) 0 : ℤ) : ℝ) =
      linEv basis col ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
  have haux : ∀ (l : List (ℕ × ℤ)) (acc : ℤ),
      ((l.foldl (fun a x => a + x.2 * (basis.map (kev3Shift eu ev et)).getD x.1 0) acc : ℤ) : ℝ) =
        (acc : ℝ) + linEv basis l ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
    intro l
    induction l with
    | nil => intro acc; simp [linEv]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, linEv, List.map_cons, List.sum_cons, ih]
      push_cast
      have hget : (((basis.map (kev3Shift eu ev et)).getD x.1 0 : ℤ) : ℝ) =
          ev3 (basis.getD x.1 []) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
        by_cases h : x.1 < basis.size
        · have h1 : x.1 < (basis.map (kev3Shift eu ev et)).size := by simpa using h
          simp only [Array.getD, h, h1, ↓reduceDIte]
          change (((basis.map (kev3Shift eu ev et))[x.1]'h1 : ℤ) : ℝ) =
            ev3 (basis[x.1]'h) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et)
          rw [Array.getElem_map, cast_kev3Shift]
        · have h1 : ¬ x.1 < (basis.map (kev3Shift eu ev et)).size := by simpa using h
          simp only [Array.getD, h, h1, ↓reduceDIte, ev3, List.map_nil, List.sum_nil, Int.cast_zero]
      rw [hget]; ring
  rw [haux]; simp

lemma cast_cholPlainKevShift (eu ev et : ℕ) (blk : CholPlainBlk) :
    ((cholPlainKevShift eu ev et blk : ℤ) : ℝ) =
      cholPlainEv blk ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
  unfold cholPlainKevShift cholPlainEv
  push_cast
  rw [cast_kev3Shift]
  congr 1
  rw [← Array.foldl_toList]
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
      ((ls.foldl (fun a col =>
        let s := col.foldl (fun a' x => a' + x.2 * (blk.basis.map (kev3Shift eu ev et)).getD x.1 0) 0
        a + s * s) acc : ℤ) : ℝ) =
      (acc : ℝ) + (ls.map fun col => linEv blk.basis col ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) ^ 2).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons col cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_linKevShift]; ring
  rw [haux]; simp

lemma cast_cholPlainKev (w D : ℕ) (blk : CholPlainBlk) :
    ((cholPlainKev w D blk : ℤ) : ℝ) =
      cholPlainEv blk ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
  unfold cholPlainKev cholPlainEv
  push_cast
  rw [cast_kev3]
  congr 1
  rw [← Array.foldl_toList]
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
      ((ls.foldl (fun a col =>
        let s := col.foldl (fun a' x => a' + x.2 * (blk.basis.map (kev3 w D)).getD x.1 0) 0
        a + s * s) acc : ℤ) : ℝ) =
      (acc : ℝ) + (ls.map fun col => linEv blk.basis col ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) ^ 2).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons col cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_linKev]; ring
  rw [haux]; simp

lemma cast_cholStdKev (w D : ℕ) (blk : CholStdBlk) :
    ((cholStdKev w D blk : ℤ) : ℝ) =
      cholStdEv blk ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
  unfold cholStdKev cholStdEv
  push_cast
  rw [cast_kev3]
  congr 1
  rw [← Array.foldl_toList]
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
      ((ls.foldl (fun a col =>
        let s1 := col.foldl (fun a' x => a' + x.2 * (blk.e1.map (kev3 w D)).getD x.1 0) 0
        let s2 := col.foldl (fun a' x => a' + x.2 * (blk.e2.map (kev3 w D)).getD x.1 0) 0
        a + s1 * s1 + 3 * (s2 * s2)) acc : ℤ) : ℝ) =
      (acc : ℝ) + (ls.map fun col =>
        linEv blk.e1 col ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) ^ 2 +
        3 * linEv blk.e2 col ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) ^ 2).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons col cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_linKev, cast_linKev]; ring
  rw [haux]; simp

/-- Compute upper bound on ℓ¹ coefficient norm of a `CholPlainBlk`. -/
def cholPlainL1 (blk : CholPlainBlk) : ℕ :=
  let bl1 := blk.basis.map l1Poly3
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2.natAbs * bl1.getD x.1 0) 0
    acc + s * s) 0
  blk.mult * l1Poly3 blk.mp * sumSq

/-- Compute upper bound on ℓ¹ coefficient norm of a `CholStdBlk`. -/
def cholStdL1 (blk : CholStdBlk) : ℕ :=
  let l1_1 := blk.e1.map l1Poly3
  let l1_2 := blk.e2.map l1Poly3
  let sumSq := blk.cols.foldl (fun acc col =>
    let s1 := col.foldl (fun a x => a + x.2.natAbs * l1_1.getD x.1 0) 0
    let s2 := col.foldl (fun a x => a + x.2.natAbs * l1_2.getD x.1 0) 0
    acc + (s1 * s1 + 3 * (s2 * s2))) 0
  l1Poly3 blk.mp * sumSq

lemma HasPolyRep3.of_linEv {da db dc : ℕ} (basis : Array Poly3) (col : List (ℕ × ℤ))
    (hb : basis.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ da ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ dc))) = true) :
    HasPolyRep3 da db dc
      (col.foldl (fun a x => a + x.2.natAbs * (basis.map l1Poly3).getD x.1 0) 0)
      (linEv basis col) := by
  have hget_rep : ∀ idx : ℕ,
      HasPolyRep3 da db dc ((basis.map l1Poly3).getD idx 0) (ev3 (basis.getD idx [])) := by
    intro idx
    by_cases h : idx < basis.size
    · have h1 : idx < (basis.map l1Poly3).size := by simpa using h
      simp only [Array.getD, h, h1, ↓reduceDIte]
      change HasPolyRep3 da db dc ((basis.map l1Poly3)[idx]'h1) (ev3 (basis[idx]'h))
      rw [Array.getElem_map]
      apply HasPolyRep3.of_poly3
      have hmem : basis[idx] ∈ basis.toList := Array.getElem_mem_toList h
      exact List.all_eq_true.mp hb _ hmem
    · have h1 : ¬ idx < (basis.map l1Poly3).size := by simpa using h
      simp only [Array.getD, h, h1, ↓reduceDIte]
      exact (HasPolyRep3.zero da db dc).congr fun _ _ _ => by simp [ev3]
  induction col with
  | nil => exact (HasPolyRep3.zero da db dc).congr fun _ _ _ => by simp [linEv]
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add]
    rw [foldl_add_shift (fun y : ℕ × ℤ => y.2.natAbs * (basis.map l1Poly3).getD y.1 0) xs]
    have ht := (hget_rep x.1).smul_int x.2
    exact (ht.add ih).congr fun u v t => by simp [linEv]

lemma HasPolyRep3.of_cholPlain {dmp da db dc : ℕ} (blk : CholPlainBlk)
    (hmp : blk.mp.all (fun x => decide (x.2.1 ≤ dmp ∧ x.2.2.1 ≤ dmp ∧ x.2.2.2 ≤ dmp)) = true)
    (hb : blk.basis.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ da ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ dc))) = true) :
    HasPolyRep3 (dmp + (da + da)) (dmp + (db + db)) (dmp + (dc + dc))
      (cholPlainL1 blk) (cholPlainEv blk) := by
  unfold cholPlainL1 cholPlainEv
  have hmp_rep : HasPolyRep3 dmp dmp dmp (l1Poly3 blk.mp) (ev3 blk.mp) :=
    HasPolyRep3.of_poly3 blk.mp hmp
  have hmp_sc : HasPolyRep3 dmp dmp dmp (blk.mult * l1Poly3 blk.mp)
      (fun u v t => (blk.mult : ℝ) * ev3 blk.mp u v t) := by
    simpa [Int.natAbs_natCast] using hmp_rep.smul_int (blk.mult : ℤ)
  have hsum_rep : HasPolyRep3 (da + da) (db + db) (dc + dc)
      (blk.cols.foldl (fun acc col =>
        let s := col.foldl (fun a x => a + x.2.natAbs * (blk.basis.map l1Poly3).getD x.1 0) 0
        acc + s * s) 0)
      (fun u v t => (blk.cols.toList.map fun col => linEv blk.basis col u v t ^ 2).sum) := by
    rw [← Array.foldl_toList]
    induction blk.cols.toList with
    | nil => exact (HasPolyRep3.zero (da + da) (db + db) (dc + dc)).congr fun _ _ _ => by simp
    | cons col cs ih =>
      simp only [List.foldl_cons, zero_add]
      rw [foldl_add_shift (fun c : List (ℕ × ℤ) =>
        let s := c.foldl (fun a x => a + x.2.natAbs * (blk.basis.map l1Poly3).getD x.1 0) 0
        s * s) cs]
      have hlin := HasPolyRep3.of_linEv blk.basis col hb
      have hsq := hlin.mul hlin
      exact (hsq.add ih).congr fun u v t => by simp [sq]
  exact (hmp_sc.mul hsum_rep).congr fun u v t => by ring

lemma HasPolyRep3.of_cholStd {dmp da db dc : ℕ} (blk : CholStdBlk)
    (hmp : blk.mp.all (fun x => decide (x.2.1 ≤ dmp ∧ x.2.2.1 ≤ dmp ∧ x.2.2.2 ≤ dmp)) = true)
    (hb1 : blk.e1.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ da ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ dc))) = true)
    (hb2 : blk.e2.toList.all (fun p => p.all (fun x => decide (x.2.1 ≤ da ∧ x.2.2.1 ≤ db ∧ x.2.2.2 ≤ dc))) = true) :
    HasPolyRep3 (dmp + (da + da)) (dmp + (db + db)) (dmp + (dc + dc))
      (cholStdL1 blk) (cholStdEv blk) := by
  unfold cholStdL1 cholStdEv
  have hmp_rep : HasPolyRep3 dmp dmp dmp (l1Poly3 blk.mp) (ev3 blk.mp) :=
    HasPolyRep3.of_poly3 blk.mp hmp
  have hsum_rep : HasPolyRep3 (da + da) (db + db) (dc + dc)
      (blk.cols.foldl (fun acc col =>
        let s1 := col.foldl (fun a x => a + x.2.natAbs * (blk.e1.map l1Poly3).getD x.1 0) 0
        let s2 := col.foldl (fun a x => a + x.2.natAbs * (blk.e2.map l1Poly3).getD x.1 0) 0
        acc + (s1 * s1 + 3 * (s2 * s2))) 0)
      (fun u v t => (blk.cols.toList.map fun col =>
        linEv blk.e1 col u v t ^ 2 + 3 * linEv blk.e2 col u v t ^ 2).sum) := by
    rw [← Array.foldl_toList]
    induction blk.cols.toList with
    | nil => exact (HasPolyRep3.zero (da + da) (db + db) (dc + dc)).congr fun _ _ _ => by simp
    | cons col cs ih =>
      simp only [List.foldl_cons, zero_add]
      rw [foldl_add_shift (fun c : List (ℕ × ℤ) =>
        let s1 := c.foldl (fun a x => a + x.2.natAbs * (blk.e1.map l1Poly3).getD x.1 0) 0
        let s2 := c.foldl (fun a x => a + x.2.natAbs * (blk.e2.map l1Poly3).getD x.1 0) 0
        s1 * s1 + 3 * (s2 * s2)) cs]
      have h1 := HasPolyRep3.of_linEv blk.e1 col hb1
      have h2 := HasPolyRep3.of_linEv blk.e2 col hb2
      have hsq1 := h1.mul h1
      have hsq2 : HasPolyRep3 (da + da) (db + db) (dc + dc) _ _ := (h2.mul h2).smul_int 3
      have h3abs : (3 : ℤ).natAbs = 3 := rfl
      rw [h3abs] at hsq2
      exact ((hsq1.add hsq2).add ih).congr fun u v t => by simp [sq]
  exact hmp_rep.mul hsum_rep

/-! ## Section 5: Zero-Δ Cholesky Harmonic Blocks (`Q3 k` + Fast Bitshift Kronecker) -/

/-- Exact integer evaluation of `Q3 k` at `(U, V, T) ∈ ℤ³`. -/
def q3Z : ℕ → ℤ → ℤ → ℤ → ℤ
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | k + 2, u, v, t =>
      2 * (t - u * v) * q3Z (k + 1) u v t - (1 - u * u) * (1 - v * v) * q3Z k u v t

lemma cast_q3Z (k : ℕ) (U V T : ℤ) : ((q3Z k U V T : ℤ) : ℝ) = Q3 k (U : ℝ) (V : ℝ) (T : ℝ) := by
  have key : ∀ n, ((q3Z n U V T : ℤ) : ℝ) = Q3 n (U : ℝ) (V : ℝ) (T : ℝ) ∧
      ((q3Z (n + 1) U V T : ℤ) : ℝ) = Q3 (n + 1) (U : ℝ) (V : ℝ) (T : ℝ) := by
    intro n
    induction n with
    | zero => simp [q3Z, Q3]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [q3Z, Q3]
      push_cast
      rw [ih.1, ih.2]
      ring
  exact (key k).1

/-- ℓ¹ coefficient bound of `Q3 k(u, v, t)`. -/
def q3L1 : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | k + 2 => 4 * q3L1 (k + 1) + 4 * q3L1 k

lemma HasPolyRep3.of_Q3 (k : ℕ) : HasPolyRep3 k k k (q3L1 k) (Q3 k) := by
  have hlin : HasPolyRep3 1 1 1 4 (fun u v t => 2 * (t - u * v)) := by
    have h := HasPolyRep3.of_poly3 [(2, 0, 0, 1), (-2, 1, 1, 0)] (by decide :
      ([(2, 0, 0, 1), (-2, 1, 1, 0)] : Poly3).all (fun x => decide (x.2.1 ≤ 1 ∧ x.2.2.1 ≤ 1 ∧ x.2.2.2 ≤ 1)) = true)
    exact h.congr fun u v t => by simp [ev3]; ring
  have hquad : HasPolyRep3 2 2 0 4 (fun u v _ => (1 - u ^ 2) * (1 - v ^ 2)) := by
    have h := HasPolyRep3.of_poly3 [(1, 0, 0, 0), (-1, 2, 0, 0), (-1, 0, 2, 0), (1, 2, 2, 0)] (by decide :
      ([(1, 0, 0, 0), (-1, 2, 0, 0), (-1, 0, 2, 0), (1, 2, 2, 0)] : Poly3).all
        (fun x => decide (x.2.1 ≤ 2 ∧ x.2.2.1 ≤ 2 ∧ x.2.2.2 ≤ 0)) = true)
    exact h.congr fun u v t => by simp [ev3]; ring
  have key : ∀ n, HasPolyRep3 n n n (q3L1 n) (Q3 n) ∧ HasPolyRep3 (n + 1) (n + 1) (n + 1) (q3L1 (n + 1)) (Q3 (n + 1)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨(HasPolyRep3.const 1).congr fun _ _ _ => by simp [Q3], ?_⟩
      have h1 := HasPolyRep3.of_poly3 [(1, 0, 0, 1), (-1, 1, 1, 0)] (by decide :
        ([(1, 0, 0, 1), (-1, 1, 1, 0)] : Poly3).all (fun x => decide (x.2.1 ≤ 1 ∧ x.2.2.1 ≤ 1 ∧ x.2.2.2 ≤ 1)) = true)
      exact h1.congr fun u v t => by simp [ev3, Q3]; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have ha := (hlin.mul ih.2).widen (da' := n + 2) (db' := n + 2) (dc' := n + 2)
        (by omega) (by omega) (by omega) (le_refl _)
      have hb := (hquad.mul ih.1).widen (da' := n + 2) (db' := n + 2) (dc' := n + 2)
        (by omega) (by omega) (by omega) (le_refl _)
      exact (ha.sub hb).congr fun u v t => by simp only [Q3]
  exact (key k).1

/-- A harmonic zero-Δ Cholesky block of order `k` with `m` monomial degrees `0..m-1`.
Each column `col` is a sparse list of `(a, c)` meaning `∑ c * u^a`. -/
structure CholHarmBlk where
  k : ℕ
  m : ℕ
  cols : Array (List (ℕ × ℤ))

def harmColEv (col : List (ℕ × ℤ)) (x : ℝ) : ℝ :=
  (col.map fun p => (p.2 : ℝ) * x ^ p.1).sum

def harmBlkEv (blk : CholHarmBlk) (u v t : ℝ) : ℝ :=
  Q3 blk.k u v t * (blk.cols.toList.map fun col => harmColEv col u * harmColEv col v).sum

def harmListEv (blks : List CholHarmBlk) (u v t : ℝ) : ℝ :=
  (blks.map fun blk => harmBlkEv blk u v t).sum

lemma harmBlkEv_symm (blk : CholHarmBlk) (u v t : ℝ) :
    harmBlkEv blk u v t = harmBlkEv blk v u t := by
  unfold harmBlkEv
  rw [Q3_symm]
  congr 1
  congr 1
  exact List.map_congr_left fun col _ => mul_comm _ _

lemma harmListEv_symm (blks : List CholHarmBlk) (u v t : ℝ) :
    harmListEv blks u v t = harmListEv blks v u t := by
  unfold harmListEv
  congr 1
  exact List.map_congr_left fun blk _ => harmBlkEv_symm blk u v t

theorem sum_harmBlkEv_nonneg {n : ℕ} (blk : CholHarmBlk) (S : Finset (Fin n))
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) :
    0 ≤ ∑ i ∈ S, ∑ j : Fin n, ∑ l : Fin n,
      harmBlkEv blk ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
  unfold harmBlkEv
  have hpull : ∀ (cs : List (List (ℕ × ℤ))),
      ∑ i ∈ S, ∑ j : Fin n, ∑ l : Fin n,
        Q3 blk.k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ *
          (cs.map fun col => harmColEv col ⟪x i, x j⟫ * harmColEv col ⟪x i, x l⟫).sum =
      (cs.map fun col => ∑ i ∈ S, ∑ j : Fin n, ∑ l : Fin n,
        harmColEv col ⟪x i, x j⟫ * harmColEv col ⟪x i, x l⟫ *
          Q3 blk.k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).sum := by
    intro cs
    induction cs with
    | nil => simp
    | cons col rest ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ← ih]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hpull]
  refine List.sum_nonneg fun y hy => ?_
  simp only [List.mem_map] at hy
  obtain ⟨col, _, rfl⟩ := hy
  exact sum_Y3_sq_nonneg_finset blk.k S x hx (harmColEv col)

theorem sum_harmListEv_nonneg {n : ℕ} (blks : List CholHarmBlk) (S : Finset (Fin n))
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) :
    0 ≤ ∑ i ∈ S, ∑ j : Fin n, ∑ l : Fin n,
      harmListEv blks ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
  induction blks with
  | nil => simp [harmListEv]
  | cons blk rest ih =>
    simp only [harmListEv, List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    exact add_nonneg (sum_harmBlkEv_nonneg blk S x hx) ih

/-- Ultra-fast bitshift Kronecker evaluation of a `CholHarmBlk` at `(2^eu, 2^ev, 2^et)`.
Use `eu = 0` to evaluate at `1` (`2^0 = 1`)! -/
def harmColKevShift (e : ℕ) (col : List (ℕ × ℤ)) : ℤ :=
  col.foldl (fun acc p => acc + p.2 * ((Nat.shiftLeft 1 (e * p.1) : ℕ) : ℤ)) 0

def harmBlkKevShift (eu ev et : ℕ) (blk : CholHarmBlk) : ℤ :=
  let U : ℤ := ((Nat.shiftLeft 1 eu : ℕ) : ℤ)
  let V : ℤ := ((Nat.shiftLeft 1 ev : ℕ) : ℤ)
  let T : ℤ := ((Nat.shiftLeft 1 et : ℕ) : ℤ)
  let qk := q3Z blk.k U V T
  let sumProd := blk.cols.foldl (fun acc col =>
    acc + harmColKevShift eu col * harmColKevShift ev col) 0
  qk * sumProd

def harmListKevShift (eu ev et : ℕ) (blks : List CholHarmBlk) : ℤ :=
  blks.foldl (fun acc blk => acc + harmBlkKevShift eu ev et blk) 0

lemma cast_harmColKevShift (e : ℕ) (col : List (ℕ × ℤ)) :
    ((harmColKevShift e col : ℤ) : ℝ) = harmColEv col ((2 : ℝ) ^ e) := by
  unfold harmColKevShift
  have haux : ∀ (l : List (ℕ × ℤ)) (acc : ℤ),
      ((l.foldl (fun a p => a + p.2 * ((Nat.shiftLeft 1 (e * p.1) : ℕ) : ℤ)) acc : ℤ) : ℝ) =
        (acc : ℝ) + harmColEv l ((2 : ℝ) ^ e) := by
    intro l
    induction l with
    | nil => intro acc; simp [harmColEv]
    | cons p ps ih =>
      intro acc
      simp only [List.foldl_cons, harmColEv, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [nat_shiftLeft_one_cast_real, pow_mul]
      ring
  rw [haux]; simp

lemma cast_harmBlkKevShift (eu ev et : ℕ) (blk : CholHarmBlk) :
    ((harmBlkKevShift eu ev et blk : ℤ) : ℝ) =
      harmBlkEv blk ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
  unfold harmBlkKevShift harmBlkEv
  push_cast
  rw [cast_q3Z]
  push_cast
  rw [nat_shiftLeft_one_cast_real, nat_shiftLeft_one_cast_real, nat_shiftLeft_one_cast_real]
  congr 1
  rw [← Array.foldl_toList]
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
      ((ls.foldl (fun a col => a + harmColKevShift eu col * harmColKevShift ev col) acc : ℤ) : ℝ) =
        (acc : ℝ) + (ls.map fun col => harmColEv col ((2 : ℝ) ^ eu) * harmColEv col ((2 : ℝ) ^ ev)).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons col cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_harmColKevShift, cast_harmColKevShift]; ring
  rw [haux]; simp

lemma cast_harmListKevShift (eu ev et : ℕ) (blks : List CholHarmBlk) :
    ((harmListKevShift eu ev et blks : ℤ) : ℝ) =
      harmListEv blks ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et) := by
  unfold harmListKevShift harmListEv
  have haux : ∀ (ls : List CholHarmBlk) (acc : ℤ),
      ((ls.foldl (fun a blk => a + harmBlkKevShift eu ev et blk) acc : ℤ) : ℝ) =
        (acc : ℝ) + (ls.map fun blk => harmBlkEv blk ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et)).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons blk rest ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_harmBlkKevShift]; ring
  rw [haux]; simp

/-- ℓ¹ bound for a harmonic block and a list of harmonic blocks. -/
def harmBlkL1 (blk : CholHarmBlk) : ℕ :=
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a p => a + p.2.natAbs) 0
    acc + s * s) 0
  q3L1 blk.k * sumSq

def harmListL1 (blks : List CholHarmBlk) : ℕ :=
  blks.foldl (fun acc blk => acc + harmBlkL1 blk) 0

lemma HasPolyRep3.of_harmCol_u {d : ℕ} (col : List (ℕ × ℤ))
    (hdeg : col.all (fun p => decide (p.1 ≤ d)) = true) :
    HasPolyRep3 d 0 0 (col.foldl (fun a p => a + p.2.natAbs) 0) (fun u _ _ => harmColEv col u) := by
  induction col with
  | nil => exact (HasPolyRep3.zero d 0 0).congr fun _ _ _ => by simp [harmColEv]
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hdeg
    obtain ⟨hp, hps⟩ := hdeg
    have h1 : HasPolyRep3 d 0 0 p.2.natAbs (fun u _ _ => (p.2 : ℝ) * u ^ p.1) := by
      have h := HasPolyRep3.of_poly3 (da := d) (db := 0) (dc := 0) [(p.2, p.1, 0, 0)] (by simp [hp])
      have hl1 : l1Poly3 [(p.2, p.1, 0, 0)] = p.2.natAbs := by simp [l1Poly3]
      rw [hl1] at h
      exact h.congr fun u _ _ => by simp [ev3]
    simp only [List.foldl_cons, zero_add]
    rw [foldl_add_shift (fun q : ℕ × ℤ => q.2.natAbs) ps p.2.natAbs]
    exact (h1.add (ih hps)).congr fun u _ _ => by simp [harmColEv]

lemma HasPolyRep3.of_harmBlk {M : ℕ} (blk : CholHarmBlk)
    (hdeg : blk.cols.toList.all (fun col => col.all (fun p => decide (blk.k + p.1 ≤ M))) = true)
    (hkM : blk.k ≤ M) :
    HasPolyRep3 M M M (harmBlkL1 blk) (harmBlkEv blk) := by
  unfold harmBlkL1 harmBlkEv
  have hQ := HasPolyRep3.of_Q3 blk.k
  have hsum_gen : ∀ (cs : List (List (ℕ × ℤ))),
      cs.all (fun col => col.all (fun p => decide (blk.k + p.1 ≤ M))) = true →
      HasPolyRep3 (M - blk.k) (M - blk.k) 0
        (cs.foldl (fun acc col =>
          let s := col.foldl (fun a p => a + p.2.natAbs) 0
          acc + s * s) 0)
        (fun u v _ => (cs.map fun col => harmColEv col u * harmColEv col v).sum) := by
    intro cs
    induction cs with
    | nil => intro _; exact (HasPolyRep3.zero _ _ 0).congr fun _ _ _ => by simp
    | cons col rest ih =>
      intro hcs
      simp only [List.all_cons, Bool.and_eq_true] at hcs
      obtain ⟨hcol, hrest⟩ := hcs
      have hcol' : col.all (fun p => decide (p.1 ≤ M - blk.k)) = true := by
        rw [List.all_eq_true] at hcol ⊢
        intro p hp
        have := hcol p hp
        simp only [decide_eq_true_eq] at this ⊢
        omega
      have hu := HasPolyRep3.of_harmCol_u col hcol'
      have hv := hu.perm_vut
      have huv := (hu.mul hv).widen (da' := M - blk.k) (db' := M - blk.k) (dc' := 0)
        (by omega) (by omega) (le_refl 0) (le_refl _)
      simp only [List.foldl_cons, zero_add]
      rw [foldl_add_shift (fun c : List (ℕ × ℤ) =>
        let s := c.foldl (fun a p => a + p.2.natAbs) 0
        s * s) rest]
      exact (huv.add (ih hrest)).congr fun u v t => by simp
  have hsum : HasPolyRep3 (M - blk.k) (M - blk.k) 0
      (blk.cols.foldl (fun acc col =>
        let s := col.foldl (fun a p => a + p.2.natAbs) 0
        acc + s * s) 0)
      (fun u v _ => (blk.cols.toList.map fun col => harmColEv col u * harmColEv col v).sum) := by
    rw [← Array.foldl_toList]
    exact hsum_gen blk.cols.toList hdeg
  exact (hQ.mul hsum).widen (da' := M) (db' := M) (dc' := M) (by omega) (by omega) (by omega) (le_refl _)

lemma HasPolyRep3.of_harmList {M : ℕ} (blks : List CholHarmBlk)
    (hdeg : blks.all (fun blk => decide (blk.k ≤ M) &&
      blk.cols.toList.all (fun col => col.all (fun p => decide (blk.k + p.1 ≤ M)))) = true) :
    HasPolyRep3 M M M (harmListL1 blks) (harmListEv blks) := by
  unfold harmListL1 harmListEv
  induction blks with
  | nil => exact (HasPolyRep3.zero M M M).congr fun _ _ _ => by simp
  | cons blk rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hdeg
    obtain ⟨⟨hkM, hcols⟩, hrest⟩ := hdeg
    simp only [List.foldl_cons, zero_add]
    rw [foldl_add_shift harmBlkL1 rest (harmBlkL1 blk)]
    exact ((HasPolyRep3.of_harmBlk blk hcols hkM).add (ih hrest)).congr fun u v t => by simp

end ThomsonN9.StageB.PolyKron
