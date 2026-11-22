import ThomsonN9.StageB.PolyKron
import Mathlib.Algebra.Polynomial.Roots

/-!
# Thomson N = 9 Stage B — Fast 2D-Kronecker + `t`-Slice Polynomial Identity Engine

Eliminates the `O(D^3)` bit-width explosion and `O(N)` kernel `Array.getD` overhead of 3D
Kronecker substitution for high-degree (`d = 18`) certificates by:
1. Using a binary bit-trie (`Trie ℤ`) for `O(log N)` basis-value lookup inside Lean's kernel,
   avoiding `Array.size` and linear `List` traversal.
2. Evaluating at 2D Kronecker points `(2^w, 2^(w*D), t₀)` for `dc + 1` integer slices `t₀ ∈ s`
   (cutting integer bit-widths by `D = 19×`, i.e., `~100×` faster GMP arithmetic, and allowing
   all slices to be verified in parallel across CPU cores).
3. Reducing each slice `t₀` directly to `PolyKron.eq_zero_of_kev3_zero` (with `dc := 0`) and
   lifting from `dc + 1` distinct slices to all `t ∈ ℝ` via `Polynomial.card_roots_le_degree`.
-/

set_option maxHeartbeats 4000000

namespace ThomsonN9.StageB.PolyKronFast

open Finset ThomsonN9.StageB.PolyKron

/-! ## Section 1: Binary Bit-Trie (`Trie ℤ`) with `O(log N)` Kernel Lookup -/

inductive Trie (α : Type) where
  | empty : Trie α
  | leaf : α → Trie α
  | node : Trie α → Trie α → Trie α

def splitEO {α : Type} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: rest =>
    let p := splitEO rest
    (a :: p.1, b :: p.2)

private lemma splitEO_spec {α : Type} (l : List α) :
    (2 * (splitEO l).1.length ≤ l.length + 1 ∧ 2 * (splitEO l).2.length ≤ l.length) ∧
    (∀ k (d : α), (splitEO l).1.getD k d = l.getD (2 * k) d) ∧
    (∀ k (d : α), (splitEO l).2.getD k d = l.getD (2 * k + 1) d) := by
  match l with
  | [] =>
    refine ⟨by simp [splitEO], fun k d => by simp [splitEO], fun k d => by simp [splitEO]⟩
  | [a] =>
    refine ⟨by simp [splitEO], fun k d => ?_, fun k d => ?_⟩
    · cases k <;> simp [splitEO]
    · cases k <;> simp [splitEO]
  | a :: b :: rest =>
    have ih := splitEO_spec rest
    refine ⟨?_, ?_, ?_⟩
    · simp only [splitEO, List.length_cons]; omega
    · intro k d
      cases k with
      | zero => simp [splitEO]
      | succ k' =>
        simp only [splitEO, List.getD_cons_succ]
        have hidx : 2 * (k' + 1) = (2 * k') + 2 := by omega
        rw [hidx, List.getD_cons_succ, List.getD_cons_succ]
        exact ih.2.1 k' d
    · intro k d
      cases k with
      | zero => simp [splitEO]
      | succ k' =>
        simp only [splitEO, List.getD_cons_succ]
        have hidx : 2 * (k' + 1) = (2 * k' + 1) + 1 := by omega
        rw [hidx, List.getD_cons_succ]
        exact ih.2.2 k' d
termination_by l.length

def Trie.ofList : ℕ → List ℤ → Trie ℤ
  | _, [] => .empty
  | _, [a] => .leaf a
  | 0, _ => .empty
  | fuel + 1, l =>
    let p := splitEO l
    .node (Trie.ofList fuel p.1) (Trie.ofList fuel p.2)

def Trie.get : Trie ℤ → ℕ → ℤ
  | .empty, _ => 0
  | .leaf v, 0 => v
  | .leaf _, _ + 1 => 0
  | .node e o, n => if n % 2 == 0 then e.get (n / 2) else o.get (n / 2)

lemma Trie.get_ofList (fuel : ℕ) (l : List ℤ) (hlen : l.length ≤ 2 ^ fuel) (i : ℕ) :
    (Trie.ofList fuel l).get i = l.getD i 0 := by
  induction fuel generalizing l i with
  | zero =>
    cases l with
    | nil => simp [Trie.ofList, Trie.get]
    | cons a rest =>
      cases rest with
      | nil =>
        cases i <;> simp [Trie.ofList, Trie.get]
      | cons b _ =>
        simp at hlen
  | succ fuel ih =>
    cases l with
    | nil => simp [Trie.ofList, Trie.get]
    | cons a rest =>
      cases rest with
      | nil =>
        cases i <;> simp [Trie.ofList, Trie.get]
      | cons b rest' =>
        have hsp := splitEO_spec (a :: b :: rest')
        have hlen1 : (splitEO (a :: b :: rest')).1.length ≤ 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
          omega
        have hlen2 : (splitEO (a :: b :: rest')).2.length ≤ 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
          omega
        simp only [Trie.ofList, Trie.get]
        by_cases heven : i % 2 = 0
        · simp only [heven, beq_self_eq_true, ↓reduceIte]
          rw [ih _ hlen1, hsp.2.1]
          have : 2 * (i / 2) = i := by omega
          rw [this]
        · have hne : (i % 2 == 0) = false := beq_false_of_ne heven
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          rw [ih _ hlen2, hsp.2.2]
          have : 2 * (i / 2) + 1 = i := by omega
          rw [this]

/-! ## Section 2: Fast 2D-Kronecker-at-Fixed-`T` Evaluators (`u = 2^eu, v = 2^ev, t = T`) -/

/-- Exact integer evaluation of `Poly3` at `(2^eu, 2^ev, T)` via a single bitshift per term. -/
def kev2T (eu ev : ℕ) (T : ℤ) (p : Poly3) : ℤ :=
  p.foldl (fun acc x =>
    acc + x.1 * T ^ x.2.2.2 * ((Nat.shiftLeft 1 (eu * x.2.1 + ev * x.2.2.1) : ℕ) : ℤ)) 0

/-- Exact integer evaluation of `Poly3` at `(T, 2^eu, 2^ev)` (for the 3rd `S₂` permutation). -/
def kev2T_tuv (eu ev : ℕ) (T : ℤ) (p : Poly3) : ℤ :=
  p.foldl (fun acc x =>
    acc + x.1 * T ^ x.2.1 * ((Nat.shiftLeft 1 (eu * x.2.2.1 + ev * x.2.2.2) : ℕ) : ℤ)) 0

lemma cast_kev2T (eu ev : ℕ) (T : ℤ) (p : Poly3) :
    ((kev2T eu ev T p : ℤ) : ℝ) = ev3 p ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) := by
  unfold kev2T
  have haux : ∀ (l : Poly3) (acc : ℤ),
      ((l.foldl (fun a x => a + x.1 * T ^ x.2.2.2 * ((Nat.shiftLeft 1 (eu * x.2.1 + ev * x.2.2.1) : ℕ) : ℤ)) acc : ℤ) : ℝ) =
        (acc : ℝ) + ev3 l ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) := by
    intro l
    induction l with
    | nil => intro acc; simp [ev3]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, ev3, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [nat_shiftLeft_one_cast_real, pow_add, pow_mul, pow_mul]
      ring
  rw [haux]; simp

lemma cast_kev2T_tuv (eu ev : ℕ) (T : ℤ) (p : Poly3) :
    ((kev2T_tuv eu ev T p : ℤ) : ℝ) = ev3 p (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) := by
  unfold kev2T_tuv
  have haux : ∀ (l : Poly3) (acc : ℤ),
      ((l.foldl (fun a x => a + x.1 * T ^ x.2.1 * ((Nat.shiftLeft 1 (eu * x.2.2.1 + ev * x.2.2.2) : ℕ) : ℤ)) acc : ℤ) : ℝ) =
        (acc : ℝ) + ev3 l (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) := by
    intro l
    induction l with
    | nil => intro acc; simp [ev3]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, ev3, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [nat_shiftLeft_one_cast_real, pow_add, pow_mul, pow_mul]
      ring
  rw [haux]; simp

/-- Evaluate a list of sparse columns against a precomputed basis `Trie ℤ` (plain SOS block). -/
def evalPlainCols (tr : Trie ℤ) (cols : List (List (ℕ × ℤ))) : ℤ :=
  cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2 * tr.get x.1) 0
    acc + s * s) 0

/-- Evaluate a list of sparse columns against two precomputed basis tries (`S₃` std SOS block). -/
def evalStdCols (tr1 tr2 : Trie ℤ) (cols : List (List (ℕ × ℤ))) : ℤ :=
  cols.foldl (fun acc col =>
    let s1 := col.foldl (fun a x => a + x.2 * tr1.get x.1) 0
    let s2 := col.foldl (fun a x => a + x.2 * tr2.get x.1) 0
    acc + s1 * s1 + 3 * (s2 * s2)) 0

def cholPlainKev2T (eu ev : ℕ) (T : ℤ) (blk : CholPlainBlk) : ℤ :=
  let tr := Trie.ofList 8 (blk.basis.toList.map (kev2T eu ev T))
  (blk.mult : ℤ) * kev2T eu ev T blk.mp * evalPlainCols tr blk.cols.toList

def cholPlainKev2T_tuv (eu ev : ℕ) (T : ℤ) (blk : CholPlainBlk) : ℤ :=
  let tr := Trie.ofList 8 (blk.basis.toList.map (kev2T_tuv eu ev T))
  (blk.mult : ℤ) * kev2T_tuv eu ev T blk.mp * evalPlainCols tr blk.cols.toList

def cholStdKev2T (eu ev : ℕ) (T : ℤ) (blk : CholStdBlk) : ℤ :=
  let tr1 := Trie.ofList 8 (blk.e1.toList.map (kev2T eu ev T))
  let tr2 := Trie.ofList 8 (blk.e2.toList.map (kev2T eu ev T))
  kev2T eu ev T blk.mp * evalStdCols tr1 tr2 blk.cols.toList

private lemma cast_dot_trie (basis : Array Poly3) (fZ : Poly3 → ℤ) (U V T : ℝ)
    (hcast : ∀ p, ((fZ p : ℤ) : ℝ) = ev3 p U V T)
    (hlen : basis.size ≤ 256) (col : List (ℕ × ℤ)) :
    ((col.foldl (fun a x => a + x.2 * (Trie.ofList 8 (basis.toList.map fZ)).get x.1) 0 : ℤ) : ℝ) =
      linEv basis col U V T := by
  have hlen' : (basis.toList.map fZ).length ≤ 2 ^ 8 := by simpa using hlen
  have haux : ∀ (l : List (ℕ × ℤ)) (acc : ℤ),
      ((l.foldl (fun a x => a + x.2 * (Trie.ofList 8 (basis.toList.map fZ)).get x.1) acc : ℤ) : ℝ) =
        (acc : ℝ) + linEv basis l U V T := by
    intro l
    induction l with
    | nil => intro acc; simp [linEv]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, linEv, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [Trie.get_ofList 8 _ hlen']
      have hget : (((basis.toList.map fZ).getD x.1 0 : ℤ) : ℝ) = ev3 (basis.getD x.1 []) U V T := by
        by_cases h : x.1 < basis.size
        · have h1 : x.1 < basis.toList.length := by simpa using h
          have h2 : x.1 < (basis.toList.map fZ).length := by simpa using h
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some,
            List.getElem_map, Array.getD, h, ↓reduceDIte]
          exact hcast _
        · have h2 : ¬ x.1 < (basis.toList.map fZ).length := by simpa using h
          have hnone : (basis.toList.map fZ)[x.1]? = none := List.getElem?_eq_none (by omega)
          simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none, Int.cast_zero,
            Array.getD, h, ↓reduceDIte, ev3, List.map_nil, List.sum_nil]
      rw [hget]; ring
  rw [haux]; simp

lemma cast_cholPlainKev2T (eu ev : ℕ) (T : ℤ) (blk : CholPlainBlk) (hlen : blk.basis.size ≤ 256) :
    ((cholPlainKev2T eu ev T blk : ℤ) : ℝ) =
      cholPlainEv blk ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) := by
  unfold cholPlainKev2T cholPlainEv evalPlainCols
  push_cast
  rw [cast_kev2T]
  congr 1
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
      ((ls.foldl (fun a col =>
        let s := col.foldl (fun b x => b + x.2 * (Trie.ofList 8 (blk.basis.toList.map (kev2T eu ev T))).get x.1) 0
        a + s * s) acc : ℤ) : ℝ) =
      (acc : ℝ) + (ls.map fun col => linEv blk.basis col ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) ^ 2).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons col cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_dot_trie blk.basis (kev2T eu ev T) _ _ _ (cast_kev2T eu ev T) hlen]; ring
  rw [haux]; simp

lemma cast_cholPlainKev2T_tuv (eu ev : ℕ) (T : ℤ) (blk : CholPlainBlk) (hlen : blk.basis.size ≤ 256) :
    ((cholPlainKev2T_tuv eu ev T blk : ℤ) : ℝ) =
      cholPlainEv blk (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) := by
  unfold cholPlainKev2T_tuv cholPlainEv evalPlainCols
  push_cast
  rw [cast_kev2T_tuv]
  congr 1
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
      ((ls.foldl (fun a col =>
        let s := col.foldl (fun b x => b + x.2 * (Trie.ofList 8 (blk.basis.toList.map (kev2T_tuv eu ev T))).get x.1) 0
        a + s * s) acc : ℤ) : ℝ) =
      (acc : ℝ) + (ls.map fun col => linEv blk.basis col (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ^ 2).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons col cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_dot_trie blk.basis (kev2T_tuv eu ev T) _ _ _ (cast_kev2T_tuv eu ev T) hlen]; ring
  rw [haux]; simp

lemma cast_cholStdKev2T (eu ev : ℕ) (T : ℤ) (blk : CholStdBlk)
    (hlen1 : blk.e1.size ≤ 256) (hlen2 : blk.e2.size ≤ 256) :
    ((cholStdKev2T eu ev T blk : ℤ) : ℝ) =
      cholStdEv blk ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) := by
  unfold cholStdKev2T cholStdEv evalStdCols
  push_cast
  rw [cast_kev2T]
  congr 1
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
      ((ls.foldl (fun a col =>
        let s1 := col.foldl (fun b x => b + x.2 * (Trie.ofList 8 (blk.e1.toList.map (kev2T eu ev T))).get x.1) 0
        let s2 := col.foldl (fun b x => b + x.2 * (Trie.ofList 8 (blk.e2.toList.map (kev2T eu ev T))).get x.1) 0
        a + s1 * s1 + 3 * (s2 * s2)) acc : ℤ) : ℝ) =
      (acc : ℝ) + (ls.map fun col =>
        linEv blk.e1 col ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) ^ 2 +
        3 * linEv blk.e2 col ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) ^ 2).sum := by
    intro ls
    induction ls with
    | nil => intro acc; simp
    | cons col cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_dot_trie blk.e1 (kev2T eu ev T) _ _ _ (cast_kev2T eu ev T) hlen1,
          cast_dot_trie blk.e2 (kev2T eu ev T) _ _ _ (cast_kev2T eu ev T) hlen2]; ring
  rw [haux]; simp

/-- Exact integer harmonic evaluation at `(U, V, T) ∈ ℤ³` (using `harmColKevShift` when an argument is `2^e`). -/
def harmColEvZ (x : ℤ) (col : List (ℕ × ℤ)) : ℤ :=
  col.foldl (fun a p => a + p.2 * x ^ p.1) 0

lemma cast_harmColEvZ (x : ℤ) (col : List (ℕ × ℤ)) :
    ((harmColEvZ x col : ℤ) : ℝ) = harmColEv col (x : ℝ) := by
  unfold harmColEvZ
  have haux : ∀ (l : List (ℕ × ℤ)) (acc : ℤ),
      ((l.foldl (fun a p => a + p.2 * x ^ p.1) acc : ℤ) : ℝ) = (acc : ℝ) + harmColEv l (x : ℝ) := by
    intro l
    induction l with
    | nil => intro acc; simp [harmColEv]
    | cons p ps ih =>
      intro acc
      simp only [List.foldl_cons, harmColEv, List.map_cons, List.sum_cons, ih]
      push_cast; ring
  rw [haux]; simp

/-- Harmonic block evaluated at `(2^eu, 2^ev, T)`. -/
def harmBlkKev2T (eu ev : ℕ) (T : ℤ) (blk : CholHarmBlk) : ℤ :=
  let U : ℤ := ((Nat.shiftLeft 1 eu : ℕ) : ℤ)
  let V : ℤ := ((Nat.shiftLeft 1 ev : ℕ) : ℤ)
  q3Z blk.k U V T * blk.cols.foldl (fun acc col => acc + harmColKevShift eu col * harmColKevShift ev col) 0

def harmListKev2T (eu ev : ℕ) (T : ℤ) (blks : List CholHarmBlk) : ℤ :=
  blks.foldl (fun acc blk => acc + harmBlkKev2T eu ev T blk) 0

/-- Harmonic block evaluated at `(2^eu, T, 2^ev)`. -/
def harmBlkKev2T_utv (eu ev : ℕ) (T : ℤ) (blk : CholHarmBlk) : ℤ :=
  let U : ℤ := ((Nat.shiftLeft 1 eu : ℕ) : ℤ)
  let V : ℤ := ((Nat.shiftLeft 1 ev : ℕ) : ℤ)
  q3Z blk.k U T V * blk.cols.foldl (fun acc col => acc + harmColKevShift eu col * harmColEvZ T col) 0

def harmListKev2T_utv (eu ev : ℕ) (T : ℤ) (blks : List CholHarmBlk) : ℤ :=
  blks.foldl (fun acc blk => acc + harmBlkKev2T_utv eu ev T blk) 0

/-- Harmonic block evaluated at arbitrary integers `(U, V, T)` (used for small `g(T)`). -/
def harmBlkEvZ (U V T : ℤ) (blk : CholHarmBlk) : ℤ :=
  q3Z blk.k U V T * blk.cols.foldl (fun acc col => acc + harmColEvZ U col * harmColEvZ V col) 0

def harmListEvZ (U V T : ℤ) (blks : List CholHarmBlk) : ℤ :=
  blks.foldl (fun acc blk => acc + harmBlkEvZ U V T blk) 0

lemma cast_harmListKev2T (eu ev : ℕ) (T : ℤ) (blks : List CholHarmBlk) :
    ((harmListKev2T eu ev T blks : ℤ) : ℝ) =
      harmListEv blks ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) := by
  have hblk : ∀ blk : CholHarmBlk,
      ((harmBlkKev2T eu ev T blk : ℤ) : ℝ) = harmBlkEv blk ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) := by
    intro blk
    unfold harmBlkKev2T harmBlkEv
    push_cast
    rw [cast_q3Z]; push_cast
    rw [nat_shiftLeft_one_cast_real, nat_shiftLeft_one_cast_real]
    congr 1; rw [← Array.foldl_toList]
    have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
        ((ls.foldl (fun a col => a + harmColKevShift eu col * harmColKevShift ev col) acc : ℤ) : ℝ) =
          (acc : ℝ) + (ls.map fun col => harmColEv col ((2 : ℝ) ^ eu) * harmColEv col ((2 : ℝ) ^ ev)).sum := by
      intro ls; induction ls with
      | nil => intro acc; simp
      | cons col cs ih =>
        intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
        push_cast; rw [cast_harmColKevShift, cast_harmColKevShift]; ring
    rw [haux]; simp
  unfold harmListKev2T harmListEv
  have haux : ∀ (ls : List CholHarmBlk) (acc : ℤ),
      ((ls.foldl (fun a blk => a + harmBlkKev2T eu ev T blk) acc : ℤ) : ℝ) =
        (acc : ℝ) + (ls.map fun blk => harmBlkEv blk ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
    intro ls; induction ls with
    | nil => intro acc; simp
    | cons blk rest ih =>
      intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast; rw [hblk]; ring
  rw [haux]; simp

lemma cast_harmListKev2T_utv (eu ev : ℕ) (T : ℤ) (blks : List CholHarmBlk) :
    ((harmListKev2T_utv eu ev T blks : ℤ) : ℝ) =
      harmListEv blks ((2 : ℝ) ^ eu) (T : ℝ) ((2 : ℝ) ^ ev) := by
  have hblk : ∀ blk : CholHarmBlk,
      ((harmBlkKev2T_utv eu ev T blk : ℤ) : ℝ) = harmBlkEv blk ((2 : ℝ) ^ eu) (T : ℝ) ((2 : ℝ) ^ ev) := by
    intro blk
    unfold harmBlkKev2T_utv harmBlkEv
    push_cast
    rw [cast_q3Z]; push_cast
    rw [nat_shiftLeft_one_cast_real, nat_shiftLeft_one_cast_real]
    congr 1; rw [← Array.foldl_toList]
    have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
        ((ls.foldl (fun a col => a + harmColKevShift eu col * harmColEvZ T col) acc : ℤ) : ℝ) =
          (acc : ℝ) + (ls.map fun col => harmColEv col ((2 : ℝ) ^ eu) * harmColEv col (T : ℝ)).sum := by
      intro ls; induction ls with
      | nil => intro acc; simp
      | cons col cs ih =>
        intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
        push_cast; rw [cast_harmColKevShift, cast_harmColEvZ]; ring
    rw [haux]; simp
  unfold harmListKev2T_utv harmListEv
  have haux : ∀ (ls : List CholHarmBlk) (acc : ℤ),
      ((ls.foldl (fun a blk => a + harmBlkKev2T_utv eu ev T blk) acc : ℤ) : ℝ) =
        (acc : ℝ) + (ls.map fun blk => harmBlkEv blk ((2 : ℝ) ^ eu) (T : ℝ) ((2 : ℝ) ^ ev)).sum := by
    intro ls; induction ls with
    | nil => intro acc; simp
    | cons blk rest ih =>
      intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast; rw [hblk]; ring
  rw [haux]; simp

lemma cast_harmListEvZ (U V T : ℤ) (blks : List CholHarmBlk) :
    ((harmListEvZ U V T blks : ℤ) : ℝ) = harmListEv blks (U : ℝ) (V : ℝ) (T : ℝ) := by
  have hblk : ∀ blk : CholHarmBlk,
      ((harmBlkEvZ U V T blk : ℤ) : ℝ) = harmBlkEv blk (U : ℝ) (V : ℝ) (T : ℝ) := by
    intro blk
    unfold harmBlkEvZ harmBlkEv
    push_cast; rw [cast_q3Z]
    congr 1; rw [← Array.foldl_toList]
    have haux : ∀ (ls : List (List (ℕ × ℤ))) (acc : ℤ),
        ((ls.foldl (fun a col => a + harmColEvZ U col * harmColEvZ V col) acc : ℤ) : ℝ) =
          (acc : ℝ) + (ls.map fun col => harmColEv col (U : ℝ) * harmColEv col (V : ℝ)).sum := by
      intro ls; induction ls with
      | nil => intro acc; simp
      | cons col cs ih =>
        intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
        push_cast; rw [cast_harmColEvZ, cast_harmColEvZ]; ring
    rw [haux]; simp
  unfold harmListEvZ harmListEv
  have haux : ∀ (ls : List CholHarmBlk) (acc : ℤ),
      ((ls.foldl (fun a blk => a + harmBlkEvZ U V T blk) acc : ℤ) : ℝ) =
        (acc : ℝ) + (ls.map fun blk => harmBlkEv blk (U : ℝ) (V : ℝ) (T : ℝ)).sum := by
    intro ls; induction ls with
    | nil => intro acc; simp
    | cons blk rest ih =>
      intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast; rw [hblk]; ring
  rw [haux]; simp

/-! ## Section 3: Exact Degree Helper for `peval` and Master 2D-Kronecker + `t`-Slice Theorem -/

lemma HasPolyRep3.of_peval_u_tight (p : List ℤ) :
    HasPolyRep3 (p.length - 1) 0 0 (l1List p) (fun u _ _ => peval p u) := by
  unfold l1List
  induction p with
  | nil => exact (HasPolyRep3.zero 0 0 0).congr fun _ _ _ => by simp [peval]
  | cons a as ih =>
    cases as with
    | nil =>
      simp only [List.length_singleton, Nat.sub_self, List.foldl_cons, List.foldl_nil, zero_add]
      exact (HasPolyRep3.const a).congr fun _ _ _ => by simp [peval]
    | cons b bs =>
      have hlen : (a :: b :: bs).length - 1 = 1 + ((b :: bs).length - 1) := by simp; omega
      rw [hlen]
      rw [List.foldl_cons, zero_add, foldl_add_shift Int.natAbs (b :: bs) a.natAbs]
      have hu : HasPolyRep3 1 0 0 1 (fun u _ _ => u) := by
        have h1 : HasPolyRep3 1 0 0 (l1Poly3 [(1, 1, 0, 0)]) (ev3 [(1, 1, 0, 0)]) :=
          HasPolyRep3.of_poly3 [(1, 1, 0, 0)] (by decide)
        exact h1.congr fun u _ _ => by simp [ev3]
      have hmul := (hu.mul ih).widen (le_refl _) (le_refl 0) (le_refl 0) (le_of_eq (one_mul _))
      have hconst := (HasPolyRep3.const a).widen (da' := 1 + ((b :: bs).length - 1)) (Nat.zero_le _) (le_refl 0) (le_refl 0) (le_refl _)
      exact (hconst.add hmul).congr fun u _ _ => by simp [peval]

lemma HasPolyRep3.of_peval_v_tight (p : List ℤ) :
    HasPolyRep3 0 (p.length - 1) 0 (l1List p) (fun _ v _ => peval p v) :=
  (HasPolyRep3.of_peval_u_tight p).perm_vut

lemma HasPolyRep3.of_peval_t_tight (p : List ℤ) :
    HasPolyRep3 0 0 (p.length - 1) (l1List p) (fun _ _ t => peval p t) :=
  (HasPolyRep3.of_peval_u_tight p).perm_tuv

private lemma natAbs_sum_le' {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∑ x ∈ s, f x).natAbs ≤ ∑ x ∈ s, (f x).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

/-- Restricting a 3D polynomial representation to an integer slice `t = t₀` yields a 2D
representation (degree `0` in `t`) with `ℓ¹` bound `L * (max 1 t₀.natAbs) ^ dc`. -/
lemma HasPolyRep3.eval_t_int {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) (t₀ : ℤ) :
    HasPolyRep3 da db 0 (L * (max 1 t₀.natAbs) ^ dc) (fun u v _ => f u v (t₀ : ℝ)) := by
  obtain ⟨c, hfev, hcl1⟩ := hf
  let M : ℕ := max 1 t₀.natAbs
  have hM1 : 1 ≤ M := le_max_left 1 _
  have htM : t₀.natAbs ≤ M := le_max_right 1 _
  refine ⟨fun a b _ => ∑ d : Fin (dc + 1), c a b d * t₀ ^ (d : ℕ), fun u v _ => ?_, ?_⟩
  · dsimp only
    rw [hfev u v (t₀ : ℝ)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h01 : ∀ f : Fin (0 + 1) → ℝ, ∑ x : Fin (0 + 1), f x = f 0 := fun f => by
      simp [Finset.univ_unique]
    rw [h01]
    simp only [Fin.val_zero, pow_zero, mul_one, Int.cast_sum, Int.cast_mul, Int.cast_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => by ring
  · have h01 : ∀ f : Fin (0 + 1) → ℕ, ∑ x : Fin (0 + 1), f x = f 0 := fun f => by
      simp [Finset.univ_unique]
    simp_rw [h01]
    have hstep : ∀ a b,
        (∑ d : Fin (dc + 1), c a b d * t₀ ^ (d : ℕ)).natAbs ≤
        (∑ d : Fin (dc + 1), (c a b d).natAbs) * M ^ dc := by
      intro a b
      calc (∑ d : Fin (dc + 1), c a b d * t₀ ^ (d : ℕ)).natAbs
          ≤ ∑ d : Fin (dc + 1), (c a b d * t₀ ^ (d : ℕ)).natAbs := natAbs_sum_le' _ _
        _ = ∑ d : Fin (dc + 1), (c a b d).natAbs * t₀.natAbs ^ (d : ℕ) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Int.natAbs_mul, Int.natAbs_pow]
        _ ≤ ∑ d : Fin (dc + 1), (c a b d).natAbs * M ^ dc := by
            refine Finset.sum_le_sum fun d _ => Nat.mul_le_mul_left _ ?_
            calc t₀.natAbs ^ (d : ℕ) ≤ M ^ (d : ℕ) := Nat.pow_le_pow_left htM _
              _ ≤ M ^ dc := Nat.pow_le_pow_right hM1 (Nat.lt_succ_iff.mp d.isLt)
        _ = (∑ d : Fin (dc + 1), (c a b d).natAbs) * M ^ dc := by rw [← Finset.sum_mul]
    calc ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), (∑ d : Fin (dc + 1), c a b d * t₀ ^ (d : ℕ)).natAbs
        ≤ ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), (∑ d : Fin (dc + 1), (c a b d).natAbs) * M ^ dc :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hstep a b
      _ = (∑ a : Fin (da + 1), ∑ b : Fin (db + 1), ∑ d : Fin (dc + 1), (c a b d).natAbs) * M ^ dc := by
          simp_rw [← Finset.sum_mul]
      _ ≤ L * M ^ dc := Nat.mul_le_mul_right _ hcl1

/-- If `f` has degree `≤ dc` in `t` and vanishes identically in `(u, v)` on `dc + 1` distinct
integer slices `t₀ ∈ s`, then `f ≡ 0` on all of `ℝ³`. -/
theorem HasPolyRep3.eq_zero_of_t_slices {da db dc L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : HasPolyRep3 da db dc L f) (s : Finset ℤ) (hs : dc < s.card)
    (hslice : ∀ t₀ ∈ s, ∀ u v : ℝ, f u v (t₀ : ℝ) = 0) :
    ∀ u v t : ℝ, f u v t = 0 := by
  obtain ⟨c, hfev, _⟩ := hf
  intro u v t
  let coeff : Fin (dc + 1) → ℝ := fun d =>
    ∑ a : Fin (da + 1), ∑ b : Fin (db + 1), (c a b d : ℝ) * u ^ (a : ℕ) * v ^ (b : ℕ)
  let P : Polynomial ℝ := ∑ d : Fin (dc + 1), Polynomial.C (coeff d) * Polynomial.X ^ (d : ℕ)
  have hPeval : ∀ x : ℝ, P.eval x = f u v x := by
    intro x
    rw [hfev u v x]
    dsimp only [P, coeff]
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  have hPdeg : P.natDegree ≤ dc := by
    dsimp only [P]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le (coeff d) (d : ℕ)).trans (Nat.lt_succ_iff.mp d.isLt)
  have hPzero : P = 0 := by
    by_contra hne
    let sR : Finset ℝ := s.image (Int.cast : ℤ → ℝ)
    have hcard : sR.card = s.card := Finset.card_image_of_injective s Int.cast_injective
    have hsub : sR ⊆ P.roots.toFinset := by
      intro r hr
      simp only [sR, Finset.mem_image] at hr
      obtain ⟨t₀, ht₀, rfl⟩ := hr
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def, hPeval]
      exact hslice t₀ ht₀ u v
    have h1 : sR.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    have h2 : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
    have h3 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
    omega
  rw [← hPeval t, hPzero, Polynomial.eval_zero]

/-- **Master 2D-Kronecker + `t`-Slice Uniqueness Theorem**:
Combines `HasPolyRep3.eval_t_int`, `PolyKron.eq_zero_of_kev3_zero` (with `dc := 0`), and
`HasPolyRep3.eq_zero_of_t_slices` to prove `f ≡ 0` on all of `ℝ³` from `dc + 1` fast 2D
Kronecker evaluations. -/
theorem eq_zero_of_kev2_slices {da db dc D L : ℕ} {f : ℝ → ℝ → ℝ → ℝ}
    (hda : da < D) (hdb : db < D) (hDpos : 0 < D)
    (hf : HasPolyRep3 da db dc L f)
    (s : Finset ℤ) (hs : dc < s.card)
    (wOf : ℤ → ℕ)
    (hw_pos : ∀ t₀ ∈ s, 1 ≤ wOf t₀)
    (hL : ∀ t₀ ∈ s, L * (max 1 t₀.natAbs) ^ dc < 2 ^ (wOf t₀))
    (hzero : ∀ t₀ ∈ s, f ((2 : ℝ) ^ (wOf t₀)) ((2 : ℝ) ^ (wOf t₀ * D)) (t₀ : ℝ) = 0) :
    ∀ u v t : ℝ, f u v t = 0 := by
  refine HasPolyRep3.eq_zero_of_t_slices hf s hs fun t₀ ht₀ u v => ?_
  have hrep2 := HasPolyRep3.eval_t_int hf t₀
  exact eq_zero_of_kev3_zero (da := da) (db := db) (dc := 0) (D := D) (w := wOf t₀)
    (hw_pos t₀ ht₀) hda hdb hDpos hrep2 (hL t₀ ht₀) (hzero t₀ ht₀) u v 0

/-! ## Section 4: Zero-`Array.getD` Fast `ℓ¹` Bounds (`cholPlainL1Fast` & `cholStdL1Fast`) -/

def cholPlainL1Fast (B : ℕ) (blk : CholPlainBlk) : ℕ :=
  blk.mult * l1Poly3 blk.mp * (B * B * blk.cols.toList.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2.natAbs) 0
    acc + s * s) 0)

def cholStdL1Fast (B1 B2 : ℕ) (blk : CholStdBlk) : ℕ :=
  l1Poly3 blk.mp * ((B1 * B1 + 3 * (B2 * B2)) * blk.cols.toList.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2.natAbs) 0
    acc + s * s) 0)

private lemma col_l1_le_mul {basis : Array Poly3} {B : ℕ}
    (hB : basis.toList.all (fun p => decide (l1Poly3 p ≤ B)) = true)
    (col : List (ℕ × ℤ)) :
    col.foldl (fun a x => a + x.2.natAbs * (basis.map l1Poly3).getD x.1 0) 0 ≤
      B * col.foldl (fun a x => a + x.2.natAbs) 0 := by
  have hget : ∀ i : ℕ, (basis.map l1Poly3).getD i 0 ≤ B := by
    intro i
    by_cases h : i < basis.size
    · have h1 : i < (basis.map l1Poly3).size := by simpa using h
      simp only [Array.getD, h1, ↓reduceDIte]
      change (basis.map l1Poly3)[i]'h1 ≤ B
      rw [Array.getElem_map]
      have hmem : basis[i]'h ∈ basis.toList := Array.getElem_mem_toList h
      have hall := List.all_eq_true.mp hB (basis[i]'h) hmem
      simpa using hall
    · have h1 : ¬ i < (basis.map l1Poly3).size := by simpa using h
      simp only [Array.getD, h1, ↓reduceDIte]
      exact Nat.zero_le B
  have haux : ∀ (l : List (ℕ × ℤ)) (a1 a2 : ℕ), a1 ≤ B * a2 →
      l.foldl (fun a x => a + x.2.natAbs * (basis.map l1Poly3).getD x.1 0) a1 ≤
        B * l.foldl (fun a x => a + x.2.natAbs) a2 := by
    intro l
    induction l with
    | nil => intro a1 a2 h; exact h
    | cons x xs ih =>
      intro a1 a2 h
      simp only [List.foldl_cons]
      apply ih
      have hx := Nat.mul_le_mul_left x.2.natAbs (hget x.1)
      have hmul : B * (a2 + x.2.natAbs) = B * a2 + x.2.natAbs * B := by ring
      omega
  exact haux col 0 0 (by simp)

lemma cholPlainL1_le_fast {B : ℕ} (blk : CholPlainBlk)
    (hB : blk.basis.toList.all (fun p => decide (l1Poly3 p ≤ B)) = true) :
    cholPlainL1 blk ≤ cholPlainL1Fast B blk := by
  unfold cholPlainL1 cholPlainL1Fast
  dsimp only
  rw [← Array.foldl_toList]
  refine Nat.mul_le_mul_left _ ?_
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (a1 a2 : ℕ), a1 ≤ B * B * a2 →
      ls.foldl (fun acc col =>
        let s := col.foldl (fun a x => a + x.2.natAbs * (blk.basis.map l1Poly3).getD x.1 0) 0
        acc + s * s) a1 ≤
      B * B * ls.foldl (fun acc col =>
        let s := col.foldl (fun a x => a + x.2.natAbs) 0
        acc + s * s) a2 := by
    intro ls
    induction ls with
    | nil => intro a1 a2 h; exact h
    | cons col cs ih =>
      intro a1 a2 h
      simp only [List.foldl_cons]
      apply ih
      have hc := col_l1_le_mul hB col
      set s1 := col.foldl (fun a x => a + x.2.natAbs * (blk.basis.map l1Poly3).getD x.1 0) 0
      set s2 := col.foldl (fun a x => a + x.2.natAbs) 0
      have hsq : s1 * s1 ≤ (B * s2) * (B * s2) := Nat.mul_le_mul hc hc
      have hmul : B * B * (a2 + s2 * s2) = B * B * a2 + (B * s2) * (B * s2) := by ring
      omega
  exact haux blk.cols.toList 0 0 (by simp)

lemma cholStdL1_le_fast {B1 B2 : ℕ} (blk : CholStdBlk)
    (hB1 : blk.e1.toList.all (fun p => decide (l1Poly3 p ≤ B1)) = true)
    (hB2 : blk.e2.toList.all (fun p => decide (l1Poly3 p ≤ B2)) = true) :
    cholStdL1 blk ≤ cholStdL1Fast B1 B2 blk := by
  unfold cholStdL1 cholStdL1Fast
  dsimp only
  rw [← Array.foldl_toList]
  refine Nat.mul_le_mul_left _ ?_
  have haux : ∀ (ls : List (List (ℕ × ℤ))) (a1 a2 : ℕ), a1 ≤ (B1 * B1 + 3 * (B2 * B2)) * a2 →
      ls.foldl (fun acc col =>
        let s1 := col.foldl (fun a x => a + x.2.natAbs * (blk.e1.map l1Poly3).getD x.1 0) 0
        let s2 := col.foldl (fun a x => a + x.2.natAbs * (blk.e2.map l1Poly3).getD x.1 0) 0
        acc + (s1 * s1 + 3 * (s2 * s2))) a1 ≤
      (B1 * B1 + 3 * (B2 * B2)) * ls.foldl (fun acc col =>
        let s := col.foldl (fun a x => a + x.2.natAbs) 0
        acc + s * s) a2 := by
    intro ls
    induction ls with
    | nil => intro a1 a2 h; exact h
    | cons col cs ih =>
      intro a1 a2 h
      simp only [List.foldl_cons]
      apply ih
      have hc1 := col_l1_le_mul hB1 col
      have hc2 := col_l1_le_mul hB2 col
      set s1 := col.foldl (fun a x => a + x.2.natAbs * (blk.e1.map l1Poly3).getD x.1 0) 0
      set s2 := col.foldl (fun a x => a + x.2.natAbs * (blk.e2.map l1Poly3).getD x.1 0) 0
      set s := col.foldl (fun a x => a + x.2.natAbs) 0
      have hsq1 : s1 * s1 ≤ (B1 * s) * (B1 * s) := Nat.mul_le_mul hc1 hc1
      have hsq2 : s2 * s2 ≤ (B2 * s) * (B2 * s) := Nat.mul_le_mul hc2 hc2
      have hmul : (B1 * B1 + 3 * (B2 * B2)) * (a2 + s * s) =
          (B1 * B1 + 3 * (B2 * B2)) * a2 + ((B1 * s) * (B1 * s) + 3 * ((B2 * s) * (B2 * s))) := by ring
      omega
  exact haux blk.cols.toList 0 0 (by simp)

end ThomsonN9.StageB.PolyKronFast
