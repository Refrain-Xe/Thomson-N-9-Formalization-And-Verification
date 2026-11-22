import ThomsonN9.StageB.CapCertSosData
import ThomsonN9.StageB.CapCertSosSliceM9
import ThomsonN9.StageB.CapCertSosSliceM8
import ThomsonN9.StageB.CapCertSosSliceM7
import ThomsonN9.StageB.CapCertSosSliceM6
import ThomsonN9.StageB.CapCertSosSliceM5
import ThomsonN9.StageB.CapCertSosSliceM4
import ThomsonN9.StageB.CapCertSosSliceM3
import ThomsonN9.StageB.CapCertSosSliceM2
import ThomsonN9.StageB.CapCertSosSliceM1
import ThomsonN9.StageB.CapCertSosSlice0
import ThomsonN9.StageB.CapCertSosSlice1
import ThomsonN9.StageB.CapCertSosSlice2
import ThomsonN9.StageB.CapCertSosSlice3
import ThomsonN9.StageB.CapCertSosSlice4
import ThomsonN9.StageB.CapCertSosSlice5
import ThomsonN9.StageB.CapCertSosSlice6
import ThomsonN9.StageB.CapCertSosSlice7
import ThomsonN9.StageB.CapCertSosSlice8
import ThomsonN9.StageB.CapCertSosSlice9
import ThomsonN9.StageB.CapCertBernData
import ThomsonN9.TableB5Chain

/-!
# Thomson N = 9 Stage B — Module 4: Cap Certificate & L3 Tube Forcing (`[-9/10, 1]`, `M=10, K=10`)

Proves `cap_tube_forcing`: every 9-point unit-sphere configuration `x` with `⟪x i, x j⟫ ≥ -9/10`
for all `i ≠ j` and `coulombEnergy9 x ≤ E_ttp_hi` satisfies `TableB5Chain.TubePremise (toMat x) z (1/10000)`
for every `z ∈ [TableB5Data.zLo, TableB5Data.zHi]`.
-/

set_option maxHeartbeats 16000000

namespace ThomsonN9.StageB.CapCert

open Finset ThomsonN9.StageB ThomsonN9.StageB.PolyKron ThomsonN9.StageB.PolyKronFast
open ThomsonN9.StageB.CapCertHarmData ThomsonN9.StageB.CapCertSosData ThomsonN9.StageB.CapCertBernData
open ThomsonN9.TableB5Data ThomsonN9.TableB5Chain ThomsonN9.TableB1
open scoped RealInnerProductSpace

/-- Convert a 9-point configuration in `R3` to a `9 × 3` matrix matching `TableB5Chain`. -/
def toMat (x : Fin 9 → R3) : Matrix (Fin 9) (Fin 3) ℝ :=
  Matrix.of fun i j => x i j

lemma toMat_dot (x : Fin 9 → R3) (i j : Fin 9) :
    toMat x i ⬝ᵥ toMat x j = ⟪x i, x j⟫ := by
  rw [inner_R3_expand]
  simp [toMat, dotProduct, Fin.sum_univ_three]

lemma toMat_unit (x : Fin 9 → R3) (hu : ∀ i, ‖x i‖ = 1) (i : Fin 9) :
    toMat x i ⬝ᵥ toMat x i = 1 := by
  rw [toMat_dot, real_inner_self_eq_norm_sq, hu i]; norm_num

/-- Canonical rational upper bound matching `SlabCert.E_ttp_hi`. -/
noncomputable def E_ttp_hi : ℝ := (E_ttp_hi_num : ℝ) / (E_ttp_hi_den : ℝ)

/-! ## Section 1: Helpers for `twoYH`, `HasPolyRep3`, and Kronecker Identity -/

private lemma peval_eq_sum_zipIdx (h : List ℤ) (x : ℝ) :
    peval h x = (h.zipIdx.map fun p => (p.1 : ℝ) * x ^ p.2).sum := by
  have hgen : ∀ (l : List ℤ) (k : ℕ),
      x ^ k * peval l x = ((l.zipIdx k).map fun p => (p.1 : ℝ) * x ^ p.2).sum := by
    intro l
    induction l with
    | nil => intro k; simp [peval]
    | cons a as ih =>
      intro k
      simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, peval]
      have h1 := ih (k + 1)
      rw [pow_succ] at h1
      linarith
  simpa using hgen h 0

private lemma peval_twoYH_aux (l : List (ℤ × ℕ)) (acc : List ℤ) (y : ℝ) :
    peval (l.foldl (fun a p => padd a (pscale (2 * p.1) (pmul [0, 1] (ppow [1, 0, -2] p.2)))) acc) y =
      peval acc y + (l.map fun p => (2 : ℝ) * y * ((p.1 : ℝ) * (1 - 2 * y ^ 2) ^ p.2)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, peval_padd, peval_pscale,
      peval_pmul, peval_ppow]
    have h01 : peval [0, 1] y = y := by simp [peval]
    have h12 : peval [1, 0, -2] y = 1 - 2 * y ^ 2 := by simp [peval]; ring
    rw [h01, h12]
    push_cast
    ring

private lemma peval_twoYH (h : List ℤ) (y : ℝ) :
    peval (twoYH h) y = 2 * y * peval h (1 - 2 * y ^ 2) := by
  unfold twoYH
  rw [peval_twoYH_aux, peval_eq_sum_zipIdx h, show peval [] y = 0 from rfl, zero_add]
  have hpull : ∀ (l : List (ℤ × ℕ)),
      (l.map fun p => (2 : ℝ) * y * ((p.1 : ℝ) * (1 - 2 * y ^ 2) ^ p.2)).sum =
      2 * y * (l.map fun p => (p.1 : ℝ) * (1 - 2 * y ^ 2) ^ p.2).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  exact hpull _

private lemma HasPolyRep3.of_plain_deg18 {blk : CholPlainBlk} {dmp db B : ℕ}
    (hok : plainDegOk blk dmp db = true) (hD : dmp + (db + db) ≤ 18)
    (hB : blk.basis.toList.all (fun p => decide (l1Poly3 p ≤ B)) = true) :
    HasPolyRep3 18 18 18 (cholPlainL1Fast B blk) (cholPlainEv blk) := by
  simp only [plainDegOk, Bool.and_eq_true] at hok
  exact (HasPolyRep3.of_cholPlain blk hok.1 hok.2).widen hD hD hD (cholPlainL1_le_fast blk hB)

private lemma HasPolyRep3.of_std_deg18 {blk : CholStdBlk} {dmp db B1 B2 : ℕ}
    (hok : stdDegOk blk dmp db = true) (hD : dmp + (db + db) ≤ 18)
    (hB1 : blk.e1.toList.all (fun p => decide (l1Poly3 p ≤ B1)) = true)
    (hB2 : blk.e2.toList.all (fun p => decide (l1Poly3 p ≤ B2)) = true) :
    HasPolyRep3 18 18 18 (cholStdL1Fast B1 B2 blk) (cholStdEv blk) := by
  simp only [stdDegOk, Bool.and_eq_true] at hok
  exact (HasPolyRep3.of_cholStd blk hok.1.1 hok.1.2 hok.2).widen hD hD hD (cholStdL1_le_fast blk hB1 hB2)

private lemma harm_rep : HasPolyRep3 9 9 9 (harmListL1 harmBlks) (harmListEv harmBlks) :=
  HasPolyRep3.of_harmList harmBlks harm_deg_ok

private def g_int_ev (x : ℝ) : ℝ :=
  harmListEv harmBlks 1 x x + harmListEv harmBlks x 1 x + harmListEv harmBlks x x 1

private lemma g_rep_u : HasPolyRep3 18 18 18 (3 * harmListL1 harmBlks) (fun u _ _ => g_int_ev u) := by
  have h1 := harm_rep.diag_1uu
  have h2 := harm_rep.diag_u1u
  have h3 := harm_rep.diag_uu1
  have hsum := ((h1.add h2).add h3).widen (da' := 18) (db' := 18) (dc' := 18)
    (L' := 3 * harmListL1 harmBlks) (by omega) (by omega) (by omega) (by omega)
  exact hsum.congr (g := fun u _ _ => g_int_ev u) fun u _ _ => by unfold g_int_ev; ring

private def sosCap_ev (u v t : ℝ) : ℝ :=
  (sos_plain_s3.map fun b => cholPlainEv b u v t).sum +
  (sos_std_s3.map fun b => cholStdEv b u v t).sum +
  (sos_ulo.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum +
  (sos_uhi.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum

private lemma cast_foldl_plain2T (eu ev : ℕ) (T : ℤ) (blks : List CholPlainBlk)
    (hlen : blks.all (fun b => decide (b.basis.size ≤ 256)) = true) :
    ((blks.foldl (fun a b => a + cholPlainKev2T eu ev T b) 0 : ℤ) : ℝ) =
      (blks.map fun b => cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
  have haux : ∀ (l : List CholPlainBlk),
      l.all (fun b => decide (b.basis.size ≤ 256)) = true →
      ∀ (acc : ℤ),
      ((l.foldl (fun a b => a + cholPlainKev2T eu ev T b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b => cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons b bs ih =>
      intro hl acc
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih hl.2]
      push_cast
      rw [cast_cholPlainKev2T eu ev T b hl.1]; ring
  rw [haux blks hlen 0]; simp

private lemma cast_foldl_plain2T3 (eu ev : ℕ) (T : ℤ) (blks : List CholPlainBlk)
    (hlen : blks.all (fun b => decide (b.basis.size ≤ 256)) = true) :
    ((blks.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b
        + cholPlainKev2T_tuv eu ev T b) 0 : ℤ) : ℝ) =
      (blks.map fun b =>
        cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) +
        cholPlainEv b ((2 : ℝ) ^ ev) ((2 : ℝ) ^ eu) (T : ℝ) +
        cholPlainEv b (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev)).sum := by
  have haux : ∀ (l : List CholPlainBlk),
      l.all (fun b => decide (b.basis.size ≤ 256)) = true →
      ∀ (acc : ℤ),
      ((l.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b
          + cholPlainKev2T_tuv eu ev T b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b =>
          cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) +
          cholPlainEv b ((2 : ℝ) ^ ev) ((2 : ℝ) ^ eu) (T : ℝ) +
          cholPlainEv b (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev)).sum := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons b bs ih =>
      intro hl acc
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih hl.2]
      push_cast
      rw [cast_cholPlainKev2T eu ev T b hl.1, cast_cholPlainKev2T ev eu T b hl.1,
        cast_cholPlainKev2T_tuv eu ev T b hl.1]; ring
  rw [haux blks hlen 0]; simp

private lemma cast_foldl_std2T (eu ev : ℕ) (T : ℤ) (blks : List CholStdBlk)
    (hlen : blks.all (fun b => decide (b.e1.size ≤ 256 ∧ b.e2.size ≤ 256)) = true) :
    ((blks.foldl (fun a b => a + cholStdKev2T eu ev T b) 0 : ℤ) : ℝ) =
      (blks.map fun b => cholStdEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
  have haux : ∀ (l : List CholStdBlk),
      l.all (fun b => decide (b.e1.size ≤ 256 ∧ b.e2.size ≤ 256)) = true →
      ∀ (acc : ℤ),
      ((l.foldl (fun a b => a + cholStdKev2T eu ev T b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b => cholStdEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons b bs ih =>
      intro hl acc
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih hl.2]
      push_cast
      rw [cast_cholStdKev2T eu ev T b hl.1.1 hl.1.2]; ring
  rw [haux blks hlen 0]; simp

private lemma id_slack (u v t : ℝ) :
    120 * (peval H_int u + peval H_int v + peval H_int t)
      - 10 * (e_int : ℝ) - 45 * harmListEv harmBlks 1 1 1
      - 120 * (g_int_ev u + g_int_ev v + g_int_ev t)
      - 840 * (harmListEv harmBlks u v t + harmListEv harmBlks u t v + harmListEv harmBlks v t u) =
    sosCap_ev u v t + ev3 res_slack_int u v t := by
  let f : ℝ → ℝ → ℝ → ℝ := fun u v t =>
    (120 * (peval H_int u + peval H_int v + peval H_int t)
      - 10 * (e_int : ℝ) - 45 * harmListEv harmBlks 1 1 1
      - 120 * (g_int_ev u + g_int_ev v + g_int_ev t)
      - 840 * (harmListEv harmBlks u v t + harmListEv harmBlks u t v + harmListEv harmBlks v t u))
    - (sosCap_ev u v t + ev3 res_slack_int u v t)
  suffices h0 : f u v t = 0 by dsimp only [f] at h0; linarith
  have hd := sos_exact_deg_ok
  have hbl := basis_l1_ok
  have hH_u := (HasPolyRep3.of_peval_u_tight H_int).widen (da' := 18) (db' := 18) (dc' := 18)
    (by decide) (by omega) (by omega) (le_refl _)
  have hH3 : HasPolyRep3 18 18 18 (120 * (l1List H_int + l1List H_int + l1List H_int))
      (fun u v t => 120 * (peval H_int u + peval H_int v + peval H_int t)) := by
    have h := (hH_u.add hH_u.perm_vut).add hH_u.perm_tuv
    simpa [Int.natAbs_natCast] using h.smul_int 120
  have he : HasPolyRep3 18 18 18 (10 * e_int.natAbs) (fun _ _ _ => 10 * (e_int : ℝ)) := by
    have h := (HasPolyRep3.const (10 * e_int)).widen (da' := 18) (db' := 18) (dc' := 18)
      (by omega) (by omega) (by omega) (by rw [Int.natAbs_mul])
    exact h.congr fun _ _ _ => by push_cast; ring
  have hs111 : HasPolyRep3 18 18 18 (45 * (harmListKevShift 0 0 0 harmBlks).natAbs)
      (fun _ _ _ => 45 * harmListEv harmBlks 1 1 1) := by
    have h := (HasPolyRep3.const (45 * harmListKevShift 0 0 0 harmBlks)).widen (da' := 18) (db' := 18) (dc' := 18)
      (by omega) (by omega) (by omega) (by rw [Int.natAbs_mul])
    refine h.congr fun _ _ _ => ?_
    push_cast
    rw [cast_harmListKevShift]
    simp only [pow_zero]
  have hg3 : HasPolyRep3 18 18 18
      (120 * (3 * harmListL1 harmBlks + 3 * harmListL1 harmBlks + 3 * harmListL1 harmBlks))
      (fun u v t => 120 * (g_int_ev u + g_int_ev v + g_int_ev t)) := by
    have h := (g_rep_u.add g_rep_u.perm_vut).add g_rep_u.perm_tuv
    simpa [Int.natAbs_natCast] using h.smul_int 120
  have hs3 : HasPolyRep3 18 18 18 (840 * (3 * harmListL1 harmBlks))
      (fun u v t => 840 * (harmListEv harmBlks u v t + harmListEv harmBlks u t v + harmListEv harmBlks v t u)) := by
    have h1 := harm_rep.widen (da' := 18) (db' := 18) (dc' := 18) (by omega) (by omega) (by omega) (le_refl _)
    have h2 := h1.perm_utv
    have h3 := h1.perm_vtu
    have h123 := ((h1.add h2).add h3).widen (L' := 3 * harmListL1 harmBlks)
      (le_refl _) (le_refl _) (le_refl _) (by omega)
    simpa [Int.natAbs_natCast] using h123.smul_int 840
  have hrep_p : HasPolyRep3 18 18 18 (sos_plain_s3.foldl (fun a b => a + cholPlainL1Fast 6 b) 0)
      (fun u v t => (sos_plain_s3.map fun b => cholPlainEv b u v t).sum) := by
    have hp := hbl.1
    simp only [sos_plain_s3, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp
    have b1 := HasPolyRep3.of_plain_deg18 hd.1 (by omega) hp.1
    have b2 := HasPolyRep3.of_plain_deg18 hd.2.1 (by omega) hp.2.1
    have b3 := HasPolyRep3.of_plain_deg18 hd.2.2.1 (by omega) hp.2.2.1
    have b4 := HasPolyRep3.of_plain_deg18 hd.2.2.2.1 (by omega) hp.2.2.2
    have hall := ((b1.add b2).add b3).add b4
    refine hall.widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_plain_s3, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_plain_s3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; ring
  have hrep_std : HasPolyRep3 18 18 18 (sos_std_s3.foldl (fun a b => a + cholStdL1Fast 8 4 b) 0)
      (fun u v t => (sos_std_s3.map fun b => cholStdEv b u v t).sum) := by
    have hs := hbl.2.1
    simp only [sos_std_s3, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hs
    have b1 := HasPolyRep3.of_std_deg18 hd.2.2.2.2.1 (by omega) hs.1.1 hs.1.2
    have b2 := HasPolyRep3.of_std_deg18 hd.2.2.2.2.2.1 (by omega) hs.2.1 hs.2.2
    refine (b1.add b2).widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_std_s3, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_std_s3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hrep_ulo : HasPolyRep3 18 18 18 (3 * sos_ulo.foldl (fun a b => a + cholPlainL1Fast 2 b) 0)
      (fun u v t => (sos_ulo.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum) := by
    have hu := hbl.2.2.1
    simp only [sos_ulo, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hu
    have b1 := HasPolyRep3.of_plain_deg18 hd.2.2.2.2.2.2.1 (by omega) hu.1
    have b2 := HasPolyRep3.of_plain_deg18 hd.2.2.2.2.2.2.2.1 (by omega) hu.2
    have c1 := (b1.add b1.perm_vut).add b1.perm_tuv
    have c2 := (b2.add b2.perm_vut).add b2.perm_tuv
    refine (c1.add c2).widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_ulo, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_ulo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hrep_uhi : HasPolyRep3 18 18 18 (3 * sos_uhi.foldl (fun a b => a + cholPlainL1Fast 2 b) 0)
      (fun u v t => (sos_uhi.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum) := by
    have hu := hbl.2.2.2
    simp only [sos_uhi, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hu
    have b1 := HasPolyRep3.of_plain_deg18 hd.2.2.2.2.2.2.2.2.1 (by omega) hu.1
    have b2 := HasPolyRep3.of_plain_deg18 hd.2.2.2.2.2.2.2.2.2 (by omega) hu.2
    have c1 := (b1.add b1.perm_vut).add b1.perm_tuv
    have c2 := (b2.add b2.perm_vut).add b2.perm_tuv
    refine (c1.add c2).widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_uhi, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_uhi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hrep_res : HasPolyRep3 18 18 18 (l1Poly3 res_slack_int) (ev3 res_slack_int) :=
    HasPolyRep3.of_poly3 res_slack_int res_deg_ok
  have hrep_f : HasPolyRep3 18 18 18 l1CapFast f := by
    have hall := ((((hH3.sub he).sub hs111).sub hg3).sub hs3).sub
      ((((hrep_p.add hrep_std).add hrep_ulo).add hrep_uhi).add hrep_res)
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by unfold l1CapFast; omega) |>.congr fun a b c => ?_
    dsimp only [f, sosCap_ev]
  have hval_of_check : ∀ T : ℤ, checkKronCapAtT (wForT T) T = true →
      f ((2 : ℝ) ^ (wForT T)) ((2 : ℝ) ^ (wForT T * D2_kron)) (T : ℝ) = 0 := by
    intro T hk
    unfold checkKronCapAtT at hk
    simp only [beq_iff_eq] at hk
    set eu := wForT T
    set ev := wForT T * D2_kron
    have hcast :
      (((120 * (pevalZ H_int ((Nat.shiftLeft 1 eu : ℕ) : ℤ)
          + pevalZ H_int ((Nat.shiftLeft 1 ev : ℕ) : ℤ)
          + pevalZ H_int T)
        - 10 * e_int - 45 * harmListKevShift 0 0 0 harmBlks
        - 120 * ((harmListKevShift 0 eu eu harmBlks + harmListKevShift eu 0 eu harmBlks + harmListKevShift eu eu 0 harmBlks)
          + (harmListKevShift 0 ev ev harmBlks + harmListKevShift ev 0 ev harmBlks + harmListKevShift ev ev 0 harmBlks)
          + (harmListEvZ 1 T T harmBlks + harmListEvZ T 1 T harmBlks + harmListEvZ T T 1 harmBlks))
        - 840 * (harmListKev2T eu ev T harmBlks + harmListKev2T_utv eu ev T harmBlks + harmListKev2T_utv ev eu T harmBlks) : ℤ) : ℝ)) =
      (((sos_plain_s3.foldl (fun a b => a + cholPlainKev2T eu ev T b) 0
        + sos_std_s3.foldl (fun a b => a + cholStdKev2T eu ev T b) 0
        + sos_ulo.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b + cholPlainKev2T_tuv eu ev T b) 0
        + sos_uhi.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b + cholPlainKev2T_tuv eu ev T b) 0
        + kev2T eu ev T res_slack_int : ℤ) : ℝ)) := by
      exact_mod_cast hk
    push_cast at hcast
    rw [cast_pevalZ, cast_pevalZ, cast_pevalZ,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift,
      cast_harmListEvZ, cast_harmListEvZ, cast_harmListEvZ,
      cast_harmListKev2T, cast_harmListKev2T_utv, cast_harmListKev2T_utv,
      cast_foldl_plain2T eu ev T sos_plain_s3 basis_len_ok.1,
      cast_foldl_std2T eu ev T sos_std_s3 basis_len_ok.2.1,
      cast_foldl_plain2T3 eu ev T sos_ulo basis_len_ok.2.2.1,
      cast_foldl_plain2T3 eu ev T sos_uhi basis_len_ok.2.2.2,
      cast_kev2T] at hcast
    push_cast at hcast
    simp only [nat_shiftLeft_one_cast_real, pow_zero] at hcast
    dsimp only [f, sosCap_ev, g_int_ev, eu, ev] at hcast ⊢
    linarith
  let s : Finset ℤ := Finset.Icc (-9) 9
  have hs : 18 < s.card := by decide
  have hw_pos : ∀ t₀ ∈ s, 1 ≤ wForT t₀ := by
    intro t₀ ht₀; simp only [s, Finset.mem_Icc] at ht₀; obtain ⟨hlo, hhi⟩ := ht₀; interval_cases t₀ <;> decide
  have hL : ∀ t₀ ∈ s, l1CapFast * (max 1 t₀.natAbs) ^ 18 < 2 ^ (wForT t₀) := by
    intro t₀ ht₀
    apply l1_slices_ok t₀
    simp only [s, Finset.mem_Icc] at ht₀
    obtain ⟨hlo, hhi⟩ := ht₀
    interval_cases t₀ <;> decide
  have hzero : ∀ t₀ ∈ s, f ((2 : ℝ) ^ (wForT t₀)) ((2 : ℝ) ^ (wForT t₀ * D2_kron)) (t₀ : ℝ) = 0 := by
    intro t₀ ht₀
    apply hval_of_check t₀
    simp only [s, Finset.mem_Icc] at ht₀
    obtain ⟨hlo, hhi⟩ := ht₀
    interval_cases t₀
    · exact CapCertSosSliceM9.kron_t_m9
    · exact CapCertSosSliceM8.kron_t_m8
    · exact CapCertSosSliceM7.kron_t_m7
    · exact CapCertSosSliceM6.kron_t_m6
    · exact CapCertSosSliceM5.kron_t_m5
    · exact CapCertSosSliceM4.kron_t_m4
    · exact CapCertSosSliceM3.kron_t_m3
    · exact CapCertSosSliceM2.kron_t_m2
    · exact CapCertSosSliceM1.kron_t_m1
    · exact CapCertSosSlice0.kron_t_0
    · exact CapCertSosSlice1.kron_t_1
    · exact CapCertSosSlice2.kron_t_2
    · exact CapCertSosSlice3.kron_t_3
    · exact CapCertSosSlice4.kron_t_4
    · exact CapCertSosSlice5.kron_t_5
    · exact CapCertSosSlice6.kron_t_6
    · exact CapCertSosSlice7.kron_t_7
    · exact CapCertSosSlice8.kron_t_8
    · exact CapCertSosSlice9.kron_t_9
  exact eq_zero_of_kev2_slices (da := 18) (db := 18) (dc := 18) (D := D2_kron)
    (by decide) (by decide) (by decide) hrep_f s hs wForT hw_pos hL hzero u v t

/-! ## Section 2: SOS Nonnegativity & 1D Minorant Bounds -/

private lemma sosCap_ev_nonneg {u v t : ℝ} (hu_lo : -9 / 10 ≤ u) (hu_hi : u ≤ 1)
    (hv_lo : -9 / 10 ≤ v) (hv_hi : v ≤ 1) (ht_lo : -9 / 10 ≤ t) (ht_hi : t ≤ 1)
    (hd : 0 ≤ detG u v t) : 0 ≤ sosCap_ev u v t := by
  have h1 : 0 ≤ ev3 blk_SOS_1_triv.mp u v t := by simp [blk_SOS_1_triv, ev3]
  have h2 : 0 ≤ ev3 blk_SOS_1_sign.mp u v t := by simp [blk_SOS_1_sign, ev3]
  have h3 : 0 ≤ ev3 blk_SOS_detG_triv.mp u v t := by simp [blk_SOS_detG_triv, ev3]; push_cast; unfold detG at hd; linarith
  have h4 : 0 ≤ ev3 blk_SOS_detG_sign.mp u v t := by simp [blk_SOS_detG_sign, ev3]; push_cast; unfold detG at hd; linarith
  have h5 : 0 ≤ ev3 blk_SOS_1_std.mp u v t := by simp [blk_SOS_1_std, ev3]
  have h6 : 0 ≤ ev3 blk_SOS_detG_std.mp u v t := by simp [blk_SOS_detG_std, ev3]; push_cast; unfold detG at hd; linarith
  have h7a : 0 ≤ ev3 blk_SOS_ulo_even.mp u v t := by simp [blk_SOS_ulo_even, ev3]; push_cast; linarith
  have h7b : 0 ≤ ev3 blk_SOS_ulo_even.mp v u t := by simp [blk_SOS_ulo_even, ev3]; push_cast; linarith
  have h7c : 0 ≤ ev3 blk_SOS_ulo_even.mp t u v := by simp [blk_SOS_ulo_even, ev3]; push_cast; linarith
  have h8a : 0 ≤ ev3 blk_SOS_ulo_odd.mp u v t := by simp [blk_SOS_ulo_odd, ev3]; push_cast; linarith
  have h8b : 0 ≤ ev3 blk_SOS_ulo_odd.mp v u t := by simp [blk_SOS_ulo_odd, ev3]; push_cast; linarith
  have h8c : 0 ≤ ev3 blk_SOS_ulo_odd.mp t u v := by simp [blk_SOS_ulo_odd, ev3]; push_cast; linarith
  have h9a : 0 ≤ ev3 blk_SOS_uhi_even.mp u v t := by simp [blk_SOS_uhi_even, ev3]; push_cast; linarith
  have h9b : 0 ≤ ev3 blk_SOS_uhi_even.mp v u t := by simp [blk_SOS_uhi_even, ev3]; push_cast; linarith
  have h9c : 0 ≤ ev3 blk_SOS_uhi_even.mp t u v := by simp [blk_SOS_uhi_even, ev3]; push_cast; linarith
  have h10a : 0 ≤ ev3 blk_SOS_uhi_odd.mp u v t := by simp [blk_SOS_uhi_odd, ev3]; push_cast; linarith
  have h10b : 0 ≤ ev3 blk_SOS_uhi_odd.mp v u t := by simp [blk_SOS_uhi_odd, ev3]; push_cast; linarith
  have h10c : 0 ≤ ev3 blk_SOS_uhi_odd.mp t u v := by simp [blk_SOS_uhi_odd, ev3]; push_cast; linarith
  unfold sosCap_ev
  simp only [sos_plain_s3, sos_std_s3, sos_ulo, sos_uhi, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  linarith [cholPlainEv_nonneg blk_SOS_1_triv h1, cholPlainEv_nonneg blk_SOS_1_sign h2,
    cholPlainEv_nonneg blk_SOS_detG_triv h3, cholPlainEv_nonneg blk_SOS_detG_sign h4,
    cholStdEv_nonneg blk_SOS_1_std h5, cholStdEv_nonneg blk_SOS_detG_std h6,
    cholPlainEv_nonneg blk_SOS_ulo_even h7a, cholPlainEv_nonneg blk_SOS_ulo_even h7b,
    cholPlainEv_nonneg blk_SOS_ulo_even h7c, cholPlainEv_nonneg blk_SOS_ulo_odd h8a,
    cholPlainEv_nonneg blk_SOS_ulo_odd h8b, cholPlainEv_nonneg blk_SOS_ulo_odd h8c,
    cholPlainEv_nonneg blk_SOS_uhi_even h9a, cholPlainEv_nonneg blk_SOS_uhi_even h9b,
    cholPlainEv_nonneg blk_SOS_uhi_even h9c, cholPlainEv_nonneg blk_SOS_uhi_odd h10a,
    cholPlainEv_nonneg blk_SOS_uhi_odd h10b, cholPlainEv_nonneg blk_SOS_uhi_odd h10c]

private lemma S2_pos : (0 : ℝ) < (S2 : ℝ) := by norm_num [S2]

private lemma minorCap_bound {t : ℝ} (ht_lo : -9 / 10 ≤ t) (ht_lt : t < 1) :
    peval H_int t / (S2 : ℝ) ≤ (1 + (l1List res_y_int : ℝ) / (20 * (S2 : ℝ))) * phi t := by
  set y : ℝ := Real.sqrt ((1 - t) / 2)
  have hy_sq : y ^ 2 = (1 - t) / 2 := Real.sq_sqrt (by linarith)
  have hy_pos : 0 < y := Real.sqrt_pos.mpr (by linarith)
  have hy_le1 : y ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have h1m2y : 1 - 2 * y ^ 2 = t := by linarith
  have hphi : phi t = (2 * y)⁻¹ := by
    unfold phi
    have h2 : 2 - 2 * t = (2 * y) ^ 2 := by linarith
    rw [h2, Real.sqrt_sq (by linarith)]
  have hid := peval_eq_zero_of_all _ minor_ok y
  simp only [peval_padd, peval_pscale, peval_pmul, peval_pneg, peval_chol1DPoly, peval_twoYH] at hid
  rw [h1m2y] at hid
  have h01 : peval [0, 20] y = 20 * y := by simp only [peval]; push_cast; ring
  have h02 : peval [19, 0, -20] y = 19 - 20 * y ^ 2 := by simp only [peval]; push_cast; ring
  have h03 : peval [0, 19, 0, -20] y = y * (19 - 20 * y ^ 2) := by simp only [peval]; push_cast; ring
  have hS : peval [-S2] y = -(S2 : ℝ) := by simp only [peval]; push_cast; ring
  rw [h01, h02, h03, hS] at hid
  have hnn0 : 0 ≤ chol1DEv sig_0 y := chol1DEv_nonneg _ _
  have hnn1 : 0 ≤ 20 * y * chol1DEv sig_1 y := mul_nonneg (by linarith) (chol1DEv_nonneg _ _)
  have hnn2 : 0 ≤ (19 - 20 * y ^ 2) * chol1DEv sig_2 y := mul_nonneg (by linarith) (chol1DEv_nonneg _ _)
  have hnn3 : 0 ≤ y * (19 - 20 * y ^ 2) * chol1DEv sig_3 y :=
    mul_nonneg (mul_nonneg hy_pos.le (by linarith)) (chol1DEv_nonneg _ _)
  have hres : peval res_y_int y ≤ (l1List res_y_int : ℝ) :=
    (le_abs_self _).trans (abs_peval_le_l1List res_y_int hy_pos.le hy_le1)
  have hkey : 20 * (2 * y * peval H_int t - (S2 : ℝ)) ≤ (l1List res_y_int : ℝ) := by
    push_cast at hid; linarith
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  rw [hphi, div_le_iff₀ hS2]
  have h2y_pos : (0 : ℝ) < 2 * y := by linarith
  have hmul : peval H_int t * (2 * y) ≤ (1 + (l1List res_y_int : ℝ) / (20 * (S2 : ℝ))) * (S2 : ℝ) := by
    have hdiv : (l1List res_y_int : ℝ) / (20 * (S2 : ℝ)) * (S2 : ℝ) = (l1List res_y_int : ℝ) / 20 := by
      field_simp
    linarith
  have := (le_mul_inv_iff₀ h2y_pos).mpr hmul
  linarith

/-! ## Section 3: 7-Piece Bernstein Tube Exclusion -/

private lemma peval_Peps_eq (y : ℝ) :
    peval Peps y = (K_bern : ℝ) * (S2 : ℝ) *
      ((1 - (eps_y_num : ℝ) / (eps_y_den : ℝ)) - 2 * y * (peval H_int (1 - 2 * y ^ 2) / (S2 : ℝ))) := by
  have hid := peval_eq_zero_of_all _ Peps_def_ok y
  simp only [peval_padd, peval_pneg, peval_pscale, peval_twoYH] at hid
  have hpeval_c : peval [const_peps] y = (const_peps : ℝ) := by simp only [peval]; ring
  rw [hpeval_c] at hid
  have hc : ((const_peps * eps_y_den : ℤ) : ℝ) = ((K_bern * S2 * (eps_y_den - eps_y_num) : ℤ) : ℝ) := by
    exact_mod_cast const_peps_ok
  push_cast at hc hid
  have hden : (0 : ℝ) < (eps_y_den : ℝ) := by norm_num [eps_y_den]
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  have hconst : (const_peps : ℝ) = (K_bern : ℝ) * (S2 : ℝ) * (1 - (eps_y_num : ℝ) / (eps_y_den : ℝ)) := by
    field_simp; linarith
  have h0 : peval Peps y = (const_peps : ℝ) - (K_bern : ℝ) * (2 * y * peval H_int (1 - 2 * y ^ 2)) := by
    linarith
  rw [h0, hconst]
  field_simp

private lemma y_in_tube_of_Peps_neg {y : ℝ} (hy0 : 0 ≤ y) (hy_top : y ≤ 9747 / 10000)
    (hneg : peval Peps y < 0) :
    ((yTubeLo_0 : ℝ) ≤ y ∧ y ≤ (yTubeHi_0 : ℝ)) ∨
    ((yTubeLo_1 : ℝ) ≤ y ∧ y ≤ (yTubeHi_1 : ℝ)) ∨
    ((yTubeLo_2 : ℝ) ≤ y ∧ y ≤ (yTubeHi_2 : ℝ)) ∨
    ((yTubeLo_3 : ℝ) ≤ y ∧ y ≤ (yTubeHi_3 : ℝ)) ∨
    ((yTubeLo_4 : ℝ) ≤ y ∧ y ≤ (yTubeHi_4 : ℝ)) ∨
    ((yTubeLo_5 : ℝ) ≤ y ∧ y ≤ (yTubeHi_5 : ℝ)) := by
  by_cases h5lo : y ≤ (yTubeLo_5 : ℝ)
  · exfalso
    have h := BPiece.nonneg Peps bp0 bp0_ok (y := y)
      (by norm_num [bp0]; linarith) (by norm_num [bp0, yTubeLo_5] at h5lo ⊢; linarith)
    linarith
  push Not at h5lo
  by_cases h5hi : y ≤ (yTubeHi_5 : ℝ)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h5lo.le, h5hi⟩))))
  push Not at h5hi
  by_cases h4lo : y ≤ (yTubeLo_4 : ℝ)
  · exfalso
    have h := BPiece.nonneg Peps bp1 bp1_ok (y := y)
      (by norm_num [bp1, yTubeHi_5] at h5hi ⊢; linarith)
      (by norm_num [bp1, yTubeLo_4] at h4lo ⊢; linarith)
    linarith
  push Not at h4lo
  by_cases h4hi : y ≤ (yTubeHi_4 : ℝ)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4lo.le, h4hi⟩))))
  push Not at h4hi
  by_cases h3lo : y ≤ (yTubeLo_3 : ℝ)
  · exfalso
    have h := BPiece.nonneg Peps bp2 bp2_ok (y := y)
      (by norm_num [bp2, yTubeHi_4] at h4hi ⊢; linarith)
      (by norm_num [bp2, yTubeLo_3] at h3lo ⊢; linarith)
    linarith
  push Not at h3lo
  by_cases h3hi : y ≤ (yTubeHi_3 : ℝ)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3lo.le, h3hi⟩)))
  push Not at h3hi
  by_cases h2lo : y ≤ (yTubeLo_2 : ℝ)
  · exfalso
    have h := BPiece.nonneg Peps bp3 bp3_ok (y := y)
      (by norm_num [bp3, yTubeHi_3] at h3hi ⊢; linarith)
      (by norm_num [bp3, yTubeLo_2] at h2lo ⊢; linarith)
    linarith
  push Not at h2lo
  by_cases h2hi : y ≤ (yTubeHi_2 : ℝ)
  · exact Or.inr (Or.inr (Or.inl ⟨h2lo.le, h2hi⟩))
  push Not at h2hi
  by_cases h1lo : y ≤ (yTubeLo_1 : ℝ)
  · exfalso
    have h := BPiece.nonneg Peps bp4 bp4_ok (y := y)
      (by norm_num [bp4, yTubeHi_2] at h2hi ⊢; linarith)
      (by norm_num [bp4, yTubeLo_1] at h1lo ⊢; linarith)
    linarith
  push Not at h1lo
  by_cases h1hi : y ≤ (yTubeHi_1 : ℝ)
  · exact Or.inr (Or.inl ⟨h1lo.le, h1hi⟩)
  push Not at h1hi
  by_cases h0lo : y ≤ (yTubeLo_0 : ℝ)
  · exfalso
    have h := BPiece.nonneg Peps bp5 bp5_ok (y := y)
      (by norm_num [bp5, yTubeHi_1] at h1hi ⊢; linarith)
      (by norm_num [bp5, yTubeLo_0] at h0lo ⊢; linarith)
    linarith
  push Not at h0lo
  by_cases h0hi : y ≤ (yTubeHi_0 : ℝ)
  · exact Or.inl ⟨h0lo.le, h0hi⟩
  push Not at h0hi
  exfalso
  have h := BPiece.nonneg Peps bp6 bp6_ok (y := y)
    (by norm_num [bp6, yTubeHi_0] at h0hi ⊢; linarith)
    (by norm_num [bp6]; linarith)
  linarith

private lemma tube_hit_of_y_box {y z : ℝ} (hzLo : (TableB5Data.zLo : ℝ) ≤ z) (hzHi : z ≤ (TableB5Data.zHi : ℝ))
    (a : ℕ) (ha : a < 6) (ylo yhi : ℚ) (hylo_pos : (0 : ℝ) ≤ (ylo : ℝ))
    (hy1 : (ylo : ℝ) ≤ y) (hy2 : y ≤ (yhi : ℝ))
    (hlo : (1 : ℝ) - 2 * (ylo : ℝ) ^ 2 ≤ (nuLoIdx a : ℝ) + 1 / 10000)
    (hhi : (nuHiIdx a : ℝ) - 1 / 10000 ≤ (1 : ℝ) - 2 * (yhi : ℝ) ^ 2) :
    |(1 - 2 * y ^ 2) - nuOfN a z| ≤ 1 / 10000 := by
  obtain ⟨hnuLo, hnuHi⟩ := nu_container_idx z hzLo hzHi a ha
  have hsq1 : (ylo : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
  have hsq2 : y ^ 2 ≤ (yhi : ℝ) ^ 2 := by nlinarith
  rw [abs_le]
  constructor <;> linarith

/-! ## Section 4: Main Theorem `cap_tube_forcing` -/

/-- **Main Stage B Cap Certificate & L3 Tube Forcing Theorem (`[-9/10, 1]`)**:
If `x : Fin 9 → R3` is an injective unit-sphere configuration with all pairwise inner products
`≥ -9/10` and `coulombEnergy9 x ≤ E_ttp_hi`, then every pair `(i, j)` (`i ≠ j`) lands within
`1 / 10000` of one of the six TTP node curves `ν₀(z), …, ν₅(z)` for any `z ∈ [zLo, zHi]`. -/
theorem cap_tube_forcing (x : Fin 9 → R3) (hu : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x)
    (hcap : ∀ i j : Fin 9, i ≠ j → -9 / 10 ≤ ⟪x i, x j⟫)
    (hE : coulombEnergy9 x ≤ E_ttp_hi)
    (z : ℝ) (hzLo : (TableB5Data.zLo : ℝ) ≤ z) (hzHi : z ≤ (TableB5Data.zHi : ℝ)) :
    TubePremise (toMat x) z (1 / 10000) := by
  let t : Fin 9 → Fin 9 → ℝ := fun i j => ⟪x i, x j⟫
  have ht_diag : ∀ i, t i i = 1 := fun i => by
    dsimp only [t]; rw [real_inner_self_eq_norm_sq, hu i]; norm_num
  have ht_sym : ∀ i j, t i j = t j i := fun i j => real_inner_comm (x j) (x i)
  have ht_hi : ∀ i j, t i j ≤ 1 := fun i j => inner_le_one_unit (hu i) (hu j)
  have ht_lt : ∀ i j, i ≠ j → t i j < 1 := fun i j hij =>
    inner_lt_one_of_ne_unit (hu i) (hu j) (fun h => hij (hinj h))
  have ht_abs : ∀ i j, |t i j| ≤ 1 := fun i j =>
    abs_le.mpr ⟨neg_one_le_inner_unit (hu i) (hu j), ht_hi i j⟩
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  let H : ℝ → ℝ := fun u => peval H_int u / (S2 : ℝ)
  let s : ℝ → ℝ → ℝ → ℝ := fun u v w => harmListEv harmBlks u v w / (S2 : ℝ)
  let R1 : ℝ := (l1Poly3 res_slack_int : ℝ) / (360 * (S2 : ℝ))
  let R2 : ℝ := (l1List res_y_int : ℝ) / (20 * (S2 : ℝ))
  have hasm := cap_assembly_9 t ht_diag ht_sym H ((e_int : ℝ) / (S2 : ℝ)) s
  -- Lower bound on slack for every ordered triple i < j < l
  have hslack : ∀ i : Fin 9, ∀ j ∈ Finset.Ioi i, ∀ l ∈ Finset.Ioi j,
      -R1 ≤ (H (t i j) + H (t i l) + H (t j l)) / 3
        - (e_int : ℝ) / (S2 : ℝ) / 36
        - 7 * sym3 s (t i j) (t i l) (t j l)
        - ((s 1 (t i j) (t i j) + s (t i j) 1 (t i j) + s (t i j) (t i j) 1)
          + (s 1 (t i l) (t i l) + s (t i l) 1 (t i l) + s (t i l) (t i l) 1)
          + (s 1 (t j l) (t j l) + s (t j l) 1 (t j l) + s (t j l) (t j l) 1)) / 3
        - s 1 1 1 / 8 := by
    intro i j hj l hl
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hjl : j < l := Finset.mem_Ioi.mp hl
    have hil : i < l := lt_trans hij hjl
    have hid := id_slack (t i j) (t i l) (t j l)
    have hsos := sosCap_ev_nonneg
      (hcap i j (ne_of_lt hij)) (ht_hi i j)
      (hcap i l (ne_of_lt hil)) (ht_hi i l)
      (hcap j l (ne_of_lt hjl)) (ht_hi j l)
      (detG_nonneg_of_unit (hu i) (hu j) (hu l))
    have hres := (abs_le.mp (abs_ev3_le_l1Poly3 res_slack_int (ht_abs i j) (ht_abs i l) (ht_abs j l))).1
    have hge : -(l1Poly3 res_slack_int : ℝ) ≤
        120 * (peval H_int (t i j) + peval H_int (t i l) + peval H_int (t j l))
        - 10 * (e_int : ℝ) - 45 * harmListEv harmBlks 1 1 1
        - 120 * (g_int_ev (t i j) + g_int_ev (t i l) + g_int_ev (t j l))
        - 840 * (harmListEv harmBlks (t i j) (t i l) (t j l)
          + harmListEv harmBlks (t i j) (t j l) (t i l)
          + harmListEv harmBlks (t i l) (t j l) (t i j)) := by linarith
    have h360 : (0 : ℝ) < 360 * (S2 : ℝ) := by linarith
    have hdiv := div_le_div_of_nonneg_right hge h360.le
    have hsym3 : sym3 s (t i j) (t i l) (t j l) =
        (harmListEv harmBlks (t i j) (t i l) (t j l)
          + harmListEv harmBlks (t i j) (t j l) (t i l)
          + harmListEv harmBlks (t i l) (t j l) (t i j)) / (3 * (S2 : ℝ)) := by
      unfold sym3
      dsimp only [s]
      rw [harmListEv_symm harmBlks (t i l) (t i j) (t j l),
          harmListEv_symm harmBlks (t j l) (t i j) (t i l),
          harmListEv_symm harmBlks (t j l) (t i l) (t i j)]
      ring
    dsimp only [R1]
    rw [← neg_div]
    refine le_trans hdiv (le_of_eq ?_)
    rw [hsym3]
    dsimp only [H, s, g_int_ev]
    field_simp
    ring
  have hSumTriples : -84 * R1 ≤
      sumTriples9 (fun i j l =>
        (H (t i j) + H (t i l) + H (t j l)) / 3
        - (e_int : ℝ) / (S2 : ℝ) / 36
        - 7 * sym3 s (t i j) (t i l) (t j l)
        - ((s 1 (t i j) (t i j) + s (t i j) 1 (t i j) + s (t i j) (t i j) 1)
          + (s 1 (t i l) (t i l) + s (t i l) 1 (t i l) + s (t i l) (t i l) 1)
          + (s 1 (t j l) (t j l) + s (t j l) 1 (t j l) + s (t j l) (t j l) 1)) / 3
        - s 1 1 1 / 8) := by
    have hc : (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (Finset.Ioi j).card : ℕ) = 84 := by decide
    have hcR : sumTriples9 (fun _ _ _ => (1 : ℝ)) = 84 := by
      unfold sumTriples9
      simpa [Finset.sum_const] using congrArg (Nat.cast (R := ℝ)) hc
    calc -84 * R1 = sumTriples9 (fun _ _ _ => -R1) := by
          unfold sumTriples9 at hcR ⊢
          have hmul : sumTriples9 (fun _ _ _ => -R1) = (-R1) * sumTriples9 (fun _ _ _ => (1 : ℝ)) := by
            unfold sumTriples9; simp only [Finset.mul_sum, mul_one]
          unfold sumTriples9 at hmul
          rw [hmul, hcR]; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
          Finset.sum_le_sum fun l hl => hslack i j hj l hl
  have hHarm : 0 ≤ ∑ i : Fin 9, ∑ j : Fin 9, ∑ l : Fin 9, s (t i j) (t i l) (t j l) := by
    dsimp only [s, t]
    simp_rw [← Finset.sum_div]
    exact div_nonneg (sum_harmListEv_nonneg harmBlks Finset.univ x hu) hS2.le
  have hsumH_ge : (e_int : ℝ) / (S2 : ℝ) - 36 * R1 ≤ sumPairs9 (fun i j => H (t i j)) := by
    linarith [hasm, hSumTriples, hHarm]
  -- Nonnegativity of every single pair deficit `(1 + R2) * phi (t i j) - H (t i j)`
  have hdef_nn : ∀ i : Fin 9, ∀ j ∈ Finset.Ioi i, 0 ≤ (1 + R2) * phi (t i j) - H (t i j) := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hm := minorCap_bound (hcap i j (ne_of_lt hij)) (ht_lt i j (ne_of_lt hij))
    dsimp only [H, R2]; linarith
  have hE_eq : coulombEnergy9 x = sumPairs9 (fun i j => phi (t i j)) := by
    unfold coulombEnergy9 sumPairs9
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact inv_norm_eq_phi (hu i) (hu j)
  have h1R2_nn : 0 ≤ 1 + R2 := by
    dsimp only [R2]
    have : (0 : ℝ) ≤ (l1List res_y_int : ℝ) / (20 * (S2 : ℝ)) := by positivity
    linarith
  let Delta_cap : ℝ := (1 + R2) * E_ttp_hi - ((e_int : ℝ) / (S2 : ℝ) - 36 * R1)
  have hsum_def_le : sumPairs9 (fun i j => (1 + R2) * phi (t i j) - H (t i j)) ≤ Delta_cap := by
    have hsplit : sumPairs9 (fun i j => (1 + R2) * phi (t i j) - H (t i j)) =
        (1 + R2) * coulombEnergy9 x - sumPairs9 (fun i j => H (t i j)) := by
      rw [hE_eq]
      unfold sumPairs9
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsplit]
    have hmul : (1 + R2) * coulombEnergy9 x ≤ (1 + R2) * E_ttp_hi :=
      mul_le_mul_of_nonneg_left hE h1R2_nn
    dsimp only [Delta_cap]
    linarith
  -- Extract per-pair deficit bound for any ordered pair i < j
  have hpair_lt : ∀ i j : Fin 9, i < j →
      ∃ a : ℕ, a < 6 ∧ |t i j - nuOfN a z| ≤ 1 / 10000 := by
    intro i j hij
    have hdef_ij : (1 + R2) * phi (t i j) - H (t i j) ≤ Delta_cap := by
      have hinner : (1 + R2) * phi (t i j) - H (t i j) ≤
          ∑ j' ∈ Finset.Ioi i, ((1 + R2) * phi (t i j') - H (t i j')) :=
        Finset.single_le_sum (fun j' hj' => hdef_nn i j' hj') (Finset.mem_Ioi.mpr hij)
      have houter : ∑ j' ∈ Finset.Ioi i, ((1 + R2) * phi (t i j') - H (t i j')) ≤
          sumPairs9 (fun i' j' => (1 + R2) * phi (t i' j') - H (t i' j')) :=
        Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' hj' => hdef_nn i' j' hj')
          (Finset.mem_univ i)
      linarith
    have hDelta_nn : 0 ≤ Delta_cap := le_trans (hdef_nn i j (Finset.mem_Ioi.mpr hij)) hdef_ij
    set y : ℝ := Real.sqrt ((1 - t i j) / 2)
    have hcap_ij : -9 / 10 ≤ t i j := hcap i j (ne_of_lt hij)
    have hlt_ij : t i j < 1 := ht_lt i j (ne_of_lt hij)
    have hy_sq : y ^ 2 = (1 - t i j) / 2 := Real.sq_sqrt (by linarith)
    have hy_pos : 0 < y := Real.sqrt_pos.mpr (by linarith)
    have hy_le1 : y ≤ 1 := by rw [Real.sqrt_le_one]; linarith
    have hy_top : y ≤ 9747 / 10000 := by
      have hsq : y ^ 2 ≤ (9747 / 10000 : ℝ) ^ 2 := by nlinarith
      nlinarith
    have h1m2y : 1 - 2 * y ^ 2 = t i j := by linarith
    have h2yphi : 2 * y * phi (t i j) = 1 := by
      unfold phi
      have h2 : 2 - 2 * t i j = (2 * y) ^ 2 := by linarith
      rw [h2, Real.sqrt_sq (by linarith)]
      field_simp
    have hmul2y : 2 * y * ((1 + R2) * phi (t i j) - H (t i j)) ≤ 2 * y * Delta_cap :=
      mul_le_mul_of_nonneg_left hdef_ij (by linarith)
    have h2y_le2 : 2 * y * Delta_cap ≤ 2 * Delta_cap := by nlinarith
    have h1m2yH : 1 - 2 * y * H (t i j) ≤ 2 * Delta_cap - R2 := by
      have hrew : 2 * y * ((1 + R2) * phi (t i j) - H (t i j)) =
          (1 + R2) * (2 * y * phi (t i j)) - 2 * y * H (t i j) := by ring
      rw [hrew, h2yphi, mul_one] at hmul2y
      linarith
    -- Show 2 * Delta_cap - R2 < eps_y using `eps_gap_ok`
    have hlt_eps : 2 * Delta_cap - R2 < (eps_y_num : ℝ) / (eps_y_den : ℝ) := by
      have hgap : ((40 * E_ttp_hi_num * S2 + (2 * E_ttp_hi_num - E_ttp_hi_den) * (l1List res_y_int : ℤ)
          - 40 * e_int * E_ttp_hi_den + 4 * (l1Poly3 res_slack_int : ℤ) * E_ttp_hi_den : ℤ) : ℝ) <
          ((20 * S2 * 50 : ℤ) : ℝ) := by exact_mod_cast eps_gap_ok
      push_cast at hgap
      dsimp only [Delta_cap, R1, R2, E_ttp_hi]
      have hdenE : (0 : ℝ) < (E_ttp_hi_den : ℝ) := by norm_num [E_ttp_hi_den]
      have hdenEps : (0 : ℝ) < (eps_y_den : ℝ) := by norm_num [eps_y_den]
      have hL : 2 * ((1 + (l1List res_y_int : ℝ) / (20 * (S2 : ℝ))) * ((E_ttp_hi_num : ℝ) / (E_ttp_hi_den : ℝ))
          - ((e_int : ℝ) / (S2 : ℝ) - 36 * ((l1Poly3 res_slack_int : ℝ) / (360 * (S2 : ℝ)))))
          - (l1List res_y_int : ℝ) / (20 * (S2 : ℝ)) =
          (40 * (E_ttp_hi_num : ℝ) * (S2 : ℝ) + (2 * (E_ttp_hi_num : ℝ) - (E_ttp_hi_den : ℝ)) * (l1List res_y_int : ℝ)
            - 40 * (e_int : ℝ) * (E_ttp_hi_den : ℝ) + 4 * (l1Poly3 res_slack_int : ℝ) * (E_ttp_hi_den : ℝ))
            / (20 * (S2 : ℝ) * (E_ttp_hi_den : ℝ)) := by
        field_simp; ring
      have hR : (eps_y_num : ℝ) / (eps_y_den : ℝ) =
          (20 * (S2 : ℝ) * 50) / (20 * (S2 : ℝ) * (E_ttp_hi_den : ℝ)) := by
        norm_num [eps_y_num, eps_y_den, E_ttp_hi_den]
        field_simp; ring
      rw [hL, hR]
      exact div_lt_div_of_pos_right hgap (by positivity)
    have hPeps_neg : peval Peps y < 0 := by
      rw [peval_Peps_eq, h1m2y]
      have hKS_pos : (0 : ℝ) < (K_bern : ℝ) * (S2 : ℝ) := by norm_num [K_bern, S2]
      have hneg' : (1 - (eps_y_num : ℝ) / (eps_y_den : ℝ)) - 2 * y * H (t i j) < 0 := by linarith
      exact mul_neg_of_pos_of_neg hKS_pos hneg'
    have q_le_r : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => by exact_mod_cast h
    rcases y_in_tube_of_Peps_neg hy_pos.le hy_top hPeps_neg with
      ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · refine ⟨0, by omega, ?_⟩
      rw [← h1m2y]
      exact tube_hit_of_y_box hzLo hzHi 0 (by omega) yTubeLo_0 yTubeHi_0 (by norm_num [yTubeLo_0]) hy1 hy2
        (by simpa [nuLoIdx] using q_le_r tube0_lo_ok) (by simpa [nuHiIdx] using q_le_r tube0_hi_ok)
    · refine ⟨1, by omega, ?_⟩
      rw [← h1m2y]
      exact tube_hit_of_y_box hzLo hzHi 1 (by omega) yTubeLo_1 yTubeHi_1 (by norm_num [yTubeLo_1]) hy1 hy2
        (by simpa [nuLoIdx] using q_le_r tube1_lo_ok) (by simpa [nuHiIdx] using q_le_r tube1_hi_ok)
    · refine ⟨2, by omega, ?_⟩
      rw [← h1m2y]
      exact tube_hit_of_y_box hzLo hzHi 2 (by omega) yTubeLo_2 yTubeHi_2 (by norm_num [yTubeLo_2]) hy1 hy2
        (by simpa [nuLoIdx] using q_le_r tube2_lo_ok) (by simpa [nuHiIdx] using q_le_r tube2_hi_ok)
    · refine ⟨3, by omega, ?_⟩
      rw [← h1m2y]
      exact tube_hit_of_y_box hzLo hzHi 3 (by omega) yTubeLo_3 yTubeHi_3 (by norm_num [yTubeLo_3]) hy1 hy2
        (by simpa [nuLoIdx] using q_le_r tube3_lo_ok) (by simpa [nuHiIdx] using q_le_r tube3_hi_ok)
    · refine ⟨4, by omega, ?_⟩
      rw [← h1m2y]
      exact tube_hit_of_y_box hzLo hzHi 4 (by omega) yTubeLo_4 yTubeHi_4 (by norm_num [yTubeLo_4]) hy1 hy2
        (by simpa [nuLoIdx] using q_le_r tube4_lo_ok) (by simpa [nuHiIdx] using q_le_r tube4_hi_ok)
    · refine ⟨5, by omega, ?_⟩
      rw [← h1m2y]
      exact tube_hit_of_y_box hzLo hzHi 5 (by omega) yTubeLo_5 yTubeHi_5 (by norm_num [yTubeLo_5]) hy1 hy2
        (by simpa [nuLoIdx] using q_le_r tube5_lo_ok) (by simpa [nuHiIdx] using q_le_r tube5_hi_ok)
  -- Symmetrize to all i ≠ j and convert to `toMat x`
  intro i j hij
  rw [toMat_dot]
  rcases lt_or_gt_of_ne hij with h | h
  · exact hpair_lt i j h
  · simpa [t, ht_sym i j] using hpair_lt j i h

end ThomsonN9.StageB.CapCert
