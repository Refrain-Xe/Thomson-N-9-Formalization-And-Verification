import ThomsonN9.StageB.SlabCertData

/-!
# Thomson N = 9 Stage B — Module 3: Slab Exclusion (`[-1, -9/10]`, `M=6, K=6`)

Proves `slab_exclusion`: every 9-point unit-sphere configuration `x` having at least one pair
with inner product `⟪x i, x j⟫ ≤ -9/10` has strict Coulomb energy strictly above `E_ttp_hi`.
-/

set_option maxHeartbeats 8000000

namespace ThomsonN9.StageB.SlabCert

open Finset ThomsonN9.StageB ThomsonN9.StageB.PolyKron ThomsonN9.StageB.SlabCertData
open scoped RealInnerProductSpace

/-- Canonical rational upper bound `E_ttp_hi = 25.7599865312698317 > E(triCapPrism z*)`. -/
noncomputable def E_ttp_hi : ℝ := (E_ttp_hi_num : ℝ) / (E_ttp_hi_den : ℝ)

/-! ## Section 1: Helper Lemmas for `twoYH`, Permutations, and `HasPolyRep3` Lists -/

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

lemma peval_twoYH (h : List ℤ) (y : ℝ) :
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

/-- Permutation invariance of `coulombEnergy9`. -/
lemma coulombEnergy9_perm (x : Fin 9 → R3) (σ : Equiv.Perm (Fin 9)) :
    coulombEnergy9 (fun i => x (σ i)) = coulombEnergy9 x := by
  have hhalf : ∀ g : Fin 9 → Fin 9 → ℝ, (∀ i j, g i j = g j i) → (∀ i, g i i = 0) →
      2 * (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, g i j) = ∑ i : Fin 9, ∑ j : Fin 9, g i j := by
    intro g hsym hdiag
    have hrow : ∀ i : Fin 9, ∑ j : Fin 9, g i j =
        (∑ j ∈ Finset.Ioi i, g i j) + ∑ j ∈ Finset.Iio i, g i j := by
      intro i
      have huniv : (Finset.univ : Finset (Fin 9)) = insert i (Finset.Ioi i ∪ Finset.Iio i) := by
        ext j; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_Ioi,
          Finset.mem_Iio, true_iff]; exact eq_or_ne j i |>.imp_right lt_or_gt_of_ne |>.imp_right Or.symm
      have hnot : i ∉ Finset.Ioi i ∪ Finset.Iio i := by simp
      have hdisj : Disjoint (Finset.Ioi i) (Finset.Iio i) := by
        rw [Finset.disjoint_left]; intro j h1 h2; simp at h1 h2; omega
      rw [huniv, Finset.sum_insert hnot, hdiag i, zero_add, Finset.sum_union hdisj]
    simp_rw [hrow, Finset.sum_add_distrib]
    have hflip : ∑ i : Fin 9, ∑ j ∈ Finset.Iio i, g i j = ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, g i j := by
      have eIio : ∀ i : Fin 9, ∑ j ∈ Finset.Iio i, g i j = ∑ j : Fin 9, if j < i then g i j else 0 := by
        intro i; rw [← Finset.sum_filter]; congr 1; ext j; simp
      have eIoi : ∀ i : Fin 9, ∑ j ∈ Finset.Ioi i, g i j = ∑ j : Fin 9, if i < j then g i j else 0 := by
        intro i; rw [← Finset.sum_filter]; congr 1; ext j; simp
      simp_rw [eIio, eIoi]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
        by_cases h : j < i <;> simp [h, hsym i j]
    linarith
  unfold coulombEnergy9
  have h1 := hhalf (fun i j => ‖x (σ i) - x (σ j)‖⁻¹)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  have h2 := hhalf (fun i j => ‖x i - x j‖⁻¹)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  have hsum : ∑ i : Fin 9, ∑ j : Fin 9, ‖x (σ i) - x (σ j)‖⁻¹ =
      ∑ i : Fin 9, ∑ j : Fin 9, ‖x i - x j‖⁻¹ := by
    rw [Equiv.sum_comp σ (fun i => ∑ j : Fin 9, ‖x i - x (σ j)‖⁻¹)]
    exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => ‖x i - x j‖⁻¹)
  linarith

private lemma HasPolyRep3.of_plain_deg {blk : CholPlainBlk} {dmp db : ℕ}
    (hok : plainDegOk blk dmp db = true) (hD : dmp + (db + db) ≤ 11) :
    HasPolyRep3 11 11 11 (cholPlainL1 blk) (cholPlainEv blk) := by
  simp only [plainDegOk, Bool.and_eq_true] at hok
  exact (HasPolyRep3.of_cholPlain blk hok.1 hok.2).widen hD hD hD (le_refl _)

private lemma HasPolyRep3.of_std_deg {blk : CholStdBlk} {dmp db : ℕ}
    (hok : stdDegOk blk dmp db = true) (hD : dmp + (db + db) ≤ 11) :
    HasPolyRep3 11 11 11 (cholStdL1 blk) (cholStdEv blk) := by
  simp only [stdDegOk, Bool.and_eq_true] at hok
  exact (HasPolyRep3.of_cholStd blk hok.1.1 hok.1.2 hok.2).widen hD hD hD (le_refl _)

private lemma harmP_rep : HasPolyRep3 5 5 5 (harmListL1 harmP) (harmListEv harmP) :=
  HasPolyRep3.of_harmList harmP harm_deg_ok.1

private lemma harmR_rep : HasPolyRep3 5 5 5 (harmListL1 harmR) (harmListEv harmR) :=
  HasPolyRep3.of_harmList harmR harm_deg_ok.2

private def gP_int_ev (x : ℝ) : ℝ :=
  harmListEv harmP 1 x x + harmListEv harmP x 1 x + harmListEv harmP x x 1

private def gR_int_ev (x : ℝ) : ℝ :=
  harmListEv harmR 1 x x + harmListEv harmR x 1 x + harmListEv harmR x x 1

private lemma gP_rep_u : HasPolyRep3 11 11 11 (3 * harmListL1 harmP) (fun u _ _ => gP_int_ev u) := by
  have h1 := harmP_rep.diag_1uu
  have h2 := harmP_rep.diag_u1u
  have h3 := harmP_rep.diag_uu1
  have hsum := ((h1.add h2).add h3).widen (da' := 11) (db' := 11) (dc' := 11)
    (L' := 3 * harmListL1 harmP) (by omega) (by omega) (by omega) (by omega)
  exact hsum.congr (g := fun u _ _ => gP_int_ev u) fun u _ _ => by simp only [gP_int_ev]

private lemma gR_rep_u : HasPolyRep3 11 11 11 (3 * harmListL1 harmR) (fun u _ _ => gR_int_ev u) := by
  have h1 := harmR_rep.diag_1uu
  have h2 := harmR_rep.diag_u1u
  have h3 := harmR_rep.diag_uu1
  have hsum := ((h1.add h2).add h3).widen (da' := 11) (db' := 11) (dc' := 11)
    (L' := 3 * harmListL1 harmR) (by omega) (by omega) (by omega) (by omega)
  exact hsum.congr (g := fun u _ _ => gR_int_ev u) fun u _ _ => by simp only [gR_int_ev]

/-! ## Section 2: Real Evaluators for Orbit A / B / G SOS Sums & Exact Kronecker Identities -/

private def sosA_ev (u v t : ℝ) : ℝ :=
  (sosA_sym.map fun b => cholPlainEv b u v t).sum +
  (sosA_asym.map fun b => cholPlainEv b u v t + cholPlainEv b u t v).sum

private def sosB_ev (u v t : ℝ) : ℝ :=
  (sosB_sym.map fun b => cholPlainEv b u v t).sum +
  (sosB_asym.map fun b => cholPlainEv b u v t + cholPlainEv b v u t).sum

private def sosG_ev (u v t : ℝ) : ℝ :=
  (sosG_s3_plain.map fun b => cholPlainEv b u v t).sum +
  (sosG_s3_std.map fun b => cholStdEv b u v t).sum +
  (sosG_s2.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum

private lemma cast_foldl_plain (eu ev et : ℕ) (blks : List CholPlainBlk) :
    ((blks.foldl (fun a b => a + cholPlainKevShift eu ev et b) 0 : ℤ) : ℝ) =
      (blks.map fun b => cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et)).sum := by
  have haux : ∀ (l : List CholPlainBlk) (acc : ℤ),
      ((l.foldl (fun a b => a + cholPlainKevShift eu ev et b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b => cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) ((2 : ℝ) ^ et)).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_cholPlainKevShift]; ring
  rw [haux]; simp

private lemma cast_foldl_plain2 (eu1 ev1 et1 eu2 ev2 et2 : ℕ) (blks : List CholPlainBlk) :
    ((blks.foldl (fun a b => a + cholPlainKevShift eu1 ev1 et1 b + cholPlainKevShift eu2 ev2 et2 b) 0 : ℤ) : ℝ) =
      (blks.map fun b =>
        cholPlainEv b ((2 : ℝ) ^ eu1) ((2 : ℝ) ^ ev1) ((2 : ℝ) ^ et1) +
        cholPlainEv b ((2 : ℝ) ^ eu2) ((2 : ℝ) ^ ev2) ((2 : ℝ) ^ et2)).sum := by
  have haux : ∀ (l : List CholPlainBlk) (acc : ℤ),
      ((l.foldl (fun a b => a + cholPlainKevShift eu1 ev1 et1 b + cholPlainKevShift eu2 ev2 et2 b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b =>
          cholPlainEv b ((2 : ℝ) ^ eu1) ((2 : ℝ) ^ ev1) ((2 : ℝ) ^ et1) +
          cholPlainEv b ((2 : ℝ) ^ eu2) ((2 : ℝ) ^ ev2) ((2 : ℝ) ^ et2)).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_cholPlainKevShift, cast_cholPlainKevShift]; ring
  rw [haux]; simp

private lemma cast_foldl_plain3 (eu1 ev1 et1 eu2 ev2 et2 eu3 ev3 et3 : ℕ) (blks : List CholPlainBlk) :
    ((blks.foldl (fun a b => a + cholPlainKevShift eu1 ev1 et1 b + cholPlainKevShift eu2 ev2 et2 b
        + cholPlainKevShift eu3 ev3 et3 b) 0 : ℤ) : ℝ) =
      (blks.map fun b =>
        cholPlainEv b ((2 : ℝ) ^ eu1) ((2 : ℝ) ^ ev1) ((2 : ℝ) ^ et1) +
        cholPlainEv b ((2 : ℝ) ^ eu2) ((2 : ℝ) ^ ev2) ((2 : ℝ) ^ et2) +
        cholPlainEv b ((2 : ℝ) ^ eu3) ((2 : ℝ) ^ ev3) ((2 : ℝ) ^ et3)).sum := by
  have haux : ∀ (l : List CholPlainBlk) (acc : ℤ),
      ((l.foldl (fun a b => a + cholPlainKevShift eu1 ev1 et1 b + cholPlainKevShift eu2 ev2 et2 b
          + cholPlainKevShift eu3 ev3 et3 b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b =>
          cholPlainEv b ((2 : ℝ) ^ eu1) ((2 : ℝ) ^ ev1) ((2 : ℝ) ^ et1) +
          cholPlainEv b ((2 : ℝ) ^ eu2) ((2 : ℝ) ^ ev2) ((2 : ℝ) ^ et2) +
          cholPlainEv b ((2 : ℝ) ^ eu3) ((2 : ℝ) ^ ev3) ((2 : ℝ) ^ et3)).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_cholPlainKevShift, cast_cholPlainKevShift, cast_cholPlainKevShift]; ring
  rw [haux]; simp

private lemma cast_foldl_std (w D : ℕ) (blks : List CholStdBlk) :
    ((blks.foldl (fun a b => a + cholStdKev w D b) 0 : ℤ) : ℝ) =
      (blks.map fun b => cholStdEv b ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D))).sum := by
  have haux : ∀ (l : List CholStdBlk) (acc : ℤ),
      ((l.foldl (fun a b => a + cholStdKev w D b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b => cholStdEv b ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D))).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      push_cast
      rw [cast_cholStdKev]; ring
  rw [haux]; simp

private lemma id_lamA (u v t : ℝ) :
    40 * peval hA_int u + 280 * (peval psiBa_int v + peval psiBa_int t) - 280 * (ca_int : ℝ)
      - 80 * gP_int_ev u - 560 * (harmListEv harmP u v t + harmListEv harmP u t v)
      - 560 * harmListEv harmR v t u =
    sosA_ev u v t + ev3 resA_int u v t := by
  let f : ℝ → ℝ → ℝ → ℝ := fun u v t =>
    (40 * peval hA_int u + 280 * (peval psiBa_int v + peval psiBa_int t) - 280 * (ca_int : ℝ)
      - 80 * gP_int_ev u - 560 * (harmListEv harmP u v t + harmListEv harmP u t v)
      - 560 * harmListEv harmR v t u) - (sosA_ev u v t + ev3 resA_int u v t)
  suffices h0 : f u v t = 0 by dsimp only [f] at h0; linarith
  have hd := sos_exact_deg_ok
  have hrep_hA : HasPolyRep3 11 11 11 (40 * l1List hA_int) (fun u _ _ => 40 * peval hA_int u) := by
    simpa [Int.natAbs_natCast] using ((HasPolyRep3.of_peval_u hA_int).smul_int 40).widen
      (da' := 11) (db' := 11) (dc' := 11) (by decide) (by omega) (by omega) (le_refl _)
  have hrep_pBv : HasPolyRep3 11 11 11 (280 * l1List psiBa_int) (fun _ v _ => 280 * peval psiBa_int v) := by
    simpa [Int.natAbs_natCast] using ((HasPolyRep3.of_peval_v psiBa_int).smul_int 280).widen
      (da' := 11) (db' := 11) (dc' := 11) (by omega) (by decide) (by omega) (le_refl _)
  have hrep_pBt : HasPolyRep3 11 11 11 (280 * l1List psiBa_int) (fun _ _ t => 280 * peval psiBa_int t) := by
    simpa [Int.natAbs_natCast] using ((HasPolyRep3.of_peval_t psiBa_int).smul_int 280).widen
      (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by decide) (le_refl _)
  have hrep_ca : HasPolyRep3 11 11 11 (280 * ca_int.natAbs) (fun _ _ _ => 280 * (ca_int : ℝ)) := by
    have h := (HasPolyRep3.const (280 * ca_int)).widen (da' := 11) (db' := 11) (dc' := 11)
      (by omega) (by omega) (by omega) (by rw [Int.natAbs_mul])
    exact h.congr fun _ _ _ => by push_cast; ring
  have hrep_gP : HasPolyRep3 11 11 11 (80 * (3 * harmListL1 harmP)) (fun u _ _ => 80 * gP_int_ev u) := by
    simpa [Int.natAbs_natCast] using gP_rep_u.smul_int 80
  have hrep_sP : HasPolyRep3 11 11 11 (560 * (2 * harmListL1 harmP))
      (fun u v t => 560 * (harmListEv harmP u v t + harmListEv harmP u t v)) := by
    have h1 := harmP_rep.widen (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by omega) (le_refl _)
    have h2 := h1.perm_utv
    have h12 := (h1.add h2).widen (le_refl _) (le_refl _) (le_refl _) (by omega : harmListL1 harmP + harmListL1 harmP ≤ 2 * harmListL1 harmP)
    simpa [Int.natAbs_natCast] using h12.smul_int 560
  have hrep_sR : HasPolyRep3 11 11 11 (560 * harmListL1 harmR) (fun u v t => 560 * harmListEv harmR v t u) := by
    have h1 := harmR_rep.perm_vtu.widen (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by omega) (le_refl _)
    simpa [Int.natAbs_natCast] using h1.smul_int 560
  have hrep_sym : HasPolyRep3 11 11 11 (sosA_sym.foldl (fun a b => a + cholPlainL1 b) 0)
      (fun u v t => (sosA_sym.map fun b => cholPlainEv b u v t).sum) := by
    have b1 := HasPolyRep3.of_plain_deg hd.1 (by omega)
    have b2 := HasPolyRep3.of_plain_deg hd.2.1 (by omega)
    have b3 := HasPolyRep3.of_plain_deg hd.2.2.1 (by omega)
    have b4 := HasPolyRep3.of_plain_deg hd.2.2.2.1 (by omega)
    have b5 := HasPolyRep3.of_plain_deg hd.2.2.2.2.1 (by omega)
    have b6 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.1 (by omega)
    have b7 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.1 (by omega)
    have b8 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.2.1 (by omega)
    have hall := (((((((b1.add b2).add b3).add b4).add b5).add b6).add b7).add b8)
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by simp [sosA_sym]) |>.congr fun u v t => ?_
    simp [sosA_sym]; ring
  have hrep_asym : HasPolyRep3 11 11 11 (2 * sosA_asym.foldl (fun a b => a + cholPlainL1 b) 0)
      (fun u v t => (sosA_asym.map fun b => cholPlainEv b u v t + cholPlainEv b u t v).sum) := by
    have b1 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.2.2.1 (by omega)
    have b2 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.2.2.2.1 (by omega)
    have hall := (b1.add b1.perm_utv).add (b2.add b2.perm_utv)
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by simp [sosA_asym]; omega) |>.congr fun u v t => ?_
    simp [sosA_asym]
  have hrep_res : HasPolyRep3 11 11 11 (l1Poly3 resA_int) (ev3 resA_int) :=
    HasPolyRep3.of_poly3 resA_int res_deg_ok.1
  have hrep_f : HasPolyRep3 11 11 11 l1A f := by
    have hall := (((((((hrep_hA.add hrep_pBv).add hrep_pBt).sub hrep_ca).sub hrep_gP).sub hrep_sP).sub hrep_sR).sub
      ((hrep_sym.add hrep_asym).add hrep_res))
    exact hall.widen (le_refl _) (le_refl _) (le_refl _) (by unfold l1A; omega) |>.congr fun a b c => by
      dsimp only [f, sosA_ev]; ring
  have hval : f ((2 : ℝ) ^ w_kron) ((2 : ℝ) ^ (w_kron * D_kron)) ((2 : ℝ) ^ (w_kron * D_kron * D_kron)) = 0 := by
    have hk := kronA_ok
    unfold checkKronA at hk
    simp only [beq_iff_eq] at hk
    have hcast : (((40 * pevalZ hA_int ((Nat.shiftLeft 1 w_kron : ℕ) : ℤ)
      + 280 * (pevalZ psiBa_int ((Nat.shiftLeft 1 (w_kron * D_kron) : ℕ) : ℤ)
        + pevalZ psiBa_int ((Nat.shiftLeft 1 (w_kron * D_kron * D_kron) : ℕ) : ℤ))
      - 280 * ca_int
      - 80 * (harmListKevShift 0 w_kron w_kron harmP + harmListKevShift w_kron 0 w_kron harmP + harmListKevShift w_kron w_kron 0 harmP)
      - 560 * (harmListKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) harmP
        + harmListKevShift w_kron (w_kron * D_kron * D_kron) (w_kron * D_kron) harmP)
      - 560 * harmListKevShift (w_kron * D_kron) (w_kron * D_kron * D_kron) w_kron harmR : ℤ) : ℝ)) =
      (((sosA_sym.foldl (fun a b => a + cholPlainKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) b) 0
      + sosA_asym.foldl (fun a b => a + cholPlainKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) b
        + cholPlainKevShift w_kron (w_kron * D_kron * D_kron) (w_kron * D_kron) b) 0
      + kev3Shift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) resA_int : ℤ) : ℝ)) := by
      exact_mod_cast hk
    push_cast at hcast
    rw [cast_pevalZ, cast_pevalZ, cast_pevalZ,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_foldl_plain, cast_foldl_plain2, cast_kev3Shift] at hcast
    push_cast at hcast
    simp only [nat_shiftLeft_one_cast_real, pow_zero] at hcast
    dsimp only [f, sosA_ev, gP_int_ev]
    linarith
  exact eq_zero_of_kev3_zero (da := 11) (db := 11) (dc := 11) (D := D_kron) (w := w_kron)
    (by decide) (by decide) (by decide) (by decide) hrep_f l1_ok.1 hval u v t

private lemma id_lamB (u v t : ℝ) :
    2 * (peval hB_int u - peval psiBa_int u + peval hB_int v - peval psiBa_int v)
      + 12 * peval psiCb_int t - 12 * (cb_int : ℝ)
      - 2 * (gP_int_ev u + gP_int_ev v + gR_int_ev u + gR_int_ev v)
      - 24 * harmListEv harmP u v t
      - 24 * (harmListEv harmR u t v + harmListEv harmR v t u) =
    sosB_ev u v t + ev3 resB_int u v t := by
  let f : ℝ → ℝ → ℝ → ℝ := fun u v t =>
    (2 * (peval hB_int u - peval psiBa_int u + peval hB_int v - peval psiBa_int v)
      + 12 * peval psiCb_int t - 12 * (cb_int : ℝ)
      - 2 * (gP_int_ev u + gP_int_ev v + gR_int_ev u + gR_int_ev v)
      - 24 * harmListEv harmP u v t
      - 24 * (harmListEv harmR u t v + harmListEv harmR v t u))
    - (sosB_ev u v t + ev3 resB_int u v t)
  suffices h0 : f u v t = 0 by dsimp only [f] at h0; linarith
  have hd := sos_exact_deg_ok
  have hB_u : HasPolyRep3 11 11 11 (l1List hB_int + l1List psiBa_int) (fun u _ _ => peval hB_int u - peval psiBa_int u) :=
    ((HasPolyRep3.of_peval_u hB_int).widen (da' := 11) (db' := 11) (dc' := 11) (by decide) (by omega) (by omega) (le_refl _)).sub
    ((HasPolyRep3.of_peval_u psiBa_int).widen (da' := 11) (db' := 11) (dc' := 11) (by decide) (by omega) (by omega) (le_refl _))
  have hB_uv : HasPolyRep3 11 11 11 (2 * (l1List hB_int + l1List psiBa_int) + 2 * (l1List hB_int + l1List psiBa_int))
      (fun u v _ => 2 * (peval hB_int u - peval psiBa_int u + peval hB_int v - peval psiBa_int v)) := by
    have ha : HasPolyRep3 11 11 11 (2 * (l1List hB_int + l1List psiBa_int))
        (fun u _ _ => 2 * (peval hB_int u - peval psiBa_int u)) := by
      simpa [Int.natAbs_natCast] using hB_u.smul_int 2
    have hb : HasPolyRep3 11 11 11 (2 * (l1List hB_int + l1List psiBa_int))
        (fun _ v _ => 2 * (peval hB_int v - peval psiBa_int v)) := by
      simpa [Int.natAbs_natCast] using hB_u.perm_vut.smul_int 2
    exact (ha.add hb).congr fun u v _ => by ring
  have hpsiC : HasPolyRep3 11 11 11 (12 * l1List psiCb_int) (fun _ _ t => 12 * peval psiCb_int t) := by
    simpa [Int.natAbs_natCast] using ((HasPolyRep3.of_peval_t psiCb_int).smul_int 12).widen
      (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by decide) (le_refl _)
  have hcb : HasPolyRep3 11 11 11 (12 * cb_int.natAbs) (fun _ _ _ => 12 * (cb_int : ℝ)) := by
    have h := (HasPolyRep3.const (12 * cb_int)).widen (da' := 11) (db' := 11) (dc' := 11)
      (by omega) (by omega) (by omega) (by rw [Int.natAbs_mul])
    exact h.congr fun _ _ _ => by push_cast; ring
  have hgPR : HasPolyRep3 11 11 11
      (2 * (3 * harmListL1 harmP + 3 * harmListL1 harmP + 3 * harmListL1 harmR + 3 * harmListL1 harmR))
      (fun u v _ => 2 * (gP_int_ev u + gP_int_ev v + gR_int_ev u + gR_int_ev v)) := by
    have h := ((gP_rep_u.add gP_rep_u.perm_vut).add gR_rep_u).add gR_rep_u.perm_vut
    simpa [Int.natAbs_natCast] using h.smul_int 2
  have hsP : HasPolyRep3 11 11 11 (24 * harmListL1 harmP) (fun u v t => 24 * harmListEv harmP u v t) := by
    have h := harmP_rep.widen (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by omega) (le_refl _)
    simpa [Int.natAbs_natCast] using h.smul_int 24
  have hsR : HasPolyRep3 11 11 11 (24 * (2 * harmListL1 harmR))
      (fun u v t => 24 * (harmListEv harmR u t v + harmListEv harmR v t u)) := by
    have h1 := harmR_rep.perm_utv.widen (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by omega) (le_refl _)
    have h2 := harmR_rep.perm_vtu.widen (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by omega) (le_refl _)
    have h12 := (h1.add h2).widen (le_refl _) (le_refl _) (le_refl _) (by omega : harmListL1 harmR + harmListL1 harmR ≤ 2 * harmListL1 harmR)
    simpa [Int.natAbs_natCast] using h12.smul_int 24
  have hdB := hd.2.2.2.2.2.2.2.2.2.2
  have hrep_sym : HasPolyRep3 11 11 11 (sosB_sym.foldl (fun a b => a + cholPlainL1 b) 0)
      (fun u v t => (sosB_sym.map fun b => cholPlainEv b u v t).sum) := by
    have b1 := HasPolyRep3.of_plain_deg hdB.1 (by omega)
    have b2 := HasPolyRep3.of_plain_deg hdB.2.1 (by omega)
    have b3 := HasPolyRep3.of_plain_deg hdB.2.2.1 (by omega)
    have b4 := HasPolyRep3.of_plain_deg hdB.2.2.2.1 (by omega)
    have b5 := HasPolyRep3.of_plain_deg hdB.2.2.2.2.1 (by omega)
    have b6 := HasPolyRep3.of_plain_deg hdB.2.2.2.2.2.1 (by omega)
    have b7 := HasPolyRep3.of_plain_deg hdB.2.2.2.2.2.2.1 (by omega)
    have b8 := HasPolyRep3.of_plain_deg hdB.2.2.2.2.2.2.2.1 (by omega)
    have hall := (((((((b1.add b2).add b3).add b4).add b5).add b6).add b7).add b8)
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by simp [sosB_sym]) |>.congr fun u v t => ?_
    simp [sosB_sym]; ring
  have hrep_asym : HasPolyRep3 11 11 11 (2 * sosB_asym.foldl (fun a b => a + cholPlainL1 b) 0)
      (fun u v t => (sosB_asym.map fun b => cholPlainEv b u v t + cholPlainEv b v u t).sum) := by
    have b1 := HasPolyRep3.of_plain_deg hdB.2.2.2.2.2.2.2.2.1 (by omega)
    have b2 := HasPolyRep3.of_plain_deg hdB.2.2.2.2.2.2.2.2.2.1 (by omega)
    have hall := (b1.add b1.perm_vut).add (b2.add b2.perm_vut)
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by simp [sosB_asym]; omega) |>.congr fun u v t => ?_
    simp [sosB_asym]
  have hrep_res : HasPolyRep3 11 11 11 (l1Poly3 resB_int) (ev3 resB_int) :=
    HasPolyRep3.of_poly3 resB_int res_deg_ok.2.1
  have hrep_f : HasPolyRep3 11 11 11 l1B f := by
    have hall := (((((hB_uv.add hpsiC).sub hcb).sub hgPR).sub hsP).sub hsR).sub
      ((hrep_sym.add hrep_asym).add hrep_res)
    exact hall.widen (le_refl _) (le_refl _) (le_refl _) (by unfold l1B; omega) |>.congr fun a b c => by
      dsimp only [f, sosB_ev]
  have hval : f ((2 : ℝ) ^ w_kron) ((2 : ℝ) ^ (w_kron * D_kron)) ((2 : ℝ) ^ (w_kron * D_kron * D_kron)) = 0 := by
    have hk := kronB_ok
    unfold checkKronB at hk
    simp only [beq_iff_eq] at hk
    have hcast : (((2 * (pevalZ hB_int ((Nat.shiftLeft 1 w_kron : ℕ) : ℤ)
      - pevalZ psiBa_int ((Nat.shiftLeft 1 w_kron : ℕ) : ℤ)
      + pevalZ hB_int ((Nat.shiftLeft 1 (w_kron * D_kron) : ℕ) : ℤ)
      - pevalZ psiBa_int ((Nat.shiftLeft 1 (w_kron * D_kron) : ℕ) : ℤ))
      + 12 * pevalZ psiCb_int ((Nat.shiftLeft 1 (w_kron * D_kron * D_kron) : ℕ) : ℤ)
      - 12 * cb_int
      - 2 * ((harmListKevShift 0 w_kron w_kron harmP + harmListKevShift w_kron 0 w_kron harmP + harmListKevShift w_kron w_kron 0 harmP)
        + (harmListKevShift 0 (w_kron * D_kron) (w_kron * D_kron) harmP + harmListKevShift (w_kron * D_kron) 0 (w_kron * D_kron) harmP + harmListKevShift (w_kron * D_kron) (w_kron * D_kron) 0 harmP)
        + (harmListKevShift 0 w_kron w_kron harmR + harmListKevShift w_kron 0 w_kron harmR + harmListKevShift w_kron w_kron 0 harmR)
        + (harmListKevShift 0 (w_kron * D_kron) (w_kron * D_kron) harmR + harmListKevShift (w_kron * D_kron) 0 (w_kron * D_kron) harmR + harmListKevShift (w_kron * D_kron) (w_kron * D_kron) 0 harmR))
      - 24 * harmListKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) harmP
      - 24 * (harmListKevShift w_kron (w_kron * D_kron * D_kron) (w_kron * D_kron) harmR
        + harmListKevShift (w_kron * D_kron) (w_kron * D_kron * D_kron) w_kron harmR) : ℤ) : ℝ)) =
      (((sosB_sym.foldl (fun a b => a + cholPlainKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) b) 0
      + sosB_asym.foldl (fun a b => a + cholPlainKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) b
        + cholPlainKevShift (w_kron * D_kron) w_kron (w_kron * D_kron * D_kron) b) 0
      + kev3Shift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) resB_int : ℤ) : ℝ)) := by
      exact_mod_cast hk
    push_cast at hcast
    rw [cast_pevalZ, cast_pevalZ, cast_pevalZ, cast_pevalZ, cast_pevalZ,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_foldl_plain, cast_foldl_plain2, cast_kev3Shift] at hcast
    push_cast at hcast
    simp only [nat_shiftLeft_one_cast_real, pow_zero] at hcast
    dsimp only [f, sosB_ev, gP_int_ev, gR_int_ev]
    linarith
  exact eq_zero_of_kev3_zero (da := 11) (db := 11) (dc := 11) (D := D_kron) (w := w_kron)
    (by decide) (by decide) (by decide) (by decide) hrep_f l1_ok.2.1 hval u v t

private lemma id_lamG (u v t : ℝ) :
    252 * (peval hC_int u - 2 * peval psiCb_int u + peval hC_int v - 2 * peval psiCb_int v
        + peval hC_int t - 2 * peval psiCb_int t)
      - 36 * (cg_int : ℝ)
      - 504 * (gR_int_ev u + gR_int_ev v + gR_int_ev t)
      - 2520 * (harmListEv harmR u v t + harmListEv harmR u t v + harmListEv harmR v t u) =
    sosG_ev u v t + ev3 resG_int u v t := by
  let f : ℝ → ℝ → ℝ → ℝ := fun u v t =>
    (252 * (peval hC_int u - 2 * peval psiCb_int u + peval hC_int v - 2 * peval psiCb_int v
        + peval hC_int t - 2 * peval psiCb_int t)
      - 36 * (cg_int : ℝ)
      - 504 * (gR_int_ev u + gR_int_ev v + gR_int_ev t)
      - 2520 * (harmListEv harmR u v t + harmListEv harmR u t v + harmListEv harmR v t u))
    - (sosG_ev u v t + ev3 resG_int u v t)
  suffices h0 : f u v t = 0 by dsimp only [f] at h0; linarith
  have hdG := sos_exact_deg_ok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hC1 : HasPolyRep3 11 11 11 (l1List hC_int + 2 * l1List psiCb_int) (fun u _ _ => peval hC_int u - 2 * peval psiCb_int u) := by
    have ha := (HasPolyRep3.of_peval_u hC_int).widen (da' := 11) (db' := 11) (dc' := 11) (by decide) (by omega) (by omega) (le_refl _)
    have hb : HasPolyRep3 11 11 11 (2 * l1List psiCb_int) (fun u _ _ => 2 * peval psiCb_int u) := by
      simpa [Int.natAbs_natCast] using ((HasPolyRep3.of_peval_u psiCb_int).smul_int 2).widen
        (da' := 11) (db' := 11) (dc' := 11) (by decide) (by omega) (by omega) (le_refl _)
    exact ha.sub hb
  have hC3 : HasPolyRep3 11 11 11
      (252 * (l1List hC_int + 2 * l1List psiCb_int + l1List hC_int + 2 * l1List psiCb_int + l1List hC_int + 2 * l1List psiCb_int))
      (fun u v t => 252 * (peval hC_int u - 2 * peval psiCb_int u + peval hC_int v - 2 * peval psiCb_int v
        + peval hC_int t - 2 * peval psiCb_int t)) := by
    have h := (hC1.add hC1.perm_vut).add hC1.perm_tuv
    refine ((h.smul_int 252).widen (le_refl _) (le_refl _) (le_refl _) (by simp; omega)).congr fun u v t => by ring
  have hcg : HasPolyRep3 11 11 11 (36 * cg_int.natAbs) (fun _ _ _ => 36 * (cg_int : ℝ)) := by
    have h := (HasPolyRep3.const (36 * cg_int)).widen (da' := 11) (db' := 11) (dc' := 11)
      (by omega) (by omega) (by omega) (by rw [Int.natAbs_mul])
    exact h.congr fun _ _ _ => by push_cast; ring
  have hgR3 : HasPolyRep3 11 11 11
      (504 * (3 * harmListL1 harmR + 3 * harmListL1 harmR + 3 * harmListL1 harmR))
      (fun u v t => 504 * (gR_int_ev u + gR_int_ev v + gR_int_ev t)) := by
    have h := (gR_rep_u.add gR_rep_u.perm_vut).add gR_rep_u.perm_tuv
    simpa [Int.natAbs_natCast] using h.smul_int 504
  have hsR3 : HasPolyRep3 11 11 11 (2520 * (3 * harmListL1 harmR))
      (fun u v t => 2520 * (harmListEv harmR u v t + harmListEv harmR u t v + harmListEv harmR v t u)) := by
    have h1 := harmR_rep.widen (da' := 11) (db' := 11) (dc' := 11) (by omega) (by omega) (by omega) (le_refl _)
    have h2 := h1.perm_utv
    have h3 := h1.perm_vtu
    have h123 := ((h1.add h2).add h3).widen (L' := 3 * harmListL1 harmR) (le_refl _) (le_refl _) (le_refl _) (by omega)
    simpa [Int.natAbs_natCast] using h123.smul_int 2520
  have hrep_p : HasPolyRep3 11 11 11 (sosG_s3_plain.foldl (fun a b => a + cholPlainL1 b) 0)
      (fun u v t => (sosG_s3_plain.map fun b => cholPlainEv b u v t).sum) := by
    have b1 := HasPolyRep3.of_plain_deg hdG.1 (by omega)
    have b2 := HasPolyRep3.of_plain_deg hdG.2.1 (by omega)
    have b3 := HasPolyRep3.of_plain_deg hdG.2.2.1 (by omega)
    have b4 := HasPolyRep3.of_plain_deg hdG.2.2.2.1 (by omega)
    have hall := ((b1.add b2).add b3).add b4
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by simp [sosG_s3_plain]) |>.congr fun u v t => ?_
    simp [sosG_s3_plain]; ring
  have hrep_std : HasPolyRep3 11 11 11 (sosG_s3_std.foldl (fun a b => a + cholStdL1 b) 0)
      (fun u v t => (sosG_s3_std.map fun b => cholStdEv b u v t).sum) := by
    have b1 := HasPolyRep3.of_std_deg hdG.2.2.2.2.1 (by omega)
    have b2 := HasPolyRep3.of_std_deg hdG.2.2.2.2.2.1 (by omega)
    refine (b1.add b2).widen (le_refl _) (le_refl _) (le_refl _) (by simp [sosG_s3_std]) |>.congr fun u v t => ?_
    simp [sosG_s3_std]
  have hrep_s2 : HasPolyRep3 11 11 11 (3 * sosG_s2.foldl (fun a b => a + cholPlainL1 b) 0)
      (fun u v t => (sosG_s2.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum) := by
    have b1 := HasPolyRep3.of_plain_deg hdG.2.2.2.2.2.2.1 (by omega)
    have b2 := HasPolyRep3.of_plain_deg hdG.2.2.2.2.2.2.2.1 (by omega)
    have b3 := HasPolyRep3.of_plain_deg hdG.2.2.2.2.2.2.2.2.1 (by omega)
    have b4 := HasPolyRep3.of_plain_deg hdG.2.2.2.2.2.2.2.2.2 (by omega)
    have c1 := (b1.add b1.perm_vut).add b1.perm_tuv
    have c2 := (b2.add b2.perm_vut).add b2.perm_tuv
    have c3 := (b3.add b3.perm_vut).add b3.perm_tuv
    have c4 := (b4.add b4.perm_vut).add b4.perm_tuv
    have hall := ((c1.add c2).add c3).add c4
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by simp [sosG_s2]; omega) |>.congr fun u v t => ?_
    simp [sosG_s2]; ring
  have hrep_res : HasPolyRep3 11 11 11 (l1Poly3 resG_int) (ev3 resG_int) :=
    HasPolyRep3.of_poly3 resG_int res_deg_ok.2.2
  have hrep_f : HasPolyRep3 11 11 11 l1G f := by
    have hall := (((hC3.sub hcg).sub hgR3).sub hsR3).sub (((hrep_p.add hrep_std).add hrep_s2).add hrep_res)
    exact hall.widen (le_refl _) (le_refl _) (le_refl _) (by unfold l1G; omega) |>.congr fun a b c => by
      dsimp only [f, sosG_ev]
  have hval : f ((2 : ℝ) ^ w_kron) ((2 : ℝ) ^ (w_kron * D_kron)) ((2 : ℝ) ^ (w_kron * D_kron * D_kron)) = 0 := by
    have hk := kronG_ok
    unfold checkKronG at hk
    simp only [beq_iff_eq] at hk
    have hcast : (((252 * (pevalZ hC_int ((Nat.shiftLeft 1 w_kron : ℕ) : ℤ)
      - 2 * pevalZ psiCb_int ((Nat.shiftLeft 1 w_kron : ℕ) : ℤ)
      + pevalZ hC_int ((Nat.shiftLeft 1 (w_kron * D_kron) : ℕ) : ℤ)
      - 2 * pevalZ psiCb_int ((Nat.shiftLeft 1 (w_kron * D_kron) : ℕ) : ℤ)
      + pevalZ hC_int ((Nat.shiftLeft 1 (w_kron * D_kron * D_kron) : ℕ) : ℤ)
      - 2 * pevalZ psiCb_int ((Nat.shiftLeft 1 (w_kron * D_kron * D_kron) : ℕ) : ℤ))
      - 36 * cg_int
      - 504 * ((harmListKevShift 0 w_kron w_kron harmR + harmListKevShift w_kron 0 w_kron harmR + harmListKevShift w_kron w_kron 0 harmR)
        + (harmListKevShift 0 (w_kron * D_kron) (w_kron * D_kron) harmR + harmListKevShift (w_kron * D_kron) 0 (w_kron * D_kron) harmR + harmListKevShift (w_kron * D_kron) (w_kron * D_kron) 0 harmR)
        + (harmListKevShift 0 (w_kron * D_kron * D_kron) (w_kron * D_kron * D_kron) harmR + harmListKevShift (w_kron * D_kron * D_kron) 0 (w_kron * D_kron * D_kron) harmR + harmListKevShift (w_kron * D_kron * D_kron) (w_kron * D_kron * D_kron) 0 harmR))
      - 2520 * (harmListKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) harmR
        + harmListKevShift w_kron (w_kron * D_kron * D_kron) (w_kron * D_kron) harmR
        + harmListKevShift (w_kron * D_kron) (w_kron * D_kron * D_kron) w_kron harmR) : ℤ) : ℝ)) =
      (((sosG_s3_plain.foldl (fun a b => a + cholPlainKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) b) 0
      + sosG_s3_std.foldl (fun a b => a + cholStdKev w_kron D_kron b) 0
      + sosG_s2.foldl (fun a b => a + cholPlainKevShift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) b
        + cholPlainKevShift (w_kron * D_kron) w_kron (w_kron * D_kron * D_kron) b
        + cholPlainKevShift (w_kron * D_kron * D_kron) w_kron (w_kron * D_kron) b) 0
      + kev3Shift w_kron (w_kron * D_kron) (w_kron * D_kron * D_kron) resG_int : ℤ) : ℝ)) := by
      exact_mod_cast hk
    push_cast at hcast
    rw [cast_pevalZ, cast_pevalZ, cast_pevalZ, cast_pevalZ, cast_pevalZ, cast_pevalZ,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_foldl_plain, cast_foldl_std, cast_foldl_plain3, cast_kev3Shift] at hcast
    push_cast at hcast
    simp only [nat_shiftLeft_one_cast_real, pow_zero] at hcast
    dsimp only [f, sosG_ev, gR_int_ev]
    linarith
  exact eq_zero_of_kev3_zero (da := 11) (db := 11) (dc := 11) (D := D_kron) (w := w_kron)
    (by decide) (by decide) (by decide) (by decide) hrep_f l1_ok.2.2 hval u v t

/-! ## Section 3: Nonnegativity of SOS Sums & 1D Minorant Inequalities -/

private lemma sosA_ev_nonneg {u v t : ℝ} (hu_lo : -1 ≤ u) (hu_hi : u ≤ -9 / 10)
    (hv_lo : -1 ≤ v) (hv_hi : v ≤ 1) (ht_lo : -1 ≤ t) (ht_hi : t ≤ 1) (hd : 0 ≤ detG u v t) :
    0 ≤ sosA_ev u v t := by
  have h1 : 0 ≤ ev3 blk_SOS_A_1_even.mp u v t := by simp [blk_SOS_A_1_even, ev3]
  have h2 : 0 ≤ ev3 blk_SOS_A_1_odd.mp u v t := by simp [blk_SOS_A_1_odd, ev3]
  have h3 : 0 ≤ ev3 blk_SOS_A_ulo_even.mp u v t := by simp [blk_SOS_A_ulo_even, ev3]; linarith
  have h4 : 0 ≤ ev3 blk_SOS_A_ulo_odd.mp u v t := by simp [blk_SOS_A_ulo_odd, ev3]; linarith
  have h5 : 0 ≤ ev3 blk_SOS_A_hiu_even.mp u v t := by simp [blk_SOS_A_hiu_even, ev3]; linarith
  have h6 : 0 ≤ ev3 blk_SOS_A_hiu_odd.mp u v t := by simp [blk_SOS_A_hiu_odd, ev3]; linarith
  have h7 : 0 ≤ ev3 blk_SOS_A_detG_even.mp u v t := by simp [blk_SOS_A_detG_even, ev3]; unfold detG at hd; linarith
  have h8 : 0 ≤ ev3 blk_SOS_A_detG_odd.mp u v t := by simp [blk_SOS_A_detG_odd, ev3]; unfold detG at hd; linarith
  have h9a : 0 ≤ ev3 blk_SOS_A_vlo.mp u v t := by simp [blk_SOS_A_vlo, ev3]; linarith
  have h9b : 0 ≤ ev3 blk_SOS_A_vlo.mp u t v := by simp [blk_SOS_A_vlo, ev3]; linarith
  have h10a : 0 ≤ ev3 blk_SOS_A_vhi.mp u v t := by simp [blk_SOS_A_vhi, ev3]; linarith
  have h10b : 0 ≤ ev3 blk_SOS_A_vhi.mp u t v := by simp [blk_SOS_A_vhi, ev3]; linarith
  unfold sosA_ev
  simp only [sosA_sym, sosA_asym, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  linarith [cholPlainEv_nonneg blk_SOS_A_1_even h1, cholPlainEv_nonneg blk_SOS_A_1_odd h2,
    cholPlainEv_nonneg blk_SOS_A_ulo_even h3, cholPlainEv_nonneg blk_SOS_A_ulo_odd h4,
    cholPlainEv_nonneg blk_SOS_A_hiu_even h5, cholPlainEv_nonneg blk_SOS_A_hiu_odd h6,
    cholPlainEv_nonneg blk_SOS_A_detG_even h7, cholPlainEv_nonneg blk_SOS_A_detG_odd h8,
    cholPlainEv_nonneg blk_SOS_A_vlo h9a, cholPlainEv_nonneg blk_SOS_A_vlo h9b,
    cholPlainEv_nonneg blk_SOS_A_vhi h10a, cholPlainEv_nonneg blk_SOS_A_vhi h10b]

private lemma sosB_ev_nonneg {u v t : ℝ} (hu_lo : -1 ≤ u) (hu_hi : u ≤ 1)
    (hv_lo : -1 ≤ v) (hv_hi : v ≤ 1) (ht_lo : -1 ≤ t) (ht_hi : t ≤ 1) (hd : 0 ≤ detG u v t) :
    0 ≤ sosB_ev u v t := by
  have h1 : 0 ≤ ev3 blk_SOS_B_1_even.mp u v t := by simp [blk_SOS_B_1_even, ev3]
  have h2 : 0 ≤ ev3 blk_SOS_B_1_odd.mp u v t := by simp [blk_SOS_B_1_odd, ev3]
  have h3 : 0 ≤ ev3 blk_SOS_B_tlo_even.mp u v t := by simp [blk_SOS_B_tlo_even, ev3]; linarith
  have h4 : 0 ≤ ev3 blk_SOS_B_tlo_odd.mp u v t := by simp [blk_SOS_B_tlo_odd, ev3]; linarith
  have h5 : 0 ≤ ev3 blk_SOS_B_thi_even.mp u v t := by simp [blk_SOS_B_thi_even, ev3]; linarith
  have h6 : 0 ≤ ev3 blk_SOS_B_thi_odd.mp u v t := by simp [blk_SOS_B_thi_odd, ev3]; linarith
  have h7 : 0 ≤ ev3 blk_SOS_B_detG_even.mp u v t := by simp [blk_SOS_B_detG_even, ev3]; unfold detG at hd; linarith
  have h8 : 0 ≤ ev3 blk_SOS_B_detG_odd.mp u v t := by simp [blk_SOS_B_detG_odd, ev3]; unfold detG at hd; linarith
  have h9a : 0 ≤ ev3 blk_SOS_B_ulo.mp u v t := by simp [blk_SOS_B_ulo, ev3]; linarith
  have h9b : 0 ≤ ev3 blk_SOS_B_ulo.mp v u t := by simp [blk_SOS_B_ulo, ev3]; linarith
  have h10a : 0 ≤ ev3 blk_SOS_B_uhi.mp u v t := by simp [blk_SOS_B_uhi, ev3]; linarith
  have h10b : 0 ≤ ev3 blk_SOS_B_uhi.mp v u t := by simp [blk_SOS_B_uhi, ev3]; linarith
  unfold sosB_ev
  simp only [sosB_sym, sosB_asym, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  linarith [cholPlainEv_nonneg blk_SOS_B_1_even h1, cholPlainEv_nonneg blk_SOS_B_1_odd h2,
    cholPlainEv_nonneg blk_SOS_B_tlo_even h3, cholPlainEv_nonneg blk_SOS_B_tlo_odd h4,
    cholPlainEv_nonneg blk_SOS_B_thi_even h5, cholPlainEv_nonneg blk_SOS_B_thi_odd h6,
    cholPlainEv_nonneg blk_SOS_B_detG_even h7, cholPlainEv_nonneg blk_SOS_B_detG_odd h8,
    cholPlainEv_nonneg blk_SOS_B_ulo h9a, cholPlainEv_nonneg blk_SOS_B_ulo h9b,
    cholPlainEv_nonneg blk_SOS_B_uhi h10a, cholPlainEv_nonneg blk_SOS_B_uhi h10b]

private lemma sosG_ev_nonneg {u v t : ℝ} (hu_lo : -1 ≤ u) (hu_hi : u ≤ 1)
    (hv_lo : -1 ≤ v) (hv_hi : v ≤ 1) (ht_lo : -1 ≤ t) (ht_hi : t ≤ 1) (hd : 0 ≤ detG u v t) :
    0 ≤ sosG_ev u v t := by
  have h1 : 0 ≤ ev3 blk_SOS_G_1_triv.mp u v t := by simp [blk_SOS_G_1_triv, ev3]
  have h2 : 0 ≤ ev3 blk_SOS_G_1_sign.mp u v t := by simp [blk_SOS_G_1_sign, ev3]
  have h3 : 0 ≤ ev3 blk_SOS_G_detG_triv.mp u v t := by simp [blk_SOS_G_detG_triv, ev3]; unfold detG at hd; linarith
  have h4 : 0 ≤ ev3 blk_SOS_G_detG_sign.mp u v t := by simp [blk_SOS_G_detG_sign, ev3]; unfold detG at hd; linarith
  have h5 : 0 ≤ ev3 blk_SOS_G_1_std.mp u v t := by simp [blk_SOS_G_1_std, ev3]
  have h6 : 0 ≤ ev3 blk_SOS_G_detG_std.mp u v t := by simp [blk_SOS_G_detG_std, ev3]; unfold detG at hd; linarith
  have h7a : 0 ≤ ev3 blk_SOS_G_ulo_even.mp u v t := by simp [blk_SOS_G_ulo_even, ev3]; linarith
  have h7b : 0 ≤ ev3 blk_SOS_G_ulo_even.mp v u t := by simp [blk_SOS_G_ulo_even, ev3]; linarith
  have h7c : 0 ≤ ev3 blk_SOS_G_ulo_even.mp t u v := by simp [blk_SOS_G_ulo_even, ev3]; linarith
  have h8a : 0 ≤ ev3 blk_SOS_G_ulo_odd.mp u v t := by simp [blk_SOS_G_ulo_odd, ev3]; linarith
  have h8b : 0 ≤ ev3 blk_SOS_G_ulo_odd.mp v u t := by simp [blk_SOS_G_ulo_odd, ev3]; linarith
  have h8c : 0 ≤ ev3 blk_SOS_G_ulo_odd.mp t u v := by simp [blk_SOS_G_ulo_odd, ev3]; linarith
  have h9a : 0 ≤ ev3 blk_SOS_G_uhi_even.mp u v t := by simp [blk_SOS_G_uhi_even, ev3]; linarith
  have h9b : 0 ≤ ev3 blk_SOS_G_uhi_even.mp v u t := by simp [blk_SOS_G_uhi_even, ev3]; linarith
  have h9c : 0 ≤ ev3 blk_SOS_G_uhi_even.mp t u v := by simp [blk_SOS_G_uhi_even, ev3]; linarith
  have h10a : 0 ≤ ev3 blk_SOS_G_uhi_odd.mp u v t := by simp [blk_SOS_G_uhi_odd, ev3]; linarith
  have h10b : 0 ≤ ev3 blk_SOS_G_uhi_odd.mp v u t := by simp [blk_SOS_G_uhi_odd, ev3]; linarith
  have h10c : 0 ≤ ev3 blk_SOS_G_uhi_odd.mp t u v := by simp [blk_SOS_G_uhi_odd, ev3]; linarith
  unfold sosG_ev
  simp only [sosG_s3_plain, sosG_s3_std, sosG_s2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  linarith [cholPlainEv_nonneg blk_SOS_G_1_triv h1, cholPlainEv_nonneg blk_SOS_G_1_sign h2,
    cholPlainEv_nonneg blk_SOS_G_detG_triv h3, cholPlainEv_nonneg blk_SOS_G_detG_sign h4,
    cholStdEv_nonneg blk_SOS_G_1_std h5, cholStdEv_nonneg blk_SOS_G_detG_std h6,
    cholPlainEv_nonneg blk_SOS_G_ulo_even h7a, cholPlainEv_nonneg blk_SOS_G_ulo_even h7b,
    cholPlainEv_nonneg blk_SOS_G_ulo_even h7c, cholPlainEv_nonneg blk_SOS_G_ulo_odd h8a,
    cholPlainEv_nonneg blk_SOS_G_ulo_odd h8b, cholPlainEv_nonneg blk_SOS_G_ulo_odd h8c,
    cholPlainEv_nonneg blk_SOS_G_uhi_even h9a, cholPlainEv_nonneg blk_SOS_G_uhi_even h9b,
    cholPlainEv_nonneg blk_SOS_G_uhi_even h9c, cholPlainEv_nonneg blk_SOS_G_uhi_odd h10a,
    cholPlainEv_nonneg blk_SOS_G_uhi_odd h10b, cholPlainEv_nonneg blk_SOS_G_uhi_odd h10c]

private lemma S2_pos : (0 : ℝ) < (S2 : ℝ) := by norm_num [S2]

private lemma minorA_bound {t : ℝ} (ht_lo : -1 ≤ t) (ht_hi : t ≤ -9 / 10) :
    peval hA_int t / (S2 : ℝ) ≤ (1 + (l1List res_yA_int : ℝ) / (20 * (S2 : ℝ))) * phi t := by
  set y : ℝ := Real.sqrt ((1 - t) / 2)
  have hy_sq : y ^ 2 = (1 - t) / 2 := Real.sq_sqrt (by linarith)
  have hy_pos : 0 < y := Real.sqrt_pos.mpr (by linarith)
  have hy_le1 : y ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have h1m2y : 1 - 2 * y ^ 2 = t := by linarith
  have hphi : phi t = (2 * y)⁻¹ := by
    unfold phi
    have h2 : 2 - 2 * t = (2 * y) ^ 2 := by linarith
    rw [h2, Real.sqrt_sq (by linarith)]
  have hid := peval_eq_zero_of_all _ minorA_ok y
  simp only [peval_padd, peval_pscale, peval_pmul, peval_pneg, peval_chol1DPoly, peval_twoYH] at hid
  rw [h1m2y] at hid
  have h01 : peval [0, 20] y = 20 * y := by simp only [peval]; push_cast; ring
  have h02 : peval [-19, 0, 20] y = 20 * y ^ 2 - 19 := by simp only [peval]; push_cast; ring
  have h03 : peval [20, 0, -20] y = 20 - 20 * y ^ 2 := by simp only [peval]; push_cast; ring
  have h04 : peval [0, -19, 0, 20] y = y * (20 * y ^ 2 - 19) := by simp only [peval]; push_cast; ring
  have h05 : peval [0, 20, 0, -20] y = y * (20 - 20 * y ^ 2) := by simp only [peval]; push_cast; ring
  have hS : peval [-S2] y = -(S2 : ℝ) := by simp only [peval]; push_cast; ring
  rw [h01, h02, h03, h04, h05, hS] at hid
  have hnn0 : 0 ≤ chol1DEv tauA_0 y := chol1DEv_nonneg _ _
  have hnn1 : 0 ≤ 20 * y * chol1DEv tauA_1 y := mul_nonneg (by linarith) (chol1DEv_nonneg _ _)
  have hnn2 : 0 ≤ (20 * y ^ 2 - 19) * chol1DEv tauA_2 y := mul_nonneg (by linarith) (chol1DEv_nonneg _ _)
  have hnn3 : 0 ≤ (20 - 20 * y ^ 2) * chol1DEv tauA_3 y := mul_nonneg (by linarith) (chol1DEv_nonneg _ _)
  have hnn4 : 0 ≤ y * (20 * y ^ 2 - 19) * chol1DEv tauA_4 y :=
    mul_nonneg (mul_nonneg hy_pos.le (by linarith)) (chol1DEv_nonneg _ _)
  have hnn5 : 0 ≤ y * (20 - 20 * y ^ 2) * chol1DEv tauA_5 y :=
    mul_nonneg (mul_nonneg hy_pos.le (by linarith)) (chol1DEv_nonneg _ _)
  have hres : peval res_yA_int y ≤ (l1List res_yA_int : ℝ) :=
    (le_abs_self _).trans (abs_peval_le_l1List res_yA_int hy_pos.le hy_le1)
  have hkey : 20 * (2 * y * peval hA_int t - (S2 : ℝ)) ≤ (l1List res_yA_int : ℝ) := by
    push_cast at hid; linarith
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  rw [hphi]
  have h2y_pos : (0 : ℝ) < 2 * y := by linarith
  rw [div_le_iff₀ hS2]
  have hmul : peval hA_int t * (2 * y) ≤ (1 + (l1List res_yA_int : ℝ) / (20 * (S2 : ℝ))) * (S2 : ℝ) := by
    have h20 : (0 : ℝ) < 20 * (S2 : ℝ) := by linarith
    have hdiv : (l1List res_yA_int : ℝ) / (20 * (S2 : ℝ)) * (S2 : ℝ) = (l1List res_yA_int : ℝ) / 20 := by
      field_simp
    linarith
  have := (le_mul_inv_iff₀ h2y_pos).mpr hmul
  linarith

private lemma minorBC_bound (h_int res_int : List ℤ) (s0 s1 s2 s3 : List (List ℤ))
    (hok : (padd (padd (twoYH h_int) [-S2])
      (padd (chol1DPoly s0)
      (padd (pmul [0, 1] (chol1DPoly s1))
      (padd (pmul [1, 0, -1] (chol1DPoly s2))
      (padd (pmul [0, 1, 0, -1] (chol1DPoly s3)) (pneg res_int)))))).all (· == 0) = true)
    {t : ℝ} (ht_lo : -1 ≤ t) (ht_lt : t < 1) :
    peval h_int t / (S2 : ℝ) ≤ (1 + (l1List res_int : ℝ) / (S2 : ℝ)) * phi t := by
  set y : ℝ := Real.sqrt ((1 - t) / 2)
  have hy_sq : y ^ 2 = (1 - t) / 2 := Real.sq_sqrt (by linarith)
  have hy_pos : 0 < y := Real.sqrt_pos.mpr (by linarith)
  have hy_le1 : y ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have h1m2y : 1 - 2 * y ^ 2 = t := by linarith
  have hphi : phi t = (2 * y)⁻¹ := by
    unfold phi
    have h2 : 2 - 2 * t = (2 * y) ^ 2 := by linarith
    rw [h2, Real.sqrt_sq (by linarith)]
  have hid := peval_eq_zero_of_all _ hok y
  simp only [peval_padd, peval_pmul, peval_pneg, peval_chol1DPoly, peval_twoYH] at hid
  rw [h1m2y] at hid
  have h01 : peval [0, 1] y = y := by simp only [peval]; push_cast; ring
  have h02 : peval [1, 0, -1] y = 1 - y ^ 2 := by simp only [peval]; push_cast; ring
  have h03 : peval [0, 1, 0, -1] y = y * (1 - y ^ 2) := by simp only [peval]; push_cast; ring
  have hS : peval [-S2] y = -(S2 : ℝ) := by simp only [peval]; push_cast; ring
  rw [h01, h02, h03, hS] at hid
  have hnn0 : 0 ≤ chol1DEv s0 y := chol1DEv_nonneg _ _
  have hnn1 : 0 ≤ y * chol1DEv s1 y := mul_nonneg hy_pos.le (chol1DEv_nonneg _ _)
  have hnn2 : 0 ≤ (1 - y ^ 2) * chol1DEv s2 y := mul_nonneg (by linarith) (chol1DEv_nonneg _ _)
  have hnn3 : 0 ≤ y * (1 - y ^ 2) * chol1DEv s3 y :=
    mul_nonneg (mul_nonneg hy_pos.le (by linarith)) (chol1DEv_nonneg _ _)
  have hres : peval res_int y ≤ (l1List res_int : ℝ) :=
    (le_abs_self _).trans (abs_peval_le_l1List res_int hy_pos.le hy_le1)
  have hkey : 2 * y * peval h_int t - (S2 : ℝ) ≤ (l1List res_int : ℝ) := by linarith
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  rw [hphi, div_le_iff₀ hS2]
  have h2y_pos : (0 : ℝ) < 2 * y := by linarith
  have hmul : peval h_int t * (2 * y) ≤ (1 + (l1List res_int : ℝ) / (S2 : ℝ)) * (S2 : ℝ) := by
    have hdiv : (l1List res_int : ℝ) / (S2 : ℝ) * (S2 : ℝ) = (l1List res_int : ℝ) := by field_simp
    linarith
  have := (le_mul_inv_iff₀ h2y_pos).mpr hmul
  linarith

/-! ## Section 4: Main Theorem `slab_exclusion` -/

/-- **Main Stage B Slab Exclusion Theorem (`[-1, -9/10]`)**:
Every 9-point configuration `x` on the unit sphere `S²` with at least one pair satisfying
`⟪x i, x j⟫ ≤ -9/10` has Coulomb energy strictly greater than `E_ttp_hi`. -/
theorem slab_exclusion (x : Fin 9 → R3) (hu : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x)
    (hpair : ∃ i j : Fin 9, i ≠ j ∧ ⟪x i, x j⟫ ≤ -9 / 10) :
    E_ttp_hi < coulombEnergy9 x := by
  obtain ⟨i₀, j₀, hne, hdot0⟩ := hpair
  obtain ⟨σ, hσ0, hσ1⟩ := exists_swap_to_01 i₀ j₀ hne
  let z : Fin 9 → R3 := fun i => x (σ i)
  have hzu : ∀ i, ‖z i‖ = 1 := fun i => hu (σ i)
  have hzinj : Function.Injective z := hinj.comp σ.injective
  have hEz : coulombEnergy9 z = coulombEnergy9 x := coulombEnergy9_perm x σ
  rw [← hEz]
  let t : Fin 9 → Fin 9 → ℝ := fun i j => ⟪z i, z j⟫
  have ht_diag : ∀ i, t i i = 1 := fun i => by
    dsimp only [t]; rw [real_inner_self_eq_norm_sq, hzu i]; norm_num
  have ht_sym : ∀ i j, t i j = t j i := fun i j => real_inner_comm (z j) (z i)
  have ht_lo : ∀ i j, -1 ≤ t i j := fun i j => neg_one_le_inner_unit (hzu i) (hzu j)
  have ht_hi : ∀ i j, t i j ≤ 1 := fun i j => inner_le_one_unit (hzu i) (hzu j)
  have ht_lt : ∀ i j, i ≠ j → t i j < 1 := fun i j hij =>
    inner_lt_one_of_ne_unit (hzu i) (hzu j) (fun h => hij (hzinj h))
  have ht_abs : ∀ i j, |t i j| ≤ 1 := fun i j => abs_le.mpr ⟨ht_lo i j, ht_hi i j⟩
  have ht01 : t 0 1 ≤ -9 / 10 := by dsimp only [t, z]; rw [hσ0, hσ1]; exact hdot0
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  -- Scaled real functions for `slab_assembly_9`
  let hA : ℝ → ℝ := fun u => peval hA_int u / (S2 : ℝ)
  let hB : ℝ → ℝ := fun u => peval hB_int u / (S2 : ℝ)
  let hC : ℝ → ℝ := fun u => peval hC_int u / (S2 : ℝ)
  let psiBa : ℝ → ℝ := fun u => peval psiBa_int u / (S2 : ℝ)
  let psiCb : ℝ → ℝ := fun u => peval psiCb_int u / (S2 : ℝ)
  let sP : ℝ → ℝ → ℝ → ℝ := fun u v w => harmListEv harmP u v w / (S2 : ℝ)
  let sR : ℝ → ℝ → ℝ → ℝ := fun u v w => harmListEv harmR u v w / (S2 : ℝ)
  have hnorm : (e_int : ℝ) / (S2 : ℝ) + 2 * sP 1 1 1 + 7 * sR 1 1 1 =
      7 * ((ca_int : ℝ) / (S2 : ℝ)) + 42 * ((cb_int : ℝ) / (S2 : ℝ)) + 35 * ((cg_int : ℝ) / (35 * (S2 : ℝ))) := by
    have h0 : ((e_int + 2 * harmListKevShift 0 0 0 harmP + 7 * harmListKevShift 0 0 0 harmR : ℤ) : ℝ) =
        ((7 * ca_int + 42 * cb_int + cg_int : ℤ) : ℝ) := by exact_mod_cast norm_ok
    push_cast at h0
    rw [cast_harmListKevShift, cast_harmListKevShift] at h0
    simp only [pow_zero] at h0
    dsimp only [sP, sR]
    field_simp
    linarith
  have hasm := slab_assembly_9 t ht_diag ht_sym hA hB hC psiBa psiCb
    ((e_int : ℝ) / (S2 : ℝ)) ((ca_int : ℝ) / (S2 : ℝ)) ((cb_int : ℝ) / (S2 : ℝ)) ((cg_int : ℝ) / (35 * (S2 : ℝ)))
    sP sR (fun u v w => by dsimp only [sP]; rw [harmListEv_symm])
    (fun u v w => by dsimp only [sR]; rw [harmListEv_symm]) hnorm
  -- Pointwise lower bounds on lam_A, lam_B, lam_G
  have hlamA : ∀ r ∈ ringSet,
      -(l1Poly3 resA_int : ℝ) / (280 * (S2 : ℝ)) ≤
        hA (t 0 1) / 7 + psiBa (t 0 r) + psiBa (t 1 r) - (ca_int : ℝ) / (S2 : ℝ)
        - 2 * (sP 1 (t 0 1) (t 0 1) + sP (t 0 1) 1 (t 0 1) + sP (t 0 1) (t 0 1) 1) / 7
        - 2 * (sP (t 0 1) (t 0 r) (t 1 r) + sP (t 0 1) (t 1 r) (t 0 r))
        - 2 * sR (t 0 r) (t 1 r) (t 0 1) := by
    intro r _
    have hid := id_lamA (t 0 1) (t 0 r) (t 1 r)
    have hsos := sosA_ev_nonneg (ht_lo 0 1) ht01 (ht_lo 0 r) (ht_hi 0 r) (ht_lo 1 r) (ht_hi 1 r)
      (detG_nonneg_of_unit (hzu 0) (hzu 1) (hzu r))
    have hres := (abs_le.mp (abs_ev3_le_l1Poly3 resA_int (ht_abs 0 1) (ht_abs 0 r) (ht_abs 1 r))).1
    have hge : -(l1Poly3 resA_int : ℝ) ≤
        40 * peval hA_int (t 0 1) + 280 * (peval psiBa_int (t 0 r) + peval psiBa_int (t 1 r)) - 280 * (ca_int : ℝ)
        - 80 * gP_int_ev (t 0 1) - 560 * (harmListEv harmP (t 0 1) (t 0 r) (t 1 r) + harmListEv harmP (t 0 1) (t 1 r) (t 0 r))
        - 560 * harmListEv harmR (t 0 r) (t 1 r) (t 0 1) := by linarith
    have h280 : (0 : ℝ) < 280 * (S2 : ℝ) := by linarith
    have hdiv := div_le_div_of_nonneg_right hge h280.le
    refine le_trans hdiv (le_of_eq ?_)
    dsimp only [hA, psiBa, sP, sR, gP_int_ev]; field_simp; ring
  have hlamB : ∀ p ∈ poleSet, ∀ r1 ∈ ringSet, ∀ r2 ∈ ringSet.filter (r1 < ·),
      -(l1Poly3 resB_int : ℝ) / (12 * (S2 : ℝ)) ≤
        (hB (t p r1) - psiBa (t p r1) + hB (t p r2) - psiBa (t p r2)) / 6
        + psiCb (t r1 r2) - (cb_int : ℝ) / (S2 : ℝ)
        - ((sP 1 (t p r1) (t p r1) + sP (t p r1) 1 (t p r1) + sP (t p r1) (t p r1) 1)
          + (sP 1 (t p r2) (t p r2) + sP (t p r2) 1 (t p r2) + sP (t p r2) (t p r2) 1)
          + (sR 1 (t p r1) (t p r1) + sR (t p r1) 1 (t p r1) + sR (t p r1) (t p r1) 1)
          + (sR 1 (t p r2) (t p r2) + sR (t p r2) 1 (t p r2) + sR (t p r2) (t p r2) 1)) / 6
        - 2 * sP (t p r1) (t p r2) (t r1 r2)
        - 2 * (sR (t p r1) (t r1 r2) (t p r2) + sR (t p r2) (t r1 r2) (t p r1)) := by
    intro p _ r1 _ r2 _
    have hid := id_lamB (t p r1) (t p r2) (t r1 r2)
    have hsos := sosB_ev_nonneg (ht_lo p r1) (ht_hi p r1) (ht_lo p r2) (ht_hi p r2)
      (ht_lo r1 r2) (ht_hi r1 r2) (detG_nonneg_of_unit (hzu p) (hzu r1) (hzu r2))
    have hres := (abs_le.mp (abs_ev3_le_l1Poly3 resB_int (ht_abs p r1) (ht_abs p r2) (ht_abs r1 r2))).1
    have hge : -(l1Poly3 resB_int : ℝ) ≤
        2 * (peval hB_int (t p r1) - peval psiBa_int (t p r1) + peval hB_int (t p r2) - peval psiBa_int (t p r2))
        + 12 * peval psiCb_int (t r1 r2) - 12 * (cb_int : ℝ)
        - 2 * (gP_int_ev (t p r1) + gP_int_ev (t p r2) + gR_int_ev (t p r1) + gR_int_ev (t p r2))
        - 24 * harmListEv harmP (t p r1) (t p r2) (t r1 r2)
        - 24 * (harmListEv harmR (t p r1) (t r1 r2) (t p r2) + harmListEv harmR (t p r2) (t r1 r2) (t p r1)) := by
      linarith
    have h12 : (0 : ℝ) < 12 * (S2 : ℝ) := by linarith
    have hdiv := div_le_div_of_nonneg_right hge h12.le
    refine le_trans hdiv (le_of_eq ?_)
    dsimp only [hB, psiBa, psiCb, sP, sR, gP_int_ev, gR_int_ev]; field_simp; ring
  have hlamG : ∀ r1 ∈ ringSet, ∀ r2 ∈ ringSet.filter (r1 < ·), ∀ r3 ∈ ringSet.filter (r2 < ·),
      -(l1Poly3 resG_int : ℝ) / (1260 * (S2 : ℝ)) ≤
        (hC (t r1 r2) - 2 * psiCb (t r1 r2) + hC (t r1 r3) - 2 * psiCb (t r1 r3)
          + hC (t r2 r3) - 2 * psiCb (t r2 r3)) / 5 - (cg_int : ℝ) / (35 * (S2 : ℝ))
        - 2 * ((sR 1 (t r1 r2) (t r1 r2) + sR (t r1 r2) 1 (t r1 r2) + sR (t r1 r2) (t r1 r2) 1)
          + (sR 1 (t r1 r3) (t r1 r3) + sR (t r1 r3) 1 (t r1 r3) + sR (t r1 r3) (t r1 r3) 1)
          + (sR 1 (t r2 r3) (t r2 r3) + sR (t r2 r3) 1 (t r2 r3) + sR (t r2 r3) (t r2 r3) 1)) / 5
        - 2 * (sR (t r1 r2) (t r1 r3) (t r2 r3) + sR (t r1 r2) (t r2 r3) (t r1 r3)
          + sR (t r1 r3) (t r2 r3) (t r1 r2)) := by
    intro r1 _ r2 _ r3 _
    have hid := id_lamG (t r1 r2) (t r1 r3) (t r2 r3)
    have hsos := sosG_ev_nonneg (ht_lo r1 r2) (ht_hi r1 r2) (ht_lo r1 r3) (ht_hi r1 r3)
      (ht_lo r2 r3) (ht_hi r2 r3) (detG_nonneg_of_unit (hzu r1) (hzu r2) (hzu r3))
    have hres := (abs_le.mp (abs_ev3_le_l1Poly3 resG_int (ht_abs r1 r2) (ht_abs r1 r3) (ht_abs r2 r3))).1
    have hge : -(l1Poly3 resG_int : ℝ) ≤
        252 * (peval hC_int (t r1 r2) - 2 * peval psiCb_int (t r1 r2)
          + peval hC_int (t r1 r3) - 2 * peval psiCb_int (t r1 r3)
          + peval hC_int (t r2 r3) - 2 * peval psiCb_int (t r2 r3))
        - 36 * (cg_int : ℝ)
        - 504 * (gR_int_ev (t r1 r2) + gR_int_ev (t r1 r3) + gR_int_ev (t r2 r3))
        - 2520 * (harmListEv harmR (t r1 r2) (t r1 r3) (t r2 r3)
          + harmListEv harmR (t r1 r2) (t r2 r3) (t r1 r3)
          + harmListEv harmR (t r1 r3) (t r2 r3) (t r1 r2)) := by linarith
    have h1260 : (0 : ℝ) < 1260 * (S2 : ℝ) := by linarith
    have hdiv := div_le_div_of_nonneg_right hge h1260.le
    refine le_trans hdiv (le_of_eq ?_)
    dsimp only [hC, psiCb, sR, gR_int_ev]; field_simp; ring
  -- Sum the triple lower bounds
  have hSumA : 7 * (-(l1Poly3 resA_int : ℝ) / (280 * (S2 : ℝ))) ≤
      ∑ r ∈ ringSet,
        (hA (t 0 1) / 7 + psiBa (t 0 r) + psiBa (t 1 r) - (ca_int : ℝ) / (S2 : ℝ)
        - 2 * (sP 1 (t 0 1) (t 0 1) + sP (t 0 1) 1 (t 0 1) + sP (t 0 1) (t 0 1) 1) / 7
        - 2 * (sP (t 0 1) (t 0 r) (t 1 r) + sP (t 0 1) (t 1 r) (t 0 r))
        - 2 * sR (t 0 r) (t 1 r) (t 0 1)) := by
    have hc : ringSet.card = 7 := by decide
    calc 7 * (-(l1Poly3 resA_int : ℝ) / (280 * (S2 : ℝ)))
        = ∑ _r ∈ ringSet, (-(l1Poly3 resA_int : ℝ) / (280 * (S2 : ℝ))) := by
          rw [Finset.sum_const, hc, nsmul_eq_mul]; push_cast; rfl
      _ ≤ _ := Finset.sum_le_sum hlamA
  have hSumB : 42 * (-(l1Poly3 resB_int : ℝ) / (12 * (S2 : ℝ))) ≤
      ∑ p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·),
        ((hB (t p r1) - psiBa (t p r1) + hB (t p r2) - psiBa (t p r2)) / 6
        + psiCb (t r1 r2) - (cb_int : ℝ) / (S2 : ℝ)
        - ((sP 1 (t p r1) (t p r1) + sP (t p r1) 1 (t p r1) + sP (t p r1) (t p r1) 1)
          + (sP 1 (t p r2) (t p r2) + sP (t p r2) 1 (t p r2) + sP (t p r2) (t p r2) 1)
          + (sR 1 (t p r1) (t p r1) + sR (t p r1) 1 (t p r1) + sR (t p r1) (t p r1) 1)
          + (sR 1 (t p r2) (t p r2) + sR (t p r2) 1 (t p r2) + sR (t p r2) (t p r2) 1)) / 6
        - 2 * sP (t p r1) (t p r2) (t r1 r2)
        - 2 * (sR (t p r1) (t r1 r2) (t p r2) + sR (t p r2) (t r1 r2) (t p r1))) := by
    have hc : (∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, (ringSet.filter (r1 < ·)).card : ℕ) = 42 := by decide
    have hcR : (∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ _r2 ∈ ringSet.filter (r1 < ·), (1 : ℝ)) = 42 := by
      simpa [Finset.sum_const] using congrArg (Nat.cast (R := ℝ)) hc
    calc 42 * (-(l1Poly3 resB_int : ℝ) / (12 * (S2 : ℝ)))
        = ∑ _p ∈ poleSet, ∑ r1 ∈ ringSet, ∑ _r2 ∈ ringSet.filter (r1 < ·),
            (-(l1Poly3 resB_int : ℝ) / (12 * (S2 : ℝ))) := by
          rw [← hcR, Finset.sum_mul]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_mul]; simp only [one_mul]
      _ ≤ _ := Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun r1 hr1 =>
          Finset.sum_le_sum fun r2 hr2 => hlamB p hp r1 hr1 r2 hr2
  have hSumG : 35 * (-(l1Poly3 resG_int : ℝ) / (1260 * (S2 : ℝ))) ≤
      ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ r3 ∈ ringSet.filter (r2 < ·),
        ((hC (t r1 r2) - 2 * psiCb (t r1 r2) + hC (t r1 r3) - 2 * psiCb (t r1 r3)
          + hC (t r2 r3) - 2 * psiCb (t r2 r3)) / 5 - (cg_int : ℝ) / (35 * (S2 : ℝ))
        - 2 * ((sR 1 (t r1 r2) (t r1 r2) + sR (t r1 r2) 1 (t r1 r2) + sR (t r1 r2) (t r1 r2) 1)
          + (sR 1 (t r1 r3) (t r1 r3) + sR (t r1 r3) 1 (t r1 r3) + sR (t r1 r3) (t r1 r3) 1)
          + (sR 1 (t r2 r3) (t r2 r3) + sR (t r2 r3) 1 (t r2 r3) + sR (t r2 r3) (t r2 r3) 1)) / 5
        - 2 * (sR (t r1 r2) (t r1 r3) (t r2 r3) + sR (t r1 r2) (t r2 r3) (t r1 r3)
          + sR (t r1 r3) (t r2 r3) (t r1 r2))) := by
    have hc : (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), (ringSet.filter (r2 < ·)).card : ℕ) = 35 := by decide
    have hcR : (∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ _r3 ∈ ringSet.filter (r2 < ·), (1 : ℝ)) = 35 := by
      simpa [Finset.sum_const] using congrArg (Nat.cast (R := ℝ)) hc
    calc 35 * (-(l1Poly3 resG_int : ℝ) / (1260 * (S2 : ℝ)))
        = ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), ∑ _r3 ∈ ringSet.filter (r2 < ·),
            (-(l1Poly3 resG_int : ℝ) / (1260 * (S2 : ℝ))) := by
          rw [← hcR, Finset.sum_mul]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_mul]; simp only [one_mul]
      _ ≤ _ := Finset.sum_le_sum fun r1 hr1 => Finset.sum_le_sum fun r2 hr2 =>
          Finset.sum_le_sum fun r3 hr3 => hlamG r1 hr1 r2 hr2 r3 hr3
  -- Harmonic positivity
  have hHarmP : 0 ≤ ∑ i ∈ poleSet, ∑ j : Fin 9, ∑ l : Fin 9, sP (t i j) (t i l) (t j l) := by
    dsimp only [sP, t]
    simp_rw [← Finset.sum_div]
    exact div_nonneg (sum_harmListEv_nonneg harmP poleSet z hzu) hS2.le
  have hHarmR : 0 ≤ ∑ i ∈ ringSet, ∑ j : Fin 9, ∑ l : Fin 9, sR (t i j) (t i l) (t j l) := by
    dsimp only [sR, t]
    simp_rw [← Finset.sum_div]
    exact div_nonneg (sum_harmListEv_nonneg harmR ringSet z hzu) hS2.le
  -- Combine assembly with 1D minorant upper bounds
  let r2_max : ℤ := max (l1List res_yA_int : ℤ) (max (20 * (l1List res_yB_int : ℤ)) (20 * (l1List res_yC_int : ℤ)))
  let R2 : ℝ := (r2_max : ℝ) / (20 * (S2 : ℝ))
  have hphi_nn : ∀ i j : Fin 9, 0 ≤ phi (t i j) := fun i j => by
    unfold phi; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hA_le : hA (t 0 1) ≤ (1 + R2) * phi (t 0 1) := by
    have h1 := minorA_bound (ht_lo 0 1) ht01
    have hle : (l1List res_yA_int : ℝ) / (20 * (S2 : ℝ)) ≤ R2 :=
      div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (hphi_nn 0 1))
  have hB_le : ∀ p ∈ poleSet, ∀ r ∈ ringSet, hB (t p r) ≤ (1 + R2) * phi (t p r) := by
    intro p hp r hr
    have hne_pr : p ≠ r := fun h => by
      subst h; exact Finset.disjoint_left.mp disjoint_poleSet_ringSet hp hr
    have h1 := minorBC_bound hB_int res_yB_int sigB_0 sigB_1 sigB_2 sigB_3 minorB_ok
      (ht_lo p r) (ht_lt p r hne_pr)
    have hle : (l1List res_yB_int : ℝ) / (S2 : ℝ) ≤ R2 := by
      have hm : 20 * (l1List res_yB_int : ℤ) ≤ r2_max :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have hmR : 20 * (l1List res_yB_int : ℝ) ≤ (r2_max : ℝ) := by exact_mod_cast hm
      dsimp only [R2]
      rw [div_le_div_iff₀ hS2 (by linarith)]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (hphi_nn p r))
  have hC_le : ∀ r1 ∈ ringSet, ∀ r2 ∈ ringSet.filter (r1 < ·), hC (t r1 r2) ≤ (1 + R2) * phi (t r1 r2) := by
    intro r1 _ r2 hr2
    have hlt : r1 < r2 := (Finset.mem_filter.mp hr2).2
    have h1 := minorBC_bound hC_int res_yC_int sigC_0 sigC_1 sigC_2 sigC_3 minorC_ok
      (ht_lo r1 r2) (ht_lt r1 r2 (ne_of_lt hlt))
    have hle : (l1List res_yC_int : ℝ) / (S2 : ℝ) ≤ R2 := by
      have hm : 20 * (l1List res_yC_int : ℤ) ≤ r2_max :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have hmR : 20 * (l1List res_yC_int : ℝ) ≤ (r2_max : ℝ) := by exact_mod_cast hm
      dsimp only [R2]
      rw [div_le_div_iff₀ hS2 (by linarith)]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (hphi_nn r1 r2))
  have hE_eq : coulombEnergy9 z = sumPairs9 (fun i j => phi (t i j)) := by
    unfold coulombEnergy9 sumPairs9
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact inv_norm_eq_phi (hzu i) (hzu j)
  have hH_le_E : hA (t 0 1) + ∑ p ∈ poleSet, ∑ r ∈ ringSet, hB (t p r)
      + ∑ r1 ∈ ringSet, ∑ r2 ∈ ringSet.filter (r1 < ·), hC (t r1 r2) ≤
      (1 + R2) * coulombEnergy9 z := by
    rw [hE_eq, sumPairs9_pole_ring (fun i j => phi (t i j))]
    have hBsum := Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun r hr => hB_le p hp r hr
    have hCsum := Finset.sum_le_sum fun r1 hr1 => Finset.sum_le_sum fun r2 hr2 => hC_le r1 hr1 r2 hr2
    simp_rw [← Finset.mul_sum] at hBsum hCsum
    linarith
  have hlow : (e_int : ℝ) / (S2 : ℝ)
      + 7 * (-(l1Poly3 resA_int : ℝ) / (280 * (S2 : ℝ)))
      + 42 * (-(l1Poly3 resB_int : ℝ) / (12 * (S2 : ℝ)))
      + 35 * (-(l1Poly3 resG_int : ℝ) / (1260 * (S2 : ℝ))) ≤ (1 + R2) * coulombEnergy9 z := by
    linarith [hasm, hSumA, hSumB, hSumG, hHarmP, hHarmR, hH_le_E]
  -- Finish via `bound_ok`
  have h1R2_pos : 0 < 1 + R2 := by
    have hr2_nn : (0 : ℝ) ≤ R2 := by
      dsimp only [R2]
      refine div_nonneg ?_ (by linarith)
      have h0 : (0 : ℤ) ≤ (l1List res_yA_int : ℤ) := Int.natCast_nonneg _
      have h1 : (0 : ℤ) ≤ r2_max := h0.trans (le_max_left _ _)
      exact_mod_cast h1
    linarith
  have hbd : ((E_ttp_hi_num * 18 * (20 * S2 + r2_max) : ℤ) : ℝ) <
      ((E_ttp_hi_den * (360 * e_int - (9 * (l1Poly3 resA_int : ℤ) + 1260 * (l1Poly3 resB_int : ℤ) + 10 * (l1Poly3 resG_int : ℤ))) : ℤ) : ℝ) := by
    exact_mod_cast bound_ok
  push_cast at hbd
  have hstrict : E_ttp_hi * (1 + R2) <
      (e_int : ℝ) / (S2 : ℝ)
      + 7 * (-(l1Poly3 resA_int : ℝ) / (280 * (S2 : ℝ)))
      + 42 * (-(l1Poly3 resB_int : ℝ) / (12 * (S2 : ℝ)))
      + 35 * (-(l1Poly3 resG_int : ℝ) / (1260 * (S2 : ℝ))) := by
    unfold E_ttp_hi
    dsimp only [R2]
    have hden : (0 : ℝ) < (E_ttp_hi_den : ℝ) := by norm_num [E_ttp_hi_den]
    have hL : (E_ttp_hi_num : ℝ) / (E_ttp_hi_den : ℝ) * (1 + (r2_max : ℝ) / (20 * (S2 : ℝ))) =
        ((E_ttp_hi_num : ℝ) * 18 * (20 * (S2 : ℝ) + (r2_max : ℝ))) / (360 * (S2 : ℝ) * (E_ttp_hi_den : ℝ)) := by
      field_simp; ring
    have hR : (e_int : ℝ) / (S2 : ℝ)
        + 7 * (-(l1Poly3 resA_int : ℝ) / (280 * (S2 : ℝ)))
        + 42 * (-(l1Poly3 resB_int : ℝ) / (12 * (S2 : ℝ)))
        + 35 * (-(l1Poly3 resG_int : ℝ) / (1260 * (S2 : ℝ))) =
        ((E_ttp_hi_den : ℝ) * (360 * (e_int : ℝ) - (9 * (l1Poly3 resA_int : ℝ) + 1260 * (l1Poly3 resB_int : ℝ) + 10 * (l1Poly3 resG_int : ℝ))))
          / (360 * (S2 : ℝ) * (E_ttp_hi_den : ℝ)) := by
      field_simp; ring
    rw [hL, hR]
    exact div_lt_div_of_pos_right hbd (by positivity)
  nlinarith

end ThomsonN9.StageB.SlabCert
