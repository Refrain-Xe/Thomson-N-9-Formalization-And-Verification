import Mathlib
import ThomsonN9.TableB6Data

/-!
# Table B6 (R15 / r15a): the splice endpoints and record anchors of the endgame partition

**B6.**  The endgame record `assembledRecord = min(12 piece bounds)` of
`numerics/bounds/results/endgame.json` splices the interval `[-1, 1]` into 12
atomic certificate regions by a chain of 13 rational endpoints
`−1 = e0 ≤ e1 ≤ … ≤ e12 = 1` (seamless: adjacent regions share endpoints bit
for bit).  This file proves the *arithmetic layer* of that splice, with all
numeric literals anchored in `ThomsonN9.TableB6Data` (the read-only
re-derivation of `endgame.json`; this file contains zero data-value literals —
only structural index literals `10`/`11`/`12`/`13`):

* **Seamless covering (genuine proof, minimal-hit-index / `Nat.find`).**
  `partition_cover_q` (over `ℚ`) and `partition_cover` (over `ℝ`): every `x`
  with `e0 ≤ x ≤ e12` lies in some piece interval `[eᵢ, eᵢ₊₁]`,
  `i : Fin 12`.  The proof takes the minimal index `j` with `x ≤ e j`
  (`Nat.find` on a decidable predicate — no `decide` on large ℚ comparisons is
  ever invoked); minimality gives `e (j−1) < x ≤ e j`, and the boundary case
  `j = 0` forces `x = e0` where the first chain link closes the interval.
  `endpoints_mono` aggregates the 12 pairwise `norm_num1` chain inequalities
  of the data file.

* **Record assembly (口径①, D61-2).**  `ar_le_bnds`: the assembled record `aR`
  is ≤ every one of the 12 piece bounds (the data file proves each of the 12
  large-Fraction comparisons by `norm_num1`, up to 570 bits);
  `record_is_min`: `∀ i : Fin 12, aR ≤ bnds i ∧ bnds 10 = aR` — the HP piece
  (index 10, the hole interval `[−153/200, −187/250]`) attains the record
  literally (`b10 = aR` bit for bit), which is the certificate-criterion
  content of `AR = min(12 piece bounds)`.  `record_min_attained` restates the
  attainment existentially.  (The alternative `Finset.min'` formulation was
  probed and stuck on a `LinearOrder` metavariable after 5 iterations —
  elaboration detail, logged as D61-2; 口径① carries the same mathematical
  content with zero API risk.)

* **Iron rule.**  `iron_rule_eps`: `aR ≤ estar + epsIron` — the standing rule
  that every lower bound is ≤ E* + 1e-6.  The data file proves the strictly
  stronger `iron_rule : aR ≤ estar` (margin 0.00054… > 0, also strict
  `margin_pos`), from which the ε-form follows by `linarith`.

* **Piece semantics (arithmetic layer).**  `piece_semantics`: every piece `i`
  obeys `estar < bnds i ∨ bnds i ≤ estar + epsIron` — the 10 exclusion pieces
  (region free of TTP, bound must exceed E*; `excl0…9_gt` in the data file)
  and the 2 TTP-covering pieces (HP index 10 and the cap piece index 11 on
  `[−187/250, 1]`, bound ≤ E* + 1e-6; `cover10/11_le_iron` in the data file)
  each satisfy their class's iron condition.

Honest scope note (B6 arithmetic-layer boundary): the certificate semantics
«on region `i` the energy `E ≥ b_i`» (the `verifyCmd` layer of the
typed_ladder / hermite / hp / strips / slab certificates cited in
`endgame.json`) is NOT part of this file — that is the numeric layer's
responsibility; this file proves the arithmetic layer only (covering /
record-min / iron rule / piece semantics).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB6

open ThomsonN9.TableB6Data

/-- 13 端点的 ℕ 索引函数（0..12；越界默认 e12——越界索引不出现在任何定理
陈述中：覆盖机器只在 j < 13 上取 Nat.find）。 -/
def endpointsQ : ℕ → ℚ
  | 0 => e0 | 1 => e1 | 2 => e2 | 3 => e3 | 4 => e4 | 5 => e5 | 6 => e6
  | 7 => e7 | 8 => e8 | 9 => e9 | 10 => e10 | 11 => e11 | _ => e12

/-- 12 分区 bound 的 ℕ 索引函数（0..11；越界默认 b11——同理不入陈述面）。 -/
def bndsQ : ℕ → ℚ
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | 6 => b6
  | 7 => b7 | 8 => b8 | 9 => b9 | 10 => b10 | _ => b11

/-- **端点链单调（聚合）**：12 对逐件 norm_num1（Data 件）的 Fin 12 聚合。 -/
theorem endpoints_mono (i : Fin 12) : endpointsQ i.val ≤ endpointsQ (i.val + 1) := by
  match i with
  | ⟨0, _⟩ => exact e0_le_e1
  | ⟨1, _⟩ => exact e1_le_e2
  | ⟨2, _⟩ => exact e2_le_e3
  | ⟨3, _⟩ => exact e3_le_e4
  | ⟨4, _⟩ => exact e4_le_e5
  | ⟨5, _⟩ => exact e5_le_e6
  | ⟨6, _⟩ => exact e6_le_e7
  | ⟨7, _⟩ => exact e7_le_e8
  | ⟨8, _⟩ => exact e8_le_e9
  | ⟨9, _⟩ => exact e9_le_e10
  | ⟨10, _⟩ => exact e10_le_e11
  | ⟨11, _⟩ => exact e11_le_e12

/-- **12 分区无缝覆盖（ℚ 版，Nat.find 最小命中指数法真证明）**：
`e0 ≤ x ≤ e12` ⇒ x 落入某相邻区间对 `[eᵢ, eᵢ₊₁]`（i : Fin 12）。
取 `j = min{j : x ≤ e j}`（存在：j=12 因 x ≤ e12）；j>0 时极小性给
`e (j−1) < x ≤ e j`；j=0 时 x = e0 由首段链 e0 ≤ e1 收口。全程不经
ℚ 大比较 decide（v1 教训 D61-2）。 -/
theorem partition_cover_q (x : ℚ) (hx0 : e0 ≤ x) (hx1 : x ≤ e12) :
    ∃ i : Fin 12, endpointsQ i.val ≤ x ∧ x ≤ endpointsQ (i.val + 1) := by
  have hpred : ∃ j : ℕ, j < 13 ∧ x ≤ endpointsQ j :=
    ⟨12, by omega, by simpa [endpointsQ] using hx1⟩
  have jspec := Nat.find_spec hpred
  rcases Nat.eq_zero_or_pos (Nat.find hpred) with h0 | hpos
  · rw [h0] at jspec
    refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · simpa [endpointsQ] using hx0
    · have hxe : x ≤ e0 := by simpa [endpointsQ] using jspec.2
      have hxeq : x = e0 := le_antisymm hxe hx0
      subst hxeq
      simpa [endpointsQ] using e0_le_e1
  · have h13 : (Nat.find hpred) - 1 < 13 := by omega
    have hmin : ¬ ((Nat.find hpred) - 1 < 13 ∧ x ≤ endpointsQ ((Nat.find hpred) - 1)) :=
      Nat.find_min hpred (show (Nat.find hpred) - 1 < Nat.find hpred by omega)
    refine ⟨⟨(Nat.find hpred) - 1, by omega⟩, ?_, ?_⟩
    · have hnot : ¬ (x ≤ endpointsQ ((Nat.find hpred) - 1)) := fun hc => hmin ⟨h13, hc⟩
      exact le_of_lt (not_le.mp hnot)
    · have hrew : (Nat.find hpred) - 1 + 1 = Nat.find hpred := by omega
      rw [hrew]
      exact jspec.2

/-- **12 分区无缝覆盖（ℝ 版）**：同一最小命中指数法，端点经 ℚ→ℝ cast
（cast 单调保持不等式链）。 -/
theorem partition_cover (x : ℝ) (hx0 : (e0:ℝ) ≤ x) (hx1 : x ≤ (e12:ℝ)) :
    ∃ i : Fin 12, (endpointsQ i.val : ℝ) ≤ x ∧ x ≤ (endpointsQ (i.val + 1) : ℝ) := by
  have hpred : ∃ j : ℕ, j < 13 ∧ x ≤ (endpointsQ j : ℝ) :=
    ⟨12, by omega, by simpa [endpointsQ] using hx1⟩
  have jspec := Nat.find_spec hpred
  rcases Nat.eq_zero_or_pos (Nat.find hpred) with h0 | hpos
  · rw [h0] at jspec
    refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · simpa [endpointsQ] using hx0
    · have hxe : x ≤ (e0:ℝ) := by simpa [endpointsQ] using jspec.2
      have hxeq : x = (e0:ℝ) := le_antisymm hxe hx0
      subst hxeq
      simpa [endpointsQ] using e0_le_e1
  · have h13 : (Nat.find hpred) - 1 < 13 := by omega
    have hmin : ¬ ((Nat.find hpred) - 1 < 13 ∧ x ≤ (endpointsQ ((Nat.find hpred) - 1) : ℝ)) :=
      Nat.find_min hpred (show (Nat.find hpred) - 1 < Nat.find hpred by omega)
    refine ⟨⟨(Nat.find hpred) - 1, by omega⟩, ?_, ?_⟩
    · have hnot : ¬ (x ≤ (endpointsQ ((Nat.find hpred) - 1) : ℝ)) := fun hc => hmin ⟨h13, hc⟩
      exact le_of_lt (not_le.mp hnot)
    · have hrew : (Nat.find hpred) - 1 + 1 = Nat.find hpred := by omega
      rw [hrew]
      exact jspec.2

/-- **记录装配下侧（逐件聚合）**：AR ≤ bᵢ 对一切片 i（Data 件 12 大分数
norm_num1 的 Fin 12 聚合）。 -/
theorem ar_le_bnds (i : Fin 12) : aR ≤ bndsQ i.val := by
  match i with
  | ⟨0, _⟩ => exact ar_le_b0
  | ⟨1, _⟩ => exact ar_le_b1
  | ⟨2, _⟩ => exact ar_le_b2
  | ⟨3, _⟩ => exact ar_le_b3
  | ⟨4, _⟩ => exact ar_le_b4
  | ⟨5, _⟩ => exact ar_le_b5
  | ⟨6, _⟩ => exact ar_le_b6
  | ⟨7, _⟩ => exact ar_le_b7
  | ⟨8, _⟩ => exact ar_le_b8
  | ⟨9, _⟩ => exact ar_le_b9
  | ⟨10, _⟩ => exact ar_le_b10
  | ⟨11, _⟩ => exact ar_le_b11

/-- **记录装配（口径①，D61-2）**：∀ i : Fin 12, AR ≤ bnds i ∧ bnds 10 = AR
——AR 是 12 分区 bound 的下界且在 HP 片（指标 10）字面取到，即证书口径
assembledRecord = min(12 分区 bound) 的数学内容（零 Finset API 风险；
口径② Finset.min' 的 elaboration 残余细目录 D61-2）。 -/
theorem record_is_min : ∀ i : Fin 12, aR ≤ bndsQ i.val ∧ bndsQ 10 = aR :=
  fun i => ⟨ar_le_bnds i, b10_eq_ar⟩

/-- **记录在 HP 片取到（存在口径）**：∃ i : Fin 12, bnds i = AR。 -/
theorem record_min_attained : ∃ i : Fin 12, bndsQ i.val = aR :=
  ⟨10, b10_eq_ar⟩

/-- **铁律（ε 版）**：AR ≤ E* + 1e-6——由 Data 件更强版 iron_rule（AR ≤ E*，
margin 0.00054… > 0）加 epsIron_pos 经 linarith 推出。 -/
theorem iron_rule_eps : aR ≤ estar + epsIron := by
  have h0 : (0:ℚ) < epsIron := epsIron_pos
  linarith [iron_rule, h0]

/-- **分片语义（算术层聚合）**：每片 i 满足 E* < bᵢ（排除片：区域不含 TTP，
bound 须 > E*——指标 0–9）或 bᵢ ≤ E* + 1e-6（TTP-covering 片：证书域含 TTP，
bound 须 ≤ E*+ε——指标 10 HP 片＋指标 11 cap 片 [−187/250,1]）。 -/
theorem piece_semantics (i : Fin 12) :
    estar < bndsQ i.val ∨ bndsQ i.val ≤ estar + epsIron := by
  match i with
  | ⟨0, _⟩ => exact Or.inl excl0_gt
  | ⟨1, _⟩ => exact Or.inl excl1_gt
  | ⟨2, _⟩ => exact Or.inl excl2_gt
  | ⟨3, _⟩ => exact Or.inl excl3_gt
  | ⟨4, _⟩ => exact Or.inl excl4_gt
  | ⟨5, _⟩ => exact Or.inl excl5_gt
  | ⟨6, _⟩ => exact Or.inl excl6_gt
  | ⟨7, _⟩ => exact Or.inl excl7_gt
  | ⟨8, _⟩ => exact Or.inl excl8_gt
  | ⟨9, _⟩ => exact Or.inl excl9_gt
  | ⟨10, _⟩ => exact Or.inr cover10_le_iron
  | ⟨11, _⟩ => exact Or.inr cover11_le_iron

end ThomsonN9.TableB6
