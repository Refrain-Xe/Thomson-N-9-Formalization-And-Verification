import Mathlib
import ThomsonN9.TableB1
import ThomsonN9.TableB1Aut
import ThomsonN9.TableB5Chain

/-!
# Table B1 Witness (R23A / r23a-pattern-witness): the σ₀ alignment witness set

**B1-Witness.**  R22A built the `l4_orbit` canonical-rep data layer
(`r22_pattern_numeric.json feedContract`: `canonicalRep` 36 unordered-pair
6-colour table, `sigma0LexMin = [0,5,6,4,2,1,7,3,8]`, 12 witnesses) and R22B
built the automorphism group (`ThomsonN9.TableB1Aut.card_ttpAut_eq_12`).
This file closes the consumption side — the tenth Table-B item (D100 ④(1)(2)
合一，D101 裁决 1/2): with

  `repData`  = the 36-colour table transcribed from `feedContract.canonicalRep`
               (pairIndex `k` ↔ the `k`-th `(i,j)`, `i<j`, lex pair),
  `sigma0`   = the explicit `Equiv.Perm (Fin 9)` with image tuple
               `[0,5,6,4,2,1,7,3,8]`,
  `witnessPred σ` = `∀ i ≠ j, rep(σ i, σ j) = nodeOfN i j`,

it proves, with zero `sorry`:

* **(i) σ₀ witness property** `sigma0_witness`:
  `rep (σ₀ i) (σ₀ j) = nodeOfN i.val j.val` for every `i ≠ j` (81 kernel-decide
  arms, `ThomsonN9.TableB1Aut.tau_mem` :149 同式).
* **(ii) aligned-coset uniqueness** `mem_witness_iff_coset`:
  `σ ∈ witnessSet ↔ σ₀⁻¹∘σ ∈ ttpAut`, equivalently
  `witnessSet = (fun s => sigma0 * s) '' ttpAut` (function composition
  `(σ₀∘s)(i) = σ₀ (s i)`).  Direction note: in this toolchain's Mathlib the
  `Equiv.Perm` multiplication is *composition-ordered* —
  `Mathlib/Algebra/Group/End.lean:68` `mul f g := Equiv.trans g f`, i.e.
  `(e₁ * e₂) i = e₁ (e₂ i)` — so the composition form `σ₀∘s` is the mul term
  `sigma0 * s` (the designer pre-anchor 2026-10-24 verified the composition
  direction numerically: forward `{σ₀∘s : s∈Aut} = W` holds, the reverse
  `{s∘σ₀}` does not — the G5 second implementation re-checks both).
* **(iii) headline** `card_witness_eq_12`:
  `Fintype.card {σ // witnessPred σ} = 12` via the bijection
  `σ ↦ σ₀⁻¹∘σ` composed with `ThomsonN9.TableB1Aut.card_ttpAut_eq_12` :458.
* **(iv) lex-min** `sigma0_lex_min`: `σ₀` is the lexicographic minimum of
  `witnessSet` — bridged to the 12 explicit elements
  `{sigma0 * tau n : n : Fin 12}` (`mem_iff_in_table` + coset) and closed
  arm-by-arm by kernel `decide` over the first-difference lex order
  (`head3_inj` :156 同式).
* **(v) PatternCons witness-independence** `pattern_cons_coset`:
  `PatternCons Y z ρ σ₀ → ∀ s ∈ ttpAut, PatternCons Y z ρ (σ₀ * s)`
  (consumes `ThomsonN9.TableB5Chain.PatternCons` :285–288; the node
  arithmetic `nodeOfN (s i) (s j) = nodeOfN i j` is rewritten by the
  `ttpAutPred` membership).
* **(vi) named instance anchor** `pattern_ident_lift_sigma0`:
  `ThomsonN9.TableB5Chain.pattern_ident_lift` :313 instantiated at `σ₀` —
  `hT + h1 + h2 + hρ + hpat` (de-conditioned `PatternCons` form) yields
  `identNode hT (σ₀ i) (σ₀ j) = nodeOfN i j`.  The 『(P1)–(P4) 未来供给』
  insertion point of D92 裁决 2(δ) thereby has its explicit σ₀ channel.

Import discipline: only `Mathlib`, `ThomsonN9.TableB1`, `ThomsonN9.TableB1Aut`,
`ThomsonN9.TableB5Chain` (transitive closure ~13 files, R22B-measured
3.6–22.1 s/件 within the documented 1200 s compile exception); imports no
other in-repo solution module and is imported by none (TableB5Chain/
TableB1Aut 先例 — non-overlay enforced by the acceptance gate).  Zero ≥15-digit
numeric literals; `#print axioms` on every theorem yields exactly
`{propext, Classical.choice, Quot.sound}` (D82-4 口径), verified live by
`numerics/bounds/r23a_witness_gate.py` (G3).
-/

namespace ThomsonN9.TableB1Witness

open ThomsonN9.TableB1 (nodeOfN nuOfN)
open ThomsonN9.TableB1Aut
open ThomsonN9.TableB5Chain (PatternCons TubePremise identNode pattern_ident_lift
  perm_ne)

/-! ## (i) rep 数据层：36 无序对 6 色表＋σ₀ 显式置换＋见证性质 -/

/-- σ₀ 行（image-tuple `[0,5,6,4,2,1,7,3,8]`——`feedContract.sigma0LexMin`
同源转录；第 k 处的像＝`sigRow0 k`）。 -/
def sigRow0 : Fin 9 → Fin 9 := ![0, 5, 6, 4, 2, 1, 7, 3, 8]

/-- σ₀ 行双射性（kernel 求值）。 -/
theorem sigRow0_bij : Function.Bijective sigRow0 := by decide

/-- **σ₀ 显式 Equiv.Perm**（image-tuple 约定：`sigma0 k = sigRow0 k`）。 -/
noncomputable def sigma0 : Equiv.Perm (Fin 9) := Equiv.ofBijective sigRow0 sigRow0_bij

/-- pairIndex：`k` ↔ 第 `k` 个 `i<j` lex 对（(0,1),(0,2),…,(0,8),(1,2),…,
(7,8)——`feedContract.pairIndexConvention` 同约定；前缀计数
`8i − i(i−1)/2` ＋ 偏移 `j−i−1`）。 -/
def pairIdx (i j : ℕ) : ℕ := 8 * i - i * (i - 1) / 2 + (j - i - 1)

/-- **36 无序对 6 色表**（`r22_pattern_numeric.json feedContract.canonicalRep`
同源转录；sha256 `e69c0253…f225` 由验收门 G5 对 `"0,0,1,3,…"` join 串锚定）。
第 `k` 项＝第 `k` 个 `i<j` lex 对的色值。 -/
def repData (k : ℕ) : ℕ :=
  match k with
  | 0 => 0  -- pair (0,1)
  | 1 => 0  -- pair (0,2)
  | 2 => 1  -- pair (0,3)
  | 3 => 3  -- pair (0,4)
  | 4 => 4  -- pair (0,5)
  | 5 => 4  -- pair (0,6)
  | 6 => 5  -- pair (0,7)
  | 7 => 5  -- pair (0,8)
  | 8 => 4  -- pair (1,2)
  | 9 => 5  -- pair (1,3)
  | 10 => 4  -- pair (1,4)
  | 11 => 0  -- pair (1,5)
  | 12 => 3  -- pair (1,6)
  | 13 => 1  -- pair (1,7)
  | 14 => 5  -- pair (1,8)
  | 15 => 5  -- pair (2,3)
  | 16 => 4  -- pair (2,4)
  | 17 => 3  -- pair (2,5)
  | 18 => 0  -- pair (2,6)
  | 19 => 5  -- pair (2,7)
  | 20 => 1  -- pair (2,8)
  | 21 => 1  -- pair (3,4)
  | 22 => 5  -- pair (3,5)
  | 23 => 5  -- pair (3,6)
  | 24 => 2  -- pair (3,7)
  | 25 => 2  -- pair (3,8)
  | 26 => 0  -- pair (4,5)
  | 27 => 0  -- pair (4,6)
  | 28 => 5  -- pair (4,7)
  | 29 => 5  -- pair (4,8)
  | 30 => 4  -- pair (5,6)
  | 31 => 5  -- pair (5,7)
  | 32 => 1  -- pair (5,8)
  | 33 => 1  -- pair (6,7)
  | 34 => 5  -- pair (6,8)
  | 35 => 2  -- pair (7,8)
  | _ => 9

/-- rep 无序对检索（`a = b` 取哑值 9——与 `nodeOfN` 对角约定一致）。 -/
def repPair (a b : ℕ) : ℕ :=
  if a = b then 9 else if a < b then repData (pairIdx a b) else repData (pairIdx b a)

/-- **头条之一：σ₀ 见证性质**——`rep (σ₀ i) (σ₀ j) = nodeOfN i.val j.val`
对一切 `i ≠ j`（81 臂 kernel decide；`TableB1Aut.tau_mem` :149 同式——
canonical rep 与算术分类的对齐性质，R23 设计师 2026-10-24 预锚 36/36）。 -/
theorem sigma0_witness (i j : Fin 9) (hij : i ≠ j) :
    repPair (sigma0 i).val (sigma0 j).val = nodeOfN i.val j.val := by
  fin_cases i <;> fin_cases j <;> decide

/-! ## (ii) 见证载体：成员条件、Set 形式、可判定性、Fintype 与对齐陪集唯一性 -/

/-- **见证成员条件**：σ 保持 canonical rep 的逐对算术分类
（36 无序对条件——`repPair` 无序故与 72 有序条件等价）。 -/
def witnessPred (σ : Equiv.Perm (Fin 9)) : Prop :=
  ∀ i j : Fin 9, i ≠ j → repPair (σ i).val (σ j).val = nodeOfN i.val j.val

/-- **见证集 Set 形式**。 -/
def witnessSet : Set (Equiv.Perm (Fin 9)) := {σ | witnessPred σ}

/-- 行内形 ↔ def 形桥（载体成员关系的双向折射）。 -/
theorem witnessPred_of_inline {σ : Equiv.Perm (Fin 9)}
    (h : ∀ i j : Fin 9, i ≠ j → repPair (σ i).val (σ j).val = nodeOfN i.val j.val) :
    witnessPred σ := h

/-- def 形 ↔ 行内形桥。 -/
theorem inline_of_witnessPred {σ : Equiv.Perm (Fin 9)} (h : witnessPred σ) :
    ∀ i j : Fin 9, i ≠ j → repPair (σ i).val (σ j).val = nodeOfN i.val j.val := h

/-- **DecidablePred 实例**（`ttpAutPredDecidable` 同式——kernel 可求值，
供逐元 decide 与 G3 公理面）。 -/
instance witnessPredDecidable (σ : Equiv.Perm (Fin 9)) : Decidable (witnessPred σ) := by
  unfold witnessPred
  infer_instance

instance decidablePredWitnessPred : DecidablePred witnessPred :=
  fun σ => inferInstanceAs (Decidable (witnessPred σ))

/-- **Fintype 实例**（`ttpAutFintype` :110 同式——行内形式声明）。 -/
instance witnessFintype :
    Fintype {σ : Equiv.Perm (Fin 9) // ∀ i j : Fin 9, i ≠ j →
      repPair (σ i).val (σ j).val = nodeOfN i.val j.val} := by
  refine Fintype.ofFinset (Finset.univ.filter witnessPred) (fun x => ?_)
  constructor
  · exact fun h => Finset.mem_filter.mp h |>.2
  · exact fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩

/-- **对齐陪集桥**：`witnessPred (σ₀ * s) ↔ ttpAutPred s`——σ₀∘s（函数复合
`(σ₀∘s)(i) = σ₀ (s i)`）与 s 的对齐：σ₀ 见证性质重写＋Aut 成员条件桥。
方向锚：本工具链 Mathlib 的 Perm 乘法为函数复合序
（`Mathlib/Algebra/Group/End.lean:68` `mul f g := Equiv.trans g f`，
`(e₁*e₂) i = e₁ (e₂ i)`），故复合形 σ₀∘s ＝ mul 形 `sigma0 * s`；反向
`s * σ₀`（即 `s∘σ₀`）不满足见证集等式——G5 反向对账天然判别。 -/
theorem witness_coset_iff (s : Equiv.Perm (Fin 9)) :
    witnessPred (sigma0 * s) ↔ ttpAutPred s := by
  constructor
  · intro h i j hij
    have hne : s i ≠ s j := fun hh => hij (s.injective hh)
    have hsig := sigma0_witness (s i) (s j) hne
    rw [← hsig]
    exact h i j hij
  · intro h i j hij
    have hne : s i ≠ s j := fun hh => hij (s.injective hh)
    have hsig := sigma0_witness (s i) (s j) hne
    show repPair (sigma0 (s i)).val (sigma0 (s j)).val = nodeOfN i.val j.val
    rw [hsig]
    exact h i j hij

/-- 复合恒等（左）：`σ₀ * (σ₀⁻¹ * σ) = σ`（mul-结合＋σ₀ 单位面）。 -/
theorem mul_coset_left (σ : Equiv.Perm (Fin 9)) :
    sigma0 * (sigma0.symm * σ) = σ := by
  rw [← mul_assoc]
  have h1 : (sigma0 * sigma0.symm) = 1 := Equiv.symm_trans_self sigma0
  rw [h1, one_mul]

/-- 复合恒等（右）：`σ₀⁻¹ * (σ₀ * σ) = σ`。 -/
theorem mul_coset_right (σ : Equiv.Perm (Fin 9)) :
    sigma0.symm * (sigma0 * σ) = σ := by
  rw [← mul_assoc]
  have h1 : (sigma0.symm * sigma0) = 1 := Equiv.self_trans_symm sigma0
  rw [h1, one_mul]

/-- **对齐陪集唯一性（头条之二）**：`σ ∈ witnessSet ↔ σ₀⁻¹∘σ ∈ ttpAut`——
mul 记号下复合 σ₀⁻¹∘σ（`(σ₀⁻¹∘σ)(i) = σ₀⁻¹ (σ i)`）＝ `sigma0.symm * σ`。 -/
theorem mem_witness_iff_coset {σ : Equiv.Perm (Fin 9)} :
    σ ∈ witnessSet ↔ sigma0.symm * σ ∈ ttpAut := by
  constructor
  · intro h
    exact (witness_coset_iff (sigma0.symm * σ)).mp
      (by rw [mul_coset_left]; exact h)
  · intro h
    have hw : witnessPred (sigma0 * (sigma0.symm * σ)) :=
      (witness_coset_iff (sigma0.symm * σ)).mpr h
    rw [mul_coset_left] at hw
    exact hw

/-- **12 显式元桥**：`σ ∈ witnessSet ↔ ∃ n : Fin 12, σ = σ₀ * tau n`
（消费 `mem_iff_in_table`（TableB1Aut :474）经陪集唯一性）。 -/
theorem mem_witness_iff_table {σ : Equiv.Perm (Fin 9)} :
    σ ∈ witnessSet ↔ ∃ n : Fin 12, σ = sigma0 * tau n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iff_in_table.mp ((mem_witness_iff_coset).mp h)
    exact ⟨n, (mul_coset_left σ).symm.trans (by rw [hn])⟩
  · rintro ⟨n, hn⟩
    rw [hn]
    exact (witness_coset_iff (tau n)).mpr (mem_ttpAut (tau_mem n))

/-- σ₀ 是见证（成员条件的直接实例——`feedContract.witnesses[0]` 的形式锚）。 -/
theorem sigma0_mem_witness : witnessPred sigma0 := fun i j hij =>
  sigma0_witness i j hij

/-- σ₀ ∈ witnessSet（Set 形式）。 -/
theorem sigma0_mem_witnessSet : sigma0 ∈ witnessSet := sigma0_mem_witness

/-- **Set 形式陪集等式**：`witnessSet = (fun s => σ₀ * s) '' ttpAut`——
函数复合 `(σ₀∘s)(i) = σ₀ (s i)` 的像集（等价形 W=={σ₀∘s : s∈ttpAut}）。 -/
theorem witnessSet_eq_coset :
    witnessSet = (fun s : Equiv.Perm (Fin 9) => sigma0 * s) '' ttpAut := by
  ext σ
  constructor
  · intro h
    refine ⟨sigma0.symm * σ, (mem_witness_iff_coset).mp h, ?_⟩
    show sigma0 * (sigma0.symm * σ) = σ
    exact mul_coset_left σ
  · rintro ⟨s, hs, heq⟩
    subst heq
    exact (witness_coset_iff s).mpr hs

/-! ## (iii) 头条：|W| = 12 -/

/-- **上界**：card W ≤ 12——σ ↦ σ₀⁻¹∘σ 入 Aut 载体单射，复合
`card_ttpAut_eq_12`（TableB1Aut :458）。 -/
theorem card_le_witness :
    Fintype.card {σ : Equiv.Perm (Fin 9) // ∀ i j : Fin 9, i ≠ j →
      repPair (σ i).val (σ j).val = nodeOfN i.val j.val} ≤ 12 := by
  refine le_trans ?_ card_ttpAut_eq_12.le
  refine Fintype.card_le_of_injective
    (fun σ : {σ : Equiv.Perm (Fin 9) // ∀ i j : Fin 9, i ≠ j →
        repPair (σ i).val (σ j).val = nodeOfN i.val j.val} =>
      (⟨sigma0.symm * σ.val, (mem_witness_iff_coset).mp σ.property⟩ :
        {σ : Equiv.Perm (Fin 9) // ∀ i j : Fin 9, i ≠ j →
          nodeOfN (σ i).val (σ j).val = nodeOfN i.val j.val})) ?_
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  apply Subtype.ext
  have hv : sigma0.symm * a = sigma0.symm * b := congrArg Subtype.val hab
  apply Equiv.ext
  intro i
  have hpt := congrArg (fun t : Equiv.Perm (Fin 9) => t i) hv
  exact sigma0.symm.injective hpt

/-- **下界**：12 ≤ card W——12 显式见证元 `sigma0 * tau n` 注入
（`tau_injective`（TableB1Aut :160）＋σ₀ 单射消去）。 -/
theorem card_ge_witness :
    12 ≤ Fintype.card {σ : Equiv.Perm (Fin 9) // ∀ i j : Fin 9, i ≠ j →
      repPair (σ i).val (σ j).val = nodeOfN i.val j.val} :=
  Fintype.card_le_of_injective
    (fun n : Fin 12 => ⟨sigma0 * tau n, (witness_coset_iff (tau n)).mpr (tau_mem n)⟩)
    (fun a b hab => by
      have hv : sigma0 * tau a = sigma0 * tau b := congrArg Subtype.val hab
      have htab : tau a = tau b := by
        apply Equiv.ext
        intro i
        have hpt := congrArg (fun t : Equiv.Perm (Fin 9) => t i) hv
        exact sigma0.injective hpt
      exact tau_injective htab)

/-- **头条定理之三：card_witness_eq_12**——见证集基数恰 12
（le_antisymm card_le_witness card_ge_witness；σ ↦ σ₀⁻¹∘σ 双射复合
`card_ttpAut_eq_12`（TableB1Aut :458）——card_ge/card_le 同式）。 -/
theorem card_witness_eq_12 :
    Fintype.card {σ : Equiv.Perm (Fin 9) // ∀ i j : Fin 9, i ≠ j →
      repPair (σ i).val (σ j).val = nodeOfN i.val j.val} = 12 :=
  le_antisymm card_le_witness card_ge_witness

/-! ## (iv) lex-min：σ₀ 是见证集的字典序最小元 -/

/-- **首差 lex 序**：`lexLess σ τ` ⟺ 首个像值不同的位置处 σ 严格小
（9 点 image-tuple 上即标准字典序）。 -/
def lexLess (σ τ : Equiv.Perm (Fin 9)) : Prop :=
  ∃ k : Fin 9, (∀ m : Fin 9, m.val < k.val → (σ m).val = (τ m).val) ∧
    (σ k).val < (τ k).val

/-- lexLess 可判定实例（有限枚举组合——kernel 可求值）。 -/
instance decidableLexLess (σ τ : Equiv.Perm (Fin 9)) : Decidable (lexLess σ τ) := by
  unfold lexLess
  infer_instance

/-- **lex-min 逐臂**：12 显式元 `σ₀ * tau n` 中 n=0 即 σ₀ 本元、其余 11 元
在首差位置严格大（首差索引：n=1 在位置 1，n=2..11 在位置 0——G5 第二实现
独立重算对账）。 -/
theorem lex_min_arm (n : Fin 12) :
    (sigma0 * tau n = sigma0) ∨ lexLess sigma0 (sigma0 * tau n) := by
  fin_cases n <;> decide

/-- **头条定理之四：σ₀ 是 witnessSet 的 lex-min**——每个见证要么就是 σ₀
要么 lex 严格大于 σ₀（经 `mem_witness_iff_table` 桥化为 12 显式元逐臂
decide；`head3_inj` :156 同式）。 -/
theorem sigma0_lex_min : ∀ σ ∈ witnessSet, σ = sigma0 ∨ lexLess sigma0 σ := by
  intro σ hσ
  obtain ⟨n, hn⟩ := (mem_witness_iff_table).mp hσ
  rw [hn]
  exact lex_min_arm n

/-! ## (v) PatternCons 见证无关性 -/

/-- **头条定理之五：PatternCons 见证无关性**——`PatternCons Y z ρ σ₀ →
∀ s ∈ ttpAut, PatternCons Y z ρ (σ₀ * s)`（TableB5Chain.lean:285–288 def
消费；12 见证任选皆可——`nodeOfN (s i) (s j) = nodeOfN i j` 经 Aut 成员
条件重写，σ₀ 重排几何面逐对不变）。 -/
theorem pattern_cons_coset {Y : Matrix (Fin 9) (Fin 3) ℝ} {z ρ : ℝ}
    (hpat : PatternCons Y z ρ sigma0) :
    ∀ s : Equiv.Perm (Fin 9), ttpAutPred s → PatternCons Y z ρ (sigma0 * s) := by
  intro s hs hT i j hij
  have hne : s i ≠ s j := fun hh => hij (s.injective hh)
  have h := hpat hT (s i) (s j) hne
  rw [hs i j hij] at h
  exact h

/-! ## (vi) pattern_ident_lift 的 σ₀ 具名实例锚 -/

/-- **头条定理之六：pattern_ident_lift_sigma0**——`TableB5Chain.lean:313`
`pattern_ident_lift` 在 σ₀ 的具名实例锚：`hT + h1 + h2 + hρ + hpat`
（hpat＝PatternCons 去条件形）⟹ `identNode hT (σ₀ i) (σ₀ j) = nodeOfN i j`。
D92 裁决 2(δ) 预留插入点的『(P1)–(P4) 未来供给』接口自此有显式 σ₀ 通道。 -/
theorem pattern_ident_lift_sigma0 {Y : Matrix (Fin 9) (Fin 3) ℝ} {z ρ : ℝ}
    (hT : TubePremise Y z ρ) (h1 : (ThomsonN9.TableB5Data.zLo : ℝ) ≤ z)
    (h2 : z ≤ (ThomsonN9.TableB5Data.zHi : ℝ))
    (hρ : ρ < (ThomsonN9.TableB5ChainData.gMin : ℝ) / 2)
    (hpat : ∀ i j : Fin 9, i ≠ j →
      |Y (sigma0 i) ⬝ᵥ Y (sigma0 j) - nuOfN (nodeOfN i.val j.val) z| ≤ ρ)
    (i j : Fin 9) (hij : i ≠ j) :
    identNode hT (sigma0 i) (sigma0 j) (perm_ne hij) = nodeOfN i.val j.val :=
  pattern_ident_lift hT h1 h2 hρ sigma0 hpat i j hij

end ThomsonN9.TableB1Witness
