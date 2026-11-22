import Mathlib

/-!
# Table A (Stage B structure-theorem layer): item A3 (R13 / r13a)

This module is deliberately self-contained: it imports only `Mathlib`, it does
not import any in-repo solution module (in particular not `ThomsonN9.Solution`
nor `ThomsonN9.TableA`), and it is not imported by any in-repo module — the
root module `ThomsonN9.lean`, `ThomsonN9/Solution.lean`,
`ThomsonN9/M1Data.lean`, `scripts/check.sh` and `lakefile.toml` are untouched,
so this file cannot interfere with the parallel r13b/r13c work (file-face
zero overlap).

It materialises item A3 of Table A in `notes/stageb-scope.md` (typed
combination identities of the (3,3,3) typed cap ladder,
`numerics/bounds/typed_ladder.py:229-300` QuotientMaps counts):

* **A3 (a) — typed bucket counting.** `TYPES = (0,0,0,1,1,1,2,2,2)`
  (`types i = i / 3`). The `C(9,3) = 84` three-point groups, each encoded once
  as a strictly increasing index triple, are bucketed by their nondecreasing
  type triple (`sort3`/`bucket`). The explicit enumeration table
  (`bucket_table`, `image_buckets`) is checked by `decide`:
  AAA orbit = 3 classes × 1 group, AAB form = 6 classes × 9 groups,
  ABC = 1 class × 27 groups, and the balance `3·1 + 6·9 + 1·27 = 84 = #groups`
  (`a3_typed_counting`, `bucket_partition` via `Finset.card_eq_sum_card_image`).
  This mirrors `QuotientMaps.full_classes` (10 classes) and
  `QuotientMaps.counts = {"AAA": 1, "AAB": 9, "ABC": 27}`
  (`numerics/bounds/typed_ladder.py:311-312`), audited as
  `class_counts` in `numerics/bounds/results/r9_s3_rederive.json`.

* **A3 (b) — ℓ₁ assembly normalisation identity.** With the five exact
  rational constants of the M9 cap certificate
  `certificates/n9-stage-a4-typedcap-m0748_M9.json`
  (`blocks.c_A = 0`, `blocks.c_B = 140609170236263/281474976710656`,
  `blocks.c_C = 20717/7599824371187712`,
  `blocks.e = 7250752630179179/281474976710656`, and
  `Σ F⁽⁰⁾ = 9503960072215/70368744177664`, the exact `Fraction` sum of all 81
  entries of the 9×9 matrix `blocks.F0`), the normalisation row of the
  quotient SDP (`numerics/bounds/typed_ladder.py` docstring line
  “3c_A + 54c_B + 27c_C = e + 9·ΣF⁽⁰⁾”) holds *on the nose* in `ℚ`
  (`a3_l1_normalization`, `norm_num`), re-proved here so the Lean kernel
  checks it. The acceptance gate `numerics/bounds/r13_a3a4_gate.py` re-reads
  the certificate chain (`results/r9_s3_rederive.json` → sole derivation
  input certificate), recomputes the identity with `fractions.Fraction` and
  compares the five ℚ literals of this file component-wise.

The `decide` proofs of the counting layer need `maxRecDepth` bumps (kernel
reduction of the 729-element product `Finset.univ` filter); no `native_decide`
is used, so no `ofReduceBool`/`ofReduceNat` axiom can appear.
-/

namespace ThomsonN9.TableA3

/-! ### A3 (a): the typed bucket enumeration of the 84 three-point groups -/

/-- 分型函数：第 `i` 个点的类型 = `i / 3`（TYPES = (0,0,0,1,1,1,2,2,2)）. -/
def types : Fin 9 → ℕ := fun i => i.val / 3

/-- 三个 ℕ 的非降序排列（分桶键）. -/
def sort3 (a b c : ℕ) : ℕ × ℕ × ℕ :=
  if a ≤ b then
    (if b ≤ c then (a, b, c) else if a ≤ c then (a, c, b) else (c, a, b))
  else
    (if a ≤ c then (b, a, c) else if b ≤ c then (b, c, a) else (c, b, a))

/-- 三点组全集：严格递增指标三元组（每个 3-点集恰编码一次），`C(9,3) = 84` 个. -/
def allTriples : Finset (Fin 9 × Fin 9 × Fin 9) :=
  Finset.univ.filter fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2

/-- 组 → 分型桶：三点类型的非降序三元组. -/
def bucket (p : Fin 9 × Fin 9 × Fin 9) : ℕ × ℕ × ℕ :=
  sort3 (types p.1) (types p.2.1) (types p.2.2)

/-- 桶 `b` 中的组数. -/
def bucketCount (b : ℕ × ℕ × ℕ) : ℕ := (allTriples.filter fun p => bucket p = b).card

/-- 全部 10 个分型类（非降序类型三元组，字典序）. -/
def classes : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 1, 1), (0, 1, 2), (0, 2, 2),
   (1, 1, 1), (1, 1, 2), (1, 2, 2), (2, 2, 2)]

/-- 同一 10 类集的 Finset 形（`image_buckets` 的右端）. -/
def classesSet : Finset (ℕ × ℕ × ℕ) :=
  {(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 1, 1), (0, 1, 2), (0, 2, 2),
   (1, 1, 1), (1, 1, 2), (1, 2, 2), (2, 2, 2)}

set_option maxRecDepth 1000000 in
/-- 组数恰为 `C(9,3) = 84`. -/
theorem card_allTriples : allTriples.card = 84 := by decide

/-- **显式枚举表**：10 个分型类上的组数依次为
`[1, 9, 9, 9, 27, 9, 1, 9, 9, 1]`（与 `classes` 字典序对齐）. -/
theorem bucket_table :
    [bucketCount (0, 0, 0), bucketCount (0, 0, 1), bucketCount (0, 0, 2),
     bucketCount (0, 1, 1), bucketCount (0, 1, 2), bucketCount (0, 2, 2),
     bucketCount (1, 1, 1), bucketCount (1, 1, 2), bucketCount (1, 2, 2),
     bucketCount (2, 2, 2)] = [1, 9, 9, 9, 27, 9, 1, 9, 9, 1] := by decide

set_option maxRecDepth 1000000 in
/-- 完备性：84 个组的分型桶恰取遍全部 10 个类. -/
theorem image_buckets : allTriples.image bucket = classesSet := by decide

set_option maxRecDepth 1000000 in
/-- 分拆求和：`∑_桶 组数 = 84`（`Finset.card_eq_sum_card_image`）. -/
theorem bucket_partition : ∑ b ∈ allTriples.image bucket, bucketCount b = 84 := by
  have h := Finset.card_eq_sum_card_image bucket allTriples
  rw [card_allTriples] at h
  simpa only [bucketCount] using h.symm

/-- 轨道口径小计：AAA 三桶合计 `3·1`，AAB 六桶合计 `6·9`，ABC 一桶 `1·27`. -/
theorem orbit_totals :
    bucketCount (0, 0, 0) + bucketCount (1, 1, 1) + bucketCount (2, 2, 2) = 3 * 1 ∧
    bucketCount (0, 0, 1) + bucketCount (0, 0, 2) + bucketCount (0, 1, 1)
      + bucketCount (0, 2, 2) + bucketCount (1, 1, 2) + bucketCount (1, 2, 2) = 6 * 9 ∧
    bucketCount (0, 1, 2) = 1 * 27 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **A3 (a) 主定理**：TYPES=(0,0,0,1,1,1,2,2,2) 的全部 `C(9,3)=84` 个三点组按类型分桶
恰为 AAA 轨道 3 类×各 1 组、AAB 型 6 类×各 9 组、ABC 1 类×27 组，且配平
`3·1 + 6·9 + 1·27 = 84 = allTriples.card`. -/
theorem a3_typed_counting :
    (bucketCount (0, 0, 0) = 1 ∧ bucketCount (1, 1, 1) = 1 ∧ bucketCount (2, 2, 2) = 1)
    ∧ (bucketCount (0, 0, 1) = 9 ∧ bucketCount (0, 0, 2) = 9 ∧ bucketCount (0, 1, 1) = 9
        ∧ bucketCount (0, 2, 2) = 9 ∧ bucketCount (1, 1, 2) = 9 ∧ bucketCount (1, 2, 2) = 9)
    ∧ bucketCount (0, 1, 2) = 27
    ∧ 3 * 1 + 6 * 9 + 1 * 27 = 84
    ∧ allTriples.card = 84 := by
  refine ⟨⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by norm_num, card_allTriples⟩

/-! ### A3 (b): the ℓ₁ assembly normalisation identity (exact ℚ arithmetic) -/

/-- **A3 (b) ℓ₁ 装配归一化恒等式**：M9 证书五字面量
（`c_A = 0`、`c_B = 140609170236263/281474976710656`、
`c_C = 20717/7599824371187712`、`e = 7250752630179179/281474976710656`、
`Σ F⁽⁰⁾ = 9503960072215/70368744177664`，即 9×9 矩阵 `F0` 全 81 元素之和）满足
`3·c_A + 54·c_B + 27·c_C − 9·ΣF⁽⁰⁾ − e = 0`（商 SDP 归一化行
`3c_A + 54c_B + 27c_C = e + 9·ΣF⁽⁰⁾`，typed_ladder.py 文档串），在 `ℚ` 中逐位精确. -/
theorem a3_l1_normalization :
    3 * (0 : ℚ)
      + 54 * (140609170236263 : ℚ) / 281474976710656
      + 27 * (20717 : ℚ) / 7599824371187712
      - 9 * (9503960072215 : ℚ) / 70368744177664
      - (7250752630179179 : ℚ) / 281474976710656 = 0 := by
  norm_num

end ThomsonN9.TableA3
