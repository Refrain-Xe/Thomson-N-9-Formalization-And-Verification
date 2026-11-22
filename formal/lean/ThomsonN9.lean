import ThomsonN9.Solution

/-!
# Root module

`lake build` builds this module and thereby `ThomsonN9/Solution.lean`, which proves all four
challenge theorems fixed in `ComparatorChallenges/ThomsonN9.lean`:

* `ThomsonN9.thomson_nine_M0`
* `ThomsonN9.thomson_nine_M1`
* `ThomsonN9.thomson_nine`
* `ThomsonN9.thomson_nine_unique`

All four theorems are verified by the Lean 4 kernel with only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) and match `ComparatorChallenges/ThomsonN9.lean`
verbatim under `scripts/check.sh`. See `README.md`.
-/
