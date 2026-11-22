# Reproducing the Thomson N = 9 Formal Proof and Independent Stage A Checks

This document describes how to verify both the complete Lean 4 kernel-checked proof (Stage B) and the independent 50-digit Python interval-arithmetic certificate verification (Stage A), as well as how to regenerate the arXiv paper figures and submission bundle.

## Requirements

- **Lean 4 formal proof (Stage B):** `elan`, `git`, `python3`, ~14 GB RAM (for full cold rebuild; ~4 GB for cached check), ~10 GB disk for Mathlib cache.
  - Pinned Lean toolchain: `leanprover/lean4:v4.34.1` (`formal/lean/lean-toolchain`)
  - Pinned Mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612` (`formal/lean/lake-manifest.json`)
  - **Never run `lake update`**, as that modifies dependency pins.
- **Stage A independent numerical certificate verifier & paper figures:** Python 3.10+ with `mpmath`, `numpy`, `scipy`, `matplotlib`.

## 1. One-Command Lean 4 Verification (Official Gate)

From the repository root (`thomson-n9/`):

```sh
bash formal/lean/scripts/check.sh
```

This script executes every gate in sequence and exits non-zero on any failure:
1. Verifies the SHA-256 digest of all 75 tracked files in `formal/lean/` against `formal/lean/SHA256SUMS.txt` (enforcing in particular that `ComparatorChallenges/ThomsonN9.lean` is untouched) and rejects any tracked-but-unpinned file.
2. Scans `ThomsonN9/Solution.lean` for forbidden tokens (`sorry`, `native_decide`, `ofReduceBool`, `ofReduceNat`, `trustCompiler`, `axiom`, `opaque`, `unsafe`, `partial`, `set_option`, `implemented_by`, `@[extern`, `csimp`, macros, `#eval`, `#exit`) and scans all supporting modules in `ThomsonN9/` (45 cone modules, 20,327 lines) and `lakefile.toml`, allowing only `set_option maxHeartbeats`, `set_option maxRecDepth`, and `linter.*` switches outside `Solution.lean`.
3. Fetches the prebuilt Mathlib cache (`lake exe cache get`).
4. Builds `ThomsonN9` and `ComparatorChallenges` (`lake build ThomsonN9 ComparatorChallenges`), enforcing exactly **4** `sorry` warnings in `ComparatorChallenges/ThomsonN9.lean` and **0** in `ThomsonN9/Solution.lean`.
5. Runs `lake env lean scripts/CheckAxioms.lean` and enforces a strict axiom whitelist asserting that `thomson_nine_M0`, `thomson_nine_M1`, `thomson_nine`, `thomson_nine_unique`, `thomson_nine_main`, `triCapPrism_injective`, and `triCapPrism_mem` depend solely on subsets of:
   ```text
   [propext, Classical.choice, Quot.sound]
   ```
6. Dumps all declarations of `ComparatorChallenges.ThomsonN9` and `ThomsonN9.Solution` under `pp.all` + `pp.universes` and runs `scripts/compare_statements.py` (`SKIP = set()`, zero exemptions), verifying an exact 36/36 match (`STATEMENT COMPARISON: OK`, digest `bafcdc5ef8cba6cd31268f3c91bb00bb64ee8907a4c0b58791617a864ab735c9`).

*Verification boundary:* All checks above run on the reference Lean `v4.34.1` kernel (`compare_statements.py` verifies statement fidelity directly; running `Lean Comparator` and an independent second kernel such as `lean4export + nanoda` is optional future hardening).

### Cold rebuild from zero `.olean` cache

To verify every Stage B module and all 19 parallel 2D-Kronecker slices from scratch without reusing compiled `ThomsonN9` or `ComparatorChallenges` artifacts (while keeping Mathlib's cache intact):

```sh
rm -rf formal/lean/.lake/build/lib/lean/ThomsonN9* \
       formal/lean/.lake/build/ir/ThomsonN9* \
       formal/lean/.lake/build/lib/lean/ComparatorChallenges* \
       formal/lean/.lake/build/ir/ComparatorChallenges*
bash formal/lean/scripts/check.sh
```

Note on RAM for cold builds: each `CapCertSosSlice*.lean` kernel check uses roughly 1.5--3.5 GB RAM. On machines with $\le 24$ GB RAM, build the 19 slice modules in batches of 3--4 before running `check.sh`:

```sh
cd formal/lean
lake build ThomsonN9.StageB.CapCertSosData
for s in M9 M8 M7 M6 M5 M4 M3 M2 M1 0 1 2 3 4 5 6 7 8 9; do
  lake build ThomsonN9.StageB.CapCertSosSlice${s}
done
bash scripts/check.sh
```

### Negative controls (statement fidelity & kernel reduction)

Run after `check.sh`:

```sh
bash formal/lean/scripts/negative-control.sh
```

This runs two automated negative controls: (a) flips the inequality in `thomson_nine` on a scratch copy of the challenge file and verifies `compare_statements.py` rejects `Solution.tsv`, naming only `ThomsonN9.thomson_nine`; and (b) asserts a false certificate boolean via `decide +kernel` and verifies the Lean 4 kernel rejects it.

## 2. Independent Stage A Verification (Python Exact Fraction + 50-dps Interval Arithmetic)

```sh
python3 numerics/bounds/stage_a_closure.py
```

This runs out-of-process rational `LDL^T` verification of all 5 slab certificates (`[-1, -9/10]`) and the 128-bit $S_3$-invariant $M=10, K=10$ cap certificate (`[-9/10, 1]`), 50-digit 1D coercivity ($\rho = 10^{-6}$), full unsampled $K_9$ combinatorial rigidity (`30,240 == TTP S_9 orbit`), 50-digit Procrustes alignment, 4th-order geodesic-Procrustes Taylor local minimality ($r^* = 0.065$), and 5/5 negative tamper controls (~3 minutes total).

## 3. Regenerating Paper Figures and the arXiv Upload Archive

```sh
python3 paper/figures/make_paper_figures.py
bash paper/build_arxiv_tarball.sh
```

This regenerates `paper/figures/fig_{ttp,overview,minorant}.{pdf,png}` directly from the exact Lean certificate integers and packages `paper/arxiv-submission.tar.gz` ready for arXiv upload.
