# The Thomson Problem for $N = 9$: Complete Lean 4 Formal Proof Package

Among all configurations of nine distinct points on the unit sphere $S^2 \subset \mathbb{R}^3$, the $D_{3h}$ **tricapped trigonal prism** `triCapPrism z*` ($z^* \approx 0.70364839580413177578$, $E(z^*) \approx 25.75998653126983156408$) uniquely minimizes the Coulomb energy $E(x) = \sum_{1 \le i < j \le 9} \|x_i - x_j\|^{-1}$ up to orthogonal transformations $O(3)$ and point relabelings $S_9$.

This repository contains the arXiv paper, the complete kernel-checked **Lean 4** formal proof (Stage B), the independent 50-digit interval-arithmetic verification suite (Stage A), all exact certificates, and one-command verification scripts.

## Start Here

- **[paper/main.tex](paper/main.tex)**: arXiv-ready LaTeX manuscript (with vector figures in `paper/figures/` and ready-to-upload archive `paper/arxiv-submission.tar.gz`; metadata in [paper/arxiv_metadata.txt](paper/arxiv_metadata.txt)).
- **[info/THEOREM_MAP.md](info/THEOREM_MAP.md)**: exact section-by-section map from every mathematical lemma in the paper to Lean 4 declarations and line numbers.
- **[REPRODUCE.md](REPRODUCE.md)**: step-by-step build and verification instructions (Lean 4 + Stage A Python checks).
- **[formal/lean/ThomsonN9/Solution.lean](formal/lean/ThomsonN9/Solution.lean)**: complete formal proofs of all four fixed challenge theorems (`thomson_nine_M0`, `thomson_nine_M1`, `thomson_nine`, `thomson_nine_unique`).
- **[formal/lean/ComparatorChallenges/ThomsonN9.lean](formal/lean/ComparatorChallenges/ThomsonN9.lean)**: unmodified fixed challenge statements (unchanged since initial commit).

## Main Theorems Proved in Lean 4

All four challenge statements fixed in `ComparatorChallenges/ThomsonN9.lean` are proved in `ThomsonN9/Solution.lean` on pinned **Lean `v4.34.1`** and **Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`**:

| Lean Theorem | Statement | Axioms |
|---|---|---|
| `ThomsonN9.thomson_nine_M0` | $\forall x \in \mathrm{SphereConfig}\;9,\; 18 \le E(x)$ | `[propext, Classical.choice, Quot.sound]` |
| `ThomsonN9.thomson_nine_M1` | $\forall x \in \mathrm{SphereConfig}\;9,\; 189/8 \le E(x)$ | `[propext, Classical.choice, Quot.sound]` |
| `ThomsonN9.thomson_nine` | $\exists z \in (0,1),\; \forall x \in \mathrm{SphereConfig}\;9,\; E(\mathrm{triCapPrism}\;z) \le E(x)$ | `[propext, Classical.choice, Quot.sound]` |
| `ThomsonN9.thomson_nine_unique` | Every global minimizer equals $g \circ \mathrm{triCapPrism}\;z \circ \sigma$ for $g \in O(3)$, $\sigma \in S_9$, $z \in (0,1)$ | `[propext, Classical.choice, Quot.sound]` |
| `ThomsonN9.thomson_nine_main` | Strengthened outer-quantified theorem: $\exists z^* \in [z^*_{\mathrm{lo}}, z^*_{\mathrm{hi}}]$ ($\mathrm{critGap}(z^*)=0$) proving global optimality and $E(x)=E(\mathrm{TTP}(z^*)) \iff x \in (O(3)\times S_9)\cdot\mathrm{TTP}(z^*)$ | `[propext, Classical.choice, Quot.sound]` |

## Proof Overview (Two-Certificate Architecture)

The proof splits at the smallest pairwise inner product $m = \min_{i < j} \langle x_i, x_j \rangle = -9/10$:

1. **Case 1 ($m \le -9/10$, `StageB/SlabCert.lean`):** A single $(2,7)$-typed three-point SDP certificate ($M=6, K=6$, scale $2^{72}$) proves $E(x) \ge 25.76553265\ldots > E_{\mathrm{ttp,hi}} = 25.7599865312698317$ (margin $> 5.54 \times 10^{-3}$), excluding all configurations with a nearly antipodal pair.
2. **Case 2 ($m \ge -9/10$, `StageB/CapCert.lean` $\to$ `RigidityL4.lean` $\to$ `LocalMinL6.lean`):**
   - A single $S_3$-invariant degree-$18$ three-point SDP certificate ($M=10, K=10$, scale $2^{152}$, verified across **19 parallel 2D-Kronecker slices** via binary bit-tries) gives a certified lower bound within $1.2 \times 10^{-17}$ of $E(\mathrm{triCapPrism}\;z^*)$ ($\Delta_{\mathrm{cap}} = 1.48 \times 10^{-16}$ below our rational upper bound $E_{\mathrm{ttp,hi}}$).
   - A $7$-piece degree-$37$ Bernstein polynomial certificate (`CapCertBernData.lean`) forces every pairwise inner product within $\rho = 10^{-4}$ of one of the six inner-product curves $\nu_0(z^*), \dots, \nu_5(z^*)$ of `triCapPrism z*`.
   - Exact $3$- and $4$-point Gram-determinant bitmasks plus a **28-leaf** symmetry-broken DFS proof tree (`RigidityL4.lean`) identify the unique $S_9$ orbit, and the quantitative Procrustes bound (`TableB5Chain.chain_convert_A`, $C_A \le 18.96$) enters a Frobenius ball of radius $1/500$.
   - IVT isolation of $z^*$ (width $10^{-18}$), compact $O(3)$ rotational gauge fixing, exact criticality, an algebraic Bregman–Young quadratic bound, and a $27\times 27$ integer-Cholesky Hessian bound ($\mu \ge 37/1000$) yield $E(y) - E(P) \ge \frac{1}{30}\sum_i \|g(y_i) - P_i\|^2$, concluding global optimality and $O(3) \times S_9$ uniqueness.

## Verification Summary

- **`bash formal/lean/scripts/check.sh`** — exits `0`:
  - `SHA256SUMS.txt` file-identity check passes across all tracked files in `formal/lean/`;
  - `0` forbidden tokens in `ThomsonN9/Solution.lean` (across all 45 project modules in the dependency cone, the only hits are `maxHeartbeats`, `maxRecDepth`, and `linter.*` switches; zero `sorry`, `native_decide`, `ofReduceBool`, `trustCompiler`, `axiom`, `opaque`, `unsafe`, `partial`, or macros);
  - `lake build ThomsonN9 ComparatorChallenges` passes (`8,972` jobs; `4` expected `sorry`s in `ComparatorChallenges`, `0` in `Solution.lean`);
  - `#print axioms` strict whitelist confirms only `[propext, Classical.choice, Quot.sound]` for all 4 challenge theorems, `thomson_nine_main`, and both admissibility lemmas;
  - `scripts/compare_statements.py` (`SKIP = set()`) confirms **36/36** challenge constants match verbatim (`STATEMENT COMPARISON: OK`, digest `bafcdc5e...35c9`).
  - *Scope note:* Checked on the reference Lean `v4.34.1` kernel (`compare_statements.py` plays the role of `Comparator` for statement fidelity; running `Lean Comparator` and a second kernel such as `nanoda` is planned for public release).
- **`bash formal/lean/scripts/negative-control.sh`** — exits `0` (`NEGATIVE CONTROL (a) OK` against `Solution.tsv` and `NEGATIVE CONTROL (b) OK` kernel rejection of tampered `decide +kernel` certificate).
- **Stage A independent 50-digit check (`python3 numerics/bounds/stage_a_closure.py`)** — exits `0` (`closed = true`, `uniqueness_proved = true`, 5/5 negative controls).

## Repository Layout

```text
thomson-n9/
├── README.md                  This overview
├── REPRODUCE.md               Full reproduction instructions
├── GAP-REPORT.md, PROGRESS.md Round-by-round research and verification logs
├── paper/                     arXiv LaTeX source (main.tex), BibTeX, figures, submission tarball
├── info/THEOREM_MAP.md        Paper-to-Lean theorem & line-number index
├── formal/lean/               Self-contained Lake package (Lean v4.34.1, Mathlib d13f23b7; 45 cone modules, 20,327 lines)
│   ├── ComparatorChallenges/  Fixed challenge statements (unmodified since initial commit)
│   ├── ThomsonN9/Solution.lean  Proofs of M0, M1, thomson_nine, thomson_nine_unique, thomson_nine_main (818 lines)
│   ├── ThomsonN9/StageB/      32 Stage B modules (1.75 MB, 12,880 lines, 57 decide +kernel sites)
│   └── scripts/               check.sh, CheckAxioms.lean, compare_statements.py, negative-control.sh
├── certificates/              Exact integer/rational SDP certificates
├── numerics/                  SDP solvers, Stage A closure verifier, Lean exporters
└── notes/                     Design decisions log decisions.md (D1–D106) and strategy notes
```

## Quick Verification Commands

```sh
# Lean 4 full verification gate (build + token scan + axioms + 36/36 statement comparison)
bash formal/lean/scripts/check.sh
bash formal/lean/scripts/negative-control.sh

# Independent Stage A exact Fraction + 50-dps interval-arithmetic verification
python3 numerics/bounds/stage_a_closure.py
```

## References

- J. J. Thomson (1904), *On the structure of the atom*, Phil. Mag. 7, 237–265.
- C. Bachoc, F. Vallentin (2008), *New upper bounds for kissing numbers from semidefinite programming*, J. Amer. Math. Soc. 21, 909–924.
- H. Cohn, J. Woo (2012), *Three-point bounds for energy minimization*, J. Amer. Math. Soc. 25, 929–958.
- L. Kryvonos, L. Liehr, M. A. Taylor (2026), *Energy minimization for eight points on the sphere*, arXiv:2609.22077.
- Vals AI (2026), *The pentagonal bipyramid is the unique minimiser of the Coulomb energy of seven points on the sphere*, https://github.com/huwngtran/thomson-n7-lean.

## License

Licensed under the [Apache License, Version 2.0](LICENSE) (Copyright 2026 Yang Li).
