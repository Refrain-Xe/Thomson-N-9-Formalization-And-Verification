# Theorem Map: Paper Claims to Lean 4 Declarations

Every declaration below is checked by the Lean 4 kernel (`leanprover/lean4:v4.34.1`, Mathlib `d13f23b7`) with zero `sorry`s, zero `native_decide`, and only the three standard axioms `[propext, Classical.choice, Quot.sound]`.

## 1. Fixed Challenge Statements and Strengthened Main Theorem (`formal/lean/ThomsonN9/Solution.lean`)

All 36 declarations of `ComparatorChallenges/ThomsonN9.lean` are matched verbatim under `pp.all` + `pp.universes` by `scripts/compare_statements.py` (`SKIP = set()`, sha256 `bafcdc5ef8cba6cd31268f3c91bb00bb64ee8907a4c0b58791617a864ab735c9`), and `Solution.lean` additionally exports `ThomsonN9.thomson_nine_main` matching Theorem 1.1 verbatim.

| Mathematical Object / Claim | Lean Declaration | File & Line (`formal/lean/ThomsonN9/`) |
|---|---|---|
| Euclidean space $\mathbb{R}^3$ | `ThomsonN9.R3` | `Solution.lean:86` |
| Admissible $n$-point unit-sphere configurations | `ThomsonN9.SphereConfig` | `Solution.lean:90` |
| Coulomb energy $\sum_{i<j}\|x_i - x_j\|^{-1}$ | `ThomsonN9.coulombEnergy` | `Solution.lean:94` |
| Cylindrical coordinates $(\rho,\theta,h)$ | `ThomsonN9.cyl` | `Solution.lean:98` |
| $D_{3h}$ tricapped trigonal prism `triCapPrism z` | `ThomsonN9.triCapPrism` | `Solution.lean:103` |
| Milestone M0 ($E(x) \ge 36/2 = 18$) | `ThomsonN9.thomson_nine_M0` | `Solution.lean:212` |
| Milestone M1 ($E(x) \ge 189/8 = 23.625$) | `ThomsonN9.thomson_nine_M1` | `Solution.lean:475` |
| **Challenge Target (Global Optimality)** | `ThomsonN9.thomson_nine` | `Solution.lean:696` |
| **Challenge Target ($O(3)\times S_9$ Uniqueness)** | `ThomsonN9.thomson_nine_unique` | `Solution.lean:722` |
| **Theorem 1.1 Verbatim ($\exists z^* \in [z^*_{\mathrm{lo}}, z^*_{\mathrm{hi}}]$, `critGap` $=0$, optimality & $\iff$ uniqueness)** | `ThomsonN9.thomson_nine_main` | `Solution.lean:764` |

## 2. Stage B Proof Spine (`formal/lean/ThomsonN9/`)

| Paper Section | Mathematical Step | Lean Declaration | File & Line (`formal/lean/ThomsonN9/`) |
|---|---|---|---|
| §4.1 | Three-point spherical kernels $Q_k(u,v,t)$ | `StageB.Q3` | `StageB/ThreePoint.lean:141` |
| §4.1 | Three-point Gram positivity $\det G \ge 0$ | `StageB.detG_nonneg_of_unit` | `StageB/ThreePoint.lean:86` |
| §7.1 | Four-point linear dependence $\det_4 = 0$ in $\mathbb{R}^3$ | `StageB.det4_eq_zero_of_unit` | `StageB/ThreePoint.lean:105` |
| §4.1 (Lemma 4.1) | Three-point harmonic positivity $\sum_{i\in S}\sum_{j,l} h \ge 0$ | `StageB.PolyKron.sum_harmListEv_nonneg` | `StageB/PolyKron.lean:1428` |
| §5.1 | $(2,7)$-typed slab assembly identity | `StageB.slab_assembly_9` | `StageB/ThreePoint.lean:770` |
| §6.1 | $S_3$-invariant cap assembly identity | `StageB.cap_assembly_9` | `StageB/ThreePoint.lean:336` |
| §9.1 | $3\text{D}$ Kronecker polynomial zero lemma | `StageB.PolyKron.eq_zero_of_kev3_zero` | `StageB/PolyKron.lean:417` |
| §9.1 | Binary bit-trie `Trie ℤ` & $2\text{D}$-Kronecker multi-slice zero lemma | `StageB.PolyKronFast.eq_zero_of_kev2_slices` | `StageB/PolyKronFast.lean:559` |
| §6.2 | Bernstein polynomial nonnegativity on $[u_1/u_2, w_1/w_2]$ | `StageB.PolyKron.BPiece.nonneg` | `StageB/PolyKron.lean:184` |
| **§5.2 (Case 1)** | **Slab exclusion ($m \le -9/10 \implies E(x) > E_{\mathrm{ttp,hi}}$)** | `StageB.SlabCert.slab_exclusion` | `StageB/SlabCert.lean:732` |
| §6.1 | Cap slack polynomial identity (via 19 Kronecker slices) | `StageB.CapCert.id_slack` *(private)* | `StageB/CapCert.lean:205` |
| §6.1 | Cap 1D minorant $H(t) \le (1+R_2)\varphi(t)$ on $[-9/10, 1)$ | `StageB.CapCert.minorCap_bound` *(private)* | `StageB/CapCert.lean:415` |
| §6.2 | $7$-piece Bernstein exclusion outside $6$ $y$-windows | `StageB.CapCert.y_in_tube_of_Peps_neg` *(private)* | `StageB/CapCert.lean:474` |
| **§6.2 (Case 2a)** | **Cap tube forcing ($m \ge -9/10, E \le E_{\mathrm{ttp,hi}} \implies \mathrm{TubePremise}$)** | `StageB.CapCert.cap_tube_forcing` | `StageB/CapCert.lean:565` |
| §7.1 | $3$- & $4$-point Gram masks + $28$-leaf complete $K_9$ DFS | `StageB.RigidityL4Data.{tri_sound_ok,k4_sound_ok,leaves_iso_ok,l4_k9_complete}` | `StageB/RigidityL4Data.lean:204-207` |
| §7.2 | Quantitative Procrustes alignment (constant $C_{A,\mathrm{hi}} \le 18.96$) | `TableB5Chain.chain_convert_A` | `TableB5Chain.lean:379` |
| **§7.2 (Case 2b)** | **Combinatorial rigidity & Procrustes ball ($\|\cdot\|_F \le 1/500$)** | `StageB.RigidityL4.rigidity_to_ball` | `StageB/RigidityL4.lean:790` |
| §2.2 | Coordinate bridge (`cyl` formula $= \mathrm{ttpPt}\;z\;i$ / `triCapPrism z = ttpPt z`) | `StageB.LocalMinL6.cyl_triCapPrism_eq_ttpPt` / `ThomsonN9.triCapPrism_eq_ttpPt` *(private)* | `StageB/LocalMinL6.lean:71` / `Solution.lean:638` |
| §2.2 | IVT stationary height $z^* \in [z^*_{\mathrm{lo}}, z^*_{\mathrm{hi}}]$ & $E(\mathrm{TTP}(z^*)) \le E_{\mathrm{ttp,hi}}$ | `StageB.LocalMinL6.exists_z_star` | `StageB/LocalMinL6.lean:321` |
| §8.1 | Compact $O(3)$ rotational gauge fixing | `StageB.LocalMinL6.exists_gauge` | `StageB/LocalMinL6.lean:627` |
| §8.2 | Exact criticality at $z^*$ | `StageB.LocalMinL6.ttp_critical` | `StageB/LocalMinL6.lean:378` |
| §8.2 | Algebraic Bregman–Young quadratic lower bound | `StageB.LocalMinL6.breg_ge_quad` | `StageB/LocalMinL6.lean:490` |
| §8.3 | $27\times 27$ integer-Cholesky penalized Hessian bound ($\mu \ge 37/1000$) | `StageB.LocalMinL6.hessian_lower_bound` | `StageB/LocalMinL6.lean:1576` |
| §7.2 | Matrix $Q \in O(3)$ to Lean linear isometry `R3 ≃ₗᵢ[ℝ] R3` | `StageB.LocalMinL6.iso_of_orthogonal` | `StageB/LocalMinL6.lean:2022` |
| **§8.3 (Case 2c)** | **Strict local minimality & equality rigidity ($\implies$) on ball $1/500$** | `StageB.LocalMinL6.local_min_ball` | `StageB/LocalMinL6.lean:1780` |
| §3 | Assembly helper (low energy $\implies$ aligned inside $1/500$ ball) | `ThomsonN9.low_energy_to_ball` *(private)* | `Solution.lean:656` |

## 3. Kernel Decision Sites (`decide +kernel`)

Total `decide +kernel` invocations in the proof dependency cone: **57**
(`SlabCertData`: 15, `CapCertHarmData`: 2, `CapCertBernData`: 9, `CapCertSosData`: 6, `CapCertSosSlice{M9..9}`: 19, `RigidityL4Data`: 4, `LocalMinL6Data`: 2). Zero occurrences of `native_decide`.
