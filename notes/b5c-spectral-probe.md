# b5c-spectral-probe.md — R16B B5c 谱夹逼三件零入库并行探针件

任务锚：b5c-spectral-probe（R16B，campaign dwfrun-f9904baf 第 11 轮，D67 裁决 2）。
定位：**零 Lean 件入库、零求解、纯 notes 产出**——预研件（notes/b5-core-study.md，
9d40343）§5 论证 3 的落地：『B5c 的探针（谱夹逼三件）不依赖 B5a/B5b 的产出，
可随时以独立探针形式插入，建议作为 B5a 施工期间的并行探针任务』。本件对
预研 §2.4 未跑项 ③④⑥＋§3.1 极分解纯代数（R3）＋§3.1.3 Gershgorin 可改造
候选共五组探针给出**三档判定（现成／可改造／缺位自建）＋实测证据**，并据此
收紧 B5c ≥800 行工程量估计、更新 B5b/B5c/B3 排期建议。

诚实口径（全文适用，R15C 同款）：
- **已跑**＝本会话在 thomson-n9/formal/lean 下亲跑且日志在 /tmp 留档（每条带路径）；
  探针＝`lake env lean` 编译验证（example/#check），**探针编译通过 ≠ 证明完成**——
  本件不含任何证明本体入库；
- **未跑**＝本会话没有执行（如实标注，不做推断性『应该可以』）；
- 迭代史口径：/tmp 日志为**终版覆盖式**（探针 1–5 分别经 5/5/6/3/3 版迭代收敛，
  中间版不留档），摩擦点清单为亲历记录（§各节『摩擦』小节，工程化输入）；
- 本件不出现『证明完成』『本体入 Lean』类越权陈述——所有结论均系探针性质。

版本口径：Mathlib @ **d13f23b723b8a846827a245b89c10fc7d3f11612**（本仓
formal/lean/lake-manifest 锚定），toolchain `leanprover/lean4:v4.34.1`
（/tmp/r16b_final_pass.log 头部记录）。与 R15C 预研件、D67 设计探针同一 rev。

零求解声明：本任务零求解（**heavySolves = 0**，零重求解；纯 notes＋探针产出，
不触四账本、endgame.json、certificates、typed_ladder、挑战件与 references；
零 formal/lean/ThomsonN9/ 入库——G7 守卫见 numerics/bounds/r16_b5c_gate.py）。

---

## §P1 探针：CFC.sqrt 保 IsSelfAdjoint／特征值交换性 API（预研 §2.4③，R2 中风险消解）

**三档判定：现成**（自伴面例走通 5 行本体；特征值交换面例走通 charpoly 谱映射链，
带实例路径摩擦）。

**grep 面**（已跑 /tmp/r16b_grep_cfc.log，两面：[A] CFC 全目录文件清册 12 件＋
[B] sqrt 声明清单 45 条）。grep 段头转录（与日志逐字一致）：

```
== [B] P1: 'sqrt' theorem/def declarations in CFC dir (grep -n 'theorem\|lemma\|def' lines containing sqrt) ==
```

关键定位（均 [B] 段逐条在档）：

| API | 位置 | 面向 |
|---|---|---|
| `CFC.sqrt_eq_cfc : sqrt a = cfc (⇑NNReal.sqrt) a` | Rpow/Basic.lean:638 | sqrt＝cfc 桥 |
| `cfcₙ_star : cfcₙ (fun x ↦ star (f x)) a = star (cfcₙ f a)` | CStarAlgebra/…/NonUnital.lean:436 | **star 保持**（自伴面的核心） |
| `cfc_star`（unital 版） | CStarAlgebra/…/Unital.lean:541 | 同上 |
| `cfc_nnreal_eq_real : cfc f a = cfc (fun x ↦ f x.toNNReal) a` | CStarAlgebra/…/Instances.lean:409 | ℝ≥0 函数→ℝ 函数桥 |
| `Matrix.IsHermitian.cfc_eq : cfc f A = hA.cfc f` | Analysis/Matrix/HermitianFunctionalCalculus.lean:143 | **预研漏定位的关键文件**：厄米阵 CFC 实例＋谱定理实现 |
| `Matrix.IsHermitian.charpoly_cfc_eq : (cfc f A).charpoly = ∏ i, (X - C (f (hA.eigenvalues i)))` | 同文件 :152 | **谱映射定理（charpoly 层）**＝特征值交换性 |

（HermitianFunctionalCalculus.lean 为本探针新发现：预研 §2.4 标注『CFC.sqrt 的
IsSelfAdjoint/特征值交换性 API……完全未查』——本组消解。）

**使用级例**（已跑 /tmp/r16b_probe1_cfc.log，exit_code=0，终版 24.6s，
源 /tmp/r16b_probe1_cfc.lean，含 5 条 #check＋3 例）：
- 例 1（主目标）：`M.IsHermitian → 0 ≤ M → (CFC.sqrt M)ᴴ = CFC.sqrt M`——
  本体 5 行（`cfcₙ_star`＋ℝ≥0 上 star 平凡＋`Matrix.star_eq_conjTranspose` 归位）；
- 例 2（特征值交换面）：`(CFC.sqrt M).charpoly = ∏ i, (X - C ((fun x ↦ NNReal.sqrt x.toNNReal) (eig i)))`
  ——链条 `sqrt_eq_cfc → cfc_nnreal_eq_real → charpoly_cfc_eq`；
- 例 2b（点态胶水）：`(fun y ↦ NNReal.sqrt y.toNNReal : ℝ → ℝ) x = Real.sqrt x`
  （0 ≤ x 时；`Real.coe_sqrt`＋`Real.coe_toNNReal`）。

**摩擦**（工程化输入）：①`⇑NNReal.sqrt` 是不透明 coe（pp.explicit 亲见为
OrderIso FunLike，R=ℝ≥0 口径），手写复述 `fun x => ↑(NNReal.sqrt x.toNNReal)`
不被认作同一项——须整体经 `cfc_nnreal_eq_real` 换 ℝ→ℝ 函数；②该 rw 链的实例
路径统一在默认 200000 心跳下超时，实测 `set_option maxHeartbeats 2000000` 后
通过（探针 1 迭代 5 版的主因）；③`ℝ≥0` 记号需 `open scoped NNReal`（探针 v1
亲历被解析为 Type 层 `≥`）。

**未跑项（如实）**：eigenvalues（函数口径 n → ℝ）与 sqrt 的**逐点值交换**
（例 2 已给 charpoly 层谱映射；`roots_charpoly_eq_eigenvalues` 对接成
Multiset.map 层陈述未单独跑——非阻断，工程化时 ~20 行内）；`CFC.sqrt_mul_sqrt_self`
（W·W=被开方阵）R15C 探针 1 P5 已验（/tmp/r15c_probe1_api.log 在盘），本组未重跑。

---

## §P2 探针：对称阵算子范数＝谱极值（Rayleigh 极值特征化）（预研 §2.4④，R1 高风险半面消解）

**三档判定：可改造（接近现成）**——预研『缺位自建（中件）』**升级**：算子层
Rayleigh 极值特征化整文件在场，矩阵层 L2 算子范数 scoped 实例在场；自建面收窄
为『矩阵↔算子搬运＋范数比较胶水』小件。

**grep 面**（已跑 /tmp/r16b_grep_opnorm.log，五面 [A]–[E]）。核心发现：

| API | 位置 | 面向 |
|---|---|---|
| `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient : ‖T‖ = ⨆ x, |T.rayleighQuotient x|` | Analysis/InnerProductSpace/Rayleigh.lean:120 | **Rayleigh 极值特征化本体**（对称算子） |
| `ContinuousLinearMap.spectralRadius_eq_nnnorm : spectralRadius 𝕜 T = ‖T‖₊` | Rayleigh.lean:182 | 自伴谱半径＝范数 |
| `ContinuousLinearMap.opNorm_le_of_re_inner_le` | InnerProductSpace/LinearMap.lean:409 | 内积上界⇒范数上界 |
| `Matrix.l2_opNorm_toEuclideanCLM : ‖toEuclideanCLM A‖ = ‖A‖` | Analysis/CStarAlgebra/Matrix.lean:242 | 矩阵↔算子范数恒等 |
| `Matrix.inner_toEuclideanCLM : ⟪x, toEuclideanCLM A y⟫ = x ⬝ᵥ A *ᵥ y` | 同文件 :136 | 矩阵二次型↔算子内积 |
| `Matrix.spectrum_toLpLin : spectrum 𝕜 (toLpLin p p A) = spectrum 𝕜 A` | Analysis/Matrix/Spectrum.lean:40 | 矩阵谱＝算子谱 |
| （scoped 实例族 `Matrix.Norms.L2Operator`：NormedRing/CStarRing/…） | CStarAlgebra/Matrix.lean:268–311 | 矩阵 L2 范数代数结构 |

grep 证据转录（与 /tmp/r16b_grep_opnorm.log 逐字一致）：

```
== [B] P2: Rayleigh anywhere in Mathlib (content, case-insensitive) ==
```
（[B] 段命中即 Rayleigh.lean 整文件——预研 §2.4 『对称阵算子范数＝最大特征值
绝对值……grep 一轮未命中，但搜索词有限，标注未定位』——本组以 rayleigh 为
关键词命中消解；）
```
== [E] P2: spectralRadius API touching matrices or IsSelfAdjoint ==
```
（[E] 段唯一命中 `Rayleigh.lean:182 spectralRadius_eq_nnnorm`。）
另 [A] 段：Analysis/Matrix/*.lean 的 opNorm 声明仅 `linfty_opNorm` 族
（Normed.lean:284–463，ℓ∞ 诱导范数）——矩阵层 opNorm↔eigenvalue 直接桥
**确认缺位**（与预研判断一致）；[C] 段：`InnerProductSpace/MatrixSpectrum.lean`
文件名缺位（实际谱理论文件为 Analysis/InnerProductSpace/Spectrum.lean＋
SingularValues.lean）；[D] 段：全 Analysis/＋LinearAlgebra/ 同时含 opNorm 与
eigenvalue 内容的文件恰为 Rayleigh.lean＋Analysis/Matrix/Order.lean 两件。

**使用级例**（已跑 /tmp/r16b_probe2_rayleigh.log，exit_code=0，终版 4.3s，
源 /tmp/r16b_probe2_rayleigh.lean，含 7 条 #check＋1 例）：
- 例 1（主目标·自建最小路线）：`M.IsHermitian → (∀ v : EuclideanSpace ℝ n,
  |v ⬝ᵥ (M *ᵥ v)| ≤ t·‖v‖·‖v‖) → ‖M‖ ≤ t`（`open scoped Matrix.Norms.L2Operator`
  下 L2 算子范数）——全链 ~30 行本体走通：`l2_opNorm_toEuclideanCLM`（矩阵范数
  ＝算子范数）→ `isSymmetric_toEuclideanLin_iff`（厄米⇒对称桥，Analysis/Matrix/
  Hermitian.lean:56）→ `norm_eq_iSup_rayleighQuotient`（Rayleigh 特征化）→
  `ciSup_le` 逐点压平＋`inner_toEuclideanCLM` 二次型搬运收尾。

**摩擦**：`ciSup_le` 在本 rev 首显式参即 ∀ 上界式（不收 BddAbove 证）；零向量
分支与除法分支需 `by_cases`；Rayleigh 商的 `‖x‖^2` 与 `‖x‖·‖x‖` 归一 `ring`。

**未跑项（如实）**：`‖M‖₂op = max |eigenvalue|` 的**直接等式**（谱半径链
`l2_opNorm→CLM 调 spectralRadius_eq_nnnorm→spectrum_toLpLin→eigenvalues`，
各段在场未拼装——探针例 1 已覆盖 B5c 所需单向上界用法，等式非必需）；
Frobenius↔L2op 范数比较件（`‖A‖₂op ≤ ‖A‖_F`，B5c 装配步依赖）**未探**——
本组不判档，留 B5c 施工前探（见 §6 余量）。

---

## §P3 探针：eigenvalues_le 类单调/夹逼 API＋eigenvalues 与 CFC.sqrt 交换性（预研 §2.4⑥）

**三档判定：夹逼面＝可改造（自建小件，路线走通）；`eigenvalues_le` 直接名＝确认缺位。**

**grep 面**（已跑 /tmp/r16b_grep_eigmono.log，五面 [A]–[E]）。grep 证据转录
（与日志逐字一致）：

```
== [A] P3: 'eigenvalues_le'-named declarations anywhere in Mathlib ==
-- end [A] --
```
（[A] 段空＝全库无 `eigenvalues_le` 命名声明——预研 §2.4 『grep 未命中（未定位）』
升格为**确认缺位**，需自建夹逼小件；）[B] 段：单调面在场的仅有
`eigenvalues₀_antitone`（Spectrum.lean:63，排序口径）与
`LinearMap.IsSymmetric.eigenvalues_antitone`（InnerProductSpace/Spectrum.lean:312）；
[ D] 段空＝sqrt↔eigenvalues 直接命名交换性 API 缺位（经 P1 的 charpoly_cfc_eq
谱映射链替代，见 §P1 例 2）；[E] 段全文转录 `inner_product_apply_eigenvector`
（InnerProductSpace/Spectrum.lean:405）＋`eigenvalue_nonneg_of_nonneg`（:409，
**二次型非负⇒特征值非负桥**，预研未定位）＋`eigenvalue_pos_of_pos`（:418）。

**使用级例**（已跑 /tmp/r16b_probe3_eig.log，exit_code=0，终版 3.9s，
源 /tmp/r16b_probe3_eig.lean，含 8 条 #check＋1 例）：
- 例 1（主目标·夹逼）：`M.IsHermitian → (∀ v : n → ℝ, |v ⬝ᵥ (M *ᵥ v)| ≤ t·(v ⬝ᵥ v))
  → ∀ i, |hM.eigenvalues i| ≤ t`——全链 ~35 行本体走通：
  `eigenvalues_mem_spectrum_real`（Spectrum.lean:83，eig i ∈ spectrum ℝ M）→
  `Matrix.spectrum_toLpLin`（矩阵谱＝算子谱）→
  `Module.End.hasEigenvalue_iff_mem_spectrum`（Eigenspace/Basic.lean:526，有限维
  谱＝特征值）→ 特征向量上二次型＝μ·‖v‖²（`real_inner_smul_right`＋
  `EuclideanSpace.inner_eq_star_dotProduct` PiL2.lean:216 搬运）→
  `dotProduct_self_eq_zero` 正性除法收尾。

**摩擦**（工程化输入，本组迭代 6 版的主因）：①`WithLp` 在本 rev 是**单字段
结构**（非类型同义）——EuclideanSpace 向量到纯函数需 `WithLp.ofLp`，零性经
`WithLp.ofLp_eq_zero`（WithLp.lean:170）；②`set` 抽象后 simp 会重新引入
`v.ofLp` 形式，需 `rw [← hw]` 回写；③根命名空间陷阱：`eigenvalue_nonneg_of_nonneg`、
`inner_product_apply_eigenvector`、`dotProduct_comm`、`dotProduct_self_eq_zero`
均**无** `LinearMap.`/`Matrix.` 前缀（探针 v2/v3 亲历 unknown）；④
`Matrix.toLpLin` 需双范数实参 `toLpLin 2 2 M`。

**未跑项（如实）**：`LinearMap.IsSymmetric.eigenvalues_antitone` 排序路线
（例 1 走特征向量路线已足）；`B ⪯ tI ⇒ eig ≤ t` 的 `Matrix.PosSemidef` 口径
对接（预研 §3.1 缓解案——二次型口径已走通，PosSemidef 口径桥留 B5c 施工时定）；
P1 例 2 的 charpoly 谱映射与例 1 夹逼的**合并件**（特征值 of CFC.sqrt M 的
显式夹逼定理）未合并跑——两半各自走通，拼装属工程化。

---

## §P4 探针：极分解纯代数小件（预研 §3.1 步骤 2，R3 低风险前置消解）

**三档判定：现成（双例走通）**——R3『低』风险预判实测确认。

**grep 面**：极分解缺位三面证据系 R15C 已跑（/tmp/r15c_grep_polar.log 在盘
复核：[D][E][F] 三面空＝全 Mathlib 无 `Matrix.polar`/`polarDecomp` 标识符），
本组不重跑（口径：R15C 同 rev 同仓 grep，零漂移）；本组 grep 增量＝
NonsingularInverse.lean/Mul.lean 的消去引理定位（探针 #check 面五条：
`Matrix.isUnit_iff_isUnit_det` :127、`Matrix.transpose_nonsing_inv` :202、
`Matrix.mul_nonsing_inv` :211、`Matrix.nonsing_inv_mul` :217、
`Matrix.transpose_mul` Data/Matrix/Mul.lean:1174）。

**使用级例**（已跑 /tmp/r16b_probe4_polar.log，exit_code=0，终版 3.9s，
源 /tmp/r16b_probe4_polar.lean，含 5 条 #check＋2 例）：
- 例 1（主目标，任务书原式）：`Wᵀ = W → W * W = (1 + A) * (1 + A)ᵀ → IsUnit W →
  (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ = 1`——纯代数 ~15 行本体（`transpose_mul`
  开转置＋`transpose_nonsing_inv` 搬 (W⁻¹)ᵀ=(Wᵀ)⁻¹＋代入 hWW 两次消去）；
- 例 2（正交性另一半）：`R * Rᵀ = 1 → Rᵀ * R = 1`（det 平方=1 →
  `IsUnit.of_mul_eq_one` → Rᵀ = R⁻¹ → 双侧）——O(3) membership 两面齐。

**摩擦**：①`Matrix.mul_nonsing_inv` 族 **A 为显式实参**且实例路径与陈述面不
字节对齐，`rw [Matrix.mul_nonsing_inv hdet]` 直接重写不中——须先
`have h1 : W * W⁻¹ = 1 := by simp [Matrix.mul_nonsing_inv W hdet]` 成局部等式
再 rw（B5a 施工同型摩擦，R15C §2.3 摩擦 1 同族）；②结合律搬运方向敏感：
`mul_assoc` 全局重写先匹配外层，中段需 `conv_lhs => arg 2` 定位后定向重写。

**联动结论**：W := CFC.sqrt ((I+A)(I+A)ᵀ) 的三前提两缺一——Wᵀ=W（§P1 例 1
走通）、W·W=(I+A)(I+A)ᵀ（`CFC.sqrt_mul_sqrt_self`，R15C 探针 1 P5 已验）、
IsUnit W（谱夹逼 [§P3] 或 Gershgorin [§P5] 路线）——**R 正交性的代数层全部
就绪，只缺 W 可逆前提的谱面供给**。

**未跑项（如实）**：例 1 例 2 合并成单定理（正交群 `Matrix.orthogonalGroup`
membership 形式陈述）未跑（两面各自走通，拼装属工程化）。

---

## §P5 探针：Gershgorin 可改造候选（预研 §3.1.3，I+B 可逆/正定路线）

**三档判定：现成（lemma 直接可用，注入例走通）。**

**grep 面**（已跑 /tmp/r16b_grep_gershgorin.log，三面 [F][G][H]）。grep 证据
转录（与日志逐字一致）：

```
== [F] P5: Gershgorin.lean full declaration outline ==
12:/-!
30:theorem eigenvalue_mem_ball {μ : K} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
63:theorem det_ne_zero_of_sum_row_lt_diag (h : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < ‖A k k‖) :
73:theorem det_ne_zero_of_sum_col_lt_diag (h : ∀ k, ∑ i ∈ Finset.univ.erase k, ‖A i k‖ < ‖A k k‖) :
-- end [F] --
```
（[F] 段＝LinearAlgebra/Matrix/Gershgorin.lean 全部四声明；[G] 段空＝全库无
外部使用者（文献面薄，可改造需自带胶水）；[H] 段空＝无 strictlyDiagonallyDominant
高层封装，占优假设需自持。三条均**根命名空间**——`Matrix.` 前缀不命中，探针
v1 亲历。）

**使用级例**（已跑 /tmp/r16b_probe5_gershgorin.log，exit_code=0，终版 4.0s，
源 /tmp/r16b_probe5_gershgorin.lean，含 4 条 #check＋3 例）：
- 例 1（I+B 形注入）：`(∀ k, ∑_{j≠k} ‖B k j‖ < ‖1 + B k k‖) → (1 + B).det ≠ 0`
  ——含偏离角换元（1 只在对角，`Matrix.one_apply`＋`Finset.mem_erase`）；
- 例 2（具体数值）：`(!![1, 1/10; 1/10, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0`
  （小扰动单位阵；摩擦：`Matrix.of !![…]` 双层包装不按 rfl 化简，裸 `!![…]`
  型注记直接 rfl——v2 亲历）；
- 例 3（谱夹逼面调用）：对角阵特征值落圆盘——`eigenvalue_mem_ball`＋
  `hasEigenvalue_toLin'_diagonal_iff` 桥（LinearAlgebra/Eigenspace/Matrix.lean:71，
  本组定位）。

**未跑项（如实）**：`‖B‖_F ≤ β < 1 ⇒ 行和非对角和 < 1` 的 Cauchy–Schwarz
逐行胶水（每行 ∑_{j≠k}|B_kj| ≤ √(n−1)·‖B 行‖ ≤ ‖B‖_F ≤ β——**书面推导**，
探针未跑，工程化估 ~30–60 行）；特征值 ≥ 1−β > 0 的**正定**结论（经 §P3 夹逼
路线可得，未合并跑）。B5c 主路线优先谱夹逼（§P3），Gershgorin 作 I+A 可逆的
独立替代路（预研 §3.1.3 定位不变）。

---

## §6 B5c 工程量估计更新（预研 §4 ≥800 行档的收紧）

锚（本会话实测）：探针 2 例 1 本体 ~30 行、探针 3 例 1 ~35 行、探针 4 双例
~30 行（附录 A 全源转录，行数可点）；预研 §4 分档口径维持（≤300／300–800／
≥800，证明本体行数不含 Data 件与门）。

| 步骤 5 子件 | 预研 §4 估计 | 本轮探针后 | 依据 |
|---|---|---|---|
| W 构造（CFC.sqrt）＋Wᵀ=W | 200–300 | **~80–150** | §P1 例 1 本体 5 行＋例 2/2b 谱映射与胶水；实例路径摩擦实测需 maxHeartbeats 放宽（工程化需显式实参化＋instance 指路） |
| R := W⁻¹(I+A) 正交 | （并入上）| **~40–80** | §P4 双例走通（~30 行本体）；合并成 orthogonalGroup membership 单定理增量 |
| 谱夹逼（eig ∈ [1−β, 1+β] 或二次型口径） | ≥300（『无现成 API 面最大』） | **~80–150** | §P3 例 1 全链走通（~35 行）；夹逼陈述＋I+B 代入增量；PosSemidef 口径桥另计 ~50–100（未跑项） |
| 算子范数-特征值桥（‖W−I‖₂ ≤ β） | ≥300 | **~50–120** | §P2 例 1 走通（~30 行）＋Rayleigh 特征化现成；**Frobenius↔L2op 比较件未探**（留余量） |
| 步骤 6 装配 | ≤300 | 维持 ≤300 | 预研 §4 依据不变（R14 同式先例） |

**收紧结论：B5c（步骤 5–6）从预研『≥800 行且方差最大』收紧为 ≈ 450–800 行、
不确定度降档为『中』**——收紧主因＝Rayleigh.lean＋HermitianFunctionalCalculus.lean
两件预研漏定位的底座文件（§P2/§P1 grep 亲验）；维持 800 上界不破的原因＝
①CFC 实例路径摩擦在工程化放大（探针 1 迭代 5 版的实测）②Frobenius↔L2op 比较
件未探③PosSemidef 口径桥未跑（三项如实，见 §P2/§P3 未跑项）。

## §7 对 B5b/B5c/B3 排期的建议更新

1. **B5a → B5b → B5c 串行维持**（D67 裁决 1 口径不变）：本轮探针不改变依赖
   单向性（5 用 2 的可逆前提、3/4 的界）；且探针实测的陈述面摩擦（WithLp
   结构化、根命名空间、A 显式实参）**加重**了『B5a 先定陈述面公共底座』的
   必要性——B5a 若采用 EuclideanSpace/WithLp 口径，§P2/§P3 的搬运例可直接
   复用；若采用纯函数口径，需自持 ofLp 胶水（两可，唯先定）。
2. **B5c 排期风险降级**：R1（高：谱夹逼＋算子范数桥两件中件叠加）→ **中**
   （§P2＋§P3 双面走通，剩余为胶水）；R2（中：CFC 自伴面）→ **低**（§P1 例 1
   现成）。B5c 可在 B5b 完成后按 ≈450–800 行口径排期；若 Frobenius↔L2op 比较
   件探针不利，回退二次型口径弱化（预研 §3.1 缓解案维持有效）。
3. **B5b 增量利好**：其 Frobenius↔trace 恒等式件（预研 §2.2 可改造档）与 B5c
   的 Frobenius↔L2op 比较件同属范数比较族——建议 B5b 施工时一并探
   `Matrix.frobenius_norm_*` 与 L2op 的比较 API，一探两用（本轮未探，如实）。
4. **B3 维持不排**（D61 裁决 1 口径不变），但记录新信息：本轮 grep 亲见
   Rayleigh.lean:202 `LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf`
   （二次型泛函的严格导数）——B3 若未来排期，此为 reApplyInnerSelf 面的现成
   严格导数底座（fderiv² 链式法则 ≥800 行的自建主件判断不变，待议维持）。
5. R16C 收口口径：本件（notes/b5c-spectral-probe.md＋r16_b5c_gate.py 双路由
   ＋包装器＋decisions 执行裁决）为 R16B 自有四件；与 R16A（TableB5Core 族＋
   notes/tableb-lean.md §4）文件集零交叠（D67 并行纪律），r16 家族放行层见
   decisions.md 本轮执行裁决。

## §8 零求解声明与诚实口径（G6 锚）

- **零求解声明：本任务 heavySolves = 0**（字面锚）——零重求解、零 SDP、零新
  数值证书、零账本触碰、endgame.json 零改动（G7 守卫 numerics/bounds/
  r16_b5c_gate.py 以 git status/diff 机器面执行）。
- 全部结论系探针性质：**探针编译通过 ≠ 证明完成**；本件无任何『本体入 Lean』
  宣称；B5 解析本体（步骤 1–6）仍未开工，其可行性陈述以探针证据为界。
- 未跑项汇总（全文『未跑』如实）：§P1 逐点值交换 Multiset 对接；§P2 ‖M‖₂op=
  max|eig| 等式拼装＋Frobenius↔L2op 比较件；§P3 antitone 路线＋PosSemidef
  口径桥＋P1/P3 合并件；§P4 双例合并单定理；§P5 Cauchy–Schwarz 行和胶水＋
  正定结论合并。
- 迭代史：探针 1–5 分别 5/5/6/3/3 版收敛，/tmp 日志为终版覆盖式（同 R15C
  §2.3 口径）；摩擦点已逐组留档（§P1–§P5『摩擦』小节）。

---

## 附录 A：探针源转录（终版，与 /tmp 五源件逐字一致）

### A.1 P1 源（/tmp/r16b_probe1_cfc.lean）

```lean
import Mathlib

/-!
R16B P1 探针源（b5c-spectral-probe §P1）：
CFC.sqrt 保 IsSelfAdjoint ＋ 特征值交换性（charpoly 谱映射）API 使用级核验。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix
open scoped MatrixOrder

-- § API 签名核验（#check 面）----------------------------------------------

#check @CFC.sqrt_eq_cfc                       -- Rpow/Basic.lean:638  sqrt a = cfc (⇑NNReal.sqrt) a
#check @cfcₙ_star                             -- NonUnital.lean:436   cfcₙ (star ∘ f) a = star (cfcₙ f a)
#check @cfc_star                              -- Unital.lean:541      cfc (star ∘ f) a = star (cfc f a)
#check @Matrix.IsHermitian.cfc_eq             -- HermitianFunctionalCalculus.lean:143
#check @Matrix.IsHermitian.charpoly_cfc_eq    -- HermitianFunctionalCalculus.lean:152

-- § 例 1（P1 主目标）：实 PSD 对称阵的 CFC.sqrt 自伴 -------------------------
-- R16B §P1 例 1：sqrt 保自伴（矩阵层陈述 (sqrt M)ᴴ = sqrt M）
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (hnn : 0 ≤ M) : (CFC.sqrt M)ᴴ = CFC.sqrt M := by
  rw [← Matrix.star_eq_conjTranspose]
  have h := cfcₙ_star (f := NNReal.sqrt) (a := M)
  have hstar : (fun x : NNReal ↦ star (NNReal.sqrt x)) = NNReal.sqrt := by
    funext x; simp
  rw [hstar] at h
  exact h.symm

-- § 例 2（P1 特征值交换面）：charpoly 层谱映射 -------------------------------
-- 『sqrt 的特征多项式 = 开方函数逐点作用于特征值的装配』（谱映射定理的直接
-- 推论）。链条＝sqrt_eq_cfc（sqrt = cfc ⇑NNReal.sqrt，R=ℝ≥0 口径）→
-- cfc_nnreal_eq_real（ℝ≥0 函数 → ℝ 函数桥，Instances.lean:409）→
-- charpoly_cfc_eq（谱映射装配）。特征值交换性＝f (eig i) 逐点复合形式。
-- 摩擦点（留档）：⇑NNReal.sqrt 的 coe 不透明（pp.explicit 亲见为 OrderIso
-- FunLike），须整体经 cfc_nnreal_eq_real 换 ℝ→ℝ 函数；该 rw 链在默认
-- 200000 心跳下实例路径统一超时，实测需 set_option maxHeartbeats 放宽。
set_option maxHeartbeats 2000000 in
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (hnn : 0 ≤ M) :
    (CFC.sqrt M).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C
        ((fun x ↦ NNReal.sqrt x.toNNReal : ℝ → ℝ) (hM.eigenvalues i))) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt M hnn, hM.charpoly_cfc_eq _]
  simp

-- § 例 2b（点态胶水，可改造面）：开方函数在非负点与 Real.sqrt 逐点一致 ------
-- （PSD 阵特征值 ≥ 0 时 f (eig i) = Real.sqrt (eig i)：NNReal.coe_sqrt 场。）
example (x : ℝ) (hx : 0 ≤ x) :
    (fun y ↦ NNReal.sqrt y.toNNReal : ℝ → ℝ) x = Real.sqrt x := by
  have h1 : ((x.toNNReal : NNReal) : ℝ) = x := Real.coe_toNNReal x hx
  show (NNReal.sqrt x.toNNReal : ℝ) = Real.sqrt x
  rw [Real.coe_sqrt, h1]
```

### A.2 P2 源（/tmp/r16b_probe2_rayleigh.lean）

```lean
import Mathlib

/-!
R16B P2 探针源（b5c-spectral-probe §P2）：
对称阵算子范数＝谱极值（Rayleigh 极值特征化）——扩面搜索后的使用级核验。
关键发现：Analysis/InnerProductSpace/Rayleigh.lean 整文件在场（预研 §2.4 未定位），
给出算子层 Rayleigh 极值特征化＋谱半径=范数；矩阵层 L2 算子范数 scoped 实例
（Analysis/CStarAlgebra/Matrix.lean，Matrix.Norms.L2Operator）。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix
open scoped Matrix.Norms.L2Operator

-- § API 签名核验（#check 面）----------------------------------------------

#check @ContinuousLinearMap.norm_eq_iSup_rayleighQuotient  -- Rayleigh.lean:120 ‖T‖=⨆|rayleigh|
#check @ContinuousLinearMap.spectralRadius_eq_nnnorm       -- Rayleigh.lean:182 自伴谱半径=范数
#check @ContinuousLinearMap.opNorm_le_of_re_inner_le      -- LinearMap.lean:409
#check @Matrix.l2_opNorm_toEuclideanCLM                    -- CStarAlgebra/Matrix.lean:242
#check @Matrix.inner_toEuclideanCLM                        -- CStarAlgebra/Matrix.lean:136
#check @Matrix.spectrum_toLpLin                            -- Spectrum.lean:40
#check @ContinuousLinearMap.bddAbove_rayleighQuotient      -- Rayleigh.lean:117

-- § 例 1（P2 主目标·自建最小路线）：二次型夹逼 ⇒ L2 算子范数 ≤ t --------------
-- vᵀMv 夹逼（∀ v，|v ⬝ᵥ (M *ᵥ v)| ≤ t·‖v‖²）⇒ ‖M‖₂op ≤ t：
-- 链＝l2_opNorm_toEuclideanCLM（矩阵范数=算子范数）→
-- norm_eq_iSup_rayleighQuotient（Rayleigh 极值特征化）→ 逐点上确界压平。
-- inner_toEuclideanCLM 把矩阵二次型转成算子内积（⟪x, T y⟫ = x ⬝ᵥ M *ᵥ y）。
set_option maxHeartbeats 800000 in
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ v : EuclideanSpace ℝ n, |v ⬝ᵥ (M *ᵥ v)| ≤ t * ‖v‖ * ‖v‖) :
    ‖M‖ ≤ t := by
  set T := toEuclideanCLM (n := n) (𝕜 := ℝ) M with hTdef
  -- 对称性桥：IsHermitian M ⇒ T 对称（Rayleigh 特征化的前提）
  have hsymm : (T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).IsSymmetric := by
    rw [hTdef, coe_toEuclideanCLM_eq_toEuclideanLin, isSymmetric_toEuclideanLin_iff]
    exact hM
  -- 二次型假设搬到算子内积口径
  have hin : ∀ x : EuclideanSpace ℝ n, |(T.reApplyInnerSelf x : ℝ)| ≤ t * ‖x‖ * ‖x‖ := by
    intro x
    have h1 : (inner ℝ x (T x) : ℝ) = x ⬝ᵥ (M *ᵥ x) := Matrix.inner_toEuclideanCLM M x x
    have h2 : (T.reApplyInnerSelf x : ℝ) = (inner ℝ x (T x) : ℝ) := by
      simp [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm]
    rw [h2, h1]
    exact h x
  calc ‖M‖ = ‖(T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ :=
        (Matrix.l2_opNorm_toEuclideanCLM M).symm
    _ = ⨆ x, |T.rayleighQuotient x| := T.norm_eq_iSup_rayleighQuotient hsymm
    _ ≤ t := by
        refine ciSup_le fun x => ?_
        by_cases hx : x = 0
        · simp [hx, ht]
        · have hpos : ‖x‖ ^ 2 > 0 := by positivity
          have hr : T.rayleighQuotient x = (T.reApplyInnerSelf x : ℝ) / ‖x‖ ^ 2 := by
            simp [ContinuousLinearMap.rayleighQuotient]
          have hden : (0:ℝ) < |‖x‖ ^ 2| := abs_pos.mpr (ne_of_gt hpos)
          rw [hr, abs_div, div_le_iff₀ hden]
          calc |(T.reApplyInnerSelf x : ℝ)| ≤ t * ‖x‖ * ‖x‖ := hin x
            _ = t * |‖x‖ ^ 2| := by rw [abs_of_nonneg (by positivity)]; ring
```

### A.3 P3 源（/tmp/r16b_probe3_eig.lean）

```lean
import Mathlib

/-!
R16B P3 探针源（b5c-spectral-probe §P3）：
Matrix.IsHermitian.eigenvalues_le 类单调/夹逼 API ＋ eigenvalues 与 CFC.sqrt
交换性——grep 扩面（eigenvalues_le 直接名缺位；LinearMap.IsSymmetric.eigenvalues_
antitone 单调面在场）＋使用级夹逼例。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix

-- § API 签名核验（#check 面）----------------------------------------------

#check @Matrix.IsHermitian.eigenvalues_mem_spectrum_real    -- Spectrum.lean:83
#check @Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues -- Spectrum.lean:213
#check @Matrix.IsHermitian.det_eq_prod_eigenvalues          -- Spectrum.lean:193
#check @LinearMap.IsSymmetric.eigenvalues_antitone          -- InnerProductSpace/Spectrum.lean:312
#check @eigenvalue_nonneg_of_nonneg                        -- InnerProductSpace/Spectrum.lean:409（根命名空间）
#check @Module.End.hasEigenvalue_iff_mem_spectrum           -- Eigenspace/Basic.lean:526
#check @Matrix.IsHermitian.roots_charpoly_eq_eigenvalues    -- Spectrum.lean:161
#check @inner_product_apply_eigenvector                  -- InnerProductSpace/Spectrum.lean:405（根命名空间）

-- § 例 1（P3 主目标·夹逼）：二次型夹逼 ⇒ 全部特征值 ∈ [−t, t] ----------------
-- ∀ v，|v ⬝ᵥ (M *ᵥ v)| ≤ t·(v ⬝ᵥ v) ⇒ ∀ i，|eigenvalues i| ≤ t。
-- 路线＝eigenvalues_mem_spectrum_real（eig i ∈ spectrum ℝ M）→
-- spectrum_toLpLin（矩阵谱＝算子谱）→ hasEigenvalue_iff_mem_spectrum（有限维
-- 谱＝特征值）→ 特征向量上二次型＝μ·‖v‖²（inner_product_apply_eigenvector 场）
-- → 两侧除以 ‖v‖²（dotProduct_self 正性）收尾。
set_option maxHeartbeats 800000 in
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ v : n → ℝ, |v ⬝ᵥ (M *ᵥ v)| ≤ t * (v ⬝ᵥ v)) :
    ∀ i, |hM.eigenvalues i| ≤ t := by
  -- 谱层夹逼（一次证好）
  have key : ∀ μ ∈ spectrum ℝ M, |μ| ≤ t := by
    intro μ hμ
    rw [← Matrix.spectrum_toLpLin (𝕜 := ℝ) (p := 2)] at hμ
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
    obtain ⟨v, hv1, hv2⟩ := hμ.exists_hasEigenvector
    have heq : (Matrix.toLpLin 2 2 M) v = μ • v := by simpa using hv1
    set w : n → ℝ := (v : n → ℝ) with hw
    have hw0 : w ≠ 0 := by
      intro hc
      apply hv2
      have h0 : (WithLp.ofLp v : n → ℝ) = 0 := by rw [← hw]; exact hc
      exact (WithLp.ofLp_eq_zero _).mp h0
    -- EuclideanSpace 内积＝dotProduct（实域 star 平凡）
    have e1 : (inner ℝ v ((Matrix.toLpLin 2 2 M) v) : ℝ) = w ⬝ᵥ (M *ᵥ w) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]
      rw [← hw]
    have e2 : (inner ℝ v v : ℝ) = w ⬝ᵥ w := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp
      rw [← hw]
    -- 特征方程⟹二次型恒等式：w ⬝ᵥ (M *ᵥ w) = μ·(w ⬝ᵥ w)
    have conv : w ⬝ᵥ (M *ᵥ w) = μ * (w ⬝ᵥ w) := by
      rw [← e1, heq, real_inner_smul_right, e2]
    -- 收尾：|μ|·s ≤ t·s（s = w ⬝ᵥ w > 0）⇒ |μ| ≤ t
    have hnn : 0 ≤ w ⬝ᵥ w := by rw [← e2]; exact real_inner_self_nonneg
    have hnz : w ⬝ᵥ w ≠ 0 := fun hc => hw0 (dotProduct_self_eq_zero.mp hc)
    have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnn (Ne.symm hnz)
    have hle := h w
    rw [conv, abs_mul, abs_of_pos hpos] at hle
    exact (mul_le_mul_iff_of_pos_right hpos).mp hle
  intro i
  exact key _ (hM.eigenvalues_mem_spectrum_real i)
```

### A.4 P4 源（/tmp/r16b_probe4_polar.lean）

```lean
import Mathlib

/-!
R16B P4 探针源（b5c-spectral-probe §P4）：
极分解纯代数小件（预研 §3.1 步骤 2 路线 ~20 行，R3 低风险前置消解）：
Wᵀ = W ∧ W * W = (1 + A) * (1 + A)ᵀ ∧ IsUnit W ⇒ R := W⁻¹ * (1 + A) 正交。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix

-- § API 签名核验（#check 面）----------------------------------------------

#check @Matrix.isUnit_iff_isUnit_det     -- NonsingularInverse.lean:127
#check @Matrix.transpose_nonsing_inv     -- NonsingularInverse.lean:202 (A⁻¹ᵀ = Aᵀ⁻¹)
#check @Matrix.mul_nonsing_inv           -- NonsingularInverse.lean:211（A 显式实参）
#check @Matrix.nonsing_inv_mul           -- NonsingularInverse.lean:217（A 显式实参）
#check @Matrix.transpose_mul             -- Data/Matrix/Mul.lean:1174 ((M * N)ᵀ = Nᵀ * Mᵀ)

-- § 例 1（P4 主目标）：R * Rᵀ = 1 ------------------------------------------------
-- 纯代数：transpose_mul 开 (W⁻¹ * (1 + A))ᵀ，transpose_nonsing_inv 搬 (W⁻¹)ᵀ =
-- (Wᵀ)⁻¹，代入 Wᵀ = W 与平方恒等式 hWW，两次消去收尾。
-- 摩擦点（留档）：①结合律搬运方向敏感——mul_assoc 全局重写先匹配外层，中段
-- 需 conv 定位（arg 2）后定向重写；②mul_nonsing_inv 族 A 为显式实参且实例
-- 路径与陈述面不字节对齐，rw 直接重写不中——需先 have 成局部等式（同陈述面
-- 上下文重释）再 rw（B5a 施工同型摩擦，R15C §2.3 摩擦 1 同族）。
example {n : Type*} [DecidableEq n] [Fintype n] {A W : Matrix n n ℝ}
    (hW : Wᵀ = W) (hWW : W * W = (1 + A) * (1 + A)ᵀ) (hunit : IsUnit W) :
    (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ = 1 := by
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hunit
  have h1 : W * W⁻¹ = 1 := by simp [Matrix.mul_nonsing_inv W hdet]
  have h2 : W⁻¹ * W = 1 := by simp [Matrix.nonsing_inv_mul W hdet]
  have hT : (W⁻¹ * (1 + A))ᵀ = (1 + A)ᵀ * W⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hW]
  calc (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ
      = W⁻¹ * ((1 + A) * ((1 + A)ᵀ * W⁻¹)) := by rw [hT, mul_assoc]
    _ = W⁻¹ * (((1 + A) * (1 + A)ᵀ) * W⁻¹) := by
        conv_lhs => arg 2; rw [← mul_assoc]
    _ = W⁻¹ * ((W * W) * W⁻¹) := by rw [← hWW]
    _ = W⁻¹ * (W * (W * W⁻¹)) := by rw [mul_assoc]
    _ = W⁻¹ * (W * 1) := by rw [h1]
    _ = W⁻¹ * W := by rw [mul_one]
    _ = 1 := h2

-- § 例 2（P4 收尾面）：R * Rᵀ = 1 ⇒ Rᵀ * R = 1（方阵右逆＝左逆）-------------------
-- det 平方 = 1 ⇒ R 可逆（IsUnit.of_mul_eq_one）⇒ Rᵀ = R⁻¹ ⇒ 双侧。
example {n : Type*} [DecidableEq n] [Fintype n] {R : Matrix n n ℝ} (hR : R * Rᵀ = 1) :
    Rᵀ * R = 1 := by
  have hdet2 : R.det * R.det = 1 := by
    have h := congrArg Matrix.det hR
    simp [Matrix.det_mul, Matrix.det_transpose] at h
    exact h
  have hdet : IsUnit R.det := IsUnit.of_mul_eq_one R.det hdet2
  have h3 : R⁻¹ * R = 1 := by simp [Matrix.nonsing_inv_mul R hdet]
  have hinv : R⁻¹ = Rᵀ := by
    calc R⁻¹ = R⁻¹ * 1 := by rw [mul_one]
      _ = R⁻¹ * (R * Rᵀ) := by rw [hR]
      _ = (R⁻¹ * R) * Rᵀ := by rw [mul_assoc]
      _ = 1 * Rᵀ := by rw [h3]
      _ = Rᵀ := by rw [one_mul]
  rw [← hinv, h3]
```

### A.5 P5 源（/tmp/r16b_probe5_gershgorin.lean）

```lean
import Mathlib

/-!
R16B P5 探针源（b5c-spectral-probe §P5）：
Gershgorin 可改造候选（LinearAlgebra/Matrix/Gershgorin.lean 在场）——
『‖B‖ 小 ⇒ I + B 正定/可逆』路线的使用级核验。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix

-- § API 签名核验（#check 面）----------------------------------------------

#check @eigenvalue_mem_ball                   -- Gershgorin.lean:30（圆盘定理，根命名空间）
#check @det_ne_zero_of_sum_row_lt_diag        -- Gershgorin.lean:63（行严格对角占优 ⇒ det ≠ 0）
#check @det_ne_zero_of_sum_col_lt_diag        -- Gershgorin.lean:73（列版本）
#check @Matrix.IsHermitian.det_eq_prod_eigenvalues  -- Spectrum.lean:193（det＝特征值积）

-- § 例 1（P5 使用级·I + B 形注入）：行严格对角占优直接给出 I + B 可逆 ---------
-- 陈述面＝预研 §3.1.3 的『I + B 正定路线』第一步（可逆性）：
-- ∀ k，∑_{j≠k} |B k j| < |1 + B k k| ⇒ (1 + B).det ≠ 0（实域 |·| 即 ‖·‖）。
example {n : Type*} [DecidableEq n] [Fintype n] {B : Matrix n n ℝ}
    (h : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖B k j‖ < ‖1 + B k k‖) :
    (1 + B).det ≠ 0 := by
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  -- 偏离角＝B 的角元（1 只在对角）：逐项换元后直接调用
  have hoff : ∀ j ∈ Finset.univ.erase k, (1 + B) k j = B k j := by
    intro j hj
    have hne : k ≠ j := fun hc => (Finset.mem_erase.mp hj).1 hc.symm
    have h1 : (1 : Matrix n n ℝ) k j = 0 := by
      simp [Matrix.one_apply, hne]
    rw [Matrix.add_apply, h1, zero_add]
  have hd : (1 + B) k k = 1 + B k k := by
    rw [Matrix.add_apply, Matrix.one_apply, if_pos rfl]  -- deprecation 提示无害
  rw [Finset.sum_congr rfl fun j hj => by rw [hoff j hj], hd]
  exact h k

-- § 例 2（P5 使用级·具体数值）：小扰动单位阵经 Gershgorin 判可逆 --------------
-- I + B with B = [[0, 1/10], [1/10, 0]]：行和非对角和 = 1/10 < 1 = 对角。
example : ((!![(1 : ℝ), 1/10; 1/10, 1] : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  fin_cases k <;> simp <;> norm_num

-- § 例 3（P5 使用级·谱夹逼面）：特征值落入圆盘（对角阵＋特征值 API 桥）--------
-- diagonal ![2, 1]：μ = 2 是 toLin' 的特征值（hasEigenvalue_toLin'_diagonal_iff
-- 桥，Eigenspace/Matrix.lean:71），圆盘定理给出 μ ∈ 闭球(2, 0)（对角占优半径 0）。
example : ∃ k : Fin 2, (2 : ℝ) ∈ Metric.closedBall
    ((Matrix.diagonal (![2, 1]) : Matrix (Fin 2) (Fin 2) ℝ) k k)
    (∑ j ∈ Finset.univ.erase k, ‖(Matrix.diagonal (![2, 1]) : Matrix (Fin 2) (Fin 2) ℝ) k j‖) := by
  refine eigenvalue_mem_ball ?_
  rw [hasEigenvalue_toLin'_diagonal_iff]
  exact ⟨0, rfl⟩
```

（注：A.1–A.5 转录与 /tmp 五源件逐字一致；源件头部『本件为 /tmp 探针』字样
为源件自带注释。）

## 附录 B：本会话已跑证据索引（全部 /tmp 留档，门 G3 逐一在盘核验）

| 日志/源 | 内容 | 结果 |
|---|---|---|
| /tmp/r16b_grep_cfc.log | P1 grep 两面（[A] CFC 目录清册＋[B] sqrt 声明 45 条） | 在档（75 行） |
| /tmp/r16b_probe1_cfc.lean | P1 源（5 #check＋3 example） | 编译对象（附录 A.1 转录） |
| /tmp/r16b_probe1_cfc.log | P1 运行日志 | exit_code=0 零 error（终版 24.6s） |
| /tmp/r16b_grep_opnorm.log | P2 grep 五面（[A] Analysis/Matrix opNorm＋[B] Rayleigh＋[C] MatrixSpectrum 缺位＋[D] 交面＋[E] spectralRadius） | 在档（47 行） |
| /tmp/r16b_probe2_rayleigh.lean | P2 源（7 #check＋1 example） | 编译对象（附录 A.2 转录） |
| /tmp/r16b_probe2_rayleigh.log | P2 运行日志 | exit_code=0 零 error（终版 4.3s） |
| /tmp/r16b_grep_eigmono.log | P3 grep 五面（[A] eigenvalues_le 缺位＋[B] 单调面＋[C] eigenvalues 清册＋[D] sqrt 交换缺位＋[E] Nonneg 段转录） | 在档（82 行） |
| /tmp/r16b_probe3_eig.lean | P3 源（8 #check＋1 example） | 编译对象（附录 A.3 转录） |
| /tmp/r16b_probe3_eig.log | P3 运行日志 | exit_code=0 零 error（终版 3.9s） |
| /tmp/r16b_probe4_polar.lean | P4 源（5 #check＋2 example） | 编译对象（附录 A.4 转录） |
| /tmp/r16b_probe4_polar.log | P4 运行日志 | exit_code=0 零 error（终版 3.9s） |
| /tmp/r16b_grep_gershgorin.log | P5 grep 三面（[F] 全声明 outline＋[G] 外部使用＋[H] 高层封装缺位） | 在档（12 行） |
| /tmp/r16b_probe5_gershgorin.lean | P5 源（4 #check＋3 example） | 编译对象（附录 A.5 转录） |
| /tmp/r16b_probe5_gershgorin.log | P5 运行日志 | exit_code=0 零 error（终版 4.0s） |
| /tmp/r16b_final_pass.log | 五探针最终验证趟（exit_code＋errors＋墙钟逐条） | 5/5 exit_code=0 |
| /tmp/r15c_grep_polar.log | P4 引用的 R15C 极分解缺位 grep（[D][E][F] 三面空） | 在盘复核（2182 字节） |
| /tmp/r15c_probe1_api.log | P1 引用的 R15C CFC.sqrt API 探针（P5 例 W·W=A 在场） | 在盘复核 |

（门核验：以上 17 条路径须全部在盘；『在盘复核』＝本会话 ls 亲见非零字节数。）
