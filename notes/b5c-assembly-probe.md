# b5c-assembly-probe.md — R17B B5c 前置探针补全四件零入库并行探针件

任务锚：r17b-b5c-assembly-probe（R17B，campaign dwfrun-f9904baf 第 12 轮，D72 裁决 2）。
定位：**零 Lean 件入库、零求解、纯 notes 产出**——R16B（eee0343）§8 未跑项中 B5c
依赖面四组胶水的补全探针：Q1 PosSemidef 口径桥、Q2 P1/P3 合并件（W 谱供给面）、
Q3 P4 双例合并（orthogonalGroup membership）、Q4 P5 行和胶水＋量纲判定。本件对
四组给出**三档判定（现成／可改造／缺位自建）＋实测证据＋本体行数实测**，并据此
对 R16B §6 的『B5c ≈450–800 行』估计做**最后更新**。Frobenius↔L2op 比较件**不在
本件**（归 R17A 一探两用，D72 文件集零交叠纪律——本件不触 formal/lean/ThomsonN9/、
不触 notes/tableb-lean.md）。

诚实口径（全文适用，R15C/R16B 同款）：
- **已跑**＝本会话在 thomson-n9/formal/lean 下亲跑且日志在 /tmp 留档（每条带路径）；
  探针＝`lake env lean` 编译验证（example/theorem），**探针编译通过 ≠ 证明完成**——
  本件不含任何证明本体入库；量纲判定＝Python 纯 Fraction 精确算术（无浮点判定）；
- **未跑**＝本会话没有执行（如实标注，不做推断性『应该可以』）；
- 迭代史口径：/tmp 日志为**终版覆盖式**（探针 1–4 分别经 4/6/2/8 版迭代收敛，
  中间版不留档，诊断用 mini 件已清理），摩擦点清单为亲历记录（各节『摩擦』小节）；
- 本件不出现『本体入 Lean』类越权陈述——所有结论均系探针性质。

版本口径：Mathlib @ **d13f23b723b8a846827a245b89c10fc7d3f11612**（本仓
formal/lean/lake-manifest 锚定），toolchain `leanprover/lean4:v4.34.1`
（/tmp/r17b_final_pass.log 头部亲验记录：Lean version 4.34.1, arm64,
commit 5045d00）。与 R15C 预研件、R16A/R16B 探针同一 rev 同栈。

零求解声明：本任务零求解（**heavySolves = 0**，字面锚）——零重求解、零 SDP、零新
数值证书；四账本（m9/m10/hermite_v2/typed_ladder）、endgame.json、certificates/
全部零触碰（只读未动），挑战件与 references/ 只读。零 formal/lean/ThomsonN9/
入库——G7 守卫见 numerics/bounds/r17_b5c2_gate.py（r17 家族放行层＝R17A TableB5Trace
在途件，D72 并行纪律）。

四组总览（三档判定一览）：

| 组 | 面向 | 三档判定 | 主证据 |
|---|---|---|---|
| Q1 | (t•1−M).PosSemidef ⇒ eig ≤ t | **现成（可改造级合并件，路线全走通）** | 探针例 1 全链 36 行净本体 exit 0 |
| Q2 | 夹逼 ⇒ CFC.sqrt M 特征值 ∈ [√a,√b] | **可改造（charpoly 谱映射路线走通；W²=M 短路路线未跑）** | 探针例 2 全链 60 行净本体 exit 0 |
| Q3 | W 三前提 ⇒ R 正交（双口径） | **现成（membership 结构替换 det 平方路线，净省 ~12 行）** | 核心引理＋双例 exit 0 |
| Q4 | frob B ≤ β ⇒ 行和 ≤ √(n−1)·β ⇒ n=3 Gershgorin | **可改造（CS 核心现成；ℝ 面拆分胶水自建；量纲【不相容】如实判定）** | 定理 1/2＋数值例 exit 0＋Fraction 判定 |

---

## §Q1 探针：PosSemidef 口径桥（R16B §P3 未跑项）

**三档判定：现成**——桥 API（PosDef.lean 三件）与特征向量路线（R16B §P3 例 1
单侧化）全部现成，合并成可用件全链走通；预研 §3.1『PosSemidef 口径桥留 B5c
施工时定』的缺口消解。

**grep 面**（已跑 /tmp/r17b_grep_psdbridge.log，[A] 段）。grep 段头转录（与日志
逐字一致）：

```
== [A] Q1: posSemidef dotProduct-mulVec bridge declarations (PosDef.lean) ==
```

[A] 段四条命中（含行号）：

| API | 位置 | 面向 |
|---|---|---|
| `Matrix.posSemidef_iff_dotProduct_mulVec : M.PosSemidef ↔ M.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ (M *ᵥ x)` | PosDef.lean:298 | **口径桥本体**（PSD ↔ 二次型） |
| `Matrix.PosSemidef.dotProduct_mulVec_nonneg` | PosDef.lean:306 | PSD ⇒ 二次型非负（单向） |
| `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` | PosDef.lean:309 | 二次型非负＋厄米 ⇒ PSD（B5b 备用面，R16A 定位复核一致） |
| `Matrix.of_dotProduct_mulVec_pos` | PosDef.lean:469 | PosDef 版（R16A 探针②主用，:454/:469 与 bdadf69 记录一致） |

**使用级例**（已跑 /tmp/r17b_probe1_psdbridge.log，exit_code=0，终版 27.5s，
源 /tmp/r17b_probe1_psdbridge.lean，含 9 条 #check＋2 例）：
- 例 1（主目标·合并件）：`M.IsHermitian → (t•1−M).PosSemidef → ∀ i,
  hM.eigenvalues i ≤ t`——①桥（`posSemidef_iff_dotProduct_mulVec.mp` 取二次型
  面）＋线性拆开（`sub_mulVec`/`smul_mulVec`/`one_mulVec`/`dotProduct_sub`/
  `dotProduct_smul`）得 `v ⬝ᵥ (M *ᵥ v) ≤ t*(v ⬝ᵥ v)`；②R16B §P3 特征向量路线
  单侧版（去 abs：`w ⬝ᵥ (M *ᵥ w) = μ*(w ⬝ᵥ w) ≤ t*(w ⬝ᵥ w)`＋`w ⬝ᵥ w > 0`
  收口）。**实测行数：全块 44 行，证明本体 41 行，净本体（去空行注释）36 行**；
- 例 2（桥本体单独件）：`(t•1−M).PosSemidef → ∀ v, v ⬝ᵥ (M *ᵥ v) ≤ t*(v ⬝ᵥ v)`
  ——**净本体 7 行**（工程化时桥可独立成 ~7 行引理供 B5b/B5c 两用）。

**摩擦**（工程化输入，迭代 4 版收敛的主因）：①`(A−B)*ᵥv` 的拆开名是
`Matrix.sub_mulVec`（Data/Matrix/Mul.lean:1074；`mulVec_sub` :1069 是向量减版，
极易混）；②`(t•A)*ᵥv`＝`Matrix.smul_mulVec`（:818，不是 `smul_mulVec_assoc`）；
③标量外提是 `dotProduct_smul`（v ⬝ᵥ x•w = x•(v ⬝ᵥ w)，:246）而非
`smul_dotProduct`（:242 是 x•v ⬝ᵥ w 侧）；④该 simp only 面自足收口，尾部 `ring`
冗余；⑤例 2 陈述面需 `[DecidableEq n]`（PosSemidef 类合成依赖）。

**未跑项（如实）**：二次型前提方向（`of_dotProduct_mulVec_nonneg` 构造
(t•1−M).PosSemidef）本件未跑（B5b 侧用途，R16A 已在 tableb-lean.md §4 走通
PosDef 版同型桥）；带 strict（PosDef）口径未跑（B5c 只需 ≤）。

---

## §Q2 探针：P1/P3 合并件——夹逼 ⇒ CFC.sqrt M 特征值 ∈ [√a,√b]（W 谱供给面）

**三档判定：可改造**——charpoly 谱映射路线（任务书路线 A）**全链走通**；备选的
W²=M 点态短路路线（路线 B）**未跑**（见未跑项）。R16B §P3 未跑项『P1 例 2 与
例 1 夹逼的合并件』消解。

**grep 面**（已跑 /tmp/r17b_grep_cfc2.log，[A] 段）。grep 段头转录（与日志
逐字一致）：

```
== [A] Q2: roots_charpoly_eq_eigenvalues + charpoly_cfc_eq signatures ==
```

关键定位（[A] 段逐条在档＋本会话 Mathlib 源亲读）：

| API | 位置 | 面向 |
|---|---|---|
| `Matrix.IsHermitian.charpoly_cfc_eq : (cfc f A).charpoly = ∏ i, (X - C (f (hA.eigenvalues i) : 𝕜))` | HermitianFunctionalCalculus.lean:152 | 谱映射（charpoly 层，R16B §P1 例 2 已用） |
| `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues : A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val` | Analysis/Matrix/Spectrum.lean:161 | **roots↔eigenvalues 对接口（本组新用）** |
| `Polynomial.roots_prod : s.prod f ≠ 0 → (s.prod f).roots = s.val.bind fun i => roots (f i)` | Algebra/Polynomial/Roots.lean:286 | 乘积分解的 roots 拆开 |
| `Polynomial.roots_X_sub_C : (X - C a).roots = {a}` | Roots.lean:311 附近 | 单因子 roots＝单点 |
| `RCLike.ofReal_real_eq_id : @ofReal ℝ _ = id` | RCLike/Basic.lean:1050 | 实域 ofReal 平凡化 |
| `Multiset.mem_map_of_mem` | Data/Multiset/MapFold.lean:117 | map 成员提取 |

**使用级例**（已跑 /tmp/r17b_probe2_sqrtband.log，exit_code=0，终版 5.0s
（elaboration 热缓存）/初跑 40.8s，源 /tmp/r17b_probe2_sqrtband.lean，含
7 条 #check＋2 例）：
- 例 1（hW 供给面）：`(CFC.sqrt M)ᴴ = CFC.sqrt M`——R16B §P1 例 1 原样重跑
  （`cfcₙ_star` 路线），**净本体 6 行**；
- 例 2（主目标·合并件）：`M.IsHermitian → 0 ≤ M → (CFC.sqrt M).IsHermitian →
  0 ≤ a → a ≤ b → (∀ v, a*(v⬝ᵥv) ≤ v ⬝ᵥ(M*ᵥv)) → (∀ v, v ⬝ᵥ(M*ᵥv) ≤ b*(v⬝ᵥv)) →
  ∀ i, Real.sqrt a ≤ hW.eigenvalues i ∧ hW.eigenvalues i ≤ Real.sqrt b`——
  三面拼装：P3 夹逼（`key : ∀ μ ∈ spectrum ℝ M, a ≤ μ ∧ μ ≤ b`，特征向量路线
  双向）＋P1 例 2 谱映射链（`sqrt_eq_cfc → cfc_nnreal_eq_real → charpoly_cfc_eq`）
  ＋roots 双口径对接（`roots_charpoly_eq_eigenvalues` ↔ `roots_prod`＋
  `roots_X_sub_C`＋`Multiset.mem_bind`）＋P2b 点态胶水（`Real.coe_sqrt` 场，
  eigM j ≥ 0 经夹逼下侧）＋`Real.sqrt_le_sqrt` 双向收口。**实测行数：全块 70 行，
  证明本体 65 行，净本体 60 行**。

**心跳实测（R16B §P1 摩擦的修正性数据）**：本组合并件在 `set_option
maxHeartbeats 2000000` 下通过后，**去掉放宽的默认 200000 心跳版本同样通过**
（已跑 /tmp/r17b_probe2_default_hb_test.log，exit_code=0，40.3s）——R16B §P1
例 2 的 2M 需求是该例表述面特有（其 rw 链细节不同），工程化时放宽仍建议保留
作保险，但**心跳摩擦降档为非阻断**。

**摩擦**（迭代 6 版收敛的主因）：①`hW.eigenvalues` 的 map 成员提取须先给
`have h : ... ∈ Multiset.map (RCLike.ofReal ∘ hW.eigenvalues) Finset.univ.val :=
Multiset.mem_map_of_mem _ (Finset.mem_univ i)` 型注记——裸 `mem_map_of_mem`
会让 `RCLike.ofReal` 的目标域留 metavariable（typeclass 卡死）；②ofReal 平凡化
用 `RCLike.ofReal_real_eq_id`（`Real.ofReal_eq_id` 在本 rev 不存在）；③
`i ∈ Finset.univ.val` 对 `mem_map_of_mem` 直接喂 `Finset.mem_univ i`（defeq，
`Finset.mem_val` 是 rfl）——`(by simp)` 反而不燃；④mem_bind 提取须在
`roots_X_sub_C`/`bind_singleton` simp 化**之前**做（顺序反了会找不到 bind
pattern）；⑤`Finset.mem_univ` 无 `Multiset.` 版（`Multiset.mem_univ` 不存在）。

**未跑项（如实）**：路线 B（W²=M 点态短路：`CFC.sqrt_mul_sqrt_self` 给
W*W=M＋特征向量上 ‖W w‖² = μ²‖w‖² = wᵀMw ∈ [a,b]·‖w‖²——需另证 μ ≥ 0，
R15C 探针 1 P5 只验了 W·W=A 恒等式本身）未跑——路线 A 已走通且给出更强的
逐点等式（eigW i = Real.sqrt (eigM j)），路线 B 不再必需；spectrum 口径陈述
（∀ μ ∈ spectrum ℝ (CFC.sqrt M)）未单列（eigenvalues 口径已足 B5c 用）；
hW 的 proof-irrelevance 面（eigenvalues 沿 IsHermitian 见证经 Classical.choice
定义——工程化须如本例固定单一 hW 见证贯穿）未深究，留 B5c 施工注意项。

---

## §Q3 探针：P4 双例合并——W 三前提 ⇒ R := W⁻¹(1+A) 正交（双口径）

**三档判定：现成**——R16B §P4 例 1 纯代数内核原样可用；例 2 的 det 平方路线被
`Matrix.orthogonalGroup` membership 结构替换（Submonoid 自带双侧性），双例合并
成『一核心＋两陈述』单定理族。R16B §P4 未跑项『双例合并成单定理（orthogonalGroup
membership 形式陈述）』消解。

**grep 面**（已跑 /tmp/r17b_grep_orth.log，[A] 段）。grep 段头转录（与日志
逐字一致）：

```
== [A] Q3: orthogonalGroup membership API (UnitaryGroup.lean) ==
```

关键定位（[A] 段逐条在档）：

| API | 位置 | 面向 |
|---|---|---|
| `Matrix.orthogonalGroup : Submonoid (Matrix n n R)`（abbrev unitaryGroup） | UnitaryGroup.lean:295 | 正交群（子幺半群） |
| `Matrix.mem_orthogonalGroup_iff : A ∈ orthogonalGroup n R ↔ A * Aᵀ = 1` | UnitaryGroup.lean:297–298 | membership ↔ 右侧等式 |
| `Matrix.mem_orthogonalGroup_iff' : A ∈ orthogonalGroup n R ↔ Aᵀ * A = 1` | UnitaryGroup.lean:301–302 | membership ↔ 左侧等式 |
| （B5c 消去族：isUnit_iff_isUnit_det :127／transpose_nonsing_inv :202／nonsing_inv_mul :217） | NonsingularInverse.lean | R16B §P4 同款（本组复核一致） |

**使用级例**（已跑 /tmp/r17b_probe3_orthmerge.log，exit_code=0，终版 14.6s，
源 /tmp/r17b_probe3_orthmerge.lean，含 6 条 #check＋1 核心引理＋2 例）：
- 核心引理 `r_mul_rTranspose_eq_one`（R16B §P4 例 1 原样）：`Wᵀ=W → W*W=(1+A)(1+A)ᵀ
  → IsUnit W → (W⁻¹*(1+A))*(W⁻¹*(1+A))ᵀ = 1`——**净本体 14 行**；
- 例 1（主目标·membership 口径）：`R ∈ Matrix.orthogonalGroup n ℝ`——经
  `mem_orthogonalGroup_iff.mpr` 一行接核心引理，**净本体 3 行**（iff 须先 have
  成局部等式，n/R 显式实参）；
- 例 2（双等式口径·合并单定理）：`R*Rᵀ=1 ∧ Rᵀ*R=1`——membership 一次供给，
  `iff.mp`/`iff'.mp` 双向取出，**净本体 9 行**（对照 R16B §P4 例 2 det 平方路线
  ~15 行——**净省 ~6 行且消去 IsUnit.of_mul_eq_one 搬运面**）。

任务书『Submonoid membership 与双等式两口径择一实测』——**两口径均实测**
（例 1/例 2 各自走通），工程化建议 membership 为主陈述（B5c 步骤 5 的 R 用途
是给 YR=XW+D_⊥R 型替换，membership 直接可引）。

**摩擦**（迭代 2 版收敛）：①`Matrix.mem_orthogonalGroup_iff.mpr` 点投影解析
陷阱——常量名上直接 `.mpr` 会被当限定名解析失败或 invalidField（iff 是
∀-首显式参 lemma），须 `(Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mpr`
或先 have 成局部 iff；②核心引理的既有摩擦复核成立（`mul_nonsing_inv` 族 A 显式
实参＋实例路径不字节对齐须 have 局部等式；`mul_assoc` 全局重写先匹配外层须
`conv_lhs => arg 2` 定向）。

**未跑项（如实）**：`specialOrthogonalGroup`（det=1 面，UnitaryGroup.lean:324）
未探（B5c 只需正交性，不需定向）；O(3) 存在性/membership 的商结构面未触。

---

## §Q4 探针：P5 行和胶水（Gershgorin 独立替通路）＋量纲判定

**三档判定：可改造**——CS 核心件 `sq_sum_le_card_mul_sum_sq` 现成（无单调性
前提的 f=g 特例）；但 ℝ 面的『单元素 ≤ 和』『erase ≤ 全和』两件 API 在本 rev
系 ℕ 面（CanonicallyOrderedAdd 前提）须 insert_erase 拆分自建（~3 行 helper）；
Gershgorin 注入面（R16B §P5 例 1）原样可用。量纲判定【不相容】如实（下文）。

**grep 面**（已跑 /tmp/r17b_grep_rowsum.log，四面 [A]–[D]）。grep 段头转录
（与日志逐字一致）：

```
== [D] Q4: squared CS candidate lemmas (sum_sq / card_mul / inner Finset) ==
```

（[D] 段命中即关键件 `sq_sum_le_card_mul_sum_sq`——Algebra/Order/Chebyshev.lean:144，
文档串自标『Special case of Chebyshev's Sum Inequality or the Cauchy-Schwarz
Inequality』，`(∑ i ∈ s, f i)^2 ≤ ↑s.card * ∑ i ∈ s, f i^2`，无单调性前提；
本组新发现，预研/R16B 均未定位。[A] 段空＝abs_sum 无 sqrt 型直接引理；[B] 段空
＝无 sqrt_sum_le 命名族；[C] 段＝EuclideanSpace.inner_eq_star_dotProduct
PiL2.lean:216 在场（WithLp 口径，本组弃用）。）

**使用级例**（已跑 /tmp/r17b_probe4_rowsum.log，exit_code=0，终版 6.2s，
源 /tmp/r17b_probe4_rowsum.lean，含 frob def＋1 helper＋2 定理＋1 数值例）：
- frob def：TableB5Core.lean:67 同款值口径 `Real.sqrt (∑ i, ∑ j, (M i j)^2)`
  （索引类型 Type* 化——Type 0 版在泛型定理面 universe 不合，摩擦④）；
- helper `univ_eq_erase_add`：`∑ i, X i = X k + ∑ i ∈ univ.erase k, X i`
  ——**净本体 2 行**（conv_lhs 定向＋sum_insert）；
- 定理 1（主目标·行和胶水）：`0 ≤ β → frob B ≤ β → (k : n) →
  ∑ j ∈ univ.erase k, |B k j| ≤ Real.sqrt ((Fintype.card n : ℝ) - 1) * β`——
  平方和链（行非对角 ≤ 行全 ≤ 全阵 ≤ β²）＋CS（`sq_sum_le_card_mul_sum_sq`）＋
  开方收口（`Real.sqrt_le_sqrt`/`Real.sqrt_mul`/`Real.sqrt_sq_eq_abs`）。
  **实测行数：全块 52 行，证明本体 49 行，净本体 45 行**；
- 定理 2（合并面·n=3 Gershgorin）：`0 ≤ β → √2*β < 1−β → frob B ≤ β →
  (1+B).det ≠ 0`——行和界（定理 1 特化 card=3）＋对角下界（逆向三角 by_cases 版
  ＋单元素 ≤ frob）＋`det_ne_zero_of_sum_row_lt_diag` 注入（R16B §P5 例 1 同款
  偏离角换元）。**实测行数：全块 62 行，证明本体 59 行，净本体 55 行**；
- 例 3（具体数值）：B = (1/10)·全一阵（Fin 3），frob² = 9/100 ⇒ β = 3/10 <
  1/(1+√2)，√2 < 7/3 经 `Real.sqrt_lt`——**净本体 14 行**，数值例走通。

**量纲判定（已跑 /tmp/r17b_dimension_q4.log，纯 Fraction 精确，常数从
TableB5Data.lean 源直读零手抄）**：
- 数值层适用域（保守口径）：β ≤ min(1/2, σ₃/(2σ₁)) 的记录保守上界
  dom = s3Dn/(2·s1Up) ≈ **0.4963450766**；
- Gershgorin 闭合阈值（n=3）：√2·β < 1−β ⟺ β < 1/(1+√2) = √2−1 ≈
  **0.4142135624**；
- **判定【不相容】**：dom > thr（(dom+1)² = 2.239048588297 > 2 精确判定）——
  保守适用域含 [thr, dom] 带（宽 ≈ 0.082132），该带内 Gershgorin 行和路线
  不能闭合，P3 谱夹逼主路线仍闭合；
- 越出带**实际可达**（非纯余量）：δ=δ_max 时实际 β = u1·sqrt72Up·deltaMax/l3²
  与 dom **精确相等**（Fraction 恒等核验 True——deltaMax_val 定义反解）；
- Gershgorin 覆盖的 δ 子域：δ_gersh = l3²·(√2−1)/(sqrt72Up·u1) ≈ **0.1429052196**
  ＜ δ_max ≈ 0.1712408975（约前 83.5%）——独立替通路定位＝仅小 β 子域备用路，
  **P3 谱夹逼主路线地位不变**（判定非猜测：全部经 Fraction 精确比较）。

**摩擦**（迭代 8 版收敛——本件四组中最多，主因是 ℝ/ℕ 面 API 分层）：
①`sq_sum_le_card_mul_sum_sq` 是**根命名空间**（Chebyshev.lean section Mul 在
`namespace Finset` 之前展开——`Finset.` 前缀不命中）；②本 rev 的
`Finset.single_le_sum` 与 `Finset.sum_le_sum_of_subset` 均系 **ℕ 面件**
（CanonicallyOrderedAdd 前提，ℝ 无此实例——错误形如『failed to synthesize
CanonicallyOrderedAdd ℝ』且报错位置在**后续** have 上，极具误导性）——ℝ 面的
『单元素 ≤ 和』『erase ≤ 全和』须 `insert_erase`＋`sum_insert` 拆分自建；
③|a+b| ≤ |a|+|b| 的老名 `abs_add` 不在（新层级系 `abs_add_le`），逆向三角
（1−|x| ≤ |1+x|）改走 by_cases＋`le_abs_self (−x)`＋`abs_neg`；
④`sq_abs`（Ring/Abs.lean:81，|a|² = a²）非 `abs_sq`；⑤frob def 索引类型须
Type*；⑥`Real.sqrt_le_sqrt` 是**蕴涵非 iff**（无 .mp/.mpr——从 √S ≤ β 取
S ≤ β² 须 `← Real.sq_sqrt`＋`pow_two`＋`mul_le_mul` 组合）；⑦card 表达式的
cast 陷阱：`Real.sqrt ((Fintype.card n : ℕ) - 1)` 会被统一成 ℝ 减法
`↑card − 1`（非 ℕ 减法再 cast），hcard 证明须 `Nat.cast_sub`＋`Nat.cast_one`
链且 card ≥ 1 前提（`Fintype.card_pos_iff.mpr ⟨k⟩`）先行；⑦' RW 方向敏感：
`rw [← Real.sqrt_sq_eq_abs]` 找 |x| pattern（目标无 |x| 时不动）——β = √(β²)
方向的构造应正向 `rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]`。

**未跑项（如实）**：行和界的 Sharpened 版（用 |B k k| 结构省 √(n−1) 因子或
逐行 Frobenius）未探——量纲不相容下 Gershgorin 已定位于小子域备用路，收紧
其域不再有主路线价值；`det_ne_zero_of_sum_col_lt_diag`（列版本）未用；
Gershgorin 圆盘→特征值位置的定量面（eigenvalue_mem_ball）R16B §P5 例 3 已探
不重跑。

---

## §5 B5c ≈450–800 行估计的最后更新（R16B §6 口径的收口）

锚（本会话实测，净本体行数＝去空行注释）：Q1 合并件 36＋桥 7；Q2 合并件 60
＋hW 供给 6；Q3 核心 14＋membership 3＋双等式 9；Q4 定理 1 45＋定理 2 55＋
helper 2＋frob def 1＋数值例 14。预研 §4 分档口径维持（证明本体行数不含 Data
件与门）。R16B §6 表的逐行更新：

| B5c 子件 | R16B §6 估计 | 本轮四件后 | 依据 |
|---|---|---|---|
| W 构造（CFC.sqrt）＋Wᵀ=W | ~80–150 | **~70–120** | Q2 例 1 hW 供给净本体 6 行实测；心跳摩擦降档（默认心跳亦过，§Q2）；成员提取 cast 摩擦实测（map 型注记等 5 条） |
| R := W⁻¹(I+A) 正交 | ~40–80 | **~30–50** | Q3 双口径实测（核心 14＋两陈述 12）；det 平方面被 membership 替换净省 ~6 行；iff 点投影陷阱留档 |
| 谱夹逼（P3 面含 PSD 口径桥） | ~80–150（另计 PSD 桥 50–100） | **~110–170（含 PSD 桥）** | Q1 合并件 36＋桥 7 实测（原『另计 50–100』的桥收进实测 7 行级）；Q2 夹逼半块 ~25（含在 60 行内）；WithLp/根命名空间摩擦已在档 |
| CFC.sqrt 特征值 ∈ [√a,√b]（Q2 主目标） | （R16B 未单列——并入谱夹逼） | **~60–90** | Q2 合并件净本体 60 行实测整件走通；心跳非阻断 |
| 算子范数-特征值桥（‖W−I‖₂ ≤ β） | ~50–120 | 维持 ~50–120 | **本轮未触**（依赖 Frobenius↔L2op，归 R17A 一探两用——零交叠纪律如实） |
| 步骤 6 装配 | ≤300 | 维持 ≤300 | 预研 §4 依据不变（R14 同式先例） |

**最后更新结论：B5c（步骤 5–6）维持 ≈450–800 行档，不确定度『中』不降**
——R16B 余量三块中：②PosSemidef 口径桥（本件 Q1 消解，实测 7 行级）与
③P1/P3 合并件（本件 Q2 消解，实测 60 行级）两块落定，上限压力减轻；但
①Frobenius↔L2op 比较件仍未探（R17A 在途，本件零交叠不越界）——800 上界的
维持理由从『三块未探』收窄为『一块在途＋工程化实例路径放大（Q4 八项摩擦
亲历）』。若 R17A 探得 Frobenius↔L2op 现成/可改造，B5c 可按 ≈450–650 排期；
若缺位自建，回退 ≈650–800＋二次型口径弱化预案（预研 §3.1 缓解案维持有效）。

## §6 排期建议

1. **B5a → B5b → B5c 串行维持**（D67 裁决 1 口径不变，本轮四件不改变依赖
   单向性）；B5b（R17A 在途）落地后 B5c 即可开工——本件四组胶水全部在档。
2. **B5c 施工顺序建议**：Q3（现成，双口径齐）→ Q1（桥 7 行先行，供 B5b 复用）
   → Q2（60 行合并件为骨架）→ Q4（Gershgorin 备用路，量纲不相容已判定——
   **只作小 β 子域的独立冗余，不作主路线**）→ 步骤 6 装配。
3. **风险面如实**：R1（谱夹逼＋算子范数桥）维持**中**——谱夹逼三面（PSD 桥/
   P3 夹逼/谱映射）已实测走通，剩 Frobenius↔L2op 一块在途；R2（CFC 自伴面）
   维持**低**（Q2 例 1 重跑 6 行＋心跳降档）。Q4 的量纲判定反过来加固了
   P3 主路线的必要性（Gershgorin 不能全覆盖适用域）。
4. **对 R17C 收口的输入**：本件四件（notes/b5c-assembly-probe.md＋
   r17_b5c2_gate.py＋嵌套 CWD 包装器＋decisions D74）为 R17B 自有件；R17A
   （TableB5Trace 族＋tableb-lean.md §5＋r17_b5b_gate）与本件文件集零交叠
   （D72 并行纪律），r17 家族放行层见 decisions.md D74。

## §7 零求解声明与诚实口径（G5/G6 锚）

- **零求解声明：本任务 heavySolves = 0**（字面锚）——零重求解、零 SDP、零新
  数值证书。
- **零账本触碰声明**：四账本（results/m9_campaign、m10_campaign、hermite_v2、
  typed_ladder）零触碰，endgame.json 零触碰（只读未动），certificates/ 零触碰，
  typed_ladder rungs 零追加——G7 守卫 numerics/bounds/r17_b5c2_gate.py 以
  git status/diff 机器面执行。
- 全部结论系探针性质：**探针编译通过 ≠ 证明完成**；本件无任何『本体入 Lean』
  宣称；B5c 本体（步骤 5–6）仍未开工，其可行性陈述以探针证据为界。
- 未跑项汇总（全文『未跑』如实）：§Q1 二次型前提方向＋PosDef 口径；§Q2 路线 B
  （W²=M 短路）＋spectrum 口径单列＋hW 见证 proof-irrelevance 深究；§Q3
  specialOrthogonalGroup＋商结构面；§Q4 行和 Sharpened 版＋列版注入＋圆盘定量
  重跑；§5 Frobenius↔L2op（归 R17A）。
- 迭代史：探针 1–4 分别 4/6/2/8 版收敛，/tmp 日志为终版覆盖式（R15C §2.3
  口径）；摩擦点已逐组留档（各节『摩擦』小节，共 5＋5＋2＋8 条亲历记录）。

---

## 附录 A：探针源转录（终版，与 /tmp 四源件逐字一致）

### A.1 Q1 源（/tmp/r17b_probe1_psdbridge.lean）

```lean
import Mathlib

/-!
R17B Q1 探针源（b5c-assembly-probe §Q1）：
PosSemidef 口径桥——（t•1−M).PosSemidef ⇒ ∀ i, hM.eigenvalues i ≤ t。
R16A 探针②桥（posSemidef_iff_dotProduct_mulVec PosDef.lean:298＋
of_dotProduct_mulVec_nonneg :309）与 R16B §P3 特征向量路线
（eigenvalues_mem_spectrum_real→spectrum_toLpLin→hasEigenvalue_iff_mem_spectrum）
的合并使用级核验。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。

迭代摩擦留档（v1→v2）：①`(A−B)*ᵥv` 的 simp 名＝`Matrix.sub_mulVec`
（Mul.lean:1074；`mulVec_sub` :1069 是向量减版——v1 误用致 simp 面全不燃）；
②`(t•A)*ᵥv`＝`Matrix.smul_mulVec`（:818，v1 误写 `smul_mulVec_assoc`）；
③例 2 陈述面需 `[DecidableEq n]`（PosSemidef 类合成依赖）；④标量外提是
`dotProduct_smul`（v ⬝ᵥ x•w = x•(v ⬝ᵥ w)，Mul.lean:246）而非
`smul_dotProduct`（:242 是 x•v ⬝ᵥ w 侧）；⑤该 simp only 面自足收口，
尾部 `ring` 冗余（v3 删）。
-/

open Matrix

-- § API 签名核验（#check 面）----------------------------------------------

#check @Matrix.posSemidef_iff_dotProduct_mulVec     -- PosDef.lean:298（口径桥本体）
#check @Matrix.PosSemidef.dotProduct_mulVec_nonneg  -- PosDef.lean:306
#check @Matrix.PosSemidef.of_dotProduct_mulVec_nonneg -- PosDef.lean:309
#check @Matrix.IsHermitian.eigenvalues_mem_spectrum_real -- Analysis/Matrix/Spectrum.lean:83
#check @Matrix.spectrum_toLpLin                     -- Analysis/Matrix/Spectrum.lean:40
#check @Module.End.hasEigenvalue_iff_mem_spectrum   -- Eigenspace/Basic.lean:526
#check @Matrix.sub_mulVec                           -- Data/Matrix/Mul.lean:1074
#check @Matrix.smul_mulVec                          -- Data/Matrix/Mul.lean:818
#check @Matrix.one_mulVec                           -- Data/Matrix/Mul.lean:1003

-- § 例 1（Q1 主目标）：(t•1−M).PosSemidef ⇒ 全部特征值 ≤ t -------------------
-- 合并路线：①口径桥把 PosSemidef 前提换成二次型上界 v ⬝ᵥ(M*ᵥv) ≤ t*(v⬝ᵥv)
-- （smul/dotProduct 线性拆开）；②R16B §P3 特征向量路线单侧版（去 abs，
-- 直接 w ⬝ᵥ(M*ᵥw) = μ*(w⬝ᵥw) ≤ t*(w⬝ᵥw) ⇒ μ ≤ t）。
set_option maxHeartbeats 800000 in
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {t : ℝ} (hpsd : Matrix.PosSemidef (t • 1 - M)) :
    ∀ i, hM.eigenvalues i ≤ t := by
  -- ①口径桥（R16A 探针②面，本侧向：PosSemidef → 二次型）
  have hq : ∀ v : n → ℝ, v ⬝ᵥ (M *ᵥ v) ≤ t * (v ⬝ᵥ v) := by
    intro v
    have h0 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
    -- h0 : 0 ≤ star v ⬝ᵥ ((t•1−M) *ᵥ v)；实域 star 平凡，线性拆开
    have hsplit : star v ⬝ᵥ ((t • 1 - M) *ᵥ v) = t * (v ⬝ᵥ v) - v ⬝ᵥ (M *ᵥ v) := by
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul, star_trivial]
    rw [hsplit] at h0
    linarith
  -- ②特征向量路线（R16B §P3 例 1 单侧版）
  intro i
  have hμ := hM.eigenvalues_mem_spectrum_real i
  rw [← Matrix.spectrum_toLpLin (𝕜 := ℝ) (p := 2)] at hμ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨v, hv1, hv2⟩ := hμ.exists_hasEigenvector
  have heq : (Matrix.toLpLin 2 2 M) v = (hM.eigenvalues i) • v := by simpa using hv1
  set w : n → ℝ := (v : n → ℝ) with hw
  have hw0 : w ≠ 0 := by
    intro hc
    apply hv2
    have h0 : (WithLp.ofLp v : n → ℝ) = 0 := by rw [← hw]; exact hc
    exact (WithLp.ofLp_eq_zero _).mp h0
  have e1 : (inner ℝ v ((Matrix.toLpLin 2 2 M) v) : ℝ) = w ⬝ᵥ (M *ᵥ w) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]
    rw [← hw]
  have e2 : (inner ℝ v v : ℝ) = w ⬝ᵥ w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp
    rw [← hw]
  have conv : w ⬝ᵥ (M *ᵥ w) = (hM.eigenvalues i) * (w ⬝ᵥ w) := by
    rw [← e1, heq, real_inner_smul_right, e2]
  have hnn : 0 ≤ w ⬝ᵥ w := by rw [← e2]; exact real_inner_self_nonneg
  have hnz : w ⬝ᵥ w ≠ 0 := fun hc => hw0 (dotProduct_self_eq_zero.mp hc)
  have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnn (Ne.symm hnz)
  have hle := hq w
  rw [conv] at hle
  exact (mul_le_mul_iff_of_pos_right hpos).mp hle

-- § 例 2（Q1 桥本体单独件）：PosSemidef ⇒ 二次型口径（R16A 探针②的 PSD 面）----
-- 工程化计数用：桥本体 ~6 行（不含特征向量面）。
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} {t : ℝ}
    (hpsd : Matrix.PosSemidef (t • 1 - M)) :
    ∀ v : n → ℝ, v ⬝ᵥ (M *ᵥ v) ≤ t * (v ⬝ᵥ v) := by
  intro v
  have h0 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
  have hsplit : star v ⬝ᵥ ((t • 1 - M) *ᵥ v) = t * (v ⬝ᵥ v) - v ⬝ᵥ (M *ᵥ v) := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, star_trivial]
  rw [hsplit] at h0
  linarith
```

### A.2 Q2 源（/tmp/r17b_probe2_sqrtband.lean）

```lean
import Mathlib

/-!
R17B Q2 探针源（b5c-assembly-probe §Q2）：
P1/P3 合并件——M PSD 厄米＋二次型夹逼 a·(v⬝ᵥv) ≤ v ⬝ᵥ(M*ᵥv) ≤ b·(v⬝ᵥv)
（0 ≤ a ≤ b）⇒ CFC.sqrt M 的全部特征值 ∈ [√a, √b]。
路线＝P1 例 2 charpoly 谱映射链（sqrt_eq_cfc→cfc_nnreal_eq_real→
charpoly_cfc_eq〔HermitianFunctionalCalculus.lean:152〕）＋ P2b 点态胶水
（Real.coe_sqrt 场）＋ P3 夹逼（特征向量路线双向）＋ roots_charpoly_
eq_eigenvalues（Analysis/Matrix/Spectrum.lean:161）对接。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix
open scoped MatrixOrder

-- § API 签名核验（#check 面）----------------------------------------------

#check @Matrix.IsHermitian.charpoly_cfc_eq      -- HermitianFunctionalCalculus.lean:152
#check @Matrix.IsHermitian.roots_charpoly_eq_eigenvalues -- Analysis/Matrix/Spectrum.lean:161
#check @Polynomial.roots_prod                   -- Algebra/Polynomial/Roots.lean:286
#check @Polynomial.roots_X_sub_C                -- Roots.lean:311（roots (X - C a) = {a}）
#check @Real.sqrt_le_sqrt                       -- sqrt 单调
#check @CFC.sqrt_eq_cfc                         -- Rpow/Basic.lean:638
#check @cfc_nnreal_eq_real                      -- CStarAlgebra Instances.lean:409

-- § 例 1（Q1 桥补面）：P1 例 1 重跑——CFC.sqrt M 自伴（hW 供给）--------------
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (hnn : 0 ≤ M) : (CFC.sqrt M)ᴴ = CFC.sqrt M := by
  rw [← Matrix.star_eq_conjTranspose]
  have h := cfcₙ_star (f := NNReal.sqrt) (a := M)
  have hstar : (fun x : NNReal ↦ star (NNReal.sqrt x)) = NNReal.sqrt := by
    funext x; simp
  rw [hstar] at h
  exact h.symm

-- § 例 2（Q2 主目标·合并件）：夹逼 ⇒ CFC.sqrt M 特征值 ∈ [√a, √b] --------------
-- hW 作显式前提（IsHermitian 是 Prop＝Aᴴ=A，eigenvalues 沿见证定义；工程化时
-- hW 由例 1 面一次供给）。maxHeartbeats 放宽系 §P1 已知摩擦（cfc 实例路径）。
set_option maxHeartbeats 2000000 in
example {n : Type*} [DecidableEq n] [Fintype n] {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (hnn : 0 ≤ M) (hW : (CFC.sqrt M).IsHermitian) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (M *ᵥ v) ≤ b * (v ⬝ᵥ v)) :
    ∀ i, Real.sqrt a ≤ hW.eigenvalues i ∧ hW.eigenvalues i ≤ Real.sqrt b := by
  -- (P3 夹逼面) M 的特征值落 [a, b]（谱层一次证好，双向）
  have hband : ∀ j, a ≤ hM.eigenvalues j ∧ hM.eigenvalues j ≤ b := by
    have key : ∀ μ ∈ spectrum ℝ M, a ≤ μ ∧ μ ≤ b := by
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
      have e1 : (inner ℝ v ((Matrix.toLpLin 2 2 M) v) : ℝ) = w ⬝ᵥ (M *ᵥ w) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]
        rw [← hw]
      have e2 : (inner ℝ v v : ℝ) = w ⬝ᵥ w := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp
        rw [← hw]
      have conv : w ⬝ᵥ (M *ᵥ w) = μ * (w ⬝ᵥ w) := by
        rw [← e1, heq, real_inner_smul_right, e2]
      have hnn : 0 ≤ w ⬝ᵥ w := by rw [← e2]; exact real_inner_self_nonneg
      have hnz : w ⬝ᵥ w ≠ 0 := fun hc => hw0 (dotProduct_self_eq_zero.mp hc)
      have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnn (Ne.symm hnz)
      have h1 := hlo w
      have h2 := hhi w
      rw [conv] at h1 h2
      exact ⟨(mul_le_mul_iff_of_pos_right hpos).mp h1,
             (mul_le_mul_iff_of_pos_right hpos).mp h2⟩
    intro j
    exact key _ (hM.eigenvalues_mem_spectrum_real j)
  -- (P1 例 2 面) charpoly 谱映射链
  have hcp : (CFC.sqrt M).charpoly =
      ∏ j, (Polynomial.X - Polynomial.C
        ((fun x ↦ NNReal.sqrt x.toNNReal : ℝ → ℝ) (hM.eigenvalues j))) := by
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt M hnn, hM.charpoly_cfc_eq _]
    simp
  -- (合并面) roots 双口径对接
  intro i
  -- eigenvalues i 是 charpoly 的根（经 roots_charpoly_eq_eigenvalues 的 map 口径）
  have hmem : hW.eigenvalues i ∈ (CFC.sqrt M).charpoly.roots := by
    rw [hW.roots_charpoly_eq_eigenvalues]
    have h : hW.eigenvalues i ∈ Multiset.map (RCLike.ofReal ∘ hW.eigenvalues)
        Finset.univ.val := Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h
  rw [hcp, Polynomial.roots_prod _ _ ?_] at hmem
  · -- hmem : eigW i ∈ bind univ.val (fun j => roots (X - C (f (eigM j))))
    obtain ⟨j, _, hj⟩ := Multiset.mem_bind.mp hmem
    have hj' : hW.eigenvalues i =
        (fun x ↦ NNReal.sqrt x.toNNReal : ℝ → ℝ) (hM.eigenvalues j) := by
      simpa using hj
    -- (P2b 点态胶水) f x = Real.sqrt x（0 ≤ x 时）
    have h0j : 0 ≤ hM.eigenvalues j := le_trans ha (hband j).1
    have hglue : (fun x ↦ NNReal.sqrt x.toNNReal : ℝ → ℝ) (hM.eigenvalues j)
        = Real.sqrt (hM.eigenvalues j) := by
      have h1 : (((hM.eigenvalues j).toNNReal : NNReal) : ℝ) = hM.eigenvalues j :=
        Real.coe_toNNReal _ h0j
      show (NNReal.sqrt (hM.eigenvalues j).toNNReal : ℝ) = Real.sqrt (hM.eigenvalues j)
      rw [Real.coe_sqrt, h1]
    rw [hj', hglue]
    exact ⟨Real.sqrt_le_sqrt (hband j).1, Real.sqrt_le_sqrt (hband j).2⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => Polynomial.X_sub_C_ne_zero _
```

### A.3 Q3 源（/tmp/r17b_probe3_orthmerge.lean）

```lean
import Mathlib

/-!
R17B Q3 探针源（b5c-assembly-probe §Q3）：
P4 双例合并——Wᵀ=W ∧ W*W=(1+A)*(1+A)ᵀ ∧ IsUnit W ⇒ R := W⁻¹*(1+A) 正交。
工程化形状＝单一核心引理（R*Rᵀ=1 纯代数，R16B §P4 例 1 原样 ~15 行）＋
双口径陈述：①Matrix.orthogonalGroup membership（Submonoid 面，主口径）；
②双等式合取（R*Rᵀ=1 ∧ Rᵀ*R=1）。R16B §P4 例 2 的 det 平方路线被
membership 结构替换：mem_orthogonalGroup_iff ↔ A*Aᵀ=1〔UnitaryGroup.lean:297〕
＋mem_orthogonalGroup_iff' ↔ Aᵀ*A=1〔:301〕——Submonoid membership 自带双侧，
两例合并成『一核心＋两陈述』的单定理族。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix

-- § API 签名核验（#check 面）----------------------------------------------

#check @Matrix.mem_orthogonalGroup_iff    -- UnitaryGroup.lean:297（↔ A * Aᵀ = 1）
#check @Matrix.mem_orthogonalGroup_iff'   -- UnitaryGroup.lean:301（↔ Aᵀ * A = 1）
#check @Matrix.orthogonalGroup            -- UnitaryGroup.lean:295（Submonoid abbrev）
#check @Matrix.isUnit_iff_isUnit_det      -- NonsingularInverse.lean:127
#check @Matrix.transpose_nonsing_inv      -- NonsingularInverse.lean:202
#check @Matrix.nonsing_inv_mul            -- NonsingularInverse.lean:217

-- § 核心引理（R16B §P4 例 1 原样）：R*Rᵀ = 1 纯代数 ---------------------------
-- transpose_mul 开转置＋transpose_nonsing_inv 搬 (W⁻¹)ᵀ=(Wᵀ)⁻¹＋代入 hWW 两次消去。
-- 摩擦（R16B §P4 已留档，本组复跑确认）：①mul_nonsing_inv 族 A 显式实参且实例
-- 路径不字节对齐，rw 直接重写不中——须 have 成局部等式再进 calc；②mul_assoc
-- 全局重写先匹配外层，中段需 conv_lhs => arg 2 定向。
theorem r_mul_rTranspose_eq_one {n : Type*} [DecidableEq n] [Fintype n]
    {A W : Matrix n n ℝ} (hW : Wᵀ = W) (hWW : W * W = (1 + A) * (1 + A)ᵀ)
    (hunit : IsUnit W) :
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

-- § 例 1（Q3 主目标·membership 口径）：R ∈ Matrix.orthogonalGroup n ℝ ----------
example {n : Type*} [DecidableEq n] [Fintype n] {A W : Matrix n n ℝ}
    (hW : Wᵀ = W) (hWW : W * W = (1 + A) * (1 + A)ᵀ) (hunit : IsUnit W) :
    (W⁻¹ * (1 + A)) ∈ Matrix.orthogonalGroup n ℝ := by
  have hiff : (W⁻¹ * (1 + A)) ∈ Matrix.orthogonalGroup n ℝ ↔
      (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ = 1 :=
    Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)
  exact hiff.mpr (r_mul_rTranspose_eq_one hW hWW hunit)

-- § 例 2（Q3 双等式口径·合并单定理）：R*Rᵀ=1 ∧ Rᵀ*R=1 ---------------------------
-- membership 一次供给两侧（Submonoid 结构内置双侧性）——R16B §P4 例 2 的
-- det 平方路线（IsUnit.of_mul_eq_one + Rᵀ=R⁻¹ 搬运 ~15 行）被两行替换。
example {n : Type*} [DecidableEq n] [Fintype n] {A W : Matrix n n ℝ}
    (hW : Wᵀ = W) (hWW : W * W = (1 + A) * (1 + A)ᵀ) (hunit : IsUnit W) :
    (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ = 1 ∧
      (W⁻¹ * (1 + A))ᵀ * (W⁻¹ * (1 + A)) = 1 := by
  have hmem : (W⁻¹ * (1 + A)) ∈ Matrix.orthogonalGroup n ℝ := by
    have hiff : (W⁻¹ * (1 + A)) ∈ Matrix.orthogonalGroup n ℝ ↔
        (W⁻¹ * (1 + A)) * (W⁻¹ * (1 + A))ᵀ = 1 :=
      Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)
    exact hiff.mpr (r_mul_rTranspose_eq_one hW hWW hunit)
  have hiff2 : (W⁻¹ * (1 + A)) ∈ Matrix.orthogonalGroup n ℝ ↔
      (W⁻¹ * (1 + A))ᵀ * (W⁻¹ * (1 + A)) = 1 :=
    Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)
  exact ⟨(Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp hmem, hiff2.mp hmem⟩
```

### A.4 Q4 源（/tmp/r17b_probe4_rowsum.lean）

```lean
import Mathlib

/-!
R17B Q4 探针源（b5c-assembly-probe §Q4）：
P5 行和胶水（Gershgorin 独立替通路）——frob B ≤ β ⇒ ∀ k,
∑_{j≠k} |B k j| ≤ √(n−1)·β（逐行 Cauchy–Schwarz：行和 ≤ √(非对角元个数)·
行范数 ≤ √(n−1)·frob B），与 |1+B k k| ≥ 1−β（逆向三角）合并成
n=3 的严格对角占优 ⇒ det (1+B) ≠ 0。关键现成件：
`sq_sum_le_card_mul_sum_sq`（Algebra/Order/Chebyshev.lean:144，『和的平方 ≤
元素数×平方和』＝CS 的 f=g 特例，无单调性前提——根命名空间）。
量纲判定（数值层相容性）不属本文件——Python 精确 Fraction 侧
/tmp/r17b_dimension_q4.log。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。

迭代摩擦留档（v1→v3）：①`sq_sum_le_card_mul_sum_sq` 是根命名空间
（Chebyshev.lean section Mul 在 namespace Finset 之前——`Finset.` 前缀不命中）；
②`Finset.single_le_sum` 本 rev 带 nonneg 副条件先行（(∀ i ∈ s, 0 ≤ f i) →
a ∈ s → f a ≤ ∑，双显式实参）；③|a+b| ≤ |a|+|b| 的老名 `abs_add` 不在
（新层级名 `abs_add_le`），逆向三角改走 by_cases＋le_abs_self/abs_neg；
④frob def 的索引类型须 Type*（Type 0 版在泛型定理面 universe 不合）；
⑤sq_abs（Ring/Abs.lean:81）非 abs_sq。
-/

open Matrix

-- § frob def（TableB5Core.lean:67 同款值口径；索引类型 Type* 化——摩擦④）---
noncomputable def frob {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (M i j)^2)

-- ℛ 面拆分底座（摩擦⑥⑦：本 rev 的 Finset.single_le_sum 与
-- Finset.sum_le_sum_of_subset 均系 ℕ 面〔CanonicallyOrderedAdd 前提〕——
-- ℝ 上须走 insert_erase 拆分自建，~3 行）
theorem univ_eq_erase_add {n : Type*} [DecidableEq n] [Fintype n] (X : n → ℝ) (k : n) :
    ∑ i, X i = X k + ∑ i ∈ Finset.univ.erase k, X i := by
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ k)]
  rw [Finset.sum_insert (Finset.notMem_erase k Finset.univ)]

-- § API 签名核验（#check 面）----------------------------------------------
#check @sq_sum_le_card_mul_sum_sq          -- Chebyshev.lean:144（CS f=g 特例，根命名空间）
#check @det_ne_zero_of_sum_row_lt_diag    -- Gershgorin.lean:63（R16B §P5 已探）
#check @Finset.card_erase_of_mem
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_mul
#check @Real.sqrt_lt
#check @sq_abs                            -- Ring/Abs.lean:81（|a|² = a²）

-- § 定理 1（Q4 主目标·行和胶水）：frob B ≤ β ⇒ 逐行非对角绝对值和 ≤ √(n−1)·β --
theorem frob_row_sum_le {n : Type*} [DecidableEq n] [Fintype n] {B : Matrix n n ℝ}
    {β : ℝ} (hβ : 0 ≤ β) (hfrob : frob B ≤ β) (k : n) :
    ∑ j ∈ Finset.univ.erase k, |B k j| ≤ Real.sqrt ((Fintype.card n : ℝ) - 1) * β := by
  -- 平方和链：全阵 ≤ β²（frob 开方侧）
  have hbeta : (∑ i, ∑ j, (B i j)^2) ≤ β^2 := by
    have h0 : (0:ℝ) ≤ ∑ i, ∑ j, (B i j)^2 := by positivity
    unfold frob at hfrob
    rw [← Real.sq_sqrt h0, pow_two, pow_two]
    exact mul_le_mul hfrob hfrob (Real.sqrt_nonneg _) hβ
  have hsq : ∑ j ∈ Finset.univ.erase k, |B k j|^2 ≤ β^2 := by
    have hrow : ∑ j ∈ Finset.univ.erase k, (B k j)^2 ≤ ∑ j, (B k j)^2 := by
      have hsplit := univ_eq_erase_add (fun j => (B k j)^2) k
      have hdiag : (0:ℝ) ≤ (B k k)^2 := sq_nonneg _
      linarith
    have htot : ∑ j, (B k j)^2 ≤ ∑ i, ∑ j, (B i j)^2 := by
      have hsplit := univ_eq_erase_add (fun i => ∑ j, (B i j)^2) k
      have hrest : (0:ℝ) ≤ ∑ i ∈ Finset.univ.erase k, ∑ j, (B i j)^2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (B i j)
      linarith
    have habs : ∑ j ∈ Finset.univ.erase k, |B k j|^2 = ∑ j ∈ Finset.univ.erase k, (B k j)^2 := by
      rw [← Finset.sum_congr rfl fun j _ => (sq_abs (B k j)).symm]
    rw [habs]
    exact le_trans (le_trans hrow htot) hbeta
  -- CS（Chebyshev.lean:144 f=g 特例）：(∑|·|)² ≤ card·∑|·|²
  have hcs : (∑ j ∈ Finset.univ.erase k, |B k j|)^2 ≤
      (Finset.univ.erase k).card * ∑ j ∈ Finset.univ.erase k, |B k j|^2 :=
    sq_sum_le_card_mul_sum_sq
  have hnn : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase k, |B k j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hcard : ((Finset.univ.erase k).card : ℝ) = (Fintype.card n : ℝ) - 1 := by
    have hpos : (1:ℕ) ≤ Fintype.card n := Fintype.card_pos_iff.mpr ⟨k⟩
    have h1 : ((Finset.univ.erase k).card : ℕ) = Fintype.card n - 1 :=
      Finset.card_erase_of_mem (Finset.mem_univ k)
    rw [h1, Nat.cast_sub hpos, Nat.cast_one]
  -- 开方收口：∑|·| ≤ √(card·β²) ＝ √(card−1)·β（hβ:β≥0）
  have hstep1 : ∑ j ∈ Finset.univ.erase k, |B k j| ≤
      Real.sqrt ((Finset.univ.erase k).card * ∑ j ∈ Finset.univ.erase k, |B k j|^2) := by
    have h1 := Real.sqrt_le_sqrt hcs
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn] at h1
  calc ∑ j ∈ Finset.univ.erase k, |B k j|
      ≤ Real.sqrt ((Finset.univ.erase k).card * ∑ j ∈ Finset.univ.erase k, |B k j|^2) :=
        hstep1
    _ ≤ Real.sqrt (((Fintype.card n : ℝ) - 1) * β^2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [← hcard]
        exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = Real.sqrt ((Fintype.card n : ℝ) - 1) * β := by
        have hc1 : (1:ℝ) ≤ (Fintype.card n : ℝ) := by
          have h : (1:ℕ) ≤ Fintype.card n := Fintype.card_pos_iff.mpr ⟨k⟩
          exact_mod_cast h
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq_eq_abs, abs_of_nonneg hβ]

-- § 定理 2（Q4 合并面·n=3 Gershgorin）：√2·β < 1−β ⇒ det (1+B) ≠ 0 -----------
theorem gershgorin_fin3 {B : Matrix (Fin 3) (Fin 3) ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hdom : Real.sqrt 2 * β < 1 - β) (hfrob : frob B ≤ β) :
    (1 + B).det ≠ 0 := by
  have hcard : Real.sqrt ((Fintype.card (Fin 3) : ℝ) - 1) = Real.sqrt 2 := by
    norm_num [Fintype.card_fin]
  have hrow : ∀ k, ∑ j ∈ Finset.univ.erase k, |B k j| ≤ Real.sqrt 2 * β := by
    intro k
    have h := frob_row_sum_le hβ hfrob k
    rwa [hcard] at h
  -- 对角元下界：|1 + B k k| ≥ 1 − β（逆向三角 by_cases 版＋单元素 ≤ frob）
  have hdiag : ∀ k, 1 - β ≤ |1 + B k k| := by
    intro k
    have hbk : |B k k| ≤ β := by
      have hs1 : (B k k)^2 ≤ ∑ j, (B k j)^2 := by
        have hsplit := univ_eq_erase_add (fun j => (B k j)^2) k
        have hrest : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase k, (B k j)^2 :=
          Finset.sum_nonneg fun j _ => sq_nonneg (B k j)
        linarith
      have hs2 : ∑ j, (B k j)^2 ≤ ∑ i, ∑ j, (B i j)^2 := by
        have hsplit := univ_eq_erase_add (fun i => ∑ j, (B i j)^2) k
        have hrest : (0:ℝ) ≤ ∑ i ∈ Finset.univ.erase k, ∑ j, (B i j)^2 :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (B i j)
        linarith
      have hS : (∑ i, ∑ j, (B i j)^2) ≤ β^2 := by
        have h0 : (0:ℝ) ≤ ∑ i, ∑ j, (B i j)^2 := by positivity
        unfold frob at hfrob
        rw [← Real.sq_sqrt h0, pow_two, pow_two]
        exact mul_le_mul hfrob hfrob (Real.sqrt_nonneg _) hβ
      have h2 : |B k k|^2 ≤ β^2 := by
        rw [sq_abs]
        exact le_trans (le_trans hs1 hs2) hS
      have hu : (0:ℝ) ≤ |B k k| := abs_nonneg _
      nlinarith [h2]
    have htri : (1:ℝ) - |B k k| ≤ |1 + B k k| := by
      by_cases hc : (0:ℝ) ≤ 1 + B k k
      · rw [abs_of_nonneg hc]
        have hle := le_abs_self (-B k k)
        rw [abs_neg] at hle
        linarith
      · have hlt : 1 + B k k < 0 := lt_of_not_ge hc
        rw [abs_of_neg hlt]
        have hle := le_abs_self (-B k k)
        rw [abs_neg] at hle
        linarith
    linarith
  -- Gershgorin 注入（R16B §P5 例 1 同款）
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  have hoff : ∀ j ∈ Finset.univ.erase k, (1 + B) k j = B k j := by
    intro j hj
    have hne : k ≠ j := fun hc => (Finset.mem_erase.mp hj).1 hc.symm
    have h1 : (1 : Matrix (Fin 3) (Fin 3) ℝ) k j = 0 := by
      simp [Matrix.one_apply, hne]
    rw [Matrix.add_apply, h1, zero_add]
  have hd : (1 + B) k k = 1 + B k k := by
    rw [Matrix.add_apply, Matrix.one_apply, if_pos rfl]
  rw [Finset.sum_congr rfl fun j hj => by rw [hoff j hj, Real.norm_eq_abs], hd,
    Real.norm_eq_abs]
  calc ∑ j ∈ Finset.univ.erase k, |B k j| ≤ Real.sqrt 2 * β := hrow k
    _ < 1 - β := hdom
    _ ≤ |1 + B k k| := hdiag k

-- § 例 3（Q4 具体数值例）：B = (1/10)·全一阵（Fin 3）⇒ det (1+B) ≠ 0 ----------
-- frob² = 9·(1/100) = 9/100 ⟹ β = 3/10 < 1/(1+√2) ≈ 0.4142（量纲域内）。
example : ((1 + Matrix.of (fun (_ : Fin 3) (_ : Fin 3) => (1:ℝ)/10) :
    Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  have hβ : (0:ℝ) ≤ 3/10 := by norm_num
  have hfrob : frob (Matrix.of (fun (_ : Fin 3) (_ : Fin 3) => (1:ℝ)/10)) ≤ 3/10 := by
    have hsum : (∑ i, ∑ j, ((Matrix.of (fun (_ : Fin 3) (_ : Fin 3) => (1:ℝ)/10) :
        Matrix (Fin 3) (Fin 3) ℝ) i j)^2) = 9/100 := by
      simp [Matrix.of_apply]
      norm_num
    unfold frob
    rw [hsum]
    norm_num
  have hdom : Real.sqrt 2 * (3/10) < 1 - 3/10 := by
    have h2 : (2:ℝ) < (7/3)^2 := by norm_num
    have h1 : Real.sqrt 2 < 7/3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr h2
    nlinarith [h1]
  exact gershgorin_fin3 hβ hdom hfrob
```

（注：A.1–A.4 转录与 /tmp 四源件逐字一致；源件头部『本件为 /tmp 探针』字样
为源件自带注释。A.4 头部『迭代摩擦留档（v1→v3）』段为源件自带的初段记录，
后续摩擦（⑥⑦ ℝ/ℕ 面 API 分层与 cast 链）在 §Q4 摩擦小节全文留档。）

## 附录 B：本会话已跑证据索引（全部 /tmp 留档，门 G3 逐一在盘核验非零字节）

| 日志/源 | 内容 | 结果 |
|---|---|---|
| /tmp/r17b_grep_psdbridge.log | Q1 grep（[A] PosDef.lean 桥四条） | 在档（390 字节） |
| /tmp/r17b_probe1_psdbridge.lean | Q1 源（9 #check＋2 example） | 编译对象（附录 A.1 转录） |
| /tmp/r17b_probe1_psdbridge.log | Q1 运行日志 | exit_code=0 零 error（终版 27.5s） |
| /tmp/r17b_grep_cfc2.log | Q2 grep（[A] roots_charpoly＋charpoly_cfc_eq 签名） | 在档（997 字节） |
| /tmp/r17b_probe2_sqrtband.lean | Q2 源（7 #check＋2 example） | 编译对象（附录 A.2 转录） |
| /tmp/r17b_probe2_sqrtband.log | Q2 运行日志 | exit_code=0 零 error（终版 5.0s） |
| /tmp/r17b_probe2_default_hb_test.lean | Q2 去心跳放宽版源（侧证件） | 编译对象 |
| /tmp/r17b_probe2_default_hb_test.log | Q2 默认 200000 心跳侧证 | exit_code=0（40.3s）——心跳摩擦降档证据 |
| /tmp/r17b_grep_orth.log | Q3 grep（[A] orthogonalGroup membership 三条） | 在档（902 字节） |
| /tmp/r17b_probe3_orthmerge.lean | Q3 源（6 #check＋1 核心引理＋2 example） | 编译对象（附录 A.3 转录） |
| /tmp/r17b_probe3_orthmerge.log | Q3 运行日志 | exit_code=0 零 error（终版 14.6s） |
| /tmp/r17b_grep_rowsum.log | Q4 grep（[A]–[D] 四面；[D] 命中 sq_sum_le_card_mul_sum_sq） | 在档（1621 字节） |
| /tmp/r17b_probe4_rowsum.lean | Q4 源（frob def＋helper＋2 定理＋1 数值例） | 编译对象（附录 A.4 转录） |
| /tmp/r17b_probe4_rowsum.log | Q4 运行日志 | exit_code=0 零 error（终版 6.2s） |
| /tmp/r17b_dimension_q4.log | Q4 量纲判定（Fraction 精确，TableB5Data.lean 源直读） | 【不相容】＋恒等 True＋δ 子域 83.5% |
| /tmp/r17b_final_pass.log | 四探针最终验证趟（exit_code＋errors＋墙钟逐条＋toolchain 亲验） | 4/4 exit_code=0 |
| /tmp/r17b_final_run.sh | 终跑脚本（生成上行的 shell 源，可复现） | 在盘 |

（门核验：以上 17 条路径须全部在盘且非零字节；『在档』字节数为本会话 ls 亲见。）
