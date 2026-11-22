# b5-core-study.md — B5 解析本体（d_P(X,Y) ≤ C·δ 证明本体）Lean 化预研件

任务锚：r15c-b5core-study（campaign dwfrun-f9904baf 第 10 轮，D61 裁决 4）。
定位：**零 Lean 件入库、零求解、纯 notes 产出**——为后续轮次 B5 解析本体的
Lean 化给出方向确定性（步骤级 Mathlib 可用性映射＋缺口＋工程量＋切分建议）。
本件不含任何新定理证明；所有『可走通』结论均以本会话实跑探针为据（探针＝
`lake env lean` 编译验证，非证明本体入库）；Mathlib 版本＝本仓
`formal/lean/.lake/packages/mathlib` @ **d13f23b723b8a846827a245b89c10fc7d3f11612**，
toolchain `leanprover/lean4:v4.34.1`（两日志头部均有记录）。

诚实口径（全文适用）：
- **已跑**＝本会话在 thomson-n9/formal/lean 下亲跑且日志在 /tmp 留档（每条带路径）；
- **未跑**＝本会话没有执行（如实标注，不做推断性『应该可以』）；
- 书面推导＝l4_procrustes.py docstring 的数学论证（数值层严格、证明本体未过 Lean——
  R14 常数件 docstring 双侧如实先例）；
- 本件不出现『证明完成』『本体入 Lean』类越权陈述——本体尚未开工，所有结论均系
  预研性质（探针编译通过 ≠ 证明完成）。

审计对象：`numerics/bounds/l4_procrustes.py`（470 行，R4 落盘）——其 docstring
步骤 1–6（:20–:32）即本件 §1 的复述对象；其常数层（λ 界/装配/sqrt 界/C_valid/
δ_max_valid）已由 R14 表 B 首件 Lean 化（TableB5.lean 354 行 17 定理＋
TableB5Data.lean 205 行 24 def 33 定理，commit 4be81bf），**d_P ≤ C·δ 的推理
本体（本件 §1 六步骤）不在其中**——正是本预研的目标缺口。

零求解声明：本任务零求解（heavySolves = 0，零重求解；纯 notes＋探针产出，
不触四账本与 endgame.json）。

---

## §1 步骤逐条数学复述

总设定（l4_procrustes.py:9–18 定理陈述）：X = TTP 构型（9×3 行单位），
S = XᵀX 对称正定，谱 λ₁ ≥ λ₂ ≥ λ₃ > 0，σᵢ = √λᵢ。Y ∈ ℝ⁹ˣ³ 行单位，固定标号
|⟨y_i,y_j⟩ − ⟨x_i,x_j⟩| ≤ δ（∀ i<j）。η := ‖G_Y − G_X‖_F，β := λ₁η/λ₃²。
适用域：β ≤ min(1/2, √λ₃/(2σ₁))（即 δ ≤ δ_max，数值层 δ_max ≈ 0.1712，
C ≈ 14.879，C_chord = 2C ≈ 29.76——l4.json 在档值，R14 常数层已入 Lean 件）。
结论：d_P(X,Y) := min_{Q∈O(3)} ‖X − YQ‖_F ≤ (σ₁³/λ₃² + 2/σ₃)·η ≤ C·δ。
（η ≤ √72·δ：E 对角恒 0 ⇒ 72 个非对角元逐个 ≤ δ，Cauchy–Schwarz。）

以下逐步复述（陈述／前提／机器可验面与解析面切分）。**机器可验面**＝Lean 中
可机械核验的等式/不等式推导（恒等式核验、逐项算术、既有引理调用）；
**解析面**＝需要构造数学论证的部分（谱论、不等式方向、范数比较）——这两面
的切分决定 §2 的 API 映射与 §4 的工程量。

### 步骤 1（E 分解）

- **陈述**：D := Y − X ⇒ E := G_Y − G_X = (X+D)(X+D)ᵀ − XXᵀ = XDᵀ + DXᵀ + DDᵀ；
  E 对角恒 0（X、Y 双侧行单位：⟨y_i,y_i⟩ = ⟨x_i,x_i⟩ = 1）。
- **前提**：X、Y 行单位（‖x_i‖ = ‖y_i‖ = 1 ∀i）；G := MMᵀ 记法。
- **机器可验面**：三交叉项展开是纯环恒等式（矩阵层 add_mul/mul_add 分配＋
  conjTranspose_add，abel 收尾——本会话探针亲验 7 行本体走通，
  /tmp/r15c_probe4_algebra.log，S1 例）；对角恒 0 是逐元 ‖y_i‖² − ‖x_i‖² = 0
  的行单位前提代入（elementwise ring/norm_num 面）。
- **解析面**：无实质解析内容（η ≤ √72·δ 的 Cauchy–Schwarz 一步属步骤 6 装配
  前的量化面——见 §2 步骤 1 行的『可改造』标注）。

### 步骤 2（投影分解）

- **陈述**：D_∥ := XA（A := S⁻¹XᵀD ∈ ℝ³ˣ³），D_⊥ := D − D_∥ 满足 XᵀD_⊥ = 0
  （D_⊥ 列 ⊥ col(X)），P₀ := XS⁻¹Xᵀ（col(X) 上正交投影）。
- **前提**：S = XᵀX 可逆（λ₃ > 0 ⇒ S 正定 ⇒ det S > 0 ⇒ 可逆）。
- **机器可验面**：XᵀD_⊥ = XᵀD − (XᵀX)S⁻¹(XᵀD) = XᵀD − S·S⁻¹·(XᵀD) = 0 是
  mul_assoc 搬运＋矩阵消去（探针亲验 2 行本体，
  /tmp/r15c_probe4_algebra.log，S2 例）；
  P₀ 幂等（P₀² = X(S⁻¹SX)S⁻¹Xᵀ 归位）与对称同样纯环。
- **解析面**：λ₃ > 0 ⇒ S 可逆这一前提桥（数值层 R14 已有 λ₃ ≥ l₃ > 0 的二次型
  夹逼 ttp_sandwich_lo；形式层需二次型夹逼 ⇒ PosDef ⇒ IsUnit 的转换链，
  Mathlib 现成 `Matrix.PosSemidef.posDef_iff_isUnit`
  /`Matrix.PosDef...`（Analysis/Matrix/Order.lean:180 场，grep 级在场——未跑
  使用级探针，如实标注）。

### 步骤 3（混合块 σ₃-范数下界）

- **陈述**：P₀E(I−P₀) = XD_⊥ᵀ + D_∥D_⊥ᵀ（混合块），而
  ‖XD_⊥ᵀ‖²_F = tr(S·D_⊥ᵀD_⊥) ≥ λ₃·‖D_⊥‖²_F
  （trace 不等式：A ⪰ λI, B ⪰ 0 ⇒ tr(AB) ≥ λ·tr(B) 取 A = S, λ = λ₃, B = D_⊥ᵀD_⊥），
  加上 ‖D_∥D_⊥ᵀ‖_F ≤ ‖D_∥‖_F·‖D_⊥‖_F（Frobenius 次乘）与
  ‖E‖_F = ‖P₀E(I−P₀) + (其余块)‖ 的下界拼装 ⇒ (σ₃ − ‖D_∥‖_F)·‖D_⊥‖_F ≤ η。
- **前提**：S ⪰ λ₃I（谱下界）；D_⊥ᵀD_⊥ ⪰ 0（Gram 型恒半正定）；β < 1
  保证 σ₃ − ‖D_∥‖ > 0 一侧。
- **机器可验面**：块分解恒等式 P₀E(I−P₀) = XD_⊥ᵀ + D_∥D_⊥ᵀ 展开后是纯环
  （代入 E = XDᵀ+DXᵀ+DDᵀ 与 D = D_∥+D_⊥、P₀X = X、XᵀD_⊥ = 0 消项——
  mul_assoc/sub 分布面）；‖XD_⊥ᵀ‖²_F = tr(S·D_⊥ᵀD_⊥) 是 Frobenius 范数定义
  （∑ᵢⱼ aᵢⱼ²）与 trace 定义（∑ᵢ (MN)ᵢᵢ）的 sum 搬运恒等式。
- **解析面**：**trace 不等式本体**（tr(SB) ≥ λ₃ tr(B)）——本会话探针亲验
  自证路线可走通且体量小（T1 本体 15 行＋T2 线性推论 6 行，
  /tmp/r15c_probe3_trace.log：T1 双 PSD 乘积 trace 非负＋T2 A−tI ⪰ 0 ⇒
  t·tr(B) ≤ tr(AB)，全证明在档 /tmp/r15c_probe3_trace.lean，源件 43 行）；
  Frobenius 次乘 `Matrix.frobenius_norm_mul` 现成（#check 亲验，
  /tmp/r15c_probe1_api.log P6）。剩余解析动作：从 λ₃ ≥ l₃（二次型口径）到
  S ⪰ l₃·I（PosSemidef 口径）的形式转换（二次型 ∀v vᵀ(S−l₃I)v ≥ 0 ⇔
  PosSemidef——Mathlib 的 `Matrix.PosSemidef` 定义即 dotProduct 口径
  （LinearAlgebra/Matrix/PosDef.lean:60 def），grep 级一致——未跑使用级
  探针，如实标注）。

### 步骤 4（平行块）

- **陈述**：XᵀEX = S·B·S，其中 B := A + Aᵀ + AAᵀ = (I+A)(I+A)ᵀ − I =
  S⁻¹(XᵀEX)S⁻¹，故 ‖B‖_F ≤ ‖XᵀEX‖_F/λ₃² ≤ λ₁η/λ₃² =: β。
- **前提**：S 可逆（同步骤 2）；‖S⁻¹·M·S⁻¹‖_F ≤ ‖M‖_F/λ₃²（双侧算子范数压缩）。
- **机器可验面**：B 的两个恒等式（B = A+Aᵀ+AAᵀ = (I+A)(I+A)ᵀ−I；XᵀEX =
  S(B)S 的展开代入 E）都是纯环；S⁻¹(XᵀEX)S⁻¹ = B 是两侧乘 S⁻¹ 的代数。
- **解析面**：**范数压缩不等式** ‖S⁻¹MS⁻¹‖_F ≤ ‖M‖_F/λ₃²——需
  ‖S⁻¹v‖₂ ≤ ‖v‖₂/λ₃（对称正定阵逆的算子范数界）＋ Frobenius 次乘两连。
  这是谱论面：λ₃ ≤ S 的最小特征值 ⇒ S ⪰ λ₃I ⇒ ‖Sv‖ ≥ λ₃‖v‖ ⇒ 逆压缩。
  Mathlib 无现成『对称阵算子范数 = 谱半径』API（grep 级：Spectrum.lean 有
  谱定理全套（见 §2 P4），但 Rayleigh 商极值特征化缺位——需自建中件）。
  λ₁ 界（λ₁η ≤ u₁η 数值侧已 R14 Lean 化）沿用。

### 步骤 5（旋转规范：右极分解）

- **陈述**：取右极分解 I+A = W·R（W = ((I+A)(I+A)ᵀ)^{1/2} 对称 PSD，R ∈ O(3)），
  β < 1 ⇒ I+A 可逆 ⇒ 分解存在；W 的特征值 = I+A 的奇异值 ∈ [√(1−β), √(1+β)]
  （由 (I+A)(I+A)ᵀ = I + B 且 ‖B‖ 小 ⇒ 谱夹逼），故 ‖W − I‖₂ ≤ 1−√(1−β) ≤ β。
  于是 YR = XW + D_⊥R ⇒ ‖X − YR‖_F ≤ ‖X − XW‖_F + ‖D_⊥R‖_F ≤ σ₁β + ‖D_⊥‖_F。
- **前提**：β < 1（I+A 可逆）；W 与 R 的存在性与正交性；‖D_⊥R‖ = ‖D_⊥‖
  （正交不变性）；‖X(W−I)‖_F ≤ σ₁‖W−I‖₂（σ₁ = X 的最大奇异值＝谱上界）。
- **机器可验面**：YR = XW + D_⊥R 的代入展开（Y = X + D = X + XA + D_⊥，
  (I+A)R = W 消项）是纯环；‖X−XW‖ ≤ ‖X‖·‖W−I‖ 一侧是次乘。
- **解析面**：**全部实质难点在此**——(i) 极分解存在性本体（Mathlib 无矩阵
  极分解：grep 三面证据 /tmp/r15c_grep_polar.log [D][E][F]，全 Mathlib 无
  `Matrix.polar`/`polarDecomp` 标识符，负向探针 /tmp/r15c_probe2_absent.log
  N2 两条 unknown 亲验）；构造路线＝CFC.sqrt（PSD 平方根现成，探针亲验
  /tmp/r15c_probe1_api.log P5：`CFC.sqrt`/`CFC.sqrt_nonneg`/
  `CFC.sqrt_mul_sqrt_self`/`CFC.sq_sqrt` 在 Matrix ℝ 上随 `open scoped
  MatrixOrder` 可用）定义 W，R := W⁻¹(I+A)，R 的正交性由 W² = (I+A)(I+A)ᵀ
  纯代数推出——但 (ii) **谱夹逼**（I+B 的特征值 ∈ [1−β,1+β] ⇒ W 特征值 ∈
  [√(1−β),√(1+β)]）与 (iii) **算子范数-特征值桥**（‖W−I‖₂ ≤ max|特征值−1|）
  均缺现成 API（谱定理件 `Matrix.IsHermitian.spectral_theorem` 在场，
  #check 亲验 /tmp/r15c_probe1_api.log P4；但特征值极值/Rayleigh 特征化与
  CFC.sqrt 的特征值交换性 API 未探——§3 风险展开）。

### 步骤 6（装配 σ₁β + 2η/σ₃）

- **陈述**：σ₁β ≤ σ₃/2（适用域）⇒ ‖D_⊥‖_F ≤ η/(σ₃−σ₁β) ≤ 2η/σ₃，故
  d_P ≤ ‖X−YR‖_F ≤ σ₁β + 2η/σ₃ = (σ₁·λ₁/λ₃²)η + (2/σ₃)η = (σ₁³/λ₃²)η + (2/σ₃)η；
  R ∈ O(3) 给出 min 的上界实现（d_P 的 min 由所展 Q = R 见证）。
- **前提**：步骤 3–5 全链；β ≤ min(1/2, σ₃/(2σ₁)) 数值不等式（R14 的
  delta_max_valid 同式先例）；d_P := min_{Q∈O(3)}… 的陈述形式选择
  （∃ Q ∈ O(3) 见证式 vs ⨅ 式——§5 切分决策点）。
- **机器可验面**：全链是有理不等式算术（linarith/nlinarith/norm_num 面）＋
  范数三角不等式（`norm_add_le`/`norm_sub_le` 现成 API 级，未单独探——
  标准 API，如实标注未跑）＋正交右乘不变性 ‖M·R‖_F = ‖M‖_F（正交群保
  Frobenius——Mathlib 需经由 ‖M·Q‖ 逐列/逐行内积不变或 Matrix.orthogonalGroup
  性质中件，grep 级未定位到直接引理——如实标注为待查项）。
- **解析面**：无新解析对象（装配层）。

---

## §2 Mathlib 可用性映射

版本口径：Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612（本仓
lake-manifest 锚定），toolchain v4.34.1。标注三档：
**现成**＝#check/example 探针亲验在场且签名可用（/tmp/r15c_probe1_api.log，
exit 0，40.96s）；**可改造**＝grep 定位到近邻 API 但需适配/包装（grep 级证据，
标注未跑使用级探针）；**缺位自建**＝grep＋负向探针双面证据缺位（
/tmp/r15c_probe2_absent.log，exit_code=1 按设计，6 条 unknown）。

### §2.1 缺位总证据（grep 两条缺位转录）

**hessian 缺位**（已跑 /tmp/r15c_grep_hessian.log，三面）：

```
== [A] hessian: any file named *hessian* anywhere in Mathlib ==
-- (empty above = no such file) --

== [B] hessian: case-insensitive content grep over Mathlib/Analysis ==
-- (empty above = zero hits in Analysis/) --

== [C] hessian: whole-Mathlib content grep (scoped outside Analysis too) --
-- end [C] --
```

（[C] 亦空：全 Mathlib 无 hessian 内容命中 ⇒ Analysis/ 无 hessian 模块是
全库级缺位，非目录级。）

**polar 缺位**（已跑 /tmp/r15c_grep_polar.log，四面）：

```
== [D] polar: file names containing 'polar' under Analysis/Matrix or LinearAlgebra/Matrix ==
-- (empty above = no such file) --

== [E] polar: case-insensitive content grep Analysis/Matrix + LinearAlgebra/Matrix ==
-- (empty above = zero hits) --

== [F] polar decomposition identifiers: Matrix.polar / polarDecomp / Matrix.IsHermitian.polar in whole Mathlib ==
-- end [F] --
```

（[H] 全库 'polar' 词面命中均为**另一概念**：polarization identity
（Analysis/InnerProductSpace/Basic.lean:512 起，内积极化恒等式）、polar set
（Analysis/LocallyConvex/Polar.lean）、polar coordinates
（Analysis/SpecialFunctions/PolarCoord.lean）——与矩阵极分解无关，本会话逐条
目检确认，已跑 /tmp/r15c_grep_polar.log [H] 段。）

负向探针（已跑 /tmp/r15c_probe2_absent.log，预期失败＝6 条 unknown identifier
/unknown constant 逐条实证缺位名）：

```
error(lean.unknownIdentifier): Unknown constant `Matrix.PosSemidef.trace_mul_nonneg`
error(lean.unknownIdentifier): Unknown constant `Matrix.polarDecomp`
error(lean.unknownIdentifier): Unknown constant `Matrix.IsHermitian.polar`
error(lean.unknownIdentifier): Unknown constant `Matrix.nonspectral_sqrt`
error(lean.unknownIdentifier): Unknown constant `Matrix.IsHermitian.sqrt'`
error(lean.unknownIdentifier): Unknown identifier `hessian`
```

（注：`Matrix.nonspectral_sqrt`/`Matrix.IsHermitian.sqrt'` 是历史版本 PSD 平方根
名——本 rev 已被 CFC.sqrt 取代移除，两条 unknown 亲验其不在场，防止后续轮次
按旧名引用。）

### §2.2 逐步映射表

| 步骤 | 面向 | API/引理 | 档位 | 证据 |
|---|---|---|---|---|
| 1 | E 三项展开 | `Matrix.add_mul`/`Matrix.mul_add`/`Matrix.conjTranspose_add`＋`abel` | 现成 | 探针 4 S1 本体 7 行亲验（/tmp/r15c_probe4_algebra.log） |
| 1 | E 对角恒 0 | 行单位前提逐元代入（elementwise ring/norm_num） | 现成（标准面，未单独探） | 未跑——如实标注 |
| 1 | η ≤ √72·δ | 72 非零元 Cauchy–Schwarz（`Finset.sum_le_sum`+`Real.sqrt_le_sqrt` 拼装） | 可改造 | grep 级（标准 Finset API），未跑探针 |
| 2 | D_⊥ 正交 | mul_assoc 消去 | 现成 | 探针 4 S2 本体 2 行亲验（同上日志） |
| 2 | P₀ 幂等/对称 | 纯环 | 现成 | 与 S1/S2 同面（未单独探） |
| 2 | λ₃>0 ⇒ S 可逆 | `Matrix.PosSemidef.posDef_iff_isUnit`（Analysis/Matrix/Order.lean:180）＋二次型夹逼桥 | 可改造 | grep 级在场（Order.lean:199 posDef_iff_det_ne_zero 同场）；未跑探针 |
| 3 | 块分解恒等式 | mul_assoc/sub 分布 | 现成 | 探针 4 同面 |
| 3 | tr(AB)≥0（双 PSD） | **缺位自建**：`CStarAlgebra.nonneg_iff_eq_star_mul_self`（Rpow/Basic.lean:380）＋`Matrix.trace_mul_comm`＋`Matrix.posSemidef_conjTranspose_mul_self`（PosDef.lean:384）＋`Matrix.PosSemidef.trace_nonneg`（PosDef.lean:350）四件套 | 缺位自建（路线已探针亲验可走通，T1 本体 15 行） | /tmp/r15c_probe3_trace.log T1 |
| 3 | A⪰tI ⇒ t·tr(B)≤tr(AB) | T1＋`Matrix.trace_add`/`trace_smul` 线性拆分 | 缺位自建（同上路线，6 行） | 同上 T2 |
| 3 | ‖XD_⊥ᵀ‖²_F = tr(S·D_⊥ᵀD_⊥) | `Matrix.frobenius_norm_def`（Analysis/Matrix/Normed.lean:561）＋sum 搬运 | 可改造 | grep 级在场；探针 1 P6 已验范数次乘在场（/tmp/r15c_probe1_api.log） |
| 3 | Frobenius 次乘 | `Matrix.frobenius_norm_mul`（Normed.lean:666） | 现成 | #check 亲验（探针 1 P6） |
| 4 | B 三恒等式 | 纯环（含 `Matrix.sub_mul`/`Matrix.mul_sub`） | 现成 | 探针 4 同面（sub_mul 方向差异留档 §2.3） |
| 4 | ‖S⁻¹MS⁻¹‖ ≤ ‖M‖/λ₃² | 对称正定逆的算子范数界——**无现成 API** | 缺位自建（中件） | grep 级：Spectrum.lean 谱定理在场（探针 1 P4 亲验）但 Rayleigh 极值特征化未定位；未跑探针 |
| 5 | W := PSD 平方根 | `CFC.sqrt`/`CFC.sqrt_nonneg`/`CFC.sqrt_mul_sqrt_self`/`CFC.sq_sqrt`（Rpow/Basic.lean:235–264、:641）＋`open scoped MatrixOrder` 实例 | 现成 | Matrix ℝ 上 example 亲验（探针 1 P5，含 W·W=A 与 0≤W 两例） |
| 5 | R := W⁻¹(I+A) 正交 | W² 恒等式＋代数 | 缺位自建（小件，纯代数——依赖 W²=(I+A)(I+A)ᵀ） | 路线草案（§3.1）；未单独探 |
| 5 | 谱夹逼 [√(1−β),√(1+β)] | `Matrix.IsHermitian.eigenvalues`/`spectral_theorem`（Analysis/Matrix/Spectrum.lean:60/:143） | 缺位自建（大件） | 谱定理 #check 亲验（探针 1 P4）；夹逼引理本体缺位（grep 级：eigenvalues_le/mono 类无命中） |
| 5 | ‖W−I‖₂ ≤ 1−√(1−β) ≤ β | 算子范数-特征值桥 | 缺位自建（中件） | grep 级无直接 API；未跑探针 |
| 5 | ‖M·R‖_F = ‖M‖_F（正交不变） | 正交群保范 | 可改造/待查 | grep 级未定位直接引理（`Matrix.orthogonalGroup` 本身在场，探针 1 P7 亲验）；如实标注待查 |
| 6 | 不等式装配 | linarith/nlinarith/norm_num | 现成 | R14 C_valid/delta_max_valid 同式先例（TableB5.lean:234/:288） |
| 6 | 范数三角 | `norm_add_le`/`norm_sub_le` | 现成（标准面） | 未单独探——如实标注 |
| 6 | d_P 陈述形式 | `Matrix.orthogonalGroup`（Submonoid）＋∃Q 见证式 | 现成/决策点 | #check 亲验（探针 1 P7）；形式选择见 §5 |

### §2.3 探针亲历的工程摩擦（对 §4 分档有直接输入）

（来源：本会话探针 4 的 v1–v10 迭代史——**过程输出未逐版留档**（/tmp 日志为
终版覆盖式），摩擦点清单为亲历记录，最终版日志 /tmp/r15c_probe4_algebra.log
（v11，exit 0）在档：）

1. **ᴴ-模式 rewrite 的实例路径坑**：`rw [Matrix.conjTranspose_add]` 以模式形式
   反复找不到 `(?M + ?N)ᴴ`（即使目标字面含 `(X + D)ᵀ`，v3/v5 亲历）；解法＝
   显式实参 `have h : (X+D)ᵀ = Xᵀ + Dᵀ := Matrix.conjTranspose_add X D` 后再 rw。
   推论：**所有含 ᴴ 的引理调用建议一律显式实参化**——B5a/B5b 的 ring 面均受
   益，估计省 20–40% 调试时间。
2. **rw 链尾 rfl 的实例透明度失败**：v7 亲历目标两显示完全相同 `A = A` 而 rw
   尾 rfl 不闭（隐实例参数路径不同）；解法＝改用 `simp only [局部引理,
   Matrix.add_mul, Matrix.mul_add, add_assoc]` 分布后 `abel` 收尾（v11 定稿）。
3. **ᴴ 记号是 scoped**：`ᴴ`（postfix:1024，ConjTranspose.lean:40）scoped 于
   namespace Matrix——文件头需 `open Matrix`（probe 3 v1 亲历语法错误）；
   `MatrixOrder` scope 是 PSD/CFC 实例的开启键（Analysis/Matrix/Order.lean:34
   注释亲读）。
4. **smul vs mul**：标量乘须 `t • M`（`t * 1` 不可elaborate，probe 3 v1 亲历）；
   trace_smul 出来是 `t • trace`，需 `smul_eq_mul` 归位（v2 亲历）。
5. **sum 级恒等式（elementwise 路线）显著劣于矩阵级路线**：S1 走 ext+sum 合并
   （v1–v3）三版失败；矩阵级 add_mul/mul_add 分布＋abel（v4+）即收敛。B5a
   实现建议：**恒等式优先矩阵层，elementwise 只做前提代入**。

### §2.4 未跑项清单（如实）

以下候选 API 仅 grep 级或未查，本会话**没有**跑使用级探针，后续轮次开工前
建议先探：
- `Matrix.PosSemidef.posDef_iff_isUnit` / `posDef_iff_det_ne_zero` 使用级；
- 二次型夹逼（∀v vᵀ(S−l₃I)v ≥ 0）⇒ `Matrix.PosSemidef` 的桥引理（方向与
  `Matrix.PosSemidef` def 的 dotProduct 口径对接，PosDef.lean:60 定义亲读，
  转换引理未定位）；
- CFC.sqrt 的 `IsSelfAdjoint`/特征值交换性 API（谱夹逼路线的依赖，名字未
  grep——诚实标注完全未查）；
- 对称阵算子范数 = 最大特征值绝对值（Rayleigh 极值特征化）——grep 一轮未
  命中，但搜索词有限，标注『未定位』而非『确认缺位』；
- ‖M·Q‖_F = ‖M‖_F（Q 正交）直接引理——未定位（待查）；
- `Matrix.IsHermitian.eigenvalues_le` 类单调/夹逼 API——grep 未命中（同上
  口径：未定位）。

---

## §3 缺口清单（证路线草案与风险）

### §3.1 矩阵极分解（步骤 5；B5c 主缺口）

**缺口**：Mathlib 无矩阵极分解（§2.1 [D][E][F]＋负向探针 N2 双面证据）。

**证路线草案**（全程已有探针支持的件＋待探件）：
1. W := CFC.sqrt ((I+A)·(I+A)ᵀ)——被开方阵 PSD 由
   `Matrix.posSemidef_conjTranspose_mul_self`（PosDef.lean:384）现成给出；
   CFC.sqrt 在 Matrix ℝ 随 `open scoped MatrixOrder` 可用（探针 1 P5 亲验，
   含 `CFC.sqrt_mul_sqrt_self`：W·W = 被开方阵）。
2. I+A 可逆 ⇒ W 可逆 ⇒ R := W⁻¹·(I+A) 存在；R·Rᵀ = W⁻¹(I+A)(I+A)ᵀW⁻¹ =
   W⁻¹·W²·W⁻¹ = 1（W 对称）——纯代数，前提是 W 对称（CFC.sqrt 保
   IsSelfAdjoint——**待探**，§2.4）与 W² = (I+A)(I+A)ᵀ（现成）。
3. I+A 可逆本身：由谱夹逼奇异值 ≥ √(1−β) > 0（步骤 5-(ii)），或由
   det((I+A)(I+A)ᵀ) = det(I+B) > 0（‖B‖<1 ⇒ 特征值 > 0——仍走夹逼）；
   独立替代：β < 1 ⇒ ‖B‖_F < 1 ⇒ I+B 正定（Gershgorin/谱半径界——
   Mathlib 有 Gershgorin.lean（LinearAlgebra/Matrix/Gershgorin.lean 在场，
   ls 亲见）——可改造候选，未探）。
4. 谱夹逼：I+B 的特征值 ∈ [1−β, 1+β]——由 ‖B‖_F ≤ β 出发需 Rayleigh 商
   极值特征化（vᵀ(I+B)v ∈ [1−β, 1+β]·‖v‖² ⇔ ‖Bv‖ ≤ ‖B‖₂‖v‖ 的算子范数
   面）——**缺位自建大件**；谱定理件在场（探针 1 P4）提供对角化底座。
5. ‖W−I‖₂ ≤ 1−√(1−β) ≤ β：特征值夹逼＋对称阵算子范数=谱极值——同 4 的
   桥。

**风险**：
- R1（高）：谱夹逼＋算子范数桥是两件中件叠加，工程量不确定度最大的单点；
  若走 spectral_theorem 全套（eigenvectorUnitary 酉对角化），矩阵搬运链长。
- R2（中）：CFC.sqrt 的伴随性质（IsSelfAdjoint、与谱相关的 API 面）未探——
  CFC 是新框架，文档面薄，可能出现实例-满足度层面的意外。
- R3（低）：W⁻¹ 存在性与 R 正交性的纯代数收尾（探针 3/4 已验同型操作面）。
- 缓解：β 界只需单向（上界 β 即可推出所需 ‖W−I‖ ≤ β）；可把『特征值 ∈
  区间』弱化陈述为二次型夹逼 ∀v（与 R14 已有的二次型口径 λ 夹逼同式——
  ttp_sandwich 先例），避开特征值函数的可测/排序面。

### §3.2 Hessian 链式法则（B3 附带段；本件只记录缺口不展开）

**缺口**：Mathlib 无 hessian 模块（§2.1 [A][B][C] 三面：全库零 hessian 文件名、
Analysis/ 零内容命中、全库零内容命中；负向探针 N4 `hessian` unknown identifier
亲验）。一阶 fderiv API 在场（探针 1 P8 亲验：`HasFDerivAt`/`HasFDerivAt.fderiv`
（FDeriv/Basic.lean:415）/`HasFDerivAt.comp`/`fderiv_comp`（FDeriv/Comp.lean:179））。

**自建草案**（B3 未来若排）：fderiv² 需以 x ↦ fderiv 𝕜 f x 的可微性为轴
自建复合链式法则——对 f∘g 的二阶导 = f''∘g·(g')² + f'·g'' 的双线性映射形式
化（ContinuousBilinearMap 面），无底座可借用；估 ≥800 行且依赖
ContDiffAt 二阶正则性 API 的现成度（未探——如实标注）。**结论维持 D61 裁决 1：
B3 本轮不排；其 CFC/谱底座与 B5c 共享，待 B5c 落地后再议。**

### §3.3 trace 不等式（步骤 3；B5b 主缺口——已消解为小件）

**缺口**：Mathlib 无 `tr(AB) ≥ 0`（A,B 均 PSD）现成 API（负向探针 N1
`Matrix.PosSemidef.trace_mul_nonneg` unknown 亲验；grep 级
Analysis/Matrix＋LinearAlgebra/Matrix 无 trace-mul-nonneg 类命中）。

**消解证据**（本会话已跑 /tmp/r15c_probe3_trace.log，exit 0，全证明在档
/tmp/r15c_probe3_trace.lean）：路线＝
`CStarAlgebra.nonneg_iff_eq_star_mul_self`（0 ≤ A ⇔ ∃C, A = CᴴC，
Rpow/Basic.lean:380）双开方 → `Matrix.trace_mul_comm` 循环移位 tr(CᴴCB) =
tr((DCᴴ)ᴴ(DCᴴ)) → `Matrix.posSemidef_conjTranspose_mul_self`＋
`Matrix.PosSemidef.trace_nonneg` 收尾；线性推论（A−tI ⪰ 0 ⇒ t·tr B ≤ tr AB）
由 trace_add/trace_smul 拆分 6 行。**风险：低**（探针全证明走通；剩余工作
是把私有定理工程化＋ Frobenius↔trace 恒等式件（§2.2 可改造档））。

---

## §4 工程量分档

锚（实测）：探针 3 全源件 43 行（T1 本体 15 行＋T2 本体 6 行）；探针 4 全源件
28 行（S1 本体 7 行＋S2 本体 2 行，v11 终版）；
R14 常数件 TableB5.lean 354 行（17 定理）/TableB5Data.lean 205 行——同仓
同栈可比锚。分档口径：**≤300 行／300–800 行／≥800 行**（Lean 证明本体行数，
不含 Data 件与门）。

| 步骤 | 分档 | 依据 |
|---|---|---|
| 步骤 1 | **≤300** | 探针 4 S1 本体 7 行亲验；对角恒 0＋η≤√72δ 面各 ~50–100 行（Finset/Simp 标准 API）；§2.3 摩擦 1/2 已有解法记录 |
| 步骤 2 | **≤300** | 探针 4 S2 本体 2 行亲验；P₀ 幂等/对称 ~30 行；可逆性前提桥 ~100 行（posDef_iff_isUnit 现成＋二次型桥待探，§2.4） |
| 步骤 3 | **300–800** | 核心不等式 T1 15 行＋T2 6 行亲验（探针 3）；增量在 Frobenius↔trace 恒等式件（~100–200）＋块分解恒等式矩阵层化（~100，§2.3 摩擦 5 建议）＋PSD 前提构造链（二次型⇒PosSemidef 桥 ~100–300 待探） |
| 步骤 4 | **300–800** | B 恒等式纯环 ~100；范数压缩不等式是档内主件：对称正定逆算子范数界自建（Rayleigh/谱面，§2.4 未定位 API ⇒ 保守估 300–500） |
| 步骤 5 | **≥800** | 三件叠加：极分解构造（CFC.sqrt 路线 ~200–300）＋谱夹逼（≥300，无现成 API 面最大）＋算子范数-特征值桥（≥300）；且 §2.4 三项待探（CFC 自伴/夹逼/正交不变）都在此步——不确定度集中 |
| 步骤 6 | **≤300** | R14 C_valid/delta_max_valid 同式先例（TableB5.lean:234/:288 各 ~50 行）；d_P 陈述形式＋正交不变性待查项是小风险点 |

总口径：B5a（1–2）≈ 500–700 行内可控（探针双面证据）；B5b（3–4）≈ 700–1300
行（核心已消解、两件可改造面待探）；B5c（5–6）≈ 1100 行起且方差最大
（三项待探全集中）。

---

## §5 建议切分与排期

切分（沿任务书给定框架，逐件给出验收面）：

- **B5a＝步骤 1–2（纯代数先行件，纯 ring 面）**：E 分解＋对角恒 0＋投影
  分解＋P₀ 性质＋S 可逆前提桥。验收面＝恒等式定理（探针 4 双例的工程化）
  ＋η ≤ √72·δ。探针证据密度最高（S1/S2 双例亲验走通）。
- **B5b＝步骤 3–4（trace 件）**：tr(AB)≥0 自建定理（探针 3 全证明在档）＋
  线性推论＋Frobenius↔trace 恒等式＋混合块/平行块两不等式。
  验收面＝(σ₃−‖D_∥‖)·‖D_⊥‖ ≤ η 与 ‖B‖_F ≤ β 两定理。
- **B5c＝步骤 5–6（极分解件）**：W/R 构造＋谱夹逼＋算子范数桥＋装配
  d_P ≤ (σ₁³/λ₃²+2/σ₃)·η 终定理。验收面＝终定理（d_P(X,Y) ≤ C·δ，
  C 用 R14 已入 Lean 的常数件）。

排期建议：**B5a → B5b → B5c 串行**（依赖单向：5 用 2 的可逆前提、3/4 的
界；6 用全部；B5a 的陈述面决策（索引类型 Fin 9/Fin 3、Frobenius 范数实例
采用、O(3) 的 ∃Q 见证式陈述）是全链公共底座，必须先行定死）。

**失败时信息量最大的首件选择：B5a**。论证：
1. B5a 的失败模式（纯 ring 面在 instance 路径摩擦下无法低成本收敛）会
   **整链否决** B5 解析本体的可行性——探针 4 的 v1–v10 迭代史（§2.3）亲历
   证明了这类摩擦真实存在且非显然（10 版重写才收敛一个两行恒等式）；若
   工程化放大后仍失控，越早知道越好。信息量/成本比最高。
2. B5a 同时锁定三个全链陈述面决策（范数实例、O(3) 陈述形式、索引类型），
   这些决策直接决定 B5b/B5c 的工程量估计是否成立——不做 B5a，B5c 的
   ≥800 行估计无法收紧。
3. 反方案（B5c 可行性尖刀先行）理由是风险最大件最先测；但 B5c 的探针
   （谱夹逼三件）**不依赖** B5a/B5b 的产出，可随时以独立探针形式插入
   （≈100 行试验件，零入库风险），无需占正式排期位——建议作为 B5a 施工
   期间的并行探针任务而非首件。
4. 若预算只允许一件：B5a（探针密度最高、失败信息量最大、且是公共底座）。

后续轮次衔接备注：本件零 Lean 入库零求解（验收门 numerics/bounds/
r15c_study_gate.py，seed 20261017）；B5a/B5b/B5c 均系后续轮次候选，
依 D61 裁决 1 维持『B3/B4 不排、预算余 0.037 当量全额留储』口径。

---

## 附录：本会话已跑证据索引（全部 /tmp 留档）

| 日志 | 内容 | 结果 |
|---|---|---|
| /tmp/r15c_grep_hessian.log | hessian 缺位 grep 三面（[A] 文件名/[B] Analysis 内容/[C] 全库内容） | 三面全空（缺位证据） |
| /tmp/r15c_grep_polar.log | polar 缺位 grep 四面（[D] 文件名/[E] 两目录内容/[F] 标识符/[H] 全库词面目检） | [D][E][F] 空；[H] 命中均为 polarization identity/polar set/polar coords（另一概念） |
| /tmp/r15c_probe1_api.lean | 正向 API 探针源（18 #check＋4 example） | 编译对象 |
| /tmp/r15c_probe1_api.log | 同上运行日志 | exit_code=0，零 error（1 条 unused-variable warning），40.96s |
| /tmp/r15c_probe2_absent.lean | 缺位名负向探针源（6 名） | 编译对象 |
| /tmp/r15c_probe2_absent.log | 同上运行日志 | exit_code=1（按设计），6 条 unknown 逐名实证 |
| /tmp/r15c_probe3_trace.lean | tr(AB)≥0 双 PSD＋线性推论全证明源 | 编译对象 |
| /tmp/r15c_probe3_trace.log | 同上运行日志 | exit_code=0，零 error 零 warning，17.50s（v2；v1 两处失败为 ᴴ 记号 scoped 与 mul_sub 方向，已修） |
| /tmp/r15c_probe4_algebra.lean | 步骤 1–2 纯代数面两例源（v11 终版） | 编译对象 |
| /tmp/r15c_probe4_algebra.log | 同上运行日志 | exit_code=0，零 error，23.29s（v1–v10 迭代史覆盖式未逐版留档，摩擦点清单见 §2.3） |

（门核验：以上 10 条路径须全部在盘。）
