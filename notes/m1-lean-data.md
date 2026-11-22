# M1 Lean 全链路线留痕（r12a-m1-lean-e2e）

任务：冻结挑战四定理第二件真证明 `thomson_nine_M1`（∀ x ∈ SphereConfig 9,
(189/8:ℝ) ≤ coulombEnergy x）的 Lean 内核真证明落盘。本文档记录两相位实现路线、
三处对任务书预设的技术勘误（探针教训）与全部方向裁决依据。

## 0. 交付件清单

| 件 | 说明 |
|---|---|
| `numerics/bounds/m1_lean_data.py` | 相位 1 数据件（seed 20261014，只读消费冻结件 `results/lp_m1_light.json`） |
| `numerics/bounds/results/m1_lean_data.json` | 全部精确 Fraction 数据（(a)–(d)） |
| `formal/lean/ThomsonN9/M1Data.lean` | 由数据件 `--emit-lean` 生成的 ℚ 常量模块（约 500 行，`import Mathlib`） |
| `formal/lean/ThomsonN9/Solution.lean` | 扩展后解件：M0 前缀逐字节不动＋M1 真证明（thomson_nine_M1） |
| `formal/lean/scripts/CheckAxioms.lean` | 增补 `thomson_nine_M1` 公理打印 |
| `numerics/bounds/r12_m1_gate.py` | 验收门 G1–G8＋NC1–3（seed 20261014） |
| `numerics/bounds/results/r12_m1_ledger.json` | 账本（门锚定的受控字段） |
| 本文 | 路线留痕 |

## 1. 相位 1：数据件（m1_lean_data.py → m1_lean_data.json）

只读输入：`results/lp_m1_light.json`（冻结，git diff HEAD 守卫；sha256 记入
provenance）。参考能量只读 `../thomson-workflow/data/energies.json`
（E* = 25.759986531，十进制口径 Fraction 解析，D28 裁决 3）。

**(a) f 的单项式展开**：`coeffs_legendre_exact`（9 项，degree 8）经独立 Bonnet
递推 `(n+1)P_{n+1} = (2n+1)t·P_n − n·P_{n−1}` 重推导为单项式基；逐项审计
`P_k(1) = 1`；k≥1 支集恰 `{1,2,3,7}`（断言，非零系数全非负）。

**(b) p 的非负证书——【勘误 1，任务书预设不可行】**：任务书预设 p(t) :=
1−f(t)²(2−2t) 的 ℚ 因子分解表（每因子带非负种类标签）。亲证（numpy 求根＋
sympy `factor_list`）：

- p 次数 15（奇）⇒ 至少一个实根；数值根恰一个 **t₀ ≈ −1.423309 ∉ [−1,1]**；
- sympy 在 ℚ 上 `factor_list` 给出**单一不可约因子**（重数 1）⇒ p ℚ-不可约。

因此任务书的因子种类表（平方／正定二次／(1−t)／(1+t)／正常数／不可约二次之
平方之**积**）不可能等于 p：这些因子在 t₀ 处要么严格为正（平方、正定二次、
正常数、(1−t₀)>0、(1+t₀)² 型），要么取负值但配对成平方——均不能在 t₀ 处取 0
而 p(t₀)=0。**设计变更**（记 D-r12a-1）：改用半直线 Lukács SOS——Möbius 变换
`u = (1−t)/(1+t)`（把 [−1,1] 映到 [∞,0]）后
`P(u) := (1+u)^15·p((1−u)/(1+u))` 满足

```
P(u) = Σᵢ d0ᵢ·z0ᵢ(u)² + u·Σᵢ d1ᵢ·z1ᵢ(u)²     （z 为 ℚ 系数多项式，d ∈ ℚ≥0）
```

数值初值来自仓库 venv 的 SDP（cvxpy/CLARABEL，仅取初值）；恒等式经零空间
重参数化（x = x₀ + N·y 保持 16 个系数方程精确成立）＋二进有理舍入后**精确**
成立；psd 经精确 Fraction LDLᵀ 验证（全部主元 > 0）。Lean 侧（M1Data）：
`PuR_cert`（ring 恒等式）＋`PuR_nonneg`（逐项 sq_nonneg×正系数）＋
`moebius_id`（Möbius 恒等式，field_simp）＋`pR_m1_nonneg`（t=−1 端点直接
norm_num）；Solution.lean 的 `pR_nonneg` 组装出 `∀ t ∈ [−1,1], 0 ≤ pR t`。
（探针①的数值结论 p ≥ 8.56e-8 > 0 于 [−1,1] 仍然成立——只是"因子分解"这一
证书形式不可行，非负性本身无恙。）

**(c) 核机制**（逐 k ∈ {1,2,3,7}，dim = 2k+1 = 3/5/7/15）：
- H_k = ker Δ 整数基：单项式×degree 表上精确高斯消元零空间（Fraction），通分
  约整；逐基元 `tri_laplacian == {}` 审计；
- Gram `R = ∫_{S²} h_l h_j / 4π`：公式
  `∫ x^{2p}y^{2q}z^{2r} dσ/4π = 2(2p)!(2q)!(2r)!(n+1)! / (p!q!r!(2n+2)!)`（探针②
  已验证的公式，奇次幂单项式为 0）；
- 精确 `R⁻¹`（逐列高斯消元，`R⁻¹·R == I` 断言）；精确 LDLᵀ（L 单位下三角，
  D 对角全正，`L·D·Lᵀ == R` 重乘断言）；`S = L⁻¹`；
- 球面理想证书：`D_k := (2k+1)P_k(x·y) − Σ(R⁻¹)_lj h_l(x)h_j(y)`（P_k 经同一
  Bonnet 递推的单项式展开，(x·y)^e 六元展开）作字典序 Grobner 归约（首项
  x²→(1−y²−z²) 型重写，归约链构造出 A_k、B_k），范式==0 断言＋
  `(‖x‖²−1)·A + (‖y‖²−1)·B == D_k` 重乘复核＋5 组整数向量二次型抽样＋
  6×6 球面有理点对 36 组再生核复核（k=1,2,3,7 全过）。

**(d) 装配常数**：`ĉ_k` 逐位取自 lp_m1_light；`f(1) = Σĉ_k`（P_k(1)=1）；
`B = (81ĉ₀ − 9f(1))/2` 精确重算 **== lp_m1_light.bound_exact 逐位**（断言）；
`189/8 < B ≤ E*+1e-6`（E* 直读 energies.json 的 energies/9/value 十进制口径）。

provenance：seed 20261014（无随机路径，惯例记档）、code_version = git
describe、lp_m1_light sha256。

## 2. 相位 2：Lean 证明（M1Data.lean ＋ Solution.lean）

`M1Data.lean` 完全由数据件生成（`--emit-lean`），只 `import Mathlib`；所有常量
为 `((n/d : ℚ) : ℝ)` 字面量，全部恒等式由内核可检 tactic 关闭。`Solution.lean`
`import ThomsonN9.M1Data`，M0 前缀逐字节不动（挑战件 26–149 行复述），M1 证明
四步：

1. **逐对**（`pairwise`）：t_ij := ⟨x_i,x_j⟩ 坐标式；`2−2t = ‖x_i−x_j‖²`
   （`EuclideanSpace.real_norm_sq_eq`＋`PiLp.sub_apply`）；t∈[−1,1]（两侧
   `sq_nonneg` 的范数恒等式）；`pR_nonneg`（Möbius 回代＋`div_nonneg`）给出
   `f²·d² ≤ 1` ⇒ `f·d ≤ 1`（`abs_le_of_sq_le_sq'`）⇒ `f ≤ d⁻¹`（`le_div_iff₀`）。
2. **核正性**（`kern_nonneg` 泛型引理 ×4）：per-pair `sphereK{k}S` 在
   `‖x_i‖²=1` 处两修正项消零（`simp only [hz i, hz j, zero_mul, add_zero] at h1`），
   求和后 `double_sum_factor`（纯 Finset 代数：`sum_product`/`sum_comm`/
   `sum_mul_sum`/`mul_sum`）把 `Σ_{i,j} Σ_{l,j'} M h h` 重排为
   `Σ_{l,j'} M·(Σ_i h_l)·(Σ_j h_j')`；`quadK{k}S` 化为平方和×正权，
   `quadK{k}_nonneg` 收口。
3. **三角恒等式**（`sum_Ioi_half`）：对称 g 的 `Σ_{i<j} g = (Σ_{i,j} g − Σ_i g_ii)/2`
   ——行分解 `univ = Ioi i ∪ (Iio i ∪ {i})`（Disjoint 用 `Finset.disjoint_right`
   + omega）＋下三角=上三角（乘积过滤器化＋`Finset.sum_nbij` 以 `Prod.swap`
   为双射）。
4. **装配**：`Σ_{i,j} f(t_ij) = 81c₀ + Σ_k c_k·(ΣΣ P_k)`（`sum_c_mul` 常数外提）；
   ≥ 81c₀（c_k≥0＋核非负）；对角线 `t_ii = 1` ⇒ `Σ_i f(t_ii) = 9·fOneR`；
   `E ≥ (ΣΣf − 9f(1))/2 ≥ (81c₀−9f(1))/2 = BR > 189/8`（`B_assembly`＋
   `B_lower` 精确分数收口）。

公理：`#print axioms ThomsonN9.thomson_nine_M1` 恰
`[propext, Classical.choice, Quot.sound]`。

## 3. 探针勘误与实现教训（诚实录）

1. **p 的 ℚ 因子分解不可行**（见 §1(b)）——任务书预设经亲证推翻，改道
   Lukács SOS；教训：奇次数多项式的"非负类因子积"证书在代数上就被排除了，
   探针①只验了"p≥0 数值成立"，未验"因子化形式存在"，两件事必须分开。
2. **k=7 展开恒等式的 elaboration 病态**：`sphereK7S`/`quadK7S` 直接
   `simp only [Fin.sum_univ_castSucc] → simp only [表] → unfold → push_cast → ring`
   路线在 k=7（225 项＋A/B 修正 352 单项）超 15 分钟 CPU 仍不终止（200k 心跳
   超时；4M 心跳实测 15 min+ 未完）。**修复**：把 M-部分提出为独立 def
   （`Mflat{k}`/`Qflat{k}`，镜像 Finset 展开项集含零项），"求和求值"成为纯
   加法重排（`simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, 表, Mflat]`
   + `abel`——乘积原子不动），多项式环恒等式留给平坦 `sphereK{k}`/`quadK{k}`
   （bal_join 浅树，默认心跳内通过）；`sphereK{k}S := rw [hsumK{k}]; exact
   sphereK{k}`。全模块 elaborate 从"不可完成"降到 **~12–20 s**。
   - 子教训 i：`simp only [Fin.sum_univ_castSucc]` 递归到底会留下 `∑ x : Fin 0`
     残项，必须加 `Fin.sum_univ_zero`；
   - 子教训 ii：`![...]` 矩阵字面量对**非 succ 形**字面索引（`⟨1,⋯⟩`）在
     simp/decide 下不求值（`Matrix.cons_val_succ` 不点火），而 castSucc 链索引
     可求值——表只用于 Finset 求和侧；二次型 RHS 一律内联 ℚ 字面量；
   - 子教训 iii：ℚ 上 `decide` 对非整数 ℚ 字面量（如 `15/4`）卡死
     （`Rat.instDecidableLe` 不归约），非负性改由 `((n/d:ℚ):ℝ)` 字面量的
     `push_cast; norm_num` 直证。
3. **∑ 优先级笔误**：生成器一度产出 `∑ i, A i + B + C`（∑ 只结合第一加数），
   elaborated 目标与数学意图错位（k=1 目标出现 `u0²·9`），修正为平坦展开无
   求和号。
4. **Solution 侧**：`dot` 私有 def 保持 defeq 透明（`set`/`have` 引入的 fvar
   不透明，rw 不可折叠）；`Fin 9` 常数求和的绑定子必须显式注类型
   （`∑ i : Fin 9, ∑ j : Fin 9, c`，否则 Fintype 卡 metavariable）；k=1 的
   A/B 修正多项式恰为字面零（`0*((0:ℚ):ℝ)` 两个同形项），刚性 rw 链
   （zero_mul×2）会过度改写而失败，改 `simp only [hz i, hz j, zero_mul,
   add_zero]`。

## 4. 验收口径

- `bash scripts/check.sh` 全链 PASS：挑战件恰 4 sorry（声明行 158/166/172/179、
  sorry 行 160/168/175/183）＋解件 0＋M1Data 0；CheckAxioms 两定理恰三标准公理；
  语句比对 OK（M1 重声明在场且逐字比对无失配，compared 34＝M0 期 33＋M1；
  "skipped (not attempted)" 打印名单系 compare_statements.py 硬编码
  presence-only 豁免集〔含 M1 名字〕，非实际未比对名单——按实现报准，D49
  口径）；token 扫描 0 命中（Solution＋M1Data）。
- `python3 numerics/bounds/r12_m1_gate.py`：G1 冻结守卫（四冻结件＋references
  树哈希＋lp_m1_light.json/lp.json git diff HEAD 全空）＋G2 token（Solution＋
  M1Data）＋G3 强制重 elaborate build（4/0/0 sorry）＋G4 公理＋G5 语句保真＋
  G6 NC1/NC2/NC3＋G7 stdlib-only 数据独立复核＋G8 账本锚；heavySolves = 0
  （Lean 构建＋精确线性代数，非重求解口径）。

## 5. 未做／开放项（如实）

- `thomson_nine`、`thomson_nine_unique` 维持未证（挑战件 sorry 不动）；
- p 的 SOS 证书的 SDP 初值步骤依赖仓库 venv（cvxpy）；其正确性不依赖该步
  （恒等式与 psd 均为生成器内精确 Fraction 断言＋门 G7 stdlib-only 复核），
  但**复现** json 需 venv（`numerics/.venv/bin/python3`）。
