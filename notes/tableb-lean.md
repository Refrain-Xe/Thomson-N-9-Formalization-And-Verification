# tableb-lean.md — 表 B（Procrustes 刚性层）Lean 化工作笔记

> 本文件为 R14 起新建的 append-only 笔记（表 B 首件 B5 起账）；沿
> notes/tablea-lean.md 同式体例。只追加不改写；勘误以追加节+内联注记落账。

## §1 R14A B5 Procrustes 常数件（r14a-b5-procrustes-lean，2026-10-11）

**任务**：表 B 首件——B5 常数认证层 Lean 化（D56 裁决 1/2/3；
heavySolves=0，零求解零 SDP 零新数值证书；l4.json 常数已是精确 Fraction，
无 dyadic 舍入面，provenance 记源文件 sha256）。

**产出八件**（自有件清单＝门 G1 OWNED 集）：

| 件 | 角色 |
|---|---|
| `numerics/bounds/r14_b5_data.py` | 发射器：stdlib Fraction 只读消费 l4.json＋local_min.json，独立第二实现（Newton sqrt 包＋ℚ[ρ,√3] 符号引擎）重导、发射、回读自检 |
| `formal/lean/ThomsonN9/TableB5Data.lean` | 生成数据件：24 def（23 ℚ 字面量＋diagQ）＋33 定理（装配四件 636-bit norm_num／λ 支配前提／sqrt 前提／S 端点事实／6 抽查定理），仅 import Mathlib |
| `formal/lean/ThomsonN9/TableB5.lean` | 手写主件：17 定理（二次型对角化恒等式〔显式 ring 证书〕＋Gram 对角/非对角＋λ 夹逼两向＋S 容器＋sqrt 界四件＋C 有效性＋δ_max 有效性），import Mathlib＋ThomsonN9.TableB5Data，零数值字面量 |
| `numerics/bounds/r14_b5_gate.py` | 验收门 G0–G5＋NC1/NC2/NC3（seed 20261016；门内独立第二实现） |
| `thomson-n9/numerics/bounds/r14_b5_gate.py` | CWD 兼容包装器（runpy 重定向，R10A/R12B/R13C 先例） |
| `numerics/bounds/results/r14_b5_data.json` | 数据档：常数/检查面/抽查点/输入 sha256 provenance |
| `numerics/bounds/results/r14_b5_ledger.json` | 账本：seed/heavy_solves=0/文件 sha256/公理并集/门全步 |
| `notes/tableb-lean.md` | 本笔记（新件 append-only） |

**数学内容三层**（与 l4_procrustes.py 对账但不 import——独立第二实现）：

1. *二次型对角化＋λ 夹逼*：9 行 TTP 构型（上/下三角 (ρ,0,±z),(−ρ/2,±√3ρ/2,±z)
   ×2 符号＋3 帽行）满足 `vᵀXᵀXv == (3(1−z²)+3/2)(v₀²+v₁²)+6z²v₂²`——
   Lean 侧 `ttp_quadform` 以显式 ring 证书
   `diff == (√3·√3−3)(ρ²v₁²+v₁²/2)+(ρ²+z²−1)·3(v₀²+v₁²)` 证（nlinarith
   直攻失败留档 D56-2；R14 会话探针亲跑通过）；⇒ z 盒内（local_min
   zStarIntervalMpmath 严格区间、与 l4.json z_box 逐位同源）二次型夹逼
   `l₃‖v‖² ≤ q ≤ u₁‖v‖²`（`ttp_sandwich_lo/hi`，系数证书
   c1: `a−l₃ = 3(1/2−z_hi²)+3(z_hi²−z²)+(3−l₃)` 等）。对角路线支配记录界：
   6z_lo²≥l₃、9/2−3z_lo²≤u₁、z_hi²<1/2 全部 Data 件 norm_num 精确验证。
   外加 S 区间容器定理（`S_interval_container`）：对角真值端点∈l4.json
   S_interval 记录区间（S22 端点==6z² 逐位、S00/S11 为 ρ 外扩**严格**容器）、
   非对角真值 0∈对称区间。
2. *装配恒等式四件*（Data 件 ℚ norm_num，字面量与 l4.json 逐位对账）：
   `C_inner==u₁·s1_up/l₃²+2/s3_dn`、`C==sqrt72_up·C_inner`、
   `C_chord==2C`、`δ_max==(s3_dn/(2·s1_up))·l₃²/(sqrt72_up·u₁)`
   （min 支路取 s3_dn/(2·s1_up)：reg2<1/2 独立验证；636-bit 大分数
   norm_num 全过——D56 探针②量级风险已消解）。
3. *有效性定理*：sqrt 有理界四件（`sqrt_u1_le_s1Up`/`s3Dn_le_sqrt_l3`/
   `sqrt72_le_sqrt72Up`/`sqrt_l3_le_s1Up`，走 Real.sqrt_le_iff 与
   sq_le_sq 型证书；D56-3 留档的 div_le_div_of_nonneg 缺席面以
   div_le_div_iff₀＋乘开形绕行）＋`C_valid`（0<l₃≤λ₃≤λ₁≤u₁ ⇒
   √72·((√λ₁)³/λ₃²+2/√λ₃) ≤ C）＋`delta_max_valid`（0≤η、η≤√72δ、
   δ≤δ_max ⇒ β:=λ₁η/λ₃²≤min(1/2,√λ₃/(2√λ₁))——β 上界链经 ℚ 恒等式
   sqrt72Up·deltaMax·u₁·(2·s1Up)==s3Dn·l₃² 的 ℝ cast）。

**诚实边界**（docstring 双侧声明）：d_P(X,Y)≤C·δ 解析本体（l4_procrustes.py
步骤 1–6：投影分解/极分解/旋转规范）不在本件；区间 Sylvester 法 soundness
（顶点多线性）＝stretch 非必需面，未成不阻断过门。

**抽查方案**（seed 20261016，A5/A6 家法）：3 个 z∈盒随机有理点（k=0,1,2
依次 i=rng.randint(⌊z_lo·2⁴⁰⌋,⌈z_hi·2⁴⁰⌉)、z=i/2⁴⁰）×v 三分量（/64 网格）；
期望值 diagQ（对角公式）与符号行展开（ℚ[ρ,√3] 引擎）双实现一致；门内
第二实现独立复算对账（Data 6 抽查定理：diagQ_spot0–2＋
diagQ_sandwich_spot0–2）。

**定理账**：Data 33＋Main 17＝50 件全定理公理恰 ⊆{propext,
Classical.choice,Quot.sound}（G3 亲验）；主件四 sqrt 界＝D56 设想的
『四件』口径（第④件取 √l₃≤s1Up 链、附 s3Dn≤s1Up 推论）。

**开发实录**（真实缺陷捕获）：①发射器符号引擎两处 bug——ttp_rows 未把 z
作参数（z 坐标硬编码 ±1，S 对角全错）与 Gram 检查误用 `list(got)!=[(0,0)]`
（dict 恒 4 键，误报非平凡 ρ/s 项），均为发射器自检首跑捕获后修复；
②主件 h2s1up 的 `show … by` 内联语法错误由 G2 首跑 elaboration 捕获，
改独立 have；③证书 c1 首版符号错（−3(1/2−z_hi²)），Lean ring 正确拒绝，
修正为 3(1/2−z_hi²)+3(z_hi²−z²)+(3−l₃)。三处均为门/编译器把关实证。

**G2 墙钟**（本轮实测，独占）：Data 45.4s＋Main 41.9s（远低于 600s 界）。

## §2 R15A B6 拼接端点/记录锚件（r15a-tableb-b6，2026-10-11）

**任务**：表 B 第二件——B6 拼接端点/记录锚件算术层 Lean 化（D61 裁决 2；
heavySolves=0，零求解零 SDP 零新数值证书；endgame.json 分区常数已是精确
Fraction 无 dyadic 舍入面，provenance 记 sha256==86863a09…69f 不变锚，
发射器与门双锚定）。

**产出八件**（自有件清单＝门 G1 OWNED 集）：

| 件 | 角色 |
|---|---|
| `numerics/bounds/r15_b6_data.py` | 发射器：stdlib Fraction 只读消费 endgame.json（partition/E*/AR/citedCertificates），独立第二实现重导、发射、回读自检＋确定性重跑字节一致 |
| `formal/lean/ThomsonN9/TableB6Data.lean` | 生成数据件：28 ℚ def（13 端点＋12 bound＋E*/AR/epsIron）＋45 定理（链 12 对/记录下侧 12 件/HP 字面等/铁律两版/分片语义 12 件/3 抽查），仅 import Mathlib |
| `formal/lean/ThomsonN9/TableB6.lean` | 手写主件：8 定理（覆盖 ℚ/ℝ 双版〔Nat.find 真证明〕＋链聚合＋记录口径①＋取到＋铁律 ε 版＋分片语义聚合），import Mathlib＋ThomsonN9.TableB6Data，零数据值字面量（剥注释零 ℚ 分数/小数；结构指标 10/11/12/13 不在此列） |
| `numerics/bounds/r15_b6_gate.py` | 验收门 G0–G5＋NC1/NC2/NC3（seed 20261017；门内独立第二实现＋endgame.json/certificates 只读守卫＋PARALLEL_FAMILY r15 放行层） |
| `thomson-n9/numerics/bounds/r15_b6_gate.py` | CWD 兼容包装器（runpy 重定向，R10A/R12B/R13C/R14A 先例） |
| `numerics/bounds/results/r15_b6_data.json` | 数据档：分区/记录/分片语义/抽查点/输入 sha256 provenance |
| `numerics/bounds/results/r15_b6_ledger.json` | 账本：seed/heavy_solves=0/文件 sha256/公理并集/门全步 |
| `notes/tableb-lean.md` | 本笔记（append-only 追加节） |

**数学内容四件**（与 endgame.json 记录对账但不 import 生成链——独立第二
实现；本会话 Fraction 亲验 12/12 分片 bound==citedCertificates
claimed_bound 值一双射、AR==min 且 HP 片字面取到、铁律 margin
0.0005405579025207914>0、10 排除片>E*＋2 片≤E*+1e-6）：

1. *12 分区无缝覆盖*：13 端点 −1=e0≤e1≤…≤e12=1 链单调（Data 件 12 对
   `show` 展开＋norm_num1——勿用 decide 于 ℚ 比较，v1 教训 D61-2；勿用
   裸 norm_num〔不展开 def〕）＋主件 `partition_cover_q`（ℚ）/
   `partition_cover`（ℝ）真证明：取 `j = min{j : x ≤ e_j}`（`Nat.find`，
   谓词可判定），j>0 时极小性给 `e_{j-1} < x ≤ e_j`，j=0 时 x=e0 由首段
   链收口——全程不经 ℚ 大比较内核归约。设计探针①（v4）已编译过
   （/tmp/r15_probe_final_b6.log）；本轮执行探针修正 `rw [hxeq]` 为
   `subst hxeq`（hpred 依赖 x 致 motive 不类型正确）后全过。
2. *记录装配*：AR==min(12 分区 bound)——Data 件 12 大分数（最大 171 字符
   ≈570-bit）逐件 AR≤bᵢ norm_num1＋HP 片（指标 10，[−153/200,−187/250]）
   b₁₀==AR 字面等；min 陈述取**口径①** `record_is_min : ∀ i:Fin 12,
   aR ≤ bnds i ∧ bnds 10 = aR`（零 API 风险；口径② Finset.min' 探针 5 迭代
   卡 LinearOrder 元变量，elaboration 残余细目录 D61-2）＋存在口径
   `record_min_attained`。
3. *铁律*：`iron_rule : aR ≤ estar`（E*=25759986531/10^9 ℚ 字面量；比铁律
   AR≤E*+1e-6 更强且真）＋严格版 `margin_pos`＋主件 ε 版 `iron_rule_eps`
   （linarith〔iron_rule, epsIron_pos〕）。
4. *分片语义算术层*：10 排除片（coverPiece==exclusion，指标 0–9）
   `estar < bᵢ`＋2 片 TTP-covering（HP 片＋cap 片 [−187/250,1]，指标
   10/11）`bᵢ ≤ estar + epsIron` 逐片铁律（Data 件 excl0..9_gt／
   cover10/11_le_iron）＋主件析取聚合 `piece_semantics`。

**诚实边界**（docstring 双侧声明）：『区域 i 上 E≥b_i』的证书语义＝数值层
职责（typed_ladder/hermite/hp 各证书 verifyCmd——endgame.json
citedCertificates 所列）不在本件；本件只证算术层（覆盖/min/铁律/分片语义）。

**抽查方案**（seed 20261017，B5 家法）：3 个随机有理点 x∈[−1,1]（2⁻²⁰
网格，k=0,1,2 依次 i=rng.randint(−2²⁰,2²⁰)、x=i/2²⁰），最小命中指数法
（j=min{j: x≤e_j}、片 i=j−1〔j=0 时 i=0〕——与主件 Nat.find 覆盖机器同
规则）定位所在片；本轮落点片 #11、#6、#11；门内独立第二实现 seed 复放
逐位对账（定理 cover_spot0..2）。

**定理账**：Data 45＋Main 8＝53 件全定理公理恰 ⊆{propext,
Classical.choice,Quot.sound}（G3 亲验）；G2 墙钟 Data 13.8s＋Main 31.3s
（本轮首编译实测，远低于 600s 界）。

**开发实录**（真实缺陷捕获）：①发射器 doc= dict 一处括号重复闭合
（IndentationError）＋抽查回读正则 `$` 行尾锚漏 ` := by` 后缀——发射器
自跑两轮捕获后修复；②主件 ℝ 版覆盖 j=0 支路 `rw [hxeq]` 因 hpred 依赖 x
motive 不类型正确，改 `subst hxeq`（执行探针捕获）；③首版 `push_cast at
hchain` 无操作警告（linter.unusedTactic）删除——G2 编译面保持零输出。
三处均为编译器/自检把关实证。

**§2 补记（门开发实录，提交前落账）**：除上述三处外，门侧自跑另拦四处
真实缺陷——⑤G5 首版 chain_json 逐区双 append 成 24 端点（应无缝 13）；
⑥NC1 首版行内追加 sorry 残留 show 致『No goals』伪错（B6 全 norm_num1
定理为多行 show 形状，改单行 rfl 锚 e0_val 整体替换）；⑦NC2/NC3 预期
检出消息『对账失守』与真实失守字面撞车致误 re-raise（改『对账失配』用词
＋flag 变量式捕获）；⑧PARALLEL_FAMILY 首版漏 r15b 的 formal/lean
TableB1* 面——路由二跑亲见 r15b 在途 TableB1.lean 被字面拦后补齐
（家族层实战校准，D61 R15A/R15B 文件集零交叠的枚举执行面）。全程
八处均为编译器/自检/门把关实证；终版门五跑（selfrun2/3＋路由 A/B/C）
全 PASS exit 0（133.5/155.9/167.5/112.8/185.6s）。

## §3 R15B B1 l4_orbit (P5) 实现证书＋轨道配平算术层（r15b-tableb-b1，2026-10-11）

**任务**：表 B 第三件——B1 算术层 Lean 化（D61 裁决 3；heavySolves=0，零求解
零 SDP 零新数值证书；只读消费 local_min.json＋l4_orbit.json，重导对账不
import 源脚本——独立第二实现）。

**产出八件**（自有件清单＝门 G1 OWNED 集）：

| 件 | 角色 |
|---|---|
| `numerics/bounds/r15_b1_data.py` | 发射器：ℚ[z,ρ,√3] 自由代数符号引擎（dict {(zdeg,rdeg,sdeg): Fraction}）——重导九行/36 条目几何分类/逐条 ring 证书乘子精确生成/容器计算，发射双 Lean 件＋回读自检＋确定性重跑字节一致 |
| `formal/lean/ThomsonN9/TableB1Data.lean` | 生成数据件：25 ℚ def（z 盒 2＋ρ 包 2＋12 ν 容器端点＋抽查 9）＋行原子 def（rhoR/s3R/dot3＋9 行＋6 ν 曲线）＋32 定理（端点事实/五链不交/ρ 包前提/抽查容器 3），仅 import Mathlib |
| `formal/lean/ThomsonN9/TableB1.lean` | 生成主件（r13_a1 emit_main_lean 先例）：56 定理，import Mathlib＋ThomsonN9.TableB1Data，零数值数据字面量（G4 机器化：零 ℚ def＋零 ≥15 位数字面量） |
| `numerics/bounds/r15_b1_gate.py` | 验收门 G0–G5＋NC1/NC2/NC3（seed 20261017；门内独立第二实现：行参数化取 l4_orbit.family_points_s3 ×2 整数表、符号元 {(rdeg,sdeg): z 系数表} 异构编码） |
| `thomson-n9/numerics/bounds/r15_b1_gate.py` | CWD 兼容包装器（runpy 重定向，R10A/R13C/R14A 先例） |
| `numerics/bounds/results/r15_b1_data.json` | 数据档：证书乘子全录/分类表/配平/容器/抽查点/输入 sha256 provenance |
| `numerics/bounds/results/r15_b1_ledger.json` | 账本：seed/heavy_solves=0/文件 sha256/公理并集/门全步 |
| `notes/tableb-lean.md` | 本笔记 §3（append-only；§2 为 R15A B6 件 0cba187 已落） |

**数学内容三层**（与 l4_orbit.py / family.py 对账但不 import）：

1. *45 逐对 Gram 恒等式*（(P5) 实现证书）：9 行 TTP 构型（上/下三角
   (ρ,0,±z),(−ρ/2,±√3ρ/2,±z)＋帽 (1/2,±√3/2,0)/(−1,0,0)，行序同
   family_points_s3）的 36 条无序对内积==六类节点曲线
   ν₁=−(1+z²)/2〔错位 6〕/ν₂=−ρ〔帽棱≡1 6〕/ν₃=−1/2〔帽帽 3〕/
   ν₄=1−2z²〔竖棱 3〕/ν₅=(3z²−1)/2〔三角内部 6〕/ν₆=ρ/2〔帽棱≡0,2 12〕
   ＋9 对角归一==1。证明＝B5 ttp_quadform 模曲线证书同式：key 内
   `dot−ν == M1·(s3R·s3R−3)＋M2·(rhoR z·rhoR z＋z²−1)`，两乘子 M1/M2 ∈
   ℚ[z,ρ,√3] 由发射器确定性归约**精确生成**（s 次数≥2 先消；D'==0 即恒等
   式成立），`unfold+ring` 消 key、`Real.mul_self_sqrt` 消零、`ring_nf＋
   linarith` 收口。乘子实测极小集：M2 ∈ {0, ±1/2, 1}、M1 ∈ {0, ±1/4,
   ±ρ/4, ±ρ²/4}（T1·T2 需 M1=−ρ²/4——探针⑤亲验手写 M1=0 被 ring 正确
   拒绝，D61-3『勿手写证书』的第三实证）。
2. *分类桥＋轨道配平*：算术分类函数 `nodeOfN`（同块→三角内部(4)/帽帽(2)；
   帽-棱 (cap−prism)%3≡1→ν₂(1)、≡0,2→ν₆(5)；异侧三角 同余→竖棱(3)、
   不同余→错位(0)——**定向勘误留档**：设计探针④手写 (prism−cap)≡1 反向，
   Σ_y decide 亲捕）＋桥接定理 `gram_nodeOfN`（interval_cases **只生成合法
   l 臂**——k<l 界假设被 interval_cases 直接消费，无 omega 兜底臂；36 臂各
   调该对专属 Gram 定理）＋计数 `edge_counts`（Fin 9×Fin 9 Finset.filter
   decide，6/6/3/3/6/12）＋`edge_total`==36＋轮廓 `prism_profile`/
   `cap_profile`（(2,1,0,1,2,2)/(0,2,2,0,0,4)）＋`sigma_y_balance`
   （Σ_v profile_v(c)==2·mult(c) 双计数恒等，∑ v ∈ univ decide）——
   全部与 l4_orbit.json orbitBalance 逐字段对账（含 D12 勘误口径）。
3. *节点分离容器*：z 盒＝local_min zStarIntervalMpmath 精确有理端点（与
   l4.json z_box 逐位同源——B5 已锚；l4_orbit.json zBox 为严格外扩 dyadic
   盒，发射器/门三方断言 orb_lo<zLo<zHi<orb_hi）。ν₁/ν₄/ν₅ 容器端点＝z²
   包端点精确有理式；ν₂/ν₆＝ρ Newton 200-bit 包（rhoDn²≤1−z_hi²≤ρ(z)²≤
   1−z_lo²≤rhoUp²）；ν₃ 点容器。主件 `nu_containers`（12 合取；ρ 上界走
   Real.sqrt_le_sqrt＋字面 sqrt_le_iff、下界走 B5 s3Dn 同式 sq 型
   nlinarith）＋五链不交（Data norm_num）⇒`node_chain`（ν₁<…<ν₆）⇒
   `node_values_distinct`（15 对两两分离，interval_cases 30 臂＋simp only
   [nuOfN]）。json 记录节点区间为 20 位显示舍入——精确对账取『真值范围⊆
   外扩(1e-15) json 区间』（Fraction 精确；原始容器-显示端点差 1e-17 量级
   舍入尘如实记 advisory）。

**抽查方案**（seed 20261017，B5 家法）：3 个 z∈盒随机有理点
（i=rng.randint(⌊z_lo·2⁴⁰⌋,⌈z_hi·2⁴⁰⌉)、z=i/2⁴⁰）；逐点六 ν 容器包含性
（ν₂/ν₆ 走逐点 Newton ρ 包＋包间序 u1/u2 字面链）；Lean 定理
spot0–2_containers 与发射器 Fraction 重算对账，门 G5 seed 复放复核。

**定理账**：Data 32＋Main 56＝88 件全定理公理恰 ⊆{propext,
Classical.choice,Quot.sound} 零 sorryAx（G3 亲验）；45 证书定理乘子
门内独立归约再生成逐字节对账（G5(c)）。

**开发实录**（真实缺陷捕获，均编译器/自检/门把关）：①发射器 ν₃ 点容器被
自检『退化』误拦（点容器为设计，检查放宽）；②json 节点区间精确包含检查
方向错（容器有理包外伸 1e-60 vs 显示舍入 1e-17——改真值范围⊆外扩 json
口径）；③Data `refine ⟨_,_⟩` term 模式占位符误用（应 `?_`——未知结构
synthesis 报错亲捕）；④`nu_chain_disjoint` 漏 `by`；⑤对角定理 unfold 列
行名重复（rowT0 出现两次被拒）；⑥主件 `hnn` 缺 zHi<1 前提（nlinarith 正确
拒绝）；⑦门 G4 行锚与发射器括号文法不一致（正例文法规范化）；⑧门解析
regex 漏 dot3 前缀＋门内 ν₁ 曲线漏 /2（G5 自检首跑捕获）。

**G2 墙钟**（本会话实测，与 R15A 并行争用）：Data 10.5–65.9s＋Main
24.1–53.6s（≤600s 界的 1/10 量级）；全门 120.6–202.9s。

**§3 补记（G1 家族层执行校准，2026-10-11）**：提交 4dc34e0 后净树验收 PASS
（165.9s），随后 R15D 收口会话开工——其 campaign-10 扩展面 endgame_gate.py
与 decisions.md D64 追加面在途时，零环境变量验收命令被 G1 字面拦（R15A
09b50c2 对其门同式先例：endgame_gate.py 收编＋两件回填）。本门家族层对称
补齐两面（gate.py PARALLEL_FAMILY 增 endgame_gate.py＋decisions.md 两行，
r15 枚举 pattern 收敛为 R15A 同款泛式；G2–G5 不读该两件，放行零削弱；自有
八件仍严格 OWNED）后零环境变量复跑 PASS exit 0（198.1s，时点在途：
endgame_gate.py/r15d_closure_gate.py 双件/decisions.md D64）。字面净树复跑
窗口由 R15D 收口后接管（D61-5 串行口径）。

## §4 R16A B5a 开工前置三探针（r16a-tableb-b5a，2026-10-11）

**任务**：表 B 第四件——B5 解析本体首件 B5a（步骤 1–2 纯代数层 Lean 化，
D67 分叉裁决：开工前先探 §2.4 六项未跑 API 中 B5a 相关三项①②⑤；
③④⑥归 R16B 并行探针）。本节为三项使用级探针的转录落账（探针＝
`lake env lean` 编译验证，Mathlib @ d13f23b7 toolchain v4.34.1，与 R15C
预研同栈同口径）。heavySolves=0。

### 探针① posDef_iff_isUnit／posDef_iff_det_ne_zero 使用级——【档位：现成】

- **源**：/tmp/r16a_probe1_posdef.lean（4 example：P1a 正向/P1b 反向/P1c det 版
  /P1d 实对称⇒IsHermitian）；**日志**：/tmp/r16a_probe1_posdef.log，
  **exit 0** 零 error（25.0s）。
- **结论**：`Matrix.PosSemidef.posDef_iff_isUnit`（Analysis/Matrix/Order.lean:180，
  签名 `hx : x.PosSemidef → x.PosDef ↔ IsUnit x`）与 `posDef_iff_det_ne_zero`
  （Order.lean:199）使用级走通——预研 §2.2『可改造』档的 grep 级在场升级为
  使用级亲验。**实对阵的 IsHermitian 口径附产**：`Sᵀ = S ⇒ S.IsHermitian`
  经 `Matrix.conjTranspose_eq_transpose_of_trivial`（LinearAlgebra/Matrix/
  ConjTranspose.lean:357，ℝ 上 ᴴ = ᵀ）三行闭——注意**预研草案里的
  `Matrix.conjTranspose_eq_transpose` 名不存在**（首跑 unknown 亲捕后修正，
  实名为 `_of_trivial` 后缀）。

### 探针② 二次型夹逼 ⇒ PosDef ⇒ IsUnit 桥——【档位：现成（预研『未定位』消解）】

- **源**：/tmp/r16a_probe2_bridge.lean（3 example：P2a `v ⬝ᵥ v > 0 ⟺ v ≠ 0`／
  P2b 夹逼⇒IsUnit 全链／P2c 弱侧⇒PosSemidef）；**日志**：
  /tmp/r16a_probe2_bridge.log，**exit 0** 零 error（32.6s；首跑一处
  namespace 修正：`of_dotProduct_mulVec_nonneg` 在 `Matrix.PosSemidef`
  命名空间下，裸 `Matrix.` 前缀 unknown 亲捕）。
- **结论**：预研 §2.4 第 2 项标注的『转换引理未定位』**消解**——dotProduct
  口径对接引理族在场且使用级走通：
  - `Matrix.posDef_iff_dotProduct_mulVec`（PosDef.lean:454：
    `M.PosDef ↔ M.IsHermitian ∧ ∀ x ≠ 0, 0 < star x ⬝ᵥ (M *ᵥ x)`）；
  - `Matrix.PosDef.of_dotProduct_mulVec_pos`（:469，构造子）＋
    `Matrix.PosDef.isUnit`（Order.lean:181 证明面自用）；
  - `Matrix.posSemidef_iff_dotProduct_mulVec`（:298）＋
    `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`（:309，B5b 备用）；
  - `Matrix.dotProduct_star_self_pos_iff`（LinearAlgebra/Matrix/
    DotProduct.lean:164：`0 < star v ⬝ᵥ v ↔ v ≠ 0`）。
  B5a 步骤 2-(vi) 的前提桥＝P2b 全链照搬（l₃>0＋∀v l₃·(v⬝ᵥv) ≤ v⬝ᵥ(S*ᵥv)
  ⇒ `IsUnit S`），ℝ 面经 `star_trivial` 归位（§2.3 摩擦 5 的 elementwise
  只做前提代入口径）。

### 探针⑤ ‖M·Q‖_F = ‖M‖_F（Q 正交）直接引理——【档位：缺位（直接引理未定位）】

- **源**：/tmp/r16a_probe5_orth.lean（P5a 六候选名 #check 负向探查＋P5b
  正对照：`Qᵀ*Q = 1 ⇒ ∑ k, (Q k j)^2 = 1` 矩阵级三行）；
  **日志**：/tmp/r16a_probe5_orth.log，exit 1 **按设计**（6 条
  unknownIdentifier 逐名实证：`Matrix.frobenius_norm_mul_orthogonal`／
  `frobenius_norm_orthogonal`／`norm_mul_orthogonal`／
  `orthogonalGroup.norm_mul`／`IsOrthogonal.norm_mul`／
  `frobenius_norm_mul_mem_orthogonalGroup` 全不在场）；正对照 P5b 零其余
  error（pow_two＋simp 收口）。**grep 级补证**：/tmp/r16a_probe5_grep.log
  （[I] 含 frobenius 字样的全部 Mathlib 文件清单＋[J] 其中含 orthogonal 的
  行——[J] 空）。
- **结论**：正交 Frobenius 不变性的**直接引理未定位**（与 R15C 预研
  『待查』一致，本轮升级为六名负向探查＋双面 grep）；且**结构面注记**：
  Matrix 的 Frobenius 范数实例系 local instance（`frobeniusNormedAddCommGroup`
  Normed.lean:518–522 `@[instance_reducible, local instance]` 不全局注册），
  `‖·‖` 在 Matrix 上无全局实例路径——B5a 由此采用**自有 def 口径**
  `frob M := Real.sqrt (∑ i, ∑ j, (M i j)^2)`（陈述面决策，见 §4 末）。
  绕行路线（B5c 用）：frob def＋逐列单位性（P5b 正对照基石）＋Cauchy–Schwarz
  自建，或 `‖M‖²_F = ∑ 列范数²` 路线；非 B5a 依赖面（B5a 只有左乘 X 与
  P₀ 面恒等式，零正交右乘）。

**附**：施工选名核对探针两件（不计入三探针判定）：/tmp/r16a_probe6_names.lean
（+ .log：38 名 #check，缺位 3＝`Fin.sum_univ_nine`〔Fin 9 显式求和改走
`Fin.sum_univ_eq_sum_range`＋`Finset.sum_range_succ` 链〕、`Matrix.dotProduct`
〔实为根命名空间 `dotProduct`，Mul.lean:72〕、`Matrix.inv_transpose`〔实名
`Matrix.transpose_nonsing_inv`，NonsingularInverse.lean:202〕）＋
/tmp/r16a_probe7_names2.lean（+ .log：12 名全在——含 `IsUnit.mul_inv_cancel`/
`inv_mul_cancel`〔DivisionMonoid 面，proj_orth/P0 两向消去用〕、
`Finset.sum_erase`〔f_a = 0 形，对角零消去直用〕、`Real.sqrt_mul`/`sqrt_sq`）
＋/tmp/r16a_probe8_fin9.lean（+ .log：战术 A `∑ i : Fin 9, g ↑i` 经
sum_range 展开亲验走通——ttpX 行函数按 ℕ 索引设计的依据）。

**B5a 全链陈述面三决策（本节定死，B5b/B5c 公共底座；模块 docstring 同文）**：

1. **索引类型**：行 `Fin 9`／列 `Fin 3`（TTP 九行构型显式矩阵 ttpX；
   通用引理〔E_decomp/E_diag_zero/sandwich_isUnit 等〕保持 {m n} 泛型，
   TTP 实例化层落 Fin 9/Fin 3）。
2. **Frobenius 范数口径**：自有 def `frob M := Real.sqrt (∑ i j, (M i j)^2)`
   （不走 local instance 的 ‖·‖ 路径——探针⑤结构面注记；数值上与
   `Matrix.frobenius_norm_def`〔Normed.lean:561〕一致，B5b/B5c 需要时经
   该引理对接）。
3. **行单位/Gram 差形式**：行单位＝`∀ i, X i ⬝ᵥ X i = 1`（dotProduct 口径）；
   Gram 差＝字面 `Y * Yᵀ - X * Xᵀ`（E 作为表达式出现在定理陈述中，不另设
   def——B5b 的块分解面可直接 rw 消入）；O(3) 面预留 ∃Q 见证式
   （`∃ Q, Q * Qᵀ = 1 ∧ …`，B5c 装配层用，本件不出现）。

## §5 R17A B5b 开工前置探针（r17a-tableb-b5b，2026-10-12）

**任务**：表 B 第五件——B5b trace 件（B5 解析本体步骤 3–4 trace/范数压缩层
Lean 化，D72 分叉裁决：开工前先探三面）。本节为使用级探针的转录落账（探针＝
`lake env lean` 编译验证，Mathlib @ d13f23b7 toolchain v4.34.1，与 R15C/R16A/
R16B/R17B 同栈同口径；本节全部日志＝R17A 会话末轮统一重跑在档，各 exit 亲捕）。
heavySolves=0。

### 探针① Frobenius↔trace 恒等式使用级——【档位：现成（自有 frob def 下 15 行闭）】

- **源**：/tmp/r17a_probe1_frobtrace.lean（`frob_sq_eq_trace_aux` 全证明：
  对角逐行 `(M*Mᵀ) i i = ∑ j, (M i j)^2`〔mul_apply＋transpose_apply＋
  dotProduct 展开〕＋行和搬运＋`Real.sq_sqrt` 收口；附五名 #check：
  `trace_mul_comm`/`trace_transpose`/`trace_add`/`Matrix.mul_apply`/
  `frobenius_norm_def`〔Normed.lean:561〕）；**日志**：
  /tmp/r17a_probe1_frobtrace.log，**exit 0** 零 error 零 sorry（35s）。
- **结论**：D72-① 消解——自有 `frob` def（D68-2）下
  `(frob M)^2 = (M*Mᵀ).trace` 是**纯 entrywise sum 搬运**，零 Mathlib norm
  instance 介入（frobenius_norm_def 仅作对接锚，本件实际未用）；主件
  `frob_sq_eq_trace`/`frob_sq_eq_trace'` 照此落地。
- **附**（R16B §7.3 一探两用面向）：`frob_sq_mul_transpose`
  `(frob (X*Dᵀ))^2 = ((XᵀX)*(DᵀD)).trace` 同链多一乘法重排，主件直落。

### 探针② Frobenius↔L2op 比较件三路线（D72-②备选实测判定）——【档位：路线 (a) 现成·自建，采用】

- **源 (a)**：/tmp/r17a_probe2_frob_opnorm.lean（四段全证明：a1 `vecNorm`
  自有 def＋sum 级 Cauchy–Schwarz 自建〔判别式路线：∑(c·x−b·y)²≥0 展开＋
  nlinarith，分离零例〕；a2 `|点积| ≤ vecNorm 乘积`；a3 frob 次乘性
  `frob(M*N) ≤ frob M * frob N`〔逐元 CS＋`Fintype.sum_mul_sum`〕；a4 列压缩
  主件 `(∀u, vecNorm(M*ᵥu) ≤ c*vecNorm u) ⇒ frob(M*N) ≤ c*frob N`
  〔transpose 面 `(Nᵀ*Mᵀ) k i = (M*ᵥ(列k N)) i` 的 mulVec 展开面〕；附六名
  #check：`Finset.sum_mul_sum`/`mul_pow`/`mul_self_le_mul_self`/
  `mulVec_apply_eq_sum`/`mulVec_mulVec`/`dotProduct_mulVec`）；
  **日志**：/tmp/r17a_probe2_frob_opnorm.log，**exit 0** 零 error 零 sorry
  （55s）。
- **源 (b)**：/tmp/r17a_probe2b_mathlibroute.lean（`noncomputable local
  instance : NormedAddCommGroup (Matrix m n ℝ) := Matrix.frobeniusNormed-
  AddCommGroup`＋桥 example `‖M‖ = frob M`〔frobenius_norm_def＋
  sqrt_eq_rpow＋norm_eq_abs 三跳〕＋`frobenius_norm_mul` 直用 example）；
  **日志**：/tmp/r17a_probe2b_mathlibroute.log，**exit 0** 零 error 零 sorry
  （57s）。
- **源 (c 负向)**：/tmp/r17a_probe2c_names.lean（四候选名 `Matrix.
  opNorm_le_frobenius`/`frobenius_le_opNorm`/`norm_le_frobenius`/
  `frobenius_norm_le` #check 负向探查＋`Matrix.toEuclideanCLM` 签名 #check）；
  **日志**：/tmp/r17a_probe2c_names.log，**exit 1 按设计**（四条
  unknownIdentifier 逐名实证缺位——与 D72 设计会话 grep 零命中同向升级为
  使用级负向探查）。
- **判定**：**采用路线 (a)**——主件 `frob_mul_le_of_vecNorm` 即 a4 照搬（纯
  sum 搬运零 WithLp 零 local instance）；B5b 需要的范数压缩面
  （`frob (S⁻¹*M*S⁻¹) ≤ frob M/λ₃²` 与 `frob (Xᵀ*E*X) ≤ λ₁*frob E`）两处
  均经 a4 两击闭合，特征值/算子范数 API 零依赖。路线 (b) 走通留档为 B5c
  备选（次乘性 Mathlib 侧现成）；路线 (c) toEuclideanCLM 未跑（(a) 已收，
  R16B §P2 摩擦已知不取）。
- **B5c 面注记**：R16B §6 余量三块中『Frobenius↔L2op 未探』就此消解——
  B5c 装配层若需 `‖M*N‖_F ≤ ‖M‖₂op·‖N‖_F` 型，走 (a) 列压缩
  （`vecNorm_mulVec_le` 面）或 (b) local instance 对接均可，两路线使用级
  在档。

### 探针③ 向量 ℓ2 范数面——【档位：现成·自建（归探针 (a) a1/a2 内）】

- **源**：同 /tmp/r17a_probe2_frob_opnorm.lean a1/a2 段（D72-③：纯函数
  `n → ℝ` 的 Pi 实例是 sup 范数非 ℓ2——**自有 `vecNorm v := Real.sqrt
  (∑ i, v i ^2)` def**＋sum 级 CS 自建，与 D68-2 frob 自有 def 同哲学；
  EuclideanSpace/WithLp 口径为备选未取）。**结论**：主件 `vecNorm` def＋
  `vecNorm_sq`/`dotProduct_self_eq`/`vecNorm_smul`/`sum_mul_sq_le_sum_sq_
  mul_sum_sq`/`abs_dotProduct_le` 六件照此落地；逆压缩向量层
  `vecNorm_inv_mulVec_le`（二次型下界 ⇒ ‖S⁻¹v‖ ≤ ‖v‖/λ₃，CS 一击＋
  特征值无关）全链走通。

### 探针④ R15C trace 探针在盘复核＋照搬源新上下文重编——【档位：在档（D69-4 口径不重跑）】

- **在盘复核**：/tmp/r15c_probe3_trace.lean 在盘（43 行，2026-10-11 时间戳
  亲验），T1 本体 15 行＋T2 6 行全证明在档——D69 裁决 4 口径复核不重跑。
- **源**：/tmp/r17a_probe3_trace_step34.lean（照搬源在新上下文〔import
  Mathlib＋TableB5Core〕重编：T1 `trace_mul_nonneg_of_posSemidef`〔CStar
  代数 nonneg 分解＋trace_mul_comm 循环移位＋posSemidef_conjTranspose_
  mul_self＋trace_nonneg〕＋T2 线性推论＋`posSemidef_of_lo` 二次型夹逼⇒PSD
  桥＋S⁻¹ 左右消去双 example；附 14 名 #check 全过）；**日志**：
  /tmp/r17a_probe3_trace_step34.log，**exit 0** 零 error 零 sorry（29s）。
- **结论**：T1/T2 主件照搬零摩擦；上界翻转 `trace_le_smul` 同链镜像。

### 主件落地（formal/lean/ThomsonN9/TableB5Trace.lean，44 定理＋vecNorm def）

零数值数据字面量（λ₁/λ₃/η/β 全为泛型变量，TTP 实例化经 TableB5Data 的
l3/u1）——无 Data 件。结构（六层）：
1. **vecNorm 层**（7 定理）：非负/平方展开/自身点积/数乘/自建 sum 级 CS/
   |点积|界；
2. **Frobenius↔trace 桥层**（13 定理）：frob_sq_eq_trace（探针①照搬）／
   frob_sq_mul_transpose（X*Dᵀ 面）／trace↔内积／frob_inner_le／frob_neg/
   frob_add_le/frob_sub_frob_le_add（三角族）／frob_mul_le（次乘性）／
   frob_mul_le_of_vecNorm（**列压缩主件**，路线 (a)）／Frobenius-Pythagoras
   双口径（trace 形 `tr(A*Bᵀ)=0`＋任务书矩阵形 `Aᵀ*B=0`）；
3. **PSD trace 族**（5 定理）：T1 trace_mul_nonneg／T2 trace_ge_smul／
   上界翻转 trace_le_smul／posSemidef_of_lo（二次型夹逼⇒PSD 桥）／
   posSemidef_transpose_mul_self；
4. **步骤 3 层**（7 定理）：P₀ 四件套（P0_mul_X/P0_transpose/XT_mul_P0/
   P0_mul_self/P0_mul_D）＋mixed_block（块分解恒等式
   `P₀*E*(1−P₀) = X*D_⊥ᵀ + D_∥*D_⊥ᵀ`，矩阵级重排）＋**头条一 step3_bound**
   （`(√λ₃ − frob D_∥)*frob D_⊥ ≤ frob (Y*Yᵀ−X*Xᵀ)`：λ₃ 下夹逼→trace 单调
   →`‖X*D_⊥ᵀ‖²_F = tr(S*D_⊥ᵀD_⊥)`→Pythagoras 二连→反向三角收口）；
5. **步骤 4 层**（9 定理）：XT_D_eq＋B 三恒等式（B_eq_factor/B_eq_inv 零
   前提纯环等式；XTEX_eq_SBS 混合块）＋逆压缩双件（vecNorm_inv_mulVec_le
   向量层 C1＋frob_inv_mul_inv_le Frobenius 层 C2＝C1 两击）＋对偶夹逼
   vecNorm_transpose_mulVec_le（λ₁ 面：对偶见证 w=(1/‖Xᵀu‖)•Xᵀu 的 CS 一击
   零 sup API）＋frob_XTEX_le（`frob (Xᵀ*E*X) ≤ λ₁*frob E`）＋**头条二
   step4_bound**（`frob B ≤ λ₁*frob E/λ₃²`＝β 口径）；
6. **TTP 实例化层**（4 定理）：ttpX_quadform_lo/hi（TableB5.ttp_sandwich_
   双侧→矩阵 mulVec 口径）＋ttpX_step3/ttpX_step4（两头条 TTP 接线：
   l3/u1 字面）。

**B5b 陈述面增量决策（本节定死，B5c 装配层底座；模块 docstring 同文）**：

1. **σ₃ 口径**：头条一取 `√λ₃` 直接陈述（`Real.sqrt lam3` 字面，平方化
   等价陈述为备选未取——前提 `0 < lam3` 保 sqrt 实值）。
2. **λ 口径**：泛型 `lam1 lam3 : ℝ`（前提 `0 < lam3`/`0 ≤ lam1`），二次型
   夹逼一律 dotProduct·mulVec 口径 `∀ v, lam3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)`
   （与 TableB5.ttp_sandwich_lo/hi 直接对接，零特征值 API——D68 三决策
   沿革）。
3. **β 口径**：头条二右端 `lam1 * frob (Y*Yᵀ−X*Xᵀ) / lam3^2`（lam3^2 记
   `lam3^2` 字面，除式陈述）；B 字面展开 `A+Aᵀ+A*Aᵀ`（A := S⁻¹*(XᵀD)
   不另设 def，与 E 同口径〔§4 决策 3〕）。
4. **vecNorm 自有 def**（D72-③落定）：`Real.sqrt (∑ i, v i ^2)`，与 frob
   同哲学零实例路径；frob↔vecNorm 桥经 `frob M = vecNorm-ish` 未设 def，
   逐定理 sum 搬运直闭。
5. **Frobenius↔L2op 采用路线 (a)**（列压缩，零 WithLp 零 local instance）：
   压缩面全部经 `frob_mul_le_of_vecNorm` 单点供给（B5c 复用面留档）。

**施工摩擦留档（R17A 亲捕，B5c 施工面预防）**：
- **have 名不可含 `ᵀ`**：`have hXᵀ := …` 在 elaborator 层报
  『Invalid pattern: Expected a constructor or constant marked with
  [match_pattern]』（`ᵀ` 系 `Matrix.transpose` 后缀记法，have 绑定位与
  记法冲突）——ASCII 名（hXT/hEXT）即消；
- **矩阵乘法结合非 rfl**：`frob (A*B*C) = frob (A*(B*C))` 须 `rw
  [Matrix.mul_assoc]` 显式重排（Matrix.mul 定义面 sum 不 defeq 结合）；
- **`div_eq_inv_mul` 方向**（本 Mathlib 版）：`a / b = b⁻¹ * a`（右逆左乘
  形），`← mul_inv`＋`← pow_two` 链拼 `λ⁻¹*λ⁻¹ = (λ²)⁻¹` 须先 `← mul_assoc`
  归左结合；
- `push_neg` 弃用告警（v4.34 起）——不阻断零 error 口径，B5c 可换
  `push Not`。

## §6 R18A B5c 极分解件（r18a-b5c-polar-lean，2026-10-12）

**任务**：表 B 第六件——B5 解析本体步骤 5–6 极分解/装配层 Lean 化（D77
裁决 1/2 口径；heavySolves=0，零求解零 SDP 零新数值证书；四账本/endgame.json/
certificates 只读；不动 references/ 与挑战件）。产出件
`formal/lean/ThomsonN9/TableB5Polar.lean`（42 定理，import Mathlib＋TableB5＋
TableB5Core＋TableB5Trace，零数值数据字面量故无 Data 件）＋门
`numerics/bounds/r18_b5c_gate.py`（seed 20261018，G0–G5＋NC1/NC2/NC3）＋
嵌套 CWD 包装器＋账本 `results/r18_b5c_ledger.json` ＋本节（append-only）。

### 开工前置探针（源 /tmp/r18a_probe_polar.lean，终版 exit 0 零 error 零 sorry，
16.5s〔热缓存〕；探针转录与 /tmp 源逐字一致——本节五组三档判定＋API 定位；
迭代史：探针件经 ≈10 版收敛〔路线 A→C→B' 三叉两转向＋API 名修正〕，
主件经 14 轮编译收敛；/tmp 日志为终版覆盖式）

### 探针① sqrt 单调性（D77 唯一待探前提）——【档位：缺位自建·路线 B'（谱映射
＋CFC 序），路线 A 被实例缺失阻断（留档），D78-1】

- **路线 A（`CFC.sqrt_le_sqrt` Rpow/Order.lean:89 算子单调）——阻断**：该
  引理需 `[NonUnitalCStarAlgebra A]`，而 Mathlib 该实例**仅 `Matrix n n ℂ`**
  有（CStarAlgebra/Matrix.lean:308 `Matrix.instCStarAlgebra` 专 ℂ；实测
  synthInstance 失败日志在档）。ℂ-搬运面（复化＋实 sqrt 相等）评估为重
  路线未取。
- **路线 C（初等交换同余，Z = X·N⁻¹）——中途弃**：施工中发现『交换 PSD 乘积
  保 PSD』在无谱工具下不可达（(W−1)(W+c•1) = M−c²•1 分解正确但 Z = X·N⁻¹
  的 PSD 性仍需交换乘积面）；且 (W+1)² ⪰ 9/4 的纯二次型直接估计只给
  (2−β)‖v‖² < 9/4‖v‖²（**算术检验**：W² 项二次型下界 (1−β)‖v‖²＋1 项
  ‖v‖² = (2−β)‖v‖²，恒 < 9/4·‖v‖² 当 β ≥ 0）——路线 C 对本探针不充分，
  弃（两处数学检误均在会话内亲算亲验后弃置，未入库）。
- **路线 B'（采用）**：谱下界（特征向量路线，R17B Q2 'key' 面逐字：
  `spectrum_toLpLin`＋`hasEigenvalue_iff_mem_spectrum`＋`exists_
  hasEigenvector`）＋sqrt 谱映射三 API 链（`CFC.sqrt_eq_cfc`
  Rpow/Basic.lean:638＋`cfc_nnreal_eq_real` CFC Instances.lean:409＋
  `cfc_map_spectrum` Unital.lean:390〔根命名空间，非 CFC. 前缀〕）＋
  `algebraMap_le_of_le_spectrum`（Unital.lean:998〔根命名空间〕，谱下界 ⇒
  CStar 序）＋`Matrix.nonneg_iff_posSemidef`（Order.lean:60）＋MatrixOrder
  序→二次型桥。落同名定理 `sqrt_quadform_lo`（两路线同名，fork 记 D78-1）。

### 探针② 行-CS 二次型界——【档位：现成·自建（B5b abs_dotProduct_le 机组装）】

- `|v ⬝ᵥ (B*ᵥv)| ≤ frob B * (v ⬝ᵥ v)`：(B*ᵥv) i = B i ⬝ᵥ v（rfl）逐行 CS
  ＋∑ vecNorm(B i)² = frob B²（vecNorm_sq＋frob 展开）＋收口两段
  nlinarith。供 (1+B) ⪰ (1−β)·1 前提（`quadform_one_add_lo`）。
- 摩擦：hsum2 的 frob 平方形与 (v ⬝ᵥ v) 形互转需 `dotProduct_self_eq`
  前向（vecNorm² → v⬝ᵥv 是**反向**）。

### 探针③ (W−1)(W+1) 交换环＋trace 循环——【档位：现成（noncomm_ring 一击）】

- `(W−1)*(W+1) = W*W−1` 与反向：`Matrix.sub_mul/add_mul/mul_add` 展开＋
  `simp only [mul_one, one_mul]`＋abel。
- **B² trace 面关键发现**：`(W+1)²(W−1)² = (W²−1)²` 是**单生成元多项式
  恒等式**——`noncomm_ring` 一击闭合（免 R17B 式手排 assoc/comm 链）；
  trace 侧无需循环移位（等式两侧直接 noncomm_ring）。

### 探针④ Y*Q = X*W + D_⊥*Q 恒等式——【档位：现成（show-rewrite 嵌套链）】

- `(1+A)*Q = W`（← W*R＋mul_assoc＋R*Q=1）＋两段 show-rewrite
  （`(X+X*A)*Q = X*Q + X*A*Q` 内嵌 `X+X*A = X*(1+A)`）＋hAQ 收口。
- 摩擦：rw 方向（`X + X*A = X*(1+A)` 需 `mul_add`+`mul_one` **正向**；
  `X*Q + X*A*Q = X*(1+A)*Q` 需 `← add_mul` **反向**＋内嵌 show）。

### 探针⑤ W 对称供给（CFC.sqrt 自伴面）——【档位：在档（R17B Q2 例 1 同式，
ᵀ/ᴴ 转换新增）】

- `cfcₙ_star` 给 ᴴ 形；ᵀ 目标经 `Matrix.conjTranspose_eq_transpose_of_
  trivial` rwa 转换（R17B 原例直接证 ᴴ，本件目标 ᵀ——多一步转换）。

### 主件落地（formal/lean/ThomsonN9/TableB5Polar.lean，42 定理）

零数值数据字面量（λ₁/λ₃/β 全泛型；结构常数 9/4·2/3·1/2·3/4·4/9·5/4 为
证明结构常数非数据常数——D77 补线/域条件的书面常数面）——无 Data 件。
结构（八层）：
1. **二次型⇒PSD 桥层**（3 定理）：quadform_nonneg_of_posSemidef（R17B Q1
   例 2 口径）＋abs_quadform_le_frob（行-CS 主件）＋quadform_one_add_lo；
2. **W 构造层**（13 定理）：sqrt_quadform_lo（D78-1 头条前提件）＋B_symm
   ＋one_add_B_eq/posSemidef/symm＋W_symm/W_posSemidef/W_mul_W/
   W_quadform_nonneg＋one_add_B_quadform_lo＋W_quadform_lo（W ⪰ √(1−β)·1）
   ＋W_isUnit（sandwich_isUnit 桥）＋W_quadform_ge_half（√(1−β) ≥ 1/2）；
3. **R 正交层**（6 定理）：W_mul_R＋WW_eq_one_add_A_AT＋R_mul_RT（R17B Q3
   核心同式）＋R_mem_orthogonalGroup（membership 主口径）＋R_eq_pair（双
   等式口径）＋Rinv_mem_orthogonalGroup（Q := R⁻¹ 见证）；
4. **frob 正交右乘不变**（1 定理）：frob_mul_right_orthogonal（trace 路线）；
5. **W−I Frobenius 界**（9 定理）：le_of_sq_le_sq 小件＋Wp1_sq_quadform
   （(W+1)² 二次型面：展开＋CS＋x := t/‖v‖² ≥ 1/2 ⇒ (x+1)² ≥ (3/2)²，
   代数证书 4u(A+2t−5/4u) = 4(Au−t²)+(2t−u)(2t+5u)）＋Wp1_sq_symm/
   posSemidef＋Wm1_Wp1/Wm1_Wp1'＋B_eq_WW_sub_one＋B_sq_trace（noncomm_ring）
   ＋Wm1_sq_posSemidef＋**frob_Wm1_le 头条**（trace_ge_smul 取 A := (W+1)²、
   t := 9/4、B' := (W−1)²——D77-1 补线全链）；
6. **步骤 5 头条**（4 定理）：vecNorm_X_mulVec_le（σ₁ 二次型面）＋
   frob_X_one_sub_W_le（列压缩）＋YQ_eq（探针④面）＋**step5_bound**
   （∃ Q ∈ orthogonalGroup n ℝ, frob (X−Y*Q) ≤ √λ₁·β + frob D_⊥）；
7. **步骤 6 条件装配**（3 定理）：smul_beta_le_half（域条件 ⇒ σ₁β ≤ √λ₃/2）
   ＋dperp_le（frob D∥ ≤ σ₁β ⇒ frob D⊥ ≤ η/(√λ₃−σ₁β)——hdpar 前提
   **字面可见**）＋**step6_final 条件终定理**（hdpar/hdom1/hdom2 三字面
   前提显式携带——D77-2：反射族 Y := X·Q̃ 下 frob D∥ ≤ σ₁β 不成立
   〔η=0、β=0 域内而 frob D∥ > 0〕，**不做假闭合**，无条件 C·δ 终定理
   不宣称）；
8. **TTP 实例化层**（2 定理）：ttpX_step5＋ttpX_step6_final（l3/u1 字面
   接线，前提显式携带沿 B5b ttpX_step3/4 式）。

**B5c 陈述面增量决策（本节定死）**：

1. **域条件书面化**：step5/step6 域一律 `β ≤ 1/2`（D77-1 书面域），层 5
   所需 β ≤ 3/4 由 1/2 ≤ 3/4 **内部 linarith 导出**——相对书面链零域弱化
   （R17B §Q4 量纲判定时曾虑 1/4 域，B' 路线下不出现）。
2. **sqrt 单调性口径**（D78-1）：谱映射＋CFC 序路线落 `sqrt_quadform_lo`
   （前提面：M 对称＋c ≥ 0＋二次型下夹逼；结论面：c·(v⬝ᵥv) ≤
   v ⬝ᵥ ((CFC.sqrt M)*ᵥv)——纯二次型口径零特征值陈述）。
3. **条件前提显式**（D77-2）：step6_final/ttpX_step6_final 的 frob D∥ ≤
   σ₁β 与 β ≤ min(1/2, √λ₃/(2√λ₁)) 两分立面全部字面入前提（dperp_le 的
   hdpar 字面牙为门 G4 锚）。
4. **B 字面括号化**：B := `(A + Aᵀ + A * Aᵀ)` 全括号字面（与 B5b
   B_eq_factor/B_eq_inv 的 LHS 精确匹配——CFC.sqrt 嵌套下重排括号必断链）。
5. **行数口径**：实测 854 行（净本体 744 行——非空非文档注释行）vs R17B
   §5 估 ≈450–650：CFC.sqrt(1+B) 字面在陈述面出现 ≈80 次（每次 ~5 行）
   撑胀陈述面；42 定理（≥28 过）——行数为陈述面冗长所致，非证明体量
   （D78-5 留痕）。

**施工摩擦留档（R18A 亲捕 11 条，B5c 后件预防）**：

- **NonUnitalCStarAlgebra 仅 ℂ 矩阵**（CStarAlgebra/Matrix.lean:308）：
  CFC.sqrt_le_sqrt 在 ℝ 矩阵面 synthInstance 失败——D78-1 路线叉源；
- **mulVec 族命名向位**：`(A+B)*ᵥv = A*ᵥv + B*ᵥv` 是 `add_mulVec`（矩阵
  侧加），`A*ᵥ(x+y) = A*ᵥx + A*ᵥy` 是 `mulVec_add`（向量侧加）——与
  B5b 的 sub_mulVec 直觉易混；
- **mulVec_mulVec 实参序**：`(v, M, N)`——v 在前（`M *ᵥ N *ᵥ v =
  (M*N)*ᵥv`）；B5Core quadsum_eq 用 `←` 方向取 (M*N)*ᵥv → M*ᵥ(N*ᵥv)；
- **dotProduct_mulVec 出 vecMul 形**：`v ⬝ᵥ (A*ᵥw) = (v ᵥ* A) ⬝ᵥ w`——
  v ᵥ* A 不含 Aᵀ 字面，对称面需 `← vecMul_transpose`＋hW 两步转换；
- **rw 首匹配可命中内层**：`rw [mul_sub]` 在含 (Y−X) 内层的 W 字面上先匹配
  Xᵀ*(Y−X) 意外展开——大字面恒等式一律 show-rewrite（整式方程）定向；
- **set 抽象后 ^2 与 * 不合**：hcs（t*t 形）对 goal（t^2 形）exact 失配，
  需 `rw [← pow_two t]` 归一；
- **field_simp 可独闭目标**：尾随 ring 报 "No goals"——field_simp 后不加
  冗余收口；
- **add_le_add_left/right 向位**：`√λ₁*x + frobD` 形（frobD 在右）需
  add_le_add_**left**（c 在右：a + c ≤ b + c）——与直觉相反；
- **IsUnit.of_mul_eq_one 显式单元实参**：`IsUnit.of_mul_eq_one _ h`
  （a 显式——裸传 h 会把 h 当 a）；
- **smul 标量 ℕ 默认**：`(9/4) • (1 : Matrix)` 中 9/4 默认 elaborates ℕ——
  需 `(9/4 : ℝ)` 显式定类型；
- **le_div_iff₀/div_le_div_of_nonneg_left 实参序**：后者为
  (ha : 0 ≤ 分子) (hc : 0 < 小分母) (h : 小分母 ≤ 大分母)——hc 是**严格**
  正（0 < 非 0 ≤）。

**门与账本**：`numerics/bounds/r18_b5c_gate.py`（seed 20261018；G0 账本
〔theorem_count=42〕＋G1 树守卫〔OWNED 六件＋冻结件 TableB5/TableB5Data/
TableB5Core/TableB5Trace/TableB1*/TableB6*/挑战件/references//四账本＋
endgame.json sha256 冻结锚 86863a09…69f＋r18 家族放行层（D68-3/D77-3）〕＋
G2 依赖序五连 elaboration ≤600s＋G3 42 定理公理恰三标准＋G4 36 语句锚
〔sqrt 单调性双面/W 供给/R membership 双口径/frob 右乘/9/4 面/2/3 头条/
∃Q 三牙/hdpar·hdom1·hdom2 字面/TTP (l3:ℝ)^2 牙〕＋G5 独立第二实现
〔有理极分解构造：W := diag 有理（w_i ≥ 1/2）＋O := Pythagorean 有理旋转
（3/5,4/5）×符号置换＋A := W·O−1 使 B = W²−1 精确＋X 列 Pythagorean 框架
使 σ_j = r_j 有理——B 恒等式/极分解 R==O/YQ 27 元/frob 右乘三面/D77 补线
squared 链/σ₁ 列压缩 squared 链/步骤 3 面 AM-GM 充分核＋C 链 Fraction 复核
〔TableB5Data 源直读零手抄〕＋账本 sha256 cross-check〕＋NC1 sorry 注入
〔quadform_nonneg_of_posSemidef〕＋NC2 双棱〔(l3:ℝ)^2→(l3:ℝ)^3 指数面＋
(2/3)→(3/4) 常数面〕＋NC3 双棱〔W' := 1+B 非 sqrt 极因子＋伪正交
Q' := (3/2)Q〕）；嵌套 CWD 包装器（runpy 式，R10A 起先例）；
`results/r18_b5c_ledger.json`（seed 20261018/heavy_solves=0/
data.theorem_count=42/axiom_policy 恰三标准列表/文件 sha256/门全步——
r16a/r17 新形态）。

**零求解声明（G5/G6 锚）**：本任务 **heavySolves = 0**（字面锚）——零重
求解、零 SDP、零新数值证书；四账本（m9_campaign/m10_campaign/
hermite_v2_campaign/typed_ladder）、endgame.json（sha256 == 86863a09…69f
冻结锚本会话亲算不变）、certificates/、typed_ladder rungs 零触碰（只读）。
D77（设计师在途）随本件首提交收编（R17A 4ce494b 收编 D72 同式）；D78
执行六裁决随本节落 decisions.md。

**§6 证据索引（/tmp 留档，门 G5 逐一在盘核验）**：

| 证据 | 内容 | 结果 |
|---|---|---|
| /tmp/r18a_probe_polar.lean | 五组探针源（探针①-⑤：15 #check＋sqrt 单调性例〔B' 路线〕＋行-CS＋交换环/trace＋YQ 恒等式＋W 对称） | 编译对象（§6 各节转录同源） |
| /tmp/r18a_probe_polar.log | 探针运行日志 | exit_code=0 零 error 零 sorry（16.5s〔热缓存〕） |
| /tmp/r18a_polar_c14.log | 主件终版编译日志 | exit 0 零 error 零 sorry（42.97s；c1–c14 迭代史 14 轮） |
| /tmp/r18a_axioms.log | 42 定理 #print axioms 全量 | 恰 {propext, Classical.choice, Quot.sound} 零 sorryAx（42×3 uniq） |
| /tmp/r18a_gate_run11.log | 门首轮全过前的迭代日志之一 | G0–G5 逐面收敛记录（sha 常量/锚/维数/C 链公式四修） |

## §7 R19A B5Uncond 无条件化件（r19a-b5u-uncond-lean，2026-10-12）

任务锚：r19a-b5u-uncond-lean（R19A，campaign dwfrun-f9904baf 第 14 轮，
D82 裁决 1/2/3 口径）。产出件 formal/lean/ThomsonN9/TableB5Uncond.lean
（namespace ThomsonN9.TableB5Uncond，**24 定理**，997 行〔含 90 行模块
docstring；import Mathlib＋TableB5＋TableB5Core＋TableB5Trace＋TableB5Polar，
零数值数据字面量故无 Data 件——常数一律以 TableB5Data 既有 def 表达〕）＋
门 numerics/bounds/r19_b5u_gate.py（＋嵌套 CWD 包装器，seed 20261019）＋
账本 results/r19_b5u_ledger.json。**B5c 步骤 6 无条件化落地**：D77-2 缺口②
（隐含前提 frob D_∥ ≤ σ₁β 反射族不可消去）被两条无条件档取代——路线 B
（全域 ½-Hölder：d_P ≤ C_B·√δ，C_B ≈ 7.128，域＝记录域全体）＋路线 A
（窄域线性：d_P ≤ (√u₁u₁/l₃² + 2√2/√l₃)·η，C_A·δ 口径 C_A ≈ 18.957、
域 δ ≤ δ_A ≈ 0.014588）——**两条无条件头条＋TTP 实例的陈述跨度内零
hdpar 前提**（D82-3 机器锚：frob (X * ((Xᵀ * X)⁻¹ 模式零命中，G4 有牙）。

### 探针三档判定转录（R18B 三路线供件 → R19A 施工面）

R18B（notes/dperp-gap-study.md）三档判定对 R19A 施工的实测对照：

| R18B 判定面 | 预估 | R19A 实测 |
|---|---|---|
| (ii) 块恒等式（例 1/例 2 纯环＋P₀ 桥） | 现成（30＋33＋48 行级） | **如预期**：抽象 P₀ 面双例源转录零改动走通（E_mul_one_sub_P0_of／one_sub_P0_E_one_sub_P0_of）；例 3 的 48 行前提桥大部分在库免费——P₀ 桥六面 P0_transpose/P0_mul_X/P0_mul_D（TableB5Trace:502–580）＋P0_mul_self 逐件复用，具体面 block_id1/block_id2 仅需 P₀·D_⊥=0（P0_mul_D＋P0_mul_X 消去）＋Y 分解（abel）两步桥 |
| §ii.3 未跑面 op(1−P₀) ≤ 1 二次型面 | ~15–20 行低风险 | **如预期**：vecNorm_one_sub_P0_le 净 ~22 行（幂等＋伴随搬移 u ⬝ᵥ (P₀*ᵥu) = ‖P₀*ᵥu‖²＋dotProduct_sub 展开＋√ 单调收口） |
| §iv.1 第 5 步 trace-CS ~20 行 | sq_sum_le_card_mul_sum_sq 面 | **口径修正（D83-①）**：实走 sum 级 CS 取 y := 1（在库 sum_mul_sq_le_sum_sq_mul_sum_sq，@- 显式实参避实例卡死）＋√card 口径 \|tr M\| ≤ √(Fintype.card n)·frob M——√card 使 9 行实例恰为 3（√9=3 接线），对齐 R18B P4 常数审计 C_B = k1·√δmax + √(3√72)；abs_trace_le_sqrt_card_frob 净 ~30 行 |
| (iii) A2 frob 对称面 40 行／A7 组装 53 行／逆向三角 18 行 | 已走通 | **零改动源转录**：frob_B_prime_eq／assembly_Y_lower／vecNorm_sub_le 照探针 2 终版逐字（A4 例 b 转 Aᵀ 面配 frob 对称面＋quadform_one_add_A_lo 非转置化） |
| §iii.5 未跑面 A9 λ₃(Y) 压缩 ~30 行 | step3_bound 同形 | **低于预估**：lamY_dperp_sq_le 净 ~13 行（posSemidef_of_lo＋trace_ge_smul＋frob_sq_mul_transpose 三件直拼——λ₃(Y) 以二次型口径假设引入〔D82-1〕，由 A7+A6 在 A10 内部供值） |
| §iii.5 未跑面 A10 闭环消歧 ~25–35 行 | nlinarith 实代数 | **如预期偏上限**：dperp_le_linear 净 ~130 行（消歧链 t ≤ √(3η) ≤ c/2＋A7/A8/A9 合并 (c−t)t ≤ η＋反证 t > 2η/c＋c ≥ √(λ₃/2) = √λ₃/√2 终链；nlinarith 组合面多、div/sqrt 单调每步显式） |
| §iii.5 未跑面 A11 终装配 | 在库对接 | **低于预估**：step6_uncond_linear 净 ~20 行（step4_bound＋step5_bound＋A10＋ring 收口） |

路线 B 七步链（§iv.1）实测全链走通：t² = frob D_⊥²（frob_sq_eq_trace）＝
tr(D_⊥D_⊥ᵀ) ＝ tr((1−P₀)E(1−P₀))〔block_id2＋congrArg〕＝ tr(E(1−P₀)²)
〔trace_mul_comm〕＝ tr(E(1−P₀))〔(1−P₀) 幂等：noncomm_ring 展开证书＋
P0_mul_self〕≤ √9·frob(E(1−P₀))〔trace-CS〕≤ 3η〔op ≤ 1 面〕。

### 施工摩擦（亲历留档）

主件六轮编译收敛（c1–c6，/tmp/r19a_c2.log…c6.log 留档；探针
/tmp/r19a_probe1.lean 另四轮）。亲历八条：

1. **隐参实例卡死**：`sum_mul_sq_le_sum_sq_mul_sum_sq (fun i => M i i) (fun _ => 1)`
   上 Fintype ?m 实例卡死（lambda 域类型不定⟹实例不定）——裸注 lambda
   不中、named 实参不中，**@- 全限定显式实参**（@ThomsonN9.TableB5Trace.
   sum_mul… n _ …）一发过；同病：`∑ i, (1:ℝ)` 的 binder 类型须显式
   `∑ i : n`。
2. **frob 的 definitional unfold**：`unfold frob; rw [Real.sq_sqrt …]` 在
   calc 中间步触『not type-correct under implicit transparency』（M i 部分
   应用面）——改 **show 面**（show (Real.sqrt (∑…))^2 = ∑… from Real.sq_sqrt h）
   一发过；`:= rfl` 关 Eq 步同理改 `heq : (frob M)^2 = ∑… := by show …`。
3. **rw 方向敏感三处**：trace_mul_comm 须先 ← mul_assoc 归 (1−P₀)·(E(1−P₀))
   再 comm；block_id2 桥用 congrArg 形（block_id2 右端 D·Dᵀ 与 frob_sq_
   eq_trace 的 (Dᵀ·D) 面不可直 rw——改用 frob_sq_eq_trace 主形对齐）；
   hYv 的 Y 替换须正向（← hYeq 会把 Y−X 内的 Y 一并展开成巨型代入）。
4. **mul_le_mul_of_pos_left/right 本仓无**：只 mul_le_mul_of_nonneg_left/
   right（≤ 面）＋ mul_lt_mul_of_pos_left/right（< 面）——strict/le 与
   left/right 四象限按需选，ht0.le 补面。
5. **Real.sqrt_mul/sqrt_div 实参序**：(h : 0 ≤ x) (y : ℝ)——y 是显式 ℝ
   不是证明；数据常数包络前提须 norm_num [sqrt72Up]（def 展开名单），
   裸 norm_num 不展 TableB5Data def。
6. **A10 消歧的严格性供面**：反证步需 η < (c−t)·t 严格不等——非严格链
   (c/2)(2η/c) ≤ (c/2)t ≤ (c−t)t 只到等号；严格性从 hcon（2η/c < t）经
   mul_lt_mul_of_pos_left 注入第一环，第二环保非严格即可。
7. **div_le_div_iff₀ 实参序**：分母序＝（左分母, 右分母），先 8 后 4 与
   先 4 后 8 不同命题（本件一处反着写过）。
8. **linarith 原子乘积不入**：2η·√λ₃ ≤ 2√2·η·c 型目标三原子乘积
   nlinarith 不燃——拆 mul_le_mul_of_nonneg_left（hkey2）＋le_of_eq (by ring)
   两步显式收口。

### 陈述面决策（D83）

- **D83-①（trace-CS √card 口径）**：trace-CS 面取锐式
  `|tr M| ≤ Real.sqrt (Fintype.card n) * frob M`（任务书转述的 card·frob
  为宽式；√card 使 9 行实例恰 √9 = 3，对齐 R18B P4 十九点网格常数审计
  C_B = k1·√δmax + √(3√72) 的 3——宽式会给 C_B′ = k1√δmax + 3·72^{1/4}
  常数劣化）。G4 牙取 Fintype.card 面在陈述内。
- **D83-②（头条 Fin 9 行特化）**：路线 B/A 头条陈述取 X Y : Matrix (Fin 9) n ℝ
  （探针 2 r18b_assembly 同式先例）——『3』字面（√(3·η)）只在 9 行语境
  数学为真；泛型面（block_id*/dperp_sq_le_hoelder/vecNorm_mulVec_le_frob/
  lamY_dperp_sq_le）保持 {m n} 多态。
- **D83-③（A9 二次型口径）**：λ₃(Y) 不以特征值/谱 API 引入，以二次型
  前提 `∀ v, lamY·(v⬝ᵥv) ≤ v⬝ᵥ((YᵀY)*ᵥv)` 供 lamY_dperp_sq_le（step3_bound
  同形口径，D82-1）；在 A10 内部以 lamY := (c−t)² 由 A7＋A6 供值
  （t ≤ c/2 ⟹ c−t ≥ c/2 > 0 使平方化合法——出域反例 P2-NC 证域条件实质）。
- **D83-④（C 形推论的域内无条件）**：step6_hoelder_Cform 的 β ≤ 1/2 前提
  由 TableB5.delta_max_valid **内部导出**（δ ≤ δmax 记录域内自动成立），
  前提只留真域面（记录谱包络 l₃ ≤ λ₃ ≤ λ₁ ≤ u₁＋δ 域）——『全域』的
  实质口径；C_B 内常数取 √(3·sqrt72Up)（√72 ≤ sqrt72Up 安全向、有理内项
  可 Fraction 复核——门 G5(f) 十九点网格对面）。
- **D83-⑤（窄域包络口径）**：路线 A 域取 η ≤ λ₃/24（c_lo := √(λ₃/2) 包络
  D79-5：c² ≥ λ₃/2 ⟹ c²/12 ≥ λ₃/24——门 G5(e) 39 点网格＋P2-NC 出域
  反例复现验证域条件实质非技术性）。

### 零求解与验收

- **heavySolves = 0（字面）**：零重求解、零 SDP、零新数值证书；四账本/
  endgame.json 只读（sha256 == 86863a09…69f 亲算不变）；TableB5Polar.lean
  R18A 本体冻结锚 sha256 == d8c58f7d…8516（D82-2 增入 G1 冻结面）。
- 验收门 numerics/bounds/r19_b5u_gate.py：G0 账本（seed 20261019/
  heavy_solves == 0/theorem_count == 24/axiom_policy 恰三标准 set 相等）＋
  G1 所有权（r19 家族放行层 D82-5；共享家族 notes 件 git 溯源 append-only
  账本锚 D80-6 自始内置）＋G2 依赖序六连 elaboration（Data→B5→Core→
  Trace→Polar→Uncond 各 ≤600s）＋G3 公理（24 定理 ⊆ 三标准零 sorryAx）＋
  G4 语句锚 26 件＋**无 hdpar 机器锚（四头条陈述跨度 frob (X * ((Xᵀ * X)⁻¹
  零命中＋跨度正向牙——D82-3 核心）**＋G5 Fraction 独立第二实现（块恒等式
  81 元×2／op ≤ 1 实例／tr == tr＋(3η)²−tr² ≥ 0／‖Y·D_⊥ᵀ‖² ≤ η²／闭环
  39 点网格＋P2-NC 复现／常数链 k1·C_B·C_A·δ_A 源直读复核）＋NC1 sorry
  注入＋NC2 三棱（√(3*→√(4*／2√2→3√2／**hdpar 前提注入必被拦**）＋NC3
  双棱（未投影 M／常数篡 3→4）。

### R19A 证据索引（本会话亲跑，/tmp 留档）

| 日志/源 | 内容 | 结果 |
|---|---|---|
| /tmp/r19a_probe1.lean | 探针 1 源（trace-CS／√9=3／op≤1 面／P₀·D_⊥=0 四面，四轮收敛） | 编译对象 |
| /tmp/r19a_c2.log…c6.log | 主件六轮编译迭代日志（c1 内联） | c6 exit 0 零 error 零 sorry |
| /tmp/r19a_axioms.log | 24 定理 #print axioms 全量 | 恰 ⊆ {propext, Classical.choice, Quot.sound} 零 sorryAx（24 件全过） |
| /tmp/r19a_c6.log | 主件终版编译日志（含 2 条无害 warning：unused simp arg＋push_neg deprecation） | exit 0 |

## §8 R21B 表 B 第八件链装配/节点辨识形式件（r21b-chain-lean，2026-10-24）

### 对象与定位

R20 缝消费的形式接口落地：`notes/l5l6-seam.md` §3 明示的『δ=ρ 缝认同
定＝簿记口径…若未来成证书须替换为逐对口径的显式转换』Lean 化＋
L2→L3→L5→L6 链装配条件定理——表 B 第八件（D90 裁决 1／D92 裁决 1）。
新件两件＋发射器＋门＋账本：

- `formal/lean/ThomsonN9/TableB5Chain.lean`（namespace
  ThomsonN9.TableB5Chain；import Mathlib＋TableB1Data＋TableB1＋
  TableB5Data＋TableB5＋TableB5Core＋TableB5Trace＋TableB5Polar＋
  TableB5Uncond＋TableB5ChainData——冻结件零改动只 import）；
- `formal/lean/ThomsonN9/TableB5ChainData.lean`（发射器
  `numerics/bounds/r21_b5chain_data.py` 产出，r13_a1/r15_b1_data.py
  先例：15 对 ν 容器间隙精确 ℚ 下界 def g01..g45＋逐对端点恒等
  norm_num 定理＋gMin（15 对之 min）＋r_ball=950125/10⁸＋sqrt2Up/
  dmaxUp/tUp 200-bit Newton 上包（r20_seam_probe.sqrt_rat 同配方逐位）
  ＋CBhi/CAhi/deltaA＋rhoNeedB/rhoNeedA 复合阈值＋域面六件）。

### 三件套定理（36 定理；D92 裁决 1–2）

- **(i) 节点辨识唯一性** `ident_unique`：z 盒内 ν_a(z)∈容器_a
  （nu_container_idx 六臂——TableB1.nu_containers 索引面）⟹ 两节点距离
  ≥ g_ab（nu_dist_ge_gap）⟹ 双命中 |t−ν_a|≤ρ ∧ |t−ν_b|≤ρ ∧ a≠b ⟹
  gMin ≤ 2ρ（pair_gap_le_two_rho）；ρ<gMin/2 ⟹ a=b。配套
  identNode（管前提 Classical.choose 的辨识映射）＋identNode_unique
  （well-definedness＝(i) 的直接消费）＋pattern_ident_lift（辨识窗内
  proximity→identification 升级桥——(P1)–(P4)/未来 L3 供给接口）。
- **(ii) δ=ρ 逐对口径显式转换** `chain_convert`／`chain_convert_A`：
  TubePremise（L2 管前提形）＋PatternCons（pattern-consistency 显式
  hypothesis：σ₀-重排逐对近邻，**管前提条件化**——D92 裁决 2：条件形
  不蕴含管前提〔非条件形经 hTube_of_hpat 的 σ-pullback 蕴含之——层间
  关系在库机器可查〕，保证 seam 推论非空）＋行单位 hunit＋辨识窗
  hρid ⟹ σ₀-重排竞争者 L5 前提以 δ:=ρ 成立：路线 B
  frob (ttpX z − rowPerm Y σ₀*Q) ≤ C_B·√ρ（eta_le_sqrt72 √72 精确面＋
  step6_hoelder_Cform 无条件头条）；路线 A（窄域 hρA: ρ≤δ_A）
  ≤ coeff_A·η（ttpX_step6_linear 头条）。桥面：ttpX_gram_nodeOfN
  （(ttpX z) i⬝ᵥ(ttpX z) j = ν_{nodeOfN(i,j)}(z)——B1 证书层与链装配层
  的形式链接，gram_nodeOfN 经 dot3_sym/nodeOfN_sym 对称化到全序对）。
- **(iii) 链装配条件定理** `chain_assemble_B`／`chain_assemble_A`：
  (ii)＋球门（C_B·√ρ ≤ r_ball／coeff_A·√72Up·ρ ≤ r_ball，
  r_ball=950125/10⁸ 精确 ℚ）＋L6Hyp（**L6 显式假设接口**：∀ Y′，
  ∃Q∈OG, frob (ttpX z−Y′*Q)≤r_ball → E Y′≥Ē；E/Ē 变量级——L6 系
  interval_certified_numeric 层不形式化，弦距口径以 d_P 球 ∃Q frob 形
  承载，B5c→B5Uncond 先例）⟹ E (rowPerm Y σ₀) ≥ Ē。
- **缝推论** `seam_cor_B_pair`／`seam_cor_A_pair`（未来 L3 证书喂入
  契约）：E (rowPerm Y σ₀) < Ē ⟹ ∃ pair，对节点集距离 > ρ_need，
  ρ_need=rhoNeedB=min(gMin/2,(r_ball/CBhi)²)／rhoNeedA=min(gMin/2,
  r_ball/CAhi)——球门/辨识窗在推论内以 CBhi/CAhi 包络内部导出
  （CB_le_CBhi／coeffA_le_CAhi 包络引理；threshB/A_lt_gMin_half、
  threshA_le_deltaA 域面 norm_num）。**R20 缝阈值（r20_l5l6_seam.json
  r* 口径行逐位在账）自此在形式层承重。**

### 常数与交叉对账（D92 裁决 3）

- gMin＝0.0370121656…（15 对容器间隙 min，attained_by g01＝ν₁–ν₂ 容器
  间隙）；辨识窗＝gMin/2＝0.0185060828…；tube.json
  /ttp_spectrum/half_gap=0.01850609934999997（float_advisory 十进制锚；
  verdict.need 同数）——定向宽安全边 **0 ≤ 2·half_gap−gMin = 3.31e-8
  ≤ 1e-5**（容器包络宽 ~1e-6 级〔ν₁/ν₄/ν₅ 系 z² 包端点精确式，宽来自
  z 盒非点；ν₂/ν₆ 200-bit Newton 包宽 ~1e-60〕、间隙 0.037 级，余量宽）。
- **r_ball 口径交叉对账**：CBhi==r20 supply.C_B.hi.exact 逐位、CAhi==
  supply.C_A.delta_caliber.exact 逐位、deltaA==supply.C_A.delta_A.exact
  逐位；(r_ball/CBhi)²==r20 seam_table r_star_raw/B_global_hoelder 行
  threshold.exact 逐位、r_ball/CAhi==r_star_raw/A_narrow_linear 行逐位；
  r_ball==r*==950125/10⁸==l6_intube quadraticGrowth.rigorousRadius 精确
  十进制（== R_MAX/16，R21A G3 箱定律口径）。轨道偏移 deltaOrbitArchive
  r_eff trim 系数值层细化不入 Lean（D90 裁决末段口径）。

### 零求解与验收

- **heavySolves = 0（字面）**：零重求解、零 SDP、零新数值证书；四账本/
  endgame.json 只读（sha256 == 86863a09…69f 亲算不变）；TableB5Uncond
  ==c79fc623…/TableB5Polar==d8c58f7d… 冻结锚；隔离面（r21_b5chain 不入
  endgame.json/endgame_chain.py 文本＋chain-only 干跑五字段零漂移＋
  冻结 22 叶分布）沿 R20/R21A。
- 验收门 `numerics/bounds/r21_b5chain_gate.py`（seed 20261021；编译型门
  1200s 文档化例外沿 R18/R19；CWD 无关）：G0 账本（seed/heavy_solves/
  kind/axiom_policy 恰三标准/theorem_count 双件 regex 复核/自有件
  sha256 严格锚/冻结锚三件）＋G1 所有权（git 双路由＋r21 家族放行层）＋
  冻结面（表 B 十件 Lean git diff 守卫＋挑战件/references 零触碰＋四账
  本＋endgame/Uncond/Polar 三 sha256）＋隔离面＋G2 发射器确定性重跑
  （/tmp 逐位 cmp）＋依赖序十连 elaboration（各 ≤600s）＋G3 公理直查
  活体（71 定理 #print axioms ⊆ 三标准零 sorryAx）＋G4 语句锚（import
  面恰十行＋接口形三件＋三件套牙＋主件零 ≥15 位字面量＋数据件 15 间隙
  def 全在＋非交叠零引用）＋G5 离线精确复核（15 间隙/gMin 独立重导逐位
  ＋CBhi/CAhi/deltaA 与 r20 位对账＋r_ball 口径交叉对账＋rhoNeed* min
  支路＋域面六件＋half_gap 定向宽安全边）＋NC1（注入 sorry 必被 G3 拦）
  ＋NC2（篡 gMin +1% 必被 G5 重导拦）＋NC3（篡 CBhi +0.1% 必被 r20 位
  对账拦）。
- 本节锚定与账本：`numerics/bounds/results/r21_b5chain_ledger.json`
  （kind=n9-r21-b5chain-ledger、seed 20261021、heavy_solves=0、
  theorem_count=36＋theorem_count_data=35、新件 sha256、冻结锚）。
