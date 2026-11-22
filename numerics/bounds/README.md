# bounds/ —— Thomson N=9 严格下界计算

本目录产出 Thomson 问题 N=9（单位球面 9 点库仑能量 `E(x)=Σ_{i<j}‖x_i−x_j‖⁻¹`）的
**严格下界**。第一个成员是 Yudin 型两点 LP 界（`lp_bound.py` → `results/lp.json`）。

## l2_rigorize.py —— L2 强制口径严格化（2026-10-05，无悔三件之一）

ε_forcing 从 tube.json 的 float 口径改为精确 Fraction：`results/l2_rigorous.json`
（~30s，无需 cvxpy/求解器）。**ε_forcing = 4.153454e-4**（精确分数入 JSON）＝
(1+R2max)·E\* − e_dy + defl（cap m0748_M8 证书数据；逐轨道更细 −R1_o）。
全链：38 PSD 块 LDLᵀ、归一化 ==0、R1/R2/defl/R2max 重算与 provenance 逐位相等、
certified 重算 == claimed_bound、typed 恒等式于证书数据 × 随机有理构型 ==0、
dyadic 装配损失（e floor 1.79e-15、h/ψ/c ≤ 2⁻⁴⁹）精确入账、minorant 抽查。
诚实要点：字面「ε_rig ≤ 数值口径（4.153070e-4）」不可满足——差恰为
E\*·R2max = 3.838e-8（数值口径自述忽略的 (1+R2) 因子）；实现断言为
ε_rig ≤ ε_num + E\*·R2max + 1e-15，超出即 exit 1；ρ_spec 平台 0.6447 不受影响。

## l4_procrustes.py —— L4（账本 L5 位）Procrustes 刚性常数（2026-10-05，无悔三件之二）

`results/l4.json`（<1s；`--selftest` 负对照）。**d_P := min_{Q∈O(3)}‖X−YQ‖_F ≤
C·δ，C = 14.8787，δ ≤ δ_max = 0.1712**（内积偏差口径 |Δ⟨x_i,x_j⟩| ≤ δ；
弦距离口径 2C = 29.7575；前提对某重排成立即模 O(3)×S₉）。方法：显式构造证明
（E=XDᵀ+DXᵀ+DDᵀ 的 P₀ 投影分解：混合块给 ‖D_⊥‖、平行块 XᵀEX=S·B·S 给旋转
规范后的 ‖D_∥‖ ≤ σ₁β，β=λ₁η/λ₃²——**线性** Lipschitz，优于账本设想的 C√η）；
常数以纯 Fraction 区间算术取 z\* 隔离区间最坏情形：λ₃(S) ≥ 2.970726、
λ₁ ≤ 3.014638（区间 Sylvester 主子式）。推导六步恒等式数值核对残差 ≤3.3e-15；
monte-carlo 299 试次 max d_P/δ = 2.002 < C（advisory）；三负对照全触发
（秩亏平面构型/t>λ₁ 认证器齿/非对称重排前提失效）。

## endgame_chain.py —— Round 4 收尾装配与闭合判定（2026-10-05）

三线（条带/管状/局部极小）产出的装配判定：`results/endgame.json`（判定 0s；
`--reverify-certs` 进程外重验证 5 类证书 ~2 分钟）。

- **拼合口径**：条带 6 片中 3 片受阻 ⇒ `allPositiveMargin=false` ⇒
  **assembledRecord = 25.759445973097478**（HP 兜底值为全局最弱片），瓶颈 =
  洞 [−0.82,−0.748]。12 原子区域分区（5 slab + 3 认证条带 + 3 洞子带 + cap）
  精确 Fraction 装配，无缝盖满 [−1,1]；exclusion 片全 > E*、TTP-covering 片
  （HP/cap）全 ≤ E*+1e-6（均精确断言）。六片全正的假想纪录（cap
  25.759571186）记入 wouldBe_if_all_strips_positive。
- **收尾链闭合（m≥−0.748：管半径 × 刚性 × 全空间局部极小）**：**closed =
  false**，断点 L0/L2/L3/L4/L5/L6/L7（仅 L1 已严格）。L3 为结构断点（ρ_spec
  差 34.8×，零集地板仍差 2.52×）；L6 的 r_tube=0.07601 是 sqrt(2ΔE/λ) 公式值
  （复核一致 ≤7.9e-14）但 λ→半径转换缺 Taylor 三阶余项界，非严格半径；
  remainingGap 逐引理精确到"缺什么参数、差多少"。
- **证书重验证**（`--reverify-certs`，全部 exit 0）：cap m0748_M8、3 条带、
  最弱 slab 各 `--verify-cert` 进程外复核；HP 按存档 reproduce 命令（显式
  --k 64）重生成到临时文件并逐位比对 claimed_bound。
- 诚实口径：判定输入只认存档账本/证书字段 + 重验证 exit code；E* 为三源校验
  参考值而非已证最优。

## tube_probe.py —— L3 路线 b tube certificate 限时可行性探针（2026-10-05，feasible=false）

GAP-REPORT Round 5 清单第 1 项（宽 cap 架构 A 核心部件）。**形式**：域乘子条件化
（slack 乘子族扩容 (s−ν_k)²−ρ²×{u,v,t}×6 节点＝管外强制/管内让界）＋两点 minorant
6 节点管外分段（每 gap 段独立 Markov–Lukács）＝两段式条件证书：全管外构型
（全部内积 ≥ a₀ 且距全部节点 ≥ ρ）⟹ E ≥ e_out(ρ,M,K)；选型理由与罚函数弃选论证
见文件 docstring。**探针矩阵**（3 次调用合并 `results/tube_probe.json`，求解累计
2502.9s ≤ 预算 1h）：(4,3)/(5,4)/(5,5)/(6,6) × uncond/full/slack × ρ ∈
{halfgap=0.0186, 0.5x=0.038, 1x=0.076, 2x=0.152, 3x, 4x}，a₀=−0.82。

- **结论 feasible=false**：架构 ρ（≤0.038）全档零分离（Δe_val：halfgap −1e-5…
  −3.3e-4；0.5x@(6,6) −8.6e-5——含 uncond 未饱和的 (6,6)，排除 K 饱和遮蔽解释）；
  机制指标证实 halfgap 处求解器不动用管自由度（bulge=0、TTP-λ≥0；2x 处
  bulge=7.67、λ=−0.149），瓶颈伪竞争者不住在半谱隙管内。分离只在粗管区且
  E*(ρ) 交叉点 (5,5)/(6,6) 同落 ρ∈(0.038,0.076) 不随规模下移；粗管 e_out−E* ≥ 0.8
  使 L2 强制 ε_forcing 退化（4.15e-4→≥0.8）→ 两段式无法拼合。
- **正确性金丝雀全过（float 级）**：认证域 slack>0、分段 minorant=0 违规、恒等式
  残差 ≤5.2e-6、oracle 不等式（e_val ≤ 实测全管外构型 E）全档成立；实测全管外构型
  端到端 spot check（84 三点 λ ≥ +4.8e-5、E−e_val=+3.5）。uncond(4,3) 与
  typed/solve.solve_case 逐位一致（25.708594779）；(4,3)/(5,4) full@halfgap 两次
  独立重解逐位一致。
- **认证集形态（advisory）**：随机 20 万中全管外 halfgap 155 个（min E 29.3）/0.5x
  5 个（35.3）/1x 1 个（68）/2x 0 个；3 紧簇参价族 qualifying 2.5k–9.3k（min E
  34–82）；tri_cap_prism 族 0（全部 ρ）。
- 复现：`numerics/.venv/bin/python numerics/bounds/tube_probe.py`（默认矩阵）；
  `--runs "M,K,variant,rhoTag;…"` 追加档；`--smoke` 快验。gaps 与 (8,6)/(9,6)
  SDPA-GMP 单点未测等残留见 JSON verdict/gaps。

## tube_analysis.py —— 管状/稳定性量化：typed 谱管重诊断 + 严格 λ_min + 引理链（2026-10-04）

GAP-REPORT Round 3 §④ 第 2/3 项的落地：在 m0748_M8 证书上重做 Round 2 的管状
诊断（typed 时代几何已变），产出 `results/tube.json`（全流程 ~85s）。

- **管半径**：λ_min(15 维商切空间) = 0.143935（FD 复核 ≤4.2e-8，与 Round 2
  cap_ladder 记录一致）⇒ r_tube = sqrt(2·ΔE/λ_min) = **0.07597**（ΔE =
  E*−certified = 4.1535e-4；口径：R²⁷ 弦距离、模 SO(3)）。严格版（区间算术
  deflation：区间 GS 补基 N + 15×15 区间 LDLᵀ，K=128 子箱）μ₀ = 0.138365 ⇒
  ≤ 0.07748；与 `full_local_min.py` 的 0.14378982（含临界性，链上取强）双实现
  一致 ⇒ 链级严格半径 **0.07601**。管内 λ_min 随机方向扫描（数值证据）：
  r=0.02/0.04/0.076 → 0.110/0.087/0.034。
- **typed 谱管重诊断（核心结论）**：ε_forcing = 4.1531e-4（每类 λ_cls ≤
  E*−e_dy+Σcounts·R1，typed 放大 ×1/类）；三轨道 ρ_spec 阶梯 = 0.0466/0.1043/
  0.2548/0.6447（ε=1.5e-8/1e-7/5.3e-6~1e-4/≥3e-4）vs 需求 0.01851——ε_forcing
  平台差 34.8×，TTP 自身 slack 水平差 13.8×，零集地板（伪近零
  (0.1961,0.1961,0.1961)）仍差 2.5×。**结构性判定：瓶颈在 slack 零集几何，
  不在薄层厚度——a₀=−0.7476 追加解与 ε_forcing 同在 0.6447 平台，ρ_spec 零
  变化，不动用**。typed 贴界 ≠ 零集局部化（同口径 ρ_spec(2e-5) 反从 untyped
  0.0755 恶化到 0.2548，定性对比）。
- **引理链 L0–L7 与三路线**（tube.json lemma_design/routes）：L3 是断点；下一轮
  首选 = 路线 b tube certificate（两点 minorant 6 节点管外分段 + 三点域乘子加
  (t−ν_k)²−ρ² 因子，复用 typed_ladder 管线）。
- 自检：扫描求值器 vs 精确 Fraction eval3（1e-12）、恒等式部分核对
  Σ84λ(TTP)=1.096e-4 ≤ E*−e_dy、区间/数值 B 对拍（2.2e-15，开发中抓出赤道
  sin/cos 表两处错误）、μ₀<λ_num 卫语句（抓出 Cholesky/LDLᵀ 混写）、worst
  点回代 λ ≤ ε。扫描为逐三元组松弛（84 类联合 + Gram 秩 3 一致性未利用）。

## typed/ —— 通用分型三点构造原型（2026-10-03 夜，typed 原型轮次）

`typed/` 包把 N=7 论文 §6 的 typed 三点界推广为**任意类型划分**的原型实现
（cut/band 两模式、(M,K,d_H) 阶梯、N∈{2,3,4,6,12} 紧合自检表全过、N=7 cap+
五 slab 校准全过）。与 `slab_band.py`（(2,7) 分带专门实现，下节）互为独立交叉
验证（N=7 同档相差 +5.2e-5，超集方向一致）。详见 `typed/README.md`。
N=9 原型阶梯：small(6,6) e_safe=25.752634258；mid(7,6) raw e=25.758110647
（已高于 untyped (8,6) 同区域 e_safe 25.757893）；d_H=16 构建成功但本机 OOM
（如实记录于 `results/typed_prototype_n9.json` 的 attempts_unfinished）。

## slab_band.py —— slab 带 [−1,−0.9] 的 typed 三点逐片严格证书（2026-10-03）

GAP-REPORT ②/③-5 的落地：把 N=7 证明 Case 2 的 **typed 三点界**
（`references/thomson-n7-lean/paper/PAPER.md` §6–7.1）移植到 N=9 并严格化。
极点＝最小内积对 (0,1)＋其余 7 环顶点分型；对类 A/B/C（1/14/21 对）、
三点类 PPR/PRR/RRR（7/42/35 个），share 分母 7/6/5，计数条件
`7c_α+42c_β+35c_γ = e + 2s_P(1,1,1) + 7s_R(1,1,1)`；λ_A 域带**上切口** u ≤ hi
（N7 §6.4 的 6/5/5 SOS 块布局：1/u−lo/v−lo/t−lo/hi−u(仅 A)/detG）——TTP
（m\*=−0.7476）被排除在一切 slab 域外，这正是每片能拿到 **certified > E\*** 正裕度
的机制（主战场切口含 TTP，SDP 界恒 ≤ E\*）。

### 正确性基建（先于一切出界）

- **精确组合恒等式自检**（纯 Fraction，随机有理构型 × 随机数据 ==
  0）：`Σ_{i<j}H_cls − e == Σ_T λ_T + Σ_all`，连同 λ 装配一致性、typed 引理 4.1
  逐根正性（`--selftest`）。开发中该自检抓出过 3 个装配 bug（Q_k 递推 (1−u²)(1−v²)
  的符号、c_γ 计数条件 F_P 侧系数缺 ×2、cvxpy 对标量表达式的全向量广播）。
- **N=7 校准**（`--calib7`）：同代码 n=7、(M,K)=(6,6)、slab [−0.99,−0.98]，
  e = 14.453835 = E(P)+8.58e-4——高于 N7 论文 slab-1 证书值（E(P)+2.5858e-6，
  N7 对五片共用一个保守 e），且其证书是本松弛可行点 ⇒ 方向性判据
  e ≥ N7 值−1e-6 PASS。typed 移植对已验证机制校准。
- TypedCore 对 `sdp_bound.build_Q` 逐系数断言一致（核递推双主本互检）。

### 结果（medium=(7,6)，Clarabel，种子 20261004，5 片全链 ~11 分钟，盖满 [−1,−0.90]）

| slab | e（SDP） | **certified（精确）** | **正裕度 over E\*** | 折减 | 粒度 |
|---|---|---|---|---|---|
| [−1, −99/100] | 25.820060 | **25.815880516105** | **+5.589e-2** | 4.1e-3 | 2⁻⁴⁰ |
| [−99/100, −97/100] | 25.805396 | **25.802848154299** | **+4.286e-2** | 2.5e-3 | 2⁻⁴⁰ |
| [−97/100, −19/20] | 25.793234 | **25.789693014930** | **+2.971e-2** | 3.3e-3 | 2⁻⁴⁰ |
| [−19/20, −91/100]（宽 0.04） | 25.774429 | **25.771122805988** | **+1.114e-2** | 3.3e-3 | 2⁻⁴⁰ |
| [−91/100, −9/10] | 25.771363 | **25.769683493481** | **+9.697e-3** | 1.7e-3 | 2⁻⁴⁰ |

每片断言 certified > E\*（正裕度）且 ≤ 数值 e+1e-9，违反即 sys.exit(1)；全 42 个
PSD 块经 `exact.py` 无主元 LDLᵀ 精确正定；回读 decode→重建→重算 certified 逐位
一致；**进程外独立复核**（fresh 进程、系统 python3 无求解器、只读 JSON）五片全过：
`python3 numerics/bounds/slab_band.py --verify-cert certificates/n9-stage-a2-slab-*.json`。
证书 `certificates/n9-stage-a2-slab-{sm1_m99o100,sm99o100_m97o100,sm97o100_m19o20,
sm19o20_m91o100,sm91o100_m9o10}.json`（thomson_certs/schema.py 格式，全 'p/q'）；
解数据与汇总 `results/slab_sol_*_medium.json`、`results/slab_band.json`。

**含义**：slab 带各片 certified > E\*（25.770–25.816 > 25.75999），即最小内积
m ∈ [−1,−0.90] 的**任何** 9 点构型能量 > E\*——带内竞争者全部排除（严格、精确
有理数证书）。与 Round 1 SDP 证书（m ≥ −9/10，certified 25.752411）拼合，
全空间无遗漏；全局严格纪录仍为 LP 25.729491（唯一覆盖全部构型的单一界）。
主战场（m ≥ −0.90 内部逼近 E\*）是 cap 线的事（cap_ladder.py）。

### Feasibility 外推（solve-only 探针，`results/slab_band.json` 的 feasibility_probe）

- **到 −0.90 无瓶颈**：裕度 +0.010~+0.056，全部 ≫ 折减（~3e-3，求解器残差主导，
  非舍入）。求解 ~70s/片（medium）＋认证 ~10s/片。
- **宽片不损**：[−0.95,−0.91]（0.04 宽）e = 25.774429，与两片 0.02 分切
  （25.782746/25.774774）几乎无差 ⇒ 片数可压；盖 [−1,−0.90] 实际用 5 片
  （外推假设的 9–13 片过悲观，N=7 片宽不可比——N=9 带内能量地形更平）。
- **裕度在 −0.85 附近枯竭**：[−0.90,−0.87] +4.1e-3（勉强 1.4× 折减），
  [−0.87,−0.83] +2.0e-4 < 折减，[−0.83,−0.79] e 已低于 E\*（−1.2e-3）——
  (7,6) typed 松弛在 m ≳ −0.85 有紧度地板（对照 cap 线 untyped (8,6) 的
  E\*−5.5e-4 地板）。若需要把 a₀ 抬离 −0.90（如 cap 线 endgame 要求
  [−1, −0.755]），必须先上 midlarge typed / d_H=16 或把折减压到 1e-4 级。
- **cap 线衔接**：cap_ladder 的 endgame 证书在 [−0.755, 1] 内部工作、Round 1
  证书盖 [−0.90, 1]，故 a₀ = −0.90 的分界**无需**移动即可无缝拼接
  （[−1,−0.90] slabs ∪ [−0.90,1] Round-1/cap）；仅当未来用 typed 重做主切口
  时，slab 责任区才扩到 [−1, −0.755]，届时瓶颈是上述 −0.85 地板而非工程量。

### 认证链（对齐 sdp_certify.py 的"舍入＋精确残差折减"）

dyadic 舍入（h/ψ/c 最近、e 向下）→ PSD 修复（+δI，LDLᵀ 验证）→ c_γ 精确重算 →
纯 Fraction 逐单项式残差：`certified = (e − (7·R1_A+42·R1_B+35·R1_Γ))/(1+R2_max)`，
R2 权重 ŵ=√((1−lo)/2) 的有理上界（完全平方时取精确值——lo=−1 时曾因无条件 +1
得 ŵ=2，残差被 2^j 放大）。逐点抽查直接在**有理 (u,v,t) 域条件**（detG ≥ 0＋切口）
上采样（不要求可实现性；曾用随机球面点采样，窄窗 [−0.97,−0.95] 60 次取不到点）。

### 复现

```
cd thomson-n9
numerics/.venv/bin/python numerics/bounds/slab_band.py --selftest   # 精确自检（无需 cvxpy）
numerics/.venv/bin/python numerics/bounds/slab_band.py --calib7     # N=7 校准 ~40s
numerics/.venv/bin/python numerics/bounds/slab_band.py              # 3 片默认全流程 ~7min
numerics/.venv/bin/python numerics/bounds/slab_band.py --slabs="-95/100:-93/100"  # 追加片
python3 numerics/bounds/slab_band.py --verify-cert <cert.json>      # 进程外独立复核
```

### 局限与下一步

- 已盖满 [−1,−0.90]（5 片）；越过 −0.85 受 (7,6) 紧度地板限制（见上节外推）。
- 结构定理（组合恒等式 §6.3、引理 4.1）是分析事实，机器侧由精确随机实例自检覆盖，
  未过 Lean 内核；Lean 化需 N7 的 `TCert`/`SlabSpec` 同型数据装配。
- medium 解多为 optimal_inaccurate（e 对容差不敏感、跨容差逐位复现）；折减公式
  按最坏情形吸收残差，故 certified 距 e 有 ~3e-3 损失——换更净求解器可再压。

## cap_ladder.py —— near-sharp cap 阶梯、残余量化与收尾设计（2026-10-03）

GAP-REPORT ③-3 的落地。五个子命令（单命令 ≤10 分钟），全部结果合并进
`results/cap_ladder.json`：

```
numerics/.venv/bin/python numerics/bounds/cap_ladder.py --solve m0755   # 一档阶梯 ~4min
numerics/.venv/bin/python numerics/bounds/cap_ladder.py --finalize      # 断言汇总
numerics/.venv/bin/python numerics/bounds/cap_ladder.py --residual      # 管状扫描+Hessian ~15s
numerics/.venv/bin/python numerics/bounds/cap_ladder.py --certify m0755 # 精确认证 ~1min
numerics/.venv/bin/python numerics/bounds/cap_ladder.py --design        # 装订 endgameDesign
```

### 阶梯（midlarge=(8,6)，种子 20261003，B(a₀) := 诚实折减界 e_safe）

| a₀ | e_raw | B=e_safe | E\*−B | Δ折减 | E\*−raw |
|---|---|---|---|---|---|
| −0.90 | 25.759381942 | 25.752724581 | 7.262e−3 | 6.66e−3 | 6.05e−4 |
| −0.85 | 25.759350777 | 25.757723656 | 2.263e−3 | 1.63e−3 | 6.36e−4 |
| −0.80 | 25.759393673 | 25.743876268 | 1.611e−2 | 1.55e−2 | 5.93e−4 |
| −0.77 | 25.759411438 | 25.757498235 | 2.488e−3 | 1.91e−3 | 5.75e−4 |
| **−0.755** | **25.759437458** | **25.757892542** | **2.094e−3** | 1.55e−3 | **5.49e−4** |

全档断言 `0 < B(a₀) ≤ E*+1e-6` PASS；m090 复跑与 Round 1 存档 e 逐位一致。
**结构发现（本轮核心量化结论）**：a₀ 从 −0.90 抬到 −0.755（距 m\*=−0.74756 仅
0.0076），原始间隙只从 6.05e−4 降到 5.49e−4——**(8,6) untyped 松弛在此已到紧度地板**，
阶梯不收敛到 E\*（N=7 的 cap 是在候选处精确取等 E(P)−2.3e−16，没有地板问题）。
e_safe 的档间波动（−0.80 档 1.55e−2）是求解器精度波动（GAP-REPORT ③-1），非松弛差异。

### 精确证书（--certify，cap 侧区域严格界，非全局）

m0755/m077/m085 三档经 sdp_certify 同一机器（dyadic 2⁻⁴⁸ 舍入＋PSD 修复＋纯
Fraction 残差折减＋exact.py LDLᵀ；切口 a 以精确有理数入证书，如 −151/200）：

| 档 | certified | 覆盖 | E\*−cert |
|---|---|---|---|
| **m0755** | **25.757085350767** | min 内积 ≥ −151/200 | 2.901e−3 |
| m085 | 25.756978334761 | min 内积 ≥ −17/20 | 3.008e−3 |
| m077 | 25.756944732286 | min 内积 ≥ −77/100 | 3.042e−3 |

m0755 证书：18 个 PSD 块全部一次通过 LDLᵀ、回读重建重算逐位一致；进程外独立复核
（fresh 进程只读 JSON＋exact.py）通过；超过 Round 1 严格纪录（LP 25.729490962）
0.027594、超 Round 1 SDP 证书（25.752410818，仅覆盖 min 内积 ≥ −9/10）0.002675。
**全局严格纪录不变**（LP 证书仍是唯一覆盖全部构型的严格界）。

### 残余量化（--residual；全部为数值证据，标注入 JSON）

- **管宽**：谱管需求 ρ_spec ≤ 0.0185（TTP 谱最小间隙 0.03701 之半）。实测 m0755
  slack 多项式的 ε-水平集离 TTP 三点组的距离：ρ_spec(2e−5)=0.0755、ρ_spec(2e−2)=0.33
  （均匀网格 n=256，h=6.9e−3）；ε=2e−5 水平集占 Gram 域 0.94% 体积。
- **强制公式（推导严格、输入数值）**：E ≤ E_band 的构型**每个** Gram 三点满足
  slack ≤ 14(E_band+36w−e)+psdF/2+503·r1（各项 ≥ 0 ⇒ 单项 ≤ 全和，**×504 型放大**；
  N=7 收尾靠精确取等把全和压到 0 才消掉）。当前 ε(E≤E\*)=2.9e−2，零噪声极限地板
  14(E\*−e)=7.7e−3 ⇒ 对应管宽 ~0.25。**结论：管状收尾在 (8,6) untyped 上对任意求解
  精度不成立——是结构问题不是精度问题**；需要 typed / d_H=16 / 精确取等型证书。
- **两点管**：LP 精确证书的 g=φ−f̂ ≤ E\*−B_LP=0.0305（36 项、无放大、证书精确），
  但 {g ≤ 0.0305} 是测度 1.32/3.99 的单区间——两点信息穷尽（与 KLT 对 N=8 的
  结论一致）；g 在 TTP 三个最低节点处 1.9e−7/9.5e−6/4.2e−6（近切）。
- **Hessian**：TTP 处 18 维切空间 Riemann Hessian λ₊=0.143935、恰 3 零模（旋转）、
  FD 交叉复核 2.8e−5、切向梯度 2.4e−9；采样二阶增长半径 ≥3.0 ⇒（数值）
  E ≤ E\*+δ（δ=2.09e−3）⇒ 测地距离 ≤ sqrt(4δ/λ₊)=0.241。

### 收尾设计（endgameDesign，JSON 内全量）

八个组件逐项标注状态：cap 精确界（**本轮已严格**）/ 管宽需求（数值证据：差 ~14 倍，
结构性不足）/ 强制机制（公式严格+输入数值）/ Hessian 距离界（数值证据）/ 组合刚性
（未开始）/ 全空间严格局部极小（未开始，数值已有）/ slab 带（另一条线，未开始）/
拼接（未开始）。下一轮优先级：typed 三点证书原型（管状收尾的先决条件）→
large=(9,6) 对称性约化 → 全空间区间 Hessian。


## verify_certificate.py —— LP 界的数值→精确桥接（dyadic 舍入 + 独立精确复核）

`verify_certificate.py`（→ `certificates/n9-stage-a.json`，仓库根目录）把 `results/lp.json`
的 LP 界构造成**全 dyadic 精确有理数证书**，不信任 lp.json 的任何 checks 标志：

1. **舍入（安全方向）**：41 个 Legendre 系数全部向下取整到 2⁻⁶⁴ 网格（实测仅 ĉ₀
   因 η 平移非 dyadic，损失 δ₀=5.75e−21；k≥1 系数 lp_bound 已舍为 dyadic，不变）；
2. **精确重认证**：在舍入后的系数上**重跑** `lp_bound.certify` 的纯 Fraction 分支定界
   Taylor 扫描（138292 叶全过，sup(f−φ) ≤ 0 精确成立，无需二次平移）；另用
   `math.isqrt` 的 φ 下界在 7 个有理点独立抽查 f ≤ φ（不经扫描机制）；
3. **exact.py 复核**（`thomson-workflow/certificates/thomson_certs`，纯标准库）：
   9 个有理测试点上核 Gram 阵 `K_f_test=[f(xᵢ·xⱼ)]` 经无主元 LDLᵀ 判**严格正定**
   （加法定理 PSD 机制的实例复核，普遍命题是分析定理）；界值纯 Fractions 双路重算
   逐位一致；
4. **证书**：按 `schema.py` 格式落盘（系数=41×41 对角块 + K_f_test 9×9 块 +
   claimed_bound），回读 decode + 再编码逐字节一致；下游仅凭 JSON 即可独立复核
   （对角块读回系数重算 B、K 块重跑 LDLᵀ，已验证逐位一致）。

结果（2026-10-03，确定性，77s）：**精确下界 B = 949250669852870679987/2³⁵⁺ …
= 25.729490962195**（float 显示），舍入损失 = 数值界 lp_raw − B =
**1.3095e−6**（精确有理数入 provenance）。断言 0 < B ≤ lp_raw 且
0 < B ≤ E* + 1e-6 全过（E* − B = 0.030496），违反即 `sys.exit(1)`。

```
cd thomson-n9
numerics/.venv/bin/python numerics/bounds/verify_certificate.py   # ~80s
```

## sdp_certify.py —— SDP 界的数值→精确桥接（dyadic 舍入＋精确残差折减，2026-10-03）

`sdp_certify.py`（→ `certificates/n9-stage-a2-sdp.json`，1.9MB）把上面的 SDP
数值主界（midlarge=(8,6) × m=−0.90）严格化为**精确 dyadic 有理数证书**，闭环
GAP-REPORT ③-6 的四缺步：(a) 解数据落盘（确定性复跑与 `results/sdp.json` 存档
e 逐位一致；`results/sdp_solution_midlarge_m090.json`）；(b) dyadic 舍入
（2⁻⁴⁸）＋ PSD 修复（18 块 +δI 最小充分平移，`exact.py` 无主元 LDLᵀ 全部
严格正定，一次通过）；(c) 两条多项式恒等式的**精确残差**（纯 Fraction）：
R1 = ‖slack 恒等式残差‖₁ = 1.813e-4，R2 = minorant 残差加权 ℓ₁ = 1.726e-5；
(d) minorant 逐点条件经 σ 块 PSD＋R2 折推精确成立（Lukács 表示）。

**精确下界 certified = (e − 36·R1)/(1+R2) = 25.752410818467**
（精确值 `579902747221865232/22518386775890053`；对一切 min 内积 ≥ −9/10 的
9 点构型成立）。断言全过：> LP 严格纪录 25.729490962195（超出 0.022920）、
≤ E*+1e-6（E* − certified = 0.0075757）；**舍入损失 e_safe − certified =
3.138e-4**（精确有理数入 provenance）。装配镜像（a=−9/10 精确）与浮点版结构
全等（系数差 ≤5.7e-14）；精确自检：三点恒等式随机有理实例 ==0（3 次）、引理
4.1 正性 ≥0（3 次）；SOS/残差/minorant 有理点抽查全过；回读重算逐位一致；
进程外独立复核（只读 JSON：19 块 LDLᵀ PD ＋ 界值重算相等）通过。
*范围限定（如实）*：只覆盖 min 内积 ≥ −9/10；[−1,−0.9) slab 带未开始；结构
定理（三点恒等式、引理 4.1）引用 PAPER.md §4–5.1，机器侧为随机有理点精确
实例验证。

```
cd thomson-n9
numerics/.venv/bin/python numerics/bounds/sdp_certify.py              # 复跑求解+认证 ~5 分钟
numerics/.venv/bin/python numerics/bounds/sdp_certify.py --solution \
  numerics/bounds/results/sdp_solution_midlarge_m090.json             # 复用解数据 ~40s
```

## construction_selftest.py —— BV/CW 三点构造的普适最优紧合自检（2026-10-03）

Round 1 的构造正确性只有 N=7 校准间接覆盖（参照值本身非 SDP 最优）。本表换成
数学上紧合的参照——N∈{2,3,4,6,12} 普适最优构型（两点 LP 界可证紧合 ⊆ 三点
SDP），e 应恰等于真值；e 超出真值 +5e-6 即构造/实现的硬错误（FAIL）。
**N∈{3,4,6,12} 全部紧合**（small=(6,4) 一档即过，超真值 2.0e-8/3.8e-8/
2.3e-7/1.3e-6，均在阈内）；N=2 理论退化（n−2=0 ⇒ 三点恒等式两边恒零，实测
除零报错如预期），不计入通过判定（其紧合性由 lp_bound 两点表覆盖）。
结果 `results/selftest.json`；全过 exit 0（本轮实测 13.3s PASS）。

```
cd thomson-n9
numerics/.venv/bin/python numerics/bounds/construction_selftest.py
```

## sdp_bound.py —— 三点 SDP 界（Bachoc–Vallentin / Cohn–Woo，按最小内积 m 参数化）

`sdp_bound.py`（→ `results/sdp.json`）把 N=7 证明（`references/thomson-n7-lean`，
PAPER.md §4–5.1；KLT arXiv:2609.22077 §4.2–4.3 同框架）的三点机器移植到 N=9：
核 `Q_k` 递推、`S_k = Sym(u^a v^b Q_k)`、三点恒等式
`dsum(slack)+(n−2)Σ_all = 2(n−2)(ΣH−e)`（slack 定义见脚本头注），SDP 在
`(h, e, F_k⪰0, SOS Gram 阵⪰0)` 上**最大化 e**，两条多项式恒等式约束：
slack 属 8 块 SOS 模（`1`／cut×3／cap×3／detG，N=7 Case 1 的布局）＋
minorant 的 Lukács 型表示 `1−2yH(1−2y²) = σ₀+yσ₁+(b²−y²)(σ₂+yσ₃)`。
结构参数 `(M,K)`：`F_k` 尺寸 `M−k`、`H` 次数 `2M−2`（N=7 Case 1 是 (6,4)）。

### 结果（2026-10-03，Clarabel，midlarge=(8,6)：61k 变量 / 210s）

| 切口 m | SDP 原始值 e | 折减 Δ | **诚实下界 e_safe** | E* − e_safe |
|---|---|---|---|---|
| −0.90（主） | 25.759381942 | 6.66e−3 | **25.752724581** | 0.007262 |
| −0.95 | 25.759371847 | 9.29e−3 | 25.750080212 | 0.009906 |
| −0.90（small=(6,4)，干净解） | 25.748363122 | 1.96e−4 | 25.748167130 | 0.011819 |

对照两点 LP 界 25.729491（差 0.030496）：三点界把差距缩到 **0.0073**。原始值距 E*
只差 6.0e−4——松弛本身接近紧合（TTP 在两切口内，`ΣH(TTP)=25.759965 ≥ e`，逐项复核
见 `results/sdp.json` 的 `ttp_check`）。诚实下界受限于求解器残差，由**量化折减**给出：
`e_safe = e − Δ`，`Δ = 36·sup(H−φ) + 504·(‖slack 恒等式残差‖₁ + SOS 块 PSD 亏损)/14
+ F 块 PSD 亏损/14`（各项实测入 JSON；sup 含 H'' 插值余量）。这是数值下界，
非严格证书——严格化需 N7 式有理舍入（2¹⁶⁰ 分母整数恒等式）或 KLT 式区间验证，未做。

**求解器敏感性注记（2026-10-03 复算审计）**：small=(6,4) 的原始值对求解器容差敏感
——紧容差（tol 1e-12）重跑得 e = 25.748421634904446（+5.9e-05，状态
optimal_inaccurate，identity_l1 9.7e-06、minorant violation +2.6e-07），折减后
e_safe = 25.74759151137102（accepted=False）；默认容差（1e-8）逐位复现上表值。
即 small 配置的 e/e_safe 有 ~1e-4 量级的求解器依赖，只作交叉参考；**主界来自
midlarge（默认与紧容差均逐位复现），不受影响**。`results/sdp.json` 为单次默认全量
运行的忠实记录（校准 + m=−0.90/−0.95 各 midlarge+small），每条 case 带 `run`
溯源块（timestamp/argv/solver_opts/repro）；旧版"合并保留"逻辑遗留的 (m=−0.90,
medium) 条目已在 2026-10-03 再生时移除（历史见 git）。

### 自检与校准（脚本每次运行先跑，不过则 exit(1)）

- **核恒等式** `Q_k = Re(ζ^k ζ̄^k)`（引理 4.1 的核心）：随机 Gram 三点上 max err 1.9e−15；
- **正性**（引理 4.1）：随机构型 × 随机 PSD F ⇒ `Σ_{i,j,l}⟨F,S_k⟩ ≥ 0`（实测 +1e4）；
- **三点恒等式**：随机 (h,F) ⇒ 等式两端相对误差 ≤ 3e−13（验证 R_s/slack 装配）；
- **N=7 校准**：同代码 a=−0.9、(M,K)=(6,4) 解出 e = 14.454504，与 N7 论文 Case 1
  证书值 E(P)+3.2259e−4 = 14.453300 差 1.2e−3（≥ 证书值，因论文证书是该 SDP 的
  可行点，SDP 最优可更高），容差 5e−3 内通过。

### 复现

```
cd thomson-n9
numerics/.venv/bin/python numerics/bounds/sdp_bound.py --only selftest   # 自检 ~1 分钟
numerics/.venv/bin/python numerics/bounds/sdp_bound.py --only calib      # N=7 校准 ~10s
numerics/.venv/bin/python numerics/bounds/sdp_bound.py --only m090 --config midlarge  # ~4 分钟
numerics/.venv/bin/python numerics/bounds/sdp_bound.py                   # 全流水线
```

依赖：`numpy`/`scipy`/`cvxpy`+`clarabel`（装在 `numerics/.venv`，venv 自带 gitignore
不入库；SCS 兜底）。种子 20261003 固定；求解器参数固定于脚本 CFG。

### 局限与下一步

- `large=(9,6)`（d_H=16，TTP 6 节点 Hermite 的自然次数，123k 变量、165 阶 PSD 块）
  在 cvxpy+Clarabel 下内存 15GB、30 分钟未收敛——**未产出结果**，是 e_safe 与原始值
  之间差距的主因之一；
- midlarge/medium 解状态 `optimal_inaccurate`（PSD 亏损 ~1e-7、恒等式残差 ~3e-6）：
  折减公式按最坏情形放大（L1 范数、‖z‖²≤m_r），Δ 偏保守；Bernstein 系数或
  PSD 平移＋重拟合可再压 ~2×，未做；
- ~~严格化路线（阶段二）~~ **已落地**（2026-10-03）：`sdp_certify.py` 的 dyadic
  舍入＋精确残差折减产出精确证书 25.752410818（见上节），剩余严格化工作只在
  换更强配置/更净求解器时重跑同一脚本；slab 分裂（m < −0.95）与 typed 证书未开始。

## local_min.py —— triCapPrism 族内严格局部极小的区间验证（2026-10-02）

`local_min.py`（→ `results/local_min.json`）用 mpmath 区间算术（`iv`，dps=40）验证
族最优的局部性质：闭式 E(z) 以二阶前向自动微分求 E′/E″（无手推公式），二分 E′ 严格
变号把 z* 隔离到 **[0.703648376463, 0.703649139406]**（宽 7.6e-7 ≤ 1e-4，端点
|E′| ≥ 8.3e-7 / 3.2e-5），隔离区间上 **E″ ∈ [42.8589, 42.8593] > 0** ⇒ 唯一驻点且
E′ 由负变正 ⇒ 族内严格局部极小。交叉复核：闭式 vs 构型 36 对直接求和（区间相交）、
MVT 一阶差商落在端点 E′ enclosure 之间、二阶均差落在 E″/2 enclosure 内；
E(隔离区间) 含 energies.json 的 E* = 25.759986531270。`--selftest` 负对照
（错误区间 [0.5,0.6] 的变号断言、篡改 E* 的能量断言）都按预期触发才 exit 0。
注意：这只证**族内**局部极小，不是全局最优性证明（那是 LP/SDP 界的任务）。

## full_local_min.py —— TTP 全空间（模 SO(3)）严格局部极小的区间验证（2026-10-04）

`full_local_min.py`（→ `results/full_local_min.json`，`--selftest` 加负对照）补上
`local_min.py`（族内一维）之后的必要件：**X(z\*) 在 (S²)⁹ 全流形上是临界点，其
Riemannian Hessian 在 15 维商切空间（18 维切空间 = 27 坐标 − 9 球约束，模 3 维
SO(3) 轨道方向）严格正定**，核恰为旋转轨道方向 ⇒ 模 SO(3) 非退化严格局部极小。
引理链 L1–L8（精确数学与区间证书分工，见脚本 docstring）：

- **临界性（L1–L3）**：D3h 固定环境子空间 F_amb∩T = span{v_fam}（显式基
  f1/f2/f3，v_fam = −(z/ρ)f1 + f2 逐点验证），∇E 与 D3h 交换 ⇒ 切向梯度
  ∝ v_fam，而 ∇E·v_fam = E′(z\*) = 0（R1 隔离区间复用并重推导）。
- **Riemannian Hessian（L4）**：q_z(v,v) = vᵀH_amb v − Σ_i(∇_iE·x_i)‖v_i‖²
  （单位球测地线加速度 = 第二基本形式修正；临界点处即流形 Hessian）。
- **旋转核（L5/L6）**：q(w,w)=0 与交叉项 = 0 是临界点处 SO(3) 不变性的精确
  恒等式；区间复核 |C_RᵀQ_redC_R|、|Q_redC_R| ~ 1e-6（∝|E′|，随 z→z\* 收敛 0）。
- **区间证书（L7）**：逐点正交切基 {e_θ, e_m}（Gram 精确对角 diag(1, 1/ρ²)），
  36 对逐项装配 Q_red（不走 27×27 三明治）；z_mid 处带列主元区间 Gram–Schmidt
  构造 15 维商子空间 A₀，[A₀|C_R] 的 G-Gram 整区间 Cholesky ≻0 ⇒ T = S_A⊕R；
  **中值形式** M(z) ⊆ M(z_mid) + [A₀ᵀQ′(I)A₀](z−z_mid)（Q′ 由对偶区间自动微分
  给出，vs 中心差分自检）＋**预条件同余**（中点具体 Cholesky 白化后区间
  Cholesky 条件数 ~1），入口宽度 ~1e-5 时认证损失仅 ~1e-4。
- **结论（L8）**：q(u) ≥ λ·dist(u, R)²，**λ_min(商) ≥ 0.14378982**（advisory
  float64 数值 0.1439338，GAP-REPORT Round 2 参考 0.143935；管状线 tubeRadius
  的输入——λ 转管半径还需 Taylor 三阶余项界，下游处理）。

交叉复核：∇E·v_fam 与 E′(I) 区间相交、q(v_fam,v_fam) 与 E″(I) 相交（共同值
E″(z\*)≈42.859，E″ 来自 local_min.py 独立闭式——Hessian 公式与族计算互相锚定）、
E(z\*) vs energies.json E\*（≤1e-8）、对偶 AD vs 中心差分（1e-4 相对容差）。
`--selftest` 负对照（都按预期触发才 exit 0）：(i) 退化 z∈[0.45,0.45001]（对称
破缺方向 λ_min ≈ −1.06）跑同一认证路径（ladder=[0]）必须报 not positive
definite；(ii) 篡改平移 M−0.4Ĝ 必须被 Cholesky 检出。开发中被这些检查抓出过
4 个实现 bug（v_fam 分解式、交叉点符号翻转、帽点 e_m 范数 1/ρ²、上三角逆的
列标范围）——负对照与交叉复核不是摆设。

## 结果（2026-10-02 首次运行，默认参数全量跑，155s）

| 量 | 值 |
|---|---|
| 认证下界 **B** | **25.729490962**（精确有理值见 `results/lp.json` 的 `bound_exact`） |
| LP 原始值（认证前） | 25.729492272 |
| sup(f−φ) 认证上界 M | 3.64e-8（平移 η = M + 2⁻⁴⁶） |
| 目标能量 E*（TTP，D3h） | 25.759986531（`thomson-workflow/data/energies.json`，三源校验 confirmed） |
| **差距 E* − B** | **0.030495569** |

脚本内部断言 `0 < B ≤ E* + 1e-6`（违反即 `sys.exit(1)`）；本次运行通过。
落盘后另做了独立复算：从 `lp.json` 存的 41 个有理系数重算 `(81c₀−9f̂(1))/2`
与 `bound_exact` 逐位一致；200 万随机点抽查 `max(f̂−φ) = −3.63e-8 ≤ 0`。

## 方法：Yudin / Delsarte 两点线性规划界

**对偶形式（证书多项式，即"插值多项式 minorant"）**。以 `t = x·y ∈ [−1,1]` 为变量，
对势 `φ(t) = (2−2t)^{−1/2}`。取 d=40 次多项式

```
f(t) = Σ_{k=0}^{40} c_k P_k(t)        （P_k = Legendre 多项式）
```

满足两点：

1. `c_k ≥ 0` 对一切 `k ≥ 1`（P_k 是 S² 上的正定核：加法定理
   `Σ_{i,j} P_k(x_i·x_j) = (4π/(2k+1)) Σ_m |Σ_i Y_km(x_i)|² ≥ 0`）；
2. `f(t) ≤ φ(t)` 对一切 `t ∈ [−1,1)`。

则对**任意** 9 点构型：

```
E = Σ_{i<j} φ(x_i·x_j) ≥ Σ_{i<j} f(x_i·x_j)
  = ½(Σ_{i,j} f(x_i·x_j) − 9·f(1))
  ≥ (81·c_0 − 9·f(1)) / 2 ,
```

第二个不等号正是用条件 1 的逐 k 非负性。LP 在 60000 个格点上离散条件 2，
**最大化**该下界（`scipy.optimize.linprog`，HiGHS，primal feasibility tolerance 1e-10）。
LP 最优解 f 在 ~5 个内积值处与 φ 相切（等化），这正是"插值多项式"的含义——
与 KLT（arXiv:2609.22077）§4.1 用 13 条 Hermite 条件构造 minorant 的思想同源，
区别在于 KLT 的 Hermite minorant 的 Legendre 系数不全非负、须配三点 SDP（其 §4.2），
而这里直接把非负系数作为 LP 约束，两点机器即可闭环。

**出处与移植说明**：
- 方法属 Yudin（Discrete Math. Appl. 1992）/ Cohn–Kumar 能量 LP 界一脉；
  KLT 论文引言与参考文献 [16] 即 Yudin 该文。KLT §1.2 明言两点界只用成对信息、
  他们改用三点法，故 KLT 与 N7（`references/thomson-n7-lean`）的数值代码中
  **均无现成两点 LP 可移植**（N7 的 `paper/numerics/paper_numerics.py` 只含
  高精度能量、Gram 值、Hessian 特征值计算，无 LP/对偶构造）。本模块为按上述
  文献自实现，实现中对 N∈{2,3,4,6,12} 做了紧合校准（见下）。
- 数学上：对 N ∈ {2,3,4,6,12}（球面上普适最优构型）两点 LP 界应当**紧合**，
  本实现复现了这一点（见自检表），这是公式正确性的最强外部校验。

## 严格化流水线（LP 只找候选，证书不信任浮点）

1. **有理化**：LP 的 Legendre 系数向下舍入到分母 `2^64` 的有理数
   （`k≥1` 的系数由此保持非负；若求解器容差导致微小负值则钳 0）。
2. **精确幂基**：Legendre→幂基系数全用 `Fraction` 精确递推；与
   `numpy.polynomial.legendre.legval` 在 7 个有理点比对（回归自检，防基变换错位）。
3. **认证 `f ≤ φ`**：分支定界扫过 `[−1, 1−2⁻⁴⁰]`，每叶对 `g = f − φ` 用
   **中点 Taylor 展开（全精确有理算术）**：
   - `f^{(k)}(m)/k!` 由精确幂基 Horner 求出；
   - `φ^{(k)}/k! = [C(2k,k)/4^k]·(2−2m)^{−1/2−k}`，其中 `(2−2m)^{−1/2}` 的
     精确有理上下界由**整数平方根** `math.isqrt` 给出（无浮点、无区间库）；
   - `k=0` 项保留符号（边距所在），`k≥1` 项取绝对值，截断尾项用
     `|f^{(k)}(m)/k!| ≤ Σ_j |p_j| C(j,k)` 与 `C(2k,k)/4^k ≤ 1` 严格控制；
   - 顶部（`h/(2−2b) > 1/2`，φ 幂级数尾失控处，边距其实巨大）退回
     "f 的 Taylor 上界 ≤ φ 的精确下界"的形式；`(1−2⁻⁴⁰, 1)` 由尾部引理覆盖。
   扫描给出 `sup(f−φ) ≤ M` 的严格上界（本次 M ≈ 3.7e-8）。
4. **平移收口**：取 `η = M + 2⁻⁴⁶`，令 `ĉ_0 = c_0 − η`（c_0 无符号约束，合法性不受影响），
   则 `f̂ = f − η ≤ φ` 于 `[−1,1)` **严格成立**；下界
   `B = (81·ĉ_0 − 9·f̂(1))/2` 用 `Fraction` 精确计算，报告值再向下取 9 位小数。
   认证损失（LP 原始值 − B）≈ 1.3e-6。

证书三要素（系数非负、逐点 minorant、界公式）全部精确可复核；`results/lp.json`
内存有全部精确有理系数、η、M 与参数。扫描规模：25.0 万叶（pass 7.4 万，
触点附近细分到宽限 5.2 万），147s。

## 参数（默认）

- `N=9`，`DEG=40`（探索：15/20/25/30/35/40 → 25.72860/25.72942/25.729426/25.729494/25.729494/25.729494，30 次已收敛，取 40 留裕量）
- `NGRID=60000`（`[−1, 1−1e-9]` 均匀格点），HiGHS `primal_feasibility_tolerance=1e-10`
- 舍入 `ROUND_BITS=64`；扫描首层 2048 叶、最小叶宽 `2⁻²²`、Taylor 精确项 K=6、
  φ 有理界分辨率 `2⁻⁶⁰`、η 余量 `2⁻⁴⁶`
- `SEED=20261002` 固定（流水线本身确定性，种子为防御性固定）

## 自检（紧合校准，`--no-selftest` 可跳过）

| N | LP 值 | 真值 E（构型） | E − LP |
|---|---|---|---|
| 2 | 0.500000000 | 0.5（对径点） | 0 |
| 3 | 1.732050808 | √3（正三角形） | −6e-11 |
| 4 | 3.674234614 | 3√6/2（四面体） | −2e-10 |
| 6 | 9.985281375 | 6√2+3/2（八面体） | −4e-10 |
| 12 | 49.165253062 | 49.165253058（二十面体，精确构造） | −4e-9 |

（负号 = LP 比真值高 e-9~e-10 量级，系格点离散＋求解器容差；判据 ±5e-6 内判 OK。
这些 N 两点界理论上紧合，实现逐位复现。）判据不过则 `sys.exit(1)`。

## 复现

```
cd thomson-n9
python3 numerics/bounds/lp_bound.py            # 完整：LP＋认证＋自检＋落盘 ~3 分钟
python3 numerics/bounds/lp_bound.py --ngrid 20000 --no-selftest   # 更快（结果差 ~1e-9）
```

依赖：`numpy`、`scipy`（本机已有）。结果写 `numerics/bounds/results/lp.json`。

## 局限与下一步

- 两点界对 N=9 差 **0.030496**：两点信息不足以达到 E*（KLT 对 N=8 亦然，差 0.027）。
  收口需要三点 SDP（strategy.md 步骤 3 / KLT §4.2 的 Cohn–Woo 框架）——
  这已超出本模块范围，是 `bounds/` 的下一个成员。
- 本界只覆盖 s=1（库仑）；未做 s>0 一族。
- 认证用的是精确有理算术＋整数平方根；若日后要 Lean 化，证书
  （41 个有理系数 + η + 界公式）可直接进 `thomson_certs` 一类的精确复核管道，
  逐点 minorant 的检查需换成区间/多项式非负分解证书（未做，见 gaps）。

## typed_ladder.py —— typed (3,3,3) cap 阶梯 Round 3（2026-10-04，切口抬到 −0.748）

cap 阶梯从 −0.90 抬向 m\* = −0.7476：**typed 三点构造的 S₃ 商** ＋ SDPA-GMP 高精度
（hp_solve.py 同管线）＋ slab_band.py 式精确认证。(3,3,3) 分型在类型重标群 S₃ 下
不变（SDP 凸 ⟹ 群平均不降 e），商 SDP 只解 2 对类轨道（AA/AB）+ 3 三点轨道
（AAA/AAB/ABC）+ 1 归一化——6 类 + 10 类 + 1 的约束缩到 3+2+1，规模 ≈ untyped
midlarge 的 2×，而构造是 typed 的。全 10 类的展开（λ_full = λ_orbit∘P）在认证链里
**逐系数精确核对**，不依赖商化论证。

### 正确性（开发中真实抓出的 4 个问题，如实记录）

1. SDPA 的 LP（负尺寸对角）块是**非负锥**：以 b=−2 的 1×1 LP 块实测 pUNBD 证实；
   h/ψ 有负系数（slab 证书实测 min −2.99）⟹ 一律 ± 拆分。
2. 归一化行 F0 非对角条目须为 −9（×2 约定下 2·v·X_ab = −18·X_ab），初版写成 −9/2
   ⟹ (6,6) e 跑飞 26.21 > E\*——被「opt ≤ E\*」断言与 Clarabel 全 SDP 交叉验证双重
   抓获（正是这两道闸存在的意义）。
3. (7,6) m090 首解 SDPA-GMP dFEAS 崩溃（iter 34 原始目标跑飞 26.3）：± 拆分的精确
   零空间方向；目标加 −1e-11·Σ± 罚锚定后 78 迭代 pdOPT。读回的 e⁺ 对**原问题**
   精确可行（罚项只改变选哪个最优点），认证零损失。
4. 常规自检链：`--selftest`（perm 方向、typed 恒等式 ==0、轨道展开、分型正性）、
   `--crosscheck -0.9 6 6`（Clarabel 全 typed SDP 独立实现 vs 商 SDPA-GMP：
   25.752570 vs 25.753123，|Δ|=5.5e-4 = Clarabel 欠收敛量级；raw R1 ≤ 1.9e-40）。

### 阶梯结果（(M,K)=(7,6)，SDPA-GMP 200 位，dyadic 2⁻⁴⁸，认证损失 ~6.5e-7）

| a₀ | e（SDPA-GMP） | **certified（精确）** | E\*−certified | vs 区域纪录 25.757085350767 |
|---|---|---|---|---|
| −0.90 | 25.758658488 | **25.758657803413** | 1.329e-3 | +1.572e-3 |
| −0.85 | 25.758662427 | **25.758661738899** | 1.325e-3 | +1.576e-3 |
| −0.80 | 25.758668455 | **25.758667778181** | 1.319e-3 | +1.582e-3 |
| −0.77 | 25.758684976 | **25.758684318167** | 1.302e-3 | +1.599e-3 |
| −0.755 | 25.758742954 | **25.758742286412** | 1.244e-3 | +1.657e-3 |
| **−0.748** | 25.758806421 | **25.758805755024** | **1.181e-3** | **+1.720e-3** |

断言（违反 sys.exit(1)，全部通过）：每档 0 < certified ≤ E\*+1e-6；**−0.748 档
certified > 25.757085350767**（Round 2 区域纪录，其区域 ⊃ 本档区域）——高出
+1.72e-3。切口 −0.748 < m\* = −0.7476，**刚好压过最优构型所在区**。证书
`certificates/n9-stage-a4-typedcap-{m090,m085,m080,m077,m0755,m0748}.json`（全
'p/q'）；进程外独立复核（系统 python3 `--verify-cert`）：38 PSD 块 LDLᵀ＋归一化
残差 = 0＋certified 重算逐位一致，全过。汇总 `results/typed_ladder.json`。

**主目标档的 (8,6) 加档**：m0748 @ (M,K)=(8,6)（pdOPT / 11749s 墙钟 ~3.3h，认证损失 ~8.6e-7）：

| a₀ | e（SDPA-GMP） | **certified（精确）** | E\*−certified | vs 区域纪录 |
|---|---|---|---|---|
| **−0.748** | 25.759572087 | **25.759571185601** | **4.153e-4** | **+2.486e-3** |

**复现性（2026-10-04 复算员分歧处理后）**：全部 8 档已用 HEAD 代码（lp_penalty=
1e-11 导出）全新重解重认证——上表即 HEAD 可复现值（`--rung <a0> --M <M>`；旧值
尾差 M6 −3.68e-9、M7 −1.7e-10~−2.2e-8、M8 −3.0e-8，全部断言在两版值下均成立）。
hp_solve 同日修复：默认 `--k [64]`＝存档粒度（旧默认 [48,56,64] 首个通过 k=48 会
得 25.759445614952，比存档低 3.58e-07），hp.json provenance.reproduce 记录了
逐位复现命令。

**与纪录的关系**：E\* − certified(−0.748, (8,6)) = **4.15e-4——1e-3 stretch 达标**；
1e-4 超预期未达（差 3.2e-4，如实记录）。typed (7,6) 在 a₀ ∈ [−0.90,−0.748] 近平坦
（地板 ~E\*−1.3e-3）；typed (8,6) 地板 E\*−4.15e-4，**优于 untyped (8,6) 的
E\*−5.4e-4**（m≥−0.90 HP 值）——typed 构造在同一 M 下首次超过 untyped。全局拼合
纪录不变（untyped m≥−0.90 HP 25.759446 仍是唯一覆盖 m≥−0.90 的单一证书；本阶梯
6+1 档均为 typed 构造在各自切口上的区域纪录，−0.748 < m\* 压过最优构型区）。

### stripFeasibility（[−0.90,−0.755] 条带覆盖，Round 4 的活；`--strip-study`）

用 slab_band.py（(2,7) 分带 typed，独立实现）Clarabel (7,6) 实测 6 条测试带：
宽 0.02 的带在 hi ≥ −0.84 有正裕度（e_raw − E\* = +6.1e-3 / +2.7e-3 / +0.9e-3 @
hi = −0.88/−0.86/−0.84），hi ≤ −0.80 转负（衰减 ~9e-4 / 0.01 hi）。**关键数据点**：
宽仅 0.005 的 [−0.76,−0.755] 裕度 −1.43e-3 并不比宽 0.02 的好——片宽在 hi ≥ −0.82
已非控制量，是 **(7,6) 松弛地板**（E\*−1.3e-3）在控制：(7,6) 下 [−0.845,−0.755]
任何片宽都拿不到正裕度。M8 档实测 typed (8,6) 地板 = **E\*−4.15e-4**（比 (7,6) 抬
~+9e-4）⟹ 交叉点右移、[−0.90,≈−0.835] 4 片宽 0.02 可盖；[−0.835,−0.755] 需 (8,6)
逐片实测（乐观 5-8 片 0.01-0.02 宽，保守仍被地板卡住须 (9,6)＋分块装配——Round 2
已知 (9,6) 本机 24GB OOM）。合计口径：**乐观 9-12 片（(8,6) 为主），保守 4 片可行
+其余待 (9,6)**；每片一次 SDPA-GMP（(7,6) ~52 min、(8,6) ~3.3 h，15 核并行 4-7 片），
HP 认证（Clarabel 折减 2e-3 在裕度边缘不可忽略）是硬前置——本包 cap 管线可直接换
band 域复用。
