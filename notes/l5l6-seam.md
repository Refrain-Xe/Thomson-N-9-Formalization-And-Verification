# L5→L6 缝量化探针（R20A / r20a-l5l6-seam-probe，2026-10-13）

> 数值面审计件（audit artifact，非证书）：本文件与
> `numerics/bounds/results/r20_l5l6_seam.json`（生成器
> `numerics/bounds/r20_seam_probe.py`，seed 20261020，heavy_solves=0）
> 不入 endgame.json/citedCertificates/12 分区、不成为 endgame_chain.py
> 输入（R11C–R19 先例，D86 裁决 1）。全部输入只读存档；全部算术为
> 确定性 Fraction／定向有理包络（200-bit 整数 Newton，方向性逐点断言）；
> 探针重跑逐位一致（G2 面）。表 B 七件（TableB5Uncond 24 定理）落位后，
> 这是 L5 形式底座的第一次数值消费。

## 0. 缝的形状（一句话）

链 L2→L3→L5→L6 中，L5 供给『内积偏差 δ ⟹ Procrustes 距离 d_P ≤ C·δ』，
L6 需求『d_P ≤ r* 落入认证二次增长球』；缝闭合条件＝**C·δ ≤ r\***。
L3 供给目前最好的 δ（=ρ，簿记同定，见 §3）是 ρ_spec=0.0466（最深 SDP
点）——比闭合所需的 6.38e-4（数值口径）大 **~72.9×**。缝不闭合，
binding=**L3 供给**（slack 零集几何），与 R19 收官终判（closed=false，
blocking=[L0,L3]）一致——本探针把『L3 是阻断』从定性升级为定量缝目标。

## 1. 供给面（三口径分层标注）

| 档 | 常数（本探针定向包络精确重算） | 值 | 域 | 证明层 |
|---|---|---|---|---|
| Lean 路线 B（√δ 档） | C_B := k1·√δmax+√(3·√72Up)，k1 := s1Up·u₁·√72Up/l₃² | **7.127939** | δ ≤ δ_max=0.17124（记录域全体，β≤1/2 内部导出） | formal_lean（TableB5Uncond `step6_hoelder_Cform`，:398） |
| Lean 路线 A（窄域线性档） | δ 口径系数 (√λ₁λ₁/λ₃²+2√2/√λ₃)·√72Up 的上包 | **18.957127** | δ ≤ δ_A=(l₃/24)/√72Up=**0.01458764**（另 β 域恒等 u₁/(24l₃)≈0.0423≤1/2 自动满足） | formal_lean（`step6_uncond_linear`，:935） |
| 数值线性档 | CVal（l4.json C_exact ≡ TableB5Data CVal 逐位） | **14.878732** | δ ≤ δ_max | written_proof_fraction（书面证明非 Lean，l4.json scope 自注） |

- 常数一律以 TableB5Data.lean def 直读（l3=1485363/500000、
  u1=1507319/500000、s1Up/s3Dn/sqrt72Up/CInner/CVal/deltaMax 精确有理）；
  装配恒等式四件（C_inner/C/C_chord/δ_max）独立第二实现 Fraction 复验；
  sqrt 包络前提四件（s1Up²≥u₁ 等）＋ C_B·√δ 支配面 19 点网格复验。
- r19 账本对账：C_B_hi/C_A_delta/δ_A 对 r19_b5u_ledger routes float
  （7.128/18.957/0.014588）全部舍入带内命中（差 ≤1.3e-4）。
- 包络方向全部显式断言（lo² ≤ q ≤ hi² 逐点）；缝阈值一律取安全向
  （上包常数、r_eff 需求、floor 舍入显示）。

## 2. 需求面（L6 认证球＋中心偏移三角入账）

- r\* = 950125/10⁸ = **0.00950125**（l6_intube /quadraticGrowth/
  rigorousRadius 精确十进制；μ(r\*)=[0.00651,0.00928]>0）——
  interval_certified_numeric 层（数值层非 Lean）。
- **轨道中心偏移入账**：deltaOrbitArchive = 2.5634854076114746e-6
  （L6 球心与 R1 存档 TTP 轨道 Hausdorff 上界）⟹ 有效需求半径
  **r_eff := r\* − delta_orbit_hi = 0.009498686514592389**（三角不等式
  安全向：d(Y,X)≤r_eff ⟹ d(Y,center)≤r\*）。偏移量级 ~2.7e-4 相对，
  不改变任何缝判定，但入账后阈值才是安全向的。
- 竞争者排除半径 [3.85e-8,5.49e-8] ≪ r_eff——排除面不构成缝瓶颈
  （注记入账）。
- 双档目标半径并列（敏感性）：
  - 0.07601（r_tube 公式值）：**未认证口径**——l6_intube
    reconciliation.rTargetFormula.certifiedHere==『否…』，μ(0.07601)
    认证区间上端 ≤0，本方法不可严格化 0.07601（float_advisory 如实标注）；
  - R_MAX=0.15202（加倍半径）：**证书拒绝口径**——负对照
    doubleRadiusControl 在档（triggered=true，μ 上端 −14151.328 ≤ 0）。

## 3. 缝闭合阈值三口径（r_eff 主口径；设计期 float 估计的精确重算）

| 口径 | δ_need（精确 Fraction 记账） | float | 设计期估计 |
|---|---|---|---|
| Lean √δ 档（B） | (r_eff/C_B_hi)² | **1.775821e-6** | ~1.78e-6 ✓ |
| Lean 窄域线性档（A） | r_eff/C_A_delta | **5.010615e-4** | ~5.01e-4 ✓ |
| 数值线性档 | r_eff/CVal | **6.384070e-4** | ~6.39e-4 ✓ |

- 域检查全过：B 档 δ_need ≤ δ_max；A 档 δ_need ≤ δ_A 且
  β=u₁√72Up·δ/l₃² ≤ 1/2（精确 Fraction）；数值档 δ_need ≤ δ_max。
- r\* 原口径（无偏移入账）与两档目标半径的阈值也全 12 行落账
  （seam_table；R_MAX 口径下数值档阈值 1.0217e-2）。
- **δ=ρ 缝认同定＝簿记口径（注记非定理）**：L5 前提是固定标号
  |⟨y_i,y_j⟩−⟨x_i,x_j⟩| ≤ δ（∀i<j）；S₉ 重排竞争者须对匹配重排应用
  前提（l4.json metric 注记原文：『前提对某重排成立时对该重排应用』）。
  ρ_spec（谱管类和特征坐标口径）与逐对内积偏差口径是不同量——本审计
  以口径同定作簿记，若未来成证书须替换为逐对口径的显式转换。

## 4. 与 L3 供给对账（tube.json /verdict 阶梯，数值层输入如实标注）

存档阶梯（AAA，三轨道一致）：ε=1.5e-8 → ρ_spec=**0.0466**（最深 SDP
点，伪近零 (0.1961,0.1961,0.1961) 深度 9.4e-9 级，可能是 SOS 族真零点）；
5.3e-6~1e-4 → 0.2548 平台；≥3e-4 → 0.6447 平台（tube 自身
ε_forcing=4.1531e-4 所在）；L3 谱管内部需求 need=0.018506（min_gap/2，
内部比值 ratio_at_floor=2.5157×）。

- **最深 SDP 点对认证 r_eff 差 ~72.9×**（数值口径 CVal·0.0466=0.6927；
  Lean 窄域档 ~92.9×／√δ 档 ~161.9×）；对 R_MAX 差 **~4.56×**；对
  未认证 0.07601 差 ~9.11×。三口径 × 三需求半径全组合不闭合——
  如实落账不硬凑（设计期预判 73×/4.6× 精确重算确认）。
- **M9 口径 ε_forcing 的阶梯不定值如实处理**：l2_rigorous
  eps_forcing 精确 Fraction（float 1.4030566524531613e-4）落在存档阶梯
  1e-4（0.2548）与 3e-4（0.6447）两点之间——存档无该点 ρ_spec 值；阶梯
  非降（存档点列逐对验证）⟹ ρ_spec(M9 ε_forcing) ∈ [0.2548,0.6447]
  括带对账，**两端对数值档阈值均 ≥399×**——缝判定对该平台歧义稳健。
- binding-constraint 识别：**L3 供给**。ρ_spec 地板由伪近零几何决定，
  ε 压缩 4 个数量级（1.5e-8）只收 13.8×（0.6447→0.0466）；到 6.38e-4
  还需再收 ~73×，阶梯对数斜率外推远不可及——非 L5 常数层（域全适用）
  亦非 L6 认证球（r* 已认证）的问题。

## 5. Round 5『闭合窗口』叙述勘正（定量落账）

architecture-decision.md §2.4（:205–:207，另 §1.3 :131–:134）称：
『L3 解析化后 ρ_spec(4.15e-4)~√ε≈0.02 量级（估计值），落入无悔件 L5 的
δ_max=0.17124 覆盖域——L2→L3→L5→L6 链有闭合窗口』。

**勘正：δ_max 是 L5 常数的适用域上界（必要条件面），不是链闭合窗口。**
闭合的判据是 C·δ ≤ 需求半径，不是 δ ≤ δ_max：

- ρ=0.02 处 d_P ≤ CVal·0.02 = **0.297575**（精确 Fraction 记账）——
  对 r_eff 差 **31.3×**、对未认证 0.07601 差 **3.91×**、对 R_MAX 差
  1.96×：全口径不闭合；
- 域窗口若被误读为闭合窗口，高估 **268×**（δ_max/δ_need_num(r_eff)
  =0.17124/6.3841e-4，精确 Fraction 记账）；
- 原文的『覆盖域』语言只在『常数在其域内有效』意义上成立——这是
  常数的**适用性**陈述，与链是否闭合相差一个 C 倍（~14.9–19.0×）与
  需求半径（0.0095–0.076）两层。Round 5 当时无 Lean 双档常数与认证
  r\*（该叙述系设计期估计，原文 :321–:322 已自注『量级估计非计算
  结果』）；本探针以 R19A/R8 存档底座把该叙述勘正定量落账。

## 6. 诚实边界

- 本件零求解零 SDP 零新数值证书；endgame.json sha256 不变
  （86863a09…69f，G1 冻结锚）；C2 冻结漂移分布 22 叶不扰（G1 隔离面）。
- l4.json 数值层线性常数的书面证明属性、tube.json 阶梯与 0.07601 的
  数值层/未认证属性、l6 r\* 的区间证书（非 Lean）属性——三层口径
  （formal_lean / written_proof_fraction / interval_certified_numeric /
  rejection_certified_numeric / float_advisory）逐行标注且机器可查
  （gate G4）；float_advisory 数不进入精确断言（只在宽安全边的
  定向比较中出现）。
- 缝表任一断言与存档不符即 FAIL（探针内置 require 面＋门 G4 交叉面）。
