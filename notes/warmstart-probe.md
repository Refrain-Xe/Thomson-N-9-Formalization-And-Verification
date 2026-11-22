# warmstart-probe — SDPA-GMP 初值通道死活探针（R11B，2026-10-10）

> 任务 r11b-warmstart-probe（D43 裁决 2）：RC2 C1 第 0 项『初值注入配置验证』
> 预算内兑现。ledger＝`numerics/bounds/results/r11_warmstart_probe.json`；
> 门＝`numerics/bounds/r11_warmstart_gate.py`（seed 20261013，G1–G6＋NC1/NC2，
> 2026-10-10 亲跑 exit 0）。本文不重写
> `notes/m11-expansion-decision.md`／`notes/rc2-engine-survey.md`——RC2 排序
> 变动由后续轮次决策件收编（见 §5）。

## 结论（verdict = channel_alive）

载体＝在册最小整解档 typed cap m090 M6（存档冷解 586.8s／76 iter／pdOPT，
`results/typed_ladder_work/m090_M6/` 三件冻结零改动——sha256 前后一致＋git
diff 守卫，门 G6）：

| run | solve_s | iter | phase | objVal |
|---|---|---|---|---|
| 冷重解（同 dat-s/param） | 518.3s | **76** | pdOPT | 2.5753123280579235e+01 |
| 自暖启（存档 .result→.ini 回注） | **0.3s** | **0** | pdOPT | 2.5753123280579235e+01 |
| dyadic 2⁻²⁴ floor 截断暖启 | 4.3s | 0 | noINFO | 2.5753123164176941e+01（偏 8 位） |
| dyadic 2⁻²⁴ clamp 控因对照 | 1.3s | 0 | noINFO | 5.1506246566772461e+01（μ<0） |

- **消费证据**：冷 76 → 暖 0（0.3s）；同输入确定性求解器口径下输出全变
  （迭代表不再逐位同冷解）⇒ .ini 真被消费。`.result` 头部自报
  `initial is …/warm_self.ini`（二进制亲验）。
- **确定性口径**：冷重解 76 iter 且迭代表与存档**逐位一致**
  （`table_identical_to_archive=true`）——墙钟 518.3s vs 存档 586.8s 属机器
  负载差，不动账。
- **质量证据（C1 判死条件③预演）**：暖启 .result 走完整认证链
  （`solution_from_parse`→`certify(k=48)`）得
  certified＝`144977193375331596/5629499535314119`——与存档证书
  claimed_bound **逐位相等**；`typed_ladder.py --verify-cert` 对暖启证书与
  存档证书各 exit 0。**精确初值传递零认证质量损失。**
- **预算**：Σsolve_s＝524.2s（Fraction 2621/5）≤ 2160s 口径 A 硬顶
  （0.0485 当量〔勘误注记 D47：原书 0.0486 系 1 ulp 舍入笔误，
  2621/54000=0.048537…四位应收 0.0485〕，计划 0.163——暖启两解远快于
  预估）。

## 1. .ini 密集格式规格（源码解码＋官方样例亲验）

来源：sdpa-gmp-7.1.3 源包（重取自 sourceforge，URL 记 ledger provenance）
`sdpa_io.cpp:149-282` `IO::read(fpData, xMat, yVec, zMat, inputSparse)`；
官方 `example1.ini` 对照；消费路径 `sdpa_main.cpp:256-277`（读入
currentPt → `computeInverse` → `mu.initialize(currentPt)` → 主循环
`solveInfo.update` 改走 initPt_xMat/initPt_zMat 参照）。

**纯顺序 scanf 流**（`gmp_fscanf "%*[^0-9+-]%Fe"`，200 位精度——
`Parameter::readFile` 末尾 `mpf_set_default_prec(200)` 先于初值读入）；
花括号／逗号／换行皆可跳字符。顺序：

1. **yVec**：m 个数。注意**读入即取负**（`yVec.ele[k] = -tmp`）——与
   `.result` xVec 段的显示层取负（`currentPt.yVec.display(fpout,-1.0)`）
   互抵，回注原样 token 即还原内部 yVec；
2. **zMat SDP 部分**：blockStruct ≥2 的块按出现序，各 size² 个数（行主序
   **全方阵含下三角**；`i≤j 且 ≠0` 者生效——**零是占位符必须写出**，
   官方样例 `{ {11.0, 0.0}, {0.0, 9.0} }` 亲证）；
3. **zMat LP 部分**：LP_nBlock 个数（blockStruct <0 与 ==1 者摊平按出现序；
   同样跳零）；
4. **xMat SDP 部分**：同 2；
5. **xMat LP 部分**：同 3。

**REVERSE_PRIMAL_DUAL**（`sdpa_tool.h:58` 无条件 #define＝1）：
`.result` 的 xVec 段＝内部 yVec×(−1) 显示、xMat 段＝内部 zMat、yMat 段＝
内部 xMat（`sdpa_io.cpp:1503-1513`）。故 `.result→.ini` 映射＝
xVec→yVec 段、xMat→zMat 段、yMat→xMat 段，且原始 blockStruct 顺序拆块后
须按 **SDP-先-LP-后** 重排（m090：37 SDP 块＋96 LP 值＝68359 数/5.06MB）。
负 blockStruct（对角块）与尺寸 1 块在内部都是 LP 标量（`sdpa_main.cpp:
120-134`）。

CLI：option type 2 `-id <ini>`（dense）／`-is <ini>`（sparse）；option
type 1 位置参 `[InitialPtFile]`（文件名 `-s` 结尾判 sparse）。四路均烟雾验
（官方样例 39→31/-id 31/位置参 31；自转换 0）。

转换器＝`numerics/bounds/warmstart_probe.py --convert RESULT DAT_S OUT.ini
[--dyadic-floor-bits N | --dyadic-clamp-bits N]`；token 全程字符串原样
（零浮点往返），独立 scanf 语义回读器 68359 token 逐位验证在案。

## 2. 传质损失鲁棒性（2⁻²⁴ 两变体均死——死因分层）

- **floor 变体**（截断，口径同 `sdp_certify.dyad(floor=True)`）：11186 个
  |v|<2⁻²⁴ 的 token 中 5766 个化为精确零 → **reader 零跳过**
  （`tmp!=0.0` 条件）→ 这些槽位回落 `setIdentity(λ*=1e4)` 默认值（对角/
  LP 槽＝1e4）→ μ 从 9.1e-30 跳到 2.75e+06 → phase=noINFO 0 迭代即退。
- **clamp 控因对照**（最近网格点、半格内钉 ±2⁻²⁴ **不落零**）：无零 token
  仍 noINFO，μ＝**−6.7e-07**（X·Z 内积为负＝粗网格本身破坏 PSD）。
- 分层结论：2⁻²⁴ 网格太粗——**即使避开零跳默认值陷阱，粗网格扰动也使
  X/Z 不再 PSD**；IPM warm-start 的传质精度需求 ≫ 24 位。精确（66 位十进制
  ＝200 位 GMP）传递则零损失。RC2 传值方案应整精度（或 ≥ 数十位）。

## 3. RC2 含义

- **C1 第 0 项兑现：alive**。初值注入配置验证通过——『新引擎类破 a5 每迭代
  标度 ×3.40』路线里『复用前解作初值』的工程前提成立：同配置下 m090_M6
  从 518s 降到 0.3s（精确前解注入、即时收敛、认证逐位复现）。
- 真正的 RC2 收益取决于**非精确前解**（如低精度预解/外推解）下的迭代压缩
  ——本轮 2⁻²⁴ 粗截断两端皆死提示：前解精度是硬约束，需 ≥ 存档证书同量级
  （2⁻⁴⁸ dyadic 回读在本档证明零损失）。**扩容首测建议 a5 M9 起步**：
  存档 a5 族前解整精度注入（任务书既定位）；粗截断传值不排。
- 若后续走多次外推（每档 M→M+1 前解迁移），注意本探针只验了『同档自注入』；
  跨档迁移属新实验（未测，如实记）。

## 4. 交付件与复现

- `numerics/bounds/warmstart_probe.py`——转换器＋运行器（--format-spec /
  --smoke / --convert / --run --stages）；
- `numerics/bounds/results/r11_warmstart_probe.json`——ledger（runs 8 条、
  verdict、consumption、quality、budget Fraction、冻结件 sha256 前后、
  .ini 格式规格、provenance）；
- `numerics/bounds/r11_warmstart_gate.py`——验收门（两轮亲跑 exit 0：
  8-run 与 7-run 两态）；
- 本笔记。求解全在 /tmp/r11_ws/work/（仓库零接触）；暖启证书落
  /tmp（不进 certificates/——冻结面不扩）。

## 5. 后续指向

append-only：RC2 排序变动（C1 alive ⇒ RC2 评估就绪待扩容首测 a5 M9）由
m11/rc2 决策件下一轮收编，本文不代写。预算入账：本轮 heavySolves 实用
524.2s＝0.0485 当量（计划 0.163；勘误注记 D47：原书 0.0486 系 1 ulp 舍入
笔误——append-only 约束 RC2 内容归属不代写，不改既存句内错数），campaign
余量相应增加（r11c 收口门核）。
