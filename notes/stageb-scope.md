# Lean Stage B 范围件（R10B-stageb-scope）

任务书：R10B（R9 ⑤ 候选 2 指定件；D34 裁决 5②『未来轮如排 Lean 工作须先出
范围件』的前置兑现；D38 裁决 3 指定件）。本件定位＝**范围界定**：零求解、
零 Lean 代码编写；全部引用数字机器可核（本设计师 R10 会话亲测，命令与判据
由验收门 `numerics/bounds/r10_stageb_gate.py`（seed 20261012，CWD 无关）逐项
重放）。结构＝五节正文（§0–§4，沿 D38 裁决 3 节单）＋§5 与 campaign 路线
关系节，共六节锚。

诚实声明：本件不承诺任何定理的证明完成时间；§2 末『不承诺』条款给出
thomson_nine／thomson_nine_unique 对 Stage A 闭合的硬依赖与 L3 永久开放现状
的定量差距。凡本会话未跑的检查一律写『未跑』。

## §0 冻结命题（命题冻结不动）

冻结文件：`formal/lean/ComparatorChallenges/ThomsonN9.lean`（185 行，本会话
`wc -l` 亲测）。四条挑战定理（名称／行号／命题本会话逐行亲读）：

| 定理名 | 声明行 | 命题（冻结口径） |
|---|---|---|
| `thomson_nine_M0` | 158 | `∀ x ∈ SphereConfig 9, (36/2 : ℝ) ≤ coulombEnergy x`（E ≥ 18：36 对、每对距离 ≤ 2） |
| `thomson_nine_M1` | 166 | `∀ x ∈ SphereConfig 9, (189/8 : ℝ) ≤ coulombEnergy x`（E ≥ 189/8 = 23.625） |
| `thomson_nine` | 172 | `∃ z ∈ Set.Ioo 0 1, ∀ x ∈ SphereConfig 9, coulombEnergy (triCapPrism z) ≤ coulombEnergy x` |
| `thomson_nine_unique` | 179 | 全局最小者 `∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 9)) (z ∈ Ioo 0 1), ∀ i, x i = g (triCapPrism z (σ i))` |

**恰 4 处 sorry**，行号 `160/168/175/183`（本设计师亲验：逐行
`stripped == "sorry"` 计数＝4，行号恰为 [160, 168, 175, 183]；门 G2 以同一
判据重放）。`scripts/check.sh` 步 4 以构建日志计数判定：挑战件恰 4 条
`declaration uses sorry`、解件 `ThomsonN9/Solution.lean` 0 条，计数偏离即
exit 1；步 5 公理检查拒 `sorryAx`；步 1 哈希钉现跳过（`SHA256SUMS.txt` 未钉，
本会话 `test -f` 亲测 ABSENT）；步 6 语句比对 foundation 阶段 DEFERRED。

冻结铁律（沿任务书）：不动 `references/` 与挑战文件；`R3`/`SphereConfig`/
`coulombEnergy`/`cyl`/`triCapPrism` 及辅助引理至 `triCapPrism_mem` 逐字移植自
`references/thomson-n7-lean`（文件头 13–16 行自述）。命题一经冻结不改——
Stage B 一切工作以**新增**解件／数据件完成，挑战件字节不动。

## §1 三层分工

信任链自下而上分三层（照 N7 四层验收栈裁剪，见 notes/strategy.md §2；
层级与数据流向为本件设计裁决，进入 Stage B 后不再改）：

| 层 | 内容 | 进入信任链 | 完整性机制 |
|---|---|---|---|
| L-1 **结构定理层** | 数学定理的 Lean 证明（Mathlib）：恒等式、正性、刚性、唯一性论证。无自定义公理，仅 `propext, Classical.choice, Quot.sound` | 是（Lean 内核） | `check.sh` 步 4–5（sorry 计数＋公理）＋步 6 语句保真 `compare_statements.py` |
| L-2 **dyadic 证书数据层** | 求解器产出的证书系数，dyadic 舍入成 2 的幂分母有理数，**以 hypothesis 注入**（系数直书进 Lean，证书性质『系数非负／f ≤ φ／PSD』作为显式假设，内核 norm_num/decide 重放代数——N7 `decide +kernel` 路线） | 是（经内核重放） | `scripts/pin_hashes.sh` 钉 `SHA256SUMS.txt`（在盘未激活，命题冻结后钉）＋ `check.sh` 步 1 拒 tracked-but-unpinned；dyadic 舍入＋`thomson-workflow/certificates/thomson_certs/exact.py` 精确验证（铁律口径） |
| L-3 **float advisory 与求解器** | scipy linprog／SDPA-GMP／探针的浮点搜索（找证书候选）；`lp.json` `method.certification` 自述『LP 解仅作候选，证书不信任浮点』 | **否** | 不进信任链；只消费其精确有理重放产物（L-2） |

仓库内三层先例（全部已在盘）：L-2 dyadic 数据先例＝hermite v2 证书 coeffs
dyadic（coeffs[0] 在 2⁻⁴⁸ 格点、coeffs[1..16] 系 2⁻⁴⁹ 奇格点＝2⁻⁴⁸ 外舍
中点——R9B 任务书措辞出入留痕）、W=17/2⁴⁹ 精确
（`numerics/bounds/hermite_minorant.py:223` `hermite_minorant_dyadic`）；
L-2 精确 Fraction 重放先例＝
`numerics/bounds/l2_rigorize.py:113` `rebuild_certificate`（R1/R2/defl/R2max）；
L-3 浮点搜索先例＝`numerics/bounds/lp_bound.py`（LP 解仅候选）与
SDPA-GMP 各账本。

## §2 结构定理清单与依赖序

### 表 A：纯有理代数件（可先行——只依赖 ℚ 上的代数与 Mathlib，不依赖任何
解析待证件；仓库内各有精确 Fraction 第二实现或等值锚）

| # | 件 | 数学形态 | 仓库地基（本会话直读） | Lean 形态 |
|---|---|---|---|---|
| A1 | 三点恒等式 | KLT (4.5) 型：Σ_84 λ_cls + Σ_all == ΣH − e_dy 对任意有理 Gram 三点组逐项成立 | `numerics/bounds/r9_s3_rederive.py:717-749` `identity_trials` 随机有理构型 3 trial 精确 ==0（seed 20261011）；`typed_ladder.py` K_cols/sos_sum 装配 | `ring`/`Finset.sum` 重排；系数是 ℚ 常数 |
| A2 | 引理 4.1 正性 | Hermite 插值余项符号：φ−H = φ^{(m)}(ξ)/m!·∏(t−ν_k)² ≥ 0，因 φ^{(m)} = (2m−1)!!(2−2t)^{−(2m+1)/2} > 0 | `numerics/bounds/r9_v2iv_reverify.py:97-104` 符号递推机器化（inv_sqrt_pow_iv/dfactorial_odd）；φ^{(m)}>0 公式核 | `Real.sqrt_pos`／幂正性；∏(t−ν)²≥0 平方和 |
| A3 | typed 组合恒等式 | 轨道计数配平（counts 3·1/6·9/1·27 口径）与 ℓ₁ 装配 | `numerics/bounds/typed_ladder.py:229-300` QuotientMaps counts | 有限枚举 `decide`／显式计数引理 |
| A4 | S₃ 商展开 | FRing (u,v,t) 分次单项式 D=16 → Q_k 递推 K=6 → Y_cols 271 列 → share_lp/GM_OF/lam | `numerics/bounds/r9_s3_rederive.py` 全链自写第二实现（stdlib only）；`typed_ladder.py:275-285` | 多项式环上的显式线性代数（系数 ℚ） |
| A5 | L2 强制恒等式 | certified = (e−defl)/(1+R2max)；ε_forcing == (1+R2max)(E*−certified) 精确恒等式 | `numerics/bounds/l2_rigorize.py:113` 重放逐位（ε_forcing 精确分数在 `results/l2_rigorous.json`） | 有理恒等式 `field_simp`/`ring` |
| A6 | Lukács·Markov–Lukács 平方表示 | [a,b] 上非负多项式 p = s(t)² + (t−a)(b−t)·u(t)²（次数 2d 与 2d+1 两型）；分段 minorant 的 σ 族由此构造 | `numerics/bounds/tube_probe.py:13,25`（『Lukács/Markov–Lukács σ 族』先例）；`strips_final.py` 消费 | 显式平方和展开（ℚ 系数直接验证） |

### 表 B：解析几何件（后置——依赖实解析事实／构型几何，工程量与风险高于表 A）

| # | 件 | 数学形态 | 仓库地基 | 备注 |
|---|---|---|---|---|
| B1 | SO(3) 轨道核 | 商掉旋转后的构型空间维数／轨道横截坐标 | l4_orbit.py（L4 orbit 位） | 唯一性定理的前置 |
| B2 | D3h 一维化 | D3h 对称构型 → 单参数族 E(z)；z* 无闭式须以唯一根区间刻画（strategy.md §0.1） | numerics/family.py（数值） | 解析（驻点唯一性） |
| B3 | Riemannian Hessian | KLT §7.4 分解 D²E=Σ_e[(3/4)f_e^{-5/2}(Df_e)²−(1/2)f_e^{-3/2}D²f_e] | l6_intube.py 半件 | 免 D³E 路线 |
| B4 | 二阶充分 | 管内 D²E ≥ μ > 0 ⇒ 二次增长 ⇒ r_tube 严格化 | local_min.py/l6 半件 | 依赖 B3＋短边刚性 |
| B5 | Procrustes | d_P(X,Y) ≤ C·δ，C=14.878732094961943、δ_max=0.17124089749729504（`results/l4.json` constants 亲读） | numerics/bounds/l4_procrustes.py（含三负对照） | 区间 Sylvester 判定可机器化 |
| B6 | 拼接端点 | 12 分区边界处两侧证书口径衔接（splice map） | notes/splice-map.md、endgame_chain.py | 依赖分区证书族 |

### 依赖序与不承诺条款

```
M0 ──(独立)──► A1…A6（六件互相独立，可与 M1 并行）──► M1
                     │
                     ▼
              B1…B6（解析几何件；B5 可独立先行）
                     │
                     ▼
        thomson_nine ──► thomson_nine_unique
```

**不承诺条款（铁律级）**：`thomson_nine`／`thomson_nine_unique` 依赖
Stage A 闭合（L0 洞片全绿＋L3 谱管链闭合）。L3 现状＝**永久开放**
（dead-at-(9,6)，D24/D25）：ε_forcing = 1.4030566524531613e-4 ≫
ε_W = 7.325716460104294e-13，比值 191524837.2 ≈ 1.9152e8×（本会话
Fraction 直算 `results/l3_analytic.json` inputs/interval_constants）；
`results/endgame.json` endgameChain `closed=false`、`blocking=[L0, L3]`、
assembledRecord = 47517790735835014335570/1844674407419222803119 =
25.759445973097478 维持。在 Stage A 闭合（或外部扩容 RC1/RC2 触发重开并
翻正）之前，**本范围件对 thomson_nine 与 thomson_nine_unique 不承诺任何
排期、可行性结论与工程量估计**——Stage B 可承诺范围＝M0＋M1＋表 A 代数件
（＋B5 Procrustes 常数件作为可选独立件）。

## §3 M0/M1 先行方案

- **M0（E ≥ 18）**：36 对两两距离 ≤ 2 ⇒ 1/d ≥ 1/2 ⇒ E ≥ 36/2。一次
  三角不等式级证明（strategy.md §1 定位为管道验证与语句保真基建的
  『hello world』）。不依赖任何证书数据。
- **M1（E ≥ 189/8 = 23.625）**：**严格数值基座已在盘**＝两点 LP 证书
  `numerics/bounds/results/lp.json`（Yudin/Delsarte 对偶＝插值多项式
  minorant，degree 40，41 个 Legendre 系数，seed 20261002）：
  `bound_exact` = 1850667279730771809…32738117664768000000（1583 字符
  精确分数）＝ 25.72949096219507（float repr），**Fraction 亲验**：
  > 189/8（真，富余 25.72949096219507 − 23.625 = 2.10449096219507）且
  ≤ E* + 1e-6 = 25.759987531（真，E* = 25.759986531 直读
  `thomson-workflow/data/energies.json` energies[9].value）。证书自检
  coeffs_nonneg_k_ge_1 / f_le_phi_certified_exact_rational /
  taylor_tail_rigorous / tail_interval_check 四项全 True；区间扫描
  250112 叶 146.6s（Python Fraction 重放口径）。
  M1 的 Lean 化路线（择一，Stage B 首轮裁决）：(i) 直接重放 lp.json 全链
  （250112 叶二分重放进内核——重，数据 9,858 B 轻而计算重）；(ii) 对
  189/8 目标单独产一份轻节点证书（如单节点退化 SDP／粗网格 minorant，
  dyadic 舍入后叶子数大幅缩减——须新数值轮产出，不在本范围件内）。

**数据导入体量实测表**（2026-10-10 本会话 `os.path.getsize` 逐份实测；
MB＝MiB=1024² 字节口径）。`certificates/*.json` 现计 **27 份**，合计
95820405 字节＝91.38 MB：

| 文件 | 字节 | MB |
|---|---|---|
| `n9-stage-a.json` | 18,006 | 0.02 |
| `n9-stage-a2-sdp-hp.json` | 2,554,866 | 2.44 |
| `n9-stage-a2-sdp.json` | 1,940,500 | 1.85 |
| `n9-stage-a2-slab-sm19o20_m91o100.json` | 1,575,281 | 1.50 |
| `n9-stage-a2-slab-sm1_m99o100.json` | 1,570,287 | 1.50 |
| `n9-stage-a2-slab-sm91o100_m9o10.json` | 1,588,445 | 1.51 |
| `n9-stage-a2-slab-sm97o100_m19o20.json` | 1,565,976 | 1.49 |
| `n9-stage-a2-slab-sm99o100_m97o100.json` | 1,567,167 | 1.49 |
| `n9-stage-a3-cap-m0755.json` | 1,934,431 | 1.84 |
| `n9-stage-a3-cap-m077.json` | 1,933,486 | 1.84 |
| `n9-stage-a3-cap-m085.json` | 1,932,414 | 1.84 |
| `n9-stage-a4-strip-m079-m765_M10.json` | 15,515,895 | 14.80 |
| `n9-stage-a4-strip-m082-m079_M9.json` | 8,278,023 | 7.89 |
| `n9-stage-a4-strip-m085-m082_M8.json` | 4,167,042 | 3.97 |
| `n9-stage-a4-strip-m088-m085.json` | 1,905,928 | 1.82 |
| `n9-stage-a4-strip-m090-m088.json` | 1,802,261 | 1.72 |
| `n9-stage-a4-typedcap-m0748.json` | 2,270,188 | 2.17 |
| `n9-stage-a4-typedcap-m0748_M8.json` | 6,695,903 | 6.39 |
| `n9-stage-a4-typedcap-m0748_M9.json` | 13,641,180 | 13.01 |
| `n9-stage-a4-typedcap-m0755.json` | 2,768,306 | 2.64 |
| `n9-stage-a4-typedcap-m077.json` | 2,984,794 | 2.85 |
| `n9-stage-a4-typedcap-m080.json` | 3,011,238 | 2.87 |
| `n9-stage-a4-typedcap-m085.json` | 2,997,283 | 2.86 |
| `n9-stage-a4-typedcap-m090.json` | 2,989,677 | 2.85 |
| `n9-stage-a4-typedcap-m090_M6.json` | 937,216 | 0.89 |
| `n9-stage-a5-hermite-cap-m0748.json` | 2,218,768 | 2.12 |
| `n9-stage-a5-hermite-cap-m0748_M8.json` | 5,455,844 | 5.20 |

导入分档结论：M1 走 lp.json 路线只须导入 9,858 字节（41 个系数合计 1,959
字符）——**轻**；slab/tube/typedcap 证书若进 Lean 须切块（单份最大
15,515,895 字节＝14.80 MB）——**重**，属表 B 后置件的数据面，不在 M0/M1
先行范围。

## §4 环境前提与工程量分档

**环境实测（2026-10-10 本会话，`command -v` 三连）**：`lake` NOT FOUND、
`lean` NOT FOUND、`elan` NOT FOUND——本机无 Lean 工具链（如实入
`numerics/bounds/results/r10_stageb_env_ledger.json`；informational 记账，
不作门 pass 判据）。check.sh 首跑前须：装 elan → `lean-toolchain` 钉扎的
`leanprover/lean4:v4.34.1` → Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`
（`lakefile.toml`/`lake-manifest.json` 钉扎，禁 `lake update`）。

**check.sh 首跑门槛（脚本头 15–16 行 Needs 条款亲读）**：需 elan/git/python3＋首跑网络
（Mathlib 及其 cache）、约 14 GB RAM、约 10 GB 磁盘；`lake exe cache get`
失败则源码编译『数小时』；`SKIP_BUILD=1` 可先跑免构建检查（步 1–2）。本会话
**未跑** check.sh（工具链缺失，如实记）。

**工程量分档**（估计口径，非实测——除标注者外）：

| 档 | 对象 | 量级依据 |
|---|---|---|
| 小 | M0 | 单文件初等证明＋全链管道（check.sh）验证（strategy.md §1） |
| 中小 | M1 | 数据面就位（9,858 B）；重放面两路线待裁（§3 (i)/(ii)） |
| 中 | 结构定理层表 A 六件 | 每件有精确 Fraction 第二实现地基；参照 N7 解文件 17,895 行、10 agent 约 15 小时（strategy.md §4 亲读） |
| 依赖闭合 | thomson_nine／thomson_nine_unique | 依赖 Stage A 闭合（L0＋L3）；L3 永久开放现状下**不承诺**（§2 条款） |

## §5 与 campaign 路线关系

- **并行性**：Stage B 的 M0/M1＋表 A 代数件**不依赖 closed**——只需冻结
  命题（§0）与在盘证书（§3），全部为 ℚ 上代数重放。故可与 campaign 主攻线
  的 RC1/RC2 等待期并行：campaign 主攻线已闭案于外部扩容触发器（RC1＝外部
  预算扩容 ≥12 当量；RC2＝新引擎类实测每迭代成本破 a5 标度 ×3.40，
  notes/m11-expansion-decision.md ④ 亲读），等待期零求解窗口正排
  M0/M1 与结构层代数件。
- **决策链**：D34 裁决 5②（Lean 脚手架开放式范围风险一轮难收口，『未来轮
  如排须先出范围件』）→ 本件兑现前置；D38 裁决 3 指定 R10B 交付本件。
- **现状锚**：R9 终态 closed=false、blocking=[L0,L3]、assembledRecord =
  47517790735835014335570/1844674407419222803119 = 25.759445973097478
  维持（HP 兜底片 [−153/200, −187/250] 全局瓶颈，margin 5.4056e-4）。
- **边界纪律**：Stage B 不动 `references/`、不动挑战文件、不消耗求解预算
  （heavySolves=0 口径）；一切新证书沿铁律 dyadic 舍入＋exact.py 精确验证
  ＋provenance 记 --k 与代码版本。
