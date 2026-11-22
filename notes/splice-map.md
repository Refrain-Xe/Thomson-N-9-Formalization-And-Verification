# 拼接地图（splice map）—— N=9 全空间能量下界的 12 原子区域装配

> 生成：2026-10-05（Round 5 无悔三件之 L7）。数据源：`numerics/bounds/results/endgame.json`
> （12 区域精确 Fraction 记账＋机器断言）、`certificates/` 22 份存档证书、
> `results/{slab_band,strips,typed_ladder,hp,tube,full_local_min,local_min,l2_rigorous,l4}.json`。
> 本文件的任务：把「拼合即证明」（E ≥ 25.759445973097478 的全空间覆盖论证）写成
> **可独立复核的装配说明书**——每个原子区域给出证书文件、验证命令、覆盖语义与
> 边界衔接。本文写就当天的复核记录见 §7（全部命令本会话逐一重跑 exit 0）。

---

## 0. 总判定（先说结论）

- **当前严格成立的全空间命题**：对全部 9 点单位球面构型 X，
  **E(X) ≥ 25.759445973097478**（精确分数
  `47517790735835014335570/1844674407417822803119`，拼合口径）。
- 该值 = 12 个原子区域覆盖界的精确 Fraction 取 min，瓶颈 = HP 片（三个洞子带并列
  全局最弱）。距离 E\* = 25.759986531（三源校验**参考值**，非已证最优）差
  5.406e-4。
- **排除论证已完成的部分**：12 片中 8 片（5 slab ＋ 3 条带）certified **> E\***
  ⇒ 全局极小若存在，只能在剩余 4 片（3 个洞子带 ∪ cap 片）内——cap 片含候选 TTP
  （m\* = −0.7475605 > −0.748 = cap 切口下端）。
- **收尾链未闭合**（`endgame.json` `closed=false`，八引理仅 L1 严格）：把下界从
  25.759446 抬到 E\* 还需 L0 三片受阻条带翻正＋L3 谱管新证书族＋L4 刚性计数＋
  L6 管内全域/Taylor 余项（§6）。

**语义约定（全部文档统一）**：E\* 是参考值；「> E\*/≤ E\*+1e-6」断言均为精确
Fraction 比较（endgame_chain 以 `Fraction` 断言），语义是「与参考值不矛盾」。
exclusion 片＝区域不含 TTP，要求 bound > E\*（把全局极小从该区域排除）；
TTP-covering 片＝证书域含 TTP，要求 bound ≤ E\*+1e-6。

---

## 1. 区域坐标与覆盖原理

**区域参数**：m(X) := min_{i<j} ⟨x_i, x_j⟩（构型最小成对内积）∈ [−1, 1]。
每个构型的 m 是 36 个内积的有限最小值，必落入下列 12 个闭区间之一（区间端点
全部为精确有理数；相邻区间**共享端点**，端点处的构型同时被两侧证书覆盖——
各证书的域条件都是闭条件，重叠无害、无需打破平局的规则）。

**每个证书的覆盖语义**（两类机制）：

| 证书类 | 域条件（对构型 X 的前提） | 机制 |
|---|---|---|
| slab / strip（分带 typed 证书） | 取 (i,j) 为 realization 的最小内积对（重排至 (0,1)，PAPER.md §6.4 exists_minpair_perm），u = ⟨x_i,x_j⟩ ∈ [lo,hi] | (2,7)（slab，M=7）/(8,6)（strip）分带 typed 三点 SDP：λ ≥ 0 于「lo ≤ u ≤ hi、其余内积 ≥ lo」的三点域（带上切口 hi−u 乘子正是把 TTP 排除出域、拿到正裕度的机制） |
| HP / cap（切口证书） | m(X) ≥ 切口 a₀（HP: −9/10；cap: −187/250） | untyped (8,6) / typed (3,3,3) S₃商 (8,6) 三点 SDP：切口下全域 λ ≥ 0 ⇒ E ≥ certified |

**验证语义**：每份证书 JSON 自含全部精确有理数据（dyadic 系数、PSD 块、残差），
`--verify-cert` 进程外重建＋精确重算（Fraction LDLᵀ 判全块正定、归一化恒等式、
certified 逐位比对），不依赖求解器与浮点。

---

## 2. 12 原子区域总表（自 m=−1 升序）

「精确 bound」为 endgame.json `partition[].bound` 的精确分数（此处列 float，
全串见 endgame.json / 证书 `claimed_bound`）。裕度 = bound − E\*（精确 Fraction
差，float 展示）。

| # | 区间（精确） | 覆盖片 | 证书文件（certificates/） | certified | 裕度 vs E\* | 口径 |
|---|---|---|---|---|---|---|
| 1 | [−1, −99/100] | slab sm1_m99o100 | `n9-stage-a2-slab-sm1_m99o100.json` | 25.815880516105 | **+5.589e-2** | exclusion |
| 2 | [−99/100, −97/100] | slab sm99o100_m97o100 | `n9-stage-a2-slab-sm99o100_m97o100.json` | 25.802848154299 | **+4.286e-2** | exclusion |
| 3 | [−97/100, −19/20] | slab sm97o100_m19o20 | `n9-stage-a2-slab-sm97o100_m19o20.json` | 25.789693014930 | **+2.971e-2** | exclusion |
| 4 | [−19/20, −91/100] | slab sm19o20_m91o100 | `n9-stage-a2-slab-sm19o20_m91o100.json` | 25.771122805988 | **+1.114e-2** | exclusion |
| 5 | [−91/100, −9/10] | slab sm91o100_m9o10 | `n9-stage-a2-slab-sm91o100_m9o10.json` | 25.769683493481 | **+9.697e-3** | exclusion |
| 6 | [−9/10, −22/25] | strip m090-m088 (7,6) | `n9-stage-a4-strip-m090-m088.json` | 25.766265654633 | **+6.279e-3** | exclusion |
| 7 | [−22/25, −17/20] | strip m088-m085 (7,6) | `n9-stage-a4-strip-m088-m085.json` | 25.761930021253 | **+1.943e-3** | exclusion |
| 8 | [−17/20, −41/50] | strip m085-m082 (8,6) | `n9-stage-a4-strip-m085-m082_M8.json` | 25.760813176470 | **+8.266e-4** | exclusion |
| 9 | [−41/50, −79/100] | **HP 兜底**（条带 m082-m079 受阻） | `n9-stage-a2-sdp-hp.json`（域 [−9/10,1] ⊇ 本区） | 25.759445973097 | −5.406e-4 | TTP-covering |
| 10 | [−79/100, −153/200] | **HP 兜底**（条带 m079-m765 受阻） | 同上 | 25.759445973097 | −5.406e-4 | TTP-covering |
| 11 | [−153/200, −187/250] | **HP 兜底**（条带 m765-m748 受阻） | 同上 | 25.759445973097 | −5.406e-4 | TTP-covering |
| 12 | [−187/250, 1] | typed cap m0748 (8,6) | `n9-stage-a4-typedcap-m0748_M8.json` | 25.759571185601 | −4.153e-4 | TTP-covering |

**min（拼合纪录）** = 区域 9/10/11 的 25.759445973097478（HP 片）。
受阻条带不入账：三片的 best_certified_attempt（25.759782986 / 25.759535741 /
25.758718429，见 `results/strips.json` `blocked`）是有效下界但**无存档证书**
（正裕度断言 exit 1），不参与拼合 min；即便入账也不改变瓶颈（区域 11 低于 HP）。

HP 精确分数：`47517790735835014335570/1844674407417822803119`；
cap 精确分数：
`93712774192614269082019881043884635719865006109330352046526968479156494140625/3637978812512164763811573465387274966467532527973356366318401998010742048629`。

---

## 3. 逐类证书的验证命令与覆盖细节

以下命令均在仓库根 `thomson-n9/` 下执行（`python3` 可换
`numerics/.venv/bin/python`；无 cvxpy 也可跑——认证链只用 Fraction）。

### 3.1 slab 五片（区域 1–5，Round 2）

```bash
python3 numerics/bounds/slab_band.py --verify-cert certificates/n9-stage-a2-slab-sm1_m99o100.json
python3 numerics/bounds/slab_band.py --verify-cert certificates/n9-stage-a2-slab-sm99o100_m97o100.json
python3 numerics/bounds/slab_band.py --verify-cert certificates/n9-stage-a2-slab-sm97o100_m19o20.json
python3 numerics/bounds/slab_band.py --verify-cert certificates/n9-stage-a2-slab-sm19o20_m91o100.json
python3 numerics/bounds/slab_band.py --verify-cert certificates/n9-stage-a2-slab-sm91o100_m9o10.json
```

每片输出应含「42 块 LDLᵀ 正定 ✓；界值重算逐位一致 ✓；claimed = … > E\* ✓」。
机制：(2,7) 分带 typed 三点界（N=7 Case 2 移植），极点对参数化，H_A 双侧
Lukács（[lo,hi]）；域见 §1 表。dyadic 2⁻⁴⁰ 舍入＋PSD 修复＋精确残差折减。

### 3.2 条带三片（区域 6–8，Round 4；strips_final.py）

```bash
python3 numerics/bounds/strips_final.py --verify-cert certificates/n9-stage-a4-strip-m090-m088.json
python3 numerics/bounds/strips_final.py --verify-cert certificates/n9-stage-a4-strip-m088-m085.json
python3 numerics/bounds/strips_final.py --verify-cert certificates/n9-stage-a4-strip-m085-m082_M8.json
```

每片 42 PSD 块 LDLᵀ＋certified 逐位重算。机制同 slab 但升阶（前两片 (7,6)、
第三片 (8,6)，SDPA-GMP 求解＋dyadic 认证管线）；受阻断代的解数据存档于
`results/strip_sol_*.json`（可复核受阻原因，best attempt 数字即出自它们）。

### 3.3 HP 片（区域 9–11 的覆盖片，Round 3；sdp_certify.py）

HP 证书没有独立 `--verify-cert` 入口，**按存档 provenance 的生成命令重放**并
逐位比对（`--k 64` 是存档粒度，Round 3 审计教训）：

```bash
python3 numerics/bounds/sdp_certify.py \
    --solution numerics/bounds/results/hp_solution_midlarge_m090.json \
    --min-bound 25.752410818 --ref-safe 25.759446386373018 \
    --k 64 --out /tmp/hp_repro.json
# 然后比对 claimed_bound 与 certificates/n9-stage-a2-sdp-hp.json 逐位相等：
python3 - <<'EOF'
import json
a = json.load(open('/tmp/hp_repro.json'))['claimed_bound']
b = json.load(open('certificates/n9-stage-a2-sdp-hp.json'))['claimed_bound']
assert a == b, (a, b)
print('HP reproduce bitwise equal ✓', a)
EOF
```

机制：untyped midlarge (8,6) 三点 SDP 的 SDPA-GMP 高精度解（GMP 200 位）＋
2⁻⁶⁴ dyadic 舍入认证，认证损失 4.3e-7；域 m ≥ −9/10。**该域同时覆盖区域 6–8
与 12**——endgame 记账按「每区域取其入账覆盖片」，区域 6–8 取条带片（exclusion
口径更强），洞区域 9–11 只有 HP（故为全局瓶颈）。

### 3.4 cap 片（区域 12，Round 3；typed_ladder.py）

```bash
python3 numerics/bounds/typed_ladder.py --verify-cert certificates/n9-stage-a4-typedcap-m0748_M8.json
```

输出「certified = 25.759571185601 重算一致 ✓（38 PSD 块 LDLᵀ 通过，归一化
残差 = 0）」。机制：typed (3,3,3) S₃ 商 (8,6) 三点构造，切口 a₀ = −187/250
< m\* = −0.7475605 ⇒ 域含 TTP（TTP-covering 片，bound ≤ E\*+1e-6 必然）。
它是 L2 强制口径的证书基础（§5）。

### 3.5 装配判定（把 12 片拼起来的机器断言）

```bash
python3 numerics/bounds/endgame_chain.py                 # 分区/口径断言（~5s）
python3 numerics/bounds/endgame_chain.py --reverify-certs  # 进程外重验 5 类证书（~2min）
```

`endgame_chain.py` 以精确 Fraction 断言：① 六条带（certified∪blocked）无缝盖满
[−9/10, −187/250] 且 certified 片上端 ≤ 切口；② 12 区域排序后端点逐一相等、
起点 −1 终点 1（无缝无洞盖满 [−1,1]）；③ exclusion 片 bound > E\*、TTP-covering
片 ≤ E\*+1e-6；④ assembledRecord = min(区域 bound)。任一失败 exit 1。

---

## 4. 边界衔接核对表

12 区域的 13 个边界点（精确分数，相邻区域共享、两侧证书均为闭域 ⇒ 重叠合法）：

```
−1  −99/100  −97/100  −19/20  −91/100  −9/10  −22/25  −17/20  −41/50  −79/100  −153/200  −187/250  1
 #1|#2      #2|#3     #3|#4    #4|#5    #5|#6   #6|#7   #7|#8   #8|#9   #9|#10    #10|#11    #11|#12
```

关键衔接点：

- **−9/10（slab↔条带，也=HP 切口）**：slab 区 #5 上端 = 条带 #6 下端 = HP 域下端。
  m = −9/10 的构型同时被 sm91o100_m9o10（域 [−91/100,−9/10]）与 m090-m088
  （域 [−9/10,−22/25]）覆盖。
- **−41/50（条带↔洞）**：#8 上端 = 洞 #9 下端。受阻条带 m082-m079 的账面 best
  25.759782986 > HP，但无证书 ⇒ 洞区域记账取 HP（保守）。
- **−187/250（洞↔cap）**：#11 上端 = #12 下端 = cap 切口。切口 < m\* ⇒ cap 域
  含 TTP；洞侧由 HP 覆盖（HP 域 [−9/10,1] ⊇ 洞三带）。
- **+1**：全域右端点（m ≤ 1 自动成立；cap 域到 1）。

全部衔接由 `endgame_chain.py` 的 Fraction 断言机器核对（§3.5 命令①）。

---

## 5. 拼合论证（「拼合即证明」的三步推理）

1. **分类**：任意 9 点单位球面构型 X，m(X) ∈ [−1,1] 落入 12 区域之一（§1）。
2. **逐区域下界**：X ∈ 区域 r ⇒ E(X) ≥ bound_r。依据：
   - 区域 1–8（exclusion）：分带 typed 证书的域机制（§1 表）——证书以「最小
     内积对 (i,j) 的 u ∈ [lo,hi]，其余 ≥ lo」为前提，m(X) ∈ [lo,hi] 的构型
     经重排满足之；
   - 区域 9–11：HP 证书（m(X) ≥ −9/10 ⊇ 各区）；
   - 区域 12：cap 证书（m(X) ≥ −187/250）。
   每份 bound 的正确性由 §3 的验证命令独立复核（精确有理数，无浮点信任）。
3. **合取**：E(X) ≥ min_r bound_r = **25.759445973097478**（HP 片）。
   推论（排除部分）：若 E 的全局极小存在且 m ∉ 洞∪cap 四片，则由 exclusion 片
   bound > E\* 得 E_min > E\*，与 E(TTP) = E\* 矛盾 ⇒ 极小只能在洞∪cap 内
   （cap 含 TTP；洞内尚未排除——这正是 L0 未闭合的洞）。

**未把纪录抬到 E\* 的缺口**（详见 `results/endgame.json` `endgameChain` 与
GAP-REPORT Round 4 §②）：若三片受阻条带翻正（Round 5 清单：(9,6) 阶或分块
装配），拼合纪录将升到 cap 片值 **25.759571185601**（wouldBe_if_all_strips_positive）
——仍 < E\*，最终一步必须走 L2→L3→L4→L5→L6 收尾链（见 §6）。

---

## 6. 收尾链组件与配套证书（非能量拼接件，但属同一装配）

| 引理 | 组件 | 数据/证书 | 状态 |
|---|---|---|---|
| L1 | cap 薄层下界 | `n9-stage-a4-typedcap-m0748_M8.json` | **已严格**（ΔE = 4.1535e-4 精确） |
| L2 | 强制：E ≤ E\* ⇒ λ_cls ≤ ε | `results/l2_rigorous.json`（本轮新增）：ε_forcing = **4.153454e-4** 精确 Fraction（= (1+R2max)·E\* − e_dy + defl；比旧数值口径 4.153070e-4 恰大 E\*·R2max = 3.84e-8——数值口径自述忽略的 (1+R2) 因子，已入账） | 恒等式/残差/装配全精确；结构性定理为实例核验（严格数值层） |
| L3 | 谱管 λ ≤ ε ⇒ 内积近 6 节点 | `results/tube.json` | **断点**（ρ_spec 差 34.8×，结构性；Round 5 首选路线 b tube certificate） |
| L4/L5 | 组合刚性；Gram→构型 Procrustes | `results/l4.json`（本轮新增）：**d_P ≤ C·δ，C = 14.8787**（δ ≤ 0.1712，内积口径；距离口径 2C = 29.7575；λ₃(S) ≥ 2.970726 区间严格）——账本 L5 位的 Procrustes 常数已落地（线性 Lipschitz，优于设想的 C√η）；L4 邻型计数仍未开始 | Procrustes 半件已做（区间+推导+负对照）；计数未做 |
| L6 | 局部极小/二次增长 | `results/local_min.json`（z\* ∈ [0.703648376463, 0.703649139406] 严格隔离）、`results/full_local_min.json`（λ_min ≥ 0.14378982，15 维商切空间）、`results/tube.json`（μ₀ = 0.138365 双实现交叉） | TTP 点已严格；r_tube = 0.07601 公式值（缺 Taylor 三阶余项）＋管内全域未严格 |
| L7 | 拼接书面文档 | **本文件** | 本轮补齐（能量拼接部分完整；收尾链拼接待 L0/L3 闭合后扩写） |

---

## 7. 复核记录（本文件写作当天，2026-10-05，全部 exit 0）

以下命令本次会话逐一执行通过（节选输出；完整日志见当轮提交信息）：

| 命令 | 结果 |
|---|---|
| `slab_band.py --verify-cert` × 5 片 | 各 42 块 LDLᵀ ✓、界值逐位一致 ✓、> E\* ✓ |
| `strips_final.py --verify-cert` × 3 片 | 各 42 块 LDLᵀ ✓、certified 逐位一致 ✓ |
| `typed_ladder.py --verify-cert`（cap m0748_M8） | 38 块 LDLᵀ ✓、重算一致 ✓（E\*−c = 4.15345e-4） |
| HP 重放（§3.3 命令，--k 64） | claimed_bound 与存档**逐位相等** ✓（28.8s） |
| `endgame_chain.py` | closed=false、assembledRecord = 25.759445973097478 逐字复现 ✓ |
| `l2_rigorize.py`（本轮） | ε_forcing = 4.153454e-4 精确入账，全断言过，exit 0（30s） |
| `l4_procrustes.py --selftest`（本轮） | C = 14.8787 / δ_max = 0.1712；三负对照全部触发 ✓ |

（`endgame_chain.py --reverify-certs` 的全量 125s 版本在 Round 4 汇总轮已跑
通 all_pass；本表为逐命令等价复核。）

---

## 8. 诚实边界

- **「拼合即证明」的证明对象是 25.759446 ≠ E\***：排除论证（8 片 > E\*）完整，
  但洞区域 [−41/50, −187/250] 的构型未被排除，只能引用 HP 弱界。收尾链
  closed=false。
- **证书的严格性层级**：全部为「严格数值层」证书（Python 大整数/Fraction 精确
  算术＋精确 LDLᵀ；dyadic 数据可精确表示），**未过 Lean 内核**；结构性定理
  （三点恒等式、引理 4.1、Lukács 表示、份额表组合恒等式）引用 PAPER.md §4–6.3
  ＋随机有理点实例核验。
- **E\* 是三源校验参考值而非已证最优**；全部与 E\* 的比较是 Fraction 精确比较，
  语义为与参考值不矛盾。
- **blocked 条带不入账**（无存档证书）；「best_certified_attempt」数字有效但不
  参与拼合 min（§2 注）。
- 本文件是**账本的说明书**，不是新证书：所有数字的权威来源是 endgame.json 与
  certificates/ 下的 JSON；两处不一致时以后者为准并视为本文件 bug。

---

# v2（Round 6，campaign 第 1 轮，2026-10-05）：Hermite 引擎换装后的装配口径更新

> 数据源（本节全部数字出自落盘账本；两处不一致以账本/证书 JSON 为准）：
> `results/endgame.json`（kind=**n9-endgame-round6**：partition/
> citedCertificates/endgameChain）、`results/hermite_strips.json`＋
> `results/hermite_cap.json`（a5 证书账本，hermite_ladder.py）、
> `results/l3_analytic.json`（L3 解析谱管，裁决 D7）、`results/l6_intube.json`
> （L6 管内二次增长区间证书）、`notes/decisions.md`（D1–D8）。
> 引擎变更（架构 C，D5/D6）：候选 minorant 从 Lukács 分段（h 自由）换为
> KLT 式 Hermite 节点插值（h 固定为精确 dyadic M，φ ≥ M 区间证书
> W=Σ2⁻⁴⁹≈2.13e-14；SDP 删 minorant 块，certified = e_dy − defl，无 R2 膨胀）。

## v2.1 新区域总表（a5 证书与两引擎取最优）

| # | 区间（精确） | 覆盖片 | certified | 裕度 vs E\* | 口径 |
|---|---|---|---|---|---|
| 1 | [−1, −99/100] | slab sm1_m99o100 | 25.815880516105 | +5.589e-02 | exclusion |
| 2 | [−99/100, −97/100] | slab sm99o100_m97o100 | 25.802848154299 | +4.286e-02 | exclusion |
| 3 | [−97/100, −19/20] | slab sm97o100_m19o20 | 25.789693014930 | +2.971e-02 | exclusion |
| 4 | [−19/20, −91/100] | slab sm19o20_m91o100 | 25.771122805988 | +1.114e-02 | exclusion |
| 5 | [−91/100, −9/10] | slab sm91o100_m9o10 | 25.769683493481 | +9.697e-03 | exclusion |
| 6 | [−9/10, −22/25] | strip m090-m088（Lukács (7,6)） | 25.766265654633 | +6.279e-03 | exclusion |
| 7 | [−22/25, −17/20] | strip m088-m085（Lukács (7,6)） | 25.761930021253 | +1.943e-03 | exclusion |
| 8 | [−17/20, −41/50] | strip m085-m082（Lukács (8,6)） | 25.760813176470 | +8.266e-04 | exclusion |
| 9 | **[−41/50, −187/250]** | **HP m∈[−9/10,1]（兜底；a5 条带 4 行全 blocked）** | 25.759445973097 | **−5.406e-04** | TTP-covering |
| 10 | [−187/250, 1] | typed cap m0748 (8,6)（两引擎取最优；a5 M8 rung 25.759558052177 更弱） | 25.759571185601 | −4.153e-04 | TTP-covering |

- **拼合纪录（v2 判定，未变）**：assembledRecord = **25.759445973097478**
  （精确分数 `47517790735835014335570/1844674407417822803119`；瓶颈＝区域 9
  的 HP 片）。判定链＝10 原子区域（5 slab＋3 旧条带＋洞（HP）＋cap）以精确
  Fraction 取 min；exclusion 8 片全部 > E\*（Fraction 严格）、TTP-covering
  2 片（HP＋cap）≤ E\*+1e-6。
- **a5 cap（hermite_cap.json）**：M7 25.758799100032 / M8 25.759558052177
  （pdOPT 认证，E\*−4.288e-4）——**两档均弱于旧 typed cap 25.759571185601**
  ⇒ cap 片仍取旧证书（两证书都在盘可 --verify-cert，账本取大界；
  endgame.json `round6Inputs.hermite_cap` 记对照）。
- 被引证书清单＋每份重验命令：`endgame.json /citedCertificates`（10 份：
  5 slab＋3 旧条带＋cap＋HP）；本轮 `--reverify-certs` 进程外重验全过
  exit 0（cap 24.0s / slabs 9.4–9.9s / strips 9.5–49.8s / HP 重放逐位一致
  / l3、l6 账本幂等重跑门 exit 0；总 177.6s）。

## v2.2 边界点衔接复核（预想 13 点 → 实际 11 点，如实）

Round 5 计划若三片 a5 条带翻正，洞将按 [−41/50,−79/100] /
[−79/100,−153/200] / [−153/200,−187/250] 三分，分区为 13 区域 14 边界点；
**实际本轮 a5 条带 4 行全部 blocked（§v2.3）⇒ 洞保持单一区间**，分区为
10 区域、**11 个边界点**（升序）：

```
−1  −99/100  −97/100  −19/20  −91/100  −9/10  −22/25  −17/20  −41/50  −187/250  1
 #1|#2      #2|#3     #3|#4    #4|#5    #5|#6  #6|#7  #7|#8  #8|#9   #9|#10    #10|
```

关键衔接（逐点核对，`endgame_chain.py` Fraction 断言机器验证排序后端点
逐一相等、起点 −1 终点 1）：

- **−9/10（slab↔条带，＝HP 域下端）**：slab #5 上端＝条带 #6 下端。
- **−41/50（条带↔洞）**：#8 上端＝洞 #9 下端。a5 m082-m079（M8 认证
  25.759708213619 = E\*−2.783e-4）**未翻正**，洞侧记账仍取 HP（保守）。
- **−187/250（洞↔cap）**：#9 上端＝#10 下端＝cap 切口 < m\*＝−0.7475605
  ⇒ cap 域含 TTP。
- **+1**：cap 域右端（m ≤ 1 自动成立）。

## v2.3 三步拼合推理（v2 更新）

1. **分类**：任意 9 点单位球面构型 X，m(X) ∈ [−1,1] 落入 10 区域之一。
2. **逐区域下界**：X ∈ 区域 r ⇒ E(X) ≥ bound_r。区域 1–8（exclusion）由
   slab/条带证书排除（bound > E\*，Fraction 严格）；区域 9（洞）唯一已入账
   覆盖片＝HP（25.759445973，全分区最弱）；区域 10（cap 域）＝两引擎最优
   cap 证书（25.759571186）。a5 Hermite 引擎本轮在 cap 与三片受阻条带上
   的认证值全部弱于既有界（cap M8 −1.31e-5；条带 4 行 blocked，其中仅
   m765-m748 较旧 (7,6) 尝试 +7.45e-4 但仍 E\*−5.23e-4）——**不改变任何
   区域的记账值**。
3. **合取**：E(X) ≥ min_r bound_r = **25.759445973097478**（HP 片）。
   收尾链（裁决 D1 主链 L2→L3→L5→L6）若闭合则把 cap 区域界抬到 E\*
   ⇒ 全空间 E ≥ E\*；本轮重试判定 **closed = false**（blocking = L0、L3，
   见 v2.4）。

## v2.4 洞与 wouldBe 的处置（v2）

- **洞 [−41/50, −187/250]**：维持 HP 兜底。a5 blocked 4 行的带数值
  （25.759708213619 / 25.759471667086 / 25.759463585921（M8）＋canary
  25.758711674316（M7））是有效下界但**无存档证书**（正裕度断言 exit 1
  不落证书），不参与拼合 min。反事实注记（2026-10-06 R6 复核勘误，精确
  Fraction 重算）：若 4 行全部入账，按「原子胞元取覆盖证书最大界」口径
  洞将三分，三片 M8 值均高于 HP ⇒ assembledRecord 升至
  25.759463585921285、瓶颈片换为 m765-m748 a5 M8（+1.761e-5，仍
  E\*−5.229e-4）——**纪录值与瓶颈片会变**，但瓶颈仍留在洞内、closed 仍
  false、缺口量级不变（−5.41e-4→−5.23e-4）；旧句「最弱 25.7587 < HP」
  仅对 M7 canary 成立，且 canary 被同片 M8 支配、与入账无关。Lukács
  口径的旧 best_certified_attempt 同口径保留在 endgame.json
  `strips.oldBlockedSuperseded` 对照（旧三值中仅 m765-m748 的 25.758718
  低于 HP，其单独入账才确实不改纪录——§2 该句维持原文）。
- **wouldBe 口径更新**：Round 4 的 `wouldBe_if_all_strips_positive`（＝cap
  证书值 25.759571186）在条带翻正假设下才有意义，本轮未触发且不再是最终
  目标；endgame.json v2 改记 **`wouldBe_if_chain_closed = E\* =
  25.759986531**（closed=true 时 cap 域经 D1 主链抬到 E\*，
  assembledRecord ≥ E\*）——这是「拼合即证明 E ≥ E\*」的唯一剩余路径。
- **L4（邻型计数）不在关键路径**（裁决 D1）：账本 L4 记
  onCriticalPath=false（备选离散路线），closed 合取不含 L4；理由引用
  decisions.md §1-D1（L5 已严格＋klt 研读自认 L4 适配版未成形＋成本权衡）
  与回滚点（D1 条件已触发 ⇒ campaign 第 2 轮首选任务＝L4 双轨道计数）。

## v2.5 收尾链八组件快照（endgame.json endgameChain，v2 口径）

| 组件 | 状态 | 关键数字（出处） |
|---|---|---|
| L0 条带 [−1,−0.748) | **blocked** | 洞 [−41/50,−187/250] 无证书（HP 兜底 E\*−5.41e-4）；a5 4 行 blocked（最接近者 m082-m079 M8 ＝ E\*−2.78e-4） |
| L1 cap | **已严格** | 旧 typed m0748_M8（ΔE=4.1535e-4 精确）；a5 M8 25.759558052 在盘更弱（两引擎取最优） |
| L2 强制 | **已严格** | ε_forcing = 4.153454e-4 精确 Fraction（l2_rigorous.json，11 asserts 全真） |
| L3 解析谱管 | **blocked** | D7：C_min=1.874e-11 vs 需 1.2128；口径(a) ρ_capped=0.644725833（=1−ν₆ 平凡值）；闭链 ε\*＝L3 6.42e-15 / L5 5.50e-13 / L6 4.89e-16 |
| L4 邻型计数 | 备选（D1） | onCriticalPath=false；理由引用 decisions.md §1-D1 |
| L5 Procrustes | **已严格** | C=14.878732094961943、δ_max=0.17124089749729504（l4.json，三负对照全触发） |
| L6 管内二次增长 | **已严格（小半径）** | rigorous r\*=0.003359199152、μ∈[0.0021869607,0.0021869622]>0（l6_intube.json；目标 0.07601 本方法不可严格化，如实） |
| L7 排除/拼接 | **已记账** | 本文件 v2＋endgame.json 机器断言（条件装配，前提＝L0–L6 全绿） |

**closed = false**（= 关键路径 L0,L1,L2,L3,L5,L6,L7 合取；L4 按 D1 不入）。

## v2.6 诚实边界（v2 增补）

- a5 证书与 a2/a4 同为「严格数值层」（精确 Fraction＋LDLᵀ＋进程外
  --verify-cert），未过 Lean 内核；Hermite minorant 的 φ ≥ M 是区间算术
  证书（hermite_probe.json `rigorous_minorant`）。
- L6 严格半径 0.0033592 ≪ 公式值 0.07601（22.6×）——「已严格」指该半径
  内二次增长成立，非目标半径；闭合链对 L3/L5 的 d_P 预算因此收紧到
  0.0034（l3 口径(b) ε=1e-11 时 d_P 上界仍高 ~3 个数量级）。
- E\* 仍是三源校验参考值而非已证最优；全部与 E\* 比较语义为「与参考值
  不矛盾」。
- 本节是账本的说明书；数字权威来源是 endgame.json 与 certificates/ 的
  JSON，两处不一致以后者为准并视为本文件 bug。
