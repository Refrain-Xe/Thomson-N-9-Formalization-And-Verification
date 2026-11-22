# 表 A（Stage B 结构定理层）Lean 化推进留痕 — R12 r12b

任务：`r12b-tablea-lean`（D49 裁决 2；与 r12a「M1 Lean 全链」并行，文件面零交叠）。
日期：2026-10-10。门：`numerics/bounds/r12_tablea_gate.py`（seed 20261014，CWD 无关，
PATH 前置 `~/.elan/bin`）。本件 heavySolves=0（零求解、零 SDP、零证书数值改动）。

## §0 摘要

表 A（`notes/stageb-scope.md` §2）六件中的**首两件已落**，载体
`formal/lean/ThomsonN9/TableA.lean`（仅 `import Mathlib`；不 import 仓内解件、
不被其 import；不触 `Solution.lean`／`scripts/check.sh`／`lakefile.toml`）：

| # | 件 | 定理／定义 | 证法 | 状态 |
|---|---|---|---|---|
| A5 | L2 强制恒等式 | `ThomsonN9.TableA.l2_eps_forcing_identity` | `norm_num`（ℚ 字面量精确算术） | **已落** |
| A2′ | 引理 4.1 正性件 | `dfactorialOdd`／`phiDeriv`＋`phiDeriv_pos`＋`hasDerivAt_phiDeriv` | 幂／根／商求导链直接计算 | **已落（两引理）** |
| A1 | 三点恒等式 | — | — | 未落（§5） |
| A3 | typed 组合恒等式 | — | — | 未落（§5） |
| A4 | S₃ 商展开 | — | — | 未落（§5） |
| A6 | Lukács·Markov–Lukács 平方表示 | — | — | 未落（§5） |

三定理经 `#print axioms` 核验公理集恰 ⊆ `{propext, Classical.choice, Quot.sound}`
（无 `sorryAx`；NC1 注入 sorry 实证必被拦）。

## §1 A5：L2 强制恒等式（`l2_eps_forcing_identity`）

命题（ℚ 上精确）：

```
(1 + R2max) · (E* − certified) = ε_forcing
```

四 ℚ 字面量逐字节取自 `numerics/bounds/results/l2_rigorous.json`（M9 口径，
cap 证书 `certificates/n9-stage-a4-typedcap-m0748_M9.json`，campaign-2 R7B f05af76）：

| 常数 | json 字段 | 值（精确分数） |
|---|---|---|
| `E_star` | `E_star.value` | `25759986531/1000000000`（十进制主口径，D28 裁决 3） |
| `certified` | `certificate_rebuild.certified_recomputed` | `22879…4375/8881…1526`（86 位分子；与 `claimed_bound` 逐位相等，json `bitwise_equal_to_claimed=true`） |
| `R2max` | `certificate_rebuild.R2max_exact` | `1306…0763/4440…0000`（77 位分子） |
| `eps_forcing` | `eps_forcing.exact` | `6230…3153/4440…0000`（89 位分子；float 1.4030566524531613e-4） |

证明：`norm_num`——Lean elaborator 侧 Rat 精确算术，最终字面量等式由内核检查。
双侧证结构：Python 侧先证＝json `eps_forcing.identity_check.holds=true`
（`l2_rigorize.py` Fraction 精确重放）；Lean 侧本件独立重证（不信任 json 数值，
四分数以字面量直书源码，门 G5 反向核对字面量 == json 重读值）。
语义定位：这是 L2 强制链 `λ_cls ≤ (1+R2max)·E − e_dy + defl` 的**恒等式锚**
（表 A5；stageb-scope §2「有理恒等式 field_simp/ring」形态的 norm_num 实现），
不是 E ≤ E* 类不等式——`E*` 此处为三源校验参考口径。

## §2 A2′：引理 4.1 正性件（`dfactorialOdd`／`phiDeriv`＋两引理）

定义（源码 `TableA.lean`）：

```lean
def dfactorialOdd : ℕ → ℚ
  | 0 => 1
  | m + 1 => (2 * m + 1) * dfactorialOdd m          -- (2m−1)!! = 1·3⋯(2m−1)

noncomputable def phiDeriv (m : ℕ) (t : ℝ) : ℝ :=
  (dfactorialOdd m : ℝ) / Real.sqrt ((2 - 2 * t) ^ (2 * m + 1))
```

（Python 侧镜像：`numerics/bounds/r9_v2iv_reverify.py:97-104` 的
`dfactorial_odd`／`inv_sqrt_pow_iv` 符号递推。）

两引理：

* `phiDeriv_pos (m) (t) (ht : t < 1) : 0 < phiDeriv m t`
  —— `t<1 ⇒ 2−2t>0 ⇒ √((2−2t)^(2m+1))>0`，分子 `(2m−1)!!>0`（对 m 归纳）。
* `hasDerivAt_phiDeriv (m) (t) (ht : t < 1) : HasDerivAt (phiDeriv m) (phiDeriv (m+1) t) t`
  —— 表 A2 公式核：`φ^{(m+1)}` 是 `φ^{(m)}` 的导数。

**证明法与任务书措辞的差异（留痕）**：任务书称 hasDerivAt_phiDeriv 为「归纳核心」。
数学上该事实对每个 m 可由幂／根／商求导链**一步直接算出**
（`HasDerivAt.pow` ＋ `HasDerivAt.sqrt` ＋ `HasDerivAt.div` ＋
`HasDerivAt.congr_deriv`，指数 `2m+1−1 = 2m` 于 ℕ 恒成立），无需对 m 归纳；
Lean 实现采用直接计算（更短、更强：不依赖归纳假设）。「归纳核心」理解为
公式族对 m 递增的结构核心（φ 的各阶导数逐阶闭环），非证明技术选择。
`phiDeriv_pos` 的分子正性子件仍用对 m 的归纳。

**范围边界（按任务书）**：插值误差公式本体
`φ − H = φ^{(m)}(ξ)/m! · ∏(t−ν_k)² ≥ 0` 的 ξ 存在性后置，不在本件；
本件只落「正性核心」（φ^{(m)}>0）与「导数递进核」（(φ^{(m)})′ = φ^{(m+1)}）。

## §3 验收门 `numerics/bounds/r12_tablea_gate.py`

seed 20261014（惯例记档；全确定性无随机路径）。CWD 无关（路径自 `__file__` 推导）。
PATH 前置 `~/.elan/bin`。全部子命令 ≤10 min（单文件 elaboration 实测 ~4 s，
含 NC 的两次额外编译全门实测见账本 `results/r12_tablea_ledger.json`）。

| 门 | 内容 |
|---|---|
| G0 | 账本在场＋受控字段（seed==20261014、heavy_solves==0、自有四件在清单） |
| G1 | 文件所有权守卫：`git status --porcelain` 与 `git diff HEAD --name-only` 的全部路径 ⊆ 自有四件（冻结件任何改动即被拒）。自跑专用放行：`R12B_G1_ALLOW_FOREIGN=p1,p2` 显式放行 r12a/r12c 并行在途件（逐项响亮打印；验收运行不设 ⇒ 字面严格，提交后树净恒过） |
| G2 | 单文件 elaboration：`lake env lean ThomsonN9/TableA.lean` exit 0、输出无 error/sorry（**不整库 build**，规避 r12a 并行在途态干扰） |
| G3 | 公理：TableA.lean 先编译为 olean 落 `formal/lean/.lake/build/lib/lean/ThomsonN9/TableA.olean`（gitignored 构建产物位，`lake env` 的 LEAN_PATH 原生可解析），/tmp 检查件 `import ThomsonN9.TableA`＋`#print axioms` 三定理——公理集 ⊆ 三标准公理、无 `sorryAx/ofReduceBool/ofReduceNat/trustCompiler` |
| G4 | 语句 regex：import 行恰 `[import Mathlib]`；两定理名＋命题形状锚（A5 的 `1 +`／差因子／RHS 单分数结构；A2′ 的 `HasDerivAt (phiDeriv m) (phiDeriv (m+1) t) t` 与 `0 < phiDeriv m t`）；两定义锚；**非交叠守卫**（`Solution.lean`/`ThomsonN9.lean`/`lakefile.toml`/`scripts/check.sh` 源码零 `TableA` 引用） |
| G5 | 离线精确复核（stdlib Fraction）：A5 四分数自 json 重读重析、重算恒等式、并与源码 regex 抽取的 ℚ 字面量逐分量（分子/分母）比对（并核 json `identity_check.holds==true`）；A2′ 平方化判据 `(phiDeriv m t)² == df²·(2−2t)^(−(2m+1))` 于 m=0..8、t=−7/4 精确成立——左端由源码字面量（递归基/步、`(2−2t)`、指数 `2m+1` 解析值）驱动，右端用独立实现的 `(2m−1)!!` 与 `2−2t` |
| NC1 | 注入 sorry 必被 G3 拦：/tmp 副本 A5 证明改 `sorry` → 独立编译（`lean --root`＋LEAN_PATH 前置副本目录）→ 公理检查必现 `sorryAx` → G3 判定逻辑必 FAIL |
| NC2 | 篡字面量必被 G5 拦：/tmp 副本两篡——(a) A5 ε 分子末位数字＋1；(b) `dfactorialOdd` 递归基 `1→2`——G5 对应检查必 FAIL（原文件 sanity PASS） |

## §4 方向取舍与裁决留痕（本件内留痕，不进 decisions.md——依据：
D49 r12a/r12b 文件面零交叠约束＋任务书产出清单不含 decisions.md；
替代案＝追加 decisions.md 新小节，因与 r12a 并行写同一文件有覆盖风险被否。

* **D-r12b-1（命名）**：`(2m−1)!!` 的 Lean 定义名取 `dfactorialOdd`（camelCase，
  沿仓内 `Solution.lean` 惯例）；任务书括注 `dfactorial_odd` 为 Python 侧名
  （`r9_v2iv_reverify.py`）。门按 `dfactorialOdd` 解析（自洽）。
* **D-r12b-2（A5 证法）**：`norm_num`（任务书「norm_num/decide 级」二选一取前者；
  首过即成，elaborator Rat 算术＋内核可检；未再试 decide——无必要）。
* **D-r12b-3（A2′ 证法）**：直接计算替代对 m 归纳（§2 差异留痕）。
* **D-r12b-4（G3 olean 落位）**：编译入 `formal/lean/.lake/build/lib/lean/ThomsonN9/`
  ——gitignored 构建产物位、`lake env` LEAN_PATH 原生解析 `import ThomsonN9.TableA`；
  替代案（/tmp 独立 LEAN_PATH 前缀）用于 NC1 副本，正身用 lake 原生路径。
* **D-r12b-5（G1 自跑放行）**：G1 字面严格＋显式环境变量放行并行在途件（§3），
  避免并行会话未提交件误伤自跑；验收运行不设 ⇒ 严格。

## §5 表 A 余件与依赖序（未落部分，沿 stageb-scope §2）

| # | 件 | 数学形态 | 仓库地基 | Lean 形态预估 |
|---|---|---|---|---|
| A1 | 三点恒等式 | KLT (4.5) 型：Σ_84 λ_cls + Σ_all == ΣH − e_dy 对任意有理 Gram 三点组逐项成立 | `r9_s3_rederive.py:717-749`（随机有理构型 3 trial 精确 ==0，seed 20261011）；`typed_ladder.py` K_cols/sos_sum | `ring`/`Finset.sum` 重排；系数 ℚ 常数 |
| A3 | typed 组合恒等式 | 轨道计数配平（3·1/6·9/1·27＝84 类）与 ℓ₁ 装配 | `typed_ladder.py:229-300` QuotientMaps counts | 有限枚举 `decide`／显式计数引理 |
| A4 | S₃ 商展开 | FRing (u,v,t) 分次单项式 D=16 → Q_k 递推 K=6 → Y_cols 271 列 → share_lp/GM_OF/lam | `r9_s3_rederive.py` 全链自写第二实现（stdlib only）；`typed_ladder.py:275-285` | 多项式环上显式线性代数（系数 ℚ） |
| A6 | Lukács·Markov–Lukács 平方表示 | [a,b] 上非负多项式 p = s² + (t−a)(b−t)·u²（2d 与 2d+1 两型）；分段 minorant σ 族构造 | `tube_probe.py:13,25`（σ 族先例）；`strips_final.py` 消费 | 显式平方和展开（ℚ 系数直接验证） |

依赖序（stageb-scope §2 不变）：`M0 ─(独立)→ A1…A6（互相独立，可与 M1 并行）→ M1 →
B1…B6（解析几何件）`。本件（A5/A2′）先行落地不改依赖序；A2′ 的 ξ 存在性半件
（插值误差公式本体）建议随 A1 一并处理（同为「定理陈述＋数据核对」型）。
**不承诺条款不变**：`thomson_nine`／`thomson_nine_unique` 依赖 Stage A 闭合
（L0 洞片＋L3 谱管；L3 现状永久开放 dead-at-(9,6)，D24/D25），
表 A 推进对二者不构成承诺。

## §6 复现

```bash
cd thomson-n9
python3 numerics/bounds/r12_tablea_gate.py        # 全门（exit 0 = 过）
# 验收命令原样（CWD＝仓库根；命中仓内嵌套 CWD 兼容包装器→真实门）：
python3 thomson-n9/numerics/bounds/r12_tablea_gate.py
# CWD＝campaign 根（…/八电子在球面的分布）时同一命令直接命中真实门。
# 并行会话在途件未提交时的自跑（仅 G1 放行，其余门不变）：
R12B_G1_ALLOW_FOREIGN=numerics/bounds/endgame_gate.py,numerics/bounds/r12c_closure_gate.py \
  python3 numerics/bounds/r12_tablea_gate.py
```

**验收路由返工留痕（初验 exit 2 实录，沿 R10A 0087eab 先例）**：工作流以
CWD＝仓库根运行验收命令 `python3 thomson-n9/numerics/bounds/r12_tablea_gate.py`
时，相对路径解析成 `thomson-n9/thomson-n9/…` 不存在（exit 2）。修复＝补仓内
嵌套 CWD 兼容包装器 `thomson-n9/numerics/bounds/r12_tablea_gate.py`（runpy 按
真实门路径执行、exit code 原样传播；嵌套目录下 r7–r11 各门包装器齐备系
R7B/R7C/R8C/R9C/R9D/R10A/R10D/R11D 先例）。门内容（G0–G5＋NC1/NC2）零改动；
三路由亲跑 exit 0（仓库根×2＋campaign 根）。

期望尾行：`[gate] PASS（…s）——exit 0`。单文件 elaboration／olean 编译／公理检查
均不整库 build，不触碰 `ThomsonN9.lean`／`ThomsonN9/Solution.lean`／
`ComparatorChallenges/`／`lakefile.toml`／`lake-manifest.json`／`lean-toolchain`／
`scripts/check.sh`（G1＋G4 非交叠守卫机器化保证）。

---

# §7 A3＋A4（R13 / r13a）——typed 计数恒等式＋S₃ 商展开结构核

任务：`r13a-tablea-a3a4`（D52 裁决 1；与 r13b「A6」／r13c「A1」并行，文件面
零交叠）。日期：2026-10-10。门：`numerics/bounds/r13_a3a4_gate.py`
（seed 20261015，CWD 无关，PATH 前置 `~/.elan/bin`；仓内嵌套 CWD 包装器
`thomson-n9/numerics/bounds/r13_a3a4_gate.py` **随门首发**——5237fe5「验收
exit 2 返工」教训前移，三路由首次自跑即全通）。本件 heavySolves=0（零求解、
零 SDP、零证书数值改动；0.037 当量全额留储）。

载体两件各自独立成模块（均仅 `import Mathlib`；不 import 仓内解件／先行
`TableA.lean`，不被其 import；不触 `Solution.lean`／`M1Data.lean`／
`scripts/check.sh`／`lakefile.toml`，G4 非交叠守卫机器化核验）：

* `formal/lean/ThomsonN9/TableA3.lean`（namespace `ThomsonN9.TableA3`）
* `formal/lean/ThomsonN9/TableA4.lean`（namespace `ThomsonN9.TableA4`）

## §7.1 A3(a)：typed 分桶计数（显式枚举表＋decide）

编码：`types : Fin 9 → ℕ := fun i => i.val / 3`（TYPES=(0,0,0,1,1,1,2,2,2)）；
`allTriples := Finset.univ.filter (i<j<k)`（每个 3-点集恰一次，共 C(9,3)=84）；
`bucket p := sort3 (types i, types j, types k)`（非降序类型三元组——与
`typed_ladder.py`/`r9_s3_rederive.py` 的 10 类 `full_classes` 键同一口径）；
`bucketCount b := (allTriples.filter (·.bucket = b)).card`。

七条定理（全部 `decide`，`card_allTriples`/`image_buckets`/`bucket_partition`
配 `maxRecDepth 1000000`——729 元积 univ 的内核归约深度；无 `native_decide`
故无 `ofReduceBool` 之虞）：

| 定理 | 内容 |
|---|---|
| `card_allTriples` | `allTriples.card = 84` |
| `bucket_table` | 显式枚举表 `[1, 9, 9, 9, 27, 9, 1, 9, 9, 1]`（字典序 10 类） |
| `image_buckets` | 完备性：image 恰为 10 类集 `classesSet` |
| `bucket_partition` | 分拆求和 `∑_桶 bucketCount = 84`（`Finset.card_eq_sum_card_image`） |
| `orbit_totals` | 轨道小计：AAA 三桶和＝3·1、AAB 六桶和＝6·9、ABC＝1·27 |
| `a3_typed_counting` | 主定理（上述全捆绑＋配平 `3·1+6·9+1·27 = 84`） |
| `a3_l1_normalization` | 见 §7.2 |

## §7.2 A3(b)：ℓ₁ 装配归一化恒等式（norm_num）

`3·c_A + 54·c_B + 27·c_C − 9·ΣF⁽⁰⁾ − e = 0`（ℚ 精确），五字面量取自 M9 证书
`certificates/n9-stage-a4-typedcap-m0748_M9.json`（blocks.c_A=0、c_B=
140609170236263/281474976710656、c_C=20717/7599824371187712、e=
7250752630179179/281474976710656、ΣF⁽⁰⁾=9503960072215/70368744177664＝9×9
F0 全 81 元素 Fraction 和；设计师探针 `/tmp/r13_probe_gen.py` 先验 ==0 精确，
本件 Lean 内核 `norm_num` 复证）。系数 3/54/27 即 §7.1 的轨道计数配平
（3 类×1、6 类×9、1×27），54·c_B 的 54＝6·9。门 G5 自
`results/r9_s3_rederive.json` 重读证书链（`inputs.certificate_is_sole_derivation_
input=true`）→ 重读 M9 证书 → 81 元素重加 → 重算恒等式 → 与源码语句
**空白归一后逐字符模板比对**（比 r12 门「四分数 sorted 比对」更强：结构＋
字面量一并钉死）。

## §7.3 A4：S₃ 商展开结构核

* `def Q : ℕ → ℚ → ℚ → ℚ → ℚ`：三臂递推 `Q₀=1`、`Q₁=t−u·v`、
  `Q_{j+2}=2(t−u·v)·Q_{j+1}−(1−u·u−v·v+u·u·v·v)·Q_j`（与
  `sdp_bound.py:176 build_Q` 的 `Q_{k+2}=2(t−uv)Q_{k+1}−(1−u²)(1−v²)Q_k`
  同一数学，ω 写展开形）。
* `Q_symm : ∀ m u v t, Q m u v t = Q m v u t`：`Nat.strongRecOn` 强归纳
  （0/1/j+2 三态 `rcases`），步骤纯 `ring`——即 r9 档案
  `structural_checks.Q_uv_symmetric_all_k` 的内核版。
* `Q_zero…Q_five`：k≤5 显式形状（项数 1/2/6/10/19/27），`simp only [Q]; ring`
  （递推一次性全展开后 ring 收口；Q₅ 度 11 仍亚秒级）。
* `ycol_count : ∑ k ∈ Finset.range 6, (9−k)^2 = 271`（decide；K=6、M=9 的
  未对称化核列 Y[k,a,b]=u^a v^b Q_k 计数，r9 `sizes.Y_cols=271`）。
* **stretch（已落）**：`Kcol_two_three_one`——非平凡列 (k,a,b)=(2,3,1) 的
  `K_col = −2(Y + Y^{(u,t,v)} + Y^{(v,t,u)})` 完全展开恒等式
  （`simp only [Kcol, Ycol, Q]; ring`；`Ycol`/`Kcol` 为求值形状 def，
  换位语义 p↦p(u,t,v)/p↦p(v,t,u) 与 `typed_ladder.py` `perm_maps[3]/[5]`
  一致）。271 列全符号装配明确不在件（数值面由 r13c A1 实例＋Python 第二
  实现承担）。

## §7.4 验收门 `r13_a3a4_gate.py`（G0–G5＋NC1/NC2）

G0 账本（seed 20261015、heavy_solves=0、自有七件在清单）／G1 所有权（含
M9 证书与 `r9_s3_rederive.json` 两份只读输入件的显式 git diff 守卫）／
G2 逐文件 elaboration（≤600s 各）／G3 olen＋16 定理公理恰三标准／G4 语句锚
（A3 20 锚＋A4 18 锚＋六文件零 "TableA3/TableA4" 非交叠守卫，含
`TableA.lean`——R12 先行件同样不得引用本件）／G5 离线精确（A3 证书链模板
比对＋84 分桶独立复算；A4 内置 ℚ 表达式求值器（+,-,*,^）驱动：def 三臂
字面量重构×5 非对称有理点×k≤5 对拍独立第二实现（多项式稀疏 dict，ω 用
(1−u²)(1−v²) 乘积形独立构造——与源码展开形不同路径）、六条形状 RHS 文本
求值对拍、ycol 独立复算、Kcol(2,3,1) 对拍）／NC1 注入 sorry 必现 sorryAx／
NC2 双篡（c_B 分子＋1；Q_two 系数 4→5）必被 G5 检出。

## §7.5 证法取舍留痕（D-r13a-1…5，本件内留痕；decisions.md 另录 D53）

* **D-r13a-1（types 算术化）**：`types := fun i => i.val / 3` 替代矩阵字面量
  `![0,0,0,1,1,1,2,2,2]`——decide 快（Nat.div 小值内核可算）、G5 可 regex
  析除数独立复算；替代案（Fin.cons 字面量）解析面弱被否。
* **D-r13a-2（bucket 键＝非降序三元组）**：与 `full_classes` 10 类键同口径
  （排序消除同一多重集的重复键）；替代案（多重集/轨道商类型）表述重被否。
* **D-r13a-3（计数=decide＋maxRecDepth）**：`classes.map bucketCount = …`
  形态内核递归深度爆（100000 不够），改列表字面量十桶直陈＋分定理 decide；
  `bucket_partition` 走 `Finset.card_eq_sum_card_image`（名字与 r12 印象的
  `card_eq_sum_image` 不同——本 Mathlib 版实际名 `card_eq_sum_card_image`）；
  `exact h` 因 84=∑ 方向＋内核归约深度失败，改 `simpa only [bucketCount]
  using h.symm`。
* **D-r13a-4（A4 对称性强归纳）**：`Nat.strongRecOn`＋`rcases n with _ | _ | n`
  三态（0/1/n+2）；步内 `simp only [Q]` 双侧展开后 `rw [ih …]` 换原子＋
  `ring`——设计预案的「退 per-k ring」未启用（归纳一次成型，亚秒）。
* **D-r13a-5（G5·A4 对拍=求值器而非系数解析）**：Lean RHS 不解析成系数表
  （脆弱），而在 5 个非对称有理点求值对拍独立实现（单系数篡改在 5 generic
  点同时消失不可期）；def 侧则 regex 析字面量重构递推（篡系数沿递推传导）。
  NC2(b) 实证 Q_two 系数 4→5 于首点即失配（-1268/2205 ≠ -262/441）。

## §7.6 复现

```bash
cd thomson-n9
python3 numerics/bounds/r13_a3a4_gate.py        # 全门（exit 0 = 过）
# 验收命令原样（CWD＝仓库根；命中仓内嵌套 CWD 兼容包装器→真实门）：
python3 thomson-n9/numerics/bounds/r13_a3a4_gate.py
# CWD＝campaign 根（…/八电子在球面的分布）时同一命令直接命中真实门。
# 并行会话在途件未提交时的自跑（仅 G1 放行，其余门不变）：
R13A_G1_ALLOW_FOREIGN=<p1,p2> python3 numerics/bounds/r13_a3a4_gate.py
```

三路由亲跑 exit 0（仓库根真实门 28.6s／仓库根包装器 26.9s／campaign 根
27.9s）。期望尾行：`[gate] PASS（…s）——exit 0`。表 A 六件进度：A5/A2′
（R12）＋**A3/A4（本件）**已落；余 A1（r13c）＋A6（r13b）在途。

## §9 A1：KLT (4.5) 型三点装配恒等式 Lean 数据锚定实例（R13 / r13c）

**产出**（本节＝表 A 第 6 件 A1 落地留痕；D52 裁决 2 口径）：

| 件 | 内容 |
|---|---|
| `numerics/bounds/r13_a1_data.py` | 数据锚定生成器：只读消费 M9 cap 证书（经 `r9_s3_rederive.S3Assembly` 独立第二实现装配面）→ λ 三轨道表（各 449 非零 ℚ；3-smooth 分母 2^a·3^b——44/1347 非 dyadic，λ_AAB 10 个、λ_ABC 34 个分母奇部 3/27，源于 share_lp 的 /6、/3 除法；复算 D2 勘误降格原『全 dyadic』措辞）/s 表（271，全 dyadic）/h_AA·h_AB（各 17）/e 字面量＋对称块构型＋84 分类表＋729/36 计数＋参考值＋18 抽查点（seed 20261015）→ `results/r13_a1_data.json`＋两 Lean 文件（确定性生成，发射后回读 Lean 源码重建表逐位自检） |
| `formal/lean/ThomsonN9/TableA1Data.lean` | 表＋求值定理件（仅 import Mathlib）：7 表分块 def（≤64 项/块）＋恒等式所需 10 个立方点求值定理＋每表 3 个固定随机有理点抽查定理（共 18，堵 {0,1}³ 立方点篡改盲区） |
| `formal/lean/ThomsonN9/TableA1.lean` | 构型/分类/计数/恒等式件（import Mathlib＋ThomsonN9.TableA1Data，全仓唯一依赖）：`gX/gY/gZ` 点字面量→`gramI` 点积→`gramI_blk_fin`（G[i][j]=if ⌊i/3⌋=⌊j/3⌋ then 1 else 0，decide）＋`class84` 84 行显式分类表（完备性 `class84_complete`＋逐行 Gram 对账 `class84_gram_ok` 均 decide）＋λ 点计数 4 条（3/27/27/27）＋`cube9` 729 字面量表（枚举完备 `cube9_enum` decide）按 5 个 s-点折叠计数（162×4＋81，`s_counts_sum`==729）＋`pairs36` 36 字面量表按 2 个 h-类计数（9/27）＋三 sum 折叠（`sum_lam_eq/sum_s_eq/sum_h_eq`，norm_num）＋`a1_assembly_identity`（Σ_84λ+Σ_all==ΣH−e，norm_num 收口）＋三参考值定理 |
| `numerics/bounds/r13_a1_gate.py`（＋`thomson-n9/numerics/bounds/` 同名 CWD 包装器） | 验收门 G0–G5＋NC1/NC2/NC3（下表）；seed 20261015 |
| `numerics/bounds/results/r13_a1_ledger.json` | 账本（sha256/墙钟/公理面/负对照实录） |

**数学结构（对称块构型 X={e₁×3,e₂×3,e₃×3}，与设计师探针 /tmp/r13_probe_a6.py 逐项一致）**：
λ 求值点恰 4 个 (orbit,perm,point)——(AAA,id,(1,1,1))×3、(AAB,id,(1,0,0))×27、
(AAB,ut,(0,0,1)→λ_AAB(t,v,u)=λ_AAB(1,0,0))×27、(ABC,id,(0,0,0))×27；s 求值点恰
5 个全在 {0,1}³——(1,1,1)×81、其余四点各 162（和 729）；h 类 2 个——(AA,1)×9、
(AB,0)×27。参考值（Lean `sum_*_value` 定理字面量＝json＝Fraction 重放三方一致）：
sum_lam=4416585812995339/281474976710656、sum_all=1003797937752669/70368744177664、
sum_H=7841265097092597/140737488355328、e=7250752630179179/281474976710656，diff==0 精确。

**实现范式实测（D50-2 复现与两处新教训）**：表分块 def＋文件级 maxHeartbeats
1000000＋`simp only [表名,块名…]`＋norm_num——TableA1Data.lean 全文件
elaboration 131.8s、TableA1.lean 12.8s（零 error 零 sorry，55 定理公理全
⊆{propext,Classical.choice,Quot.sound}，decide 件为空公理集）。探针结论复核：
求值定理成本 ≈0（成本主导在 def 展开，~0.1s/项）；449 项单 def 默认心跳超时
的教训由分块消解。**新教训①**：kernel `decide` 不能算 ℚ（Rat 四则非内核
原语——`gramN`（ℚ 点积）的 decide 卡在 `Rat.add` 不可约）⇒ 决策层全部 ℕ 化
（`gramI` ℕ 点积、`sPtI` ℕ 点、计数 filter 全 ℕ），ℚ 层由 cast＋norm_num 收口
（`lamEval` 的 ↑(ℕ)→ℚ 强转经 norm_num 归一后与求值定理 syntactic match）。
**新教训②**：simp/norm_num 不能展开计算式列表（`List.range`/`flatMap` 链）
⇒ `cube9`/`pairs36` 用字面量表＋`cube9_enum`/`pairs36_enum` decide 对账真枚举
（完备性不断链）；`maxRecDepth` 提至 50000（729 元素 decide 递归深度）。

**抽查盲区堵法（D52 裁决 2）**：恒等式全部求值点在 {0,1}³ 立方上，立方点取 0
的 monomial 系数篡改不可检 ⇒ 每表（λAAA/λAAB/λABC/svec/hAA/hAB）3 个固定随机
有理点抽查求值定理（seed 20261015，分量 Fraction(rng.randint(-64,64),64)、表序
固定、λ/s 每点 3 分量 h 每点 1 分量；期望值 Python Fraction 独立算出，Lean
norm_num 独立重证）。抽查对账实测有牙：开发中 selfcheck 曾对 dict 误用 list 版
eval1（迭代到键 0..16 而非系数）致 json hAA/hAB 抽查期望值错而 Lean 定理对——
被门 G5(c) 当场拦下后修复（D-r13c-5 实录）。

### §9.1 验收门 `numerics/bounds/r13_a1_gate.py`

seed 20261015（确定性；抽查点为 seed 复放）。CWD 无关（路径自 `__file__` 推导）；
PATH 前置 `~/.elan/bin`。自跑实测全门 281.9s exit 0（Data 131.8s＋Main 12.8s
＋NC1 篡件编译＋NC3 篡件编译 12s 级＋G5 Fraction 全程）。

| 门 | 内容 |
|---|---|
| G0 | 账本在场＋受控字段（seed==20261015、heavy_solves==0、自有八件在清单） |
| G1 | 文件所有权守卫**三层放行**（D-r13c-8/D53-4 对齐）：①自有八件；②`R13C_G1_ALLOW_FOREIGN` 自跑逐件放行；③PARALLEL_FAMILY pattern 家族（r13a/r13b/r13d 在途交付件，逐项响亮打印）——三层外字面拦截；**M9 证书与 r9_s3_rederive.json 显式只读守卫**独立于放行集（git diff HEAD 空）。提交后树净 ⇒ 两层放行集皆空 ⇒ 等价字面严格 |
| G2 | 逐文件 elaboration ≤600s/文件（D52 裁决 4）：依赖序 `lake env lean -o` 编译 Data→Main，各 exit 0、无 error/sorry；olean 落 `.lake/build/lib/lean/ThomsonN9/`（gitignored）供 G3/主件 import 复用（不二次编译） |
| G3 | 公理恰三标准：**两文件全部 55 定理**（regex 枚举）#print axioms ⊆ {propext, Classical.choice, Quot.sound}（decide 件可为空集）、零 sorryAx/ofReduceBool/ofReduceNat/trustCompiler |
| G4 | 语句锚 36 条（两 import 面、7 表定义、10 立方点求值、gramI_blk_fin＋块结构形状、class84＋完备＋对账、计数 11 条、三 sum 折叠、恒等式名＋LHS/RHS 形状、三参考值定理）＋18 抽查定理计数；**非交叠守卫**（Solution.lean/TableA.lean/M1Data.lean/ThomsonN9.lean/lakefile.toml/check.sh 零 "TableA1" 引用） |
| G5 | 离线精确复核（Fraction）：(a) λ×3/s/h×2/e 七表自 M9 证书经 r9_s3_rederive 独立第二实现重算==Lean 源码 regex 解析==json 三方**逐位**；(b) 对称构型恒等式重放 diff==0（用 **Lean 解析表**＋门内独立重写分类/计数逻辑）且 Σλ/Σ_all/ΣH==json 参考值==Lean value 字面量；(c) 18 抽查点 seed 复放＋解析表/重算表**双实现**求值==定理字面量==json；(d) 计数枚举独立复算（λ 4 点 [3,27,27,27]、s 5 点 [162,162,162,162,81] 和 729、h [9,27]）==json==Lean 计数引理字面量 |
| NC1 | 注入 sorry 必被 G3 拦：/tmp 副本 lamAAA_at_111 证明改 sorry→独立编译（--root＋LEAN_PATH 前置）必现 sorry 警告＋公理集现 sorryAx（实测 {sorryAx,propext,Classical.choice,Quot.sound}） |
| NC2 | 篡 λ 表系数必被 G5/抽查拦：lamAAA_0 首项分子＋1→G5(a) 证书逐位比对检出（抽查求值兜底同在）；原文件双路 sanity PASS |
| NC3 | 篡构型点坐标必被 G2/G5 拦：gX 字面量 1→2→G5(b) 构型结构检查检出＋G2 篡改源 elaboration 失败且**首错即 gramI ↑i ↑j = if ↑i/3=↑j/3 then 1 else 0 被 decide 证伪**（首错命题断言，防假拦截） |

### §9.2 方向取舍与裁决留痕（D-r13c-1…7，沿 r12b §4 先例记本文件）

* **D-r13c-1（分件）**：表＋求值定理入 TableA1Data.lean、构型/分类/计数/恒等式
  入 TableA1.lean（主件 import 之）。依据：elaboration 成本集中在 def 展开
  （449×3＋271 项 ≈130s），主件纯 decide/norm_num 簿记 12.8s——隔离重件、
  主件轻而可读；替代案（单文件）实测预算内亦可（~145s）但放弃，取隔离性。
* **D-r13c-2（决策层 ℕ 化）**：Gram/sPt/计数全部 ℕ（点坐标 0/1 整数），ℚ 由
  cast 收口。依据：kernel decide 不能算 ℚ 四则（探针实证卡在 Rat.add 不可约）；
  替代案（ℚ gram＋native_decide）弃——native_decide 依赖 ofReduceBool 违 G3
  公理恰三标准。
* **D-r13c-3（字面量表＋enum 对账）**：cube9/pairs36 用字面量表＋decide 枚举
  完备引理，class84 用字面量表＋`class84_complete` 对账 `triplesAll`（真
  i<j<l 枚举计算式）。依据：simp/norm_num 不能展开 range/flatMap 计算链，而
  完备性必须锚到真枚举（否则字面量表与「全三元组」脱钩）。
* **D-r13c-4（NC3 拦截路径返工实录）**：首版 NC3 的 G2 拦截用 `lean --root
  /tmp` 重定位编译篡改件——报错实为 olean 解析失败（假拦截），门却叙述为
  「gramI decide 失败」（不诚实）→ 返工为 `lake env lean` 直编篡改源（import
  解析到真实 olean）＋首错命题断言（错误文本须含 decide 反证的 G 引理命题）。
  留痕教训：负对照的检出证据必须与声称的拦截机制严格对齐。
* **D-r13c-5（自查 bug 实录）**：r13_a1_data.py selfcheck 曾对 dict 误用
  list 版 eval1（`for c in coeffs` 迭代 dict 得键 0..16）→ json hAA/hAB 抽查
  期望值＝Σk·x^k（错）而 Lean 定理＝真值（对）。门 G5(c) 三方对账当场拦下，
  修复为显式 range(17) 取值表。此为抽查对账机制有牙的实证（非负对照、真实
  缺陷捕获）。
* **D-r13c-6（裁决留痕位置）**：任务书铁律要求裁决进 notes/decisions.md，但
  D52 裁决 4 对 r13a/r13b/r13c 三线要求文件面零交叠、且本任务产出清单不含
  decisions.md——沿 r12b D-r12b-4 先例留痕本文件 §9.2（r13d 收口可统一收编
  decisions.md）。替代案（直写 decisions.md）因并行会话同文件追加的覆盖风险
  被否。
* **D-r13c-7（G1 并行放行·首版）**：G1 字面严格＋`R13C_G1_ALLOW_FOREIGN` 显式
  放行 r13a/r13b 在途件（首版机制，r12b 先例）——**被首验证伪**，见 D-r13c-8。
* **D-r13c-8（首验返工实录·G1 并行家族放行，D53-4 对齐）**：首验 exit 1 实录＝
  工作流以验收命令（不设环境变量）运行时点 r13b 在途件 TableA6.lean 未提交被
  G1 字面严格拦下——环境变量放行对不设环境变量的验收命令无效（结构性缺陷）。
  r13a 同因先例（18f586b，D53-4 裁决）已确立 PARALLEL_FAMILY pattern 家族放行层
  ⇒ 本门对齐同款三层结构（①OWNED ②环境变量 ③pattern 家族〔r13_a3a4*/r13_a6*/
  r13d* 门/数据/账本/嵌套包装器及工作目录、TableA[0-9]*.lean 含分块子模块目录
  （r13b 实录建 TableA6/ 目录拆块）、notes/tablea* 笔记族、GAP-REPORT/PROGRESS
  收口文档〕），逐项响亮打印非静默；家族外路径仍字面拦截。三面探针实证（直调
  gate1_ownership）：家族内在途件放行 PASS＋家族外探针 numerics/bounds/
  zz_a1_foreign_probe.py EXPECTED-FAIL 必拦＋探针移除回 PASS。边界：TableA[0-9]
  不匹配 r12 冻结面 TableA.lean；certificates/references/endgame.json 不在集；
  两只读输入件守卫独立。替代案（弃）：等待 r13b 提交后树净再验——验收时序
  不受本会话控制，不可靠。

### §9.3 量级边界（如实）

随机构型全恒等式（84×449＋504×271≈23.5 万项）超出本轮 elaboration 预算
（D52 裁决 2，本节与 TableA1.lean 文档串均明示）；泛构型证据由 Python 侧
`results/r9_s3_rederive.json` 3 trial（seed 20261011，精确 diff==0）＋设计师
第 4 独立 trial（任意小有理构型，/tmp/r13_probe_gen.py）在档承担。Lean 件为
对称块构型精确实例＋18 随机点抽查；λ_full==λ_orbit∘P 的多项式级轨道置换一致性
（ring 于 449+449 项）留 stretch 未做（任务书允许、信息量低于构型实例）。

### §9.4 复现

```bash
cd thomson-n9
python3 numerics/bounds/r13_a1_data.py    # 生成器（json＋两 Lean 文件，确定性）
python3 numerics/bounds/r13_a1_gate.py    # 全门（exit 0 = 过；自跑 ~282s）
# 验收命令原样（CWD＝仓库根，经嵌套 CWD 包装器）：
python3 thomson-n9/numerics/bounds/r13_a1_gate.py
# 并行会话在途件未提交时的自跑（仅 G1 放行）：
R13C_G1_ALLOW_FOREIGN=numerics/bounds/r13_a6_data.py,... python3 numerics/bounds/r13_a1_gate.py
```

期望尾行：`[gate] PASS（…s）——exit 0`。两 Lean 件不整库 build、不触
`Solution.lean`/`TableA.lean`/`M1Data.lean`/`ThomsonN9.lean`/`lakefile.toml`/
`scripts/check.sh`（G1＋G4 非交叠守卫机器化保证）。

## §7.7 首验返工补记（D53-4：G1 并行家族放行）

**返工实录**：工作流首验（净树预期）时 r13c 在途件 `TableA1.lean` 尚未提交
（后其 b60b6c5 落定），G1 字面严格按设计拦截 ⇒ exit 1——与 R12B 自跑场景同因，
但验收命令不设环境变量 ⇒ 环境变量放行机制不足以过验收。修复＝G1 增第三层
放行：`PARALLEL_FAMILY` pattern 集（D52 任务切分的 r13b/r13c/r13d 交付件
家族：形式层 `TableA[0-9]*.lean` 及分块子模块目录〔R13 实录 r13b 曾建
`TableA6/` 目录拆块，纯文件 pattern 覆盖不到——返工中途实时撞见并泛化〕、
`r13_a1*/r13_a6*/r13d*` 门/数据/账本/嵌套包装器及其工作目录、`notes/tablea*`
笔记族、r13d 收口文档 GAP-REPORT/PROGRESS），逐项响亮打印非静默；家族外
任何路径（冻结件/certificates/references/既有 results·bounds 资产/
Solution.lean/M1Data.lean/lakefile/toolchain/check.sh/TableA.lean）仍字面拦截，
两只读输入件守卫不受放行集影响。

**牙齿双面实证（返工后重测）**：家族外探针 `numerics/bounds/aaa_zz_foreign_
probe.py` → G1 EXPECTED-FAIL 拦截 ✓；家族内在途件（TableA6.lean＋TableA6/
目录＋r13_a6_data.py＋results/r13_a6_data.json）→ 放行 PASS ✓。三路由复跑
全 exit 0（真实门 32.3s／campaign 根 32.3s／包装器 28.4s，r13b 在途件在场）。
提交后树净 ⇒ 放行集空 ⇒ G1 等价字面严格。**D-r13a-6（放行集边界）**：放行
按「任务家族 pattern」而非「任意 r13* 前缀」收窄（TableA[0-9] 不匹配 r12
冻结面 TableA.lean；certificates/references 全不在集）；endgame.json 等冻结
账本明确不放行（r13d 若重写属真改动，应响亮拦截而非静默放行）。

## §8 A6：Lukács·Markov–Lukács 平方表示件（R13 / r13b）

**产出**（自有 16 件，与 r13a/r13c 文件面零交叠；r13a/r13c 在途件经 G1 自跑
放行变量 R13B_G1_ALLOW_FOREIGN 或家族 pattern 放行——本门采用逐路径显式
放行＋冻结件 sha256 锚，口径见下）：数据件 `numerics/bounds/r13_a6_data.py`
（只读消费 M9 证书＋r9_s3_rederive.json 对账；产 8 块 L/D/主元正性/残差 33
系数带号/R2 两类/b²/ŵ/乘子族）→ `results/r13_a6_data.json`；Lean 件
`formal/lean/ThomsonN9/TableA6.lean`（总成）＋`TableA6/Gen.lean`（通用代数
层）＋`TableA6/{AA,AB}{0..3}.lean`（8 块）；门 `numerics/bounds/
r13_a6_gate.py`＋嵌套 CWD 包装器 `thomson-n9/numerics/bounds/r13_a6_gate.py`；
账本 `results/r13_a6_ledger.json`（本节）。

**四层定理（全部 #print axioms 恰 {propext, Classical.choice, Quot.sound}）**：
(i) 逐块 `stepsq_{b} : Σ_{k,l}[(L_kl·d_l−M_kl)²+(M_k ⬝ᵥL_l−S_kl)²]==0`（单次
norm_num）＋`entries_of_sumsq2` 逐项提取 ⇒ step1（L·diag(D)=M）/step2
（M·Lᵀ=S）⇒ `recon_{b} : L·diag(D)·Lᵀ = S`；(ii) `sig{b}_quad`：σ_i(y)=
v(y)ᵀSv(y)=Σ_j d_j·(Σ_k L[k][j]y^k)²——Gen.quad_of_recon 纯矩阵代数链
（dotProduct/mulVec/vecMul/transpose/diagonal，无数据展开）；(iii)
`p{AA,AB}_nonneg : ∀y:ℝ, 0≤y → y·y≤437/500 → 0 ≤ p_cls y`（√b 无理化；
乘子 1/y/(b²−y²)/y(b²−y²) 域非负＋d_j>0 字面量＋sq_nonneg＋Finset.sum_nonneg）；
(iv) `r2_reduction_{AA,AB}`：Σ_{j=0}^{33} sgn_j·(rhs_j−lhs_j)·(117/125)^j ==
R2_cls（ℚ norm_num；R2_AA=3889…6831/2220…0000、R2_AB=1306…0763/4440…0000
与 r9_s3_rederive.json R2_exact 逐位）＋`lhs_spot_{cls}_{1..3}` 抽查求值
（Σ_j lhs_j·y^j == p_cls(y) @ y∈{2/5,17/40,4/5}，seed 20261015）。

**证法取舍留痕（本件内留痕；D52 零交叠约束不进 decisions.md，沿 r12b 先例）**：
- **D-r13b-1（平方和折叠替代逐项 norm_num）**：任务书预设「L·D·Lᵀ==S 逐
  entries norm_num」实测不可行——17×17 单块逐项（fin_cases+norm_num，行分
  def 优化后）4m30s/块、8 块并行受 CPU 争用 >18 min，且 norm_num 于
  Finset.sum 符号指标的 VecLit 展开多路撞墙（探针 A/C/E/F/H/I/L/M 系列留
  /tmp/r13b_*）。改道**合并平方和**：Σ[(L·d−M)²+(M⬝ᵥL−S)²]==0 单次
  norm_num（22s/块）＋通用提取器 entries_of_sumsq2（sum_eq_zero_iff_of_nonneg
  两层+pow_eq_zero_iff）。信息量等价（ℝ 上平方和为零⟺逐项为零），陈述仍是
  精确 ℚ/ℝ 恒等式。**已知引擎怪象留痕**：同一文件内第二个大平方和 norm_num
  必快速失败（t4–t7 探针：字面量/序/maxRecDepth 均排除；t5/t6 定位为「文件
  内第二个大 sum-unroll norm_num」）⇒ 每块文件只放一个大 norm_num（step1+
  step2 合并）。
- **D-r13b-2（两步 L·diag=M、M·Lᵀ=S 而非直乘）**：直接 (L·diag d)·Lᵀ 展开
  在 sum 内引入 diagonal 的 ite（符号指标不可约），实测 >11 min 未过；两步
  分解把 ite 消灭在无和的 step1（mul_diagonal 逐项）。
- **D-r13b-3（(ii) 用矩阵代数链替代 ring 平坦展开）**：任务书预设 ring 展开
  289 项×8 块实测 elaboration 爆炸（>100 errors/63s）；quad_of_recon 以
  Matrix 引理链（mulVec_mulVec/dotProduct_mulVec/vecMul_vecMul/mulVec_transpose/
  mulVec_diagonal/vecMul_diagonal）一次证明、8 块实例化零成本——D50-2 平坦形
  范式的代数化替身。
- **D-r13b-4（lhs↔p_cls 系数级全恒等式不在 Lean 件）**：反diagonal 系数提取
  需逐 j 展开 ∑p∑q ite（33×289/块，估 >6 min/块）或多项式 ext+逐系数
  norm_num（同量级）；按 D52 裁决 2「随机点抽查」口径落 3 点/类抽查求值定理
  ＋门 G5·④ Fraction 全恒等式重放（Σ_j lhs_j y^j == p_cls(y) 精确，3 点；
  G5·①–③ 另有 (ii) 5 点/块、(iv) 全式重放）。gap 如实记录。
- **D-r13b-5（G1 冻结件守卫以账本 sha256 锚定）**：certificates/ 与
  numerics/bounds/results/ 不在 git 追踪面 ⇒ git diff 守卫不可用；账本
  frozen_sha256 记 M9 证书＋r9_s3_rederive.json 哈希，G1 逐跑比对（只读守卫
  有牙：篡证书必失配）。替代案（弃）：把两件纳入 git——越权改冻结面。

**门（r13_a6_gate.py，seed 20261015，CWD 无关）**：G0 账本；G1 所有权
（git status -uall/diff ⊆ 自有 16 件；自跑放行变量 R13B_G1_ALLOW_FOREIGN；
冻结件 sha256）；G2 分块 elaboration（Gen→8 块并行→总成，各 ≤600s，-o 产
olean）；G3 公理 46 定理 ⊆ 三标准（Lean 4 模块名非命名空间——裸名探针）；
G4 语句锚＋非交叠（Solution/M1Data/TableA/lakefile/check.sh 零 TableA6 引用）；
G5 Fraction 第三实现（LDLᵀ 独立重算＋主元全正＋json 逐分量＋(ii) 8 块×5 点
＋(iv) 两类＋抽查 3 点/类＋json↔源码字面量逐分量：8 块 S/L/M 行＋d＋lhs/
rhs/sgn＋R2_cls）；NC1 sorry 注入（块 olean 复用快路径重编总成→sorryAx）；
NC2 dAA0 首主元变号（G5·⑤ 拦）；NC3 lhsAA 篡分量（G5·⑤＋(iv) 数值双拦）。
自跑 PASS exit 0（383.3s）。

**边界如实**：H≤φ 于 [lo,1] 逐点优越性与一般 Lukács 存在定理不在本件
（umbrella docstring 明示）；heavySolves=0（elaboration/Fraction 非求解口径，
D52 裁决 5）；本轮 0.037 当量全额留储不动。

**§8 补记（D-r13b-6：G1 并行家族放行层，D53-4 对齐）**：r13a/r13c 首验实录
（18f586b/7ac3111）证明验收命令不设环境变量时姊妹线在途件必撞 G1 字面严格层
⇒ 本门 G1 补同款第三层 PARALLEL_FAMILY pattern（TableA[0-9]*＋r13_*＋
notes/tablea*＋GAP-REPORT/PROGRESS；TableA.lean 冻结面/certificates/references/
endgame.json 明确不在集）。10 例 pattern 单测＋家族外探针 zz_r13b_foreign_
probe.py 直调 gate1_ownership CAUGHT 亲验（验后即删）；补强后 campaign 根
验收命令原样终验 PASS exit 0（348.4s，/tmp/r13b_gateF.log）。

**§8 补记二（D-r13b-6 续：r13d 殿后面扩容）**：post-commit 复跑实测撞见 r13d
在途件（r13d_closure_gate.py×2＋GAP-REPORT/PROGRESS/decisions.md＋
endgame_gate.py M）——家族 pattern 初版 r13_ 不匹配 r13d（无下划线名）且
殿后面未含 endgame_gate.py（R12C 先例：收口轮按增补式扩展该门）⇒ 扩为
r13*＋上述殿后面；12 例 pattern 单测（TableA.lean 冻结面/endgame.json/
certificates/references/r9_* 均必拦）后，r13d 在途态 campaign 根验收命令
原样复跑 PASS exit 0（313.2s，六件放行逐项响亮打印）。

**§8 补记三（D-r13b-7：嵌套 CWD 包装器首验返工）**：工作流首验 exit 1
实录＝包装器首版误用 `parents[2]`（真实门在 parents[3]——r12b 5237fe5 先例
口径），解析回包装器自身 ⇒ runpy 无限递归；且首发前自测「包装器路由」实跑
CWD 停在 campaign 根、命中真实门（…/thomson-n9/numerics/…），包装器本体
从未被真正执行——验证盲区如实留痕。修复＝parents[3]＋逐级上溯自指守卫
（候选解析等于本文件即跳过，单测 REAL_GATE 无 thomson-n9/thomson-n9 自指）
＋本次以 CWD=仓库根实际命中包装器本体的路由亲验 PASS exit 0（323.5s，
gateW2）＋campaign 根验收命令原样复跑 PASS exit 0（339.9s，gateA2）。
教训（对齐 5237fe5 前移教训的再教训）：包装器路由验证必须核实入口文件
解析路径，不能只看 exit code。
