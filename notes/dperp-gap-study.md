# dperp-gap-study.md — R18B B5c 步骤 6 缺口研究件（反例核验＋块恒等式＋自举路线＋三路线评估）

任务锚：r18b-dperp-gap-study（R18B，campaign dwfrun-f9904baf 第 13 轮，
D77 裁决 2 的证据与方向供件）。定位：**零 Lean 件入库、零求解、纯 notes＋
/tmp 探针**（R15C/R16B/R17B 同款），与 R18A 文件集零交叠（不触
formal/lean/ThomsonN9/、不触 notes/tableb-lean.md、不触四账本/endgame.json
——只读未动）。数学内容四件：

- **(i) 反射族反例机器核验**（python stdlib Fraction 精确、确定性、seed
  20261018）：取有理 9×3 行单位满秩 X（有理球面点×9）＋Q̃ = diag(−1,1,1)、
  Y := X·Q̃，核验 G_Y == G_X 逐位（η=0、δ=0、β=0 ≤ 适用域全前提成立）而
  frob D_∥ = frob (X·(Q̃−1)) > 0 = σ₁·β——数值层书面证明步骤 6 隐含前提
  ‖D_∥‖ ≤ σ₁β 的机器反例（严格 Fraction 无浮点；对 l4.json 只评估不动文件）；
- **(ii) 块恒等式 Lean 探针**（/tmp，lake env lean 同栈）：E*(1−P₀) = Y*D_⊥ᵀ
  与 (1−P₀)*E*(1−P₀) = D_⊥*D_⊥ᵀ（纯环例，P₀ 面前提代入）；
- **(iii) σ₃(Y) 自举路线探例**：‖((1+A)ᵀ)*ᵥv‖² = v ⬝ᵥ ((1+B)*ᵥv) ≥
  (1−β)*(v⬝ᵥv)（二次型，行-CS 面）⇒ ‖Y*ᵥv‖ ≥ √(λ₃*(1−β))*‖v‖ −
  ‖D_⊥*ᵥv‖ 组装例（‖Y*D_⊥ᵀ‖ ≤ η ⇒ frob D⊥ ≤ η/σ₃(Y) 闭环条件研究）；
- **(iv) ½-Hölder 面与三候选无条件路线书面评估**：tr(D_⊥*D_⊥ᵀ) =
  tr(E*(1−P₀)) ≤ 3η 型 √η 界的 Lean 可行性、路线 A（σ₃(Y) 自举）/路线 B
  （E(I−P₀)=Y·D_⊥ᵀ 面）/路线 C（谱扰动 Weyl 型）各自依赖面、工程量档位与
  风险分级，给 R19 无条件化排期判断。

诚实口径（全文适用，R15C/R16B/R17B 同款）：
- **已跑**＝本会话在 thomson-n9/formal/lean 下亲跑且日志在 /tmp 留档（每条带
  路径）；Lean 探针＝`lake env lean` 编译验证（example/theorem），**探针编译
  通过 ≠ 证明完成**——本件不含任何证明本体入库；量纲判定＝Python 纯 Fraction
  精确算术（无浮点判定）；
- **未跑**＝本会话没有执行（如实标注，不做推断性『应该可以』）；
- 迭代史口径：/tmp 日志为**终版覆盖式**（Lean 探针 1/2 分别经 5/6 版迭代收敛，
  中间版不留档，诊断用 mini 件已清理），摩擦点清单为亲历记录（各节『摩擦』
  小节）；Fraction 脚本 2/2 版收敛（§i 一版定稿、§iii 闭环研究 2 版）；
- 本件不出现『本体入 Lean』类越权陈述——所有结论均系探针/研究性质。

版本口径：Mathlib @ **d13f23b723b8a846827a245b89c10fc7d3f11612**（本仓
formal/lean/lake-manifest 锚定），toolchain `leanprover/lean4:v4.34.1`
（/tmp/r18b_final_pass.log 亲验记录）。与 R15C 预研件、R16A/R16B/R17A/R17B/
R18A 探针同一 rev 同栈。Lean 探针 import 面＝Mathlib＋ThomsonN9.TableB5Core
＋TableB5Trace（探针 1）；探针 2 另加 ThomsonN9.TableB5Polar（R18A 已提交件，
import 只读——abs_quadform_le_frob 在库复用）。

零求解声明：本任务零求解（**heavySolves = 0**，字面锚）——零重求解、零 SDP、
零新数值证书；四账本（m9_campaign/m10_campaign/hermite_v2_campaign/
typed_ladder）、endgame.json、certificates/ 全部零触碰（只读未动），挑战件与
references/ 只读，l4.json 只评估不动（§i.5）。零 formal/lean/ThomsonN9/
写入——G1 守卫见 numerics/bounds/r18b_dperp_gate.py。

四件总览（三档判定一览）：

| 件 | 面向 | 三档判定 | 主证据 |
|---|---|---|---|
| (i) 反射族反例 | 步骤 6 隐含前提的机器反例 | **现成（一版定稿，C1–C9 全过）** | /tmp/r18b_counterexample.log exit 0，frob D_∥² = 204442845285416922537088/16856636797887840591561 > 0 = (σ₁β)² |
| (ii) 块恒等式 | E(1−P₀)=Y·D_⊥ᵀ 双例＋P₀ 桥 | **现成（纯环，例 1/2/3 全走通）** | /tmp/r18b_probe1_block_id.log exit 0（净本体 30＋33＋48 行） |
| (iii) σ₃(Y) 自举 | 二次恒等式＋行-CS 下界＋frob 对称面＋逆向三角＋组装＋闭环 | **可改造（Lean 面全走通；闭环消歧/op≤1/λ₃(Y) 压缩三面未跑留 R19）** | /tmp/r18b_probe2_bootstrap.log exit 0（净本体 22＋40＋18＋53 行）＋ /tmp/r18b_closure_study.log P1–P5 全过 |
| (iv) 三路线评估 | Hölder 面 Lean 可行性＋A/B/C 档位 | **书面评估（依赖面全部定位；C 档不推荐）** | §iv 七步链＋三路线档位表＋Fraction 常数对照（§5） |

---

## §i 反射族反例机器核验（D77 裁决 2 证据面）

### §i.1 数学对象

l4_procrustes.py:20–32 书面链步骤 6 写『σ₁β ≤ σ₃/2 时 ‖D_⊥‖ ≤ η/(σ₃−σ₁β)
≤ 2η/σ₃』——从步骤 3 的 (σ₃ − ‖D_∥‖_F)·‖D_⊥‖_F ≤ η 到该式，隐含前提
**frob D_∥ ≤ σ₁β**。反例机器（D77-2 设计师给向，本件机器化）：

- X：9 个有理球面点（stereographic 参数 u,v ∈ ℚ ⟹ 点
  (2u, 2v, 1−u²−v²)/(1+u²+v²) 有理，行单位逐位精确），seed 20261018 LCG
  确定性生成，u ≠ 0 保证（首列坐标非零——frob D_∥ > 0 的实质前提）；
- Q̃ := diag(−1,1,1)，Y := X·Q̃。

逐项核验（/tmp/r18b_counterexample.py，本会话亲跑 exit 0，全 Fraction）：

| 编号 | 断言 | 结果 |
|---|---|---|
| C1 | X 行单位 9/9＋det(XᵀX) ≠ 0（Gauss-Jordan 与 cofactor 双实现一致）＋Sylvester 顺序主子式全 > 0（⟹ 正定 ⟹ 0 < λ₃ ≤ λ₁，β 公式分母良定义） | det = 27644548911799213067871202087424/1250488850331411254353184573409 ≠ 0 ✓ |
| C2 | Y := X·Q̃ 行单位 9/9（反射保行范数） | ✓ |
| C3 | G_Y == G_X 逐位（81 元全等；Gram 双实现：矩阵乘 vs 三项点积和）⟹ η := ‖G_Y−G_X‖_F == 0（η² == 0 精确）、δ == 0 | ✓ |
| C4 | β := λ₁η/λ₃² == 0（η==0）⟹ β = 0 ≤ min(1/2, σ₃/(2σ₁))——**适用域全前提成立** | ✓ |
| C5 | D := Y−X == X·(Q̃−1)（27 元）⟹ D_∥ := X·A（A := Q̃−1）、D_⊥ == 0、Xᵀ·D_⊥ == 0（投影分解前提成立） | ✓ |
| C6 | B := A+Aᵀ+A·Aᵀ == 0（9 元全零）⟹ 步骤 4 结论 ‖B‖_F ≤ β = 0 **成立**（(1+A) = Q̃ 正交 ⟹ B = (1+A)(1+A)ᵀ−1 = 0） | ✓ |
| C7 | (1+A)(1+A)ᵀ == I₃（⟹ 极分解 W = 1、‖W−I‖_F = 0 ≤ β = 0）＋Y·Q̃ == X（27 元；⟹ 步骤 5 结论 ‖X−YR‖_F = 0 ≤ σ₁β+‖D_⊥‖ = 0 成立，R := Q̃） | ✓ |
| **C8** | **缺口本体**：frob D_∥² = 4·Σᵢ x_{i0}² = 204442845285416922537088/16856636797887840591561 > 0（平方和直接与闭式双实现一致；首列非零元 9/9）而 (σ₁β)² = λ₁β² = 0 ⟹ **frob D_∥ > σ₁·β = 0** | ✓ 被违 |
| C9 | 终定理不反例（诚实框架）：d_P ≤ ‖X−Y·Q̃‖_F² == 0 ⟹ d_P == 0 == C·δ（δ=0） | ✓ |

**结论（与 D77-2 逐字对齐）**：定理全前提成立（C3/C4 域内、C6/C7 中间结论
皆成立）而步骤 6 隐含前提 frob D_∥ ≤ σ₁β 被违（C8）——即该前提**不是定理
前提的推论**，步骤 6 照写是无效推断。反射族本身 d_P = 0（C9），**不反例终
定理** d_P ≤ C·δ，只断裂所给链路——无条件 d_P ≤ C·δ 是否为真命题未经证明
（§iii/§iv 的路线研究即为其供方向）。

### §i.2 反例数值字面（G2/G4 锚面，gate 从此处重算）

seed = 20261018（LCG：x ↦ (1103515245·x+12345) mod 2³¹，stereographic
参数 u = (next%21−10)/10、v 同式，u ≠ 0 重抽）：

```
<!--X-FRACTIONS-BEGIN-->
X（9×3，行单位，Fraction 精确）＝
  [60/209, -200/209, -9/209]
  [-50/51, 10/51, -1/51]
  [12/29, 24/29, 11/29]
  [40/113, 60/113, 87/113]
  [50/87, -70/87, 13/87]
  [8/9, 4/9, -1/9]
  [2/11, 6/11, 9/11]
  [-30/59, -30/59, 41/59]
  [100/189, -160/189, 11/189]
Q̃ = diag(-1,1,1)
<!--X-FRACTIONS-END-->
```

关键精确值（双实现一致）：

- det(XᵀX) = **27644548911799213067871202087424/1250488850331411254353184573409**
  ≠ 0（Gauss-Jordan 与 cofactor 双路同值）；
- frob D_∥² = **204442845285416922537088/16856636797887840591561** > 0
  （≈ 12.1310；frob D_∥ ≈ 3.4830；平方和与闭式 4·Σᵢ x_{i0}² 双路同值）；
- (σ₁β)² = λ₁·β² = 0（β = λ₁η/λ₃²，η = 0）；
- η = 0、δ = 0、B = 0（9 元）、Y·Q̃ = X（27 元）——全部 == 判定精确。

确定性复跑：同命令双跑输出逐字节一致（diff 空，
/tmp/r18b_det_rerun1.log vs r18b_det_rerun2.log 亲验）。

### §i.3 双实现口径

- Gram：`X·Xᵀ` 矩阵乘（实现 1）vs 逐行三项点积 ⟨x_i,x_j⟩（实现 2）——
  两路在 X 与 Y 上各 81 元全同值；
- det：Gauss-Jordan 部分主元（实现 1）vs cofactor 递归展开（实现 2）；
- frob D_∥²：27 元平方和（实现 1）vs 闭式 4·Σᵢ x_{i0}²（实现 2）。

门 G2 的『门内独立重算』即从本节字面 X/Q̃ 出发的**第三实现**（gate 自带
矩阵工具，与 /tmp 脚本零共享代码）。

### §i.4 迭代史与摩擦

脚本一版定稿（无迭代）；两处死代码清理后重跑（复跑一致）。无实质摩擦——
反射族的 Gram 不变性在 Fraction 下是逐位恒等（⟨y_i,y_j⟩ 与 ⟨x_i,x_j⟩ 的
三项和逐项相同），无需任何数值技巧。

### §i.5 l4.json 评估（只读不动文件）

本会话直读 numerics/bounds/results/l4.json（只读）：C_float =
14.878732094961943、delta_max_float = 0.17124089749729504、
lambda3_lower_float = 2.970726、lambda1_upper_float = 3.014638（与
TableB5Data.lean 直读 l3 = 1485363/500000、u1 = 1507319/500000 逐位一致）。
**评估结论：数值层不受影响**——l4.json 的严格部分是 λ 界（区间 Sylvester）
与常数装配（Fraction 区间算术），其 scope 字段自记『定理证明为书面推导
（未过 Lean）』；本件的缺口是**书面推导的推断步骤**（步骤 6 隐含前提），
与数值层常数无涉。书面推导缺口如实记录于本节 §i.1（终定理 d_P ≤ C·δ 的
无条件真值不受反例影响——C9，但其书面链路在步骤 6 断裂）。文件零改动：
sha256 = 9f588a3b61c562d8574523d57ac5e868a893b62f4db52509280b9c090300fb96
（本会话亲算，gate G1 冻结锚）。

---

## §ii 块恒等式 Lean 探针（路线 B/A 的 ‖Y·D_⊥ᵀ‖ ≤ η 供给面）

**三档判定：现成**——两恒等式均为纯环例（P₀ 面前提代入，幂等性都不需要），
外加 P₀ := X·S⁻¹·Xᵀ 的前提桥（三供给）。源
/tmp/r18b_probe1_block_id.lean（175 行，含 6 条 #check＋3 例），运行日志
/tmp/r18b_probe1_block_id.log exit_code=0（4.4s）。

### §ii.1 数学面

前提（抽象 P₀ 面）：P₀ᵀ = P₀、P₀*X = X、P₀*D_⊥ = 0、D_∥ = X*A、
Y = X + D_∥ + D_⊥。推导核心：

```
(1−P₀)*Y  = Y − P₀*(X + D_∥ + D_⊥) = Y − X − D_∥ = D_⊥
            （P₀X=X；P₀D_∥ = P₀(XA) = (P₀X)A = XA = D_∥；P₀D_⊥=0）
Xᵀ*(1−P₀) = Xᵀ − XᵀP₀ = Xᵀ − (P₀ᵀX)ᵀ = 0        （P₀ 对称＋P₀X=X）
Yᵀ*(1−P₀) = ((1−P₀)Y)ᵀ = D_⊥ᵀ                     （(1−P₀)ᵀ = 1−P₀）
```

- **例 1（主目标）**：E*(1−P₀) = Y*D_⊥ᵀ，E := Y*Yᵀ − X*Xᵀ（= G_Y−G_X）：
  E(1−P₀) = Y·(Yᵀ(1−P₀)) − X·(Xᵀ(1−P₀)) = Y·D_⊥ᵀ − 0。**净本体 30 行**；
- **例 2（路线 B 面）**：(1−P₀)*E*(1−P₀) = D_⊥*D_⊥ᵀ：左块 = ((1−P₀)Y)·
  ((1−P₀)Y)ᵀ − ((1−P₀)X)(…) = D_⊥D_⊥ᵀ − 0。**净本体 33 行**；
- **例 3（P₀ 面前提桥）**：P₀ := X*S⁻¹*Xᵀ（hS : XᵀX = S、IsUnit S.det、
  Sᵀ = S、Xᵀ*D_⊥ = 0）⟹ 五前提导出（对称：transpose_nonsing_inv；右不变：
  S⁻¹S = 1；零化：XᵀD_⊥ = 0）＋例 1 重放。**净本体 48 行**。

意义（对路线 A/B 的供给，见 §iii/§iv）：

```
‖Y·D_⊥ᵀ‖_F = ‖E·(1−P₀)‖_F ≤ ‖E‖_F · op(1−P₀) ≤ η·1 = η
             （对称幂等 ⟹ op ≤ 1：vᵀ(1−P₀)v = ‖v‖²−‖P₀v‖² ≤ ‖v‖²，
              P₀ = P₀P₀ᵀ ⟹ vᵀP₀v = ‖P₀v‖² ≥ 0——纯二次型面）
tr(D_⊥D_⊥ᵀ) = tr((1−P₀)E(1−P₀)) = tr(E(1−P₀)²) = tr(E(1−P₀)) ≤ 3η
             （循环＋幂等＋trace-CS——§iv 的 ½-Hölder 面）
```

### §ii.2 摩擦（v1→v5 迭代收敛的主因，亲历五条）

①裸 `rw [mul_sub]` 在 `Xᵀ * (1 − P0)` 上实例路径不字节对齐（pattern 明明
在场却报 did not find occurrence）——须 calc 项式 `Matrix.mul_sub _ _ _`
或改写目标形状（R17B『实例路径不字节对齐』同款面）；②`Matrix.mul_sub/
sub_mul/mul_assoc/mul_add` 是 Matrix 专属名，根名不中；③m×n 矩阵目标是
**模非环**——`ring`/`noncomm_ring` 不适用（报 ring_nf made no progress 或
suggests abel），加法收口用 `simp`/`abel`，乘法面用 calc/rw；④`X * 0` 的
`0` 需显式类型注记（`(0 : Matrix n m ℝ)`）——裸 0 会默认 ℕ 卡实例
（HMul (Matrix m n ℝ) ℕ _ 报错且位置误导）；⑤`1 − P₀` 语法上是 Sub，
`rw [Matrix.mul_sub]` 会先匹配错因子——须显式实参
`Matrix.mul_sub (1 - P0) (Y * Yᵀ) (X * Xᵀ)` 定向；`noncomm_ring` 在含
`(1 − P₀)` 因子的 m×m 目标上会归一化成 `-1 • (…)` 与未归一侧不齐——定向
小引理（e1/e2：`rw [← Matrix.mul_assoc, Matrix.mul_assoc]`）替代。

### §ii.3 未跑项（如实）

op(1−P₀) ≤ 1 的二次型面 Lean 例**未跑**（§ii.1 意义栏的推导为书面——
P₀ = P₀P₀ ⟹ vᵀP₀v = ‖P₀v‖² 的 Lean 化留 R19 工程面，预估 ~15–20 行，
纯二次型+vecNorm 面，低风险）；`P₀*P₀ = P₀` 幂等桥（例 3 供给面之外）
未单列（例 3 的三供给不含幂等——块恒等式本就不需要）；数值实例面已由
§iii.4 P5 独立第二实现覆盖（Fraction 精确，81 元×2）。

---

## §iii σ₃(Y) 自举路线（路线 A 的 Lean 面＋闭环条件研究）

**三档判定：可改造**——四件 Lean 例全走通（二次恒等式／行-CS 下界／frob
对称面／逆向三角＋组装）；闭环消歧与 λ₃(Y) 压缩两面**数值面已核、Lean 面
未跑**（留 R19，如实）。源 /tmp/r18b_probe2_bootstrap.lean（215 行，含
10 条 #check＋4 定理），运行日志 /tmp/r18b_probe2_bootstrap.log
exit_code=0（4.3s）；闭环研究 /tmp/r18b_closure_study.py＋
/tmp/r18b_closure_study.log（P1–P5 全过 exit 0）。

### §iii.1 数学面（路线 A 全链 A1–A11）

设 t := frob D_⊥、c := √(λ₃(1−β))（β ≤ 1/2 ⟹ c² ≥ λ₃/2）：

- **A1**（在库·B5b step4_bound）：frob B ≤ β，B := A+Aᵀ+A·Aᵀ；
- **A2**（探针 2·真新面）：frob B' = frob B，B' := Aᵀ+A+AᵀA =
  (1+A)ᵀ(1+A)−1——**注意 B' ≠ Bᵀ**（B 本身对称），frob_transpose_eq 单发
  不可达；走 trace 循环移位 tr((NNᵀ)²) = tr(N(NᵀNNᵀ)) = tr((NᵀNNᵀ)N) =
  tr((NᵀN)²)＋frob(M−1)² = tr(M²)−2·tr M+card 线性拆开；
- **A3**（在库·R18A L1 abs_quadform_le_frob）：|v ⬝ᵥ (M*ᵥv)| ≤ frob M·
  (v⬝ᵥv)（行-CS 二次型界）；
- **A4**（探针 2 例 b·转置面）：‖(1+A)*ᵥv‖² = vᵀ(1+B')v = ‖v‖² + vᵀB'v ≥
  (1−β)·‖v‖²；
- **A5**（在库·B5b step3 同形）：‖X*ᵥw‖² = wᵀSw ≥ λ₃·‖w‖²；
- **A6**（在库族）：‖D_⊥*ᵥv‖ ≤ t·‖v‖（行 CS）；
- **A7**（探针 2 例 c·组装＋逆向三角）：
  ‖Y*ᵥv‖ = ‖X(1+A)*ᵥv + D_⊥*ᵥv‖ ≥ √λ₃·√(1−β)·‖v‖ − ‖D_⊥*ᵥv‖
  ⟹ 二次型口径 λ₃(Y) ≥ (c − t)²；
- **A8**（探针 1 例 1＋§ii 未跑面）：‖Y·D_⊥ᵀ‖_F = ‖E(1−P₀)‖_F ≤
  ‖E‖_F·op(1−P₀) ≤ η；
- **A9**（B5b step3 同形·未跑）：‖Y·D_⊥ᵀ‖²_F = tr(S_Y·D_⊥ᵀD_⊥) ≥
  λ₃(Y)·t²（trace_ge_smul 面，S_Y := YᵀY PSD 平凡）；
- **A10**（闭环消歧·数值面已核）：合并 A7/A8/A9 得 **(c − t)·t ≤ η**；配
  ½-Hölder 面（§iv：t² ≤ 3η）与域 **η ≤ c²/12** 消歧：
  t ≤ √(3η) ≤ c/2 ⟹ c − t ≥ c/2 > 0；反证 t > 2η/c 则 (c−t)t ≥
  (c/2)·t > (c/2)·(2η/c) = η 矛盾。**结论 t ≤ 2η/c ≤ 2√2·η/√λ₃**；
- **A11**（在库·R18A step5_bound）：d_P ≤ σ₁β + t ≤ σ₁·β + 2√2·η/√λ₃
  ——**无条件线性界**（窄域 η ≤ λ₃(1−β)/12，见 §5 域对照）。

### §iii.2 Lean 探针四件（实测行数）

| 定理 | 断言 | 净本体 | 关键路线 |
|---|---|---|---|
| r18b_quad_id | ((1+A)ᵀ*ᵥv) ⬝ᵥ ((1+A)ᵀ*ᵥv) = v ⬝ᵥ ((1+B)*ᵥv)（hB : B = A+Aᵀ+A*Aᵀ） | （与下件合计 22 行） | mulVec_transpose＋dotProduct_mulVec＋mulVec_mulVec＋hAB（noncomm_ring，须先 transpose_add/one 归一） |
| r18b_quadform_lo | frob B ≤ β ⟹ (1−β)(v⬝ᵥv) ≤ ‖(1+A)ᵀ*ᵥv‖² | 同上合计 | quad_id＋add_mulVec/one_mulVec＋dotProduct_add＋abs_quadform_le_frob（在库）＋mul_le_mul_of_nonneg_right |
| r18b_frob_symm_face | frob (Aᵀ+A+Aᵀ*A) = frob (A+Aᵀ+A*Aᵀ) | **40** | set N := 1+A；tr 循环（← mul_assoc ×2＋trace_mul_comm＋congr 1＋noncomm_ring）；key : frob(M−1)² = tr(M²)−2tr M+card（恒等式写成 M*M−M−M+1 避 2*M smul 面）；abel 收口 hBminus |
| r18b_vecNorm_sub_le | vecNorm u − vecNorm w ≤ vecNorm (u+w) | **18** | by_cases＋abs_le.mp 拆 CS＋dotProduct 展开＋nlinarith |
| r18b_assembly | √(λ₃(1−β))·‖v‖ − ‖D_⊥*ᵥv‖ ≤ ‖((X*(1+A)+D_⊥)*ᵥv)‖ | **53** | 例 b 转置面（frob 对称面供给）＋√ 单调（sq_sqrt 事实显式供给）＋add_mulVec/mulVec_mulVec 拆装＋逆向三角＋sub_le_sub 收口 |

探针 2 的 `r18b_quad_id`＋`r18b_quadform_lo` 合计净本体 22 行（含 #check
注释外的全部证明行）。

### §iii.3 摩擦（v1→v6 迭代收敛的主因，亲历六条）

①`noncomm_ring` 遇 `(1+A)ᵀ` 原子不自动展 1ᵀ+Aᵀ——须先
`rw [Matrix.transpose_add, Matrix.transpose_one]` 归一再 noncomm_ring；
②abs 面须 `abs_le.mp` 拆双面喂 linarith（`|x| ≤ a` 原样 linarith 不燃）；
③乘积两项（frob B·(v⬝ᵥv)）的 β 单调须 `mul_le_mul_of_nonneg_right` 显式
（linarith 线性原子不跨乘积）；④trace 线性化时 `2*M` 矩阵标量乘是 smul 面
坑——恒等式写成 `M*M - M - M + 1` 走 trace_add/trace_sub/trace_one 全根名；
⑤`dotProduct_self_eq` 方向敏感（calc 步用正向，取平方时用反向）且
`Real.sqrt_nonneg` 无 `.mpr`（直接 `Real.sqrt_nonneg _`）；√ 的平方消除须
`Real.sq_sqrt` 作为**事实显式供给**再 nlinarith（nlinarith 不自己开 √）；
⑥`rw [← h1B]` 把 N*Nᵀ 换成 1+(…)−1 会破坏后续 pattern——改为
hBminus : A+Aᵀ+A*Aᵀ = N*Nᵀ−1（abel 收口）再正向代入。

### §iii.4 闭环条件研究（Fraction 数值面，P1–P5）

/tmp/r18b_closure_study.py（seed 20261018，常数从 TableB5Data.lean 源直读
零手抄，sqrt 用整数 Newton 有理包——l4_procrustes.py:94 同式）：

- **P1 记录恒等式复核**：dom = s3Dn/(2·s1Up) = 0.4963450766 < 1/2 ✓；
  η_max_cond = sqrt72Up·deltaMax = 1.453027198 == dom·l3²/u1 **精确** ✓；
- **P2 闭环消歧网格**：c_lo := √(l3/2) 下包 ≈ 1.218755，η := c_lo²/12 ≈
  0.123780（≈ l3/24），39 点有理网格（t = √(3η)·k/39）上逆否验证
  『t·(c−t) ≤ η ⟹ t ≤ 2η/c（≈ 0.203126）』**无违例** ✓；
- **P2-NC 负对照（域条件是实质前提）**：η := c_lo²/3 ≈ 0.495121 出域
  （> c²/12 ≈ 0.123780 且 > c²/4——二次 t²−ct+η 无实根，任意 t 满足
  t(c−t) ≤ η）时 t := c_lo 满足 t(c−t) = 0 ≤ η 而 t = c_lo > 2η/c ≈
  0.812503——**√η 面（§iv）必需**，路线 A 的域条件非技术性 ✓；
- **P3 路线 A 常数/域**：C_A_inner = u1·s1Up/l3² + 2/c_lo ≈ 2.234119，
  C_A = √72·C_A_inner ≈ **18.957**（vs 条件版 C ≈ 14.879，比值 **1.2741**）；
  δ_A = (l3/24)/√72 ≈ **0.014588**（vs δ_max ≈ 0.171241，域窄 **11.74 倍**）；
- **P4 路线 B（½-Hölder）常数/全域覆盖**：k1 := s1Up·u1·√72/l3² ≈
  5.032616，C_B = k1·√δ_max + √(3√72) ≈ **7.128**；19 点网格验证
  k1·δ + √(3·√72·δ) ≤ C_B·√δ（δ ∈ (0, δ_max] 全域）**无违例** ✓；β ≤ 1/2
  域面 Fraction 精确复核（√72Up·deltaMax ≤ l3²/(2·u1) ✓——记录域全体在
  路线 B 域内）；
- **P5 块恒等式有理实例**（§ii 的独立第二实现）：随机有理 X（gen_X 同款）
  ＋随机有理 A（frob B² = 0.017250 ≤ 1/4 域内）＋D_⊥ := M − X·(S⁻¹·(Xᵀ·M))
  （Xᵀ·D_⊥ == 0 精确，S⁻¹ Gauss-Jordan 自实现）⟹ Y := X·(1+A) + D_⊥：
  (i) E·(1−P₀) == Y·D_⊥ᵀ（81 元）✓；(ii) (1−P₀)E(1−P₀) == D_⊥D_⊥ᵀ ✓；
  (iii) ‖E(1−P₀)‖²_F = 12.631967 ≤ ‖E‖²_F = 21.276868 ✓（op ≤ 1 实例面）；
  (iv) tr(D_⊥D_⊥ᵀ) == tr(E(1−P₀)) = 2.517641（循环＋幂等）且 squared 口径
  (3η)² − tr² = 185.153 ≥ 0 ✓（½-Hölder 面实例）；(v) ‖Y·D_⊥ᵀ‖²_F ==
  ‖E(1−P₀)‖²_F = 12.631967 ≤ η² = 21.276868 ✓（A8 实例面；**λ₃(Y) 压缩
  层归 Lean 面，数值层如实只到此处**——A9 的 λ₃(Y) 无理，实例不证）。

迭代史：2 版收敛（v1 域条件误用 l3/24 与 c_lo 包络的微观差不齐；v2 改
c_lo²/12 口径＋实例 A 系数缩 10×（域检查正确拦截过系数过大的首版——
负对照式自检在档））。

### §iii.5 未跑项（如实）

- A8 的 op(1−P₀) ≤ 1 二次型面 Lean 例未跑（§ii.3 同项，~15–20 行预估）；
- A9 的 λ₃(Y) 压缩面 Lean 例未跑（B5b step3_bound 同形改造，~30 行预估——
  需 S_Y := YᵀY 的 PSD 前提由 A7 二次型口径供给）；
- A10 闭环消歧的 Lean 化未跑（实代数 nlinarith 域：c−t ≥ c/2 三角不等式
  组合，~25–35 行预估）；
- A11 终装配（与在库 step5_bound 对接）未跑；
- W²=M 短路路线（R17B §Q2 已判不必需）不重跑；路线 C 的谱面探针**未跑**
  （§iv 判定不推荐，如实）。

---

## §iv ½-Hölder 面与三候选无条件路线书面评估

### §iv.1 ½-Hölder 面（tr(D_⊥·D_⊥ᵀ) ≤ 3η 的 Lean 可行性）

七步链（每步标注在库/已探/新面）：

| 步 | 断言 | 面档 |
|---|---|---|
| 1 | t² = frob(D_⊥)² = tr(D_⊥·D_⊥ᵀ) | 在库（B5b frob_sq_eq_trace） |
| 2 | tr(D_⊥D_⊥ᵀ) = tr((1−P₀)E(1−P₀)) | **已探**（探针 1 例 2，净本体 33 行） |
| 3 | = tr(E·(1−P₀)·(1−P₀)) | 在库（trace_mul_comm 循环） |
| 4 | = tr(E·(1−P₀)) | 环面（P₀ 幂等：P₀² = P₀ from P₀ = XS⁻¹Xᵀ，ring；探针 1 例 3 供给面邻接） |
| 5 | \|tr M\| ≤ 3·frob M（9×9） | **新面 ~20 行**（Σ M_ii 的 CS：sq_sum_le_card_mul_sum_sq 在库（R17B §Q4 定位）＋单元素 ≤ 和（ℝ 面拆分胶水在库先例 R17B §Q4）＋对角 ≤ 全阵） |
| 6 | frob(E·(1−P₀)) ≤ frob E = η | **半在库**（frob_mul_le_of_vecNorm 在库（R17A）＋op(1−P₀) ≤ 1 新面 ~15–20 行（§ii.3 未跑项，纯二次型）） |
| 7 | t² ≤ 3η ⟹ d_P ≤ σ₁β + √(3η) | 在库（step5_bound）＋sqrt 单调（在库族） |

**可行性判定：高（全部面已定位，无缺位 API）**——预估工程量 ~120–200 行
（含引理装配；两个新面合计 ~35–40 行，其余为在库件接线）。

### §iv.2 三候选无条件路线档位表

| 路线 | 依赖面（新面加粗） | 工程量档位 | 风险 | 产出（常数/域） | 判定 |
|---|---|---|---|---|---|
| **A（σ₃(Y) 自举）** | 探针 1 例 1＋**op≤1 二次型面 ~15–20 行**＋探针 2 四件（quad_id/quadform_lo/**frob 对称面 40 行**/rtri/assembly）＋**λ₃(Y) 压缩 ~30 行**＋**闭环消歧 ~25–35 行**＋终装配 ~30 行 | ~260–360 行 | **低–中**（全部二次型/trace/frob 面，零特征值 API、零 CFC 新面；已探 6 面，未探 3 面均有在库同形先例） | 线性 d_P ≤ C_A·δ，C_A ≈ 18.957（劣 1.2741×）；域 δ ≤ δ_A ≈ 0.014588（窄 11.74×） | **推荐主路线（R19）** |
| **B（E(I−P₀)=Y·D_⊥ᵀ 面）** | 探针 1 例 2＋步骤 3/4 幂等环面＋**trace-CS ~20 行**＋**op≤1 ~15–20 行**＋在库 frob_mul_le_of_vecNorm＋在库 step5_bound | ~120–200 行 | **低**（§iv.1 七步全定位） | ½-Hölder d_P ≤ C_B·√δ，C_B ≈ 7.128；**域＝记录域全体**（δ ≤ 0.171241） | **快胜件（R19 先行或同轮）** |
| **C（谱扰动 Weyl 型）** | λ₃(YᵀY) ≥ λ₃((1+A)ᵀS(1+A)) − ‖交叉项＋D_⊥ᵀD_⊥‖_op（Weyl 双矩阵扰动）＋Frobenius↔op 桥（在库 R17A）＋特征值 API（**缺位风险**——本仓未探 Weyl 型扰动面） | ~300–450 行＋API 自建风险 | **高**（Weyl 面缺位未探；产出自证复杂） | 与路线 A 同（线性、同域）——**无增益** | **不推荐（档位三）** |

### §iv.3 R19 排期判断

1. **路线 B 先落**（~150 行级，风险低）：无条件 d_P ≤ C_B·√δ 全记录域——
   B5c 件即刻获得无条件面（½-Hölder 口径，正是账本 L5 原设想——
   l4_procrustes.py:34–35 注记的『σ₃(TTP)>0 时线性严格更强』之 Hölder 补面）；
2. **路线 A 主攻**（~300 行级）：无条件线性 d_P ≤ C_A·δ 窄域（δ ≤ 0.014588）
   ——与 B 形成两档：小 δ 线性/全域 √δ。R18A 条件层（step6_final 三前提
   显式）保留为中间件与对照，**不拆不改**（D78-4 可回滚点：A 落地后在条件
   层上加装，无返工面）；
3. **路线 C 不排**（除非 A 的未探三面中出现实质阻断——届时 C 的谱面再议，
   依据本件 §iii.5 未跑清单如实回看）；
4. 预算口径：R19 两路线合计 ~400–550 行工程量（R18A 854 行同轮当量内），
   heavySolves = 0 维持（零求解轮）。

---

## §5 数值对照表（Fraction 直读 TableB5Data.lean，P1–P4 供据）

| 量 | 条件版（在库 R18A） | 路线 A（无条件·窄域） | 路线 B（无条件·全域） |
|---|---|---|---|
| 前提 | frob D_∥ ≤ σ₁β（hdpar，反射族下不可消去） | 无（A1–A10 全链） | 无（§iv.1 七步） |
| 界形 | d_P ≤ C·δ（线性） | d_P ≤ C_A·δ（线性） | d_P ≤ C_B·√δ（½-Hölder） |
| 内常数 | u1·s1Up/l3² + 2/s3Dn ≈ 1.7399 | u1·s1Up/l3² + 2/c_lo ≈ 2.234119 | k1 = s1Up·u1·√72/l3² ≈ 5.032616（σ₁β 项） |
| 全常数（δ 口径） | C ≈ 14.879 | C_A ≈ 18.957（比值 1.2741） | C_B ≈ 7.128（√δ 口径） |
| 适用域 | δ ≤ δ_max ≈ 0.171241 | δ ≤ δ_A ≈ 0.014588（窄 11.74×） | δ ≤ δ_max ≈ 0.171241（全域） |
| D_⊥ 界 | ‖D_⊥‖ ≤ 2η/σ₃（hdpar 下） | t ≤ 2η/c ≤ 2√2·η/√λ₃ | t ≤ √(3η) |

（全部数值 Fraction 精确计算后转 float 显示，源 /tmp/r18b_closure_study.log
P1–P4；条件版常数与 l4.json C_float = 14.878732094961943 及 TableB5Data.lean
CVal 一致复核。）

## §6 排期建议（对 R19 的输入）

1. **B → A 串行**（§iv.3）：B 的七步面与 A 的前六面共享（块恒等式/op≤1/
   trace-CS），先行落 B 可把共享面一次入库供 A 复用；
2. **共享面清单**（两路线交集，一次工程化）：探针 1 例 1/例 2（30＋33 行
   级）＋op(1−P₀) ≤ 1（~15–20 行）＋trace-CS（~20 行）＋幂等环面（例 3
   邻接）——A/B 合计去重后 ~400–550 行（§iv.3 第 4 条）；
3. **风险面如实**：A 的三个未探面（op≤1/λ₃(Y) 压缩/闭环消歧）均有在库
   同形先例（frob_mul_le_of_vecNorm/step3_bound/nlinarith 实代数），判定
   低–中风险；B 无未探面。C 不排（§iv.2）；
4. **对 R18C 收口的输入**：本件（notes/dperp-gap-study.md＋
   r18b_dperp_gate.py＋嵌套包装器＋decisions D79）为 R18B 自有件；与 R18A
   （TableB5Polar.lean 族＋tableb-lean.md §6＋r18_b5c_gate）文件集零交叠
   （D77-3 并行纪律），r18 家族放行层见 R18A 门 G1（dperp-gap-study.md 在
   放行清单——R18A 门源 :150–160 亲读）。

## §7 零求解声明与诚实口径（G4/G5 锚）

- **零求解声明：本任务 heavySolves = 0**（字面锚）——零重求解、零 SDP、
  零新数值证书。
- **零账本触碰声明**：四账本（m9_campaign/m10_campaign/hermite_v2_campaign/
  typed_ladder）零触碰，endgame.json 零触碰（只读，sha256 冻结锚
  86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f），
  certificates/ 零触碰，l4.json 只评估零改动（§i.5 冻结锚
  9f588a3b…fb96），typed_ladder rungs 零追加——G1 守卫
  numerics/bounds/r18b_dperp_gate.py 以 git status/sha256 机器面执行。
- 全部结论系探针/研究性质：**Lean 探针编译通过 ≠ 证明完成**；本件无任何
  『本体入 Lean』宣称；B5c 无条件化（路线 A/B）仍未开工，其可行性陈述以
  探针证据为界；**无条件 d_P ≤ C·δ 终定理本轮不宣称**（D77-2 口径维持，
  R19 依本件方向供件再排）。
- 未跑项汇总（全文『未跑』如实）：§ii op≤1 二次型面＋幂等桥单列；
  §iii A8 尾面＋A9 λ₃(Y) 压缩＋A10 闭环消歧 Lean 化＋A11 终装配＋路线 C
  谱面；§iv trace-CS 与 op≤1 的新面实现；l4.json --selftest 不重跑（只读
  评估口径）；/tmp 诊断 mini 件已清理不留档。
- 迭代史：Lean 探针 1/2 分别 5/6 版收敛（§ii.2/§iii.3 摩擦各五/六条亲历）；
  Fraction 脚本 1/2 版（§i.4/§iii.4）；/tmp 日志为终版覆盖式（R15C §2.3
  口径）。

---

## 附录 A：探针源转录（终版，与 /tmp 两源件逐字一致）

### A.1 探针 1 源（/tmp/r18b_probe1_block_id.lean，175 行）

```lean
import Mathlib
import ThomsonN9.TableB5Core
import ThomsonN9.TableB5Trace

/-!
R18B 探针 1 源（dperp-gap-study §ii，r18b-dperp-gap-study，D77 裁决 2 证据面）：
块恒等式双例＋P₀ 面前提桥——纯环例，P₀ 面前提代入：

  例 1：E*(1−P₀) = Y*D_⊥ᵀ，其中 E := Y*Yᵀ − X*Xᵀ（= G_Y−G_X）。
       前提：P₀ᵀ = P₀、P₀*X = X、P₀*D_⊥ = 0、D_∥ = X*A、Y = X + D_∥ + D_⊥。
  例 2：(1−P₀)*E*(1−P₀) = D_⊥*D_⊥ᵀ（同前提）。
  例 3（P₀ 面前提桥）：P₀ := X*S⁻¹*Xᵀ（S = XᵀX 可逆对称，Xᵀ*D_⊥ = 0）
       ⟹ 例 1 五前提全部导出（hP0T/hP0X/hP0Dperp 由构造供给）。

数学面（l4_procrustes.py 步骤 3 混合块＋R18B 路线 B 的 η 面供给）：
  (1−P₀)*Y = Y − P₀*(X + D_∥ + D_⊥) = Y − X − D_∥ = D_⊥
     （P₀X=X、P₀D_∥=P₀(XA)=(P₀X)A=XA=D_∥、P₀D_⊥=0——幂等性不需要）
  Xᵀ*(1−P₀) = Xᵀ − XᵀP₀ = Xᵀ − (P₀ᵀX)ᵀ = 0（P₀ 对称＋P₀X=X）
  ⟹ E*(1−P₀) = Y*(Yᵀ*(1−P₀)) − X*(Xᵀ*(1−P₀)) = Y*D_⊥ᵀ − 0
     （Yᵀ(1−P₀) = ((1−P₀)Y)ᵀ = D_⊥ᵀ）
  ⟹ (1−P₀)*E*(1−P₀) = ((1−P₀)Y)*((1−P₀)Y)ᵀ − 0 = D_⊥*D_⊥ᵀ

意义（路线 B/A 的 ‖Y*D_⊥ᵀ‖ ≤ η 供给面）：
  ‖Y*D_⊥ᵀ‖_F = ‖E*(1−P₀)‖_F ≤ ‖E‖_F * op(1−P₀) ≤ η（对称幂等 ⇒ op ≤ 1）；
  tr(D_⊥*D_⊥ᵀ) = tr((1−P₀)E(1−P₀)) = tr(E*(1−P₀)²) = tr(E*(1−P₀)) ≤ 3η（½-Hölder 面）。

迭代摩擦留档（v1→v3）：①裸 `rw [mul_sub]` 在 `Xᵀ * (1 − P0)` 上实例路径不
字节对齐（pattern 明明在场）——须 calc 项式 `Matrix.mul_sub _ _ _` 或 noncomm_ring
（R17B『实例路径不字节对齐』同款面）；②`Matrix.mul_sub/sub_mul/mul_assoc` 是
Matrix 专属名，根名 `mul_sub` 不中；③`X * S⁻¹ * Xᵀ` 左结合解析——mul_assoc 方向
与前推链须按左结合骨架推（先外后内两次前向），hXt 用两次后向；④转置后结合序
与目标不一致处以 noncomm_ring 收口；⑤矩阵 `1` 需 [DecidableEq m]。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix
open ThomsonN9.TableB5Trace

-- § API 签名核验（#check 面）----------------------------------------------

#check @Matrix.transpose_mul          -- (M*N)ᵀ = Nᵀ*Mᵀ
#check @Matrix.transpose_sub          -- (M−N)ᵀ = Mᵀ−Nᵀ
#check @Matrix.transpose_one          -- 1ᵀ = 1
#check @Matrix.transpose_transpose    -- (Mᵀ)ᵀ = M
#check @Matrix.nonsing_inv_mul        -- S⁻¹*S = 1（IsUnit S.det 前提）
#check @Matrix.transpose_nonsing_inv  -- (S⁻¹)ᵀ = (Sᵀ)⁻¹

-- § 例 1（主目标）：E*(1−P₀) = Y*D_⊥ᵀ（纯环，抽象 P₀ 面）-----------------------

example {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    {X Y Dpar Dperp : Matrix m n ℝ} {A : Matrix n n ℝ} {P0 : Matrix m m ℝ}
    (hP0T : P0ᵀ = P0) (hP0X : P0 * X = X) (hP0Dperp : P0 * Dperp = 0)
    (hDpar : Dpar = X * A) (hY : Y = X + Dpar + Dperp) :
    (Y * Yᵀ - X * Xᵀ) * (1 - P0) = Y * Dperpᵀ := by
  -- ① Xᵀ*(1−P₀) = 0（P₀ 对称＋P₀X=X）
  have hXt : Xᵀ * P0 = Xᵀ := by
    have h := congrArg Matrix.transpose hP0X          -- (P0*X)ᵀ = Xᵀ
    rwa [Matrix.transpose_mul, hP0T] at h             -- Xᵀ*P0ᵀ = Xᵀ → Xᵀ*P0 = Xᵀ
  have hXT : Xᵀ * (1 - P0) = 0 := by
    calc Xᵀ * (1 - P0) = Xᵀ * 1 - Xᵀ * P0 := Matrix.mul_sub _ _ _
      _ = Xᵀ - Xᵀ * P0 := by rw [Matrix.mul_one]
      _ = Xᵀ - Xᵀ := by rw [hXt]
      _ = 0 := by rw [sub_self]
  -- ② (1−P₀)*Y = D_⊥（P₀X=X、P₀D_∥=D_∥、P₀D_⊥=0——幂等性不需要）
  have hP0Dpar : P0 * Dpar = Dpar := by
    rw [hDpar, ← Matrix.mul_assoc, hP0X]
  have hP0Y : P0 * Y = X + Dpar := by
    rw [hY, Matrix.mul_add, Matrix.mul_add, hP0X, hP0Dpar, hP0Dperp]
    simp
  have hYm : (1 - P0) * Y = Dperp := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP0Y, hY]
    simp
  -- ③ Yᵀ*(1−P₀) = D_⊥ᵀ（Yᵀ(1−P₀) = ((1−P₀)Y)ᵀ = D_⊥ᵀ）
  have h1mT : (1 - P0)ᵀ = 1 - P0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hP0T]
  have hYT : Yᵀ * (1 - P0) = Dperpᵀ := by
    rw [← h1mT, ← Matrix.transpose_mul, hYm]
  -- ④ 装配
  calc (Y * Yᵀ - X * Xᵀ) * (1 - P0)
      = Y * (Yᵀ * (1 - P0)) - X * (Xᵀ * (1 - P0)) := by
          rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Y * Dperpᵀ - X * (0 : Matrix n m ℝ) := by rw [hYT, hXT]
    _ = Y * Dperpᵀ := by simp

-- § 例 2（路线 B 面）：(1−P₀)*E*(1−P₀) = D_⊥*D_⊥ᵀ（同前提）--------------------

example {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    {X Y Dpar Dperp : Matrix m n ℝ} {A : Matrix n n ℝ} {P0 : Matrix m m ℝ}
    (hP0T : P0ᵀ = P0) (hP0X : P0 * X = X) (hP0Dperp : P0 * Dperp = 0)
    (hDpar : Dpar = X * A) (hY : Y = X + Dpar + Dperp) :
    (1 - P0) * (Y * Yᵀ - X * Xᵀ) * (1 - P0) = Dperp * Dperpᵀ := by
  have hP0Dpar : P0 * Dpar = Dpar := by
    rw [hDpar, ← Matrix.mul_assoc, hP0X]
  have hP0Y : P0 * Y = X + Dpar := by
    rw [hY, Matrix.mul_add, Matrix.mul_add, hP0X, hP0Dpar, hP0Dperp]
    simp
  have hYm : (1 - P0) * Y = Dperp := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP0Y, hY]
    simp
  have hXm : (1 - P0) * X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP0X]
    simp
  have h1mT : (1 - P0)ᵀ = 1 - P0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hP0T]
  have hYT : Yᵀ * (1 - P0) = Dperpᵀ := by
    rw [← h1mT, ← Matrix.transpose_mul, hYm]
  have e1 : (1 - P0) * (Y * Yᵀ) * (1 - P0)
      = ((1 - P0) * Y) * (Yᵀ * (1 - P0)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc]
  have e2 : (1 - P0) * (X * Xᵀ) * (1 - P0)
      = ((1 - P0) * X) * (Xᵀ * (1 - P0)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc]
  calc (1 - P0) * (Y * Yᵀ - X * Xᵀ) * (1 - P0)
      = (1 - P0) * (Y * Yᵀ) * (1 - P0) - (1 - P0) * (X * Xᵀ) * (1 - P0) := by
          rw [Matrix.mul_sub (1 - P0) (Y * Yᵀ) (X * Xᵀ), Matrix.sub_mul]
    _ = ((1 - P0) * Y) * (Yᵀ * (1 - P0)) - ((1 - P0) * X) * (Xᵀ * (1 - P0)) := by
          rw [e1, e2]
    _ = Dperp * Dperpᵀ - (0 : Matrix m n ℝ) * (Xᵀ * (1 - P0)) := by rw [hYm, hYT, hXm]
    _ = Dperp * Dperpᵀ := by simp

-- § 例 3（P₀ 面前提桥）：P₀ := X*S⁻¹*Xᵀ 供给例 1 全部前提 ---------------------

example {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {X Dperp : Matrix m n ℝ} {A S : Matrix n n ℝ} {Dpar Y : Matrix m n ℝ}
    (hS : Xᵀ * X = S) (hSdet : IsUnit S.det) (hST : Sᵀ = S)
    (hXD : Xᵀ * Dperp = 0) (hDpar : Dpar = X * A) (hY : Y = X + Dpar + Dperp) :
    (Y * Yᵀ - X * Xᵀ) * (1 - (X * S⁻¹ * Xᵀ)) = Y * Dperpᵀ := by
  -- (a) 对称性：(X*S⁻¹*Xᵀ)ᵀ = X*(S⁻¹)ᵀ*Xᵀ = X*(Sᵀ)⁻¹*Xᵀ = X*S⁻¹*Xᵀ
  have hP0T : (X * S⁻¹ * Xᵀ)ᵀ = X * S⁻¹ * Xᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hST, Matrix.mul_assoc]
  -- (b) P₀*X = X*S⁻¹*(Xᵀ*X) = X*(S⁻¹*S) = X
  have hP0X : (X * S⁻¹ * Xᵀ) * X = X := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hS, Matrix.nonsing_inv_mul S hSdet]
    simp
  -- (c) P₀*D_⊥ = X*S⁻¹*(Xᵀ*D_⊥) = 0
  have hP0Dperp : (X * S⁻¹ * Xᵀ) * Dperp = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hXD]
    simp
  -- (d) 例 1 五前提齐备，原式重放
  have hXt : Xᵀ * (X * S⁻¹ * Xᵀ) = Xᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hS, Matrix.mul_nonsing_inv S hSdet]
    simp
  have hXT : Xᵀ * (1 - (X * S⁻¹ * Xᵀ)) = 0 := by
    calc Xᵀ * (1 - (X * S⁻¹ * Xᵀ)) = Xᵀ * 1 - Xᵀ * (X * S⁻¹ * Xᵀ) :=
          Matrix.mul_sub _ _ _
      _ = Xᵀ - Xᵀ * (X * S⁻¹ * Xᵀ) := by rw [Matrix.mul_one]
      _ = Xᵀ - Xᵀ := by rw [hXt]
      _ = 0 := by rw [sub_self]
  have hP0Dpar : (X * S⁻¹ * Xᵀ) * Dpar = Dpar := by
    rw [hDpar, ← Matrix.mul_assoc, hP0X]
  have hP0Y : (X * S⁻¹ * Xᵀ) * Y = X + Dpar := by
    rw [hY, Matrix.mul_add, Matrix.mul_add, hP0X, hP0Dpar, hP0Dperp]
    simp
  have hYm : (1 - (X * S⁻¹ * Xᵀ)) * Y = Dperp := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP0Y, hY]
    simp
  have h1mT : (1 - (X * S⁻¹ * Xᵀ))ᵀ = 1 - (X * S⁻¹ * Xᵀ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hP0T]
  have hYT : Yᵀ * (1 - (X * S⁻¹ * Xᵀ)) = Dperpᵀ := by
    rw [← h1mT, ← Matrix.transpose_mul, hYm]
  have e1 : (Y * Yᵀ) * (1 - (X * S⁻¹ * Xᵀ))
      = Y * (Yᵀ * (1 - (X * S⁻¹ * Xᵀ))) := by
    rw [Matrix.mul_assoc]
  have e2 : (X * Xᵀ) * (1 - (X * S⁻¹ * Xᵀ))
      = X * (Xᵀ * (1 - (X * S⁻¹ * Xᵀ))) := by
    rw [Matrix.mul_assoc]
  calc (Y * Yᵀ - X * Xᵀ) * (1 - (X * S⁻¹ * Xᵀ))
      = (Y * Yᵀ) * (1 - (X * S⁻¹ * Xᵀ)) - (X * Xᵀ) * (1 - (X * S⁻¹ * Xᵀ)) := by
          rw [Matrix.sub_mul]
    _ = Y * (Yᵀ * (1 - (X * S⁻¹ * Xᵀ))) - X * (Xᵀ * (1 - (X * S⁻¹ * Xᵀ))) := by
          rw [e1, e2]
    _ = Y * Dperpᵀ - X * (0 : Matrix n m ℝ) := by rw [hYT, hXT]
    _ = Y * Dperpᵀ := by simp
```

（注：A.1 转录与 /tmp/r18b_probe1_block_id.lean 终版逐字一致；源件头部
『迭代摩擦留档（v1→v3）』段为源件自带初段记录，v4/v5 摩擦（④⑤两条最终
形态：noncomm_ring 在 `1 − P₀` 因子面卡 zsmul 归一改定向小引理 e1/e2；
`X * 0` 需类型注记）在 §ii.2 摩擦小节全文留档。）

### A.2 探针 2 源（/tmp/r18b_probe2_bootstrap.lean，215 行）

```lean
import Mathlib
import ThomsonN9.TableB5Core
import ThomsonN9.TableB5Trace
import ThomsonN9.TableB5Polar

/-!
R18B 探针 2 源（dperp-gap-study §iii，r18b-dperp-gap-study，D77 裁决 2 方向供件）：
σ₃(Y) 自举路线四件——任务书 (iii) 面：

  例 a（二次恒等式·纯环）：‖((1+A)ᵀ *ᵥ v)‖² = v ⬝ᵥ ((1+B) *ᵥ v)，
       B := A+Aᵀ+A*Aᵀ——(1+A)(1+A)ᵀ = 1+B 的 dotProduct 面。
  例 b（行-CS 下界）：frob B ≤ β、0 ≤ β ⇒ (1−β)*(v ⬝ᵥ v) ≤ ‖((1+A)ᵀ *ᵥ v)‖²
       ——例 a ＋ R18A L1 abs_quadform_le_frob（在库件，import 面）。
  frob 对称面（例 c 前置·真新面）：frob (Aᵀ+A+Aᵀ*A) = frob (A+Aᵀ+A*Aᵀ)
       ——注意 B' := Aᵀ+A+AᵀA（=(1+A)ᵀ(1+A)−1）不是 Bᵀ（B 本身对称），
       frob_transpose_eq 单发不可达；走 trace 循环移位
       tr((NNᵀ)²) = tr(N(NᵀNNᵀ)) = tr((NᵀNNᵀ)N) = tr((NᵀN)²)
       ＋frob(M−1)² 线性拆开（frob(M−1)² = tr(M²)−2·tr M+card）。
  例 c（组装例·Y 面）：hX : λ₃*(w⬝ᵥw) ≤ ‖X*ᵥw‖²（σ₃(X)² 二次型面）⇒
       √(λ₃*(1−β)) * ‖v‖ − ‖D_⊥*ᵥv‖ ≤ ‖((X*(1+A) + D_⊥) *ᵥ v)‖
       ——逆向三角（自建 ~20 行）＋例 b 转置面（经 frob 对称面）＋
       √λ₃·√(1−β) = √(λ₃(1−β))。

数学面（路线 A 的 λ₃(Y) 下界供给）：
  ‖(1+A)v‖² = vᵀ(1+A)ᵀ(1+A)v = vᵀ(1+Bᵀ)v ≥ (1−β)‖v‖²（frob B' = frob B ≤ β）；
  σ₃(X) 面 ‖Xw‖² ≥ λ₃‖w‖²；逆向三角 ⇒
  ‖Yv‖ = ‖X(1+A)v + D⊥v‖ ≥ √λ₃√(1−β)‖v‖ − ‖D⊥v‖。
  与块恒等式（探针 1）合用：λ₃(Y)·‖D⊥‖²_F ≤ ‖YD⊥ᵀ‖²_F = ‖E(1−P₀)‖²_F ≤ η²
  ⇒ (√(λ₃(1−β)) − t)·t ≤ η（t := ‖D⊥‖_F）＋√η 面 t² ≤ 3η 消歧 ⇒ t ≤ 2η/c
  ——闭环条件研究（Fraction 数值面归 /tmp/r18b_closure_study.py，本件只探
  Lean 可行面）。

迭代摩擦留档（v1→v6）：①noncomm_ring 遇 `(1+A)ᵀ` 原子（不自动展 1ᵀ+Aᵀ）——
须先 rw transpose_add/transpose_one 归一；②abs 面须 abs_le.mp 拆双面喂
linarith（|x|≤a 原样 linarith 不燃）；③乘积两项（frob B·(v⬝ᵥv)）的 β 单调
须 mul_le_mul_of_nonneg_right 显式（linarith 线性原子不跨乘积）；④trace
线性化时 `2*M` 矩阵标量乘是 smul 面坑——恒等式写成 M*M−M−M+1 走
trace_add/trace_sub/trace_one 全根名；⑤dotProduct_self_eq 方向敏感
（calc 步用正向）；⑥rw [← h1B] 把 N*Nᵀ 换成 1+(…)−1 会破坏后续 pattern——
改为 hBminus : A+Aᵀ+A*Aᵀ = N*Nᵀ−1（abel 收口）再正向代入。
Mathlib @ d13f23b723b8a846827a245b89c10fc7d3f11612, toolchain v4.34.1。
本件为 /tmp 探针，不入库（零 formal/lean/ThomsonN9/ 写入）。
-/

open Matrix
open ThomsonN9.TableB5Core
open ThomsonN9.TableB5Trace
open ThomsonN9.TableB5Polar

-- § API 签名核验（#check 面）----------------------------------------------

#check @Matrix.mulVec_transpose        -- Aᵀ *ᵥ x = x ᵥ* A
#check @Matrix.dotProduct_mulVec       -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w
#check @Matrix.mulVec_mulVec           -- M *ᵥ (N *ᵥ v) = (M*N) *ᵥ v
#check @Matrix.add_mulVec              -- (A+B) *ᵥ x = A*ᵥx + B*ᵥx
#check @Matrix.one_mulVec              -- 1 *ᵥ v = v
#check @ThomsonN9.TableB5Polar.abs_quadform_le_frob   -- R18A L1（在库）
#check @ThomsonN9.TableB5Trace.frob_transpose_eq      -- B5b（在库）
#check @Matrix.trace_add
#check @Matrix.trace_sub
#check @Matrix.trace_one

-- § 例 a（二次恒等式·纯环）：‖((1+A)ᵀ*ᵥv)‖² = v ⬝ᵥ ((1+B)*ᵥv) ------------------

theorem r18b_quad_id {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hB : B = A + Aᵀ + A*Aᵀ) (v : n → ℝ) :
    ((1 + A)ᵀ *ᵥ v) ⬝ᵥ ((1 + A)ᵀ *ᵥ v) = v ⬝ᵥ ((1 + B) *ᵥ v) := by
  have hAB : (1 + A) * (1 + A)ᵀ = 1 + B := by
    rw [hB, Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hAB]

-- § 例 b（行-CS 下界）：frob B ≤ β ⇒ (1−β)*(v⬝ᵥv) ≤ ‖((1+A)ᵀ*ᵥv)‖² ------------

theorem r18b_quadform_lo {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hB : B = A + Aᵀ + A*Aᵀ) {β : ℝ} (hβ : 0 ≤ β)
    (hBf : frob B ≤ β) (v : n → ℝ) :
    (1 - β) * (v ⬝ᵥ v) ≤ ((1 + A)ᵀ *ᵥ v) ⬝ᵥ ((1 + A)ᵀ *ᵥ v) := by
  rw [r18b_quad_id A B hB v]
  have hsplit : v ⬝ᵥ ((1 + B) *ᵥ v) = (v ⬝ᵥ v) + v ⬝ᵥ (B *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
  rw [hsplit]
  have h2 := abs_quadform_le_frob B v
  obtain ⟨hlo, _⟩ := abs_le.mp h2
  have hs : (0:ℝ) ≤ v ⬝ᵥ v := by
    rw [dotProduct_self_eq]; exact sq_nonneg _
  have hstep : frob B * (v ⬝ᵥ v) ≤ β * (v ⬝ᵥ v) :=
    mul_le_mul_of_nonneg_right hBf hs
  linarith [hlo, hstep]

-- § frob 对称面（例 c 前置·真新面）--------------------------------------------

theorem r18b_frob_symm_face {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    frob (Aᵀ + A + Aᵀ*A) = frob (A + Aᵀ + A*Aᵀ) := by
  set N : Matrix n n ℝ := 1 + A with hNdef
  have hTT : (N*Nᵀ)ᵀ = N*Nᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hSS : (Nᵀ*N)ᵀ = Nᵀ*N := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  -- 平方 trace 循环移位：tr((NNᵀ)²) = tr((NᵀN)²)
  have htr : ((N*Nᵀ)*(N*Nᵀ)).trace = ((Nᵀ*N)*(Nᵀ*N)).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  have htrN : (Nᵀ*N).trace = (N*Nᵀ).trace := Matrix.trace_mul_comm Nᵀ N
  -- frob(M−1)² = tr(M²) − 2·tr M + card（M 对称；恒等式避 2*M 的 smul 面）
  have key : ∀ M : Matrix n n ℝ, Mᵀ = M →
      frob (M - 1)^2 = (M*M).trace - M.trace - M.trace + (Fintype.card n : ℝ) := by
    intro M hM
    have hexp : (M - 1)*(M - 1)ᵀ = M*M - M - M + 1 := by
      rw [Matrix.transpose_sub, hM, Matrix.transpose_one]; noncomm_ring
    have h1 : frob (M - 1)^2 = ((M - 1)*(M - 1)ᵀ).trace := by
      rw [frob_sq_eq_trace]
    rw [h1, hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_one]
  have h1B : 1 + (A + Aᵀ + A*Aᵀ) = N*Nᵀ := by
    rw [hNdef, Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  have h1B' : 1 + (Aᵀ + A + Aᵀ*A) = Nᵀ*N := by
    rw [hNdef, Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  have hBminus : A + Aᵀ + A*Aᵀ = N*Nᵀ - 1 := by
    rw [← h1B]; abel
  have hB'minus : Aᵀ + A + Aᵀ*A = Nᵀ*N - 1 := by
    rw [← h1B']; abel
  have e1 : frob (A + Aᵀ + A*Aᵀ)^2
      = ((N*Nᵀ)*(N*Nᵀ)).trace - (N*Nᵀ).trace - (N*Nᵀ).trace
        + (Fintype.card n : ℝ) := by
    rw [hBminus, key (N*Nᵀ) hTT]
  have e2 : frob (Aᵀ + A + Aᵀ*A)^2
      = ((Nᵀ*N)*(Nᵀ*N)).trace - (Nᵀ*N).trace - (Nᵀ*N).trace
        + (Fintype.card n : ℝ) := by
    rw [hB'minus, key (Nᵀ*N) hSS]
  have hnn1 : (0:ℝ) ≤ frob (A + Aᵀ + A*Aᵀ) := frob_nonneg _
  have hnn2 : (0:ℝ) ≤ frob (Aᵀ + A + Aᵀ*A) := frob_nonneg _
  nlinarith [e1, e2, htr, htrN]

-- § 逆向三角（自建底座，~20 行）：‖u‖ − ‖w‖ ≤ ‖u + w‖ ------------------------

theorem r18b_vecNorm_sub_le {n : Type} [Fintype n] (u w : n → ℝ) :
    vecNorm u - vecNorm w ≤ vecNorm (u + w) := by
  by_cases hle : vecNorm u ≤ vecNorm w
  · linarith [vecNorm_nonneg (u + w)]
  · have hcs := abs_dotProduct_le u w
    obtain ⟨hlo, hhi⟩ := abs_le.mp hcs
    have hexp : vecNorm (u + w)^2 = (u ⬝ᵥ u) + 2*(u ⬝ᵥ w) + (w ⬝ᵥ w) := by
      rw [← dotProduct_self_eq (u + w)]
      simp [dotProduct_add, add_dotProduct, dotProduct_comm]
      ring
    have hkey : (vecNorm u - vecNorm w)^2 ≤ vecNorm (u + w)^2 := by
      rw [hexp, dotProduct_self_eq u, dotProduct_self_eq w]
      nlinarith [hlo, hhi]
    have hpos : (0:ℝ) < vecNorm u - vecNorm w := by
      have : vecNorm w < vecNorm u := lt_of_not_ge hle
      linarith
    have hnn : (0:ℝ) ≤ vecNorm (u + w) := vecNorm_nonneg _
    nlinarith [hkey, hpos, hnn]

-- § 例 c（组装例·Y 面）：√(λ₃(1−β))·‖v‖ − ‖D⊥*ᵥv‖ ≤ ‖(X*(1+A)+D⊥)*ᵥv‖ ------

theorem r18b_assembly {n : Type} [Fintype n] [DecidableEq n]
    {X Dperp : Matrix (Fin 9) n ℝ} {A : Matrix n n ℝ} {lam3 β : ℝ}
    (hl3 : 0 < lam3) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hX : ∀ w : n → ℝ, lam3 * (w ⬝ᵥ w) ≤ vecNorm (X *ᵥ w)^2)
    (hBf : frob (A + Aᵀ + A*Aᵀ) ≤ β) (v : n → ℝ) :
    Real.sqrt (lam3 * (1 - β)) * vecNorm v - vecNorm (Dperp *ᵥ v)
      ≤ vecNorm ((X * (1 + A) + Dperp) *ᵥ v) := by
  -- (1) ‖(1+A)*ᵥv‖ ≥ √(1−β)·‖v‖（例 b 的转置面，经 frob 对称面）
  have h1 : (1 - β) * (v ⬝ᵥ v) ≤ ((1 + A) *ᵥ v) ⬝ᵥ ((1 + A) *ᵥ v) := by
    have h := r18b_quadform_lo (Aᵀ) (Aᵀ + A + Aᵀ*A) (by
        rw [Matrix.transpose_transpose]) hβ (by
        rw [r18b_frob_symm_face A]; exact hBf) v
    have heq : ((1 + Aᵀ)ᵀ *ᵥ v) = ((1 + A) *ᵥ v) := by
      congr 1
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_transpose]
    rwa [heq] at h
  have hstep1 : Real.sqrt (1 - β) * vecNorm v ≤ vecNorm ((1 + A) *ᵥ v) := by
    have hsq1 : Real.sqrt (1 - β)^2 = 1 - β :=
      Real.sq_sqrt (by linarith)
    have hnn1 : (0:ℝ) ≤ Real.sqrt (1 - β) * vecNorm v :=
      mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg v)
    have h2 : (Real.sqrt (1 - β) * vecNorm v)^2 ≤ vecNorm ((1 + A) *ᵥ v)^2 := by
      rw [← dotProduct_self_eq ((1 + A) *ᵥ v)]
      have hexp : (Real.sqrt (1 - β) * vecNorm v)^2
          = Real.sqrt (1 - β)^2 * (v ⬝ᵥ v) := by
        rw [mul_pow, dotProduct_self_eq]
      rw [hexp, hsq1]
      exact h1
    have hnn2 : (0:ℝ) ≤ vecNorm ((1 + A) *ᵥ v) := vecNorm_nonneg _
    nlinarith [h2, hnn1, hnn2, hsq1]
  -- (2) σ₃(X) 面：‖X*ᵥw‖ ≥ √λ₃·‖w‖
  have hs2 : Real.sqrt lam3^2 = lam3 := Real.sq_sqrt hl3.le
  have hXw : ∀ w : n → ℝ, Real.sqrt lam3 * vecNorm w ≤ vecNorm (X *ᵥ w) := by
    intro w
    have h := hX w
    rw [dotProduct_self_eq w] at h
    have hnn1 : (0:ℝ) ≤ Real.sqrt lam3 * vecNorm w :=
      mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg w)
    have hnn2 : (0:ℝ) ≤ vecNorm (X *ᵥ w) := vecNorm_nonneg _
    nlinarith [h, hnn1, hnn2, hs2]
  -- (3) 组装：Y*ᵥv = X*ᵥ((1+A)*ᵥv) + D⊥*ᵥv（mulVec_mulVec＋add_mulVec）
  have hsplit : (X * (1 + A) + Dperp) *ᵥ v = (X *ᵥ ((1 + A) *ᵥ v)) + (Dperp *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [hsplit]
  have htri := r18b_vecNorm_sub_le (X *ᵥ ((1 + A) *ᵥ v)) (Dperp *ᵥ v)
  -- (4) √λ₃·√(1−β) = √(λ₃(1−β))
  have hsq : Real.sqrt lam3 * Real.sqrt (1 - β) = Real.sqrt (lam3 * (1 - β)) := by
    rw [Real.sqrt_mul hl3.le]
  calc Real.sqrt (lam3 * (1 - β)) * vecNorm v - vecNorm (Dperp *ᵥ v)
      = Real.sqrt lam3 * (Real.sqrt (1 - β) * vecNorm v) - vecNorm (Dperp *ᵥ v) := by
          rw [← hsq]; ring
    _ ≤ Real.sqrt lam3 * vecNorm ((1 + A) *ᵥ v) - vecNorm (Dperp *ᵥ v) := by
          refine sub_le_sub (mul_le_mul_of_nonneg_left hstep1
            (Real.sqrt_nonneg _)) le_rfl
    _ ≤ vecNorm (X *ᵥ ((1 + A) *ᵥ v)) - vecNorm (Dperp *ᵥ v) := by
          linarith [hXw ((1 + A) *ᵥ v)]
    _ ≤ vecNorm (X *ᵥ ((1 + A) *ᵥ v) + Dperp *ᵥ v) := htri
```

（注：A.2 转录与 /tmp/r18b_probe2_bootstrap.lean 终版逐字一致；源件头部的
迭代摩擦段（v1→v6 六条）与 §iii.3 一致。）

## 附录 B：本会话已跑证据索引（全部 /tmp 留档，门 G3 逐一在盘核验非零字节）

| 日志/源 | 内容 | 结果 |
|---|---|---|
| /tmp/r18b_probe1_block_id.lean | §ii 探针 1 源（6 #check＋3 例，175 行） | 编译对象（附录 A.1 转录） |
| /tmp/r18b_probe1_block_id.log | §ii 探针 1 运行日志 | exit_code=0 零 error（4.4s） |
| /tmp/r18b_probe2_bootstrap.lean | §iii 探针 2 源（10 #check＋4 定理，215 行） | 编译对象（附录 A.2 转录） |
| /tmp/r18b_probe2_bootstrap.log | §iii 探针 2 运行日志 | exit_code=0 零 error（4.3s） |
| /tmp/r18b_counterexample.py | §i 反例源（Fraction 精确，seed 20261018，C1–C9＋双实现） | 编译对象 |
| /tmp/r18b_counterexample.log | §i 反例运行日志（--emit 含 X 字面） | exit 0，C1–C9 全过 |
| /tmp/r18b_closure_study.py | §iii.4/§iv 闭环研究源（常数 TableB5Data.lean 直读） | 编译对象 |
| /tmp/r18b_closure_study.log | 闭环研究运行日志（P1–P5＋P2-NC） | exit 0 全过 |
| /tmp/r18b_det_rerun1.log / r18b_det_rerun2.log | 反例确定性双跑 | diff 空（逐字节一致） |
| /tmp/r18b_det_rerun3.log | 闭环研究确定性复跑 | 与主日志 diff 空 |
| /tmp/r18b_final_pass.log | 终验趟（探针 2×Lean＋Fraction 2×＋确定性 2×） | 6/6 全过（探针 4.4s/4.3s） |
| /tmp/r18b_final_run.sh | 终跑脚本（生成上行的 shell 源，可复现） | 在盘 |

（门核验：以上 12 条路径须全部在盘且非零字节；『exit_code=0』字样为各日志
尾部自报。）

（本件与 R18A 文件集零交叠亲验：formal/lean/ThomsonN9/ 与
notes/tableb-lean.md 本会话零写入；四账本/endgame.json/l4.json sha256 冻结
锚见 §i.5/§7——G1 机器面执行。）
