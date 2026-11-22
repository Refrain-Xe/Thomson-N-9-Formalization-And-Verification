# typed/ — Bachoc–Vallentin 分型三点构造（S² 适配）

N=7 证明（`references/thomson-n7-lean/paper/PAPER.md` §6）typed 三点界的推广实现：
把 [n] 按索引块分成 T 个类型，每类型一套 PSD 核块、每对类一条 minorant、逐
三点类一条 slack，份额（shares）把 Ψ 分配到第三点上。构造与推导见 `core.py`
模块 docstring；正确性由三层机器自检覆盖（见下）。

## 文件

| 文件 | 内容 |
|---|---|
| `core.py` | 类型结构 `TypeStructure`、装配 `assemble_typed`（协变块 Q_k/Y_k、gm/Ψ、份额、slacks、归一化、minorant 地图）、自检三件套 |
| `solve.py` | cvxpy SDP 构建/求解（Clarabel 主、SCS 兜底）、数值复核与折减 e_safe |
| `typed_selftest.py` | N∈{2,3,4,6,12} 普适最优构型紧合自检表 → `results/typed_selftest.json` |
| `calibrate_n7.py` | N=7 cap+五 slab 档对照论文数值 → `results/typed_calib_n7.json` |
| `prototype_n9.py` | N=9 (3,3,3) cut a=−151/200 原型阶梯 → `results/typed_prototype_n9.json` |

## 构造要点（数学）

- **分型基**：S² 的调和分解 H_k，再现核在根的正交补平面复坐标下为
  Q_k = Re(ζ^k \bar ζ^k)（PAPER.md §4，与 untyped `sdp_bound.py` 共用 `build_Q`）；
  协变块 Y_k[a,b] = u^a v^b Q_k（a,b < M−k）。
- **typed 三点对称化**：无序三点的核项 D_T = 2[s_X(u,v,t)+s_Y(u,t,v)+s_Z(v,t,u)]
  （根求和 × 2 换位因子），替代 untyped 的六置换 Sym——六个有序三点 = 3 根 ×
  2 换位，换位只转置 Y_k（与对称 F 配对不变）。
- **恒等式**：Σ_T λ_T + Σ_all = Σ_{i<j}H_cls(t_ij) − e，其中 Σ_all ≥ 0 是引理
  4.1 逐根逐类型。λ_T ≥ 0 于出现域 + H_cls ≤ φ 于类区间 ⟹ E ≥ e。
- **域**：`mode="cut"` 单切口（任意分型有效）；`mode="band"` 带状（要求类型 0
  恰为重标后的极小对 {0,1}，尺寸 2）：类 (0,0) 的 H 与含 {0,1} 的 slack 带
  [lo,hi]，其余只用下切口（PAPER.md §6.4）。

## 自检与校准（正确性验证）

1. **核自检**：Q_k = Re(ζ^k \bar ζ^k) 于随机 Gram 三点（容差 ~1e-14）；
   分型正性：Σ_{i,j,l}⟨F^{type(i),k}, Y_k⟩ ≥ 0，随机 PSD 逐类型。
2. **typed 恒等式**：随机 (h, ψ, PSD F, 归一化 c, e) × 随机构型上
   Σ_T λ_T + Σ_all = Σ_{i<j}H − e 逐点成立（rel ~1e-14/1e-12）——覆盖份额
   求和=Ψ、gm/Ψ 定义、核项根和×2=D、归一化计数、s(1,1,1) 全部装配通路。
3. **紧合自检表**（`typed_selftest.py`，exit 0 = 全过）：N∈{3,4,6,12} 普适
   最优构型上 (2,n−2) 分型 typed SDP 恰得真值（高出 +1.0e-8/+1.5e-7/
   +2.0e-8/+4.7e-6，均在预注册有效阈 5e-6 内；untyped 表为 +2e-8/+3.8e-8/
   +2.3e-7/+1.3e-6，同量级）。N=2 理论退化行（无第三点/无三点类，份额与
   slack 机制空转，`assemble_typed` 显式拒绝）。
4. **N=7 校准**（`calibrate_n7.py`，(2,5) band，(M,K,d_H)=(6,6,10) 同论文）：
   cap [−1,−0.99] 的 e_opt 与 E(P) 双向贴合（|e−E(P)| = 2.2e-6，理论最优被
   夹在 [E(P)−2.3e-16, E(P)]）；五个 slab 的 e_opt 全部高于论文可行值
   （+1.7e-4…+9.1e-4；untyped Case-1 校准偏差 +1.2e-3 同量级）。

## N=9 原型（规模记录，见 `results/typed_prototype_n9.json`）

类型结构 (3,3,3)（= `numerics/family.py` 的 `tri_cap_prism` 轨道布局：0–2 顶
三角、3–5 底三角、6–8 赤道帽），cut 模式 a=−151/200（Round 2 区域最好证书的
同覆盖域）。逐档单命令（≤10 分钟，超时即止并如实记录）：

| config | (M,K) | d_H | PSD 块数（SOS/F/σ） | 最大块 | 求解耗时 | 结果 |
|---|---|---|---|---|---|---|
| small | (6,6) | 10 | 80 / 18 / 24 | 56 | 75s | e = 25.753016383，e_safe = 25.752634258 |
| mid | (7,6) | 12 | 80 / 18 / 24 | 84 | 447s（420s 时限） | raw e = 25.758110647，Δ=4.3e-3 未收敛 → e_safe = 25.753788280 |
| midlarge | (8,6) | 14 | 80 / 18 / 24 | 120 | 1128s 处终止 | **无求解结果**（超单命令 10 分钟预算 kill；瓶颈＝cvxpy 单线程规范化，Clarabel time_limit=500 未及生效） |
| large16 | (9,6) | 16 | 80 / 18 / 24 | 165 | — | 构建成功（1,214,429 变量 / 9,895 行 / nx=1,079，1.45s、0.20GB），Clarabel 求解被 OOM kill（exit 137，本机 24GB） |

typed (7,6) 的 **raw** e = 25.758111 已高于 untyped (8,6) 同区域（a=−151/200）
e_safe 25.757893（Round 2 cap 阶梯 m0755 档）——typed 松弛的方向性收益在 raw 值
上可见；短板是求解器收敛精度与规模（时限内残差 → 折减 Δ；d_H≥14 的稠密装配
在本机超时/超内存），与 Round 2 诊断一致（求解器精化与规模化列为下一轮工作：
候选＝类型自同构约化（(3,3,3) 的 0↔1 对换可把 10 条 slack 并成 5 条）、
分块装配直连 Clarabel、或降 σ/SOS 块数）。

### 与 Round 2 `slab_band.py` 的交叉验证

`slab_band.py`（Round 2）是 (2,7) 分带 typed 的专门实现；其 N=7 校准档
slab [−0.99,−0.98]、(M,K)=(6,6) 给 e = 14.453835（bounds/README.md:24），本包
同档（SOS 乘子族为其超集）给 e = 14.453886994——两独立实现相差 +5.2e-5，方向
与本包乘子族更大一致（超集松弛 ⟹ 最优 ≥）。

## 用法（在 thomson-n9 下）

```
numerics/.venv/bin/python numerics/bounds/typed/typed_selftest.py            # 紧合自检表
numerics/.venv/bin/python numerics/bounds/typed/calibrate_n7.py              # N=7 校准
numerics/.venv/bin/python numerics/bounds/typed/prototype_n9.py --config small   # N=9 原型一档
```
