# r22a-pattern-numeric — l4_orbit (P1)–(P4) pattern-consistency 数值层（σ₀ 显式化＋轨道-稳定子精确计数）

轮次：Round 22（campaign dwfrun-f9904baf 第 17 轮）；任务 r22a-pattern-numeric
（D96 裁决 1，D95 候选①落地）。本 note 为新增独立 note（append-only 首建）。

## 1. 交付物与口径

- 主件 `numerics/bounds/r22_pattern_numeric.py`＋存档
  `numerics/bounds/results/r22_pattern_numeric.json`（schema
  `thomson-n9/bounds/r22-pattern-numeric/1`；sort_keys＋indent、无时间戳/
  code_version；heavy_solves==0；seed 20261022 仅声明——流程本身无随机性，
  l4_orbit.py 先例）；门 `numerics/bounds/r22_pattern_gate.py`
  （G0–G3＋NC-a/b/c，seed 20261022）。
- 审计件（`artifact_class=='audit'`、`provenance.read_only==true`）：零求解
  零 SDP 零 Lean 面新增；数值层系数值面不构成严格增量（D96 裁决 3，
  R9D/R20/R21A 先例）；不入 endgame.json/citedCertificates/12 分区、不作
  endgame_chain.py 输入（活体 grep＋endgame.json sha256 冻结锚
  `86863a09…69f` 归门 G0）。
- 全部复用不复制：importlib 复用 `l4_orbit.py`
  （compute_context(50)＋build_tables＋run_scout＋verify_coloring；
  l4_orbit_gate 同源先例）、import 复用 `r15_b1_data.nodeOfN_rule`（Lean
  TableB1.lean:823 nodeOfN 同构规则）；l4_orbit.json／tube.json／
  local_min.json 只读。

## 2. 数学内容七面（F1–F6＋F7 归门）

- **F1 枚举重建**：全 K9 6 色染色过 (P1)–(P3) 过滤＋精确复验——
  scout==exact accepted==distinct==30240（与 l4_orbit.json 存档
  labeledTotal 一致）。
- **F2 桥面**：构造性多项式恒等证书 `ttp_reference_coloring()`（(P5)）vs
  算术分类 nodeOfN **双实现**对账（r15 import＋主件独立移植）＋门内
  **第三分类实现**（几何位直分类）——三方两两 36/36 零 mismatch。
- **F3 自同构群**：全 S₉ 扫描 Aut(ttp_ref)（φ_σ(ttp)==nodeOfN tuple）恰
  12 元；生成元 g₁=(012)(345)(678)、k=(01)(34)(78)、h=(03)(14)(25) 张成
  ==全群；阶分布（lex 扫描序）[1,2,2,3,3,2,2,2,2,6,6,2]、阶重集
  {1:1, 2:7, 3:2, 6:2} ≅ D₃×C₂（D3h 型 12 阶——l4_orbit.json
  orbitBalance erratum『D12 勘误』的群论面：6 棱顶＋3 帽顶的几何对称群
  显式落库）。
- **F4 轨道-稳定子**：orbit{σ·ttp_ref : σ∈S₉}（拉回作用 (σ·C)[i,j]=
  C[σ(i),σ(j)]，9!=362880 全扫描、禁采样）去重==30240==F1 幸存集**全集
  逐位集合相等**；9!/30240==12==|Stab| 精确。
- **F5 σ₀ 实例化（feed contract）**：存档 canonical rep
  （l4_orbit.json survivorSet.classes[0].representative；元组 index k↔
  第 k 个 (i,j) i<j lex 对）恰 12 个 σ-见证（rep[σ(i),σ(j)]==nodeOfN(i,j)
  ∀36 对）；lex-min **σ₀=[0,5,6,4,2,1,7,3,8]** 显式入库；见证集
  =={σ₀∘s : s∈Aut}（Aut 左陪集；φ_σ∘φ_τ=φ_{τ∘σ} ⇒ W=σ₀·Stab）。
- **F6 孤立面**：见 §1；F7 负对照 NC-a（篡改 orbit/幸存集单元素→判据
  FAIL）／NC-b（篡改 |Aut|/生成元张成→FAIL）／NC-c（篡改 rep 单色→见证
  计数≠12→FAIL）全在门内以同一判据函数注入执行。
- json 体积口径：幸存集/轨道全集（30240×36）不入 json，存计数＋sha256
  指纹；全集逐位比较由门活体执行（禁采样口径不变）。

## 3. 与 klt-endgame-study.md transferableTo[4]（L4 双轨道适配）的关系

klt-endgame-study.md §2 第 4 条（L4：组合刚性——邻型计数＋幂和矩条件
← KLT 命题 5.1 (i)–(iii)）指出 KLT 单轨道便利不转移：TTP 双轨道（3 棱顶
＋6 帽顶）下 ker F₀ 需 2 维、且需额外论证「恰 3 顶点属轨道 1、6 顶点属
轨道 2」。R22A 把该适配的**组合枚举数值层**做实：

- l4_orbit (P1)–(P4) 的 30240 染色层从『过滤集＝单 iso 类』（Round 8 存档）
  推进到『orbit==幸存集全集相等＋|Stab|=12 精确计数』——轨道-稳定子
  9! = 30240×12 的两面正是双轨道适配所需的群论基座数值面（F3/F4）；
- D3h 型 12 阶对称群（≅D₃×C₂）的显式生成元＋全部 12 元＋阶分布入库，
  是『几何对称群约束逐顶点邻型计数轮廓（棱顶 (2,1,0,1,2,2)／帽顶
  (0,2,2,0,0,4)）』的群论面——erratum『D12 勘误』的对称性自此有精确
  群论对象支撑。
- L4 完整引理（幂和矩条件＋Vandermonde 稳定性）仍 off-path 非阻断
  （D96 裁决与整体路线节）；本件只交付其组合枚举层数据，不主张 L4
  推进。

## 4. 与 TableB5Chain 桥的关系（pattern_ident_lift 插入点消费）

`formal/lean/ThomsonN9/TableB5Chain.lean:281–288` `PatternCons` def（σ₀
显式、对 hT 全称量化的条件形）与 `:313` `pattern_ident_lift` 定理
（σ-近邻形 ⟹ identNode 辨识形）是 D92 裁决 2(δ) 预留的插入点；本件
`feedContract` 自此供数：

- σ₀=[0,5,6,4,2,1,7,3,8] 是 PatternCons 的 σ₀ 显式实例化数据：给定 Y 侧
  实现（Gram 逐对内积命中 canonical rep 色的节点管），σ₀ 把 rep 拉回
  nodeOfN 算术分类（φ_{σ₀}(rep)==nodeOfN tuple，36 对零差）；
- 恰 12 个 σ-见证（|Stab(ttp_ref)|=12 的右平移）说明该对齐置换不唯一但
  有精确计数——喂入契约带上计数与全部见证列表，消费方可任选（lex-min
  为默认 canonical）；
- 边界如实：PatternCons 是条件形（管前提在 Lean 侧显式量化），Y 侧几何
  前提（Gram 节点管）由 l4_orbit (P1)–(P4)／L6 供给——本件交付的是
  σ₀/计数/指纹**数据层**，不新增严格命题（D96 裁决 3 口径）。

## 5. 执行留痕（2026-10-24）

- 设计师预锚（D96 前置核验段）七面全部本会话亲测复现一致：30240×3、
  36/36×3、|Aut|=12＋张成＋阶分布、orbit==幸存集 True（1.4s 量级）、
  12 见证、σ₀=[0,5,6,4,2,1,7,3,8]。
- 门自跑：`python3 numerics/bounds/r22_pattern_gate.py` ALL PASS 68.2s
  exit 0；验收命令 `python3 thomson-n9/numerics/bounds/r22_pattern_gate.py`
  （CWD＝campaign 根）复跑 ALL PASS 69.9s exit 0；主件单跑 33.6s。
- 首版门未写前，探索脚本 /tmp/r22a_explore.py 曾把陪集方向断言写反
  （打印表达式未打印比较）——正式件修正为 σ₀∘Aut 并以门 G2/F5 复核；
  记录于此供后来者不重复踩。
