> **Archival Note (Final Proof Complete — Round 25):** This file is the chronological (newest-first) campaign research log retained for historical provenance; earlier entries toward the bottom of this file (Rounds 0–23) describe intermediate pre-closure states. **The Thomson $N = 9$ proof is completely closed in both Stage A and Lean 4 (Stage B, Round 25).** For the final theorem statements, formal proof, and one-command verification, see [README.md](README.md), [REPRODUCE.md](REPRODUCE.md), [formal/lean/ThomsonN9/Solution.lean](formal/lean/ThomsonN9/Solution.lean), and [paper/main.tex](paper/main.tex) (Zenodo DOI: [10.5281/zenodo.24453172](https://doi.org/10.5281/zenodo.24453172)).

---

本文件由各次运行顺序追加（新条目置顶）。当前条目：**Round 25（终局收官，2026-11-20）：Stage A（`closed = true`）＋ Stage B（Lean 4 全 4 条挑战定理内核形式化）全面证毕！`formal/lean/ThomsonN9/Solution.lean` 正式证明 `thomson_nine_M0`、`thomson_nine_M1`、`thomson_nine`（D3h 三帽三棱柱全局最优）与 `thomson_nine_unique`（模 $O(3)\times S_9$ 刚性唯一），`bash formal/lean/scripts/check.sh` 全绿 exit 0（36/36 挑战常量逐字匹配、`skipped=[]`、0 处 `sorry`、0 禁用记号、公理仅 `[propext, Classical.choice, Quot.sound]`），`scripts/negative-control.sh` 与内核篡改负对照双过，冻结文件 `ComparatorChallenges/ThomsonN9.lean` 与 `endgame.json` 零改动。**

## Round 25（终局收官，2026-11-20）：Stage B Lean 4 全面形式化证毕（`thomson_nine` 与 `thomson_nine_unique` 全绿，公理仅三标准）

在冻结栈（`leanprover/lean4:v4.34.1`、`Mathlib d13f23b`）下落地完整 Stage B 形式化证明体系 `formal/lean/ThomsonN9/StageB/`（32 模块、`1.75 MB`、`12,880` 行；全项目传递依赖锥共 45 模块 `20,327` 行：`ThreePoint` / `PolyKron` / `PolyKronFast` / `SlabCert` / `CapCert` 含 19 片并行 2D-Kronecker 切片与 7 片度-37 Bernstein / `RigidityL4` 28-叶压缩 DFS + `TableB5Chain` Procrustes / `LocalMinL6` IVT 驻点 + 紧致 $O(3)$ 规范固定 + Bregman-Young + 27×27 整数 Cholesky Hessian 下界）并总装至 `ThomsonN9/Solution.lean`（818 行，含全部 4 条挑战定理及外层固定 $\exists z^* \in [z^*_{\mathrm{lo}}, z^*_{\mathrm{hi}}]$ 的加强总定理 `thomson_nine_main`），配合 `scripts/CheckAxioms.lean` 严格白名单审计与 `scripts/compare_statements.py` 零豁免比对（`SKIP = set()`）。官方总验门 `bash formal/lean/scripts/check.sh` exit 0（8972 jobs，75 个文件哈希锁定，全锥禁用记号扫描通过，`Solution.lean` 0 处 `sorry`，7 项 `#print axioms` 全部仅 `[propext, Classical.choice, Quot.sound]`，36/36 常量比对 `OK`，`sha256 = bafcdc5e…35c9`）；`scripts/negative-control.sh` 双负对照（语句翻转与内核篡改）均精准拦截。详见 `GAP-REPORT.md` Round 25 节与 `notes/decisions.md` D106。

## Round 24（Antigravity 接管破局，2026-11-20）：Stage A 全面闭合（`closed = true`，全局最优性与 $O(3)\times S_9$ 唯一性双证毕）

根因定位前序 23 轮（3.84B tokens）停滞于全引擎硬编码 `K=6`（遗漏临界谐波 $F_6, F_7$）及 `(3,3,3)` 对称帽冗余。新增 `numerics/bounds/sym_cap_sdpa.py`（纯 `Fraction` $S_3$ 同型约化，81× 加速）、`certificates/n9-stage-a-r24-symcap-m0765_M10K10.json`（`1.8 MB`，128-bit，24 块 `LDLᵀ` 通过，组合恒等式误差 0，$\varepsilon_{\text{forcing}} \le 9.961\times 10^{-20}$）、`numerics/bounds/l6_taylor.py`（50-dps 区间 $z^*$ 测地四阶 Taylor，`r* = 0.06500`，4,369× L5 裕度；初版审计修正 $f>2$ 分支与 $4/3$ 系数后重验全过）及总验门 `numerics/bounds/stage_a_closure.py` → `results/stage_a_closure.json`（全 11 证书 444 个 PSD 块进程外全验＋5/5 负对照，`1355.21s` exit 0，`closed=true`, `uniqueness_proved=true`）。独立零导入审计 `/tmp/independent_stage_a_audit.py`（含 5 个球面精确有理 9 点构型与 500 组对抗对）`106.5s` exit 0。历史冻结账本 `endgame.json`（`86863a09…69f`）零改动。详见 `GAP-REPORT.md` Round 24 节与 `notes/decisions.md` D104。

## Round 23（campaign dwfrun-f9904baf 第 18 轮，2026-10-24 / 2026-11-20 交接收口）：R23A TableB1Witness + R23C 净树收口

R23A（`96bc585`）完成表 B 第十件 `TableB1Witness.lean`（19 定理零 sorry，公理三标准，`W==σ₀∘Aut`、`|W|=12`、`lex-min==σ₀`、`PatternCons` 与 `pattern_ident_lift` 消费）及 D101/D102。R23C（D103）由 Antigravity 接管补完：`endgame_gate.py` 增补 campaign-18 锚、`r23c_closure_gate.py` 修复 C5 `r23*.json` 匹配并补齐 `GAP-REPORT.md`/`PROGRESS.md`/`decisions.md` D103。R23 终判 `closed=false`、`assembledRecord` 维持、`progress=true`、本轮 0 求解（累计 `33.421/40`）。后续进入 Round 24 数学与算法破局阶段。

## Round 22 轮次汇总（汇总员-R22，campaign dwfrun-f9904baf 第 17 轮，2026-10-24，0 求解）：复算＋返工双审计收编（零分歧）＋轮次终判——closed=false 三面一致维持／assembledRecord 维持零提升／progress=true（严格口径：新严格引理 TableB1Aut 21 定理落地，表 B 第九件）

Round 22（campaign dwfrun-f9904baf 第 17 轮，2026-10-24）轮次汇总
（GAP-REPORT 本轮节 ④；decisions D96/D97/D98/D99＋D100——D100 系本
汇总裁决，下轮 D101 顺延）。开工前置亲验：HEAD=242217e、git status
--porcelain 唯一在途件＝notes/decisions.md（复算员＋返工员两审计条
目在途——HEAD 版 sha256==c7b5f574…72ae＝工作文件前 565798 字节
sha256 逐位相等亲验＝纯 EOF append；本腿收编，D90 先例）。收编面：
复算员-R22 独立复算（零仓 import 自写 /tmp 脚本）三腿验收重跑 exit
0＋独立第二实现重算补 GAP-REPORT ③ 节『未独立重跑项』缺口——自写
DFS 9! 全枚举 30240 幸存者指纹 9dcf8b47…c42d8==
survivorSetSha256==orbitSha256、精确决策表 tri 3/11/42＋quad
16/2435 与 l4_orbit.json 逐项一致、LDLᵀ 交叉复核 56/56、nodeOfN 72
有序对零 mismatch、|Aut|=12／阶分布／σ₀／12 见证全对上、AR/margin/
wouldBe/铁律/预算独立 Fraction 亲算逐位——零数值分歧；两笔未复算
项如实记。返工员-R22 复核：返工面空（零代码零数值工件改动），复算
员结论全部成立。本腿亲跑：endgame.json sha256==86863a09…69f 亲算
＋净树 env -i 白盒（PATH/HOME 外全剥离）验收命令原样复跑
r22c_closure_gate PASS exit 0（150.7s，ACCEPT_EXIT=0
亲捕，HEAD=a824cf8——两段式回填；C1 双门＋C1a＋C2 22 叶
＋C3 直读＋C4 三面＋C5 33.421/40＋C6 树净＋NC 双面全过，在途件收编
后 C6 树净语义恢复亲证）。轮次终判：closed=false 三面一致维持（存
档直读＋chain-only 干跑＋gate-③ 定量 ≥2 组在档 D34-4/D89-2）；
blocker L0/L3 不动（closed 重试不排 D90-3/D96-3）；assembledRecord
维持零提升；progress=true（D37-1/D96-3 严格口径——R22B TableB1Aut
21 定理零 sorry 落地表 B 第九件，streak 清零 forcePivot 不触发）。
未跑项如实：历史全门 gate-①②③⑥ 不重烧（≥2 组在档）；复算员/
返工员 /tmp 深度脚本面未复刻（其记录为证据源）。预算：本轮六腿
Σsolve_s==0 精确、0.037 当量全额留储；campaign 33.421/40 维持。
R23 候选：pattern_ident_lift 插入点形式消费（σ₀＋12 见证 feed
contract 数据层在库）／表 B 第十件或 B2–B4/B3 另议不排（D61-1）／
closed 重试不排——由 R23 设计师裁决（D101 顺延）。

## Round 22 一致性收口（执行员-R22-r22c-round22-closure，campaign dwfrun-f9904baf 第 17 轮，2026-10-24，0 求解）：endgame_gate campaign-17 增补＋r22c_closure_gate 新门——closed=false 三面一致维持／assembledRecord 维持／progress=true（严格口径：新严格引理 TableB1Aut 21 定理落地，表 B 第九件）

Round 22（campaign dwfrun-f9904baf 第 17 轮，2026-10-24）一致性收口
（GAP-REPORT 本轮节 ③；decisions D96/D97/D98/D99——D96 系设计师裁决
随 R22A 主件 1aee6cd 收编、D97/D98 系 R22A/R22B 执行裁决、D99 系本
收口裁决，下轮 D100 预留轮次汇总）。开工前置亲验：HEAD=244f864、
git status --porcelain 0 行净树（R22A 1aee6cd＋R22B 244f864 双主件在
链轮询亲见）。本会话亲跑：三跑时序（①扩展前基线 docs_check importlib
绝对路径直跑真门 PASS 十六锚／②扩展后落笔前负对照如期 GateFail——新
检查恰拦截／③落笔后正向复跑 PASS 十七锚）；r22c_closure_gate 组件级
importlib 自跑（C1 复跑 r22_pattern_gate 67.9s 非编
译门 300s 上限＋r22_b9aut_gate 83.9s 编译型 1200s
文档化例外——双门 exit 0＋结果锚 seed 20261022/heavy_solves==0 双件/
kind/task/artifact_class 隔离声明/endgame_chain.py 输入路由禁令/
provenance.read_only/axiom_policy 恰三标准/endgame.json sha256==
86863a09…69f 冻结锚＋C1a r22 家族放行层双路由＋C2 chain-only 干跑五
字段零漂移冻结 22 叶全归类＋C3 直读 closed=False/blocking=[L0,L3]/AR
47517790735835014335570/1844674407417822803119==25.759445973097478/
margin 0.0005405579025207914 float 逐位/wouldBe==25759986531/10⁹/
sha256==86863a09…69f 零改动＋铁律 AR≤E\*+1e-6 精确＋无容差 AR<E\*＋
E\*−AR==margin 逐位＋C4 文档三件锚 D96/D97/D98/D99 四 h3＋C5 预算本
轮 Σsolve_s==0 精确/campaign 33.421/40 五源 Fraction 双核验/r22 新产
物 2 件零正 solve＋NC1/NC2 篡改必拦未篡 sanity；C6 因在途自有件按设
计拦截——R11D 先例亲证）；主提交后净树 env -i 白盒（PATH/HOME 外全
剥离）验收命令原样复跑 r22c_closure_gate PASS exit 0
（152.2s，ACCEPT_EXIT=0 亲捕，HEAD=cae6efc
——两段式回填 D84-3/D88-4/D93-4）＋嵌套 CWD 包装器路由〔仓根
thomson-n9/…〕＋会话根包装器路由〔campaign 根 numerics/…，D7/D8/D9
先例〕亲跑 PASS exit 0。轮次终判：closed=false 三面一致维持（存档直
读＋chain-only 干跑＋gate-③ 定量 ≥2 组在档 R21C 1493.6s@95a353a＋
复算员 1508.1s@104e8b6——D34-4/D89-2 收口腿不三跑全门 D99-①）；
blocker L0/L3 不动（closed 重试不排 D90-3/D96-3）；assembledRecord
维持零提升；progress=true（D37-1/D96-3 严格口径——R22B TableB1Aut 21
定理零 sorry 落地表 B 第九件，streak 清零 forcePivot 不触发）。未跑
项如实：扩展后全门 gate-①②③⑥ 不三跑（≥2 组在档 D34-4/D89-2）；
R22A/R22B 会话亲跑记录（D97/D98）为第一证据源，本腿经 C1 子门复跑覆
盖。预算：本轮 Σsolve_s==0 精确、0.037 当量全额留储；campaign
33.421/40 维持。R23 候选：pattern_ident_lift 插入点形式消费／表 B 第
十件或 B2–B4/B3 另议不排（D61-1）／closed 重试不排（D90-3/D96-3，
D99-⑤ 预留 D100 由 R23 设计师裁决）。


## Round 21 轮次汇总（汇总员-R21，campaign dwfrun-f9904baf 第 16 轮，2026-10-24，0 求解）：复算分歧三条经返工腿 D94 闭合收编＋轮次终判汇总腿独立复核——closed=false 三面一致维持／assembledRecord 维持零提升／progress=true（严格口径：新严格引理 TableB5Chain 36 定理落地，表 B 第八件）

Round 21（campaign dwfrun-f9904baf 第 16 轮，2026-10-24）轮次汇总
（GAP-REPORT 本轮节 ④；decisions D95——汇总编号 D94 被返工勘误
裁决占用〔D94 裁决 6〕顺延 D95，下轮 D96）。开工前置亲验：HEAD=
33a845a（返工员-R21 D94 落账）、git status --porcelain 0 行净树。
复算员-R21 三条 discrepancies 全经返工腿闭合（D94）：分歧 1 数量
级措辞勘正（『四个数量级』→『约三个数量级』＝1448.5×——ecd3906
活性面四处直改＋D91 历史原文不动 D59 先例）＋分歧 2① 八包装器
路由亲跑闭合＋分歧 2② 经门覆盖注记 8×＋分歧 2③ 区间 LDLᵀ 承重
面核实（仓内 u₁ 认证＝闭式支配＋区间 Sylvester——零仓面改动）。
复算确认组收编：门复跑全 exit 0（r21_chain_gate 0.4s＋
r21_b5chain_gate 83.7s＋r21d_closure_gate 82.1s）＋全门 1508.1s
PASS FULLGATE_EXIT=0 亲捕＋自写 verify_r21.py 68/68 零 repo
import（AR/铁律/15 间隙重导/谱界 Sylvester＋精确曲线/ε 链 21 行/
L6 衔接/宣称抽查）。本腿亲跑：endgame.json 直读 closed=False/
blocking=[L0,L3]/组件 L1·L2·L5·L6·L7 rigorous=True＋L0·L3=False
＋L4 off-path＋AR 47517790735835014335570/1844674407417822803119
==25.759445973097478/margin 0.0005405579025207914/wouldBe==
25759986531/10⁹＋sha256==86863a09…69f 亲算＋铁律 AR≤E\*+1e-6 精确
＋无容差 AR<E\*＋E\*−AR==margin 逐位＋预算五源 Fraction 独立重加
==721885/2==33.421/40（口径 B 6.579<12）＋TableB5Chain/
TableB5ChainData 静态计数 36/35 定理、sorry 0/0＋decisions 前缀锚
（append 前 533232 字节 sha256==d9e94f3d…，D95 纯 EOF append）＋
docs_check 追加前基线与追加后保锚双跑十六锚＋净树 env -i 白盒
验收命令 r21d_closure_gate 复跑 PASS exit 0（79.8s，
ACCEPT_EXIT=0 亲捕——D94 执行留痕遗留项收账，两段式回填）。轮次
终判：closed=false 三面一致维持；blocker L0/L3 不动（closed 重试
不排 D90-3）；assembledRecord 维持零提升；progress=true（D37-1/
D90-3 严格口径——streak 清零，forcePivot 不触发）。未跑项如实：
全门不三跑（R21C 1493.6s＋复算员 1508.1s ≥2 组在档 D34-4/D89-2）；
复算员 verify_r21.py 深度复算面未复刻（其记录为证据源）；R21A
G2 cmp／R21B 十连 elaboration 继续经门覆盖口径不变。预算：本轮
六腿 Σsolve_s==0 精确、0.037 当量全额留储；campaign 33.421/40
维持。R22 候选：l4_orbit 组合枚举数值面／表 B 第九件或 B2–B4/B3
另议不排／closed 重试不排（D95 裁决 5）。

## Round 21 一致性收口（执行员-R21-r21c-round21-closure，campaign dwfrun-f9904baf 第 16 轮，2026-10-24，0 求解）：endgame_gate campaign-16 增补＋r21d_closure_gate 新门——closed=false 三面一致维持／assembledRecord 维持／progress=true（严格口径：新严格引理 TableB5Chain 36 定理落地，表 B 第八件）

Round 21（campaign dwfrun-f9904baf 第 16 轮，2026-10-24）一致性收口
（GAP-REPORT 本轮节 ③；decisions D90/D91/D92/D93——D90 系设计师
裁决随 R21A 主件 04138b5 收编、D91/D92 系 R21A/R21B 执行裁决、D93
系本收口裁决，下轮 D94 预留轮次汇总）。开工前置亲验：R21A 04138b5
（10-24 02:11）＋R21B f9a3978（10-24 03:34）两主件提交落链轮询亲
见、git status --porcelain 0 行净树（HEAD=f9a3978）。本会话亲跑：
三跑时序（①扩展前基线 docs_check importlib 绝对路径直跑真门
PASS 十五锚／②扩展后落笔前负对照如期 GateFail——新检查恰拦截／
③落笔后正向复跑 PASS 十六锚）；r21d_closure_gate 组件级 importlib
自跑（C1 复跑 r21_chain_gate 0.4s 非编译门 300s 上限＋r21_b5chain_gate
~80s 编译型 1200s 文档化例外——双门 exit 0＋结果锚 seed 20261021/
heavy_solves==0/隔离声明/路由禁令＋C1a r21 家族放行层双路由＋C2
chain-only 干跑五字段零漂移冻结 22 叶全归类＋C3 直读 closed=False/
blocking=[L0,L3]/AR 47517790735835014335570/1844674407417822803119
==25.759445973097478/margin 0.0005405579025207914 float 逐位/
wouldBe==25759986531/10⁹/sha256==86863a09…69f 零改动＋铁律 AR≤E\*
+1e-6 精确＋无容差 AR<E\*＋E\*−AR==margin 逐位＋C4 文档三件锚
D90/D91/D92/D93 四 h3＋C5 预算本轮 Σsolve_s==0 精确/campaign
33.421/40 五源 Fraction 双核验/r21 新产物 3 件零正 solve＋NC1/NC2
篡改必拦未篡 sanity——C6 因在途自有件按设计拦截 R11D 先例）；扩展后
全门后台＋轮询净树一跑（gate-① --reverify-certs 全量＋②③④⑥，
历史带 ~1500–1620s）PASS exit 0（1493.6s，净树 HEAD=95a353a；
gate-① reverify 全量 1493.4s；FULLGATE_EXIT=0 亲捕
/tmp/r21c_pre/fullgate_exit.txt——落历史带 R7 1493.8s−0.2s 带缘–
R13D 1620.7s、较 R19B 1485.9s 高 7.7s〔0.5%〕冷/暖缓存带内，两段式
回填沿 D84-3/D88-4）；主提交后净树 env -i 白盒（PATH/HOME 外全剥离）
验收命令原样复跑 r21d_closure_gate 全六项 PASS exit 0（77.6s，
ACCEPT_EXIT=0 亲捕 /tmp/r21c_pre/r21d_accept.log；嵌套/会话根包装器
路由另各一跑 79.4s/80.4s PASS）。轮次终判：closed=false 三面
一致维持（存档直读＋chain-only 干跑＋gate-③ 定量＝扩展后全门一跑）；
blocker L0/L3 不动（closed 重试不排 D90-3）；assembledRecord 维持
零提升；progress=true（R21B TableB5Chain 36 定理零 error 零 sorry
＋公理恰三标准——双源亲证）；预算终账本轮 Σsolve_s==0 精确、
0.037 当量全额留储。诚实声明与未跑项：R21A G2 cmp／R21B 十连
elaboration 面经 C1 子门复跑覆盖非本会话独立重算如实记；δ_ident/
ε_need float_advisory 分层＋L6Hyp 条件定理假设显式命名如实记；
墙钟回填位两段式。

## Round 20 轮次汇总（汇总员-R20，campaign dwfrun-f9904baf 第 15 轮，2026-10-24，0 求解）：复算分歧一条经返工腿闭合收编＋轮次终判第四组会话级独立复核——closed=false 维持／assembledRecord 维持／progress=false（严格口径如实：数值面审计件不构成新严格引理/新证书/纪录提升，R9D 先例）

Round 20（campaign dwfrun-f9904baf 第 15 轮，2026-10-24）轮次汇总
（GAP-REPORT 本轮节 ③；decisions D89——D86 预留位启用，下轮
D90 顺延）。开工前置亲验：HEAD=0809c73（返工员-R20 两段式回填）、
git status --porcelain 0 行净树。本会话亲跑（第四组会话级独立
证据）：endgame.json 直读 closed=False/blocking=[L0,L3]/绿
L1/L2/L5/L6/L7＋L0/L3/L4=False＋sha256 亲算 86863a09…69f 不变＋
铁律 AR≤E\*+1e-6 精确（无容差 AR<E\* 亦真、E\*−AR==margin float
逐位、wouldBe_if_chain_closed==E\*、spliceMap assembled_equal_R7
=true）；r20_seam_gate 全门 PASS exit 0（0.4s，G0–G4＋NC1–NC3）；
缝账本 12 行 supply 常数直读独立重算全命中（C_B 7.127939/C_A
18.957127/CVal 14.878732——CVal==l4.json C_exact 逐位恒等；
TableB5Data.lean def l3/u1 直读）；D87 勘误段偏差算术第三组
复算命中（B 0.2353%/0.1812%/0.0540%；A 0.0123%/0.0270%；
num 0.0929%/0.0270%）；预算五源 Fraction 独立重算==721885/2
精确=33.421/40、口径 B 余 6.579<12（r20_l5l6_seam 零正 solve
正则亲验）；decisions D86(:5437)/D87(:5539)/D88(:5673) 三 h3＋
D87 勘误追加段/勘误回填段/D88 结果追加回填段在档＋decisions.md
字节前缀面亲验（0809c73 blob 490388 字节前缀成立——D80-6）；
docs_check importlib 直跑追加前基线/追加后保锚双跑 PASS 十五锚。
复算收编：复算员确认组全数收编（全门净树复跑 1505.0s exit 0
FULLGATE_EXIT=0 亲捕——R20B nohup 裸发缺口补齐进程退出码独立
证据；探针重跑 cmp 逐位一致 37869 字节；区间路径 78/78＋LDLᵀ
40/40——l₃/u₁ 谱界独立矩阵分解背书；R20B 收口数字 52/52）；分歧
一条（D87 括注『偏差 ≤0.1%』对 B 档不成立——精确 0.235%）经
返工腿 edd3339＋0809c73 闭合收编（影响面零、判定面零变化）。
轮次终判（与证据严格对齐）：closed=false 三面一致维持（存档
直读＋chain-only 干跑 22 叶冻结分布＋gate-③ 定量〔R20B 1514.4s
＋复算员 1505.0s ≥2 组在档，本腿不三跑 D34-4〕）；blocker L0
洞片 [−153/200,−187/250] HP 兜底 margin 5.4056e-4（a5 M10
25.759951713654896 仍最优 E\*−3.4817e-5）＋L3 谱管 dead-at-(9,6)
零预算不动（R20A binding=L3 定量：三口径全组合不闭合 72.93×/
4.56×/9.11×，缝阈值 1.775821e-6/5.010615e-4/6.384070e-4——阻断
不动）；closed 重试不排（D86-3）；assembledRecord 维持零提升
（缝探针不入 12 分区，wouldBe==E\*）；progress=false 严格口径
如实（数值面审计件不构成新严格引理/新证书/纪录提升——R9D
收账轮先例，不硬凑）；预算终账 Σsolve_s==0、0.037 当量全额
留储。全链：1298b1c（R20A 五件＋D86/D87）→6a77d4a（R20B 收口
＋D88）→fb6650f（R20B 回填）→edd3339（复算勘误·返工员-R20）→
0809c73（勘误回填）→本汇总提交（GAP-REPORT ③＋PROGRESS 置顶＋
D89）；零求解零 SDP 零新证书零账本数值改动（endgame.json
sha256 不变亲算）。

## Round 20 一致性收口（执行员-R20-r20b-round20-closure，campaign dwfrun-f9904baf 第 15 轮，2026-10-13，0 求解）：endgame_gate campaign-15 增补＋r20c_closure_gate 新门——closed=false 三面一致维持／assembledRecord 维持／progress=false（严格口径如实：数值面审计件不构成新严格引理/新证书/纪录提升，R9D 先例）

Round 20（campaign dwfrun-f9904baf 第 15 轮，2026-10-13）一致性收口
（GAP-REPORT 本轮节 ②；decisions D88——D 编号顺延沿 D80-2/D82-5/
D84-2，轮次汇总预留 D89）。开工前置亲验：HEAD=1298b1c（R20A 缝探针
主件：r20_seam_probe.py＋r20_l5l6_seam.json＋notes/l5l6-seam.md＋
r20_seam_gate.py＋嵌套包装器＋D86 随主件收编＋D87 六件）、树净 0 行
亲验后动笔（D16-1）。本会话亲跑：扩展前基线 docs_check 绝对路径
importlib 直跑真门模块 PASS 十四锚（/tmp/r20b_pre/docs_baseline_
pre_ext.log）＋扩展后负对照同法直跑如期 GateFail『Round 20 节
（D86 裁决 4 消歧命名）』新检查恰拦截（D48-2 勿经会话根包装器，
/tmp/r20b_pre/docs_negctl_pre_write.log）＋文档三件落笔后正向复跑
PASS 十五锚；收口预检 chain-only 干跑 /tmp/r20b_pre/dryrun_probe.json
五字段逐位零漂移＋全集漂移 22 叶并行递归归类（certReverify 17＋
code_version/timestamp 2＋L1 quant 1＋engineV2 2，未归类 0——与
D84 裁决 4 冻结分布逐位同，R20A 审计件隔离面维持）；endgame.json
直读 closed=False/blocking=[L0,L3]/绿 L1/L2/L5/L6/L7＋L4 off-path＋
sha256 亲算 86863a09…69f 不变＋铁律 AR≤E\*+1e-6 精确（无容差
AR<E\* 亦真、E\*−AR==margin float 逐位、wouldBe==E\*、AR==min(12
分区)）；r20_l5l6_seam 账本锚直读（seed 20261020/heavy_solves=0/
kind/task/schema 三层口径词汇表＋隔离声明＋provenance.read_only＋
常数 routes 包络命中三路线 within_rounding 全 True）＋零正 solve
正则全零；预算终账五源直读（m9 102504.9＋m10 185065.6＋typed 末
rung 42305.7〔rungs==9〕＋hermite phase1 30542.1＋r11 探针 524.2）
==721885/2 精确=33.421/40、口径 B 余 6.579<12（M11 不可触发维持）。
轮次终判（与证据严格对齐）：closed=false 三面一致维持（存档直读＋
chain-only 干跑＋gate-③ 定量）；blocker L0 洞片 [−153/200,−187/250]
HP 兜底 margin 5.4056e-4（a5 M10 25.759951713654896 仍最优）＋L3
谱管 dead-at-(9,6) 零预算不动（R20A binding=L3 定量：三口径全组合
不闭合 72.9×/4.56×/9.11×，缝阈值 1.7758e-6/5.0106e-4/6.3841e-4——
阻断不动，数值面审计不改变终判 D86-3）；L4 off-path 非阻断；
closed 重试不排（账本无望全绿 D86 裁决 3）；assembledRecord 维持
零提升（缝探针不入 12 分区——R11C–R19 先例；wouldBe_if_chain_
closed=E\*）；progress=false 严格口径如实（数值面审计件不构成新
严格引理/新证书/纪录提升——R9D 收账轮先例，不硬凑）。新收口门
numerics/bounds/r20c_closure_gate.py（seed 20261020，CWD 无关）＋
嵌套 CWD 包装器：C1 r20_seam_gate 复跑（非编译门 300s 上限——零
Lean 编译无 1200s 编译型例外）＋账本锚/C2 干跑五字段＋漂移分布冻结
口径/C3 直读＋铁律＋sha256 零改动/C4 文档三件锚（D86/D87/D88）/
C5 预算双核验/C6 树净＋endgame.json 相对 HEAD 零改动双保险；门自身
负对照 NC1（篡 r20_l5l6_seam heavy_solves 0→1 ⇒ C1 锚拦）＋NC2
（篡四账本之一 total_solve_s +2000s ⇒ C5 冻结值拦）＋未篡副本
sanity；预提交自跑 C1–C5＋NC 全过（0.8s，C1a 0.4s——C6 因在途自有件
按设计拦截——R11D 起先例；r20_seam_gate G1 r20 家族放行层覆盖收口
在途自有件双路由）；提交后验收命令 env -i 白盒（PATH/HOME 外全
剥离）原样复跑全六项 PASS exit 0（**0.9s，ACCEPT_EXIT=0 亲捕**，
/tmp/r20b_pre/r20c_accept.log：C1a 0.4s＋C2 22 叶全归类＋C3 sha256
零改动＋C4 三面 True＋C5 33.421/40＋C6 树净＋NC 双面；嵌套包装器
与会话根包装器路由另各一跑均 PASS exit 0——三路由全通）＋
endgame_gate 扩展后全门 nohup 后台＋轮询净树一跑 PASS exit 0
（**1514.4s，gate-① reverify 全量 1514.3s，净树 HEAD=6a77d4a**，
gate-④ 十五锚〔campaign-15 节 Round 20 dwfrun-f9904baf＋D86 锚＋
历史十四锚〕；/tmp/r20b_pre/endgame_gate_full.log——进程退出码证据
＝门终止行自报『[gate] PASS（1514.4s）——exit 0』〔门 main() 仅在
return 0 前打印该行，R11D–R19B 同口径；nohup 外壳 FULLGATE_EXIT
echo 未保留如实记〕；第 21 墙钟数据点落 R7 1493.8s–R13D 1620.7s
历史带内，沿 5cc2e61/d52313a/704265e/dc642c3/e4f687e 两段式回填
先例本段回填落账）。
零求解零 SDP 零新证书零账本数值改动（endgame.json sha256 不变亲算）；
本提交只 add 自有件（endgame_gate.py 扩展＋r20c_closure_gate.py＋
嵌套包装器＋文档三件）。

## Round 19 轮次汇总（汇总员-R19，campaign dwfrun-f9904baf 第 14 轮，2026-10-13，0 求解）：复算分歧一条经返工腿闭合收编＋轮次终判第四组会话级独立复核——closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 TableB5Uncond 24 定理落地，表 B 第七件）

Round 19（campaign dwfrun-f9904baf 第 14 轮，2026-10-13）轮次汇总
（GAP-REPORT 本轮节 ③；decisions D85——沿 R13/R14/R15/R16/R17/
R18 汇总同款口径，D84 裁决 2 预留编号启用）。开工前置亲验：
HEAD=2939044（返工员-R19 两段式回填）、git status --porcelain
0 行净树。本会话亲跑（第四组会话级独立证据）：endgame.json 直读
closed=False/blocking=[L0,L3]/绿 L1/L2/L5/L6/L7＋L4 off-path＋
sha256 亲算 86863a09…69f 不变＋铁律 AR≤E\*+1e-6 精确（无容差
AR<E\* 亦真、E\*−AR==margin float 逐位、wouldBe==E\*）；chain-only
干跑 /tmp/r19sum_dry.json 九组逐位零漂移＋全集漂移 22 叶并行递归
归类（certReverify 17＋code_version/timestamp 2＋L1 quant 1＋
engineV2 2，未归类 0——与 D84 裁决 4 入冻分布逐位同）；TableB5
Uncond.lean 亲 grep `^theorem`==24/sorry==0/wc -l==997＋sha256==
c79fc623… 同锚＋TableB5Polar sha256==d8c58f7d…8516 冻结锚＋/tmp/
r19a_axioms.log 直读 24 行恰三标准零 sorryAx；r19_b5u_ledger 锚
直读（seed 20261019/heavy_solves=0/theorem_count=24〔lean_
theorems_uncond==24 同值〕/公理恰三标准 set 相等＋零正 solve 正则）；
decisions D82(:5232)/D83(:5242)/D84(:5253) 三 h3 在档＋字节前缀面
亲验（anchored==46860e2 blob 447231 字节为前缀、追加 11381 字节
纯 append——D80-6 机制）；预算终账五源 Fraction 独立重算
（102504.9＋185065.6〔两读路同值〕＋42305.7＋30542.1＋524.2）
==721885/2 精确=33.421/40、口径 B 余 6.579<12（M11 不可触发
维持）；复算员独立脚本亲复跑 ALL_OK exit 0（125 项 [PASS] 零
FAIL，/tmp/r19sum/r19_independent_audit_rerun.log）；/tmp 在档
日志直读抽查十三件全对上（r19b_pre 六件＋r19_audit 三件＋
r19_rework 四件）；全链 7 提交实序时间戳亲验（dc642c3→a637d66→
46860e2→9428692→e4f687e→ccdebc7→2939044）；docs_check
importlib 绝对路径直跑真门追加前基线 PASS 十四锚
（/tmp/r19sum/docs_baseline_pre_append.log）。轮次终判（与证据
严格对齐）：closed=false 三面一致维持（存档直读＋chain-only 干跑
＋gate-③ 定量〔R19B 1485.9s＋复算员 1555.9s ≥2 组在档，本腿
不三跑 D85 裁决 2〕）；blocker L0 洞片 [−153/200,−187/250] HP
兜底 margin 5.4056e-4（a5 M10 25.759951713654896 仍最优）＋L3
谱管 dead-at-(9,6) 零预算不动；L4 off-path 非阻断；closed 重试
不排（账本无望全绿 D82 裁决 4）；assembledRecord 维持零提升
（TableB5Uncond 形式层件不入 12 分区——R11C–R18 先例；
wouldBe_if_chain_closed=E\*）；progress=true 严格口径（表 B
第七件 ≥1 严格定理落地即 true；新证书 0/纪录提升 0 如实；
路线 A 已落地——D83 裁决 1 无阻断、D82 可回滚点未启用）。
复算收编：discrepancies 三条——第 1 条（C1a 墙钟 58.7 vs 58.6
混引）经返工腿 ccdebc7＋2939044 闭合收编（就地勘正＋D84 勘误
追加段＋净树复跑 58.5s PASS 回填；判定面与账本数字零影响）、
第 2/3 条非分歧如实收编（墙钟带内/未跑项口径准确）。表 B 七件
落位、B5 解析本体形式层全链无条件化收官；下轮候选维持本轮节
清单（B2–B4 待 B3 另议/L5 数值消费小探针可议/thomson_nine 不
承诺/RC2 待 ≥2.799/M11 待 ≥12/L0 瓶颈不动）。零求解零 SDP 零
新证书零账本数值改动（endgame.json sha256 不变亲算）；本提交
只 add 文档三件（GAP-REPORT Round 19 节 ③＋PROGRESS 置顶＋
decisions D85）。

## Round 19 一致性收口（执行员-R19-r19b-round19-closure，campaign dwfrun-f9904baf 第 14 轮，2026-10-12，0 求解）：endgame_gate campaign-14 增补＋r19c_closure_gate 新门——closed=false 三面一致维持／assembledRecord 维持／progress=true（严格口径：新严格引理 TableB5Uncond 24 定理落地，表 B 第七件）

Round 19（campaign dwfrun-f9904baf 第 14 轮，2026-10-12）一致性收口
（GAP-REPORT 本轮节 ②；decisions D84——D 编号顺延沿 D80-2/D82-5，
轮次汇总预留 D85）。开工前置亲验：HEAD=46860e2（R19A 无条件化主件：
TableB5Uncond.lean 24 定理＋r19_b5u_gate＋r19_b5u_ledger＋tableb-lean
§7＋D82/D83 六件）、树净 0 行亲验后动笔（D16-1）。本会话亲跑：
扩展前基线 docs_check 绝对路径 importlib 直跑真门模块 PASS 十三锚
（/tmp/r19b_pre/docs_baseline_pre_ext.log）＋扩展后负对照同法直跑
如期 GateFail『Round 19 节（D82 裁决 4 消歧命名）』新检查恰拦截
（D48-2 勿经会话根包装器，/tmp/r19b_pre/docs_negctl_pre_write.log）
＋文档三件落笔后正向复跑 PASS 十四锚；chain-only 干跑
/tmp/r19c_dry.json 五字段逐位零漂移＋全集漂移 22 叶全叙述性预期
（certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2
——与 R18C 同叶数同分布，收口预检 /tmp/r19b_pre/dryrun_probe.json
亲跑确认）；endgame.json 直读 closed=False/blocking=[L0,L3]/绿
L1/L2/L5/L6/L7＋L4 off-path＋sha256 亲算 86863a09…69f 不变＋铁律
AR≤E\*+1e-6 精确（无容差 AR<E\* 亦真、E\*−AR==margin float 逐位、
wouldBe==E\*、AR==min(12 分区)）；r19_b5u_ledger 锚直读（seed
20261019/heavy_solves=0/theorem_count=24〔lean_theorems_uncond==24
同值〕/公理恰三标准 set 相等）；TableB5Uncond.lean 亲 grep
`^theorem`==24/sorry==0/wc -l==997；预算终账五源直读（m9 102504.9＋
m10 185065.6＋typed 末 rung 42305.7〔rungs==9〕＋hermite phase1
30542.1＋r11 探针 524.2）==721885/2 精确=33.421/40、口径 B 余
6.579<12（M11 不可触发维持）；R19 新产物零正 solve 正则全零。
轮次终判（与证据严格对齐）：closed=false 三面一致维持（存档直读＋
chain-only 干跑＋gate-③ 定量）；blocker L0 洞片 [−153/200,−187/250]
HP 兜底 margin 5.4056e-4（a5 M10 25.759951713654896 仍最优）＋L3
谱管 dead-at-(9,6) 零预算不动；L4 off-path 非阻断；closed 重试不排
（账本无望全绿 D82 裁决 4）；assembledRecord 维持零提升
（TableB5Uncond 形式层件不入 12 分区——R11C–R18 先例；
wouldBe_if_chain_closed=E\*）；progress=true 严格口径（表 B 第七件
≥1 严格定理落地即 true；新证书 0/纪录提升 0 如实；路线 A 已落地
——D83 裁决 1 无阻断、D82 可回滚点未启用）。新收口门
numerics/bounds/r19c_closure_gate.py（seed 20261019，CWD 无关）＋
嵌套 CWD 包装器：C1 r19_b5u_gate 复跑（编译型门 1200s 文档化例外
D80-1）＋账本锚/C2 干跑五字段＋漂移分布冻结口径/C3 直读＋铁律＋
sha256 零改动/C4 文档三件锚（D82/D83/D84）/C5 预算双核验/C6 树净
＋endgame.json 相对 HEAD 零改动双保险；门自身负对照 NC1（篡
r19_b5u_ledger heavy_solves 0→1 ⇒ C1 锚拦）＋NC2（篡四账本之一
total_solve_s +2000s ⇒ C5 冻结值拦）＋未篡副本 sanity；预提交自跑
C1–C5＋NC（C6 因在途自有件按设计拦截——R11D 起先例）；提交后验收
命令 env -i 白盒（PATH/HOME 外全剥离）原样复跑全六项 **PASS exit 0
（59.1s，ACCEPT_EXIT=0 亲捕，/tmp/r19b_pre/r19c_accept.log）**＋
endgame_gate 扩展后全门 nohup 后台＋轮询净树一跑 **PASS exit 0
（1485.9s，gate-① reverify 全量 1485.8s，FULLGATE_EXIT=0 亲捕，
/tmp/r19b_pre/endgame_gate_full.log：gate-④ 十四锚全过〔campaign-14
节＋D82 锚＋历史十三锚〕；与历史带 R7 1493.8s–R13D 1620.7s 同量级、
较带内最小 R18C 1491.7s 低 5.8s〔0.39%〕缓存暖态如实记）**，沿
5cc2e61/d52313a/704265e/dc642c3 两段式回填先例本段回填落账。零求解零 SDP 零新证书零账本数值改动（endgame.json sha256
不变亲算）；本提交只 add 自有件（endgame_gate.py 扩展＋r19c_closure
_gate.py＋嵌套包装器＋文档三件）。

## Round 18 轮次汇总（汇总员-R18，campaign dwfrun-f9904baf 第 13 轮，2026-10-12，0 求解）：复算确认收编（零分歧零返工腿）＋轮次终判第四组会话级独立复核——closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B5c TableB5Polar 42 定理落地，表 B 第六件）

Round 18（campaign dwfrun-f9904baf 第 13 轮，2026-10-12）轮次汇总
（GAP-REPORT 本轮节 ④；decisions D81——沿 R13/R14/R15/R16/R17
汇总同款口径，D77 裁决 3 预留编号）。开工前置亲验：HEAD=dc642c3
（R18C 两段式回填）、树净 0 行、复算员结果 discrepancies==[] 已
落链。本会话亲跑第四组会话级独立复核：endgame.json 直读
（closed=False/blocking=[L0,L3]/绿 L1/L2/L5/L6/L7＋L4 off-path）＋
sha256 亲算==86863a09…69f（R10 基线不变）＋chain-only 干跑
/tmp/r18sum_dry.json 九项比对零漂移＋复算员独立脚本三件亲复跑
全过（r18_iron_rule ALL_OK：AR≤E\*+1e-6 精确＋无容差 AR<E\* 亦真
＋E\*−AR==0.0005405579025207914 逐位＋argmin==分区 10 洞片＋12
分区无缝盖满；r18b_recompute PASS：det(XᵀX)≠0 与 frob D∥² 两数
自写 LCG/Bareiss 独立复现逐位；r18_ldlt_bareiss PASS：两
TTP-covering 证书 56 方块整数化 Bareiss 顺序主子式全精确正定、
负对照 4 项有牙）＋定理计数亲 grep TableB5Polar `^theorem`==42/
sorry==0/wc -l==854（净本体 744）＋r18_b5c_ledger 锚直读（seed
20261018/heavy_solves=0/theorem_count=42〔lean_theorems_polar==42
同值〕/公理恰三标准
set 相等＋零正 solve 正则）＋三门 SEED_GATE==20261018＋
dperp-gap-study.md 863 行 heavySolves=0 字面＋decisions D77
（:4917）/D78（:4968）/D79（:5021）/D80（:5063）四节在档＋D80-6
修复面源码亲验（r18_b5c_gate.py:720/:747 git 溯源 append-only
前缀验证＋账本 files_note 2add9429… 双记）＋预算终账五源直读
独立重算（m9 102504.9＋m10 185065.6〔budget.total_solve_s==rows
Σ 两读路同值〕＋typed 末 rung 42305.7〔rungs==9〕＋hermite
phase1 30542.1＋r11 探针 524.2）==721885/2 精确＝33.421/40、
口径 B 余 6.579<12（M11 不可触发维持）＋/tmp 在档日志九件抽查
全对上（复算员四件＋R18C 五件全 exit 0/负对照如期）＋全链 5
提交 a6ebaf6→31282cb→553dd38→77ff0b3→dc642c3 实序时间戳亲验＋
docs_check importlib 绝对路径直跑追加前基线 PASS 十三锚。轮次
终判（与证据严格对齐）：closed=false 三面一致维持（存档直读＋
干跑零漂移＋gate-③ 定量——R18C 1491.7s＋复算员 1497.2s 两组
全门在档，D34-4 ≥2 组口径本会话不三跑 D81 裁决 1）；blocker
L0 洞片 HP 兜底 margin 5.4056e-4（a5 M10 25.759951713654896
仍最优）＋L3 谱管 dead-at-(9,6) 零预算不动；assembledRecord 维持
零提升（B5c/R18B 形式层件不入 12 分区——R11C–R17 先例；
wouldBe==E\*）；progress=true 严格口径（新严格引理 B5c 42 定理
表 B 第六件；新证书 0/纪录提升 0 如实；B5c 无条件终定理未证
如实——step6_final 条件化三前提字面携带，无条件化归 R19 双
路线供件）。下轮候选维持 R18C 清单：B5c 步骤 6 无条件化双路线
（B E(I−P₀) 面快胜件→A σ₃(Y) 自举串行——R18B §6/D79-5）为
下一件；L0 洞片全局瓶颈维持，无新求解预算不重试。

## Round 18（campaign dwfrun-f9904baf 第 13 轮）收口（执行员-R18-r18c-round18-closure，2026-10-12，0 求解）：一致性收口——B5c 极分解件 42 定理（表 B 第六件）＋B5c 步骤 6 缺口研究件收编＋endgame_gate campaign-13 增补＋r18c_closure_gate 六面门；closed=false 三面一致维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B5c TableB5Polar 42 定理落地，表 B 第六件）

Round 18（campaign dwfrun-f9904baf 第 13 轮，2026-10-12）r18c 收口
（GAP-REPORT 本轮节 ③；decisions D80——沿 R8C/R9D/R10D/R11D/
R12C/R13D/R14B/R15D/R16C/R17C 收口同款口径）。开工前置亲验：
HEAD=553dd38（R18B）、树净 0 行、R18A 31282cb（10-12 07:08）→
R18B 553dd38（10-12 20:04）提交实序亲见（D16-1 防撞纪律）。本会话
亲跑：①chain-only 干跑 /tmp/r18c_dry.json exit 0 五字段组逐位零
漂移＋全集漂移 22 叶全叙述性归类（certReverify 17＋
code_version/timestamp 2＋L1 quant 1＋engineV2 2，未归类 0——
r18c_closure_gate C2 机器化）＋②endgame.json 直读（closed=False/
blocking=[L0,L3]/绿 L1/L2/L5/L6/L7＋L4 off-path）＋sha256 亲算
==86863a09…69f（R10 基线不变）＋铁律 Fraction 双面（AR≤E\*+1e-6
精确＋无容差 AR<E\* 亦真、E\*−AR==0.0005405579025207914 逐位）＋
AR==min(12 分区) Fraction 精确重算＋③endgame_gate gate-④ 增补式
扩展 campaign-13 节（regex『Round 18（campaign dwfrun-f9904baf』
＋D77 锚，历史 Round 8–17 检查全保留）：扩展前基线 docs_check
importlib 直跑真门 PASS 十二锚（/tmp/r18c_pre/
docs_baseline_pre_ext.log）＋扩展后负对照 Round 18 节未落笔时点
如期 GateFail 恰在新检查拦截（/tmp/r18c_pre/docs_negctl_pre_write.log
——D48-2 勿经会话根包装器）＋文档三件落笔后正向复跑 PASS 十三锚
＋扩展后全门后台＋轮询净树一跑 PASS 1491.7s（gate-① reverify
全量 1491.5s——两段式回填落账，GAP-REPORT ③ 回填位）＋
⑤r18c_closure_gate 六面门（seed
20261018：C1 两子门复跑 r18_b5c_gate〔编译型门 1200s 文档化例外
——内部每文件 600s 界不变 D64-5〕＋r18b_dperp_gate 各 exit 0＋
结果锚〔r18_b5c_ledger seed 20261018/heavy_solves=0/
theorem_count=42/公理恰三标准；R18B 腿沿 D70-1/D75-1 降格〕＋C2
干跑＋C3 铁律＋C4 文档三件〔D77/D78/D79/D80〕＋C5 预算＋C6 树净＋
NC 双面；提交后净树 env -i 白盒原样复跑 PASS 71.6s（C1a 71.1s＋
C1b 0.1s——两段式回填落账，GAP-REPORT ⑤ 回填位）＋⑥树净终验。轮次终判（与证据严格对齐）：closed=false
三面一致维持（存档直读＋干跑零漂移＋gate-③ 定量）；blocker L0
洞片 [−153/200,−187/250] HP 兜底 margin 5.4056e-4（a5 M10
25.759951713654896 仍最优）＋L3 谱管 dead-at-(9,6) 零预算不动；
M11 触发器 6.579<12 不可触发维持；closed 重试不排（D77-4）。
assembledRecord 维持 47517790735835014335570/
1844674407417822803119=25.759445973097478 零提升（B5c 形式层件
不入 12 分区——R11C–R17 先例；wouldBe==E\*）；progress=true
严格口径（新严格引理 B5c TableB5Polar 42 定理表 B 第六件；新证书
0/纪录提升 0 如实；**B5c 无条件终定理未证如实**——step6_final 系
条件化定理〔hdpar/hdom1/hdom2 三前提字面携带〕，无条件 d_P ≤ C·δ
不宣称，R18B 反射族反例机器核验证明该前提在反射族下被违）。
预算终账：本轮 Σsolve_s==0 精确（全任务 heavySolves=0）；campaign
360942.5s==721885/21600==33.421/40（与 R11–R17 终账逐位不变，
账↔文档双核验）；口径 B 余 6.579<12。下轮候选：B5c 步骤 6
无条件化双路线（B E(I−P₀) 面快胜件→A σ₃(Y) 自举串行共享面一次
入库——R18B §6 排期判断）为下一件；L0 洞片全局瓶颈维持，无新
求解预算不重试。


## Round 17 轮次汇总（汇总员-R17，campaign dwfrun-f9904baf 第 12 轮，2026-10-12，0 求解）：复算确认收编（零分歧零返工腿）＋轮次终判第四组会话级独立复核——closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B5b 44 定理落地，表 B 第五件）

Round 17（campaign dwfrun-f9904baf 第 12 轮，2026-10-12）轮次汇总
（GAP-REPORT 本轮节 ④；decisions D76——沿 R13/R14/R15/R16 汇总
同款口径）。开工前置亲验：HEAD=40c46d5（R17C 两段式回填）、树净
0 行、复算员结果 discrepancies==[] 已落链。本会话亲跑第四组会话级
独立复核：endgame.json 直读（closed=False/blocking=[L0,L3]/绿
L1/L2/L5/L6/L7＋L4 off-path）＋sha256 亲算==86863a09…69f（R10
基线不变）＋铁律 Fraction 双面（AR≤E\*+1e-6 精确＋无容差 AR<E\*
亦真、E\*−AR==0.0005405579025207914 逐位）＋AR==min(12 分区
claimed_bound) argmin==[−153/200,−187/250]（L0 洞片）＋chain-only
干跑 /tmp/r17sum_dry.json 五字段组逐位零漂移＋复算员独立脚本
PartA/PartB 亲复跑全过（Part A 全过＋Part B 两 covering 证书 62
方块 Fractions LDLᵀ 全半正定含 165×165/120×120 大块、负对照双面
有牙，1 分 32.6s，跑后树净）＋定理计数亲 grep TableB5Trace
`^theorem`==44/sorry==0＋r17_b5b_ledger 锚直读（seed 20261017/
heavy_solves=0/theorem_count=44/lean_theorems_trace==44/公理恰三
标准列表）＋b5c-assembly-probe.md 852 行 heavySolves=0 字面＋
r17_b5c2_gate.py:56 SEED_GATE==20261017＋decisions D72（:4571）/
D73（:4731）/D74（:4663）/D75（:4796）四节在档＋预算终账五源
直读独立重算（m9 rows Σ102504.9＋m10 185065.6＋typed rung
42305.7＋hermite phase1 30542.1＋r11 探针 8 runs 524.2 直读闭合）
==721885/2 精确＝360942.5s＝33.421/40、口径 B 余 6.579<12（M11
不可触发维持）＋/tmp 在档日志抽查全对上（r17a_gate_run3 248.2s
PASS/endgame_gate_full 1601.2s PASS FULLGATE_EXIT=0/r17c_accept
76.2s PASS ACCEPT_EXIT=0）＋全链 5 提交 8a68362→670afec→4ce494b
→9fdca2f→40c46d5 实序时间戳亲验＋docs_check/c4_docs 双组件
importlib 直跑追加前基线 PASS（gate-④ 十二锚＋C4 三面）。轮次
终判（与证据严格对齐）：closed=false 三面一致维持（存档直读＋
干跑零漂移＋gate-③ 定量——R17C 1601.2s＋复算员 1608.0s 两组
全门在档，D34-4 ≥2 组口径本会话不三跑）；blocker L0 洞片 HP
兜底 margin 5.4056e-4（a5 M10 25.759951713654896 仍最优）＋L3
谱管 dead-at-(9,6) 零预算不动；assembledRecord 维持零提升（B5b/
R17B 形式层件不入 12 分区——R11C–R16 先例；wouldBe==E\*）；
progress=true 严格口径（新严格引理 B5b 44 定理表 B 第五件；新
证书 0/纪录提升 0 如实）。下轮候选维持 R17C 清单：B5c 本体
≈450–650（Q3→Q1→Q2→Q4→装配）为下一件。两处口径注记（D76
裁决 3）：TableB5Trace wc -l 亲测 1016（R17A 自述 1018 系其会话
内计数口径偏差，git show 4ce494b 亦 1016——定理计数 44 锚定面
不受影响）；r11 探针 524.2 直读闭合替代沿冻结值口径（账面不变）。

## Round 17（campaign dwfrun-f9904baf 第 12 轮）收口（执行员-R17-r17c-round17-closure，2026-10-12，0 求解）：一致性收口——B5b 44 定理＋B5c 四探针收编＋endgame_gate campaign-12 增补＋r17c_closure_gate 六面门；closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B5b 44 定理落地，表 B 第五件）

Round 17（campaign dwfrun-f9904baf 第 12 轮，2026-10-12）收口
（GAP-REPORT 本轮节 ③；decisions D75）。依赖 R17B（670afec：B5c
前置探针补全四件零入库＋D74）＋R17A（4ce494b：B5b trace/范数压缩层
TableB5Trace 44 定理＋D72 随主件收编＋D73）两提交全落、开工时点轮询
亲见 670afec〔10-11 19:00〕→4ce494b〔10-12 02:39〕实序＋树净 0 行
亲验后执行——收口全程不触并行在途件（D16-1）。本会话亲跑：
chain-only 干跑（/tmp/r17c_dry.json）五字段逐位零漂移＋全集漂移
22 叶机器化归类（certReverify 17＋code_version/timestamp 2＋L1
quant 1＋engineV2 2，未归类 0）＋endgame.json 直读
（closed=False/blocking=[L0,L3]/绿 L1/L2/L5/L6/L7/L4 off-path）＋
sha256 亲算（86863a09…69f 不变，与 R10–R16 基线时点相等）＋铁律
AR≤E\*+1e-6 精确（E\*−AR 逐位==margin 0.0005405579025207914，无容差
AR<E\* 亦真）＋扩展前基线 docs_check（importlib 绝对路径直跑真门
PASS 十一锚——HEAD=4ce494b 时点，R17A/R17B 未落地窗口不可得如实取
HEAD 时点）＋扩展前负对照（Round 17 节未落笔时点同法直跑如期
GateFail『④ GAP-REPORT.md 无『Round 17（campaign dwfrun-f9904baf』
本轮节』——D48 裁决 2 教训勿经会话根包装器）＋落笔后正向复跑 PASS
十二锚＋r17c_closure_gate 预提交自跑 C1–C5＋NC（C6 因在途自有件按
设计拦截——R11D/R12C/R13D/R14B/R15D/R16C 先例；C1a/C1b 子门 G1 走
r17 家族放行层零环境变量）。收口交付：endgame_gate.py gate-④
campaign-12 增补（regex『Round 17（campaign dwfrun-f9904baf』＋D72
锚三检查，历史 Round 8–16 检查全保留）＋r17c_closure_gate.py（C1 两
子门复跑＋结果锚〔R17B 腿沿 D70-1 降格：探针件＋门源码 seed 锚〕＋
C2–C6＋NC 双面）＋嵌套 CWD 包装器＋文档三件＋D75 收口裁决（含两段
式回填段）。轮次终判：closed=false 三面一致维持（直读＋干跑＋gate-③
定量〔扩展后全门净树一跑 PASS exit 0 1601.2s——gate-① reverify 全量
1601.0s＋gate-④ 十二锚，/tmp/r17c_pre/endgame_gate_full.log；提交后
验收命令 env -i 白盒复跑 PASS exit 0 76.2s——C1a 75.6s＋C1b 0.2s，
/tmp/r17c_pre/r17c_accept.log；两段式回填落账〕）、blocker L0 洞片
[−153/200,−187/250] HP 兜底
margin 5.4056e-4（a5 M10 25.759951713654896 仍最优）＋L3 谱管
dead-at-(9,6) 零预算不动、M11 触发器 6.579<12 不可触发维持、closed
重试不排（账本无望全绿）；assembledRecord 维持 25.759445973097478
零提升（B5b/R17B 形式层件不入 12 分区——R11C–R16 先例；
wouldBe_if_chain_closed=E\*）；progress=true（新严格引理 B5b 44 定理
落地表 B 第五件；新证书 0/纪录提升 0 如实）；heavySolves=0（0.037
当量全额留储 D72-3）。下轮候选：B5c 本体按 ≈450–650 行口径
（R17B §5『若现成则 ≈450–650』条件成立——R17A 路线 (a) 列压缩已
收口；施工顺序 Q3→Q1→Q2→Q4→装配）；B2–B4 待 B3；thomson_nine 不
承诺；RC2 ≥2.799/M11 ≥12 待触发。

## Round 16（campaign dwfrun-f9904baf 第 11 轮）轮次汇总（汇总员-R16，2026-10-11，0 求解）：复算确认收编（零分歧零返工腿）＋轮次终判第四组会话级独立复核——closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B5a 16 定理落地，表 B 第四件）

Round 16（campaign dwfrun-f9904baf 第 11 轮，2026-10-11）汇总终版
（GAP-REPORT 本轮节 ④；decisions D71）。开工 HEAD=c86d96a 净树
0 行亲验，复算员结果（discrepancies==[] 零分歧）已落链——无返工腿
（对照 R15 两分歧＋dae9596，本轮如实无），本节收编其确认组并以
第四组会话级证据独立复核。本会话亲跑：endgame.json 直读
（closed=False/blocking=[L0,L3]/绿 L1/L2/L5/L6/L7）＋sha256 亲算
（86863a09…69f 不变）＋铁律 AR≤E\*+1e-6 精确（E\*−AR 逐位==margin
0.0005405579025207914，无容差 AR<E\* 亦真）＋chain-only 干跑五字段
零漂移（漂移叶全归类未归类 0）＋复算员独立脚本亲复跑两遍全过
exit 0（Part A：E\* 三源/AR 分数与 float repr 逐字符/argmin==第 10
片 HP 兜底/12 分区无缝/exclusion 10 片全>E\*/covering 2 片全≤
E\*+1e-6/12 证书三方一致/sha256；Part B：4 证书 140 PSD 块自写
LDLᵀ 全正定含 120×120 与 165×165 最大块＋负对照有牙）＋全链 6
提交实序时间戳亲验（bdadf69 16:01→eee0343 16:11→8689431 16:19→
704265e 16:51→c86d96a 16:57）＋定理计数亲 grep TableB5Core==16＋
r16_b5a_ledger 锚直读（seed 20261017/heavy_solves=0/theorem_count
=16/公理恰三标准）＋预算终账独立重算（m9 102504.9＋m10 185065.6＋
typed_ladder m0748_M9 rung 42305.7〔九 rung 亲读、只计该 rung 的
R8 冻结口径——复算员口径注记收编〕＋hermite_v2 phase1 30542.1＋
r11 探针 8 runs 524.2==721885/2 精确、33.421/40、口径 B 6.579<12
M11 不可触发维持）＋复算/收口在档 /tmp 日志抽查全对上
（r16audit_r16c_accept 226.3s＋r16audit_endgame_gate_full 1639.3s
FULLGATE_EXIT=0）＋docs_check/c4_docs 双组件 importlib 直跑 PASS
（本节追加前后双跑保锚）。轮次终判：closed=false 三面一致（直读＋
干跑＋gate-③ 定量两组全门在档——R16C 1615.4s＋复算员 1639.3s，
D34-4『≥2 组不重复消耗』口径本会话不三跑）、assembledRecord 维持
25.759445973097478 零提升（B5a/R16B 形式层件不入 12 分区——
R11C–R15 先例）、progress=true（新严格引理 B5a 16 定理落地表 B
第四件；新证书 0/纪录提升 0 如实）、heavySolves=0（0.037 当量全额
留储 D67-3）。closed 重试不排（L0 洞片 [−153/200,−187/250]＋L3
谱管 dead-at-(9,6) 零预算不动、M11 触发器 6.579<12 不可触发维持）。
下轮候选：B5b trace 件（B5a 陈述面底座已定死，建议一并探
Frobenius↔L2op 比较 API）→B5c 本体 ≈450–800 行；B2–B4 待 B3；
thomson_nine 不承诺；RC2 ≥2.799/M11 ≥12 待触发。

## Round 16（campaign dwfrun-f9904baf 第 11 轮）收口（执行员-R16-r16c-round16-closure，2026-10-11，0 求解）：一致性收口——B5a 首件＋B5c 探针收编＋endgame_gate campaign-11 增补＋r16c_closure_gate 六面门；closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B5a 落地，表 B 第四件）

Round 16（campaign dwfrun-f9904baf 第 11 轮，2026-10-11）收口
（GAP-REPORT 本轮节 ③；decisions D70）。依赖 R16A（bdadf69：B5a
纯代数层 16 定理＋D67 随主件收编＋D68）＋R16B（eee0343：B5c 谱夹逼
三件零入库探针 671 行＋D69）两提交全落、树净 0 行亲验后执行——收口
全程不触并行在途件（D16-1）。本会话亲跑：chain-only 干跑
（/tmp/r16c_dry.json）五字段逐位零漂移＋全集漂移 22 叶机器化归类
（certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2，
未归类 0）＋endgame.json 直读（closed=False/blocking=[L0,L3]/绿
L1/L2/L5/L6/L7）＋sha256 亲算（86863a09…69f 不变，与 R10–R15 基线
时点相等）＋铁律 AR≤E\*+1e-6 精确（E\*−AR 逐位==margin 0.0005405579
025207914，无容差 AR<E\* 亦真）＋AR==min(12 分区 bound) Fraction 精确
重算＋citedCertificates 12 份在盘对账＋扩展前基线 docs_check
（importlib 绝对路径直跑真门 PASS 十锚——扩展前时点 HEAD=eabf6db）＋
扩展前负对照（Round 16 节未落笔时点同法直跑如期 GateFail『④
GAP-REPORT.md 无『Round 16（campaign dwfrun-f9904baf』本轮节』——
D48 裁决 2 教训勿经会话根包装器）＋落笔后正向复跑 PASS 十一锚＋
r16c_closure_gate 预提交自跑 C1–C5＋NC（C6 因在途自有件按设计拦截
——R11D/R12C/R13D/R14B/R15D 先例；C1a/C1b 子门 G1 走 r16 家族放行层
零环境变量）。收口交付：endgame_gate.py gate-④ campaign-11 增补
（『Round 16（campaign dwfrun-f9904baf』regex＋D67 锚三检查，历史
Round 8–15 检查全保留——D29-5/D34-4/D38-5/D43-5/D49-3/D52-5/D56-4/
D61-5 先例链；docstring ④ 段同步）＋numerics/bounds/r16c_closure_gate.py
（seed 20261017，CWD 无关；C1 两子门复跑〔r16_b5a_gate＋r16_b5c_gate
各 exit 0 ≤600s〕＋结果锚〔r16_b5a_ledger：seed/heavy_solves==0/
theorem_count==16/公理恰三标准列表形态；R16B 腿＝notes 件＋门源码
SEED_GATE 锚——D64 裁决 1 降格先例〕＋C2 干跑零漂移＋C3 sha256＋铁律
＋C4 文档三件〔D67/D68/D69/D70〕＋C5 预算〔Σsolve_s==0 精确、
campaign 360942.5s=721885/2=33.421/40 与 R11–R15 逐位不变、口径 B
6.579<12〕＋C6 树净＋NC 双面）＋嵌套 CWD 包装器＋GAP-REPORT Round 16
节 append-only＋PROGRESS 置顶＋decisions D70 收口裁决。轮次终判：
closed=false 三面一致（直读＋干跑＋gate-③ 定量）、assembledRecord
维持 25.759445973097478 零提升（B5a/R16B 形式层件不入 12 分区——
R11C/R12/R13/R14/R15 先例）、progress=true（B5a 新严格引理 16 定理
≥1 落地即 true；新证书 0/纪录提升 0 如实）、heavySolves=0（0.037
当量全额留储 D67-3）。closed 重试不排（L0 洞片＋L3 谱管零预算不动、
M11 触发器 6.579<12 不可触发维持）。下轮候选：B5b trace 件（B5a
陈述面底座已定死）→B5c 本体 ≈450–800 行；RC2 ≥2.799/M11 ≥12 待
触发。扩展后全门净树一跑与验收复跑墙钟两段式回填（沿 5cc2e61/
d52313a 先例，见 GAP-REPORT 本轮节 ③⑤ 回填位）。

## Round 15（campaign dwfrun-f9904baf 第 10 轮）轮次汇总（汇总员-R15，2026-10-11，0 求解）：复算确认收编＋两分歧返工（dae9596＋D65）闭合终态亲验＋轮次终判独立复核——closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B6 53＋B1 88 定理双线落地）

Round 15（campaign dwfrun-f9904baf 第 10 轮，2026-10-11）汇总终版
（GAP-REPORT 本轮节 ⑤；decisions D66）。开工 HEAD=dae9596 净树 0 行
亲验，复算员结果与返工员提交（dae9596＋D65 三裁决，零代码改动）已
落链——复算两分歧于本会话开工前闭合，本节收编其终态。本会话亲跑：
endgame.json 直读（closed=False/blocking=[L0,L3]/绿 L1/L2/L5/L6/L7）
＋sha256 亲算（86863a09…69f 不变）＋铁律 AR≤E\*+1e-6 精确（E\*−AR
逐位==margin）＋chain-only 干跑五字段零漂移（叙述面漂移全归类、
未归类 0）＋全链 9 提交实序＋时间戳亲验（9d40343→…→dae9596）＋D65
落盘逐处亲验（/tmp/r15_indep_ldlt 五件日志＋脚本 sha256==46e266c2…
4324c＋endgame_chain.py:957-963 片型谓词在位）＋定理计数亲 grep
53〔45+8〕/88〔32+56〕＋两账本锚直读（seed 20261017/heavy_solves=0）
＋预算终账独立重算（四源＋R11 探针=360942.5s=721885/2、33.421/40、
口径 B 6.579<12 M11 不可触发维持）＋复算/收口在档 /tmp 日志抽查全
对上（r15audit_endgame_gate 1609.8s＋r15d_accept 256.1s＋
endgame_gate_full 1615.5s）。轮次终判：closed=false 三面一致
（直读＋干跑＋gate-③ 定量三组在档）、assembledRecord 维持零提升
（B6/B1 形式层证明不入 12 分区）、progress=true（新严格引理 B6＋B1
双线落地；新证书 0/纪录提升 0 如实）、closed 重试不排。下轮候选：
B5a 解析本体首件（先探 §2.4 六项 API）／B2–B4 待 B3 Hessian 自建／
thomson_nine 不承诺／RC2 a5 M9 待预算 ≥2.799／M11 待触发 ≥12。

## Round 15（campaign dwfrun-f9904baf 第 10 轮）收口（执行员-R15-r15d-round15-closure，2026-10-11，0 求解）：一致性收口——B6/B1 双件＋B5 预研收编＋endgame_gate campaign-10 增补＋r15d_closure_gate 六面门；closed=false 维持／assembledRecord 维持／progress=true（严格口径：新严格引理 B6＋B1 双线落地）

Round 15（campaign dwfrun-f9904baf 第 10 轮，2026-10-11）收口
（GAP-REPORT 本轮节 ④；decisions D64）。依赖 R15C（9d40343：B5 预研
＋D61/D62 收编）＋R15A（0cba187：B6 记录锚件 53 定理）＋R15B（4dc34e0：
B1 Gram 节点算术层 88 定理＋D63）三提交全落、树净 0 行亲验后执行——
收口全程不触并行在途件（D16-1）。本会话亲跑：chain-only 干跑
（/tmp/r15d_dry.json）五字段逐位零漂移＋全集漂移 22 叶机器化归类
（certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2，
未归类 0）＋endgame.json 直读（closed=False/blocking=[L0,L3]/绿
L1/L2/L5/L6/L7）＋sha256 亲算（86863a09…69f 不变）＋铁律 AR≤E\*+1e-6
精确（margin 0.0005405579025207914 逐位）＋预算终账（四账本冻结值
逐位相等、typed_ladder rungs==9、campaign 360942.5s=33.421/40、口径 B
6.579<12 M11 不可触发维持、r15 新产物 4 件零正 solve）＋endgame_gate
gate-④ campaign-10 增补式扩展（扩展前基线九锚 PASS→扩展前负对照
GateFail 如期检出→文档三件落笔→正向十锚 PASS；时序沿 D58 裁决 2）＋
新收口门 r15d_closure_gate.py（seed 20261017，C1 三子门复跑＋C2 干跑
归类＋C3 直读铁律 sha256＋C4 文档三件锚〔D61/D62/D63/D64〕＋C5 预算
＋C6 树净＋NC 双面负对照）＋嵌套 CWD 包装器。轮次终判：closed=false
三面一致（直读＋干跑＋gate-③ 定量）、assembledRecord 维持零提升
（B6/B1 形式层证明不入 12 分区）、progress=true（新严格引理 B6＋B1
≥1 落地，D37 严格口径；新证书 0/纪录提升 0 如实）、closed 重试不排
（D61 裁决 5）。下轮候选：B5a 解析本体首件（预研 §5 切分，开工前先探
§2.4 六项 API）／B2–B4 待 B3 Hessian 自建／thomson_nine 不承诺／RC2
a5 M9 待预算 ≥2.799／M11 待触发 ≥12。

## Round 14（campaign dwfrun-f9904baf 第 9 轮）轮次汇总（汇总员-R14，2026-10-11，0 求解）：复算五组确认收编＋两分歧返工闭合终态亲验＋轮次终判第四组独立复核——closed=false 维持／assembledRecord 维持／progress=true（严格口径：B5 新严格引理 50 定理，表 B 首件）

Round 14（campaign dwfrun-f9904baf 第 9 轮，2026-10-11）汇总终版
（GAP-REPORT 本轮节 ④；decisions D60）。开工 HEAD=77ab45b 净树 0 行
亲验，返工员两提交（acf5394＋77ab45b）已在链。本会话亲跑：endgame.json
直读（closed=False/blocking=[L0,L3]/绿 L1/L2/L5/L6/L7）＋sha256 亲算
（86863a09…69f 不变）＋铁律 AR≤E\*+1e-6 精确＋chain-only 干跑第四组
零漂移＋R14C 两分歧落盘逐处亲验（残留扫描＋ledger 7 件重锚==现盘）＋
全链 8 提交实序亲验＋在档 /tmp 日志抽查全对上＋docs_check/c4_docs
importlib 直跑保锚 PASS。轮次终判：closed=false 三面一致、
assembledRecord 维持零提升（B5 系形式层证明不入 12 分区）、
progress=true（新严格引理 50 定理落地；新证书 0/纪录提升 0 如实）、
预算 Σsolve_s==0／campaign 33.421/40／口径 B 余 6.579<12（M11 不可
触发维持）。下轮候选：表 B 余件（B1–B4、B6 或 B5 解析本体预研）／
RC2 a5 M9 待预算 ≥2.799／M11 待触发 ≥12。

## Round 14（campaign dwfrun-f9904baf 第 9 轮）R14C 勘正（返工员-R14，2026-10-11，0 求解）：注释级两计数错勘正——ℚ 字面量 22→23（898a36d 同类）＋抽查盒宽 840→838,863（千进位脱落）；零数值面改动

R14C（campaign dwfrun-f9904baf 第 9 轮，2026-10-11）勘正
（GAP-REPORT Round 14 节 ③；decisions D59）。复核复算两分歧
均亲验成立后勘正 8 处文字；发射器重跑 TableB5Data.lean 字节一致
＋json 仅 4 行非数值变化；被验面无变化。

## Round 14（campaign dwfrun-f9904baf 第 9 轮）收口（执行员-R14-r14b-round14-closure，2026-10-11，0 求解）：一致性收口——B5 常数件收编＋endgame_gate campaign-9 增补＋r14b_closure_gate 六面门；closed=false 维持／assembledRecord 维持／progress=true（严格口径：B5 新严格引理 50 定理落地，表 B 首件）

Round 14（campaign dwfrun-f9904baf 第 9 轮，2026-10-11）收口
（GAP-REPORT 本轮节 ②；decisions D58）。依赖 R14A（4be81bf＋c8765c9＋
898a36d：B5 Procrustes 常数件 Lean 化 50 定理〔Data 33＋Main 17〕全落
盘提交、树净 0 行亲验）后执行——收口全程不触并行在途件（D16-1）。

- **R14A 收编**：数据件 r14_b5_data.py（Fraction 独立第二实现：Newton
  sqrt 包＋ℚ[ρ,√3] 符号引擎，只读 l4.json＋local_min.json）→
  TableB5Data.lean（24 def＋33 定理）＋TableB5.lean（手写 17 定理零数值
  字面量）；三层 50 定理公理恰 ⊆{propext, Classical.choice, Quot.sound}
  零 sorryAx（①ttp_quadform 显式 ring 证书＋λ 夹逼两向＋S 区间容器／
  ②装配恒等式四件 636-bit norm_num 与 l4.json 逐位／③sqrt 界四件＋
  C_valid＋delta_max_valid〔div_le_div_iff₀ 绕行〕）；门 r14_b5_gate
  自跑 5 次＋三路由 CWD 全 exit 0（112–168s）＋提交后净树复跑
  148.0s＋勘正后 136.9s；d_P≤C·δ 本体不在件内如实。
- **endgame_gate gate-④ campaign-9 增补**：历史检查全保留（D29-5/
  D34-4/D38-5/D43-5/D49-3/D52-5 先例）；新增『Round 14（campaign
  dwfrun-f9904baf』regex＋PROGRESS 条目＋D56 锚三检查追加在全部历史
  检查后＋docstring ④ 段同步；扩展前基线 docs_check importlib 绝对
  路径直跑 PASS（八锚）→扩展后 Round 14 节未落笔时点负对照如期
  GateFail『④ GAP-REPORT.md 无…本轮节』（D48-2 教训，勿经会话根
  包装器）→落笔后正向 PASS 九锚；扩展后全门 nohup 后台＋轮询净树
  一跑 **PASS exit 0（1617.1s**，净树 HEAD=5e46ad7，/tmp/r14b_pre/
  endgame_gate_full.log：gate-① reverify 全量 1616.8s＋gate-④ 九锚
  全过＋gate-⑥ 树净；居 1493.8–1620.7s 历史带高位〔r13b_t1.lean
  遗留探针占核争用，R13D 同源先例〕——两段式回填入档，0 当量）。
- **r14b_closure_gate.py**（seed 20261016，CWD 无关）＋会话根/嵌套
  双包装器：C1 r14_b5_gate 复跑 exit 0＋账本锚（seed/heavySolves==0/
  theorem_count==50/公理恰三标准）＋C2 chain-only 干跑五字段逐位零
  漂移＋全集漂移 22 叶机器化归类（certReverify 17＋cvt 2＋L1 quant 1
  ＋engineV2 2，未归类 0）＋C3 直读＋铁律 AR≤E\*+1e-6 精确＋sha256==
  86863a09…零改动＋C4 文档三件锚（D56/D57/D58）＋C5 Σsolve_s==0 精确
  ＋campaign 360942.5s=33.421/40 账↔文档双核验＋口径 B 6.579<12＋R14
  新产物零正 solve 正则＋C6 树净＋NC1 篡 r14_b5_ledger heavy_solves
  0→1 拦＋NC2 篡 m10 total_solve_s +2000s 拦＋未篡 sanity。
- **轮次终判（与证据严格对齐）**：closed=false 三面一致（存档直读＋
  干跑零漂移＋gate-③ 定量）；assembledRecord 维持
  47517790735835014335570/1844674407417822803119＝25.759445973097478
  零提升（B5 系形式层证明非数值证书不入 12 分区）；progress=true
  （D37 裁决 1 严格口径：B5 新严格引理 50 定理 ≥1 落地即 true；新证书
  0/纪录提升 0 如实）；预算 Σsolve_s==0 精确（0.037 当量全额留储）、
  campaign 33.421/40、口径 B 余 6.579<12 ⇒ M11 不可触发维持；四账本
  零新行、typed_ladder rungs==9 不追加。
- **提交后验收复跑（两段式回填入档）**：r14b_closure_gate 验收命令
  campaign 根净树原样复跑 **PASS exit 0（109.8s**，零环境变量 G1 字面
  严格，/tmp/r14b_pre/r14b_accept.log：C1a 109.3s＋C2–C6＋NC 全过；
  预提交自跑 C1a 177.6s 与之并列同款口径）；endgame_gate 全门
  1617.1s（见上）。
- **全链提交**：85d3917（设计 D56）→4be81bf（R14A 主件）→c8765c9
  （R14A 两段式回填）→898a36d（R14A 勘正）→5e46ad7（R14B 收口：
  endgame_gate 增补＋r14b_closure_gate＋双包装器＋文档三件＋D58）→
  本回填提交（全门/验收墙钟入档）；全链零求解零账本数值改动。


## Round 13（campaign dwfrun-f9904baf 第 8 轮）轮次汇总（汇总员-R13，2026-10-11，0 求解）：复算六组确认收编＋三分歧返工闭合终态亲验＋轮次终判第四组独立复核——closed=false 维持／assembledRecord 维持／progress=true（严格口径：表 A 新严格引理四线落地，Stage B 承诺面收官）

Round 13（campaign dwfrun-f9904baf 第 8 轮，2026-10-10/11）汇总终版
（GAP-REPORT 本轮节『轮次汇总』；decisions D55）。前置核验：开工
HEAD=f3a48c8 净树 0 行亲验，返工员两提交（54fccc9＋f3a48c8）已在链。

- **交付面（四任务全落）**：R13A 表 A3/A4（6a895a4＋返工 18f586b，
  16 定理：84 分桶 typed 计数七定理＋a3_l1 归一化 norm_num＋Q 递推
  强归纳＋ycol_count 271）；R13B 表 A6（157172b＋4b11b68＋b7b4222，
  46 定理：8 块精确 LDLᵀ 重构/平方表示/p_cls 域非负/R2 折减恒等式，
  Gen＋8 块＋总成 10 文件）；R13C 表 A1（b60b6c5＋返工 7ac3111，
  55 定理：λ/s/h 装配恒等式＋84/729/36 计数折叠＋18 随机点抽查）；
  R13D 收口（f3c8ce3＋7e573fb＋2d9e921：r13d_closure_gate 六面门
  ＋endgame_gate gate-④ campaign-8 增补扩展＋文档三件）。公理全部
  ⊆{propext, Classical.choice, Quot.sound}，零 sorryAx。
- **复算收编（六组确认，转录标明出处）**：r13d 验收命令净树复跑
  PASS 861.3s（三子门 134.9/310.7/415.1s 全 exit 0）＋A6 LDLᵀ 第三
  实现 83 检查（Bareiss/Sylvester 独立路径）＋A1/A3/A4 第三实现 49
  检查（三 sum 折叠 diff==0＋A4 Q 递推逐项恒等）＋endgame 铁律预算
  Fraction 亲算 37 检查（AR==min(12 分区) 精确）＋账本抽查一致＋
  全程只读零写入。三分歧 D1/D2/D3 已由返工员闭合，本会话逐处亲验
  落盘：D1 链序实序（b60b6c5 23:34:08→18f586b 23:41:01，git
  rev-list＋时间戳 13 提交亲验）；D2『3-smooth ℚ』措辞在场
  tablea-lean.md:291＋r13_a1_data.py:15/:287＋TableA1Data.lean:14；
  D3 a6 账本 files 面门脚本锚==bb6eed25… 现版＋erratum 注记在档。
- **轮次终判（与证据严格对齐）**：closed=false 三面一致（存档直读
  ＋chain-only 干跑零漂移——本会话第四组亲跑 0.4s，组件 rigorous
  L1/L2/L5/L6/L7=True、L0/L3=False、L4 off-path 全等；＋endgame_gate
  gate-③ 定量 1620.7s PASS 在档）；assembledRecord 维持
  47517790735835014335570/1844674407417822803119＝25.759445973097478
  零提升（HP 兜底片 margin 0.0005405579025207914 不变，endgame.json
  sha256==86863a09…69f 亲算复核）；progress=true（D37 裁决 1 严格
  口径：新严格引理 4 线全落即 true——16＋46＋55 定理；新证书 0/
  纪录提升 0 如实）；预算 Σsolve_s==0 精确（0.037 当量全额留储）、
  campaign 360942.5s＝33.421/40、口径 B 余 6.579<12 ⇒ M11 不可触发
  维持；四账本零新行、typed_ladder rungs==9 不追加。
- **Stage B 承诺面收官**：M0（R11）＋M1（R12）＋表 A 六件（A5/A2′
  ＋A3/A4/A6/A1）全落——重构轮 3/3 完成；thomson_nine/
  thomson_nine_unique 维持不承诺（Stage A 闭合硬依赖，stageb-scope
  §2）。下轮候选维持：B5 Procrustes 常数件可独立先行（首选）／
  RC2 a5 M9 首测待预算 ≥2.799／M11 待触发 ≥12／L0 洞片无求解路径
  不重试。
- **全链 14 提交（汇总终版）**：c08e905→6a895a4→b60b6c5→18f586b→
  7ac3111→157172b→4b11b68→b7b4222→f3c8ce3→7e573fb→2d9e921→
  54fccc9→f3a48c8→本汇总提交（三文档件：GAP-REPORT 汇总节＋PROGRESS
  置顶＋D55）；全链零求解零账本数值改动。

## Round 13（campaign dwfrun-f9904baf 第 8 轮）复算返工勘误（返工员-R13，2026-10-11，0 求解）：D1 链序换位／D2 dyadic 措辞降格／D3 a6 账本孤儿锚——三勘误纯文档/锚面收口

复算员独立复算报三分歧（D1/D2/D3），返工员逐条亲验**全属实**并本提交修正
（详见 GAP-REPORT Round 13 节『复算返工勘误』条＋decisions D54）：

- **D1（GAP-REPORT 链序）**：终版全链列表误将 18f586b（R13A 首验返工，
  2026-10-10 23:41:01）列于 b60b6c5（R13C A1，23:34:08）之前——git
  rev-list --reverse＋提交时间戳逐位亲验实际相邻对次序为 b60b6c5→18f586b
  （初版 2d9e921 按任务分组口径串排所致）；已勘正并补勘误留痕，纯文档零
  数值影响。
- **D2（『dyadic』措辞）**：λ_AAA/λ_AAB/λ_ABC 各 449 系数中 44/1347 非
  dyadic（λ_AAB 10 个分母奇部 3、λ_ABC 33 个奇部 3＋1 个奇部 27——
  Fraction 分母奇部亲算；源于 r9_s3_rederive.py share_lp 的 /6、/3 除法，
  r9_s3_rederive.py:448-450 亲读）；λ_AAA/s/h_AA/h_AB/e 全 dyadic。数值
  自身无恙（恒等式 diff==0、18 抽查、e/h 对账经复算员独立复核）。五处
  措辞降格为『3-smooth ℚ（分母 2^a·3^b）』：GAP-REPORT ③、notes/
  tablea-lean.md §9、r13_a1_data.py docstring（中文两处＋英文模板）、
  TableA1Data.lean 头注（模板与成品逐字同步）；b60b6c5 提交信息同措辞系
  不可变历史，以勘误留痕替代改写。
- **D3（a6 账本孤儿锚）**：r13_a6_ledger.json files 面为其门脚本记锚
  c2d738e0…——逐提交 git show＋shasum 穷尽亲测该值从未对应任何提交版
  （全历史仅 c66940b6@157172b 与 bb6eed25@4b11b68+ 两版），系生成时工作
  树中间态未入档；账本 files 面三锚（门/wrapper/tablea-lean）统一重锚至
  勘误时点现版＋files_anchor_erratum 注记（原值存证）；无任何验收门依赖
  files 面（a6 门 G0 只查在场、G1 冻结锚仅 M9 证书＋r9 json 且盘上亲验
  一致）。a1 账本 files 面三件因 D2 措辞修改同步重锚＋同款注记。
- **重跑面**：r13_a1_data.py /tmp 沙箱复放 exit 0（TableA1Data.lean/
  TableA1.lean 字节一致、json 除 timestamp/路径/git 版本三环境键外逐位
  一致）；r13_a1_gate 全门自跑 **PASS exit 0（434.8s**，G2 Data 164.8s
  ＋Main 43.5s，G3 55 定理恰三标准，NC1–3 全检出）；endgame_gate
  docs_check 直跑 PASS（八锚全过）＋r13d C4 文档三件锚直跑 PASS；提交后
  （54fccc9）r13d_closure_gate 验收命令净树原样复跑 **PASS exit 0
  （913.9s**，campaign 根零环境变量：C1 三子门 a3a4 144.3s＋a6 322.9s＋
  a1 446.0s 全过〔变更面 a1 门净树无放行层〕＋C2–C6＋NC 全过，与
  2d9e921 时点 993.8s 同带内）。
- **零改动面**：endgame.json sha256 不变；四账本数值/定理/门检查面不变；
  全部 Lean 定理语句与证明不动（仅 TableA1Data.lean 头注 /-! … -/ 注释
  块）；0 求解（heavySolves=0）。


## Round 13 收口（执行员-R13-r13d-round13-closure，campaign dwfrun-f9904baf 第 8 轮，2026-10-10，0 求解）：重构轮 3/3 一致性收口——closed=false 维持（三面一致，blocker L0/L3）／assembledRecord 维持／progress=true（严格口径：表 A 新严格引理四线落地，Stage B 承诺面收官）

Round 13（campaign dwfrun-f9904baf 第 8 轮，2026-10-10）收口
（GAP-REPORT 本轮节 ④）：依赖 R13A（6a895a4＋首验返工 18f586b——表
A3/A4 两件 Lean 化，16 定理公理恰三标准、r13_a3a4_gate 三路由
27.9/26.9/27.9s exit 0）/R13B（157172b——A6 Lukács 平方表示件：8 块
精确 LDLᵀ 全主元>0＋σ 平方表示＋p_cls 域非负＋R2 折减恒等式对账
r9 R2_exact 逐位，46 定理公理恰三，四路由自跑 383.3/450.2/384.1/
348.4s exit 0）/R13C（b60b6c5＋7ac3111——A1 三点装配恒等式：对称块
构型精确实例＋449 项 λ/271 项 s 表＋18 随机点抽查堵立方点盲区，
55 定理公理 ⊆三标准，自跑 281.9s 独占 exit 0）全部落盘提交后执行
（本会话轮询 git log 亲见五提交；收口全程不触并行在途件——D16-1）。
本收口会话六件：**① chain-only 干跑**
`python3 numerics/bounds/endgame_chain.py --out /tmp/r13d_pre/r13d_dry.json`
（0.3s，零 --reverify-certs）五字段 14 检查点与存档逐位零漂移
（closed=false/blocking=[L0,L3]/assembledRecord=
47517790735835014335570/1844674407417822803119=25.759445973097478/
spliceMap 维持 v2/组件 L1·L2·L5·L6·L7 绿＋L0·L3·L4 红），全集漂移
22 叶逐叶机器化归类全叙述性预期（certReverify 17＋
code_version/timestamp 2＋L1 quant 佐证串 1＋engineV2 账本探测 2，
未归类叶 0）——本轮零账本数值变更（表 A 四件系形式层证明非数值
证书不入 12 分区〔R11C/R12 先例〕、四账本零新行、typed_ladder
rungs==9 不追加）⇒ 不跑 --reverify-certs 全量刷新（gate-① 随 ③
全门一跑执行）；**② endgame.json 直读＋铁律 Fraction 亲算**：铁律
AR≤E\*+1e-6 精确成立（E\* 十进制精确口径 Fraction("25.759986531")，
D28 裁决 3；E\*−AR 精确重算==
997153328507562120104790189/1844674407417822803119000000000=
0.0005405579025207914 与账本 margin 逐位）、AR==min(12 分区) 精确
重算＋分区无缝盖满＋cited 12 份在盘一致、sha256==
86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f
零改动；**③ endgame_gate.py gate-④ 增补式扩展**（campaign-8 节
regex『Round 13（campaign dwfrun-f9904baf』＋D52 锚三检查，历史
Round 8–12 检查全保留；docstring 同步；**扩展前负对照亲验**——
Round 13 节未落笔时点 docs_check 子进程直跑如期 GateFail
『④ GAP-REPORT.md 无…本轮节』检出，绝对路径 importlib 加载真门
模块直跑，D48 裁决 2 教训执行；节落笔后正向 PASS）＋扩展后全门
nohup 后台净树一跑 PASS exit 0（1620.7s，净树 HEAD=f3c8ce3，日志
/tmp/r13d_pre/endgame_gate_full.log；八锚全过含 campaign-8＋D52；墙钟
高于历史带归因 r13b 遗留探针进程占核争用如实记）；
**④ 预算终账**：本轮 Σsolve_s==0 精确（全任务 heavySolves=0——
R13A/B/C 账本零正 solve 字段＋R13D 收口零求解；0.037 当量全额留储
D52 裁决 5）；四账本与 R8 终账冻结值逐位相等；campaign 累计
360942.5s=721885/21600=33.421/40 与 R11/R12 终账逐位不变账↔文档
双核验；口径 B 余 6.579<12 ⇒ M11 触发器不可触发维持；**⑤ 新收口
验收门** numerics/bounds/r13d_closure_gate.py（seed 20261015，CWD
无关）＋campaign 根嵌套包装器（runpy 式 r11c/r12c 先例）：C1 三子门
复跑（r13_a3a4/r13_a6/r13_a1 逐个子进程）＋三门账本在档锚（公理
恰三、heavySolves==0、定理数 16/46+8 重构件/55、零 sorry 由子门
sorryAx 拦截面承担）＋C2–C6＋门自身负对照（/tmp 篡 r13 账本双面
必失配＋未篡副本 sanity）；**⑥ 树净终验**＋decisions D52 结果回填
（R13D 节）。轮次终态：closed=false（三面一致：存档直读＋chain-only
干跑＋endgame_gate gate-③〔扩展后全门净树终验，两段式回填〕）、
assembledRecord 维持零提升（HP 兜底片 margin 5.4056e-4 不变）、
progress=true（D37 裁决 1 严格口径：表 A 新严格引理 4 线≥1 落地；
新证书 0 如实、纪录提升 0 如实）、本轮 0 当量、campaign 33.421/40；
closed 重试不排（D52 裁决 5：L0/L3 不动＋M11 不可触发）。

## Round 12 汇总收口（汇总员-R12，campaign dwfrun-41fdc169 第 7 轮，2026-10-10，零求解）：独立复算审计收编（零分歧零返工）＋轮次终判补记——closed=false（三面一致，blocker L0/L3）／assembledRecord 维持／progress=true（严格口径维持，经独立复核巩固）

Round 12（campaign dwfrun-41fdc169 第 7 轮，2026-10-10）汇总员
（GAP-REPORT 本轮节 ④）：**复算员独立复核全程只读零仓库写入**
（脚本/日志在其 /tmp/audit_r12/，复核时点净树 HEAD=579c72a）——
五验收脚本全量重跑全 exit 0：r12_m1_gate 直跑 49.3s（G1 冻结件
diff 空＋references 树哈希 4237b5e5…48 文件、G3 恰 4 挑战
sorry@[158,166,172,179]＋解件/M1Data 0、G4 公理恰三、G5
compared=34 非 DEFERRED、G7 stdlib-only 全过、NC×3 有牙）＋
r12_tablea_gate 17.8s（G5 A5 四分数 json 重读重算＋A2′ 平方化
判据 m=0..8、NC 双篡检出）＋r12c_closure_gate 66.7s（C1–C6＋门
负对照双面）＋**endgame_gate 扩展后全门后台＋轮询 PASS（1503.8s，
门自报 exit 0——nohup 未捕获 $? 与 R12D 同口径；gate-① reverify
全量 1503.6s；与 R12D 1498.7s 同带内）**＋check.sh 全链 23.3s
（恰 4 挑战 sorry、M0/M1 公理均恰三标准、M1 命题打印
189/8≤coulombEnergy）；**自写独立第二实现 indep_verify.py（纯
stdlib 零仓库 import，自写矩阵/Legendre/球面矩，78/78 全过）**：
f/p/Möbius 逐系数==m1_lean_data.json 逐位＋SOS 恒等式精确＋独立
LDLᵀ 同一 (L,D) 全主元>0（minD0=1.0758e-06/minD1=1.0676e-06）＋
逐 k∈{1,2,3,7} dim/Gram/Rinv/S/LDLᵀ/球面恒等式/理想证书独立
重证＋装配 B==bound_exact==25.728237201 逐位＋189/8<B≤E\*+1e-6
精确＋A5 四分数==(1+R2max)·(E\*−certified)==ε_forcing＋endgame.json
端到端（铁律精确、E\*−AR==margin 逐位、AR==min(12 分区)、12 片
无缝盖满、cited 12 在盘、sha256==86863a09…69f 零改动、chain-only
干跑 14 检查点零漂移复现）＋预算五源重核 Σ==360942.5==721885/2
精确==33.421/40、口径 B 余 6.579<12＋汇总↔原始抽查全对上
（D50-4 诚实项亲验：SKIP 系硬编码 presence-only 打印集、M1 实际
计入 compared=34 bad_type 空；decisions D49:3134/D50:3220 锚在档）。
**discrepancies=[]——零分歧零返工**（较 R9/R10/R11 各轮 2–3 条
返工备注；其未复跑项〔SDP 初值步需仓库 venv/endgame_gate $? 捕获
口径/网格采样非区间算术〕按其诚实声明原样收编）。**汇总员亲跑**
（净树 579c72a）：r12c_closure_gate 全门 campaign 根验收命令原样
**PASS exit 0（65.3s，/tmp/r12_sum/r12c_closure_baseline.log——
净树全门第四跑）**＋endgame.json 直读五字段＋铁律 Fraction 亲算
（AR=47517790735835014335570/1844674407417822803119、E\*−AR 精确
==margin 逐位）＋chain-only 干跑 exit 0（第三组独立）＋
endgame_gate docs_check 绝对路径 importlib 直跑（本节追加前基线
PASS＋追加后复跑 PASS——campaign-7＋D49 锚 ✓；全门不三跑：R12D
1498.7s＋复算员 1503.8s ≥2 组独立在档，D34 裁决 4 先例）。轮次
终判补记：closed=false 三面一致维持复核面增厚（直读＋干跑各三组、
gate-③ 两组）；assembledRecord 维持零提升（HP 兜底片全局瓶颈
margin 5.4056e-4 不变）；progress=true 经独立复核巩固（新严格
引理 2：M1＋表 A5/A2′；新证书 0/纪录提升 0 如实）；本轮 0 当量、
campaign 33.421/40。汇总裁决 D51 入档（零分歧收编口径/验证面
切分含 append-only 保锚/提交切分）。全链（终版）：0006d3e→
b4646f6→66c6aa7→cbe1844→5237fe5→23ade71→579c72a→本汇总收口
提交；本提交只 add 文档三件；零求解零 SDP 零证书零账本数值改动。

## Round 12 收口（执行员-R12-r12c-round12-closure，campaign dwfrun-41fdc169 第 7 轮，2026-10-10，0 求解）：重构轮 2/3 一致性收口——closed=false 维持（三面一致，blocker L0/L3）／assembledRecord 维持／progress=true（严格口径：M1＋表 A 双线落地）

Round 12（campaign dwfrun-41fdc169 第 7 轮，2026-10-10）收口
（GAP-REPORT 本轮节 ③）：依赖 R12A（b4646f6——thomson_nine_M1
Lean 内核真证明＝冻结挑战四定理第二件，189/8≤coulombEnergy，
公理恰三标准、check.sh 全链 PASS 19.3s、r12_m1_gate 三路由
45.8/46.2/46.0s exit 0；数据件 Lukács SOS 设计变更 D50-1——
p ℚ-不可约预设因子分解排除，半直线 SOS 精确 Fraction LDLᵀ 全
主元>0）/R12B（66c6aa7＋cbe1844＋5237fe5——表 A 首两件 A5/A2′
Lean 化落地，TableA.lean 三定理公理恰标准三、单文件 elaboration
防撞）全部落盘提交后执行。本收口会话六件：**① chain-only 干跑**
`python3 numerics/bounds/endgame_chain.py --out /tmp/r12c_dry.json`
（0.3s，零 --reverify-certs）五字段 14 检查点与存档逐位零漂移
（closed=false/blocking=[L0,L3]/assembledRecord
47517790735835014335570/1844674407417822803119=
25.759445973097478/spliceMap 维持 v2/组件 L1·L2·L5·L6·L7 绿
＋L0·L3·L4 红），全集漂移 22 叶逐叶机器化归类全叙述性预期
（certReverify 17＋code_version/timestamp 2＋L1 quant 佐证串 1
＋engineV2 账本探测 2，未归类叶 0）——本轮零账本数值变更
（m1_lean_data 25.728<AR 不入 12 分区〔R11C 先例〕、四账本零新行、
typed_ladder rungs==9 不追加）⇒ 不跑 --reverify-certs 全量刷新
（gate-① 随 ③ 全门一跑执行）；**② endgame.json 直读＋铁律
Fraction 亲算**：铁律 AR≤E\*+1e-6 精确成立（E\* 十进制精确口径
25759986531/10⁹，D28 裁决 3；E\*−AR 精确重算
997153328507562120104790189/1844674407417822803119000000000＝
0.0005405579025207914 与账本 margin 于存档 double 精度逐位一致）、
AR==min(12 分区) Fraction 精确、cited 12 份在盘、sha256==
86863a09…69f 与 R10/R11 基线相等零改动；**③ endgame_gate
gate-④ 增补式扩展**（campaign-7 节 regex＋D49 锚，历史检查全保留
＋docstring 同步；扩展前负对照亲验——绝对路径 importlib 加载真门
模块 docs_check 子进程直跑，Round 12 节未落笔时点如期 GateFail
『④ GAP-REPORT.md 无…本轮节』检出，D48 裁决 2 教训执行；扩展后
全门 nohup 后台＋轮询净树一跑 **PASS exit 0（1498.7s，净树
HEAD=23ade71，gate-① reverify 全量 1498.5s、七锚含 campaign-7＋
D49 ✓＋树净 ✓，日志 /tmp/r12c_draft/endgame_gate_full.log；退出码
证据＝门终止行自报，nohup 外壳未单独捕获 $? 如实记——R11D 同
口径；沿 2bd20c3→c920184 先例两段式回填）**；
**④ 预算终账**：本轮 Σsolve_s==0 精确（全任务 heavySolves=0；
四账本与 R8 终账冻结值逐位相等、typed_ladder rungs==9、R11 探针
冻结 2621/5s 复读；campaign 累计 360942.5s＝721885/21600＝
33.421/40 与 GAP-REPORT 字面双核验、与 R11 终账逐位不变；口径 B
余 6.579<12 ⇒ M11 不可触发维持；R12 新产物零正 solve 字段正则
核验）；**⑤ r12c_closure_gate.py**（seed 20261014，CWD 无关；
C1–C6＋门自身负对照 /tmp 篡 r12 账本双面必失配〔篡 m1 账本
sorry_counts.solution 0→1 ⇒ C1 锚拦；篡四账本之一
total_solve_s +2000s ⇒ C5 冻结值拦；未篡副本 sanity〕；campaign
根 CWD 包装器齐备——净树自跑两路由 PASS exit 0〔仓内 63.8s＋
campaign 根验收命令原样 63.9s，日志 /tmp/r12c_gate_repo.log／
/tmp/r12c_gate_campaign.log〕）；**⑥ 树净终验**。轮次终判（与证据严格对齐，
不硬凑）：closed=false 三面一致（存档直读＋干跑零漂移＋gate-③
定量）；assembledRecord 维持零提升（HP 兜底片全局瓶颈 margin
5.4056e-4 不变）；progress=true（新严格引理 2：M1＝冻结挑战
第二件真证明＋表 A A5/A2′；新证书 0 如实、纪录提升 0 如实）；
本轮 0 当量、campaign 33.421/40。全链：0006d3e→b4646f6→
66c6aa7→cbe1844→5237fe5→本收口提交（门＋扩展＋文档三件）→
〔两段式回填提交：全门墙钟落账〕。四账本＋endgame.json 全程零
数值改动（sha256 不变）。

## Round 11 汇总收口（汇总员-R11，2026-10-10，零求解）：复算审计收编＋D47 返工处置核实＋轮次终判——closed=false（三面一致，blocker L0/L3）／assembledRecord 维持／progress=true（严格口径维持，经独立复核巩固）

Round 11（campaign dwfrun-41fdc169 第 6 轮，2026-10-10）汇总员
（GAP-REPORT 本轮节 ⑤）：**复算员独立复核全程只读零仓库写入**
（脚本/日志在其 /tmp/r11_audit/）——四验收命令全量重跑全 exit 0
（r11_warmstart_gate／r11_m1light_gate／r11_m0_gate 三门 G＋NC
全过；r11c_closure_gate 全门 103.7s）＋**endgame_gate 扩展后全门
后台重跑 PASS exit 0（1495.6s，第 11 墙钟数据点带内；gate-①
reverify 全量）**＋亲读存档日志尾行 1521.0s 与 R11D 宣称逐字一致；
自写独立第二实现双件（纯 stdlib 零仓库 import）：①LP 轻证书全链
Fraction 重推导（Legendre 自算、B==bound_exact 逐位==25.728237201、
131073 格点 minorant、12×12 Gram LDLᵀ 正定、η==M_sup+2⁻⁴⁶）＋
②载体 typed m090_M6 证书 38 PSD 块全正定＋certified 四方逐串一致
——R11A/B/C 交付面零翻案；汇总↔原始抽查全对上（预算 2621/5、
campaign 721885/21600=33.421、AR==min(12 分区)、E\*−AR 精确、
四账本零 r11 行）。**两条 discrepancies 经返工 D47（commit
a4e3aaf）逐条核实均成立**——D44 裁决 1 下标错标 c₈→c₇（计数 4
正确、证书数值无误）＋D46 标题 0.0486→0.0485（1 ulp；账本精确
分数无误）；in-place 勘误五处（复算列二＋自查补三）零数值工件
改动，本汇总会话在盘亲验（decisions.md:3047-3089）。**汇总员亲跑
（净树 HEAD=a4e3aaf）**：r11c_closure_gate campaign 根验收命令
原样全门 PASS exit 0（112.6s，C1–C6 含树净；返工提交后全门首跑）
＋endgame.json 直读五字段＋铁律 AR≤E\*+1e-6 Fraction 精确＋
E\*−AR==margin 逐位＋sha256==86863a09…69f＋chain-only 干跑
exit 0（第三组独立）＋endgame_gate docs_check 子进程直跑（⑤ 追加
前后各一 PASS，全锚含 campaign-6＋D43 ✓；全门不三跑——R11D
1521.0s＋复算员 1495.6s 两组独立在档）。**轮次终判（与证据严格
对齐）**：closed=false 三面一致（直读＋干跑各三组、gate-③ 两组）
维持；assembledRecord 维持零提升；**progress=true 严格口径维持
（新严格引理 1〔M0 冻结挑战首件真证明〕＋新证书 1〔lp_m1_light〕
——复算双件零翻案、返工零数值修复，判定经独立复核巩固）**；
本轮 524.2s=2621/54000≈0.0485/0.2 当量（四位精确口径，D47 勘误
后；三位 0.049 亦正确）、campaign 360942.5s=33.421/40（精确
721885/21600）、口径 B 余 6.579<12 ⇒ M11 触发器不可触发维持；
四账本＋endgame.json 全程零数值改动。执行面教训留痕（D48 裁决
2）：会话根 numerics/bounds/endgame_gate.py 系 runpy __main__
委托包装器，import 即触发全门 reverify——docs_check 直跑须于
仓库根 import 或绝对路径加载真门模块（本会话两次误触发均即时
亲停、无残留、零仓库写入）。全链：
1c0beb6→4ed4d5c→682fe2a→15428f1→d1b99c3→09b4399→a4e3aaf→
本汇总收口提交（GAP-REPORT ⑤＋PROGRESS 置顶＋decisions D48）。
下轮候选维持 ④ 节末四条（Stage B 结构定理层表 A 六件＋M1 Lean
重放／RC2 扩容首测 a5 M9 整精度注入／M11 重开按 R9C ④／L0 洞片
不重试）。

## Round 11 收口（执行员-R11-r11d-closure，2026-10-10）：重构轮换轴兑现——M0 首证＋warm-start 判活＋M1 轻证书；closed=false（三面一致，blocker L0/L3）／assembledRecord 维持／progress=true（严格口径，终结两轮平台期）

Round 11（campaign dwfrun-41fdc169 第 6 轮，2026-10-10）收口
（GAP-REPORT 本轮节 ④）：任务结构（D43，commit 1c0beb6）＝重构
指令 1/3 主攻点换轴——Stage B Lean 形式层开工（新证据推翻 R10B
环境前提）∥RC2 C1 warm-start 第 0 项∥M1 轻证书→R11D 收口。
**R11A（682fe2a）**：thomson_nine_M0 Lean 内核真证明落盘
（Solution.lean 199 行＝挑战件 26–149 逐字节复述＋三角不等式
对对界证明；CheckAxioms 恰三标准公理；check.sh 全链 PASS
39.1s；r11_m0_gate G1–G6＋NC1/NC2/NC3 exit 0 40.6s）。
**R11B（15428f1）**：RC2 C1 第 0 项判活 **channel_alive**——
.ini 格式源码级解码（68359 token 逐位回读验证）；载体 m090_M6
冷重解 518.3s/76 iter（确定性口径）vs 自暖启 0.3s/**0 iter**/
pdOPT；certify(k=48) certified=144977193375331596/5629499535314119
与存档证书逐位相等＋verify-cert 双 exit 0；传质须整精度
（2⁻²⁴ 两变体皆死）；r11_warmstart_gate G1–G6＋NC1/NC2 exit 0；
Σsolve_s=2621/5=524.2s≤2160s。**R11C（4ed4d5c）**：
lp_m1_light.json（deg 8/ngrid 8000，LP minorant 认证下界
25.728237201≫189/8 且 ≤E\*+1e-6，四检查全 True，9 系数供 Lean
重放；跨会话逐位确定性实证）；r11_m1light_gate G1–G5＋NC×3
exit 0 64.3s。**R11D 收口（本节）**：chain-only 干跑（0.3s）五
字段 14 检查点逐位零漂移＋全集漂移 22 叶全叙述性预期（未归类
0）；endgame.json 直读＋铁律 AR≤E\*+1e-6 精确＋margin 逐位＋
AR==min(12 分区)＋cited 12 份一致＋sha256==86863a09…69f 零改动；
endgame_gate gate-④ 增补（campaign-6 节 regex＋D43 锚，历史全
保留；扩展前负对照 docs_check GateFail 亲验）；新收口门
r11c_closure_gate.py（seed 20261013）C1 三子门＋C2 干跑＋C3 直读
＋C4 文档锚＋C5 预算双核验＋C6 树净＋门自身负对照（/tmp 篡 r11
账本双面必失配）＋campaign 根包装器；扩展后全门 nohup 后台一跑
（净树，PASS exit 0／1521.0s——gate-① reverify 全量 1520.9s、
六锚含 campaign-6＋D43 ✓、树净 ✓、第 10 墙钟数据点带内，已两段
式回填 GAP-REPORT ③）。**轮次终判（与证据严格
对齐）**：closed=false 三面一致；assembledRecord 维持零提升；
**progress=true（D37 裁决 1 严格口径：新严格引理 1〔M0 冻结
挑战首件真证明〕＋新证书 1〔lp_m1_light〕——任一落地即 true，
终结 R9/R10 平台期）**；本轮 524.2s＝2621/54000≈0.049/0.2 当量
（低于计划 0.163）、campaign 360942.5s＝33.421/40（精确
721885/21600）、口径 B 余 6.579<12 ⇒ M11 触发器不可触发维持；
四账本＋endgame.json 全程零数值改动。下轮候选：Stage B 结构
定理层表 A 六件＋M1 Lean 重放／RC2 扩容首测 a5 M9 整精度注入
（channel_alive）／M11 重开按 R9C ④ 动作序。

## Round 10 汇总收口（汇总员-R10，2026-10-10，零求解）：复算审计收编＋D41 返工处置核实＋轮次终判——closed=false（三面一致，blocker L0/L3）／assembledRecord 维持／progress=false（严格口径）

Round 10（campaign dwfrun-41fdc169 第 5 轮，2026-10-10）汇总员
（GAP-REPORT 本轮节 ⑤）：**复算员独立复核全程只读零仓库写入**
（脚本/日志在其 /tmp/r10_audit/）——四验收命令全量重跑全 exit 0
（r10_pifix_gate 验收命令原样路由 16 检 0 败含 G5 电池三门／
r10_stageb_gate／r10_rc2_gate／r10c_closure_gate 净树 C1–C6 72.5s）
＋endgame_gate 扩展后全门后台重跑 PASS exit 0（gate-① reverify
全量；墙钟第 9 数据点带内——字面值按 D41 裁决 1 留痕
decisions.md 不入正文）；自写独立第二实现（纯 stdlib 零仓库
import）对 slab sm1_m99o100 证书 42 块双算法（Fractions LDLᵀ＋
Bareiss-Sylvester）判正定＋从原始 dyadic 块重推导 certified=
1419245723139071/54975685305550 与 claimed_bound 逐位相等（Δ=0
精确）；AR/12 分区/margin/铁律 Fraction 全对上＋endgame.json
sha256 三处一致＋chain-only 干跑零漂移（22 叶口径逐位复现）＋
R10A 两探针件 raw 逐位 diff（pi_degree 5→17 唯一漂移、triple
判死维持、三 dip 修正 bound 与冻结件旧缺陷 ∏ν³≈−1.116e-11
实证）＋预算七源 360418.3s=33.372/40 全对上。**返工 D41（commit
8400d2f）三条备注全裁定『非账目差异、仓库无错』**：墙钟系单跑
测量不改账／cap 片 25.75984622533888<E* 系 TTP-covering 反向
要求 ≤（复算员过严假设，cert==partition bound 精确相等）／漂移
叶 22 系门口径 ONLY 子树折叠（r10c_closure_gate.py:272-276，
朴素展开 74/76 未归类亦 0）——零代码零数值修复；在盘亲验
（decisions.md:2685-2743 单节＋git show --stat 单件 +61 行）。
**汇总员亲跑（净树 HEAD=8400d2f）**：r10c_closure_gate campaign
根验收命令原样 PASS exit 0（68.5s，C1a/b/c=67.8s/0.1s/0.1s＋C2–C6
全过含 C6 树净，日志 /tmp/r10_sum_closure.log）＋endgame.json
直读五字段＋铁律 AR≤E*+1e-6 Fraction 精确＋E*−AR==margin 逐位＋
sha256==86863a09…69f＋chain-only 干跑 exit 0（第三组独立干跑
在档）＋endgame_gate docs_check 子进程直跑（本节追加前后各一
PASS——gate-④ 锚含 campaign-5＋D38 保护性复跑；全门不三跑：
≥2 组独立在档，D34 裁决 4/D41 裁决 5）。**轮次终判（与证据
严格对齐）**：closed=false 三面一致维持且复核面增厚（存档直读
＋chain-only 干跑各三组、gate-③ 定量两组）；assembledRecord
维持零提升；progress=false（D37 裁决 1 严格口径：新证书 0/
新引理 0/纪录提升 0）；本轮 0/0.2 当量、campaign 33.372/40 维持。
全链提交 5a6ab9c→34301ce→aab1e15→65c47c8→0087eab→5b45882→
1669a51→1ecbe11→8400d2f→本汇总提交（GAP-REPORT ⑤＋PROGRESS
置顶＋decisions D42）；零求解零 SDP 零证书零账本数值改动。

## R10D 终验补记（执行员-R10-R10D-round10-closure，2026-10-10，纯文档，沿 c920184 先例）：endgame_gate 扩展后全门净树一跑 PASS 落账

扩展后 endgame_gate 全门（gate-④ 含新增 campaign-5 Round 10 节＋
D38 锚）**净树后台＋轮询一跑 PASS——1495.9s**（净树 HEAD=1669a51；
命令 `python3 numerics/bounds/endgame_gate.py`；日志
/tmp/r10d_draft/endgame_gate_full.log；门终止行自报『[gate] PASS
（1495.9s）——exit 0』）：gate-① --reverify-certs 全量重跑 exit 0
（1495.8s：cap m0748_M9＋5 slab＋5 strips＋HP 重放＋l3/l6/l4_orbit
幂等门）＋gate-② 存档 vs 重跑逐位一致（R10A 修复件链上零影响实证）
＋gate-③ closed=false blocking=[L0,L3] 定量＋gate-④ 六锚全过（含
本轮新增节）＋gate-⑥ 树净 ✓——closed=false 三面一致闭环（存档直读
＋chain-only 干跑＋gate-③ 定量）。墙钟第 8 数据点（1493.8–1582.3s
带内）。本提交只 add GAP-REPORT/PROGRESS 两文件（终验补记两段式
回填）；零求解零账本数值改动。

## Round 10 收口（执行员-R10-R10D-round10-closure，2026-10-10，零求解）：零求解维护轮一致性收口——closed=false（三面一致）／assembledRecord 维持／progress=false（严格口径：R10A 系正确性债修复非新证书）

Round 10（campaign dwfrun-41fdc169 第 5 轮，2026-10-10）收口执行员
（GAP-REPORT 本轮节 ④）：**三件收编全部过门**——R10A pifix-build-pi
（commit 65c47c8，D40 六裁决）：hermite_minorant build_pi_polynomial
节点因子 [ν]→(t−ν)=[−ν,1] 修复（R9B ④ 发现）＋单元恒等自检（次数
17/18/首一/Π(ν_k)==0 精确/64 点对拍）＋两变体回归重算落新件
（372.8s/414.5s，冻结件零覆写）：contact 决定性字段（13 顶层＋4 证书
级＋7 区×5 字段）对冻结件逐位相等、唯一漂移 pi_degree 5→17、
verdict=alive 维持；triple 判死维持（ok=False/dead、pi_degree 0→18、
三 dip 真 Π 修正 bound=−22.334/−9.2445e-2/−3.8363e-5＋dense 格点
−6.7971240e-10 独立面）；门 16 检 0 败三路由 exit 0＋G5 电池三门
（30.3s/10.1s/27.9s）。R10B stageb-scope（commit 34301ce，D39 五
裁决）：Lean Stage B 范围件六节（四定理恰 4 sorry 亲验/LP bound_exact
>189/8 Fraction 亲验/27 证书 95820405B 实测/三层分工/表 A·B 依赖序/
环境 elan 缺失如实记）。R10C rc2-engine-survey（commit aab1e15）：
RC2 候选引擎类预研零实测设计件（C1 warm-start 首测第 0 项配置验证＋
迭代减半 4.2344 当量入口径 B 6.628 可及域精确 Fraction＋判死线
0.7826＞C4 调参＞C2 细分 11.86＞C3 对称；C5 不复活 D31 闭案）。
**R10D 一致性核验收口**：①chain-only 干跑五字段 14 检查点逐位零漂移
（closed=false/blocking=[L0,L3]/assembledRecord=
47517790735835014335570/1844674407417822803119=25.759445973097478/
spliceMap 维持 v2/组件 L1·L2·L5·L6·L7 绿＋L0·L3·L4 红；全集漂移
22 叶全叙述性预期且机器化归类未归类叶 0；不跑 --reverify-certs——
零新证书零账本数值变更，D34 裁决 4）②直读＋铁律 Fraction 亲算
（AR≤E*+1e-6 精确、margin 0.0005405579025207914 重算==账本、AR==min
(12 分区)、cited 12 在盘、sha256 相对 R10 基线 5a6ab9c 零改动）
③endgame_gate.py gate-④ 增补式扩展（Round 10 节 regex＋D38 锚，
历史检查全保留）＋扩展前负对照 GateFail 检出亲验＋扩展后全门后台
＋轮询净树一跑（**PASS exit 0／1495.9s**，gate-① reverify 全量
1495.8s；结果两段式回填落账 GAP-REPORT 本轮节 ③）④预算终账：本轮 Σsolve_s=0、
campaign 360418.3s=33.372/40 维持、两读法余量 0.2/6.628 均 <12 ⇒
M11 触发器不可触发、R10 新产物 4 件零正 solve 字段⑤新门
r10c_closure_gate.py（seed 20261012，C1–C6）＋campaign 根包装器；
预提交自跑 C1–C5 全过（70.3s）。**轮次终判（与证据严格对齐）**：
closed=false（绿 L1/L2/L5/L6/L7、blocker L0/L3）；assembledRecord
维持（零提升）；progress=false（严格口径 D37 裁决 1——新证书 0/
新引理 0/纪录提升 0；R10A 系既有证书正确性债修复非新证书）；本轮
0/0.2 当量。下轮候选：M11 重开条件触发时按 R9C ④ 动作序＋RC2 首测
按 R10C 排序（C1 第 0 项居首）；Stage B 排程按 R10B 范围件。本会话
零求解零 SDP 零证书零账本数值改动。

## Round 9 汇总收口（汇总员-R9，2026-10-10，零求解）：复算审计收编＋返工处置核实＋轮次终判——closed=false（blocker L0/L3）／assembledRecord 维持／progress=false（严格口径：两件独立复算面＋M11 预算门闭案系实质成果，不构成新证书/新引理/纪录提升）

Round 9（campaign dwfrun-41fdc169 第 4 轮，2026-10-10）汇总员
（GAP-REPORT 本轮节 ⑨）：**复算员独立复核全程只读零写入**——五
验收门独立重跑全 exit 0（r9_m11_gate 0.06s／r9_s3_gate 3.06s／
r9_v2iv_gate 8.58s／r9c_closure_gate 仓内 12.40s＋campaign 根
12.0s／chain-only 干跑 0.27s）＋endgame_gate 全门后台跑 PASS
exit 0（1538.7s，与 R9D 1497.2s 同量级）；铁律数字 Fraction 亲算
（AR≤E*+1e-6 精确成立、E*−AR 与账本 margin 逐位、AR==min(12 分区)
精确＋分区无缝盖满 [−1,1]、cited 12/12 在盘一致、endgame.json
sha256 零写入）；chain-only 干跑零漂移独立复核（15 检查点全同）；
R9C 预算账七加数重算 360418.3s=33.372/40（两读法 0.2／6.628 均
<12 ⇒ M11 触发器不可触发）；R9A r9_s3_rederive.json 9/9 字段对
证书 provenance 与 l2_rigorous 三方逐位＋ε_forcing 恒等式亲算
精确相等；R9B r9_v2iv.json 逐项对账全吻（③ 5341 叶/covered==2/
min gap 1.630295439898737e-16、④ strip 4.436957692814465e-14
双口径收紧比、⑤ c0_dense rel_diff=0.0 witness 级如实）；另补做
两道 /tmp 独立第二实现（Fractions LDLᵀ 38/38 块 PSD＋三负对照
90.8s；自写区间路径 φ−M′≥0 全覆盖 24827 叶零违例＋strip 上界
4.428462e-14）——与 R8 复算员/R9B 各自独立吻合。**两条分歧经
返工员（⑧/D36）处置后汇总员在盘核实闭环**：①soundness 留痕缺口
＝G6/NC4 机器化落地（12 检独立亲跑 exit 0：G6 max slack
−4.644e-15 零违例、NC4 234/300 检出）＋claim 双现场〔R9 返工注〕
在档＋账本确未回填（r9_v2iv.json 0 处『soundness』、最后触碰提交
仍＝dd23ca5）；②审计工具自留痕＝非仓库问题三路验证在档。**轮次
终判（与证据严格对齐）**：closed=false（endgame_chain 三面一致：
存档直读＋chain-only 零漂移＋endgame_gate gate-③ 定量；绿
L1/L2/L5/L6/L7、blocker L0/L3、L4 off-path）；assembledRecord
维持 47517790735835014335570/1844674407417822803119=
25.759445973097478（零提升）；progress=false（严格口径 D37 裁决
1——新 SDP 证书 0/新严格引理 0/纪录提升 0；R9A/R9B 独立复算面系
既有证书可信度分层提升非新引理）；本轮 0/0.2 当量、campaign
33.372/40 维持。**汇总员亲跑**：r9c_closure_gate campaign 根
PASS exit 0（13.4s，C1–C6 全过）＋r9_v2iv_gate 12 检 exit 0
（9.9s）＋endgame.json 终态直读；endgame_gate 不三跑（R9D＋
复算员 ≥2 组独立在档，D34 裁决 4 同纪律）。本会话零求解零 SDP
零证书零账本数值改动。

## R9 复核返工（返工员-R9，2026-10-10，零求解）：复算分歧两条逐条核实与处置——①soundness 留痕缺口机器化补检＋②审计工具自留痕如实记账

R9 返工（GAP-REPORT Round 9 节 ⑧／decisions D36）：**分歧①**（R9B ③
『soundness 抽查 300 随机叶 ≤+2.22e-16 零违例』宣称无落盘机器字段）——
复算员全部事实断言属实（r9_v2iv.json items.direct_interval 18 键无
soundness、扩展前门无该检查，claim 仅会话叙述＋decisions 文字留痕）；
实质经两实现独立复证成立（本返工 /tmp 复刻二分+mpmath dps=80 真值：
零违例 max slack −4.644e-15；复算员自写区间路径：零违例 max slack
0.0）——数值无分歧。处置（D36 裁决 1，两案取舍）：采门增补式扩展
G6（soundness 抽查机器化：复刻二分与 G1 新鲜产出计数逐位对账+300 叶
seed 20261010+单点精确 Fraction 真值参考，判据同向保守）＋NC4（检出器
+1e-12 偏置必现违例）；弃账本回填（事后回填＝伪造 provenance，违 D34
裁决 4 冻结先例）。扩展门 12 检（G1–G6+NC1–NC4）两路由亲跑 exit 0
（仓库根 9.9s＋campaign 根包装器 9.9s；G6 max slack −4.644e-15 零违例；
NC4 234/300 违例检出）。claim 双现场加〔R9 返工注〕。**分歧②**（复算员
/tmp 审计工具三条修正自述：LDLᵀ 负对照 2⁻⁴⁰ 扰动尺度不相称改三尺度、
朴素幂区间叶界二重接触节点发散改盒中心 Taylor 包络 24827 叶收敛、负
对照函数漏用传入 coeffs）——如实记账非仓库问题：git 净树＋log 零审计
写入；仓库 LDLᵀ＝纯精确有理无主元判定无尺度盲区（存档 F0 块 λ_min
~2⁻²⁹≈1.86e-9 直测：−2⁻⁴⁰ 仍 PD 系精确正确答案、−2⁻²⁸ 翻负、对称破
−2⁻²⁰ 翻负）；仓库叶界自始即 Taylor 设计；仓库 NC1 尺度相称（9.1e-13 ≫
1.63e-16）本轮亲验检出。零账本零证书零求解改动，closed=false 维持。

## Round 9 收口（执行员-R9-round9-closure，2026-10-10，零求解）：零求解收账轮三件收编＋一致性核验收口——closed=false／assembledRecord 维持／新证书 0 如实（实质成果＝两件独立复算面＋M11 预算门闭案）

Round 9（campaign dwfrun-41fdc169 第 4 轮，2026-10-10）收口执行员
（GAP-REPORT 本轮节 ④）：**三件收编全部过门**——R9A S₃ 商环装配自写
第二实现（commits 31ec9d2＋2fc8950）：R1×3/R2×2/defl/R2max/certified
对证书 provenance 与 l2_rigorous 三方**逐位相等**＋3 trial 恒等式==0
＋结构性自查 9 项（PSD 不在范围如实分层）；R9B v2 相位 0 区间算术
自写重验（commit dd23ca5）：七区域 Π≥0＋W==17/2⁴⁹＋直接区间路径
φ−M′≥0 全覆盖（5341 叶、最小认证间隙 1.630e-16≥0）＋strip 上界
4.436958e-14（容差内、<1e-12）五项全过；R9C M11 扩容决策件
（commit 7f49b40）：预算门两读法（0.2／6.628 当量）均 <12 ⇒ 触发器
不可触发、campaign 内不排任何 M11 求解。**R9D 一致性核验收口**：
①chain-only 干跑五字段 14 检查点逐位零漂移（closed=false／
blocking=[L0,L3]／assembledRecord=47517790735835014335570/
1844674407417822803119=25.759445973097478／spliceMap 维持 v2／组件
L1·L2·L5·L6·L7 绿＋L0·L3·L4 红；22 处叙述性漂移全为预期类目——
零 --reverify-certs 全量刷新，D34 裁决 4）；②endgame 直读一致＋铁律
AR≤E*+1e-6 精确成立（margin 0.0005405579025207914 精确重算逐位）＋
endgame.json sha256 零改动；③endgame_gate gate-④ 增补式扩展（Round 9
regex＋D34 锚，历史检查全保留）后全门后台＋轮询终验一次；④预算终账
本轮 Σsolve_s=0（四账本与 R8 终账冻结值逐位相等＝无新求解行）；
⑤三门复跑全 exit 0（0.07s/2.9s/8.3s）＋r9c_closure_gate.py
（C1–C6，seed 20261010）＋campaign 根包装器。**轮次终态**：L0＝洞
单片两引擎四档全阻（a5 M10 25.759951713654896 仍最优）campaign 内
终态受阻正式留档（重开条件 RC1 外部扩容 ≥12 当量/RC2 新引擎类）；
L3 永久开放（ε 1.403e-4≫ε_W 差 1.9152e8×）；绿 L1/L2/L5/L6/L7；
progress＝收账轮口径（账面纪录零变化如实；两件独立复算面补齐＝两份
被复算证书各有「构造代码之外」的第二实现验证）。下轮候选：hermite_
minorant build_pi_polynomial 修复件（R9B 发现）居首、外部扩容等待期
零求解维护件。本会话零求解零 SDP 零证书零账本数值改动。

## Round 8 汇总收口（汇总员-R8，2026-10-10，零求解）：复算收编＋D33 返工处置核实＋轮次终判——closed=false／assembledRecord 维持／progress=true（无新证书，严格量化成果两件）

Round 8（campaign dwfrun-41fdc169 第 3 轮，2026-10-09）汇总员收口
（GAP-REPORT 本轮节 ⑧）：**复算员独立复核收编**（只读零仓库写入，
产物 /tmp/r8audit/，转录）——五组门亲跑全过 exit 0（r8c3_l2m9
307.8s／r8c3_engine 30.0s／r8c3_closure 两路由 342.9s＋358.6s／
endgame_gate 两路由 1595.3s＋1496.9s；历史三门 r8_anchor 24/24＋
r8_l6 8/8＋r8_m9 9/10——G6 幂等失配复现且根因独立核实＝m9_campaign
rows[3] 冻结 not_run vs typed_ladder R7B M9 rung〔42305.7s〕后到改动，
重装配 13.408 当量逐位复现，append-only 不回写〔D32 裁决 5〕）；自写
零 import Fractions LDLᵀ 38/38 块严格正定（最小主元 9.077e-13）＋
certified/R2max/defl 经 provenance 残差逐位重算＋三负对照全检出
（S₃ 商环装配未自写重推——诚实分层）；ε 恒等式 (1+R2max)(E*−certified)
==ε 双口径逐位；assembledRecord 12 分区 min 三方逐位相等＋铁律
AR≤E*+1e-6 精确（富余 5.4e-4）；R8B 相位流/数字逐项（X9=+2.9348e-6、
阈比 18.06×、lift −1.2656e-4、W=3.0198e-14、strip gap 4.4284e-14＝
收紧 1.5717e4×、triple 判死）；预算四源核齐 360418.3s=33.372/40、
本轮 2.828/9.30、余 6.628<12；NC1 自建复演检出 exit 1。
**五项分歧 D33 处置在盘核实**（四项文档误已由 R8-R1 修正 92ef847、
门复跑回填 dd15795；本会话亲验）：①ε 分数串「602」补字——git grep
缺陷串全仓 0 命中；②洞片尝试链重写（两引擎四档、v2 高出 a5 M9
X9=+2.9348e-6）；③1.9e9×→1.9e8×（亲算 1.9152e8）；④−66.23%→
−66.22%（亲算 66.2195%）；⑤未复算四条——NC2 已由 R8-R1 补演检出、
墙钟第 6 数据点，S₃ 商环装配＋v2 区间算术两条独立重推仍留待后续
（如实）。**汇总员亲跑**（净树 HEAD=dd15795）：r8c3_engine_gate
exit 0（29.9s，G1–G7＋NC1–NC3）＋endgame.json 终态直读（closed=false／
blocking=[L0,L3]／assembledRecord 精确分数＋float 25.759445973097478／
margin 5.4056e-4／bottleneck HP 兜底／partition 12／cited 12／spliceMap
维持 v2 assembled_equal_R7=true／组件 rigorous L1/L2/L5/L6/L7=True）＋
Fraction 亲算三项；长门不重复消耗（已有 ≥2 组独立在档）。**轮次终判**：
closed=false、blocking=[L0（洞单片两引擎四档全阻，a5 M10
25.759951713654896〔E*−3.4817e-5〕仍最优——引擎改良方向定量闭案，
M11+ 扩容〔≥12 当量触发器〕唯一已识别路径、未排）,L3（永久开放
dead-at-(9,6)；ε 1.403e-4≫ε_W 差 1.9152e8×、L6 缺 11.2536×）]；
assembledRecord 维持（wouldBe=E*）；绿 L1/L2/L5/L6/L7（L4 off-path）；
progress=true（新证书 0、纪录不变如实——ε 口径严格更新 −66.22%＋
contact 区间算术证书〔Π≥0 全分支〕strip gap 上界收紧 1.5717e4×）。
下轮候选：M11 扩容决策件（预算门先行）居首；S₃ 商环装配/v2 区间
证书独立重推两件零求解复算件次之；cap M10 缓排维持（D27 裁决 3）。
本会话零求解零证书零账本数值改动，唯一仓库写入＝GAP-REPORT ⑧＋
本条目。

## Round 8（campaign dwfrun-41fdc169 第 3 轮，2026-10-09）R8C 收口：消费 R8A/R8B 产出——引擎 v2 未翻正分支落账，closed=false 维持（与证据对齐）

campaign 第 3 轮收口（GAP-REPORT「Round 8（campaign dwfrun-41fdc169
第 3 轮，2026-10-09）」节）：三任务全部落盘提交（R8A 76f34a5＋32bdcda＋
659203e／R8B 8d285f6＋a0075dd／R8C 本提交）。**两线产出**：①R8A——
L2 ε_forcing 换 cap M9 口径＝1.4030566524531613e-4（−66.22%——精确 66.2195%，
原记 −66.23% 系末位进位误，R8-R1 返工修正；精确分数串同步返工补正
「602」缺字，见 GAP-REPORT ⑦），==(1+R2max)
(E*−certified) 精确恒等式），l3/endgame 联动刷新、「待刷新」标注解除，
endgame 官方刷新 --reverify-certs 1575.5s 全过；②R8B——引擎 v2 条件阶梯：
相位 0 contact 区间证书 PASS／triple 判死（奇次幂余项符号交替＋两处历史
bug 修复），相位 1 M9 contact pdOPT@91iter/30542.1s=2.828 当量
**blocked**（attempt=25.759825152755017、margin −1.6138e-4、X9=+2.9348e-06
较 5.3e-5 阈低 18.1×）⇒ 相位 2 不触发（M10 不求解）——引擎改良此向定量
闭案（M9 缺口主体为松弛/域限制非 minorant 拟合损失）。**R8C 消费**：
endgame_chain v2 消费最小增量（coverage()/holeGapTable v2 标签＋v2 三态列
〔本轮终态＝blocked：attempt 精确分数＋lift −1.266e-4〕＋L2/L3 口径串
动态化＋双账本源）＋endgame 终态刷新 --reverify-certs 全过；closed=false
blocking=[L0,L3]（L0＝洞单片两引擎四档全阻：a5 M10 25.759951713655〔差
3.482e-5〕仍最优、v2 M9 25.759825152755 未越——原记「三引擎」系误将邻片
m079-m765 的 Lukács M9 混入洞片链，R8-R1 返工修正；L3＝永久开放 dead-at-(9,6)、
新 ε 1.403e-4≫ε_W=7.33e-13（差 1.9e8×，原记 1.9e9× 差 10 倍——R8-R1
返工修正）、caliber(c) L6 缺 11.2536×）；assembledRecord
=25.759445973097478 维持（spliceMap 维持 v2）；绿 L1/L2/L5/L6/L7；
progress=true（无新证书如实）。endgame_gate 增补式扩展（gate-④ 本轮节
regex＋D29 锚、gate-③′ v2 消费完整性）两路由 PASS；r8c3_l2m9/r8c3_engine
两子门复跑 exit 0；负对照×2 /tmp 篡改检出 exit 1；历史三门 r8_anchor
24/24＋r8_l6 8/8＋r8_m9 9/10（G6 失败根因＝R7B cap M9 rung 后到破坏
Round 8-1 冻结账本幂等性，重装配 diff 逐字段定位留档、不回写历史账本）；
r8c3_closure_gate exit 0；预算终账本轮 2.828/9.30、campaign 累计
33.372/40（M11 唯一路径但触发器＝扩容 ≥12 当量未触发）。decisions D29
结果回填＋D32 六裁决（分区计数语义／v2 探测判据／口径串动态化／L6 机值
出入／G6 处置／负对照归属）。本会话零求解零证书（一次代执行干预未遂
零损耗留痕 D32）。

## Round 7 汇总收口（汇总员-R7，2026-10-09，零求解）：复算收编＋D28 处置核实＋轮次终判——closed=false／assembledRecord 维持／progress=true（新证书 2）

campaign dwfrun-41fdc169 第 2 轮（Round 7 campaign-2）汇总员收口
（GAP-REPORT Round 7 节 ⑦）：三任务结果（R7A f26a97e／R7B
f05af76+bd15f27／R7C 4cdd6ed→ec54677）＋复算员独立复核（66 项纯
Fraction 审计全过；自写整数 Bareiss LDLᵀ 两新证书 42/42、38/38 严格
正定；三门独立重跑全过 r7_capm9 9/9×两路由／r7_m10 10/10×两路由／
endgame_gate 1563.3s+1602.2s；/tmp 篡改负对照复现检出 exit 1；预算
21.053≤22.5 重算）收编，转录出处 /tmp/r7audit/。D28 返工三处置本
会话直读在盘核实：①holeGapTable m079-m765.m10.lift_vs_m9_best 精确
基线＋lift_baseline 标注（dea7f13 刷新后 endgame.json）；②
ladderSummary.frozen_2026_10_09＋顶层 best=M9 25.75984622533888；
③E\* 双精确口径留痕不改数（D28 裁决：未来消费端〔M11 外推〕取十
进制口径）。**D28 执行留痕末项『endgame_gate 全门复跑』由本会话
补齐**：campaign 根、净树 HEAD=07b01c7、后台＋轮询 → PASS exit 0
（1493.8s；gate-1 重跑 1493.6s＋gate-2 存档 vs 重跑逐位一致＋
gate-3 closed=false blocking=[L0,L3] 逐项定量＋12 证书在盘一致＋
gate-4 双口径文档＋gate-6 树净）。轮次终判与 R7C 一致：closed=false
blocking=[L0（洞单片 m765-m748 M10 blocked 差 3.482e-5，HP 兜底
E\*−5.406e-4 仍全局瓶颈）,L3（永久开放 dead-at-(9,6) D24/D25；ε
前提差 1.40e-4≫ε_W=7.33e-13，L6 缺 11.25×）]；绿 L1/L2/L5/L6/L7
（L4 off-path）；assembledRecord=25.759445973097478 维持（无纪录
提升；wouldBe_if_chain_closed=E\*）；**progress=true**（新证书 2：
strip m079-m765 M10 翻绿〔洞 2/3 消除〕＋typed cap m0748 M9 换记）。
预算终账 21.053/22.5 当量、campaign 30.54/40 余 ~9.5——M11 即便
收敛为单片保守外推（M10 实测 5.93 当量×≥2≈12 当量）仍超余量，
下轮排程先过 HEAVY_BUDGET 预算门；下轮候选五件以 L2 ε_forcing
cap M9 口径重算（l2_rigorous.json 仍旧 M8 口径，D20 裁决 3）居首。
零求解零新证书零账本数值改动；唯一仓库写入＝GAP-REPORT ⑦＋本条目。

## D28 复核返工（返工员-R7，2026-10-09，零求解）：复算员三条轻微分歧核实与处置——两修一留痕，账面结论零变化

对象＝R7 终态（ec54677）复算员分歧三条，逐条 Fraction 亲算核实（详见
notes/decisions.md D28＋GAP-REPORT 末节补记）。①endgame.json
holeGapTable m079-m765 行 m10.lift_vs_m9_best 系对 strips.json blocked
节 12 位小数截断串取差（+1.413813668849739e-4），比 m9_campaign.json
精确分数取差（+1.4138136640702865e-4）高 4.78e-13、与权威斜率表
m10_campaign.slope_table 不一致——已修（endgame_chain.py 基线改读
m9_campaign 精确分数＋lift_baseline 行内标注，814e30c）；endgame.json
官方刷新 --reverify-certs 1532.5s（12 证书＋HP 重放逐位一致＋l3/l6/
l4_orbit 幂等门全过 exit 0，code_version=dea7f13 净树）；closed=false、
assembledRecord=25.759445973097478、blocking/partition/remainingGap
逐位不变，片 2 展示串 +1.414e-04 不变。②typed_ladder.json
ladderSummary.best 遗留 M8（25.759571185600716）而顶层 best 已换记
M9——冻结标注 frozen_2026_10_09（dea7f13；顶层动态重算正确、无消费者、
R7B『best 换记』宣称不失实）。③E* 双精确口径并存（Fraction(json
float)=7250791608880037/281474976710656 vs 25759986531/10^9，差
−8.674815035192296e-16；9 rung gap 与条带证书 margin 属前者，endgame/
campaign 账本属后者）——两口径均精确记录、全部不等式双口径下严格
成立、报告引用值双口径同；不改数，D28 裁决约束未来消费端取十进制
口径。零求解零新证书；progress 口径不变（无新证书、账面结论零变化）。

## Round 7（campaign dwfrun-41fdc169 第 2 轮，2026-10-07）：M10 双片＋cap M9 战役——洞 2/3 消除、cap 换记 M9、assembledRecord 维持，closed=false

campaign dwfrun-41fdc169 第 2 轮（总账面 Round 7 campaign-2，设计 D27；
与历史 Round 7 节〔2026-10-06〕以 campaign ID 消歧，D26 裁决 1 append-only）。
三任务：R7A m10-strips（Lukács M10 m079-m765＋a5 M10 m765-m748 并行，
f26a97e）＋R7B cap-m9-typed（typed m0748 M9 并行，f05af76/bd15f27）＋
R7C endgame-closure（本条目，0 求解纯收口）。战役窗口 10-07 14:47 三解
并行启动→10-09 03:1x R7A 终态提交。

**结果**：片 2 m079-m765 Lukács M10 **翻正**（pdOPT@110iter/121039.7s，
certified=25.759987007553885，正裕度 +4.7655e-7；斜率保持 45.624%≥
45.470% 勉强过阈）；片 3 m765-m748 a5 M10 **blocked**（noINFO@56/
64025.9s，attempt=25.759951713654896，差 3.482e-5；保持 36.11%<45.82%
斜率未保持）；cap m0748 M9 typed **胜出换记**（pdOPT@89iter/42305.7s，
certified=25.75984622533888=E*−1.403056611e-4，lift +2.750397e-4 落
预测带）。L0 洞 [−79/100,−187/250]→[−153/200,−187/250] 单片；cap 片
换记 M9（ε_forcing 口径牵动按 D20 裁决 3 标注待刷新）；
assembledRecord=25.759445973097478 维持（瓶颈＝HP 兜底片 E*−5.406e-4，
铁律 ≤E*+1e-6 复核过）⇒ splice-map 维持 v2（D20 裁决 4 机器判定逐位
相等）；分区 11→12 区域、citedCertificates 11→12 份。

**closed 重试判定**：closed=false、blocking=[L0（洞单片 m765-m748
blocked 差 3.48e-5，HP 兜底仍全局瓶颈；M11 外推 vs 引擎改良＝下轮
分叉，斜率输入已入 m10_campaign slope_table）, L3（永久开放——锚定
探针 dead-at-(9,6) D24/D25；cap M9 后 caliber(c) ε 前提仍差 1.4e-4≫
ε_W=7.33e-13，且 L6 仍缺 11.25×）]；绿 L1/L2/L5/L6/L7（L4 off-path）。

**预算**：本轮 Σsolve_s=227371.3s=**21.053 当量**（红线 22.5 未破）——
R7A 185065.6s=17.136（≤19 ✓）＋R7B 42305.7s=3.917（超 3.5 设计外推
+0.42，如实）＋R7C 0。campaign 40 当量累计：R8 9.491＋本轮 21.053=
30.54，**余 ~9.5 当量**——下轮 M11 双片外推（~2×M10 成本≈37 当量）
显著超余量，需持有会话按 HEAVY_BUDGET 机制裁决。

**progress=true**（新证书 2：strip m079-m765 M10＋typed cap m0748 M9，
均进程外重验 exit 0；另有 L0 洞缩小＋cap 换记的账面资产变化）。

**R7C 交付**：endgame_chain.py v3.x 消费扩展（M10 引擎标签＋
holeGapTable m10 三态列＋cap M9 归属修正＋L3/L6 口径串动态化诚实修正
——硬编码 22.5×/3.25e-14 系 R7-3 时点值改为 l3_analytic 动态生成）＋
endgame 全量刷新（--reverify-certs 1566.4s：12 证书＋HP 重放逐位＋
l3/l6/l4_orbit 幂等门 exit 0；确定性核查 2 轮 ALL PASS）＋
endgame_gate.py 增补式扩展（gate-④ 本轮节 regex＋D27 锚、gate-③ m10
列完整性，其余六门不动）＋文档三件＋D27 结果追加回填＋D27-C 执行
留痕。三门亲跑：r7_capm9_gate 9/9、r7_m10_gate 10/10、endgame_gate
两路由（见 GAP-REPORT Round 7 campaign-2 节 ⑥）。/tmp 三合成场景
演练（合成数据零入仓）。

## Round 6（campaign dwfrun-41fdc169 复核重放轮，2026-10-07）：终态收官复核——三门重跑全过＋证书独立复核零分歧，closed=false／assembledRecord 维持（零新求解）

campaign dwfrun-41fdc169（10-07 13:06 启动）收到的第 1 批输入＝历史
Round 6（2026-10-05）四任务结果＋设计的**重放**。复算员-R6（全程只读，
产物在 /tmp）以文件系统痕迹核实：本轮窗口零新求解/零新证书（唯一活动
＝endgame reverify 路径的 l4_orbit.json 幂等重生成〔13:14，与 HEAD
逐位一致〕＋/tmp/hp_cert_endgame_reverify.json〔13:12〕），仓库＝
R8 终态 HEAD=ad1f283。①**三门重跑全过 exit 0**：endgame_gate
（498.3s，六门）、r8_m9_gate（~35 分钟，10/10，含负对照三件全触发）、
r8_anchor_gate（39.3s，24/24，dead-at-(9,6) 与存档一致）。②**独立
Fractions LDLᵀ**（零 repo import）：HP 证书 18 PSD 块＋M9 翻正片
证书 42 PSD 块全对称严格正定、恒等式/margin 精确、篡改负对照全检出
（−2⁻⁵² 微扰正确不报）。③**assembledRecord 独立重算**＝min(11 分区)
=47517790735835014335570/1844674407417822803119=25.759445973097478
逐位一致；R8-1 战役数字逐项对上；**discrepancies=[]**；三处微小观察
（墙钟差 0.6s/0.2s、E\* Fraction(json float) 解析差 −8.675e-16、
solver_events Z 后缀笔误）零界值影响。④**汇总员亲跑**：endgame_gate
（campaign 根包装器路径，522.0s）PASS exit 0＋endgame.json/四账本
关键字段直读与历史 Round 6 节逐项一致（cap M8 25.759558913325233
未达标 4.28e-4、strips 五行全 blocked、l3 C_min=1.874e-11、l6 claim
现档 r*=0.00950125——R6 版 0.0033592 已被 R7-3/R8-3 超越，如实）。
**轮次终态**：closed=false（blocking=[L0：洞 [−79/100,−187/250] 两片
缺口 1.409e-4/1.643e-4、HP 兜底 E\*−5.406e-4 全局瓶颈；L3：ρ_raw
vacuous＋caliber(c) 前提未兑现＋即便兑现 L6 仍缺 11.254×＋锚定探针
判死 ⇒ 本管线无已识别 closed 路径]）；绿 L1/L2/L5/L6/L7（L4
off-path）；assembledRecord 维持无提升；**新证书 0／新严格引理 0
（复核窗口零新增——历史 R6 证书在盘经本轮重验，不重复计入）⇒
progress=false（D26 裁决 2，先例 R8-4 阶段 1 数值口径）**；重求解
0 当量。文档：GAP-REPORT 追加「Round 6（复核重放轮）」节（历史
Round 6 节权威性不变）、decisions D26。

## Round 8 收口轮次·阶段 1（2026-10-06）：endgame_chain v3（产出自适应，D20）＋closed 重试判定＋验收门 Round 8 口径——三线并行时序下的两阶段收口

campaign 第 3 轮（总 Round 8，设计 D19）。**时序事实**：本收口会话启动
（04:18）时 R8-1/2/3 产出均未落盘；执行中（04:52 核对）三线会话并行
运行中——R8-1 canary（m082-m079 Lukács M9，SDPA-GMP 04:26 启动）求解
中、R8-2 锚定 A 臂解在盘（判定未出）、R8-3 未见产出 ⇒ **裁决 D20：产
出自适应消费（在盘入账/未到盘如实记 missing＋维持 R7 记账）＋两阶段
收口**（阶段 1=机制＋文档＋自有文件提交＋功能五门；阶段 2=三线全部
提交后重跑 v3 消费产出→刷新账本→全门〔含⑥〕→终提交）。本阶段交付：
①**endgame_chain.py v3**（kind=n9-endgame-round8）：round8Inputs 四键
（m9_strips/m9_cap/anchor_probe/l6_joint，onDisk 布尔＋note 必非空）；
L0 逐片记账（holeGapTable：m082-m079 +2.0355e-4／m079-m765 +4.5079e-4／
m765-m748 +5.2295e-4，M9 三态＋canary lift₁ 未测如实）；cap 多引擎取
最优扩四候选（typed M9 在盘参与，D10/D16 裁决 2＋D20 裁决 1②）；L3
增补 D19 裁决 3 结构性前提与 R8-2 探针状态；L6 增补 R8-3 状态；L4 分层
记账不动（D16 裁决 3）；spliceMapVerdict 机器判定（D20 裁决 4，基准
固定常量 R7_ASSEMBLED——修复一处初版非确定性）。②**closed 重试判定
closed=false（blocking=[L0,L3]，逐项定量无硬凑）**；assembledRecord=
25.759445973097478（Fraction 逐位与 R7 相等）⇒ splice-map 维持 v2。
③**两种结局机器演练（/tmp/e8t，closed=true 分支）**：伪造 M9 三片
证书＋L3 前提兑现 ⇒ v3 正确产出 closed=true/blocking=[]/assembledRecord
=E*/cap 链抬升/L0 翻绿＋两拦截断言按设计触发（代码路径非死代码；合成
证书只在 /tmp 绝不入仓）。④--reverify-certs 全量亲跑三轮（257.5s 首
轮：10 证书＋HP 重放逐位＋l3/l6/l4_orbit 幂等门；确定性核查存档 vs
重跑逐位一致 ALL PASS）。⑤**endgame_gate.py Round 8 口径**：③ 增
round8Inputs 完整性＋spliceMapVerdict 一致性＋splice-map v3 拦截；④
文档三件改 Round 8/D20+；本会话自跑功能五门过＋⑥ 如实挂（三线未提交
文件在工作树——非本会话所属，D20 附记裁决 6）＋/tmp 篡改副本负对照
exit 1。**轮次终态（截至收口时点）**：closed=false（blocking=L0 条带
洞＋L3 断点，逐项定量见 GAP-REPORT Round 8 ④）；绿 L1/L2/L5/L6/L7
（L4 off-path 维持）；assembledRecord 维持 25.759445973097478 无提升；
新证书 0／新严格引理 0（三线产出未落盘——数值进展 0，机制进展=v3 两
结局自适应账本经演练验证）⇒ **progress 数值口径 false、机制口径就绪**；
重求解实耗 0 当量（收口不重解；M9/锚定求解归三线会话记账）；阶段 2
完成后以三线实际产出刷新本条目与 endgame.json。第 4 轮走向由 R8-2 分支
决定（alive ⇒ 锚定证书工程冲 closed；dead ⇒ 纪录冲刺＋终局文档）。

**阶段 2 终态刷新（同会话，13:5x；三线产出消费）**：①R8-3（b2875fd）：
r* 0.006718398305→**0.00950125**（≥硬阈 0.0084，μ@r*>0），L6 链扣缺口
22.507×→11.254×；**发现 R7-3 BD2 box 二阶通道证书无效（规则双 bug），
legacy 冻结并以修复后口径重交付**；本收口消费入账（read_l6 采信门过）。
②R8-2（9ff2921）：锚定探针 **dead-at-(9,6)**（两臂 pdINF，结构性不可行，
M* 外推不适用）⇒ **D19 裁决 3 的 closed=true 唯一已识别前提证伪**，终局
定位转「assembledRecord 冲高＋closed 永久开放」；其执行裁决原号 D20 与
本收口 D20（7623edb 在先）撞号 ⇒ 按 D16 裁决 1 重编 **D24**。③R8-1
（进行中）：canary m082-m079 Lukács M9 pdOPT@92 iter/31536s ⇒
**certified=25.760169689153>E\*（裕度 +1.832e-4，洞首片翻绿）**，lift₁=
+3.867e-4 过阈继续；M9 行已折入 strips.json（收口即时消费：洞缩至
[−79/100,−187/250]、分区 11 区域、citedCertificates=11）；m079-m765
求解中，余片＋cap＋endgame 终刷新按 **D22 裁决 4 归 R8-1 收尾**（本收口
不等待，D20 附记裁决 6 阶段边界）。④终刷新：--reverify-certs 全量
525.2s（**11 证书**含新 M9 重验 217.9s＋HP 重放逐位＋l3/l6/l4_orbit 幂等
门）全过；closed=false 维持（blocking=[L0 余两片洞逐项定量、L3 前提
判死＋L6 仍缺 11.254×]）；assembledRecord=25.759445973097478 维持
（HP 片仍全局最弱）⇒ splice-map 维持 v2（分区变化入 partition 字段）。
⑤gate 终态自跑（两阶段事实）：阶段 2 提交时点 ①②③④过、⑥如实挂；
**R8-1 canary 中间提交（03aae27）后树净 ⇒ 本收口在净树 HEAD 亲跑六门
全过 PASS exit 0 两路**（仓内 525.1s＋campaign 根 522.1s：reverify 重跑
11 证书＋逐位一致＋closed=false blocking 逐项定量＋文档三件＋git 干净）；
终态篡改负对照（L0.rigorous=true）exit 1。R8-1 余片完成后的再折入与
刷新按 D22 裁决 4 归其收尾。**轮次终态（截至阶段 2 刷新时点）**：closed=false；绿
L1/L2/L5/L6/L7（L4 off-path）；assembledRecord 维持无提升；**新证书
1 件**（M9 canary 条带）、**新严格引理/证书级结果 3 件**（L6 r* 0.0095
〔含 R7-3 BD2 无效撤回的诚实更正〕、锚定判死 dead-at-(9,6)〔第 4 轮
定向决定性信息〕、M8→M9 阶梯斜率实测〔lift₁=+3.87e-4〕）⇒
progress=true；重求解实耗（R8 系列，转录自其账本）：canary 31536s≈
2.92 当量＋Arm A 893s＋Arm B 15836s＋R8-3 零重求解（当量口径 10800s/
解，D21 裁决 3）；第 4 轮走向（按 R8-2 判死分支）：R8-1 战役完成度＞
纪录冲刺（M9 全折入后 assembledRecord 变化重判）＞终局文档（closed
永久开放口径）。

## Round 7 收口（含汇总员收口终态，2026-10-06）：closed=false／blocking=L0+L3／assembledRecord 维持 25.759445973097478；复算 3 分歧经 D17 返工全部处置（判定量值结论零变化）；新严格引理 3 件 ⇒ progress=true

## Round 7 复核返工（2026-10-06）：复算员三条分歧处置（裁决 D17）——判定量值结论零变化

三条全部核实成立（本会话独立复算，非转引）：①「锚定 λ′ 侧不可达
E*−e≥2.7e-3」高估 0.344%——档内 dist_to_E_star=0.0026907421793502806
逐位复算一致，GAP-REPORT/PROGRESS 改「=2.6907e-3 ≥2.69e-3 ≫1e-6」
（判死结论不变）；②D15 裁决 1／GAP-REPORT ③ 的 γ₂≈47–273×L_k 系漏除
2! 修复前 2× 旧值——闭式独立复算（φ″=3(2−2ν)^{−5/2}＋精确 M″）与档内
[23.485, 136.619] 逐位一致（0.0000%），文本改 23.5–136.6（机制结论
不变）；③HP 证书 provenance.gap_to_E_star.exact 隐含 E*=
7250791608880037/2^48（float64 二进精确）——根因 sdp_certify.py
Fraction(json float) 且注释自诩「精确十进制」；改 Fraction(str(...))
与 endgame_chain/gates 十进口径统一，按 reverify 同款命令重生成存档
证书：claimed_bound=47517790735835014335570/1844674407417822803119 及
blocks/params/checks 等全部数学字段逐位不变，gap exact 改
997153328507562120104790189/1844674407417822803119000000000（=十进
E*−certified，float 与 endgame.json margin_vs_E_star 逐位一致）；typed_
ladder/hp_solve 的同源 float64 口径维持（D17 裁决 4：显示不可见＋幂等
门敏感＋无宣称数依赖）。本会话亲跑：HP 重生成 25.0s（回读＋再编码逐
字节一致）；r7_eps_chain_gate 17/17（27.9s）、moment_gate 17/0
（39.5s）、endgame_gate 提交前功能五门过（239.8s，gate-6 因返工未提交
按设计拦截）＋提交后干净 HEAD 复跑 exit 0（见 git log 本提交后记录）。

## Round 7 收口轮次（2026-10-06）：GAP-REPORT Round 7 ＋ endgame_chain v2.x（消费 R7-1/2/3 产出）＋验收门 endgame_gate.py Round 7 口径

campaign 第 2 轮（总 Round 7，设计 D12）四任务三线收编＋本收口：①R7-1
矩容器抬天花板（1fab129，D13）：**判死**——KLT 引理 4.2 ζ 外积容器族接入
S₃ 商三点恒等式（N=9 R_k 常数 6/7 与 3/28 新推导），探针 (5,4)/(6,6)/(7,6)
Δe_val=+3.3e-7/−8.5e-7/+1.6e-7 全部 ≤ 全局噪声地板 8.53e-7、锚定 λ′ 侧
不可达（E*−e=2.6907e-3，复核勘误：原「≥2.7e-3」系上入舍入，D17）、容器被使用但不抬 e_val ⇒ 相位 B 按任务书条款不
执行、无新 cap 证书；moment_gate 17/0。②R7-2 L4 双轨道邻型计数（73ca3f3，
D14）：精确层**已严格**——K9 六色边染色枚举（scout 完备性证书＋Z[z,r]/
(r²+z²−1) 多项式恒等）幸存集=30240 标号染色=TTP 单 iso 类（**无条件引理**：
内积∈节点集 ⇒ 染色≅TTP）；稳定层常数 c_V≥1.1633e-3/计数阈值 ρ_max≈3.0e-5/
对径分离 2ν₄=0.019512（ρ 前提差 1540× 未满足如实）；轨道配平 6 棱顶+3 帽顶
Σ_y=2·mult ✓＋D12 帽-棱勘误再勘误（12ν₆+6ν₂ 非 ν₅）。③R7-3 ε-链零件
（4e85bca，D15〔原 D14 撞号重编〕）：**C_glob∈[1.596355678e-7,
1.597953632e-7]**（c0 级胞元全域严格，较 R6 C_min 抬 8518×，结合位点=
胞元角点非节点渐近——γ₂ 机制裁决）；判据余量 74.6×；L6 斜率压缩
**r*=0.0033592→0.0067184（2.00×）**（K-lift 认证斜率 12.836＋BD2 box 二阶
通道）；链 caliber(c)（ε_W=7.3257e-13 级）刷新：L3-need 74.6×/L5 6390×/
**L6 缺 22.5×——ε-链终卡点确认在 L6**（D7 预判兑现）；口径(a) ε_forcing
下 ρ_raw=51.0 仍 vacuous。本任务（R7-4）：endgame_chain.py v2→**v2.x**
（cap 三引擎取最优＝D10 扩展〔D16 裁决 2〕——R7-1 判死无证书 ⇒ 记账值
不变、判死对照入 round7Inputs；L4 分层记账〔layers.exactLayer/stableLayer
分记 rigorous，组件整体 false＋onCriticalPath=false 维持 D1/D12——D16
裁决 3〕；L3 quant/status 全量刷新＋翻绿判据〔D16 裁决 4：只认现行 ε 口径
或 caliber(c) 且前提兑现〕；L6/L0 刷新；reverify 增 l4_orbit 幂等重跑门）
＋**closed 重试判定 closed=false（blocking=[L0 洞（条带延后＋引擎升级判死）
＋L3（ε 前提未兑现＋即便兑现 L6 仍缺 22.5×）]，逐项定量无硬凑**＋
assembledRecord=25.759445973097478（Fraction min 逐位重算**不变**——十区域
记账值零改动 ⇒ splice-map 维持 v2 不出 v3 节〔D16 裁决 5〕；wouldBe_if_
chain_closed=E*）＋--reverify-certs 两轮全过（241.3s/239.8s：10 证书＋HP
重放逐位＋l3/l6/l4_orbit 幂等门）＋文档三件（GAP-REPORT Round 7 六段式/
PROGRESS 本条目/decisions D16 收编＋D15 重编号）＋endgame_gate.py Round 7
口径（六项：重跑/逐位一致/完整性含 L4 分层与 D1/D12 双引用/文档三件/
负对照检出面/git 干净；本会话自跑 **exit 0 两路**：campaign 根 thomson-n9/
前缀路径直跑＋/tmp CWD 绝对路径〔CWD 无关由 __file__ 保证〕＋/tmp 篡改
副本负对照 exit 1）。诚实声明：closed=false 与证据严格对齐——D12 两路线
共同前置（cap 抬升）被 R7-1 判死证伪于 (≤7,6) 档，R7-2/3 零件为「前置
兑现后即可消费」的预制件；第 3 轮候选=(9,6)/分块重议（新信息：更大档位
仍未测试）＞d_H=16＞L6 方向相关联合界（22.5× 已知改良）。R7-1/2/3 门
（moment 17/0 43s、l4_orbit ALL PASS 53s、r7_eps 17/17 31.5s）与
l4_orbit.py 幂等重跑（sha256 逐位一致）均为本收口会话亲跑。提交交错
（R7-3 的 4e85bca 曾收入 R7-1 的 D13 草稿、D14 撞号）由 D16 裁决 1 收编。

**Round 7 独立复算审计＋汇总收口（汇总员-R7，2026-10-06；复算与返工
数据截至 e2e165b）**：独立复算（只读、/tmp/audit_r7、零 import 仓库代码）
对整轮复核——①四门重跑 4/4 exit 0（moment 17/0 42s、l4_orbit ALL PASS
51.6s、r7_eps 17/17 30.2s、endgame 244.1s）；②自写 Fractions LDLᵀ 重验
HP 证书 18 PSD 块全正定＋certified 分数逐字符重算一致；③自写 Fractions
min 重算 assembledRecord 逐位一致（10 区域按值全等、margin 差 <1e-18）；
④mpmath.iv 区间复核 L4 稳定层（‖V⁻¹‖_∞ 保守 ~9%、c_V 18 位、ρ_max 相对
差 1.1e-16、前提差 1539.6×）；⑤四份 R7 账本与汇总逐字段对上、无
「标注严格实为数值」错标。**3 条分歧（2 誊写差＋1 条 R4 期预存纳米差）
全部成立并经 D17 返工（e2e165b）处置：锚定距离 2.7e-3→2.6907e-3、γ₂
比值 47–273→23.5–136.6（JSON 本就正确）、HP 证书 gap 口径统一十进精确
（数学字段逐位不变）——判定量值结论零变化**。汇总员在干净 HEAD=e2e165b
亲跑 endgame_gate 六门全过 PASS exit 0（239.7s，含 --reverify-certs 重跑
239.6s＋git 干净）；另修复本文件「Round 7 收口轮次」标题重复（e2e165b
插入所致，内容零变化）。**轮次终态：closed=false（blocking=L0 条带洞
＋L3 断点，逐项定量见 GAP-REPORT Round 7 ④），账本绿 L1/L2/L5/L6/L7
（L4 分层记账 off-path 维持 D1/D12/D16 裁决 3），assembledRecord 维持
25.759445973097478（=47517790735835014335570/1844674407417822803119，
无提升——cap 三引擎取最优仍 typed m0748_M8 胜出），本轮新证书＝0（R7-1
判死 ⟹ 无 a6 证书；D17 返工仅重生成 HP 证书 informational 字段、
claimed_bound 逐位不变）、新严格引理＝3 件（R7-2 无条件引理「内积∈
TTP 节点集 ⇒ 染色≅TTP」＋构造实现证书；R7-3 C_glob 严格区间
[1.596355678e-7,1.597953632e-7] 抬 8518×；L6 严格半径 r* 翻倍至
0.0067184）⇒ progress=true；重求解实耗 0/32 (8,6)-当量（全部 float，
预算剩余 32）；第 3 轮首选＝(9,6)/分块重议（矩容器判死构成「更大档位
仍未测试」新信息）＞d_H=16 重议＞L6 方向相关联合界（22.5× 缺口的已知
改良，估 r*→0.0095+）＞条带重解（依赖引擎复活）。**

## Round 6 收口轮次（2026-10-05）：GAP-REPORT Round 6 ＋ endgame_chain v2 重写（架构 C）＋ splice-map v2 ＋ 验收门 endgame_gate.py

campaign 第 1 轮（总 Round 6）四线收编：①R6-1 判死活 alive（3de154a：
Hermite 6 节点插值三判据全过，c0=4.52e-9，φ≥M 区间证书 W=2.13e-14，
裁决 D5/D6——h 固定、删 minorant 块、无 R2）；②R6-2/3 hermite-engine
（107b8eb/eb182ef）：cap M8 pdOPT 认证 25.759558052177（E*−4.285e-4，
验收未达标如实入账＋残差分解）、三片条带 M8 全 blocked（m082-m079
E*−2.783e-4 / m079-m765 −5.149e-4 / m765-m748 −5.230e-4——后者较
Lukács (7,6) +7.45e-4，贴 m* 受阻确被结构性削弱但幅度不足）；③R6-4
l3-analytic（f54717a，D7）：解析谱管全精确 Fraction，34.8× 断点如实裁定
未消除（0.6447 平台逐位=1−ν₆ 平凡值；C_min=1.874e-11 vs 需 1.2128；
闭链 ε*=6.42e-15/5.50e-13/4.89e-16；架构 ρ≈0.02 估计被证伪）；④R6-6
l6-intube（1c46714）：管内二次增长严格证书 r*=0.003359199152、
μ∈[0.0021869607,0.0021869622]>0（KLT §7.4 分解免 D³E；目标 0.07601 本
方法不可严格化，如实；ν₆ 12 边 Maxwell 不刚、增广 ν₂ 18 边刚性＋正自
应力）。本任务（R6-7）：endgame_chain.py 按架构 C 重写（L0/L1 读 a5 账本
两引擎取最优、L3 读 l3_analytic、L6 读 l6_intube、L4 按 D1 记
onCriticalPath=false 备选路线、主链 L2→L3→L5→L6）＋closed 重试判定
**closed=false（blocking=L0 条带洞＋L3 解析断点，逐项定量）**＋
assembledRecord=25.759445973097478（Fraction 逐位，HP 片瓶颈，a5 未改变
记账值；wouldBe 口径更新为 wouldBe_if_chain_closed=E*）＋--reverify-certs
全量重验（10 证书＋l3/l6 幂等重跑门，177.6s 全过 exit 0）＋splice-map
v2 节（10 区域总表/11 边界点衔接/三步推理/洞与 wouldBe 处置）＋验收门
endgame_gate.py（六项检查：重跑/逐位一致/完整性含 D1-L4 处置/文档三件/
负对照检出面/git 干净；自跑两路 exit 0：仓内直跑＋会话根包装器——D9，
与 hermite D8 同款）。诚实声明：closed=false 与证据严格对齐（hermite
引擎未转化为更强证书、L3 断点未消除、L6 半径缩 22.6×）；D1 回滚条件已
触发 ⇒ campaign 第 2 轮首选 L4 双轨道邻型计数。并行调度提交交错
（hermite/l3/l6 的 add -A 曾收编本任务中间文件）如实入账 GAP-REPORT
Round 6 ⑥。

**Round 6 独立复算审计＋汇总收口（汇总员-R6，2026-10-06，commit
b8e8176）**：独立复算（全程只读、/tmp 作业、零 import 仓库代码的自写
验证器 61 检查 0 败）对整轮复核——①四门（endgame/hermite/l3/l6）+
minorant 完整档重跑全 exit 0，/tmp 副本负对照演练（改 L0.rigorous=true
⇒ endgame_gate gate-2 失配 exit 1）与宣称逐字一致；②两条独立数学路径：
纯 Fractions LDLᵀ 重验 a5 cap M7/M8 证书（30 PSD 块全 PD、归一/defl/
claimed_bound==e−defl 全精确，M8=36253355014066527/1407374883553280
=25.759558052176974）＋独立区间重构 Hermite minorant（Σmax|M−h|=
7.1859e-15 ≤ W=3/2^47 ⇒ M≤φ 于 [−1,1] 独立成立，c0 14 位一致）；
③汇总数字逐项对上（cap ΔE、三片 blocked 值、l3 常数与 1−ν₆ 恒等、
闭链 ε*、l6 半径/22.627×、endgame 分区 min==assembledRecord 逐位、
11 边界点、exclusion 8 片 >E*）。唯一分歧＝splice-map v2.4 反事实句
不精确（全入账实为 25.759463585921285＝+1.76e-5、瓶颈片会换但 closed
仍 false）——**D11 勘误**（b8e8176 单句替换，账本零改动）。汇总员在
最终 HEAD 亲跑 endgame_gate（186.3s PASS）/hermite_gate（26/0）/l6（
9.8s OK）/l3（四门过、幂等）全 exit 0，git 全程干净。**轮次终态：
closed=false（blocking=L0 条带洞＋L3 断点），账本绿 L1/L2/L5/L6/L7
（L4 按 D1 off-path 备选），assembledRecord 维持 25.759445973097478
（无提升），本轮新证书＝a5 hermite cap M7/M8＋l6_intube 区间证书、
新严格引理＝R6-1 φ≥M minorant＋L6 半件→严格件（r*=0.0033592）；
重求解实耗 ≈5.5/8 (8,6)-当量；第 2 轮首选＝L4 双轨道计数（D1 回滚
已触发）。**

## Round 5 汇总轮次（2026-10-05）：GAP-REPORT Round 5 ＋ 架构 C-混合决策 ＋ Round 6 计划

Round 5 五线（commits `08a729b`（tube_probe）→ `34a5d6b`（KLT 研读）→
`54ef01e`（无悔三件）→ `f355b27`（架构决策）→ `5f91260`（复算员 7 条分歧
修订））＋独立复算审计的收编。GAP-REPORT.md 追加 Round 5 七节。要点：

1. **L3 路线 b tube certificate 探针判定 feasible=false**（`bounds/tube_probe.py`
   → `results/tube_probe.json`）：四条证据——①架构 ρ（halfgap=0.0186）全
   (M,K)∈{(4,3),(5,4),(5,5),(6,6)} 档零分离（Δe_val −1.1e-5…−3.3e-4，(6,6)
   uncond 未饱和排除 K 饱和解释）；②机制级——halfgap 处求解器不动用管自由度
   （bulge=0、TTP λ_min≥0），伪竞争者不住在半谱隙管内；③e_out(ρ)≥E\* 交叉点
   不随规模下移（(5,5)/(6,6) 同落 ρ∈(0.038,0.076)，R4 判据 ρ≤0.018506 全档
   不满足）；④粗管 e_out−E\*≥0.8 使 ε_forcing 退化 ≥0.8 切断两段式拼合、
   认证集居民只剩高能构型（min E 29.3–68 ≫ E\*）。24 档求解 2502.9s ≤1h 预算；
   独立复算员同种子三次重跑 22 个 e_val 逐位复现。(8,6) 封口实验（~11–15h/档）
   列为 R6-7 可选项默认不跑。
2. **KLT N=8 收尾研读**（`notes/klt-endgame-study.md`）：KLT 收尾＝零 ε
   三明治（Hermite 节点插值在候选处精确取等＋三点矩容器 SOS 恒等式＋区间
   Newton 修正）＋离散等号情形分析，全程无 ε/管半径/Taylor 余项；八条可迁
   引理与账本 L0–L7 缺口一一对应。核心启示：我们卡在"证书只能从下方逼近
   E\*"的根因是 Lukács 分段 minorant 不在节点处相切——Hermite 让裕度在节点
   处本来为零，"贴 m\* 裕度 ε² 消失"被结构性删除。gaps 7 条如实（pypdf
   提取风险、Lean 源未读、N=9 零探针等）。
3. **无悔三件把账本 L2/L5/L7 翻绿**（`results/{l2_rigorous,l4}.json`、
   `notes/splice-map.md`）：L2 ε_forcing 精确 Fraction 4.153454e-4（字面
   口径差 E\*·R2max=3.84e-8 不可满足性如实入账）；L5（无悔件名义"L4"）
   Procrustes C=14.8787/δ_max=0.17124（显式构造＋区间算术＋三负对照）；
   L7 12 原子区域装配说明书（写作当天全部验证命令重跑 exit 0）。L0/L3/L4/L6
   四断点原样，closed=false 不变。
4. **架构决策：C-混合（B 几何骨架＋KLT Hermite 引擎），escalated=false 不
   升级**（`notes/architecture-decision.md`）：A 实质证伪（探针四条证据）、
   纯 B 结构性不完整（L0 受阻根因＋L3 断点无手段）、C 唯一全覆盖（保留 B
   全部已严格资产，只换两件引擎）。关键定量预期自洽：L3 解析
   ρ_spec(4.15e-4)~√ε≈0.02（估计值）落入 L5 δ_max=0.17124 覆盖域。置信度：
   架构选择高、落地中等（Hermite 化 N=9 零探针是唯一硬风险）。
5. **Round 6 计划（R6-1…R6-7，总预算 ~2–3 周单机）**：R6-1 Hermite 引擎
   判死活探针最优先（0.5–1 天纯 float，两方案皆败 ⇒ C 倒塌升级重议）→
   R6-2 L1 cap 缺口归零（目标 e_val>E\*）/ R6-3 L0 三片装配（目标拼合纪录
   25.759446→≥25.759571）→ R6-7 收口；R6-4（L3 解析管）/R6-5（L4 双轨道
   邻型计数）/R6-6（L6 Hessian 分解免 D³E）独立可并行。
6. **独立复算 7 条分歧全部成立并修订收口**（commit 5f91260，runs 原始数据
   未动）：recommendedConfig 引用失实（JSON grep 计数 0，改可溯源引用）、
   倍率 ×3.6–4.0 写窄（实为 ×3.62–×4.99，(8,6) 折算改 ~11–15h）、金丝雀界
   非全称（改合并 24 runs 口径）、spot check E=29.28 不可复现（现行代码一律
   32.392058，改可复现性披露）、min|α+β| 漏自对（0.0195157、ρ≪0.01）、
   N=9 余项串型（φ^{(12)}/12!·∏(t−ν_k)²）、三小项出处。架构结论不受影响。
7. **汇总员复核（本会话亲自运行/读取）**：tube_probe.json verdict/
   separationTable/gaps/verdictRevision 读取＋recommendedConfig 计数 0 独立
   复核；l2_rigorous.json/l4.json 关键字段核对；三份 notes 关键节读取；
   GAP-REPORT L295/L497/L864 引用行核对；git log 五 commits 核对。未重跑
   任何数值（复算员＋研判员已覆盖，引自任务书独立复算块）。

## 无悔三件轮次（2026-10-05）：L2 ε_forcing 严格化 ＋ L4 Procrustes 常数 ＋ L7 拼接地图

Round 5 清单的三件独立交付（两收尾架构的地基），全部 exit 0：

1. **L2 严格化（`bounds/l2_rigorize.py` → `results/l2_rigorous.json`，30s）**：
   ε_forcing 从 float 口径改为精确 Fraction：**4.153454e-4**
   （= (1+R2max)·E* − e_dy + defl，逐轨道更细 −R1_o 入 JSON）。全链入账：
   38 PSD 块 LDLᵀ、归一化恒等式 ==0、R1/R2/defl/R2max 精确重算并与证书
   provenance 逐位相等、certified 重算 == claimed_bound、typed 恒等式于证书
   dyadic 数据 × 随机有理构型 ==0（残差精确为 0）、dyadic 装配损失（e floor
   1.79e-15、h/ψ/c ≤2⁻⁴⁹）精确入账。**诚实要点**：字面断言 ε_rig ≤ 数值口径
   不可满足——差恰为 E\*·R2max = 3.838e-8（数值口径 tube.json 自述忽略的
   (1+R2) 因子）；实现为 ε_rig ≤ ε_num + E\*·R2max + 1e-15（任何额外超出
   exit 1），精确差值与不可满足性说明入 JSON asserts.literal_rigorous_le_ledger。
   下游影响：ρ_spec 平台 0.6447 不受 +3.8e-8 影响（tube.json 扫描同平台）。
2. **L4 Procrustes 刚性常数（`bounds/l4_procrustes.py` → `results/l4.json`）**：
   账本 L5 位「Gram→构型」落地：**d_P := min_{Q∈O(3)}‖X−YQ‖_F ≤ C·δ，
   C = 14.8787，δ ≤ δ_max = 0.1712**（内积口径 |Δ⟨x_i,x_j⟩| ≤ δ；弦距离口径
   常数 2C = 29.7575；模 O(3)×重排）。方法＝显式构造证明（混合块/平行块
   投影分解 + 右极分解旋转规范，线性 Lipschitz——优于账本设想的 C√η）＋
   区间算术常数（z\* 隔离区间上 λ₃(S) ≥ 2.970726、λ₁ ≤ 3.014638，纯
   Fraction 区间 + Sylvester 主子式）。推导六步恒等式数值核对 max 残差
   3.3e-15；monte-carlo 299 试次 max d_P/δ = 2.002 < C（advisory）；
   --selftest 三负对照全部触发（秩亏平面构型拒绝 / t>λ₁ 认证器有齿 /
   非对称重排 δ=1.10 > δ_max 前提失效）。
3. **L7 拼接地图（`notes/splice-map.md`）**：12 原子区域完整装配说明书——
   总表（区间精确分数/证书/certified/裕度/口径）、逐类验证命令、覆盖语义
   （slab/strip 极点参数化 vs HP/cap 切口）、13 边界点衔接表、三步拼合推理
   （分类→逐区域→合取 min）、洞与 wouldBe 25.759571、配套证书（z\*/λ_min/
   L2/L4 本轮件）、诚实边界。写作当天全部验证命令逐一重跑 exit 0：5 slab +
   3 strip + cap 的 --verify-cert、HP 按存档 --k 64 重放逐位相等、
   endgame_chain 判定逐字复现。

判定不变：Stage A closed=false（本轮三件是地基非断点修复；L0 洞/L3 结构断点
原样）。账本映射：任务书「L4 Procrustes」= 账本 L5 位；账本 L4（邻型计数）仍未开始。

## Round 4 汇总轮次（2026-10-05）：GAP-REPORT Round 4 ＋ Stage A 完整性判定（closed=false）

Round 4 四线（commits `6ef9647`/`21a1aca`/`f650e1c`/`04fcafc`/`049f85c`/
`8c6c42b`）＋独立复算审计的收编。GAP-REPORT.md 追加 Round 4 六节（① 条带覆盖
与拼合 ② 收尾链装配 ③ 局部极小与 λ_min ④ Stage A 判定＋Round 5 清单 ⑤
Stage B Lean 规划草图 ⑥ 诚实声明）。要点：

1. **Stage A 判定：未完成（closed=false）**——八引理仅 L1（cap m≥−0.748 ⇒
   E≥25.759571186）严格；不宣告『严格数值证明完成』。当前拼合口径全空间
   严格下界维持 **25.759445973**（HP 兜底，E*−5.41e-4）；新区域纪录
   [−0.90,−0.82] ≥ 25.760813176470（3/6 条带认证，(8,6) 地板 E*−2.0e-4
   实测盖死 [−0.82,−0.748] 的 (8,6) 路线）。Round 5 精确清单（GAP-REPORT
   R4 §④）：L3 路线 b tube certificate（首选实验，~3h/档，可行性未验证）＞
   L0 三片受阻条带 ((9,6)/分块) ＞ L6 Taylor 三阶余项界＋管内全域区间
   Hessian ＞ L4 刚性 ＞ L5 Procrustes ＞ L7 书面拼接＋L2 卫生项。
2. **λ_min 三条独立实现相容**：tube μ₀=0.138365 ≤ full_local_min
   **0.14378982**（链上取强，含临界性，TTP 模 SO(3) 严格局部极小区间证书）
   ≤ 审计第三路 0.143849 ≤ 数值 0.143935；链级严格管半径公式值 0.07601
   （缺 Taylor 三阶余项界，非严格半径）。
3. **证书账本**：22 份 dyadic 证书（LP/SDP/HP/slab×5/cap×3/typedcap×8/
   strip×3）＋2 份区间证书全部经 endgame --reverify-certs（125s）与审计
   独立重跑（Fractions LDLᵀ、HP reproduce 逐位）；12 原子区域精确 Fraction
   记账机器断言无缝盖满 [−1,1]。
4. **Stage B 草图**：结构层（恒等式/解析引理/L7 拼接）进 Lean；数据层
   （全部 dyadic/区间证书）保留为外部证书、纯 Fraction 验证器＋哈希钉注入；
   求解器不进信任链；本机仍无 Lean 环境（`which lake lean elan` 复查
   not found）。
5. **汇总员复核（本会话亲自运行，均 exit 0）**：endgame_chain.py 判定重跑
   （closed=false/拼合纪录逐字复现）；typedcap-m0748_M8 与 strip
   m085-m082_M8 两份 --verify-cert（38/42 块 LDLᵀ、重算一致）。
   strip_work/（105MB 可再生 SDPA 工作目录）随本轮 gitignore（与 hp_work/
   typed_ladder_work/ 同款）。

## Round 4 收尾装配轮次（2026-10-05）：endgame_chain.py —— 拼合纪录判定 + m≥−0.748 引理链闭合判定

三线（条带/管状/局部极小）产出的装配与判定落地。新增 `numerics/bounds/endgame_chain.py`
→ `results/endgame.json`（判定 0s；`--reverify-certs` 进程外重验证 5 类证书共 125s）。

1. **拼合口径（判定 1）**：条带 6 片中 3 片受阻（正裕度断言 exit 1）⇒
   `allPositiveMargin = false` ⇒ **assembledRecord = min(各原子区域覆盖界) =
   25.759445973097478（HP 证书值，全局最弱片）**，瓶颈 = 洞 [−0.82,−0.748]
   （3 个 blocked 子带由 HP m∈[−9/10,1] 兜底，3 片并列全局最弱）。分区 12 原子
   区域（5 slab + 3 认证条带 + 3 洞子带 + cap）以精确 Fraction 装配并断言无缝
   盖满 [−1,1]；exclusion 片全部 > E*（精确），TTP-covering 片（HP/cap）全部
   ≤ E*+1e-6。若六片全正，拼合纪录将抬到 cap 证书值 25.759571186
   （endgame.json 的 wouldBe_if_all_strips_positive 字段）。blocked 片的
   best_certified_attempt（25.759782986/25.759535741/25.758718429）是有效界但
   未入账（无存档证书），不参与拼合 min。
2. **收尾链闭合判定（判定 2）**：**closed = false**，断点 L0/L2/L3/L4/L5/L6/L7
   （仅 L1 已严格）。精确剩余差距（remainingGap，逐引理到参数）：
   - **L3 谱管（结构断点）**：需 ρ_spec ≤ 0.018506（半谱隙）；ε_forcing=
     4.153e-4 处 ρ_spec = 0.6447（差 34.8×）；零集地板 ε=1.5e-8 仍 0.0466
     （差 2.52×）。逐三元组松弛在本证书族内不可达 ⇒ 路线 b tube certificate
     （~3h/档，可行性未验证）或 d_H=16/(9,6)。
   - **L0**：洞 [−0.82,−0.748] 现由 HP 兜底 25.759446 = E*−5.41e-4（< E*），
     需 3 片受阻条带翻正（(9,6) 阶或分块装配，Round 5）。
   - **L6**：TTP 点已严格（full_local_min λ≥0.14378982 含临界性 + tube_analysis
     μ₀=0.138365 双实现交叉）但 ① λ→半径转换缺 Taylor 三阶余项界——r_tube
     0.07601 = sqrt(2ΔE/λ) 公式值复核一致（≤7.9e-14）但**非严格半径**；② 管内
     全域二次增长仅 ball_scan 数值（r=0.076 → λ_min≈0.0336>0）。
   - **L2**：ε_forcing 公式精确但 float 求值，精确 Fraction 入账列为卫生项
     （非断点）；**L4/L5/L7**：整条未开始。
   - 无"本轮可补的小步"（smallStepFixable=false）：每个断点都需要新证书族/
   新引理/新区间计算，单个小步无法把 closed 翻真。
3. **证书重验证（--reverify-certs，全部 exit 0）**：cap m0748_M8（38 块 LDLᵀ，
   25.759571185601 重算一致）、3 条带（42 块 LDLᵀ 各全正定，重算=声称）、最弱
   slab sm91o100_m9o10（25.769683493481 逐位一致）、HP 按存档 reproduce 命令
   （显式 --k 64）重生成到临时文件 **claimed_bound 逐位一致**。
4. **诚实边界**：E* 仍是三源校验参考值而非已证最优（所有 ≤/> 断言语义为与
   参考值不矛盾）；判定输入只认存档账本/证书字段 + 进程外重验证 exit code；
   六片书面拼接产物（独立文档）仍未写出（Round 2 起遗留，本轮覆盖结论以
   endgame.json 记账为准）。

## 管状量化轮次（2026-10-04）：tube_analysis.py —— Round 4 清单 2/3-Hessian 落地

GAP-REPORT Round 3 §④ 第 2 项（管状收尾的 typed 重诊断）+ 第 3 项 Hessian 半部分的
落地。新增 `numerics/bounds/tube_analysis.py` → `results/tube.json`（全流程 85s）。
要点：

1. **商空间 λ_min 与管半径**：TTP 切空间 Hessian（公式 = Σ_{i<j}(uᵢ−uⱼ)ᵀM̃(uᵢ−uⱼ)
   − Σλᵢ(uᵢ·vᵢ)，M̃=3r⁻⁵ddᵀ−r⁻³I）18 维谱 = 3 旋转零模 + **λ₊ = 0.143935**（与
   Round 2 cap_ladder 记录逐位一致；FD 测地线二阶差分复核相对偏差 ≤4.2e-8；
   ‖BR‖=2.4e-9）。**管半径 r_tube = sqrt(2·ΔE/λ_min) = 0.07597**（ΔE = E*−certified
   (m0748_M8) = 4.1535e-4；口径：R²⁷ 弦距离、模 SO(3)、15 维本质切空间）。管内
   λ_min 随机方向扫描（数值证据）：r=0.02/0.04/0.076 → min λ_min =
   0.110/0.087/0.034（管内二次增长保持为正但斜率衰减）。
2. **严格 λ_min（本轮 rigorous）**：区间算术（mpmath.iv dps40）deflation 方案——
   旋转补空间 15 列区间正交基 N(z)（区间 GS，逐点正交归一）+ 15×15 区间 LDLᵀ
   （全主元区间严格正 ⇒ PD）；z-箱取 local_min.json 严格区间（宽 7.63e-7），
   K=128 子箱分裂控制包裹（324 项乘积依赖问题，单箱宽 0.45 → K 箱 3.4e-3）。
   **μ₀ = 0.138365 认证**（∀z∈箱 ∀切向 δ⊥旋转：δᵀH_zδ ≥ μ₀‖δ‖²；损失 3.9%；
   81s）⇒ 严格管半径 ≤ 0.07748。**与并行工作流 full_local_min.py（commit
   6ef9647）双实现交叉验证一致**：0.138365（本文件，仅 Hessian 二次型口径）≤
   0.14378982（full_local_min，中值形式+预条件同余，**含临界性 L1–L3**）≤
   0.143935（数值）——引理链 L6 取强者 0.14378982，对应管半径 0.07601。
   本文件自检链：区间/数值 B 逐条对拍（2.2e-15）+ μ₀ < λ_num 卫语句——两者在
   开发中各抓出一个实现 bug（赤道 sin/cos 表错误×2、Cholesky/LDLᵀ 混写），
   均修复后通过；对拍已固化为常设自检。
3. **typed 谱管重诊断（核心结论：结构性不足）**：m0748_M8 证书数据（certificates/
   n9-stage-a4-typedcap-m0748_M8.json 的 dyadic 块）装配三轨道 λ_AAA/λ_AAB/λ_ABC，
   求值器对精确 Fraction eval3 对拍 1e-12；恒等式部分核对 Σ84 λ_cls(TTP) =
   1.096e-4 ≤ E*−e_dy = 4.144e-4 ✓。**ε_forcing = 4.1531e-4**（每类 λ_cls ≤
   E*−e_dy+Σcounts·R1；typed 放大 ×1/类 vs untyped ×504 型）。均匀网格扫描
   （n=512，域 [−0.748,1]³∩detG≥0，三轨道）：**ρ_spec 阶梯 = 0.0466(ε=1.5e-8)
   / 0.1043(1e-7) / 0.2548(5.3e-6~1e-4) / 0.6447(≥3e-4)** vs 需求 0.01851
   （半谱隙）——ε_forcing 所在平台差 **34.8×**；压到 TTP 自身 slack 水平
   （5.35e-6）仍差 13.8×；零集地板（全网最深点 (0.1961,0.1961,0.1961)，三轨道
   共同伪近零 9.4e-9 与 R1 同级，疑为 SOS 族真零点）仍差 2.5×。**结构性发现**：
   typed 贴界（4.15e-4）未换来零集局部化——AAB/ABC 在远端有 3.7e-6 级近零，
   同口径 ρ_spec(2e-5) 反从 untyped 的 0.0755 恶化到 0.2548（证书/域不同，定性
   对比）。**判定：瓶颈 = slack 零集几何（L3），非薄层厚度——a₀=−0.7476 追加解
   的 ε ~3.7e-4 与 ε_forcing 同在 0.6447 平台，ρ_spec 零变化，不动用**（预算
   保留）。
4. **引理链设计**（tube.json lemma_design，L0–L7）：L0 条带 [−1,−0.748)（部分
   已严格：[−1,−0.90] 五片；[−0.90,−0.748) 未开始）→ L1 cap 已严格（25.759571186）
   → L2 强制（证书已严格，ε_forcing 本轮落口径）→ **L3 谱管（断点：本证书族
   内不可能达标，数值证据）** → L4 刚性（未开始，前置 L3）→ L5 Procrustes
   （标准不等式未写）→ L6 局部极小（TTP 点本轮严格 μ₀；管内全域未开始）→
   L7 拼接（未开始）。三条路线取舍（routes）：a 追加 cap（数据判定不动用）；
   **b tube certificate（下一轮首选）**：两点 minorant 6 节点管外分段 + 三点域
   乘子加 (t−ν_k)²−ρ² 因子，复用 typed_ladder 管线 ~3h/档；c 文献移植（无可用
   定量结果）。
5. **诚实边界**：扫描是逐三元组松弛（84 类联合 + Gram 秩 3 一致性未利用——恰是
   路线 b 的构造空间）；λ_min 严格版只在 TTP z-箱（管内全域二次增长未严格）；
   E* 仍是参考值；区间部分依赖 local_min.json z-箱与教科书 Hessian 公式（数值
   侧 FD+对拍双复核，公式本身未在 Lean/文本中重证）。

## Round 3 汇总轮次（2026-10-04）：GAP-REPORT Round 3 ＋ 三线收编与复现性收口

Round 3 三线（commits `c9a177d` → `9734683` → `a7b61b5`/`cbf4cc6` → 复现性修复
`241b61b`/`e56be8f`）＋独立复算审计。GAP-REPORT.md 追加 Round 3 五节（① typed
原型 ② 高精度重解 ③ typed 阶梯与条带可行性 ④ Round 4 清单 ⑤ 诚实声明）。要点：

1. **纪录口径**：单一证书全局纪录**不变**（LP 25.729490962，唯一覆盖全构型）；
   **拼合口径全空间严格下界 25.752411 → 25.759445973**（最弱片由 Round 2 SDP
   证书换成 HP 证书，slab 五片仍全 > E\*）。HP 认证损失 4.3e-7（Round 2 为
   6.97e-3）——SDPA-GMP 把恒等式残差从 8.6e-5 压到 1e-38，实验关闭"折减由求解器
   残差主导"诊断；E\*−cert = 5.41e-4，覆盖域仍 m ≥ −9/10。
2. **typed 阶梯**（`typed_ladder.py`，S₃ 商＋SDPA-GMP＋slab_band 式认证）：8 份
   精确证书全过断言（38 PSD 块/份）；最好档 m0748×(8,6) certified
   **25.759571185601**（E\*−c = 4.15e-4——1e-3 stretch 达成、1e-4 差 3.2e-4 如实
   记录；> Round 2 区域纪录 +2.49e-3）；typed (8,6) 地板首次反超 untyped 同 M；
   切口 −0.748 距 m\* = −0.7476 仅 4.40e-4（仍含候选 ⟹ 结构性反转保持，阶梯不
   收敛 E\*）。条带可行性分段判定：[−0.90,≈−0.845] 直接可做（3-4 片宽 0.02 正
   裕度 +0.9e-3~+6.1e-3）；[−0.845,−0.755] (7,6) 任何片宽不可行（松弛地板
   E\*−1.3e-3 控制，0.005 宽实测仍 −1.4e-3），(8,6)（地板 E\*−4.15e-4）有实质
   希望须逐片实测；乐观 9-12 片/保守 4 片＋(9,6)；Round 4 条带必须换 SDPA-GMP。
3. **复现性两处分歧收口**（复算员发现）：hp_solve 默认 `--k [64]`＝存档粒度
   （旧默认 [48,56,64] 首个通过 k=48 得 25.759445614952，低 3.58e-7，两值均
   有效）＋provenance.reproduce 记录复现命令（commit 241b61b）；typed 阶梯全部
   8 档用 HEAD（lp_penalty 导出）全新重解刷新（尾差 M6 −3.68e-9/M7 ≤2.2e-8/
   M8 −3.0e-8，断言全过，commit e56be8f）。
4. **汇总员复核**（本会话亲自运行）：`typed_ladder.py --verify-cert` 全部 8 份
   （逐份 exit 0，certified/LDLᵀ/归一化残差重算一致）＋ `--selftest`（精确自检
   全过）＋ HP claimed_bound Fraction 算术（47517790735835014335570/
   1844674407417822803119 = 25.759445973097478）＋ 阶梯 8 档裕度重算 ＋ E\*/m\*/
   Round 2 纪录参照值核对。SDPA-GMP 重解与 venv 重跑（calibrate/selftest）未
   亲跑——引独立复算审计块（其声明零改动仓库、全程 /tmp 镜像）。
5. **Round 4**（GAP-REPORT R3 §④）：typed (8,6) SDPA-GMP 条带 [−0.90,−0.755]
   （把拼合界从 25.759446 抬向 M8 地板 25.759571）→ m0748_M8 证书上的管状重诊断
   （ρ_spec 需求 ≤0.0185 vs 重测；零噪声地板 5.8e-3）→ 刚性＋15 维区间 Hessian
   （最独立可先做）→ (9,6)/d_H=16 规模化＋SDPA-GMP 管线推广（slab 五档/cap 旧
   五档/m=−0.95）→ 书面拼接＋Lean 侧顺延。

## typed 原型轮次（2026-10-03 夜）：numerics/bounds/typed/ —— 分型三点构造原型与全部正确性验证

Round 2 下一轮清单第一项（typed 三点原型，N=9 收尾的共同先决条件）的落地。
新增 `numerics/bounds/typed/` 包（core.py 装配＋solve.py 求解复核＋三个 CLI），
**正确性验证全过**；界数值为数值证据（同 untyped 口径，折减 e_safe）。详见
`bounds/typed/README.md`。要点：

1. **构造（N=7 论文 §6 的推广）**：任意类型划分（索引块），分型基沿用 S² 调和
   分解（Q_k/Y_k 协变块，与 untyped 共用 build_Q——引理 4.1 机制逐位同源）；
   typed 三点对称化＝根求和×2（换位只转置 Y_k）；份额表、Ψ/gm、逐三点类
   slack、归一化 (6) 的推广、Lukács/Markov–Lukács minorant（一侧/两侧区间）。
   cut 模式对任意分型有效（纯组合推导）；band 模式要求类型 0＝极小对 {0,1}
   （尺寸 2），类 (0,0) 与含 {0,1} 的 slack 带 [lo,hi]（PAPER.md §6.4 域）。
2. **机器自检三层**（每次求解前跑，不过即拒绝出界）：核恒等式 Q_k=Re(ζ^k\bar ζ^k)
   ~1.7e-14；分型正性（引理 4.1 逐类型随机 PSD）ok；**typed 恒等式**
   Σ_T λ_T+Σ_all=Σ_{i<j}H_cls−e 于随机数据 rel ~1e-14…1e-12——覆盖份额求和=Ψ、
   gm/Ψ、核项根和×2=D、归一化计数、s(1,1,1) 全部装配通路。
3. **紧合自检表**（`typed_selftest.py` → `results/typed_selftest.json`，exit 0）：
   N∈{3,4,6,12} 普适最优构型、(2,n−2) 分型、small(6,4) 一档全紧合——e 高出
   真值 +1.0e-8 / +1.5e-7 / +2.0e-8 / +4.7e-6（untyped 表 +2e-8/+3.8e-8/
   +2.3e-7/+1.3e-6，同量级；均在预注册有效阈 5e-6 内）。N=2 理论退化行
   （无第三点/无三点类，份额与 slack 机制空转，assemble_typed 显式拒绝），
   不计入判定；两点紧合性由 lp_bound 表覆盖。
4. **N=7 校准**（`calibrate_n7.py` → `results/typed_calib_n7.json`，(2,5) band、
   (M,K,d_H)=(6,6,10) 同论文，exit 0）：cap [−1,−0.99] 的 e_opt 与 E(P) **双向
   贴合**（e−E(P) = +2.2e-6；理论最优被夹在 [E(P)−2.27e-16, E(P)]，同时校准
   有效性与近紧性）；五 slab 的 e_opt 全部高于论文可行值（e−e_paper =
   +1.7e-4…+9.1e-4；untyped Case-1 校准偏差 +1.2e-3 同量级；方向与"我们的
   SOS 乘子族是论文 6/5/5 块族的超集 ⟹ 最优 ≥ 论文可行值"一致）。与 Round 2
   `slab_band.py` 的独立 typed 实现交叉验证：同档 slab [−0.99,−0.98] (6,6)，
   其 e=14.453835 vs 本包 14.453887（差 +5.2e-5，超集方向一致）。
5. **N=9 原型**（`prototype_n9.py` → `results/typed_prototype_n9.json`；类型
   (3,3,3)＝tri_cap_prism 轨道布局，cut a=−151/200）：small(6,6) e_safe=
   25.752634258（75s）；mid(7,6) raw e=25.758110647 **已高于 untyped (8,6) 同
   区域 e_safe 25.757893**（typed 方向性收益在 raw 值可见），但 420s 时限内
   未收敛（Δ=4.3e-3 → e_safe=25.753788）；midlarge(8,6) 超 10 分钟单命令预算
   于 18:48 终止（无结果；瓶颈＝cvxpy 单线程规范化）；large16(9,6,d_H=16)
   构建成功（1,214,429 变量/9,895 行/最大块 165/122 个 PSD 块，1.45s、0.20GB）
   但求解在本机（24GB）OOM kill（exit 137）——两档失败均已如实写入 JSON 的
   attempts_unfinished。规模/耗时表见 typed/README.md。
6. **局限（如实）**：typed 界均为数值证据（无精确证书；严格化走 slab_band.py
   的 dyadic 路线，未接）；d_H=16 在本机未跑通（超内存），需类型自同构约化
   （(3,3,3) 的 0↔1 对换可把 10 条 slack 并成 5 条）/分块直连求解器；求解器
   精化（时限内残差主导折减）与 Round 2 诊断相同，仍未解决。


## Round 2 汇总轮次（2026-10-03 夜）：GAP-REPORT.md 追加 Round 2 ＋ 三线收编

GAP-REPORT.md 保留 Round 1 为历史、追加 Round 2 五节（① 新严格纪录 ② cap
阶梯与收尾设计 ③ slab 带进度 ④ 下一轮清单 ⑤ 诚实声明）。要点：

1. **纪录口径两层**：单一证书的全局严格纪录**不变**（LP 25.729490962，唯一
   覆盖全构型）；新增**拼合口径**——slab 五片（[−1,−0.90]，全部 certified >
   E\*）∪ SDP 证书（m ≥ −9/10，25.752410818）铺满全空间 ⇒ 拼合全空间严格
   下界 = 25.752410818（最弱片）。区域最好严格界：cap m0755 certified =
   25.757085350767（覆盖 min 内积 ≥ −151/200，超 LP 纪录 +0.027594）。
2. **SDP 证书折减结构**：certified = (e−36·R1)/(1+R2)，R1 = 1.813e-4（求解器
   残差 8.58e-5＋δ 平移 9.6e-5）、R2 = 1.726e-5；36·R1 = 6.53e-3 ≈ Round 1
   数值折减 6.66e-3——折减仍由求解器精度主导；舍入损失仅 3.1376e-4。
   自检表 N∈{3,4,6,12} 全紧合（+2.0e-8/+3.8e-8/+2.3e-7/+1.3e-6）；N=2 理论
   退化（明示偏离全过判据）。独立复算（审计）：SDP/cap/slab 全部逐位复现，
   自写 LDLᵀ 18/18 与 42/42 块，零 import 自写装配重算 certified 逐位相等
   （verifier 第二实现缺步由审计关闭），discrepancies 为空。
3. **cap 结构结论**：(8,6) untyped 阶梯有原始间隙地板 ~5.5e-4（−0.90→−0.755
   仅 6.05e-4→5.49e-4）；管状收尾在该配置对任意精度不成立（谱管需求
   ρ_spec ≤ 0.0185 vs 可得 0.0755–0.33，×504 型放大零噪声地板 7.7e-3）——
   需要 typed / d_H=16 / 精确取等。两点信息穷尽（LP g ≤ 0.0305 是单区间）。
   endgameDesign 八组件：cap 精确界已严格，管宽/强制/Hessian 数值证据，
   刚性/全空间局部极小/拼接未开始，slab 带已盖 [−1,−0.90]。
4. **slab 带**：5/5 片严格证书盖满 [−1,−0.90]（certified 25.7697–25.8159，
   全部 > E\*，裕度 +9.7e-3…+5.6e-2）；瓶颈＝求解器残差进折减（~3e-3）与
   (7,6) 紧度地板（−0.85 附近裕度枯竭）；a₀=−0.90 与 cap/Round-1 线无缝
   衔接，扩带至 −0.755 才需 typed/d_H=16。
5. **下一轮**：typed 三点原型（3+3+3 分型，small=(6,4)×a₀=−0.755 先行）→
   large=(9,6) D3h 约化 → 求解器精化（36·R1 → 2e-4 量级）→ 15 维区间
   Hessian → Lean 化结构定理。
6. **汇总员复核**（/tmp 镜像、系统 python3 无 cvxpy）：`sdp_certify.py` 全链
   exit 0（33.1s，certified/blocks 与已提交证书逐位同）；`slab_band.py
   --verify-cert`（最紧片）exit 0（10.3s，42 块 LDLᵀ、裕度 +9.697e-3）；
   slab/cap 裕度与常数独立重算核对。工作树遗留的 n9-stage-a2-sdp.json 改动
   经比对仅 provenance date/runtime_s 两键（blocks 逐位同），随本轮提交收编。

## cap 阶梯与收尾设计轮次（2026-10-03 晚）：cap_ladder.py → 阶梯/精确证书/残余量化/endgameDesign

GAP-REPORT ③-3（切口下探）落地并把收尾所需成分全部量化。产出
`numerics/bounds/cap_ladder.py` 与 `numerics/bounds/results/cap_ladder.json`
（5 档解数据 `results/cap_solution_midlarge_mXXX.json`、3 份精确证书
`certificates/n9-stage-a3-cap-*.json`）。详见 `bounds/README.md` 首节。要点：

1. **阶梯**（midlarge=(8,6)，种子 20261003，每档单命令 ~4 分钟）：a₀ ∈ {−0.90,
   −0.85, −0.80, −0.77, −0.755}，B(a₀)=e_safe 全档过断言 0 < B ≤ E\*+1e-6；
   最好档 **m0755：B = 25.757892542（E\*−B = 2.094e−3）**，比 Round 1 主界
   （m=−0.90，25.752724581）抬 0.005168；m090 复跑与 sdp.json 存档逐位一致。
   **结构发现**：原始间隙 −0.90→−0.755 只从 6.05e−4 → 5.49e−4——(8,6) untyped
   已到紧度地板，阶梯不收敛 E\*（与 N=7 cap 的精确取等结构性不同）。
2. **精确证书（区域严格界，非全局）**：m0755/m077/m085 三档过 sdp_certify 机器
   （切口以精确有理数参数化，如 −151/200；B_W=39/40 的 (39/40)²>(1−a)/2 精确检查）。
   最好 **certified(m0755) = 25.757085350767**（精确有理数，覆盖 min 内积 ≥
   −151/200；18 PSD 块 LDLᵀ 全过、回读逐位重算一致、进程外独立复核通过）。
   超 Round 1 SDP 证书 0.002675、超 LP 严格纪录 0.027594；E\*−cert = 2.901e−3。
   **全局严格纪录不变**（LP 25.729490962 仍唯一覆盖全部构型）。
3. **残余量化（数值证据，方法与标注入 JSON）**：(a) 强制公式——E ≤ E_band 的构型
   每个 Gram 三点 slack ≤ 14(E_band+36w−e)+psdF/2+503·r1（单项 ≤ 全和的 ×504 型
   放大；N=7 靠精确取等消掉）；当前 ε(E≤E\*)=2.9e−2、零噪声地板 7.7e−3。
   (b) 管扫描——m0755 的 slack 零集离 TTP 三点组 ρ_spec(2e−5)=0.0755 ≫ 需求
   0.0185（谱半间隙）；ε=2e−5 水平集占 Gram 域 0.94%。**管状收尾在 (8,6) untyped
   上对任意求解精度不成立（结构性），需要 typed/d_H=16/精确取等证书**。
   (c) 两点管——LP 证书 g=φ−f̂ ≤ 0.0305 的水平集测度 1.32/3.99（两点信息穷尽）。
   (d) TTP Hessian（数值）：λ₊=0.143935、3 旋转零模、FD 复核 2.8e−5 ⇒（采样
   凸性半径 ≥3.0 内）E ≤ E\*+δ ⇒ 测地距离 ≤ sqrt(4δ/λ₊)=0.241。
4. **endgameDesign**：八组件清单（cap 精确界[本轮已严格]/管宽/强制/Hessian[数值]/
   刚性[未开始]/全空间局部极小[未开始]/slab 带[另一条线]/拼接[未开始]）＋量化差距
   ＋下一轮优先级（typed 证书原型为先决条件）。


## SDP 严格化轮次（2026-10-03 下午）：三点 SDP 下界的精确证书 n9-stage-a2 ＋ 构造自检表

接 bounds 轮次（见下）GAP-REPORT ③-6 的四缺步，本轮把 SDP 数值界严格化并补上
构造正确性的紧合外部校验。两个提交：

1. **`numerics/bounds/sdp_certify.py` → `certificates/n9-stage-a2-sdp.json`（1.9MB）**：
   midlarge (M,K)=(8,6) × m=−0.90 主界配置的确定性复跑（本机 Clarabel 复跑与
   `results/sdp.json` 存档 e = 25.759381941996825 **逐位一致**，解数据落盘
   `results/sdp_solution_midlarge_m090.json` 1.4MB）→ 全部数据舍入为分母 2⁻⁴⁸
   的 dyadic 有理数（h 最近、e 向下、18 个 PSD 块最近舍入后 **+δI 平移修复**，
   δ 取最小充分 dyadic，地板 2⁻⁴⁰；逐块过 `thomson_certs/exact.py` 无主元
   LDLᵀ 严格正定，全部一次通过）→ 精确残差折减、纯 Fractions 重算：

   **certified = (e − 36·R1)/(1 + R2) = 25.752410818467**
   （精确值 579902747221865232/22518386775890053；R1 = ‖slack 恒等式精确残差‖₁
   = 1.813e-4（含求解器残差 8.58e-5 与 δ 平移），R2 = minorant 精确残差加权 ℓ₁
   = 1.726e-5）。断言全过：certified > LP 严格纪录 25.729490962195（超出
   **0.022920**）且 ≤ E*+1e-6（E* − certified = 0.007575713）。
   **舍入损失 e_safe − certified = 3.138e-4**（精确有理数入 provenance）——
   严格证书只比 Round 1 数值 e_safe 低万分之三。装配镜像（a=−9/10 精确）与浮点
   版结构全等、系数一致到 5.7e-14；两个**精确**自检：三点恒等式在随机有理
   config × 随机 dyadic (h,e,PSD F) 上 ==0 逐位成立（3 次）、引理 4.1 正性
   Σ_all ≥ 0 精确成立（3 次）；SOS 逐点非负/残差求值一致性/minorant 平方式
   抽查全过；证书回读 decode→重建→重算逐位一致、再编码逐字节一致。另做了
   进程外独立复核（fresh 进程只读 JSON：19 块 LDLᵀ 全 PD＋界值重算逐位相等）。
   **范围（如实）**：只覆盖 min 内积 ≥ −9/10 的构型（m_lo=−9/10, m_hi=1）；
   [−1,−0.9) slab 带未开始；三点恒等式/引理 4.1 是引用的结构定理（PAPER.md
   §4–5.1），机器侧只有随机有理点的精确实例验证，未重证明；独立验证员对
   (e−36R1)/(1+R2) 装配的第二实现仍未做（证书 JSON 自含全部数据可复核）。
2. **`numerics/bounds/construction_selftest.py` → `results/selftest.json`**：
   BV/CW 三点构造在 N∈{2,3,4,6,12} 普适最优构型上的紧合自检表（Round 1 遗留：
   构造数学正确性只有 N=7 校准间接覆盖）。N∈{3,4,6,12} 全部**紧合**（small
   (6,4) 一档即过；e 高出真值 2.0e-8 / 3.8e-8 / 2.3e-7 / 1.3e-6，均在预注册
   有效阈 5e-6 内——超出才是构造/实现的硬错误）：

   | N | E_true | e(SDP, small) | E_true − e |
   |---|---|---|---|
   | 3 | 1.732050808（√3） | 1.732050828 | −2.0e-8 |
   | 4 | 3.674234614（3√6/2） | 3.674234653 | −3.8e-8 |
   | 6 | 9.985281374（6√2+3/2） | 9.985281601 | −2.3e-7 |
   | 12 | 49.165253058（二十面体精确构造） | 49.165254341 | −1.3e-6 |

   N=2 按理论退化行处理：n−2=0 ⇒ 三点恒等式两边恒零、界机制不存在（实测
   SDP 路径在 2(n−2) 除零处 ZeroDivisionError，如理论预期），不计入通过判定；
   N=2 紧合性由 lp_bound 两点表覆盖。这是三点构造正确性目前最强的外部校验
   （LP 界紧合 ⊆ 三点 SDP 紧合，4 个独立构型全中）。
3. **Round 1 两处清理的确认（本轮验证，无需新改动）**：`results/sdp.json` 的
   stale (m=−0.9, medium) 条目与 `local_min.json` 的 zStarIntervalWidthDecimal
   浮点伪精度（→ 精确十进制宽 7.62943e-07）**均已在 Round 1 审计提交 81476f0
   修复**（本轮 grep 当前文件：medium/25.758579 不存在、宽度字段已是 7.62943e-07；
   git show f061935 确认旧条目曾在、81476f0 commit message 记录了移除）。
4. **可移植性修复（验证门反馈）**：验证方用系统 `python3`（miniconda，
   numpy/scipy 有、cvxpy 无）跑 `sdp_certify.py` 在 `import sdp_bound` 处
   ModuleNotFoundError 退出 1。修复：`sdp_bound.py` 的 cvxpy 改为可选导入
   （cp=None，`solve_case` 入口 `require_cvxpy()` 给可操作错误——只有求解
   路径需要它，装配/自检/证书复核不需要）；`sdp_certify.py` 在无 cvxpy 的
   解释器下**显式**回退到已提交的解数据（打印明示、provenance 记录来源与
   "生成运行经 venv 复跑逐位一致"）；`construction_selftest.py` 缺 cvxpy 时
   快速失败并给出正确命令（它必须求解，无回退路径）。实测：`python3
   numerics/bounds/sdp_certify.py` 全链 exit 0，certified 与已提交证书
   **逐位一致**（579902747221865232/22518386775890053，仅 provenance 时间/
   来源描述变化）；venv 下 selftest 重跑 PASS（值不变）。

## 高精度运行（2026-10-03，Round 3）：SDPA-GMP 扩展精度重解，m≥−0.90 认证纪录 25.752411 → 25.759446

Round 2 认证值 25.752410818 距该档 e 值 25.759382 的 ~6.97e-3 折减里，求解器残差主导
（Clarabel 双精度 IPM 停滞：insufficient progress@33，收紧容差复跑与 Round 1 存档逐位
一致），舍入本身只 3.14e-4。本轮把求解做干净：

1. **路线 a（SDPA-GMP 扩展精度）**：同一 midlarge (8,6) m=−9/10 三点 SDP 以**精确有理
   系数**导出 SDPA sparse .dat-s（`hp_solve.py build_rows`，代入 Clarabel 解逐条校验
   b−A(X) 与其自报残差一致），SDPA-GMP 7.1.3（GMP 200 位）求解 pdOPT@69 迭代
   （mu=6.0e-33，p.feas=3.9e-73）：**e = 25.759446403**（比 Clarabel 停滞值高 6.4e-5，
   距 E* 5.4e-4），恒等式残差 **R1=1.0e-38 / R2=1.2e-40**（纯 Fraction 重算；Clarabel
   为 8.6e-5 / 1.7e-5，降 ~34 个数量级）。构建配方 `sdpa_build.sh`（GMP 6.3.0+netlib
   spooles+两处源码补丁）。
2. **认证路径升级（sdp_certify.py）**：① 解数据新增 `exact` 字段（66 位十进制精确
   回读的 Fraction），dyadic 舍入对 exact 走**整数运算**——σ 块尺度 ~1.5e15 时
   float64 中转会丢格点精度（这是 σ 大尺度问题的正解，σ 子问题重解的探索见
   results/hp.json provenance.route_decision）；② PSD 修复 δ 一律从 2^-40 地板起步、
   由精确 LDLᵀ 判定翻倍（不再按 float64 eigvalsh 估计起步——大尺度块的估计噪声
   ~1e-16·‖M‖ 会固化进 δ）；③ `--min-bound`（纪录线，默认仍 LP 纪录）/`--ref-safe`
   （rounding_loss 参考覆盖）两个新选项，旧路径回归逐位兼容（Round 1 数据复认证
   通过且 δ 更小）。
3. **结果**：certificates/n9-stage-a2-sdp-hp.json，**certified = 25.759445973097**
   （粒度 2^-64；R1=1.19e-8、R2=2.5e-11，认证总损失 4.3e-7）——**改进 Round 2 纪录
   +7.0352e-3**，E* − certified = 5.41e-4；断言 certified > 25.752410818 且
   ≤ E*+1e-6 全过（负对照 --min-bound 25.7599 实测 sys.exit(1)）。回读重算逐位一致。
4. 诚实边界：sdpa_gmp 二进制不入库（sdpa_build.sh 源码重建，~5 分钟）；hp_work/ 的
   .dat-s/.result（11MB）可由脚本再生，已 gitignore；数值复核 accepted=False 仅因
   float64 λmin 门限被 σ 尺度噪声触发（精确判据全过，见 results/hp.json
   numeric_check_note）；覆盖域仍为 m≥−0.90（不含更近对径对），与 Round 2 相同。

## bounds 轮次汇总（2026-10-03）：下界攻坚五连提交与差距报告

本轮（2026-10-02/03，commits `1cc93e1` → `81476f0` 共 5 个）产出 `numerics/bounds/`
全套下界计算，并经一轮独立复算审计（含审计修复 `81476f0`）。完整差距分析见
**`GAP-REPORT.md`**（本仓库根目录）。要点：

1. **LP 两点界（严格）**：B = 25.729490962（精确有理证书
   `certificates/n9-stage-a.json`，舍入损失 1.31e-6）；距 E\* = 25.759986531 差
   0.030495569。独立复算确认（三路径重解 <1e-9、证书逐位复核、独立 minorant
   认证 55 万叶全过、LDLᵀ 独立复验）。
2. **SDP 三点界（数值）**：m=−0.90 切口 e_safe = 25.752724581（raw 25.759381942，
   距 E\* 仅 6.0e-4；Δ=6.66e-3 主要是求解器精度），差距缩至 **0.007262**；
   m=−0.95 切口 25.750080212。可复现性与求解器稳定性经审计确认；**严格证书
   未获得**（缺解数据落盘＋dyadic 舍入＋精确恒等式验证四步）。
3. **z\* 隔离（严格）**：[0.703648376463, 0.703649139406]（宽 7.63e-7），
   族内严格局部极小（E″>0）；独立区间路径复核确认；全空间（18 维）局部
   极小未做。
4. **结构性判断**：TTP 最小内积 −0.7475605 落在 m≥−0.90 主战场内部——N=7 式
   "Case 1 正裕度"在 N=9 不存在，收尾必然走"近紧 cap（切口抬向 −0.7476）＋
   管状＋刚性＋全空间局部极小"，外加 [−1, a₀] 的 typed slab 带（估计 ~9–13
   片，未开始）。下一轮优先级：求解器精度（Δ→2e-4 量级）＞ large=(9,6) ＞
   切口下探 ＞ typed 原型 ＞ slab 扫描 ＞ SDP 严格化桥 ＞ 全空间局部极小。
5. 诚实边界：严格成立的只有 LP 界、z\* 区间、族内局部极小；SDP 数字均为数值
   证据；E\* 本身是待证参考值。详见 GAP-REPORT.md §④。



## 升级运行（2026-10-02，第 2 次）：做了什么、为什么

本次为增量升级（4 个 commit，`9850653` → `d9a55e1`），不推倒重来。动机全部来自 v1 奠基运行的
教训（见上"遗留问题"与"给下一次运行的提示"）：

1. **`numerics/optimize.py` 参考能量改读唯一可信来源**（`9850653`）：硬编码
   `REFERENCE_ENERGY = 25.759986531` 改为运行时读 `../thomson-workflow/data/energies.json`
   的 `energies.9.value`（三源校验表，value 25.759986531 / highPrecision 25.759986531270 /
   status "confirmed"）。加载器校验 status 必须为 confirmed、value 与 highPrecision 相差
   ≤1e-6，文件缺失/损坏即打印原因并退出 1——**绝不静默回退到内置常数**（会冒名顶替可信源）。
   v1 教训：参考值散落在 optimize.py、README、与工作流校验表三处，存在漂移风险。
2. **`optimize.py --selftest` 负对照**（`d346f6c`）：v1 教训是"验收门只被证明过会接受，从未
   被证明过会拒绝"。现在断言路径抽成 `accepted()`，真实模式与负对照走同一条路径；selftest
   在同样的 64 起点优化后，用故意错的参考能量（真值 ±0.5）各走一遍：真值必须被接受（对照
   的对照），两个错值必须触发 `ACCEPTANCE FAILED`，全部满足才打印 `SELFTEST PASS` 退出 0
   （不写任何文件）；任一不满足退出 1。**负负对照**：把 `accepted()` 篡改为永远返回 True 的
   副本跑 `--selftest`，确实 `SELFTEST FAILED` 退出 1（证明 selftest 本身有牙）。未知参数
   退出 2；energies.json 缺失退出 1，均已实测。
3. **`check.sh` 加固**（`d9a55e1`）：v1 只把 token 扫描与 sorry 计数打印出来供人读，脚本
   本身不判死刑。现在：token 扫描任一命中即打印命中行并 `exit 1`（实测：向 Solution.lean
   注入一行 `sorry` 后 `SKIP_BUILD=1 bash scripts/check.sh` 退出 1、报 FORBIDDEN TOKEN，
   随后 `git checkout` 还原）；sorry 计数必须恰好挑战 4/解 0，空 build.log 即 `exit 1`
   （判定逻辑在合成 build.log 上实测：4/0 通过、1/1 双双报 MISMATCH、空文件触发空日志判
   定；**脚本内完整路径仍需 lake，未跑**）；axioms.log 非空判定；语句比对失败显式
   `exit 1`（set -e + pipefail 下本就会非零，现为显式消息）。另：`__pycache__` 核查——根
   `.gitignore` 第 1 行 `__pycache__/` 已覆盖两个现存 pycache 目录（`git check-ignore -v`
   实测），`git ls-files | grep -i pycache` 为空即**从未有缓存文件被跟踪**，无需
   `git rm --cached`；`formal/lean/.gitignore` 仍补了一行 `__pycache__/` 以防子树被单独
   拷走。
4. PROGRESS 即本条目；README 的数值复现条目与复现命令同步更新（JSON 来源、`--selftest`）。

## 升级运行验收结果（本次实际执行的命令与输出）

1. `python3 thomson-n9/numerics/optimize.py` → 退出码 0：
   `reference energy: …/thomson-workflow/data/energies.json  N=9 value 25.759986531
   (highPrecision 25.75998653127, status confirmed)`；`best energy: 25.759986531270`，
   `|diff| = 2.698e-10`，`starts reaching the best basin: 64`，`ACCEPTANCE OK`；
   `reference_config.json` 与改动前逐字节相同（`git status --porcelain` 不显示它）——
   改能量来源未改变任何数值行为。
2. `python3 thomson-n9/numerics/optimize.py --selftest` → 退出码 0：
   `selftest: true reference accepted by the gate (control of the control)`；
   `ACCEPTANCE FAILED: |E_best - 26.259986531| >= 1e-06` 与
   `ACCEPTANCE FAILED: |E_best - 25.259986531| >= 1e-06`（两个错值均触发断言）；
   `SELFTEST PASS`。负负对照：篡改 `accepted()` 恒 True 的副本 → `SELFTEST FAILED`、
   退出 1。`optimize.py --bogus` → 退出 2；JSON 路径指向不存在文件 → 退出 1。
3. `bash -n formal/lean/scripts/check.sh` 通过；`SKIP_BUILD=1 bash formal/lean/scripts/check.sh`
   → 退出码 0（步 1 跳过 + 步 2 无禁 token）；注入 sorry 后同命令退出 1（FORBIDDEN TOKEN），
   还原后树净。
4. git：4 个 commit 后 `git -C thomson-n9 status --porcelain` 为空。

## 升级运行的遗留（未跑的照旧如实记）

- 本机仍无 elan/lake/lean（`which lake lean elan` 全部 not found，本次复查）：`check.sh`
  步 3–6（Mathlib 构建、sorry 计数在真实构建上的判定、公理打印、语句比对）、
  `negative-control.sh`、`pin_hashes.sh` 依旧**未运行**；本次新增的判定中，只有能在无
  Lean 环境下执行的部分（token 扫描及其负测试、合成 build.log 的计数判定、`bash -n`）
  得到实测。
- v1 遗留第 2/3/4/5/6/8 条（manifest 非逐字拷贝、SHA256SUMS 未钉、比对 DEFERRED、
  Comparator/第二内核未搬、严格数值未开始、4 个 sorry 未证）原样顺延，本次未触及。


## 本次做了什么（2026-10-02，奠基运行）

1. **读蓝本**：`references/thomson-n7-lean/REPRODUCE.md`（验收脚本蓝本）、
   `formal/lean/scripts/check.sh`、`ComparatorChallenges/ThomsonN7.lean`（挑战文件写法与
   `triCapPrism` 定义/引理出处）、`references/klt-n8-paper.pdf`（方法蓝本，33 页已抽文本
   通读证明概述与 §4/§6/§7）。
2. **仓库骨架** `thomson-n9/`（git 初始化，单 commit，工作树干净）：
   - `README.md`（定理陈述、候选构型与参考能量、两阶段验收标准、当前状态）、
     `notes/strategy.md`（攻坚路线）、本文件。
   - `formal/lean/`：自包含 Lake 包，`name = "ThomsonN9"`，仅依赖 Mathlib
     `d13f23b723b8a846827a245b89c10fc7d3f11612`（与参考仓库同 rev）；
     `lean-toolchain`（`leanprover/lean4:v4.34.1`）、`.gitignore` 自参考仓库原样拷贝；
     `lake-manifest.json` 拷贝后**仅**把根包名 `"ThomsonN7"` 改为 `"ThomsonN9"`（依赖
     pins 逐字节不变，diff 已验证；原因见"遗留问题"第 2 条）。未运行 `lake update`。
   - `ComparatorChallenges/ThomsonN9.lean`：固定挑战命题，4 个 `sorry`：
     `thomson_nine_M0`（E ≥ 36/2）、`thomson_nine_M1`（E ≥ 189/8）、`thomson_nine`
     （∃ z ∈ (0,1)，`triCapPrism z` 全局最小）、`thomson_nine_unique`（最优构型在正交
     变换＋重排下等于某个 `triCapPrism z`，以"∀ y, E x ≤ E y"为全局最优假设）。
     `triCapPrism` 及其全部可采纳性引理（`tri_top/tri_bot/tri_cap/tri_cases/
     triCapPrism_injective/triCapPrism_mem` 与所依赖的 `norm_sq_cyl_sub` 等 4 条辅助引理）
     逐字移植自参考仓库挑战文件并在头注注明出处。
   - `ThomsonN9.lean` 根模块（`import ThomsonN9.Solution`）与 `ThomsonN9/Solution.lean`
     占位（`import Mathlib` ＋ 未来证明结构说明；无 sorry、无公理、无元编程）。
   - `scripts/`：`check.sh`（适配：包名/定理名/4 个 sorry；`SHA256SUMS.txt` 不存在时跳过
     哈希步；语句比对在解文件尚无任何常量时报 DEFERRED）、`DumpBody.lean`（原样）、
     `compare_statements.py`（SKIP 集合改为空）、`CheckAxioms.lean`（奠基期检查挑战文件中
     已证引理的公理）、`negative-control.sh`（篡改 `thomson_nine` 不等号须被检出；奠基期
     以未篡改挑战文件的 dump 充当解方 dump）、`pin_hashes.sh`（新增：把 git 跟踪文件
     的 sha256 钉入 `SHA256SUMS.txt`）。
   - `numerics/`：`energy.py`、`optimize.py`、`family.py`、`reference_config.json`。
3. **数值复现**（环境：macOS 15.6 arm64，miniconda python3，numpy 2.4.6，scipy 1.17.1）。

## 验收结果（本次实际运行的命令与输出）

以下命令都在本次运行中实际执行；未运行的一律写在"遗留问题"。

1. `python3 thomson-n9/numerics/energy.py` → 退出码 0：
   `octahedron energy: 9.985281374238571  expected 9.985281374238570  diff 1.78e-15`，
   `energy.py smoke test OK`。
2. `python3 thomson-n9/numerics/optimize.py` → 退出码 0（验收门）：
   - `starts: 64   seed: 20261002`；`local minima found (6 d.p.): [25.759987]`；
     `starts reaching the best basin: 64`；
   - `best energy: 25.759986531270`，`|diff| = 2.698e-10`（阈值 1e-6），
     `norm deviation from 1: max 0.00e+00`；
   - `ACCEPTANCE OK`；写出 `numerics/reference_config.json`（17 位有效数字）。
   - 复跑一次 JSON 逐字节相同（diff 为空）：输出可复现。
3. `python3 thomson-n9/numerics/family.py` → 退出码 0：
   - `family optimum: z* = 0.703648401219   E(z*) = 25.759986531270`；
     与引用常数 0.70365 差 `1.599e-06`；
   - `|E(z*) - E_global| = 0.000e+00`（能量一致）；
     `max |pairwise-distance spectrum difference| = 1.645e-07`（构型同构指纹一致）；
   - `FAMILY CONSISTENCY OK`。
4. 挑战文件移植保真：脚本比对确认参考文件的 4 个区段（定义 R3..cyl、triCapPrism 定义、
   辅助引理 norm_sq_cyl_sub..cos_sub_eq_one_of_cyl_eq、tri 引理 tri_idx_inj..triCapPrism_mem）
   在本仓库挑战文件中逐字节出现，`ALL PORTED REGIONS VERBATIM: True`。
5. 脚本静态/功能验证（无 Lean 环境下能做的部分）：
   - `bash -n` 对 `check.sh`、`negative-control.sh`、`pin_hashes.sh` 全部通过；
     `python3 -m py_compile` 对 `compare_statements.py` 通过。
   - 用合成的 DumpBody 式 tsv（/tmp，已清理）实测 `compare_statements.py`：
     篡改 `thomson_nine` 类型行后输出 `kind/universe/type mismatches:
     ['ThomsonN9.thomson_nine']` 与 `STATEMENT COMPARISON: FAILED`（退出码 1，正是
     negative-control.sh 所 grep 的两个串）；同一文件自比对输出
     `STATEMENT COMPARISON: OK`（退出码 0）；空"解"文件比对报全部 missing 且 FAILED
     ——这正是 check.sh 步 6 在奠基期选择 DEFERRED 而非执行的原因。
6. git：`git -C thomson-n9 status --porcelain` 为空（提交后复查）。

## 未运行／未做成的事（遗留问题，后续运行接手）

1. **Lean 构建与 check.sh 未运行**：本机无 elan/lake/lean（`which lake lean elan` 全部
   not found）。因此 `bash formal/lean/scripts/check.sh`、`scripts/CheckAxioms.lean`、
   `scripts/negative-control.sh`、`pin_hashes.sh` 都**未**验证过——它们是按参考仓库适配的，
   逻辑上自洽但没有任何一次实际执行。移植的 Lean 引理逐字节来自参考仓库（其
   REPRODUCE.md 记录了在 Lean v4.34.1 + Mathlib d13f23b 下完整构建通过），但这不能替代
   在本仓库的一次真实构建；首次构建预计需联网拉取 Mathlib 缓存（约 10–25 分钟）。
2. **lake-manifest.json 非逐字拷贝**：仅根包名 `ThomsonN7` → `ThomsonN9`（diff 验证其余
   字节相同）。原因：Lake 对根包名不匹配的 manifest 会视为过期并重新解析依赖（等同于
   被禁止的 `lake update`），逐字拷贝反而违背"钉死依赖"的目的。此判断未经本机构建验证。
3. **SHA256SUMS.txt 未钉**：按任务书，命题冻结前允许不钉；`check.sh` 步 1 目前打印跳过
   信息。冻结后运行 `bash formal/lean/scripts/pin_hashes.sh`（该脚本本身也未运行过）。
4. **语句比对 DEFERRED**：解文件是占位、没有重述挑战常量，`check.sh` 步 6 报 DEFERRED
   而非执行比对；`negative-control.sh` 已把比对工具本身置于被检状态，但也未运行。
5. **Comparator / 第二内核层未搬**：`run_comparator.sh`、`thomson_n9.comparator.json`、
   `second-kernel.sh`、`tools.sh` 未纳入（任务书未要求，属于阶段二收尾）。
   `check_claims.py` 与 `claims.tsv` 未搬（无对应论文索引，不适用）。
6. **阶段一严格数值未开始**：无区间算术证书检查器；`189/8` 下界、`z*` 唯一驻点、SDP
   正性均未严格化。`optimize.py`/`family.py` 是浮点复现，不构成任何下界的证明。
7. **可复现性边界**：固定种子下本机复跑逐字节可复现；但跨 numpy/scipy 版本 SLSQP 轨迹
   可能微差，`reference_config.json` 的字节级稳定性以本机（numpy 2.4.6 / scipy 1.17.1）
   为准。若工作流门检出脏树，重跑 `optimize.py` 后重新提交即可。
8. **4 个 `sorry` 均未证明**（这正是后续运行的任务）；M1 = 189/8 的证明路线未定
   （候选见 `notes/strategy.md` §1）。

## 给下一次运行的提示

- 先装 elan（`curl https://elan.lean-lang.org/elan-init.sh | sh`）再跑
  `SKIP_BUILD=1 bash formal/lean/scripts/check.sh` 与完整 `check.sh`，把"遗留问题"第 1 条
  关掉；然后钉哈希（第 3 条）。
- 数值侧下一步：`numerics/rigorous.py`（区间算术）＋ M1 严格下界证书（strategy.md §5）。
- 本文件按运行顺序追加；不要改写历史条目。
