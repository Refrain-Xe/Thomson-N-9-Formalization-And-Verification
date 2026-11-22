import Mathlib
import ThomsonN9.TableB1Data
import ThomsonN9.TableB5Data

/-!
# Table B5Chain data (R21B / r21b): the exact rational constants of the
# chain-assembly / node-identification piece

This module is deliberately self-contained: it imports only `Mathlib`,
`ThomsonN9.TableB1Data` and `ThomsonN9.TableB5Data` (both frozen,
read-only), imports no in-repo solution module, and is imported only by
`ThomsonN9/TableB5Chain.lean`.  It materialises, as explicit `ℚ`
literals, the data layer of the L2→L3→L5→L6 chain assembly
(`notes/l5l6-seam.md` §3 δ=ρ seam identification; emitter
`numerics/bounds/r21_b5chain_data.py`, seed 20261021, heavy_solves=0;
provenance = sha256 of TableB1Data.lean / TableB5Data.lean /
r20_l5l6_seam.json / tube.json, recorded in
`results/r21_b5chain_data.json`):

* `g01..g45` — the 15 pairwise ν-container gap lower bounds (exact ℚ;
  container b lower end − container a upper end, from the TableB1Data
  container endpoints bit for bit, one `norm_num` identity theorem
  each);
* `gMin` — the minimum of the 15 gaps (exact ℚ; the
  identification-window constant: ρ < gMin/2 makes the node
  identification unique, `ident_unique` in TableB5Chain);
* `r_ball` — the L6 certified ball radius 950125/10⁸
  (= r* = l6_intube quadraticGrowth.rigorousRadius exact decimal);
* `sqrt2Up`/`dmaxUp`/`tUp` — 200-bit integer-Newton rational upper
  envelopes of √2 / √deltaMax / √(3·sqrt72Up) (same recipe as
  `r20_seam_probe.sqrt_rat`, reproduced bit for bit — `CBhi`/`CAhi` are
  cross-checked against `r20_l5l6_seam.json` supply exact Fractions);
* `CBhi` = k1·dmaxUp + tUp (route-B C_B envelope, k1 := s1Up·u₁·sqrt72Up/l₃²),
  `CAhi` = (s1Up·u₁/l₃² + 2·sqrt2Up/s3Dn)·sqrt72Up (route-A δ-caliber
  envelope), `deltaA` = (l₃/24)/sqrt72Up (route-A narrow domain);
* `rhoNeedB`/`rhoNeedA` — the seam corollary composite thresholds
  min(gMin/2, ball-gate threshold), with the six domain-face `norm_num`
  theorems.

Honest scope note (B5Chain-data boundary, D92): the identification /
conversion / assembly theorems live in `TableB5Chain.lean`; this file
is the data layer only.  The half_gap cross-check (tube.json
float_advisory decimal anchor 0.01850609934999997) is a gate-face duty,
recorded in `r21_b5chain_data.json` (directed wide-margin assertion
0 ≤ 2·half_gap − gMin ≤ 1e-5).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5ChainData

open ThomsonN9.TableB1Data
open ThomsonN9.TableB5Data

/-! ### 15 对 ν 容器间隙（node 指标 0 基：ν_(a+1)；间隙＝容器 b 下端−容器 a 上端） -/
/-- g01：ν_1–ν_2 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g01 : ℚ := 48044537801371665285885750845552709377952126711517044301494649103634118726358250183201341430927204611752306319609576349237/1298074214633706907132624082305024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g02：ν_1–ν_3 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g02 : ℚ := 30945064856350658642194375951527242099350870124512289674385202473648470711253821718855761/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g03：ν_1–ν_4 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g03 : ℚ := 12407870195007325754665838957180312718264758599583/16384000000000000000000000000000000000000000000000
/-- g04：ν_1–ν_5 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g04 : ℚ := 30945064856350658642194375951527242099350870124512289674385202473648470711253821718855761/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g05：ν_1–ν_6 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g05 : ℚ := 2863121581657908355428795578029609186202026668937507871926494308526160353289460316391392277954474629608065138056547033557849/2596148429267413814265248164610048000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g12：ν_2–ν_3 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g12 : ℚ := 338336944892217936901600415587010115338144704246587833785505/1606938044258990275541962092341162602522202993782792835301376
/-- g13：ν_2–ν_4 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g13 : ℚ := 935007237728569006393771191764681186202026668937508599216267325186317110600948316391392277691952113117050255440339154119513/1298074214633706907132624082305024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g14：ν_2–ν_5 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g14 : ℚ := 1237362185788920038461741117152073186202026669272892459753998972906415121622260316391392278041982135105070098928616326703961/1298074214633706907132624082305024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g15：ν_2–ν_6 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g15 : ℚ := 3425417901065139224017744385272774249797738603413952754308579/3213876088517980551083924184682325205044405987565585670602752
/-- g23：ν_3–ν_4 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g23 : ℚ := 63719472153898103524140454959577438673543101124747659056083547526351529288746178281144239/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g24：ν_3–ν_5 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g24 : ℚ := 92835194569051975926583127854581726298052610373536869023155607420945412133761465156567283/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g25：ν_3–ν_6 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g25 : ℚ := 2748744011280703350214543554098754019121449194920777086737569/3213876088517980551083924184682325205044405987565585670602752
/-- g34：ν_4–ν_5 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g34 : ℚ := 29115453994454610495360631660690694695456090871586027720696417315539294978776752031990327/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g35：ν_4–ν_6 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g35 : ℚ := 897010494246219896422213306594537186202026670949815398891522294807688963286260316391392278479519662590094903288962792434521/2596148429267413814265248164610048000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- g45：ν_5–ν_6 容器间隙下界＝容器 b 下端−容器 a 上端（精确 ℚ）。 -/
def g45 : ℚ := 292301991845471375608140661212217186202026669272893550688658497896650257589492316391392277648198360368547775004304507546457/2596148429267413814265248164610048000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

/-! ### 端点恒等（ℚ norm_num，逐位） -/
/-- g01 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g01_eq : g01 = nu2Lo - nu1Hi := by norm_num [g01, nu2Lo, nu1Hi]
/-- g02 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g02_eq : g02 = nu3Lo - nu1Hi := by norm_num [g02, nu3Lo, nu1Hi]
/-- g03 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g03_eq : g03 = nu4Lo - nu1Hi := by norm_num [g03, nu4Lo, nu1Hi]
/-- g04 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g04_eq : g04 = nu5Lo - nu1Hi := by norm_num [g04, nu5Lo, nu1Hi]
/-- g05 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g05_eq : g05 = nu6Lo - nu1Hi := by norm_num [g05, nu6Lo, nu1Hi]
/-- g12 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g12_eq : g12 = nu3Lo - nu2Hi := by norm_num [g12, nu3Lo, nu2Hi]
/-- g13 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g13_eq : g13 = nu4Lo - nu2Hi := by norm_num [g13, nu4Lo, nu2Hi]
/-- g14 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g14_eq : g14 = nu5Lo - nu2Hi := by norm_num [g14, nu5Lo, nu2Hi]
/-- g15 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g15_eq : g15 = nu6Lo - nu2Hi := by norm_num [g15, nu6Lo, nu2Hi]
/-- g23 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g23_eq : g23 = nu4Lo - nu3Hi := by norm_num [g23, nu4Lo, nu3Hi]
/-- g24 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g24_eq : g24 = nu5Lo - nu3Hi := by norm_num [g24, nu5Lo, nu3Hi]
/-- g25 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g25_eq : g25 = nu6Lo - nu3Hi := by norm_num [g25, nu6Lo, nu3Hi]
/-- g34 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g34_eq : g34 = nu5Lo - nu4Hi := by norm_num [g34, nu5Lo, nu4Hi]
/-- g35 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g35_eq : g35 = nu6Lo - nu4Hi := by norm_num [g35, nu6Lo, nu4Hi]
/-- g45 端点恒等（自 TableB1Data 容器端点导出，norm_num 逐位）。 -/
theorem g45_eq : g45 = nu6Lo - nu5Hi := by norm_num [g45, nu6Lo, nu5Hi]

/-! ### 辨识窗常数 gMin（15 对间隙之 min） -/
/-- gMin：15 对容器间隙下界之 min（精确 ℚ；辨识窗＝gMin/2）。 -/
def gMin : ℚ := 48044537801371665285885750845552709377952126711517044301494649103634118726358250183201341430927204611752306319609576349237/1298074214633706907132624082305024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- gMin 的 min 树恒等（15 项嵌套 min，norm_num 逐位）。 -/
theorem gMin_eq : gMin = min (min (min (min (min (min (min (min (min (min (min (min (min (min (g01) (g02)) (g03)) (g04)) (g05)) (g12)) (g13)) (g14)) (g15)) (g23)) (g24)) (g25)) (g34)) (g35)) (g45) := by norm_num [gMin, g01, g02, g03, g04, g05, g12, g13, g14, g15, g23, g24, g25, g34, g35, g45]
/-- gMin > 0（间隙非退化）。 -/
theorem gMin_pos : (0:ℚ) < gMin := by norm_num [gMin]

/-! ### L6 球半径 r_ball（== r* == 950125/10⁸） -/
/-- r_ball：L6 认证球半径＝r*＝950125/10⁸（l6_intube rigorousRadius 精确
十进制；== R_MAX/16，R21A G3 箱定律口径）。 -/
def r_ball : ℚ := 950125/100000000
/-- r_ball > 0。 -/
theorem r_ball_pos : (0:ℚ) < r_ball := by norm_num [r_ball]

/-! ### 平方根上包三件（200-bit Newton；r20 sqrt_rat 同配方逐位） -/
/-- √2 的 200-bit 有理上包。 -/
def sqrt2Up : ℚ := 2272553576084360916141657902949647315979581976043234410928603/1606938044258990275541962092341162602522202993782792835301376
/-- sqrt2Up² ≥ 2。 -/
theorem sqrt2Up_sq_ge : (2:ℚ) ≤ sqrt2Up^2 := by norm_num [sqrt2Up]
/-- sqrt2Up > 0。 -/
theorem sqrt2Up_pos : (0:ℚ) < sqrt2Up := by norm_num [sqrt2Up]
/-- √deltaMax 的 200-bit 有理上包。 -/
def dmaxUp : ℚ := 664971267564157938699292041361674900694909796752905510121205/1606938044258990275541962092341162602522202993782792835301376
/-- dmaxUp² ≥ deltaMax。 -/
theorem dmaxUp_sq_ge : deltaMax ≤ dmaxUp^2 := by
  norm_num [dmaxUp, deltaMax]
/-- dmaxUp > 0。 -/
theorem dmaxUp_pos : (0:ℚ) < dmaxUp := by norm_num [dmaxUp]
/-- √(3·sqrt72Up) 的 200-bit 有理上包。 -/
def tUp : ℚ := 8107610645713198834809589852925925635447792414588437069465667/1606938044258990275541962092341162602522202993782792835301376
/-- tUp² ≥ 3·sqrt72Up。 -/
theorem tUp_sq_ge : 3*sqrt72Up ≤ tUp^2 := by
  norm_num [tUp, sqrt72Up]
/-- tUp > 0。 -/
theorem tUp_pos : (0:ℚ) < tUp := by norm_num [tUp]

/-! ### C_B／C_A 包络与窄域（精确 Fraction 装配） -/
/-- CBhi：路线 B 常数包＝k1·dmaxUp＋tUp（k1 := s1Up·u₁·sqrt72Up/l₃²）；
与 r20_l5l6_seam.json supply.C_B.hi 精确 Fraction 逐位一致（发射器
require 面＋门 G5 双查）。 -/
def CBhi : ℚ := 46347242438965846640112229167128343942631190184187663190501281085893507198932388708642817819347012690537632164611481084164204980342994379143731823861168077402391763388037580916132171862539581/6502194354682578821117604824908903918828518095641547146869918770254654340737338810094817122247099047970007885715545179831723344347746808557064090923034078262466642935713795520749412043194368
/-- CBhi 装配恒等。 -/
theorem CBhi_eq : CBhi = s1Up * u1
    * sqrt72Up / (l3 * l3)
    * dmaxUp + tUp := by
  norm_num [CBhi, s1Up, u1,
    sqrt72Up, l3, dmaxUp, tUp]
/-- CBhi > 0。 -/
theorem CBhi_pos : (0:ℚ) < CBhi := by norm_num [CBhi]
/-- CAhi：路线 A δ 口径常数包＝(s1Up·u₁/l₃²＋2·sqrt2Up/s3Dn)·sqrt72Up；
与 r20 supply.C_A.delta_caliber 精确 Fraction 逐位一致。 -/
def CAhi : ℚ := 212453437075530488528245355471358742621978584865472343432380988687917881559074064996822346271714912650477384809097834962459433597794588599230568156573548393163609318644746315352329378953712987/11207048342415202452402618008248517881778607328540524549783570256870678816731794756203665580127813239581190109664365318182994512618647881266258025646733998088218328010241689366407954405785600
/-- CAhi 装配恒等。 -/
theorem CAhi_eq : CAhi = (s1Up * u1
    / (l3 * l3)
    + 2 * sqrt2Up / s3Dn) * sqrt72Up := by
  norm_num [CAhi, s1Up, u1,
    sqrt72Up, s3Dn, sqrt2Up,
    l3]
/-- CAhi > 0。 -/
theorem CAhi_pos : (0:ℚ) < CAhi := by norm_num [CAhi]
/-- deltaA：路线 A 窄域半径＝(l₃/24)/sqrt72Up（精确 Fraction；与 r20
supply.C_A.delta_A 逐位一致）。 -/
def deltaA : ℚ := (l3 / 24) / sqrt72Up
/-- deltaA > 0。 -/
theorem deltaA_pos : (0:ℚ) < deltaA := by
  norm_num [deltaA, l3, sqrt72Up]

/-! ### 复合阈值（seam 推论 ρ_need） -/
/-- rhoNeedB：√δ 档复合阈值＝min(gMin/2, (r_ball/CBhi)²)（min 取球门支
——域面定理在库）。 -/
def rhoNeedB : ℚ := min (gMin/2) ((r_ball/CBhi)^2)
/-- rhoNeedA：窄域线性档复合阈值＝min(gMin/2, r_ball/CAhi)。 -/
def rhoNeedA : ℚ := min (gMin/2) (r_ball/CAhi)

/-! ### 域面六件（norm_num 精确） -/
/-- 球门阈值（B 档）＜辨识窗。 -/
theorem threshB_lt_gMin_half : (r_ball/CBhi)^2 < gMin/2 := by
  norm_num [r_ball, CBhi, gMin]
/-- 球门阈值（A 档）＜辨识窗。 -/
theorem threshA_lt_gMin_half : r_ball/CAhi < gMin/2 := by
  norm_num [r_ball, CAhi, gMin]
/-- 球门阈值（A 档）≤ 路线 A 窄域半径（δ_A 域检查）。 -/
theorem threshA_le_deltaA : r_ball/CAhi ≤ deltaA := by
  norm_num [r_ball, CAhi, deltaA, l3,
    sqrt72Up]
/-- 辨识窗半宽 ≤ deltaMax（路线 B 域检查：ρ<gMin/2 ⟹ ρ≤deltaMax）。 -/
theorem gMin_half_le_deltaMax : gMin/2 ≤ deltaMax := by
  norm_num [gMin, deltaMax]
/-- deltaA ≤ deltaMax（窄域 ⊆ 记录域）。 -/
theorem deltaA_le_deltaMax : deltaA ≤ deltaMax := by
  norm_num [deltaA, l3, sqrt72Up,
    deltaMax]
/-- 2·u₁·sqrt72Up·deltaMax ≤ l₃²（路线 A hdom1 内部导出的记录域端事实）。 -/
theorem two_u1_sqrt72Up_deltaMax_le_l3sq :
    2 * u1 * sqrt72Up
      * deltaMax ≤ l3 * l3 := by
  norm_num [u1, sqrt72Up,
    deltaMax, l3]

end ThomsonN9.TableB5ChainData
