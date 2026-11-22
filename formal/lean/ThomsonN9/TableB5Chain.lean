import Mathlib
import ThomsonN9.TableB1Data
import ThomsonN9.TableB1
import ThomsonN9.TableB5Data
import ThomsonN9.TableB5
import ThomsonN9.TableB5Core
import ThomsonN9.TableB5Trace
import ThomsonN9.TableB5Polar
import ThomsonN9.TableB5Uncond
import ThomsonN9.TableB5ChainData

/-!
# Table B5Chain (R21B / r21b): the chain-assembly / node-identification
# formal piece of the L2→L3→L5→L6 link

This file is the eighth Table B piece: the formal interface that consumes
the R20 seam (`notes/l5l6-seam.md` §3) — the Lean realization of the
『δ=ρ 簿记认同 → 逐对口径显式转换』 gap plus the L2→L3→L5→L6 chain
assembly conditional theorems.  Frozen pieces are imported read-only
(TableB1Data/TableB1 for the ν-node arithmetic layer, the TableB5 family
for the unconditional Procrustes body, TableB5ChainData for the emitted
rational constants).

Three theorem blocks (D90-1/D92-1):

* **(i) Node identification uniqueness** (`ident_unique`).  For `z` in the
  recorded z-box each node curve `ν_a(z)` lies in its rational container
  (`nu_container_idx`), so any two node values are ≥ the container gap
  `g_ab` apart (`nu_dist_ge_gap`, 15 exact-ℚ pairs); hence two hits
  `|t-ν_a(z)| ≤ ρ` and `|t-ν_b(z)| ≤ ρ` with `a ≠ b` force `gMin ≤ 2ρ`
  (`pair_gap_le_two_rho`), and `ρ < gMin/2` forces `a = b`.  The tube
  premise induces an identification map `identNode` (classical choice on
  the tube premise); `identNode_unique` is its well-definedness face —
  any hit-witness coincides with the chosen one (this consumes
  `ident_unique`); `pattern_ident_lift` upgrades σ-proximity into the
  identification form inside the window.
* **(ii) δ=ρ conversion** (`chain_convert`, `chain_convert_A`).  Under the
  tube premise `TubePremise` (per-pair distance ≤ ρ to the node set), the
  explicit pattern-consistency hypothesis `PatternCons` (the identification
  pattern is realized by the vertex relabeling σ₀ — the l4_orbit (P1)–(P4)
  insertion point, an explicit hypothesis, NOT derived here) and row-unit
  competitors, the σ₀-permuted competitor satisfies the L5 premise with
  δ := ρ: route B `d_P ≤ C_B·√ρ` (via `TableB5Core.eta_le_sqrt72` + the
  unconditional `step6_hoelder_Cform`) and route A `d_P ≤ coeff_A·η` on
  the narrow domain ρ ≤ δ_A (via `ttpX_step6_linear`).  The bridge
  `ttpX_gram_nodeOfN` ties the labeled TTP Gram entries to the node
  curves: `(ttpX z) i ⬝ᵥ (ttpX z) j = ν_{nodeOfN(i,j)}(z)`.
* **(iii) Chain assembly** (`chain_assemble_B`, `chain_assemble_A`).  (ii)
  + the ball gate `C_B·√ρ ≤ r_ball` (resp. `coeff_A·√72Up·ρ ≤ r_ball`,
  `r_ball = 950125/10⁸` exact ℚ) + the explicit L6 hypothesis interface
  `L6Hyp` (E/Ebar are variables — the L6 layer is interval_certified_numeric
  and is NOT formalized; the chord-distance caliber is carried by the
  ∃Q-frob ball predicate, B5c→B5Uncond precedent) give
  `E (rowPerm Y σ₀) ≥ Ebar`.
* **Seam corollary** (`seam_cor_B_pair`, `seam_cor_A_pair`) — the future
  L3-certificate feed contract: `E (rowPerm Y σ₀) < Ebar` implies some pair
  has distance > ρ_need to the node set, with
  `ρ_need = min(gMin/2, (r_ball/CBhi)²)` (route B) resp.
  `min(gMin/2, r_ball/CAhi)` (route A).  The R20 seam thresholds
  (`r20_l5l6_seam.json` r*-caliber rows, reproduced bit for bit by
  `CBhi`/`CAhi`) are load-bearing at the formal layer from this piece on.

Conditionality honesty (D92): `hL6`/`hpat`/`hunit` are explicit named
hypotheses — nothing here is claimed unconditional.  The tube premise
`hTube` is carried on the statement face as the L2 supply interface (its
formal role: activating `hpat` and being the negated face of the seam
corollary); `hρid` is the identification-window premise that makes
"identification" semantically meaningful (route B additionally uses it
for the δ_max domain face; route A's narrow domain is `hρA`).  The
orbit-offset trim (deltaOrbitArchive, r_eff caliber) is a numerics-layer
refinement and does not enter this file (r_ball = r* caliber).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5Chain

open Matrix
open ThomsonN9.TableB5Data
open ThomsonN9.TableB1 (nodeOfN nuOfN rowOfN gram_nodeOfN diag_norm_all)
open ThomsonN9.TableB1Data (dot3 rhoR s3R rowT0 rowT1 rowT2 rowB0 rowB1 rowB2
  rowC0 rowC1 rowC2 nu1Lo nu1Hi nu2Lo nu2Hi nu3Lo nu3Hi nu4Lo nu4Hi nu5Lo nu5Hi
  nu6Lo nu6Hi)
open ThomsonN9.TableB5Core (ttpX ttpRow rowDot frob)
open ThomsonN9.TableB5ChainData

/-! ### 置换/索引小件 -/

/-- 置换保持不等（Fin 9 顶点重排双射面）。 -/
theorem perm_ne {σ₀ : Equiv.Perm (Fin 9)} {i j : Fin 9} (hij : i ≠ j) :
    σ₀ i ≠ σ₀ j := fun h => hij (Equiv.injective σ₀ h)

/-- 置换逆保持不等。 -/
theorem symm_perm_ne {σ₀ : Equiv.Perm (Fin 9)} {i j : Fin 9} (hij : i ≠ j) :
    σ₀.symm i ≠ σ₀.symm j := perm_ne hij (σ₀ := σ₀.symm)

/-- Fin 值不等提升到点不等。 -/
theorem fin_ne_of_val_ne {i j : Fin 9} (h : i.val ≠ j.val) : i ≠ j :=
  fun hc => h (by rw [hc])

/-! ### nodeOfN 组合面（对称性＋合法域） -/

/-- nodeOfN 对称（i,j < 9；81 臂 decide）。 -/
theorem nodeOfN_sym (i j : ℕ) (hi : i < 9) (hj : j < 9) :
    nodeOfN i j = nodeOfN j i := by
  interval_cases i <;> interval_cases j <;> decide

/-- nodeOfN 合法域：i≠j（i,j<9）时分类值 < 6（哑值 9 仅对角）。 -/
theorem nodeOfN_lt6 (i j : ℕ) (hi : i < 9) (hj : j < 9) (hne : i ≠ j) :
    nodeOfN i j < 6 := by
  interval_cases i <;> interval_cases j <;>
    first | (exact absurd rfl hne) | decide

/-! ### 行桥（ttpX 行 ↔ rowOfN 三元组 ↔ 节点曲线） -/

/-- ttpX 第 k 行的三元组重构＝rowOfN k z（9 臂）。 -/
theorem ttpX_rowVec (z : ℝ) (k : ℕ) (hk : k < 9) :
    ((ttpX z) (Fin.mk k hk) 0, (ttpX z) (Fin.mk k hk) 1, (ttpX z) (Fin.mk k hk) 2)
      = rowOfN k z := by
  interval_cases k <;>
    simp [ttpX, ttpRow, rowOfN, rowT0, rowT1, rowT2, rowB0, rowB1, rowB2,
      rowC0, rowC1, rowC2, rhoR, s3R] <;> (try ring)

/-- ttpX 第 k 行对一般向量的点积＝dot3（rowOfN k z）（9 臂）。 -/
theorem ttpX_row_dot (z : ℝ) (k : ℕ) (hk : k < 9) (w : Fin 3 → ℝ) :
    (ttpX z) (Fin.mk k hk) ⬝ᵥ w = dot3 (rowOfN k z) (w 0, w 1, w 2) := by
  interval_cases k <;>
    simp [ttpX, ttpRow, rowOfN, rowT0, rowT1, rowT2, rowB0, rowB1, rowB2,
      rowC0, rowC1, rowC2, rhoR, s3R, dot3, rowDot, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- ttpX Gram 元＝dot3（rowOfN 行偶）。 -/
theorem ttpX_gram (z : ℝ) (k l : ℕ) (hk : k < 9) (hl : l < 9) :
    (ttpX z) (Fin.mk k hk) ⬝ᵥ (ttpX z) (Fin.mk l hl)
      = dot3 (rowOfN k z) (rowOfN l z) := by
  rw [ttpX_row_dot z k hk (ttpX z (Fin.mk l hl)), ttpX_rowVec z l hl]

/-- dot3 对称（Gram 对称面）。 -/
theorem dot3_sym (a b : ℝ × ℝ × ℝ) : dot3 a b = dot3 b a := by
  simp only [dot3]; ring

/-- **TTP Gram–节点桥**：z² ≤ 1 时 labeled 对 (i,j)（i≠j）的 TTP Gram 元
恰为该对分类所指节点曲线（gram_nodeOfN 经 dot3_sym/nodeOfN_sym 对称化到
全序对——B1 证书层与链装配层的形式链接）。 -/
theorem ttpX_gram_nodeOfN (z : ℝ) (hz : z^2 ≤ 1) : ∀ i j : Fin 9, i ≠ j →
    (ttpX z) i ⬝ᵥ (ttpX z) j = nuOfN (nodeOfN i.val j.val) z := by
  intro i j hij
  rw [ttpX_gram z i.val j.val i.isLt j.isLt]
  rcases lt_or_gt_of_ne hij with h | h
  · exact gram_nodeOfN z hz i.val j.val i.isLt j.isLt h
  · rw [dot3_sym, gram_nodeOfN z hz j.val i.val j.isLt i.isLt h,
      nodeOfN_sym j.val i.val j.isLt i.isLt]

/-- ttpX 行单位（diag_norm_all 桥）。 -/
theorem ttpX_diag_one (z : ℝ) (hz : z^2 ≤ 1) (i : Fin 9) :
    (ttpX z) i ⬝ᵥ (ttpX z) i = 1 := by
  rw [ttpX_gram z i.val i.val i.isLt i.isLt]
  exact diag_norm_all z hz i.val i.isLt

/-- z 盒 ⟹ z² ≤ 1（TableB5 同式）。 -/
theorem z_box_sq_le_one (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    z^2 ≤ 1 := by
  have hzLop : (0:ℝ) < (zLo:ℝ) := by norm_num [zLo]
  have hzh2 : ((zHi:ℝ))^2 < 1/2 := by norm_num [zHi]
  have hpos : (0:ℝ) < z := by nlinarith [h1, hzLop]
  nlinarith [hzh2, h2, hpos]

/-! ### (i) 节点辨识唯一性 -/

/-- ν 容器端点索引装配（下端；0 基 node 指标）。 -/
def nuLoIdx : ℕ → ℚ
  | 0 => nu1Lo | 1 => nu2Lo | 2 => nu3Lo | 3 => nu4Lo | 4 => nu5Lo | _ => nu6Lo
/-- ν 容器端点索引装配（上端）。 -/
def nuHiIdx : ℕ → ℚ
  | 0 => nu1Hi | 1 => nu2Hi | 2 => nu3Hi | 3 => nu4Hi | 4 => nu5Hi | _ => nu6Hi

/-- **ν 容器包含（索引面）**：z 盒内 ν_a(z) 落入容器_a（六臂——
TableB1.nu_containers 的 z²/ρ 包络口径）。 -/
theorem nu_container_idx (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (a : ℕ) (ha : a < 6) :
    (nuLoIdx a : ℝ) ≤ nuOfN a z ∧ nuOfN a z ≤ (nuHiIdx a : ℝ) := by
  obtain ⟨h1lo, h1hi, h2lo, h2hi, h3lo, h3hi, h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ :=
    TableB1.nu_containers z h1 h2
  interval_cases a
  · simp only [nuLoIdx, nuHiIdx, nuOfN]; exact ⟨h1lo, h1hi⟩
  · simp only [nuLoIdx, nuHiIdx, nuOfN]; exact ⟨h2lo, h2hi⟩
  · simp only [nuLoIdx, nuHiIdx, nuOfN]; exact ⟨h3lo, h3hi⟩
  · simp only [nuLoIdx, nuHiIdx, nuOfN]; exact ⟨h4lo, h4hi⟩
  · simp only [nuLoIdx, nuHiIdx, nuOfN]; exact ⟨h5lo, h5hi⟩
  · simp only [nuLoIdx, nuHiIdx, nuOfN]; exact ⟨h6lo, h6hi⟩

/-- 15 对容器间隙函数（精确 ℚ 字面 def 的配对索引；非法臂哑值 0）。 -/
def gPair : ℕ → ℕ → ℚ
  | 0, 1 => g01 | 0, 2 => g02 | 0, 3 => g03 | 0, 4 => g04 | 0, 5 => g05
  | 1, 2 => g12 | 1, 3 => g13 | 1, 4 => g14 | 1, 5 => g15
  | 2, 3 => g23 | 2, 4 => g24 | 2, 5 => g25
  | 3, 4 => g34 | 3, 5 => g35
  | 4, 5 => g45
  | _, _ => 0

/-- gPair 值面＝容器 b 下端-容器 a 上端（15 臂 push_cast；其余臂由
a<b 排除）。 -/
theorem gPair_val (a b : ℕ) (ha : a < 6) (hb : b < 6) (hab : a < b) :
    (gPair a b : ℝ) = (nuLoIdx b : ℝ) - (nuHiIdx a : ℝ) := by
  interval_cases a <;> interval_cases b <;> first
    | (exact absurd hab (by omega))
    | (simp only [gPair, nuLoIdx, nuHiIdx];
        push_cast [g01_eq, g02_eq, g03_eq, g04_eq, g05_eq, g12_eq, g13_eq,
          g14_eq, g15_eq, g23_eq, g24_eq, g25_eq, g34_eq, g35_eq, g45_eq];
        ring)

/-- **节点距离 ≥ 容器间隙**：z 盒内 a<b 时 |ν_a(z)-ν_b(z)| ≥ g_ab
（node_chain 序＋容器包含）。 -/
theorem nu_dist_ge_gap (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (a b : ℕ) (ha : a < 6) (hb : b < 6) (hab : a < b) :
    (gPair a b : ℝ) ≤ nuOfN b z - nuOfN a z := by
  obtain ⟨clo, chi⟩ := nu_container_idx z h1 h2 b hb
  obtain ⟨alo, ahi⟩ := nu_container_idx z h1 h2 a ha
  have hg := gPair_val a b ha hb hab
  linarith

/-- gMin ≤ 每对间隙（15 臂 norm_num 字面比较）。 -/
theorem gMin_le_gPair (a b : ℕ) (ha : a < 6) (hb : b < 6) (hab : a < b) :
    gMin ≤ gPair a b := by
  interval_cases a <;> interval_cases b <;> first
    | (exact absurd hab (by omega))
    | (simp only [gPair]; norm_num [gMin, g01, g02, g03, g04, g05, g12, g13,
        g14, g15, g23, g24, g25, g34, g35, g45])

/-- **双命中 ⟹ gMin ≤ 2ρ**（任务书 (i) 的 g_ab 面：|t-ν_a|≤ρ ∧
|t-ν_b|≤ρ ∧ a<b ⟹ gMin ≤ g_ab ≤ ν_b-ν_a ≤ 2ρ）。 -/
theorem pair_gap_le_two_rho (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (t ρ : ℝ) (a b : ℕ) (ha : a < 6) (hb : b < 6) (hab : a < b)
    (hA : |t - nuOfN a z| ≤ ρ) (hB : |t - nuOfN b z| ≤ ρ) :
    (gMin:ℝ) ≤ 2 * ρ := by
  rw [abs_le] at hA hB
  have hgap := nu_dist_ge_gap z h1 h2 a b ha hb hab
  have hmin := gMin_le_gPair a b ha hb hab
  have hc : ((gPair a b : ℚ) : ℝ) ≥ (gMin:ℝ) := by exact_mod_cast hmin
  linarith

/-- **(i) 节点辨识唯一性**：z 盒内 t 同时落入两个不同节点曲线的 ρ-窗
（ρ < gMin/2）不可能——被命中的 node 指标唯一（a = b）。 -/
theorem ident_unique (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (t ρ : ℝ) (hρ : ρ < (gMin:ℝ)/2) (a b : ℕ) (ha : a < 6) (hb : b < 6)
    (hA : |t - nuOfN a z| ≤ ρ) (hB : |t - nuOfN b z| ≤ ρ) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · linarith [pair_gap_le_two_rho z h1 h2 t ρ a b ha hb h hA hB, hρ]
  · linarith [pair_gap_le_two_rho z h1 h2 t ρ b a hb ha h hB hA, hρ]

/-! ### 接口形（L2 管前提／pattern-consistency／L6 显式假设） -/

/-- **L2 管前提形**（节点集 ρ-命中；72 个有序对全称——由 i<j 口径经点积
对称等价）。 -/
def TubePremise (Y : Matrix (Fin 9) (Fin 3) ℝ) (z ρ : ℝ) : Prop :=
  ∀ i j : Fin 9, i ≠ j → ∃ a : ℕ, a < 6 ∧ |Y i ⬝ᵥ Y j - nuOfN a z| ≤ ρ

/-- **辨识映射**：管前提给出的逐对 node 指标（Classical.choose；
well-definedness＝identNode_unique——恰为定理 (i) 的消费面）。 -/
noncomputable def identNode {Y : Matrix (Fin 9) (Fin 3) ℝ} {z ρ : ℝ}
    (hT : TubePremise Y z ρ) (i j : Fin 9) (hij : i ≠ j) : ℕ :=
  Classical.choose (hT i j hij)

/-- identNode 满足管前提逐对命中（choose_spec）。 -/
theorem identNode_spec {Y : Matrix (Fin 9) (Fin 3) ℝ} {z ρ : ℝ}
    (hT : TubePremise Y z ρ) (i j : Fin 9) (hij : i ≠ j) :
    identNode hT i j hij < 6 ∧ |Y i ⬝ᵥ Y j - nuOfN (identNode hT i j hij) z| ≤ ρ :=
  Classical.choose_spec (hT i j hij)

/-- **辨识映射 well-definedness**：任何命中 witness ＝ identNode
（定理 (i) 的直接消费——映射与 witness 选取无关）。 -/
theorem identNode_unique {Y : Matrix (Fin 9) (Fin 3) ℝ} {z ρ : ℝ}
    (hT : TubePremise Y z ρ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (hρ : ρ < (gMin:ℝ)/2) (i j : Fin 9) (hij : i ≠ j) (a : ℕ) (ha : a < 6)
    (hHit : |Y i ⬝ᵥ Y j - nuOfN a z| ≤ ρ) : a = identNode hT i j hij :=
  ident_unique z h1 h2 (Y i ⬝ᵥ Y j) ρ hρ a (identNode hT i j hij) ha
    (identNode_spec hT i j hij).1 hHit (identNode_spec hT i j hij).2

/-- **pattern-consistency 形**（显式 hypothesis；l4_orbit (P1)–(P4) 插入
点）：σ₀-重排逐对近邻——管前提条件化（对 hT 全称量化），σ₀ 显式。
D92 裁决 2：条件形不蕴含管前提（非条件形经 σ-pullback 蕴含之——
`hTube_of_hpat` 在库），保证 seam 推论非空。 -/
def PatternCons (Y : Matrix (Fin 9) (Fin 3) ℝ) (z ρ : ℝ)
    (σ₀ : Equiv.Perm (Fin 9)) : Prop :=
  ∀ (hT : TubePremise Y z ρ), ∀ i j : Fin 9, i ≠ j →
    |Y (σ₀ i) ⬝ᵥ Y (σ₀ j) - nuOfN (nodeOfN i.val j.val) z| ≤ ρ

/-- σ-pullback：σ-近邻形（非条件）蕴含管前提（层间关系透明化引理——
D92 裁决 2①；witness＝nodeOfN(σ₀⁻¹i, σ₀⁻¹j)）。 -/
theorem hTube_of_hpat {Y : Matrix (Fin 9) (Fin 3) ℝ} {z ρ : ℝ}
    (σ₀ : Equiv.Perm (Fin 9))
    (hpat : ∀ i j : Fin 9, i ≠ j →
      |Y (σ₀ i) ⬝ᵥ Y (σ₀ j) - nuOfN (nodeOfN i.val j.val) z| ≤ ρ) :
    TubePremise Y z ρ := by
  intro i j hij
  have hne : σ₀.symm i ≠ σ₀.symm j := symm_perm_ne hij
  have h := hpat (σ₀.symm i) (σ₀.symm j) hne
  simp only [Equiv.apply_symm_apply] at h
  refine ⟨nodeOfN (σ₀.symm i).val (σ₀.symm j).val,
    nodeOfN_lt6 (σ₀.symm i).val (σ₀.symm j).val (σ₀.symm i).isLt
      (σ₀.symm j).isLt (fun hc => hij (by
        have he : σ₀.symm i = σ₀.symm j := Fin.val_injective hc
        calc i = σ₀ (σ₀.symm i) := (Equiv.apply_symm_apply σ₀ i).symm
          _ = σ₀ (σ₀.symm j) := by rw [he]
          _ = j := Equiv.apply_symm_apply σ₀ j)),
    h⟩

/-- **辨识升级桥**：辨识窗内 σ-近邻形 ⟹ identNode 辨识形（proximity →
identification 的形式升级——定理 (i) 经 identNode_unique 的链内消费；
(P1)–(P4)/未来 L3 供给的接口文档）。 -/
theorem pattern_ident_lift {Y : Matrix (Fin 9) (Fin 3) ℝ} {z ρ : ℝ}
    (hT : TubePremise Y z ρ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (hρ : ρ < (gMin:ℝ)/2) (σ : Equiv.Perm (Fin 9))
    (hpat : ∀ i j : Fin 9, i ≠ j →
      |Y (σ i) ⬝ᵥ Y (σ j) - nuOfN (nodeOfN i.val j.val) z| ≤ ρ)
    (i j : Fin 9) (hij : i ≠ j) :
    identNode hT (σ i) (σ j) (perm_ne hij) = nodeOfN i.val j.val := by
  symm
  exact identNode_unique hT h1 h2 hρ (σ i) (σ j) (perm_ne hij)
    (nodeOfN i.val j.val)
    (nodeOfN_lt6 i.val j.val i.isLt j.isLt
      (fun h => hij (Fin.val_injective h)))
    (hpat i j hij)

/-! ### (ii) δ=ρ 转换（σ₀-重排 L5 前提） -/

/-- σ₀-重排矩阵（行置换：rowPerm Y σ₀ i = Y (σ₀ i)）。 -/
noncomputable def rowPerm (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (σ₀ : Equiv.Perm (Fin 9)) : Matrix (Fin 9) (Fin 3) ℝ :=
  Matrix.of fun i j => Y (σ₀ i) j

/-- rowPerm 行点积面。 -/
theorem rowPerm_dot (Y : Matrix (Fin 9) (Fin 3) ℝ) (σ₀ : Equiv.Perm (Fin 9))
    (i j : Fin 9) :
    rowPerm Y σ₀ i ⬝ᵥ rowPerm Y σ₀ j = Y (σ₀ i) ⬝ᵥ Y (σ₀ j) := rfl

/-- rowPerm 行单位。 -/
theorem rowPerm_unit {Y : Matrix (Fin 9) (Fin 3) ℝ}
    (hunit : ∀ i : Fin 9, Y i ⬝ᵥ Y i = 1) (σ₀ : Equiv.Perm (Fin 9)) (i : Fin 9) :
    rowPerm Y σ₀ i ⬝ᵥ rowPerm Y σ₀ i = 1 := by
  rw [rowPerm_dot]; exact hunit (σ₀ i)

/-- **(ii) δ=ρ 转换·路线 B**：管前提＋pattern-consistency（σ₀ 显式、
管前提条件化）＋行单位＋辨识窗 ⟹ σ₀-重排竞争者的 L5 前提以 δ:=ρ 成立
（∃Q ∈ orthogonalGroup, frob (ttpX z - rowPerm Y σ₀*Q) ≤ C_B·√ρ）——
eta_le_sqrt72（√72 精确面）＋step6_hoelder_Cform（无条件头条）。hTube
作为 hpat 激活实参消费；hρid 供 δ_max 域面（gMin/2 ≤ deltaMax 在库）。 -/
theorem chain_convert (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hunit : ∀ i : Fin 9, Y i ⬝ᵥ Y i = 1)
    (hTube : TubePremise Y z ρ) (σ₀ : Equiv.Perm (Fin 9))
    (hpat : PatternCons Y z ρ σ₀) (hρid : ρ < (gMin:ℝ)/2) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      frob ((ttpX z) - rowPerm Y σ₀ * Q)
        ≤ ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2
            * Real.sqrt (deltaMax:ℝ) + Real.sqrt (3 * (sqrt72Up:ℝ)))
          * Real.sqrt ρ := by
  have hz1 := z_box_sq_le_one z h1 h2
  have hgram : ∀ i j : Fin 9, i ≠ j →
      |rowPerm Y σ₀ i ⬝ᵥ rowPerm Y σ₀ j - (ttpX z) i ⬝ᵥ (ttpX z) j| ≤ ρ := by
    intro i j hij
    rw [rowPerm_dot, ttpX_gram_nodeOfN z hz1 i j hij]
    exact hpat hTube i j hij
  have heta := TableB5Core.eta_le_sqrt72 (ttpX z) (rowPerm Y σ₀) ρ (ttpX_diag_one z hz1)
    (rowPerm_unit hunit σ₀) hgram hρ0
  have hdm : ρ ≤ (deltaMax:ℝ) := by
    have hc : (gMin:ℝ)/2 ≤ (deltaMax:ℝ) := by
      exact_mod_cast gMin_half_le_deltaMax
    linarith
  exact TableB5Uncond.step6_hoelder_Cform (ttpX z) (rowPerm Y σ₀)
    (by norm_num [l3] : (0:ℝ) < (l3:ℝ)) (le_refl _) (le_refl _)
    (by norm_num [l3, u1] : (l3:ℝ) ≤ (u1:ℝ)) (TableB5Trace.ttpX_quadform_lo z h1 h2)
    (TableB5Trace.ttpX_quadform_hi z h1 h2) hρ0 heta hdm

/-- **(ii) δ=ρ 转换·路线 A（窄域线性档）**：另带窄域前提 hρA : ρ ≤ δ_A
（heta24 域）；结论为 η 口径系数形（ttpX_step6_linear 头条）。 -/
theorem chain_convert_A (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hunit : ∀ i : Fin 9, Y i ⬝ᵥ Y i = 1)
    (hTube : TubePremise Y z ρ) (σ₀ : Equiv.Perm (Fin 9))
    (hpat : PatternCons Y z ρ σ₀) (hρid : ρ < (gMin:ℝ)/2)
    (hρA : ρ ≤ (deltaA:ℝ)) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      frob ((ttpX z) - rowPerm Y σ₀ * Q)
        ≤ (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
            + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ))
          * frob (rowPerm Y σ₀ * (rowPerm Y σ₀)ᵀ - (ttpX z) * (ttpX z)ᵀ) := by
  have hz1 := z_box_sq_le_one z h1 h2
  have hgram : ∀ i j : Fin 9, i ≠ j →
      |rowPerm Y σ₀ i ⬝ᵥ rowPerm Y σ₀ j - (ttpX z) i ⬝ᵥ (ttpX z) j| ≤ ρ := by
    intro i j hij
    rw [rowPerm_dot, ttpX_gram_nodeOfN z hz1 i j hij]
    exact hpat hTube i j hij
  have heta := TableB5Core.eta_le_sqrt72 (ttpX z) (rowPerm Y σ₀) ρ (ttpX_diag_one z hz1)
    (rowPerm_unit hunit σ₀) hgram hρ0
  -- h72: η ≤ √72Up·ρ（√72 精确 → 上包）
  have h72 : frob (rowPerm Y σ₀ * (rowPerm Y σ₀)ᵀ - (ttpX z) * (ttpX z)ᵀ)
      ≤ (sqrt72Up:ℝ) * ρ := by
    have hs : Real.sqrt 72 ≤ (sqrt72Up:ℝ) := TableB5.sqrt72_le_sqrt72Up
    have h2 : Real.sqrt 72 * ρ ≤ (sqrt72Up:ℝ) * ρ :=
      mul_le_mul_of_nonneg_right hs hρ0
    linarith [heta, h2]
  -- hdm: ρ ≤ deltaMax（δ_A ≤ deltaMax 域链）
  have hdm : ρ ≤ (deltaMax:ℝ) := by
    have hc : (deltaA:ℝ) ≤ (deltaMax:ℝ) := by
      exact_mod_cast deltaA_le_deltaMax
    linarith
  -- hdom1: β := u₁η/l₃² ≤ 1/2（记录域端事实 2·u₁·sqrt72Up·deltaMax ≤ l₃²）
  have h2c : 2 * (u1:ℝ) * (sqrt72Up:ℝ) * (deltaMax:ℝ) ≤ (l3:ℝ)^2 := by
    have h5 : 2 * (u1:ℝ) * (sqrt72Up:ℝ) * (deltaMax:ℝ) ≤ (l3:ℝ) * (l3:ℝ) := by
      exact_mod_cast two_u1_sqrt72Up_deltaMax_le_l3sq
    linarith [h5, show (l3:ℝ) * (l3:ℝ) = (l3:ℝ)^2 from by ring]
  have hU : (u1:ℝ) * ((sqrt72Up:ℝ) * (deltaMax:ℝ)) * 2 ≤ (l3:ℝ)^2 := by
    have hx : (u1:ℝ) * ((sqrt72Up:ℝ) * (deltaMax:ℝ)) * 2
        = 2 * (u1:ℝ) * (sqrt72Up:ℝ) * (deltaMax:ℝ) := by ring
    rw [hx]; exact h2c
  have hdom1 : (u1:ℝ) * frob (rowPerm Y σ₀ * (rowPerm Y σ₀)ᵀ
      - (ttpX z) * (ttpX z)ᵀ) / (l3:ℝ)^2 ≤ 1 / 2 := by
    have hl3 : (0:ℝ) < (l3:ℝ) := by norm_num [l3]
    have hl3p : (0:ℝ) < (l3:ℝ)^2 := pow_pos hl3 2
    have hUp : (u1:ℝ) * ((sqrt72Up:ℝ) * (deltaMax:ℝ)) ≤ (l3:ℝ)^2 / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith [hU]
    rw [div_le_div_iff₀ hl3p (by norm_num : (0:ℝ) < 2)]
    have e1 : (u1:ℝ) * frob (rowPerm Y σ₀ * (rowPerm Y σ₀)ᵀ
        - (ttpX z) * (ttpX z)ᵀ) ≤ (u1:ℝ) * ((sqrt72Up:ℝ) * (deltaMax:ℝ)) := by
      refine mul_le_mul_of_nonneg_left (le_trans h72 ?_) (by norm_num [u1])
      exact mul_le_mul_of_nonneg_left hdm (by norm_num [sqrt72Up])
    linarith [e1, hUp]
  -- heta24: η ≤ l₃/24（窄域：ρ ≤ δ_A ⟹ √72Up·ρ ≤ √72Up·δ_A = l₃/24）
  have hsdA : (sqrt72Up:ℝ) * (deltaA:ℝ) = (l3:ℝ) / 24 := by
    have hne : (sqrt72Up:ℝ) ≠ 0 := by
      have : (0:ℚ) < sqrt72Up := by norm_num [sqrt72Up]
      exact_mod_cast ne_of_gt this
    push_cast [deltaA]
    field_simp <;> ring
  have heta24 : frob (rowPerm Y σ₀ * (rowPerm Y σ₀)ᵀ - (ttpX z) * (ttpX z)ᵀ)
      ≤ (l3:ℝ) / 24 := by
    have e1 : frob (rowPerm Y σ₀ * (rowPerm Y σ₀)ᵀ - (ttpX z) * (ttpX z)ᵀ)
        ≤ (sqrt72Up:ℝ) * (deltaA:ℝ) := by
      have e2 : (sqrt72Up:ℝ) * ρ ≤ (sqrt72Up:ℝ) * (deltaA:ℝ) :=
        mul_le_mul_of_nonneg_left hρA (by norm_num [sqrt72Up])
      linarith [h72, e2]
    linarith [e1, hsdA]
  exact TableB5Uncond.ttpX_step6_linear z h1 h2 (rowPerm Y σ₀) hdom1 heta24

/-! ### (iii) 链装配条件定理（L6 显式假设接口） -/

/-- **L6 显式假设接口**（E/Ebar 变量级；弦距口径以 d_P 球 ∃Q frob 形承载——
L6 系 interval_certified_numeric 层不形式化，B5c→B5Uncond 先例）。
r_ball 口径＝r*（轨道偏移 r_eff trim 系数值层细化不入 Lean，D92）。 -/
def L6Hyp (z r : ℝ) (E : Matrix (Fin 9) (Fin 3) ℝ → ℝ) (Ebar : ℝ) : Prop :=
  ∀ Y' : Matrix (Fin 9) (Fin 3) ℝ, (∃ Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
    frob ((ttpX z) - Y' * Q) ≤ r) → E Y' ≥ Ebar

/-- **(iii) 链装配·路线 B**：chain_convert＋球门（C_B·√ρ ≤ r_ball）＋
L6 假设 ⟹ E (rowPerm Y σ₀) ≥ Ē。 -/
theorem chain_assemble_B (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hunit : ∀ i : Fin 9, Y i ⬝ᵥ Y i = 1)
    (hTube : TubePremise Y z ρ) (σ₀ : Equiv.Perm (Fin 9))
    (hpat : PatternCons Y z ρ σ₀) (hρid : ρ < (gMin:ℝ)/2)
    (E : Matrix (Fin 9) (Fin 3) ℝ → ℝ) (Ebar : ℝ)
    (hL6 : L6Hyp z (r_ball:ℝ) E Ebar)
    (hBall : ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2
        * Real.sqrt (deltaMax:ℝ) + Real.sqrt (3 * (sqrt72Up:ℝ)))
      * Real.sqrt ρ ≤ (r_ball:ℝ)) :
    E (rowPerm Y σ₀) ≥ Ebar := by
  obtain ⟨Q, hQmem, hQle⟩ :=
    chain_convert z h1 h2 ρ hρ0 Y hunit hTube σ₀ hpat hρid
  refine hL6 (rowPerm Y σ₀) ⟨Q, hQmem, ?_⟩
  linarith [hQle, hBall]

/-- **(iii) 链装配·路线 A（窄域）**：chain_convert_A＋球门
（coeff_A·√72Up·ρ ≤ r_ball）＋L6 假设 ⟹ E (rowPerm Y σ₀) ≥ Ē。 -/
theorem chain_assemble_A (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hunit : ∀ i : Fin 9, Y i ⬝ᵥ Y i = 1)
    (hTube : TubePremise Y z ρ) (σ₀ : Equiv.Perm (Fin 9))
    (hpat : PatternCons Y z ρ σ₀) (hρid : ρ < (gMin:ℝ)/2)
    (hρA : ρ ≤ (deltaA:ℝ))
    (E : Matrix (Fin 9) (Fin 3) ℝ → ℝ) (Ebar : ℝ)
    (hL6 : L6Hyp z (r_ball:ℝ) E Ebar)
    (hBall : ((Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
        + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * (sqrt72Up:ℝ)) * ρ
      ≤ (r_ball:ℝ)) :
    E (rowPerm Y σ₀) ≥ Ebar := by
  obtain ⟨Q, hQmem, hQle⟩ :=
    chain_convert_A z h1 h2 ρ hρ0 Y hunit hTube σ₀ hpat hρid hρA
  refine hL6 (rowPerm Y σ₀) ⟨Q, hQmem, ?_⟩
  have hnn : (0:ℝ) ≤ (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) := by
    refine add_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (by norm_num [u1])) (by positivity))
      (div_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hz1 := z_box_sq_le_one z h1 h2
  have hgram : ∀ i j : Fin 9, i ≠ j →
      |rowPerm Y σ₀ i ⬝ᵥ rowPerm Y σ₀ j - (ttpX z) i ⬝ᵥ (ttpX z) j| ≤ ρ := by
    intro i j hij
    rw [rowPerm_dot, ttpX_gram_nodeOfN z hz1 i j hij]
    exact hpat hTube i j hij
  have heta := TableB5Core.eta_le_sqrt72 (ttpX z) (rowPerm Y σ₀) ρ (ttpX_diag_one z hz1)
    (rowPerm_unit hunit σ₀) hgram hρ0
  have hs : Real.sqrt 72 ≤ (sqrt72Up:ℝ) := TableB5.sqrt72_le_sqrt72Up
  have h72 : Real.sqrt 72 * ρ ≤ (sqrt72Up:ℝ) * ρ :=
    mul_le_mul_of_nonneg_right hs hρ0
  have e1 : (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ))
      * frob (rowPerm Y σ₀ * (rowPerm Y σ₀)ᵀ - (ttpX z) * (ttpX z)ᵀ)
      ≤ (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
        + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * ((sqrt72Up:ℝ) * ρ) :=
    mul_le_mul_of_nonneg_left (by linarith [heta, h72]) hnn
  have hrw : (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * ((sqrt72Up:ℝ) * ρ)
      = ((Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
          + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * (sqrt72Up:ℝ)) * ρ := by ring
  rw [hrw] at e1
  linarith [e1, hBall]

/-! ### 包络引理（C_B ≤ CBhi／coeff_A·√72Up ≤ CAhi） -/

/-- 路线 B 真常数 ≤ CBhi 包络（dmaxUp/tUp 上包；D92 裁决 3）。 -/
theorem CB_le_CBhi :
    (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * Real.sqrt (deltaMax:ℝ)
      + Real.sqrt (3 * (sqrt72Up:ℝ)) ≤ (CBhi:ℝ) := by
  have hsup : (0:ℝ) ≤ (s1Up:ℝ) := by norm_num [s1Up]
  have hu1n : (0:ℝ) ≤ (u1:ℝ) := by norm_num [u1]
  have hs72n : (0:ℝ) ≤ (sqrt72Up:ℝ) := by norm_num [sqrt72Up]
  have hk1nn : (0:ℝ) ≤ (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 :=
    div_nonneg (mul_nonneg (mul_nonneg hsup hu1n) hs72n) (by positivity)
  have hdnn : (0:ℝ) ≤ deltaMax := by
    have : (0:ℚ) ≤ deltaMax := by norm_num [deltaMax]
    exact_mod_cast this
  have hd : Real.sqrt (deltaMax:ℝ) ≤ (dmaxUp:ℝ) := by
    have e : (deltaMax:ℝ) ≤ (dmaxUp:ℝ)^2 := by exact_mod_cast dmaxUp_sq_ge
    have hp : (0:ℝ) ≤ (dmaxUp:ℝ) := by norm_num [dmaxUp]
    exact (Real.sqrt_le_iff.mpr ⟨hp, e⟩)
  have ht : Real.sqrt (3 * (sqrt72Up:ℝ)) ≤ (tUp:ℝ) := by
    have e : 3 * (sqrt72Up:ℝ) ≤ (tUp:ℝ)^2 := by exact_mod_cast tUp_sq_ge
    have hp : (0:ℝ) ≤ (tUp:ℝ) := by norm_num [tUp]
    exact (Real.sqrt_le_iff.mpr ⟨hp, e⟩)
  have hrhs : (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * (dmaxUp:ℝ)
      + (tUp:ℝ) = (CBhi:ℝ) := by
    push_cast [CBhi_eq]; ring
  have e1 : (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * Real.sqrt (deltaMax:ℝ)
      ≤ (s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2 * (dmaxUp:ℝ) :=
    mul_le_mul_of_nonneg_left hd hk1nn
  linarith [e1, ht, hrhs]

/-- 路线 A 真系数·√72Up ≤ CAhi 包络（√u₁≤s1Up／√2≤sqrt2Up／s3Dn≤√l₃）。 -/
theorem coeffA_le_CAhi :
    (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
        + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * (sqrt72Up:ℝ) ≤ (CAhi:ℝ) := by
  have hu : Real.sqrt (u1:ℝ) ≤ (s1Up:ℝ) := TableB5.sqrt_u1_le_s1Up
  have h2 : Real.sqrt 2 ≤ (sqrt2Up:ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num [sqrt2Up]
    · exact_mod_cast sqrt2Up_sq_ge
  have hl : (s3Dn:ℝ) ≤ Real.sqrt (l3:ℝ) := TableB5.s3Dn_le_sqrt_l3
  have hl3 : (0:ℝ) < (l3:ℝ) := by norm_num [l3]
  have hl3p : (0:ℝ) < (l3:ℝ)^2 := pow_pos hl3 2
  have hs3p : (0:ℝ) < (s3Dn:ℝ) := by norm_num [s3Dn]
  have hu1n : (0:ℝ) ≤ (u1:ℝ) := by norm_num [u1]
  have hs72n : (0:ℝ) ≤ (sqrt72Up:ℝ) := by norm_num [sqrt72Up]
  have t1 : Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      ≤ (s1Up:ℝ) * (u1:ℝ) / (l3:ℝ)^2 := by
    rw [div_le_div_iff₀ hl3p hl3p]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu hu1n)
      (pow_pos hl3 2).le
  have e0 : 2 * Real.sqrt 2 * (s3Dn:ℝ) ≤ 2 * (sqrt2Up:ℝ) * (s3Dn:ℝ) := by
    calc 2 * Real.sqrt 2 * (s3Dn:ℝ) = Real.sqrt 2 * (2 * (s3Dn:ℝ)) := by ring
      _ ≤ (sqrt2Up:ℝ) * (2 * (s3Dn:ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg (by norm_num) hs3p.le)
      _ = 2 * (sqrt2Up:ℝ) * (s3Dn:ℝ) := by ring
  have t2 : 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)
      ≤ 2 * (sqrt2Up:ℝ) / (s3Dn:ℝ) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hl3) hs3p]
    have hn : (0:ℝ) ≤ 2 * (sqrt2Up:ℝ) :=
      mul_nonneg (by norm_num) (by norm_num [sqrt2Up])
    calc 2 * Real.sqrt 2 * (s3Dn:ℝ) ≤ 2 * (sqrt2Up:ℝ) * (s3Dn:ℝ) := e0
      _ ≤ 2 * (sqrt2Up:ℝ) * Real.sqrt (l3:ℝ) :=
          mul_le_mul_of_nonneg_left hl hn
  have hsum : Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)
      ≤ (s1Up:ℝ) * (u1:ℝ) / (l3:ℝ)^2 + 2 * (sqrt2Up:ℝ) / (s3Dn:ℝ) := by
    linarith [t1, t2]
  have hrhs : ((s1Up:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      + 2 * (sqrt2Up:ℝ) / (s3Dn:ℝ)) * (sqrt72Up:ℝ) = (CAhi:ℝ) := by
    push_cast [CAhi_eq]; ring
  have e : (Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * (sqrt72Up:ℝ)
      ≤ ((s1Up:ℝ) * (u1:ℝ) / (l3:ℝ)^2 + 2 * (sqrt2Up:ℝ) / (s3Dn:ℝ))
        * (sqrt72Up:ℝ) :=
    mul_le_mul_of_nonneg_right hsum hs72n
  linarith [e, hrhs]

/-! ### 推论（缝形式／未来 L3 证书喂入契约） -/

/-- rhoNeedB 等于球门支（域面定理在库）。 -/
theorem rhoNeedB_eq : rhoNeedB = (r_ball/CBhi)^2 :=
  min_eq_right threshB_lt_gMin_half.le

/-- rhoNeedA 等于球门支。 -/
theorem rhoNeedA_eq : rhoNeedA = r_ball/CAhi :=
  min_eq_right threshA_lt_gMin_half.le

/-- CBhi·(r_ball/CBhi)＝r_ball（包络支路闭端）。 -/
theorem CBhi_mul_eq : (CBhi:ℝ) * ((r_ball:ℝ) / (CBhi:ℝ)) = (r_ball:ℝ) := by
  have hne : (CBhi:ℝ) ≠ 0 := by
    have : (0:ℚ) < CBhi := CBhi_pos
    exact_mod_cast ne_of_gt this
  field_simp

/-- CAhi·(r_ball/CAhi)＝r_ball。 -/
theorem CAhi_mul_eq : (CAhi:ℝ) * ((r_ball:ℝ) / (CAhi:ℝ)) = (r_ball:ℝ) := by
  have hne : (CAhi:ℝ) ≠ 0 := by
    have : (0:ℚ) < CAhi := CAhi_pos
    exact_mod_cast ne_of_gt this
  field_simp

/-- **缝推论·路线 B（pair 形）**：E (rowPerm Y σ₀) < Ē ⟹ ∃ pair，
到节点集距离 > rhoNeedB＝min(gMin/2, (r_ball/CBhi)²)——R20 缝阈值
（r20_l5l6_seam.json r* 口径行逐位在账）自此在形式层承重。前提：
pattern-consistency（σ₀ 显式、管前提条件化）＋行单位＋L6 假设；
球门/辨识窗在推论内以 CBhi 包络内部导出（CB_le_CBhi）。 -/
theorem seam_cor_B_pair (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hunit : ∀ i : Fin 9, Y i ⬝ᵥ Y i = 1) (σ₀ : Equiv.Perm (Fin 9))
    (hpat : PatternCons Y z (rhoNeedB:ℝ) σ₀)
    (E : Matrix (Fin 9) (Fin 3) ℝ → ℝ) (Ebar : ℝ)
    (hL6 : L6Hyp z (r_ball:ℝ) E Ebar)
    (hElt : E (rowPerm Y σ₀) < Ebar) :
    ∃ i j : Fin 9, i ≠ j ∧ ∀ a : ℕ, a < 6 →
      (rhoNeedB:ℝ) < |Y i ⬝ᵥ Y j - nuOfN a z| := by
  by_contra hcon
  push_neg at hcon
  have hT : TubePremise Y z (rhoNeedB:ℝ) := hcon
  have hρid : (rhoNeedB:ℝ) < (gMin:ℝ)/2 := by
    rw [rhoNeedB_eq]; exact_mod_cast threshB_lt_gMin_half
  have hρnn : (0:ℚ) ≤ rhoNeedB := by
    rw [rhoNeedB_eq]; norm_num [r_ball, CBhi]
  have hsq : Real.sqrt ((rhoNeedB:ℝ)) ≤ (r_ball:ℝ) / (CBhi:ℝ) := by
    have hEq : (rhoNeedB:ℝ) = (((r_ball:ℚ)/CBhi : ℚ) : ℝ)^2 := by
      rw [rhoNeedB_eq]
      have hc : ((((r_ball:ℚ)/CBhi)^2 : ℚ) : ℝ)
          = (((r_ball:ℚ)/CBhi : ℚ) : ℝ)^2 := by push_cast; ring
      rw [hc]
    have hp : (0:ℝ) ≤ (((r_ball:ℚ)/CBhi : ℚ) : ℝ) := by
      have : (0:ℚ) ≤ r_ball/CBhi := div_nonneg r_ball_pos.le CBhi_pos.le
      exact_mod_cast this
    rw [hEq, Real.sqrt_sq hp]
    push_cast
    exact le_refl _
  have hB : ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2
      * Real.sqrt (deltaMax:ℝ) + Real.sqrt (3 * (sqrt72Up:ℝ)))
      * Real.sqrt (rhoNeedB:ℝ) ≤ (r_ball:ℝ) := by
    have hu : (0:ℝ) ≤ Real.sqrt (rhoNeedB:ℝ) := Real.sqrt_nonneg _
    have e1 : ((s1Up:ℝ) * (u1:ℝ) * (sqrt72Up:ℝ) / (l3:ℝ)^2
        * Real.sqrt (deltaMax:ℝ) + Real.sqrt (3 * (sqrt72Up:ℝ)))
        * Real.sqrt (rhoNeedB:ℝ) ≤ (CBhi:ℝ) * Real.sqrt (rhoNeedB:ℝ) :=
      mul_le_mul_of_nonneg_right CB_le_CBhi hu

    have e3 : (CBhi:ℝ) * Real.sqrt (rhoNeedB:ℝ)
        ≤ (CBhi:ℝ) * ((r_ball:ℝ) / (CBhi:ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by
        have : (0:ℚ) ≤ CBhi := CBhi_pos.le
        exact_mod_cast this)
    have e4 := CBhi_mul_eq
    linarith [e1, e3, e4]
  have hchain := chain_assemble_B z h1 h2 (rhoNeedB:ℝ) (by exact_mod_cast hρnn)
    Y hunit hT σ₀ hpat hρid E Ebar hL6 hB
  exact absurd hElt (not_lt.mpr hchain)

/-- **缝推论·路线 A（pair 形）**：同 B，窄域 ρNeedA＝min(gMin/2,
r_ball/CAhi)（δ_A 域面 threshA_le_deltaA 在库；coeffA_le_CAhi 包络）。 -/
theorem seam_cor_A_pair (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ))
    (Y : Matrix (Fin 9) (Fin 3) ℝ)
    (hunit : ∀ i : Fin 9, Y i ⬝ᵥ Y i = 1) (σ₀ : Equiv.Perm (Fin 9))
    (hpat : PatternCons Y z (rhoNeedA:ℝ) σ₀)
    (E : Matrix (Fin 9) (Fin 3) ℝ → ℝ) (Ebar : ℝ)
    (hL6 : L6Hyp z (r_ball:ℝ) E Ebar)
    (hElt : E (rowPerm Y σ₀) < Ebar) :
    ∃ i j : Fin 9, i ≠ j ∧ ∀ a : ℕ, a < 6 →
      (rhoNeedA:ℝ) < |Y i ⬝ᵥ Y j - nuOfN a z| := by
  by_contra hcon
  push_neg at hcon
  have hT : TubePremise Y z (rhoNeedA:ℝ) := hcon
  have hρid : (rhoNeedA:ℝ) < (gMin:ℝ)/2 := by
    rw [rhoNeedA_eq]; exact_mod_cast threshA_lt_gMin_half
  have hρA : (rhoNeedA:ℝ) ≤ (deltaA:ℝ) := by
    rw [rhoNeedA_eq]; exact_mod_cast threshA_le_deltaA
  have hρnn : (0:ℚ) ≤ rhoNeedA := by
    rw [rhoNeedA_eq]; norm_num [r_ball, CAhi]
  have hB : ((Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
      + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * (sqrt72Up:ℝ))
      * (rhoNeedA:ℝ) ≤ (r_ball:ℝ) := by
    have hle := coeffA_le_CAhi
    have hnn : (0:ℝ) ≤ (rhoNeedA:ℝ) := by exact_mod_cast hρnn
    have hlo : ((Real.sqrt (u1:ℝ) * (u1:ℝ) / (l3:ℝ)^2
        + 2 * Real.sqrt 2 / Real.sqrt (l3:ℝ)) * (sqrt72Up:ℝ))
        * (rhoNeedA:ℝ) ≤ (CAhi:ℝ) * (rhoNeedA:ℝ) :=
      mul_le_mul_of_nonneg_right hle hnn
    have hprod : (CAhi:ℝ) * (rhoNeedA:ℝ) = (r_ball:ℝ) := by
      rw [rhoNeedA_eq]; push_cast; exact CAhi_mul_eq
    linarith [hlo, hprod]
  have hchain := chain_assemble_A z h1 h2 (rhoNeedA:ℝ) (by exact_mod_cast hρnn)
    Y hunit hT σ₀ hpat hρid hρA E Ebar hL6 hB
  exact absurd hElt (not_lt.mpr hchain)

end ThomsonN9.TableB5Chain
