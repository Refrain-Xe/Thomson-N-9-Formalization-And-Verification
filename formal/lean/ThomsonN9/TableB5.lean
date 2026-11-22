import Mathlib
import ThomsonN9.TableB5Data

/-!
# Table B5 (R14 / r14a): the Procrustes rigidity constant layer of the TTP family

**B5.** For the 9-point TTP (tri-cap-prism) configuration `X(z)` — two parallel
triangles of radius `ρ = √(1−z²)` at heights `±z` plus the three equatorial
cap points `(1/2, √3/2, 0)`, `(−1, 0, 0)`, `(1/2, −√3/2, 0)` — this file
proves the constant layer of the L4 Procrustes theorem exactly, with all
numeric literals anchored in `ThomsonN9.TableB5Data` (the read-only
re-derivation of `numerics/bounds/results/l4.json`):

* **Diagonalisation.** `ttp_quadform`: the quadratic form of `S = XᵀX`
  satisfies `vᵀXᵀXv = (3(1−z²)+3/2)(v₀²+v₁²) + 6z²v₂²` for every `z` with
  `z² ≤ 1` — proved by an explicit `ring` certificate
  `diff = (√3·√3−3)(ρ²v₁²+v₁²/2) + (ρ²+z²−1)·3(v₀²+v₁²)` whose two
  coefficients vanish by `Real.mul_self_sqrt` (the direct `nlinarith` attack
  fails; D56-2).  The Gram entries follow: `ttpQ_e0/e1/e2` (diagonal
  `3(1−z²)+3/2, 3(1−z²)+3/2, 6z²`) and `ttpQ_off01/off02/off12` (the mixed
  second differences vanish — since the matrix `X` is not formalised, the
  off-diagonal entries `S_ij = 0` are stated as vanishing mixed second
  differences of the quadratic form, which is exactly the polarisation
  identity content of `S_ij = 0`; D57-3).

* **λ sandwich (quadratic-form route, no eigenvalue API).** For `z` in the
  recorded z-box (`zLo ≤ z ≤ zHi`, the strict isolation interval of
  `local_min.json`): `l₃·‖v‖² ≤ vᵀXᵀXv ≤ u₁·‖v‖²` (`ttp_sandwich_lo`,
  `ttp_sandwich_hi`).  The recorded interval-Sylvester bounds are dominated
  by the diagonal route: `6·zLo² ≥ l₃`, `9/2 − 3·zLo² ≤ u₁`, `zHi² < 1/2`
  (TableB5Data, `norm_num`), from which both directions follow by
  coefficient-wise `nlinarith` certificates.

* **S-interval container.** `S_interval_container`: for `z` in the box the
  true diagonal entries lie in the recorded `l4.json` `S_interval` intervals
  (S22 endpoints equal `6zLo²`/`6zHi²` bit for bit, S00/S11 are strictly
  widened ρ-enclosures), and the true off-diagonal value `0` lies in the
  recorded symmetric intervals.

* **Square-root envelopes (four).** `sqrt_u1_le_s1Up`, `s3Dn_le_sqrt_l3`,
  `sqrt72_le_sqrt72Up`, `sqrt_l3_le_s1Up`: the 200-bit rational envelopes of
  `TableB5Data` bound the corresponding real square roots (`Real.sqrt_le_iff`
  / `sq_le_sq`-style certificates; D56-3: `div_le_div_of_nonneg` is absent at
  this Mathlib revision — division monotonicity goes through
  `div_le_div_iff₀` or multiply-out forms).

* **Validity of C.** `C_valid`: for any real spectrum with
  `0 < l₃ ≤ λ₃ ≤ λ₁ ≤ u₁`, one has
  `√72·((√λ₁)³/λ₃² + 2/√λ₃) ≤ C`, where `C` is the assembled constant of
  `TableB5Data` (`C = sqrt72Up·(u₁·s1Up/l₃² + 2/s3Dn)`).

* **Validity of the δ_max regime.** `delta_max_valid`: if `0 ≤ η`,
  `η ≤ √72·δ` and `δ ≤ δ_max`, then for any spectrum with
  `0 < l₃ ≤ λ₃ ≤ λ₁ ≤ u₁` the regime parameter obeys
  `β = λ₁η/λ₃² ≤ min(1/2, √λ₃/(2√λ₁))` — the exact applicability domain of
  the L4 proof.

Honest scope note (B5-first-piece boundary): the analytic body
`d_P(X,Y) ≤ C·δ` (the `l4_procrustes.py` proof steps 1–6: projection split /
polar decomposition / rotation normalisation) is NOT part of this file; this
file certifies the constant layer only.  The interval-Sylvester soundness
(multilinearity at the vertices) is a non-essential stretch face and is not
formalised here.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace ThomsonN9.TableB5

open ThomsonN9.TableB5Data

/-- The TTP quadratic form `vᵀXᵀXv = Σᵢ (xᵢ·v)²` as an explicit 9-square sum:
upper triangle rows `(ρ,0,z)`, `(−ρ/2, √3ρ/2, z)`, `(−ρ/2, −√3ρ/2, z)`;
lower triangle rows with `z → −z`; cap rows `(1/2, √3/2, 0)`, `(−1,0,0)`,
`(1/2, −√3/2, 0)`; `ρ = √(1−z²)`. -/
noncomputable def ttpQ (z v0 v1 v2 : ℝ) : ℝ :=
  (Real.sqrt (1-z^2)*v0 + z*v2)^2
  + (-(Real.sqrt (1-z^2)/2)*v0 + (Real.sqrt 3 * Real.sqrt (1-z^2)/2)*v1 + z*v2)^2
  + (-(Real.sqrt (1-z^2)/2)*v0 - (Real.sqrt 3 * Real.sqrt (1-z^2)/2)*v1 + z*v2)^2
  + (Real.sqrt (1-z^2)*v0 - z*v2)^2
  + (-(Real.sqrt (1-z^2)/2)*v0 + (Real.sqrt 3 * Real.sqrt (1-z^2)/2)*v1 - z*v2)^2
  + (-(Real.sqrt (1-z^2)/2)*v0 - (Real.sqrt 3 * Real.sqrt (1-z^2)/2)*v1 - z*v2)^2
  + (v0/2 + Real.sqrt 3 * v1/2)^2 + (-v0)^2 + (v0/2 - Real.sqrt 3 * v1/2)^2

/-- **二次型对角化恒等式（显式 ring 证书）**：对一切 `z² ≤ 1`，
`vᵀXᵀXv = (3(1−z²)+3/2)(v₀²+v₁²) + 6z²v₂²`。证书两系数
`(√3·√3−3)` 与 `(ρ²+z²−1)` 经 `Real.mul_self_sqrt` 消零（nlinarith 直攻
失败留档 D56-2；探针 R14 本会话亲跑通过）。 -/
theorem ttp_quadform (z : ℝ) (hz : z^2 ≤ 1) (v0 v1 v2 : ℝ) :
    ttpQ z v0 v1 v2 = (3*(1-z^2)+3/2)*(v0^2+v1^2) + 6*z^2*v2^2 := by
  have hρ : 0 ≤ 1 - z^2 := by nlinarith [hz]
  have hcert : ttpQ z v0 v1 v2 - ((3*(1-z^2)+3/2)*(v0^2+v1^2) + 6*z^2*v2^2)
      = (Real.sqrt 3 * Real.sqrt 3 - 3)
          * (Real.sqrt (1-z^2) * Real.sqrt (1-z^2) * v1^2 + v1^2/2)
      + (Real.sqrt (1-z^2) * Real.sqrt (1-z^2) + z^2 - 1) * (3*(v0^2+v1^2)) := by
    unfold ttpQ; ring
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3),
      Real.mul_self_sqrt hρ] at hcert
  ring_nf at hcert
  linarith

/-- Gram 对角元 `S₀₀ = 3(1−z²)+3/2`（`q(e₀)`）。 -/
theorem ttpQ_e0 (z : ℝ) (hz : z^2 ≤ 1) : ttpQ z 1 0 0 = 3*(1-z^2)+3/2 := by
  rw [ttp_quadform z hz 1 0 0]; ring

/-- Gram 对角元 `S₁₁ = 3(1−z²)+3/2`（`q(e₁)`）。 -/
theorem ttpQ_e1 (z : ℝ) (hz : z^2 ≤ 1) : ttpQ z 0 1 0 = 3*(1-z^2)+3/2 := by
  rw [ttp_quadform z hz 0 1 0]; ring

/-- Gram 对角元 `S₂₂ = 6z²`（`q(e₂)`）。 -/
theorem ttpQ_e2 (z : ℝ) (hz : z^2 ≤ 1) : ttpQ z 0 0 1 = 6*z^2 := by
  rw [ttp_quadform z hz 0 0 1]; ring

/-- 非对角元 `S₀₁ = 0`（混合二阶差消失；极化恒等式内容，D57-3）。 -/
theorem ttpQ_off01 (z : ℝ) (hz : z^2 ≤ 1) :
    ttpQ z 1 1 0 - ttpQ z 1 0 0 - ttpQ z 0 1 0 = 0 := by
  rw [ttp_quadform z hz 1 1 0, ttp_quadform z hz 1 0 0, ttp_quadform z hz 0 1 0]; ring

/-- 非对角元 `S₀₂ = 0`（混合二阶差消失）。 -/
theorem ttpQ_off02 (z : ℝ) (hz : z^2 ≤ 1) :
    ttpQ z 1 0 1 - ttpQ z 1 0 0 - ttpQ z 0 0 1 = 0 := by
  rw [ttp_quadform z hz 1 0 1, ttp_quadform z hz 1 0 0, ttp_quadform z hz 0 0 1]; ring

/-- 非对角元 `S₁₂ = 0`（混合二阶差消失）。 -/
theorem ttpQ_off12 (z : ℝ) (hz : z^2 ≤ 1) :
    ttpQ z 0 1 1 - ttpQ z 0 1 0 - ttpQ z 0 0 1 = 0 := by
  rw [ttp_quadform z hz 0 1 1, ttp_quadform z hz 0 1 0, ttp_quadform z hz 0 0 1]; ring

/-- **λ 夹逼·下侧**（二次型口径，免特征值 API）：对 z 盒内一切 z 与一切 v，
`l₃·‖v‖² ≤ vᵀXᵀXv`。对角路线支配：`l₃ ≤ 6·zLo² ≤ 6z²`（z ≥ zLo）且
`l₃ < 3 < 3(1−z²)+3/2`（z_hi² < 1/2 ⇒ a(z) > 3）。 -/
theorem ttp_sandwich_lo (z v0 v1 v2 : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    (l3:ℝ)*(v0^2+v1^2+v2^2) ≤ ttpQ z v0 v1 v2 := by
  have hzLop : (0:ℝ) < (zLo:ℝ) := by norm_num [zLo]
  have hzh2 : ((zHi:ℝ))^2 < 1/2 := by norm_num [zHi]
  have hsix : (l3:ℝ) ≤ 6 * (zLo:ℝ)^2 := by norm_num [zLo, l3]
  have hl3lt3 : (l3:ℝ) < 3 := by norm_num [l3]
  have hpos : (0:ℝ) < z := by nlinarith [h1, hzLop]
  have hz1 : z^2 ≤ 1 := by nlinarith [hzh2, h2, hpos]
  have hzlo2 : (zLo:ℝ)^2 ≤ z^2 := by nlinarith [h1, hpos]
  have hzhi2 : z^2 ≤ (zHi:ℝ)^2 := by nlinarith [h2, hpos]
  rw [ttp_quadform z hz1 v0 v1 v2]
  have key : ((3*(1-z^2)+3/2)*(v0^2+v1^2) + 6*z^2*v2^2)
      - (l3:ℝ)*(v0^2+v1^2+v2^2)
      = (3*(1-z^2)+3/2 - (l3:ℝ))*(v0^2+v1^2) + (6*z^2 - (l3:ℝ))*v2^2 := by ring
  have c1 : (0:ℝ) ≤ 3*(1-z^2)+3/2 - (l3:ℝ) := by
    have e1 : 3*(1-z^2)+3/2 - (l3:ℝ)
        = 3*(1/2 - (zHi:ℝ)^2) + 3*((zHi:ℝ)^2 - z^2) + (3 - (l3:ℝ)) := by ring
    nlinarith [hzhi2, hzh2, hl3lt3, e1]
  have c2 : (0:ℝ) ≤ 6*z^2 - (l3:ℝ) := by nlinarith [hzlo2, hsix]
  have d1 : (0:ℝ) ≤ v0^2+v1^2 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
  nlinarith [key, mul_nonneg c1 d1, mul_nonneg c2 (sq_nonneg v2)]

/-- **λ 夹逼·上侧**：对 z 盒内一切 z 与一切 v，`vᵀXᵀXv ≤ u₁·‖v‖²`。对角路线
支配：`3(1−z²)+3/2 ≤ 9/2−3·zLo² ≤ u₁`（z ≥ zLo）且 `6z² ≤ 6·zHi² < 3 ≤ u₁`。 -/
theorem ttp_sandwich_hi (z v0 v1 v2 : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    ttpQ z v0 v1 v2 ≤ (u1:ℝ)*(v0^2+v1^2+v2^2) := by
  have hzLop : (0:ℝ) < (zLo:ℝ) := by norm_num [zLo]
  have hzh2 : ((zHi:ℝ))^2 < 1/2 := by norm_num [zHi]
  have hforty : 9/2 - 3 * (zLo:ℝ)^2 ≤ (u1:ℝ) := by norm_num [zLo, u1]
  have h3u1 : (3:ℝ) ≤ (u1:ℝ) := by norm_num [u1]
  have hpos : (0:ℝ) < z := by nlinarith [h1, hzLop]
  have hz1 : z^2 ≤ 1 := by nlinarith [hzh2, h2, hpos]
  have hzlo2 : (zLo:ℝ)^2 ≤ z^2 := by nlinarith [h1, hpos]
  have hzhi2 : z^2 ≤ (zHi:ℝ)^2 := by nlinarith [h2, hpos]
  rw [ttp_quadform z hz1 v0 v1 v2]
  have key2 : ((u1:ℝ)*(v0^2+v1^2+v2^2))
      - ((3*(1-z^2)+3/2)*(v0^2+v1^2) + 6*z^2*v2^2)
      = ((u1:ℝ) - (3*(1-z^2)+3/2))*(v0^2+v1^2) + ((u1:ℝ) - 6*z^2)*v2^2 := by ring
  have c3 : (0:ℝ) ≤ (u1:ℝ) - (3*(1-z^2)+3/2) := by nlinarith [hzlo2, hforty]
  have c4 : (0:ℝ) ≤ (u1:ℝ) - 6*z^2 := by nlinarith [h3u1, hzhi2, hzh2]
  have d1 : (0:ℝ) ≤ v0^2+v1^2 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
  nlinarith [key2, mul_nonneg c3 d1, mul_nonneg c4 (sq_nonneg v2)]

/-- **S 区间容器定理**：对 z 盒内一切 z，对角真值端点落在 l4.json 记录
`S_interval` 内（S22 端点==6z² 逐位、S00/S11 为 ρ 外扩严格容器、非对角真值
0 ∈ 对称区间）。 -/
theorem S_interval_container (z : ℝ) (h1 : (zLo:ℝ) ≤ z) (h2 : z ≤ (zHi:ℝ)) :
    (S00lo:ℝ) < 3*(1-z^2)+3/2 ∧ 3*(1-z^2)+3/2 < (S00hi:ℝ) ∧
    (S11lo:ℝ) < 3*(1-z^2)+3/2 ∧ 3*(1-z^2)+3/2 < (S11hi:ℝ) ∧
    (S22lo:ℝ) ≤ 6*z^2 ∧ 6*z^2 ≤ (S22hi:ℝ) ∧
    (S01lo:ℝ) ≤ 0 ∧ 0 ≤ (S01hi:ℝ) ∧ (S02lo:ℝ) ≤ 0 ∧ 0 ≤ (S02hi:ℝ) ∧
    (S12lo:ℝ) ≤ 0 ∧ 0 ≤ (S12hi:ℝ) := by
  have hzLop : (0:ℝ) < (zLo:ℝ) := by norm_num [zLo]
  have hpos : (0:ℝ) < z := by nlinarith [h1, hzLop]
  have hzlo2 : (zLo:ℝ)^2 ≤ z^2 := by nlinarith [h1, hpos]
  have hzhi2 : z^2 ≤ (zHi:ℝ)^2 := by nlinarith [h2, hpos]
  have c00lo : (S00lo:ℝ) < 9/2 - 3*((zHi:ℝ))^2 := by norm_num [S00lo, zHi]
  have c00hi : 9/2 - 3*((zLo:ℝ))^2 < (S00hi:ℝ) := by norm_num [S00hi, zLo]
  have c11lo : (S11lo:ℝ) < 9/2 - 3*((zHi:ℝ))^2 := by norm_num [S11lo, zHi]
  have c11hi : 9/2 - 3*((zLo:ℝ))^2 < (S11hi:ℝ) := by norm_num [S11hi, zLo]
  have c22lo : (S22lo:ℝ) = 6*((zLo:ℝ))^2 := by norm_num [S22lo, zLo]
  have c22hi : (S22hi:ℝ) = 6*((zHi:ℝ))^2 := by norm_num [S22hi, zHi]
  have c01lo : (S01lo:ℝ) ≤ 0 := by norm_num [S01lo, S01hi]
  have c01hi : (0:ℝ) ≤ (S01hi:ℝ) := by norm_num [S01hi]
  have c02lo : (S02lo:ℝ) ≤ 0 := by norm_num [S02lo, S02hi]
  have c02hi : (0:ℝ) ≤ (S02hi:ℝ) := by norm_num [S02hi]
  have c12lo : (S12lo:ℝ) ≤ 0 := by norm_num [S12lo, S12hi]
  have c12hi : (0:ℝ) ≤ (S12hi:ℝ) := by norm_num [S12hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### sqrt 有理界四件（ℝ） -/

/-- sqrt 界①：`√u₁ ≤ s1Up`（前提 `u₁ ≤ s1Up²`，`Real.sqrt_le_iff`）。 -/
theorem sqrt_u1_le_s1Up : Real.sqrt (u1:ℝ) ≤ (s1Up:ℝ) := by
  rw [Real.sqrt_le_iff]; constructor <;> norm_num [u1, s1Up]

/-- sqrt 界②：`s3Dn ≤ √l₃`（前提 `s3Dn² ≤ l₃`，sq_le_sq 型证书）。 -/
theorem s3Dn_le_sqrt_l3 : (s3Dn:ℝ) ≤ Real.sqrt (l3:ℝ) := by
  have e : ((s3Dn:ℝ))^2 ≤ (l3:ℝ) := by norm_num [s3Dn, l3]
  have hpos : (0:ℝ) < (s3Dn:ℝ) := by norm_num [s3Dn]
  nlinarith [e, hpos, Real.sqrt_nonneg ((l3:ℝ)),
    Real.sq_sqrt (by norm_num [l3] : (0:ℝ) ≤ (l3:ℝ))]

/-- sqrt 界③：`√72 ≤ sqrt72Up`（前提 `72 ≤ sqrt72Up²`）。 -/
theorem sqrt72_le_sqrt72Up : Real.sqrt 72 ≤ (sqrt72Up:ℝ) := by
  rw [Real.sqrt_le_iff]; constructor <;> norm_num [sqrt72Up]

/-- sqrt 界④：`√l₃ ≤ s1Up`（√l₃ ≤ √u₁ ≤ s1Up 链）。 -/
theorem sqrt_l3_le_s1Up : Real.sqrt (l3:ℝ) ≤ (s1Up:ℝ) := by
  have h : (l3:ℝ) ≤ (u1:ℝ) := by norm_num [l3, u1]
  exact le_trans (Real.sqrt_le_sqrt h) sqrt_u1_le_s1Up

/-- sqrt 链推论：`s3Dn ≤ s1Up`（δ_max 适用域 `s3Dn/(2·s1Up) ≤ 1/2` 之源）。 -/
theorem s3Dn_le_s1UpR : (s3Dn:ℝ) ≤ (s1Up:ℝ) :=
  le_trans s3Dn_le_sqrt_l3 sqrt_l3_le_s1Up

/-! ### 有效性定理（C 与 δ_max 适用域） -/

/-- **C 有效性**：对一切实谱 `0 < l₃ ≤ λ₃ ≤ λ₁ ≤ u₁`，
`√72·((√λ₁)³/λ₃² + 2/√λ₃) ≤ C`——L4 定理的谱因子以装配常数 C 全程支配
（l4_procrustes.py 步骤 6 的右端）。 -/
theorem C_valid (lam3 lam1 : ℝ) (h3 : (l3:ℝ) ≤ lam3) (h1 : lam1 ≤ (u1:ℝ))
    (hord : lam3 ≤ lam1) :
    Real.sqrt 72 * ((Real.sqrt lam1)^3 / lam3^2 + 2 / Real.sqrt lam3) ≤ (CVal:ℝ) := by
  have hl3 : (0:ℝ) < lam3 := lt_of_lt_of_le (by norm_num [l3]) h3
  have hl1 : (0:ℝ) < lam1 := lt_of_lt_of_le hl3 hord
  have hs1 : Real.sqrt lam1 ≤ (s1Up:ℝ) :=
    le_trans (Real.sqrt_le_sqrt h1) sqrt_u1_le_s1Up
  have hs3 : (s3Dn:ℝ) ≤ Real.sqrt lam3 :=
    le_trans s3Dn_le_sqrt_l3 (Real.sqrt_le_sqrt h3)
  have cube : (Real.sqrt lam1)^3 ≤ (u1:ℝ) * (s1Up:ℝ) := by
    have hp : (Real.sqrt lam1)^3 = Real.sqrt lam1 * ((Real.sqrt lam1)^2) := by ring
    rw [hp, Real.sq_sqrt hl1.le]
    have e1 : Real.sqrt lam1 * lam1 ≤ (s1Up:ℝ) * lam1 :=
      mul_le_mul_of_nonneg_right hs1 hl1.le
    have e2 : (s1Up:ℝ) * lam1 ≤ (s1Up:ℝ) * (u1:ℝ) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num [s1Up])
    nlinarith [e1, e2]
  have A_le : (Real.sqrt lam1)^3 / lam3^2
      ≤ (u1:ℝ) * (s1Up:ℝ) / ((l3:ℝ)*(l3:ℝ)) := by
    have hl3pos : (0:ℝ) < (l3:ℝ) := by norm_num [l3]
    rw [div_le_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hl3))
      (by nlinarith [hl3pos] : (0:ℝ) < (l3:ℝ)*(l3:ℝ))]
    have l3sq : (l3:ℝ)*(l3:ℝ) ≤ lam3*lam3 := by nlinarith [h3, hl3pos]
    have e1 : (Real.sqrt lam1)^3 * ((l3:ℝ)*(l3:ℝ))
        ≤ (u1:ℝ)*(s1Up:ℝ) * ((l3:ℝ)*(l3:ℝ)) :=
      mul_le_mul_of_nonneg_right cube (mul_nonneg hl3pos.le hl3pos.le)
    have e2 : (u1:ℝ)*(s1Up:ℝ) * ((l3:ℝ)*(l3:ℝ))
        ≤ (u1:ℝ)*(s1Up:ℝ) * (lam3*lam3) :=
      mul_le_mul_of_nonneg_left l3sq (mul_nonneg (by linarith [hl1, h1])
        (by norm_num [s1Up]))
    nlinarith [e1, e2]
  have B_le : 2 / Real.sqrt lam3 ≤ 2 / (s3Dn:ℝ) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hl3) (by norm_num [s3Dn])]
    nlinarith [hs3]
  have innerR : (u1:ℝ) * (s1Up:ℝ) / ((l3:ℝ)*(l3:ℝ)) + 2 / (s3Dn:ℝ)
      = (CInner:ℝ) := by exact_mod_cast C_inner_val
  have sum_le : (Real.sqrt lam1)^3 / lam3^2 + 2 / Real.sqrt lam3
      ≤ (CInner:ℝ) := by
    rw [← innerR]; linarith [A_le, B_le]
  have Ccast : (sqrt72Up:ℝ) * (CInner:ℝ) = (CVal:ℝ) := by exact_mod_cast C_val
  have Apos : (0:ℝ) ≤ (Real.sqrt lam1)^3 / lam3^2 :=
    div_nonneg (pow_nonneg (Real.sqrt_nonneg lam1) 3) (sq_nonneg lam3)
  have Bpos : (0:ℝ) ≤ 2 / Real.sqrt lam3 := by positivity
  have step1 : Real.sqrt 72 * ((Real.sqrt lam1)^3 / lam3^2 + 2 / Real.sqrt lam3)
      ≤ (sqrt72Up:ℝ) * ((Real.sqrt lam1)^3 / lam3^2 + 2 / Real.sqrt lam3) :=
    mul_le_mul_of_nonneg_right sqrt72_le_sqrt72Up (by linarith [Apos, Bpos])
  have step2 : (sqrt72Up:ℝ) * ((Real.sqrt lam1)^3 / lam3^2 + 2 / Real.sqrt lam3)
      ≤ (sqrt72Up:ℝ) * (CInner:ℝ) :=
    mul_le_mul_of_nonneg_left sum_le (by norm_num [sqrt72Up])
  linarith [step1, step2, Ccast]

/-- **δ_max 适用域有效性**：`0 ≤ η`、`η ≤ √72·δ`、`δ ≤ δ_max` 且实谱
`0 < l₃ ≤ λ₃ ≤ λ₁ ≤ u₁` 时，`β = λ₁η/λ₃² ≤ min(1/2, √λ₃/(2√λ₁))`——
即 L4 证明的 β 前提在记录 δ_max 域内自动成立。 -/
theorem delta_max_valid (lam3 lam1 eta delta : ℝ) (heta0 : (0:ℝ) ≤ eta)
    (heta : eta ≤ Real.sqrt 72 * delta) (hdel : delta ≤ (deltaMax:ℝ))
    (h3 : (l3:ℝ) ≤ lam3) (h1 : lam1 ≤ (u1:ℝ)) (hord : lam3 ≤ lam1) :
    lam1 * eta / lam3^2
      ≤ min (1/2) (Real.sqrt lam3 / (2 * Real.sqrt lam1)) := by
  have hl3 : (0:ℝ) < lam3 := lt_of_lt_of_le (by norm_num [l3]) h3
  have hl1 : (0:ℝ) < lam1 := lt_of_lt_of_le hl3 hord
  have hs1 : Real.sqrt lam1 ≤ (s1Up:ℝ) :=
    le_trans (Real.sqrt_le_sqrt h1) sqrt_u1_le_s1Up
  have hs3 : (s3Dn:ℝ) ≤ Real.sqrt lam3 :=
    le_trans s3Dn_le_sqrt_l3 (Real.sqrt_le_sqrt h3)
  have hsqrtpos : (0:ℝ) < Real.sqrt 72 := by positivity
  have hd0 : (0:ℝ) ≤ delta := by nlinarith [heta0, heta, hsqrtpos]
  have eta_le : eta ≤ (sqrt72Up:ℝ) * (deltaMax:ℝ) := by
    have e1 : Real.sqrt 72 * delta ≤ (sqrt72Up:ℝ) * delta :=
      mul_le_mul_of_nonneg_right sqrt72_le_sqrt72Up hd0
    have e2 : (sqrt72Up:ℝ) * delta ≤ (sqrt72Up:ℝ) * (deltaMax:ℝ) :=
      mul_le_mul_of_nonneg_left hdel (by norm_num [sqrt72Up])
    linarith [heta, e1, e2]
  have idR : (u1:ℝ) * ((sqrt72Up:ℝ) * (deltaMax:ℝ)) * (2*(s1Up:ℝ))
      = (s3Dn:ℝ) * ((l3:ℝ)*(l3:ℝ)) := by
    norm_num [u1, sqrt72Up, deltaMax, s1Up, s3Dn, l3]
  have hs1upR : (0:ℝ) < (s1Up:ℝ) := by norm_num [s1Up]
  have h2s1up : (0:ℝ) < 2*(s1Up:ℝ) := by nlinarith [hs1upR]
  have beta_le : lam1 * eta / lam3^2 ≤ (s3Dn:ℝ) / (2*(s1Up:ℝ)) := by
    rw [div_le_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hl3)) h2s1up]
    rw [show lam3^2 = lam3*lam3 from by ring]
    have Dnn : (0:ℝ) ≤ (sqrt72Up:ℝ)*(deltaMax:ℝ) :=
      mul_nonneg (by norm_num [sqrt72Up]) (by norm_num [deltaMax])
    have u1nn : (0:ℝ) ≤ (u1:ℝ) := by linarith [hl1, h1]
    have p1 : lam1 * eta ≤ (u1:ℝ)*((sqrt72Up:ℝ)*(deltaMax:ℝ)) := by
      have a1 : lam1 * eta ≤ (u1:ℝ) * eta := mul_le_mul_of_nonneg_right h1 heta0
      have a2 : (u1:ℝ) * eta ≤ (u1:ℝ) * ((sqrt72Up:ℝ)*(deltaMax:ℝ)) :=
        mul_le_mul_of_nonneg_left eta_le u1nn
      linarith [a1, a2]
    have e1 : lam1*eta*(2*(s1Up:ℝ))
        ≤ (u1:ℝ)*((sqrt72Up:ℝ)*(deltaMax:ℝ))*(2*(s1Up:ℝ)) :=
      mul_le_mul_of_nonneg_right p1 h2s1up.le
    have l3sq : (l3:ℝ)*(l3:ℝ) ≤ lam3*lam3 := by
      nlinarith [h3, (show (0:ℝ) < (l3:ℝ) by norm_num [l3])]
    have e2 : (u1:ℝ)*((sqrt72Up:ℝ)*(deltaMax:ℝ))*(2*(s1Up:ℝ))
        ≤ (s3Dn:ℝ)*(lam3*lam3) := by
      rw [idR]
      exact mul_le_mul_of_nonneg_left l3sq (by norm_num [s3Dn])
    linarith [e1, e2]
  have half_le : (s3Dn:ℝ) / (2*(s1Up:ℝ)) ≤ 1/2 := by
    rw [div_le_div_iff₀ h2s1up (by norm_num)]
    nlinarith [s3Dn_le_s1UpR]
  have sqrt_le : (s3Dn:ℝ) / (2*(s1Up:ℝ))
      ≤ Real.sqrt lam3 / (2 * Real.sqrt lam1) := by
    rw [div_le_div_iff₀ h2s1up (mul_pos (by norm_num : (0:ℝ) < 2)
      (Real.sqrt_pos.mpr hl1))]
    have hs1lam1 : (0:ℝ) ≤ 2 * Real.sqrt lam1 :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg lam1)
    have hs3lam3 : (0:ℝ) ≤ Real.sqrt lam3 := Real.sqrt_nonneg lam3
    have e1 : (s3Dn:ℝ) * (2 * Real.sqrt lam1)
        ≤ (Real.sqrt lam3) * (2 * Real.sqrt lam1) :=
      mul_le_mul_of_nonneg_right hs3 hs1lam1
    have f : (2:ℝ) * Real.sqrt lam1 ≤ (2:ℝ)*(s1Up:ℝ) :=
      mul_le_mul_of_nonneg_left hs1 (by norm_num)
    have e2 : (Real.sqrt lam3) * (2 * Real.sqrt lam1)
        ≤ (Real.sqrt lam3) * (2*(s1Up:ℝ)) :=
      mul_le_mul_of_nonneg_left f hs3lam3
    linarith [e1, e2]
  exact le_min (le_trans beta_le half_le) (le_trans beta_le sqrt_le)

end ThomsonN9.TableB5
