import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Route W, IMS06′ 的纯数值部分（S-W-NECK G1，后缀 `_NK`）

IMS06′（neck band exclusion）的最后一步：IMS05′（σ = 1/2）给 `r ≤ 2π√(2/(3σ)) = 4π/√3`，
而 band 估计（|dz| ≤ 2，z 的变化为 20）给 r = 8，所以只要 `4π/√3 < 8` 就矛盾。
本文件只含这个数值事实（`π < 3.15`、`√3 > 1.73`），以及 IMS05′ 常数的 `σ = 1/2` 形式。
-/

set_option autoImplicit false

namespace GC.LongTime

/-- `4π/√3 < 8`（`π < 3.15`，`√3 > 1.73`：`4π/√3 < 4 * 3.15 / 1.73 < 7.3`）。 -/
theorem four_pi_div_sqrt_three_lt_eight_NK : 4 * Real.pi / Real.sqrt 3 < 8 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have h3 : (1.73 : ℝ) < Real.sqrt 3 := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [Real.pi_pos]

/-- IMS05′ 的常数 `2π√(2/(3σ))` 在 `σ = 1/2` 时 `< 8`（它等于 `4π/√3`）。 -/
theorem stabilityRadiusConstant_half_lt_eight_NK :
    2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2))) < 8 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hs : Real.sqrt (2 / (3 * (1 / 2))) < 1.16 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hs0 : 0 ≤ Real.sqrt (2 / (3 * (1 / 2))) := Real.sqrt_nonneg _
  nlinarith [Real.pi_pos]

/-- 常数形式与 `4π/√3` 的等式（核对用）：`2π√(2/(3·(1/2))) = 4π/√3`。 -/
theorem stabilityRadiusConstant_half_eq_NK :
    2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2))) = 4 * Real.pi / Real.sqrt 3 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h : Real.sqrt (2 / (3 * (1 / 2))) = 2 / Real.sqrt 3 := by
    rw [show (2 : ℝ) / (3 * (1 / 2)) = 2 ^ 2 / 3 by norm_num, Real.sqrt_div (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h]
  ring

/-- consumer：半径 8 与 IMS05′（σ = 1/2）的上界矛盾。 -/
theorem radius_eight_not_le_stabilityRadius_NK
    (h : (8 : ℝ) ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) : False :=
  absurd stabilityRadiusConstant_half_lt_eight_NK (not_lt.mpr h)

end GC.LongTime
