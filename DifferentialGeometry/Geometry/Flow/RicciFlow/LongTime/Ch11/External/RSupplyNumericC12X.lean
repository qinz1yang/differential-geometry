import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# 数值引理 `rNext ≥ min(1, 100·cMax)·rSupply`（O-C12X-RSUP G1b，后缀 `_C12X`）

R-C11-7 D-6 的纯数值引理。astra Step（`PreparedSpatialStep.lean:216`）取
`rNext := min rSupply (100·cMax/√Qall)`，取 min 前已有 `0 < rSupply`、`Qall ≤ rSupply⁻²`、
`0 < Qall`（Step:150-160）与 `0 < cMax`；于是 `min` 的第二项不是独立障碍：
`rNext ≥ min 1 (100·cMax) · rSupply`。它只比较 `rNext` 与 `rSupply`，**不**给 `rSupply`
相对上一块半径的下界（那条路线不成立，见 `out/CH12X-RSUPPLY-design.md`）。
-/

noncomputable section

namespace GC.LongTime.Ch11

/-- **`rNext ≥ min(1, 100·cMax)·rSupply`**：右边逐字是 astra Step 的 `rNext` 定义。 -/
theorem rNext_ge_min_mul_rSupply_C12X {rSupply Qall cMax : ℝ} (hr : 0 < rSupply)
    (hQ : 0 < Qall) (hc : 0 < cMax) (hQr : Qall ≤ (rSupply ^ 2)⁻¹) :
    min 1 (100 * cMax) * rSupply ≤ min rSupply (100 * cMax / Real.sqrt Qall) := by
  have hs : 0 < Real.sqrt Qall := Real.sqrt_pos.mpr hQ
  have hprod : Real.sqrt Qall * rSupply ≤ 1 := by
    have h1 : Real.sqrt Qall ≤ Real.sqrt ((rSupply ^ 2)⁻¹) := Real.sqrt_le_sqrt hQr
    rw [Real.sqrt_inv, Real.sqrt_sq hr.le] at h1
    calc Real.sqrt Qall * rSupply ≤ rSupply⁻¹ * rSupply :=
          mul_le_mul_of_nonneg_right h1 hr.le
      _ = 1 := inv_mul_cancel₀ hr.ne'
  refine le_min ?_ ?_
  · calc min 1 (100 * cMax) * rSupply ≤ 1 * rSupply :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le
      _ = rSupply := one_mul _
  · rw [le_div_iff₀ hs]
    calc min 1 (100 * cMax) * rSupply * Real.sqrt Qall
        ≤ 100 * cMax * rSupply * Real.sqrt Qall := by
          gcongr
          exact min_le_right _ _
      _ = 100 * cMax * (Real.sqrt Qall * rSupply) := by ring
      _ ≤ 100 * cMax * 1 := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 100 * cMax := mul_one _

end GC.LongTime.Ch11
