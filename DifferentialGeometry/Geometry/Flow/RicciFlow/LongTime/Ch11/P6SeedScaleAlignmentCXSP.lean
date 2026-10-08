import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

/-!
# CX-SPINE G32：primary 与 auxiliary seed 尺度的准确对应

保留 Qbase=chi*Qaux，scalar convergence 要求精度 1/chi 才给 auxiliary 宽度 1 的 ratio band。
时间窗口包含不提升 Full Good 的曲率 threshold；Qaux/2 仍独立保留。
-/

open Filter
open scoped Topology

namespace GC.LongTime.Ch11

/-- 同一 seed 半径下，两种固定曲率常数给准确比例，不要求两尺度相等。 -/
theorem seed_primary_aux_scale_CXSP {Hbase Haux r : ℝ} (haux : 0 < Haux) :
    Hbase * (r ^ 2)⁻¹ = (Hbase / Haux) * (Haux * (r ^ 2)⁻¹) := by
  field_simp

/-- primary scalar 精度 1/chi 生产 auxiliary level=chi*L 的严格双侧 band。 -/
theorem auxiliary_scalar_band_CXSP {χ Qaux Rn L : ℝ} (hχ : 0 < χ) (hQ : 0 < Qaux)
    (herr : |Rn / (χ * Qaux) - L| < 1 / χ) :
    Qaux * (χ * L - 1) < Rn ∧ Rn < Qaux * (χ * L + 1) := by
  have heq : Rn / Qaux - χ * L = χ * (Rn / (χ * Qaux) - L) := by
    field_simp
  have hsmall : |Rn / Qaux - χ * L| < 1 := by
    rw [heq, abs_mul, abs_of_pos hχ]
    have hh := mul_lt_mul_of_pos_left herr hχ
    simpa only [mul_one_div_cancel hχ.ne'] using hh
  have hlo : χ * L - 1 < Rn / Qaux := by linarith [(abs_lt.mp hsmall).1]
  have hhi : Rn / Qaux < χ * L + 1 := by linarith [(abs_lt.mp hsmall).2]
  constructor
  · have hh := (lt_div_iff₀ hQ).mp hlo
    nlinarith only [hh]
  · have hh := (div_lt_iff₀ hQ).mp hhi
    nlinarith only [hh]

/-- auxiliary clock 改写到 primary 單位，保留准确 chi 因子。 -/
theorem auxiliary_window_primary_clock_CXSP {χ Qaux C L β0 : ℝ}
    (hχ : 0 < χ) (hQ : 0 < Qaux) :
    (β0 / (C * (χ * L) + 1)) / Qaux =
      (χ * β0 / (C * (χ * L) + 1)) / (χ * Qaux) := by
  field_simp

/-- 固定 positive primary Good 深度后，大 level 的 auxiliary 窗口位于该时间域。 -/
theorem eventually_auxiliary_window_fits_CXSP {χ C β0 βbase : ℝ}
    (hχ : 0 < χ) (hC : 0 < C) (hbase : 0 < βbase)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    ∀ᶠ j in atTop, χ * β0 / (C * (χ * L j) + 1) ≤ βbase := by
  let B := max 1 ((χ * β0) / (βbase * (C * χ)))
  filter_upwards [hL.eventually_ge_atTop B] with j hj
  have hLj : 1 ≤ L j := (le_max_left _ _).trans hj
  have hden : 0 < C * (χ * L j) + 1 := by positivity
  have hbound : χ * β0 ≤ L j * (βbase * (C * χ)) :=
    (div_le_iff₀ (mul_pos hbase (mul_pos hC hχ))).mp ((le_max_right _ _).trans hj)
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hbound, hbase]

end GC.LongTime.Ch11
