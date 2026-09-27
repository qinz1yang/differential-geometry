import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set



noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis



theorem exists_smooth_nonneg_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {s : Set E} (hs : IsOpen s) (hne : s.Nonempty) {mass : ℝ} (hmass : 0 < mass) :
    ∃ κ : E → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ s ∧
      (∀ z, 0 ≤ κ z) ∧ (∫ z, κ z ∂μ) = mass := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨f, hfs, hfc, hf, hrange, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hs.mem_nhds hx)
  have hn (z : E) : 0 ≤ f z := (hrange (mem_range_self z)).1
  have hpos : 0 < ∫ z, f z ∂μ :=
    hf.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hn (by rw [hfx]; norm_num)
  refine ⟨fun z => (mass / ∫ z, f z ∂μ) * f z,
    contDiff_const.mul hf, hfc.mul_left, tsupport_mul_subset_right.trans hfs,
    fun z => mul_nonneg (div_nonneg hmass.le hpos.le) (hn z), ?_⟩
  rw [integral_const_mul]
  exact div_mul_cancel₀ mass hpos.ne'

end DifferentialGeometry.Analysis
