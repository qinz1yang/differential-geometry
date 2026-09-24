import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {X F : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup F] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem ContinuousOn.memLp_restrict_compact {S : Set X} (hS : IsCompact S)
    {f : X → F} (hf : ContinuousOn f S) (p : ℝ≥0∞) : MemLp f p (μ.restrict S) := by
  let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf
  apply MemLp.of_bound (hf.aestronglyMeasurable_of_isCompact hS hS.measurableSet) C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx

end MeasureTheory

end
