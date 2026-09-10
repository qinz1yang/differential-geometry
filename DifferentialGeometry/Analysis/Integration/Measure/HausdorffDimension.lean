import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
namespace Poincare.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem addHaar_eq_zero_of_dimH_lt (μ : Measure E) [IsAddHaarMeasure μ]
    {s : Set E} (hs : dimH s < Module.finrank ℝ E) : μ s = 0 := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  have hdim : dimH (e '' s) < Module.finrank ℝ E := by
    rw [e.dimH_image]
    exact hs
  have hn : volume (e '' s) = 0 := by
    have hd : dimH (e '' s) < (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ≥0) := by
      simpa using hdim
    simpa only [NNReal.coe_natCast, hausdorffMeasure_pi_real] using hausdorffMeasure_of_dimH_lt hd
  have he : IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  have hn' := absolutelyContinuous_isAddHaarMeasure (μ.map e) volume hn
  exact le_antisymm
    ((le_map_apply_image e.continuous.measurable.aemeasurable s).trans_eq hn') zero_le

end Poincare.MeasureTheory
