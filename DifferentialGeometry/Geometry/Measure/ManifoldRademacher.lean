import DifferentialGeometry.Geometry.Measure.ChartNull
import DifferentialGeometry.Analysis.Integration.Measure.Differentiation.Rademacher

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_nondiff_null
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ∀ α : M, LocallyLipschitzOn (extChartAt I α).target
      (f ∘ (extChartAt I α).symm)) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} = 0 := by
  change riemannianMeasure (I := I) g (chartAtlasPOU I M)
    {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} = 0
  apply riemannianMeasure_null_of_chartLocalMeasure
  intro α
  apply chartLocalMeasure_null_of_chart_image_null
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [local_diff_ae (hf α)] with y hy
  rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
  have hxt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by
      simpa only [extChartAt_source] using hxs)
  have hdiff := (hy hxt).congr_nhds
    (nhdsWithin_extChartAt_target_eq_of_mem hxt)
  apply hx
  rw [mdifferentiableAt_iff_source_of_mem_source hxs,
    mdifferentiableWithinAt_iff_differentiableWithinAt]
  exact hdiff

end DifferentialGeometry.Geometry.Measure

end
