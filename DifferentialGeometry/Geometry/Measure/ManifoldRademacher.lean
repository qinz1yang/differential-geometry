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

theorem riemannianVolumeMeasure_nondiff_null_on
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ α : M, LocallyLipschitzOn
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' U)
      (f ∘ (extChartAt I α).symm)) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {x : M | x ∈ U ∧ ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} = 0 := by
  change riemannianMeasure (I := I) g (chartAtlasPOU I M) _ = 0
  apply DifferentialGeometry.Geometry.Measure.riemannianMeasure_null_of_chartLocalMeasure
  intro α
  apply DifferentialGeometry.Geometry.Measure.chartLocalMeasure_null_of_chart_image_null
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [local_diff_ae (hf α)] with y hy
  rintro ⟨x, ⟨⟨hxU, hx⟩, hxs⟩, rfl⟩
  have hxt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by simpa only [extChartAt_source] using hxs)
  have hxext : x ∈ (extChartAt I α).source := by simpa only [extChartAt_source] using hxs
  have hpre : extChartAt I α x ∈ (extChartAt I α).symm ⁻¹' U := by
    change (extChartAt I α).symm (extChartAt I α x) ∈ U
    rwa [(extChartAt I α).left_inv hxext]
  have hn : (extChartAt I α).symm ⁻¹' U ∈ 𝓝[(extChartAt I α).target] (extChartAt I α x) :=
    (continuousOn_extChartAt_symm (I := I) α (extChartAt I α x) hxt).preimage_mem_nhdsWithin
      (hU.mem_nhds hpre)
  have hdiff := (hy ⟨hxt, hpre⟩).congr_nhds (nhdsWithin_inter_of_mem' hn)
  have hdiff' := hdiff.congr_nhds (nhdsWithin_extChartAt_target_eq_of_mem hxt)
  apply hx
  rw [mdifferentiableAt_iff_source_of_mem_source hxs,
    mdifferentiableWithinAt_iff_differentiableWithinAt]
  exact hdiff'

theorem riemannianVolumeMeasure_nondiff_null
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ∀ α : M, LocallyLipschitzOn (extChartAt I α).target
      (f ∘ (extChartAt I α).symm)) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} = 0 := by
  have hn := riemannianVolumeMeasure_nondiff_null_on g f (U := univ) isOpen_univ
    (by simpa only [preimage_univ, inter_univ] using hf)
  simpa only [mem_univ, true_and] using hn

end DifferentialGeometry.Geometry.Measure

end
