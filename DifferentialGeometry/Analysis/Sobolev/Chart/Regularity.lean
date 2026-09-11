import DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison

noncomputable section

open Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

private theorem contMDiffAt_of_chart_regularities
    {α x : M} (hx : x ∈ (extChartAt I α).source) {f : M → ℝ}
    (hchart : ContMDiffAt I 𝓘(ℝ, E) n (extChartAt I α) x)
    (hf : ContDiffAt ℝ n (chartPushedRaw I α f)
      (toEuclidean (E := E) (extChartAt I α x))) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n f x := by
  let coord : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun y => toEuclidean (E := E) (extChartAt I α y)
  have hto : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      n (toEuclidean (E := E)) (extChartAt I α x) :=
    contMDiffAt_iff_contDiffAt.mpr (toEuclidean (E := E)).contDiff.contDiffAt
  have hcoord : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      n coord x := hto.comp x hchart
  have hraw : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      𝓘(ℝ, ℝ) n (chartPushedRaw I α f) (coord x) :=
    contMDiffAt_iff_contDiffAt.mpr hf
  refine (hraw.comp x hcoord).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source α).mem_nhds hx] with y hy
  have htarget : coord y ∈ chartTargetEuclid (I := I) α :=
    ⟨extChartAt I α y, (extChartAt I α).map_source hy, rfl⟩
  rw [Function.comp_apply, chartPushedRaw_apply_of_mem α f htarget]
  simp only [coord, ContinuousLinearEquiv.symm_apply_apply, (extChartAt I α).left_inv hy]

theorem contMDiffAt_of_contDiffAt_chartPushedRaw
    (α : M) {f : M → ℝ}
    (hf : ContDiffAt ℝ n (chartPushedRaw I α f)
      (toEuclidean (E := E) (extChartAt I α α))) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n f α :=
  contMDiffAt_of_chart_regularities (mem_extChartAt_source α) contMDiffAt_extChartAt hf

theorem contMDiffAt_of_contDiffAt_chartPushedRaw_of_mem_source
    [IsManifold I n M] {α x : M} (hx : x ∈ (extChartAt I α).source) {f : M → ℝ}
    (hf : ContDiffAt ℝ n (chartPushedRaw I α f)
      (toEuclidean (E := E) (extChartAt I α x))) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n f x :=
  contMDiffAt_of_chart_regularities hx
    (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)) hf

end DifferentialGeometry.Analysis.Sobolev.Chart
