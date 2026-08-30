import DifferentialGeometry.Analysis.Integration.Measure.ChartNull
import DifferentialGeometry.Geometry.Boundary.ModelBoundary

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem modelHaar_frontier_range_eq_zero [HasSmoothBoundary E H I] :
    modelHaar (E := E) (frontier (Set.range I)) = 0 := by
  let μ : Measure E := (Module.finBasis ℝ E).addHaar
  have hμ : μ (frontier (Set.range I)) = 0 := by
    exact HasSmoothBoundary.range_frontier_basisAddHaar_volume_zero I
  have hac : modelHaar (E := E) ≪ μ :=
    Measure.absolutelyContinuous_isAddHaarMeasure (modelHaar (E := E)) μ
  exact hac hμ

theorem riemannianVolumeMeasure_boundary_eq_zero
    [T2Space M] [CompactSpace M] [HasSmoothBoundary E H I]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g (I.boundary M) = 0 := by
  classical
  obtain ⟨s, hs⟩ := finite_chart_cover (H := H) (M := M)
  apply null_of_chart_cover (H := H)
    (riemannianVolumeMeasure (I := I) (M := M) g) (I.boundary M) s
  · rw [hs]
    exact subset_univ _
  · intro x hx
    have hchart := chart_model_null (I := I) (M := M) g x
      (measure_mono_null inter_subset_left
        (modelHaar_frontier_range_eq_zero (I := I)))
    apply measure_mono_null _ hchart
    intro y hy
    constructor
    · exact hy.2
    change (extChartAt I x) y ∈ frontier (Set.range I)
    have hy_boundary : I.IsBoundaryPoint y := hy.1
    have hy_frontier :
        (extChartAt I x) y ∈ frontier (extChartAt I x).target :=
      (I.isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
        (chart_mem_atlas H x) hy.2).mp hy_boundary
    have hy_source : y ∈ (extChartAt I x).source := by
      rw [extChartAt_source]
      exact hy.2
    have hy_target : (extChartAt I x) y ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hy_source
    rw [mem_frontier_iff_notMem_interior
      (OpenPartialHomeomorph.extend_target_subset_range (chartAt H x) hy_target)]
    intro hy_interior
    have hy_chart_target : (chartAt H x) y ∈ (chartAt H x).target :=
      (chartAt H x).map_source hy.2
    have hy_extend_interior :
        (extChartAt I x) y ∈ interior (extChartAt I x).target := by
      change I ((chartAt H x) y) ∈ interior ((chartAt H x).extend I).target
      exact (chartAt H x).mem_interior_extend_target hy_chart_target hy_interior
    exact (mem_frontier_iff_notMem_interior hy_target).mp hy_frontier hy_extend_interior

end Measure
end Integral
end DifferentialGeometry
