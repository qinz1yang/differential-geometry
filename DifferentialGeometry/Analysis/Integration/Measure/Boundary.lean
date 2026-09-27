import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Geometry.Boundary.Model.Basic

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

theorem chartLocalMeasure_boundary_eq_zero [HasSmoothBoundary E H I]
    (g : SmoothRiemannianMetric I M) (α : M) : chartLocalMeasure g α (I.boundary M) = 0 := by
  have hb : MeasurableSet (I.boundary M) := (I.isClosed_boundary (by simp : (∞ : WithTop ℕ∞) ≠ 0)).measurableSet
  rw [chartLocalMeasure_def, Measure.map_apply_of_aemeasurable
    ((aemeasurable_extChartAt_symm_restrict_target α).mono_ac
      (withDensity_absolutelyContinuous _ _)) hb]
  apply withDensity_absolutelyContinuous _ _
  rw [Measure.restrict_apply' (measurableSet_extChartAt_target α)]
  have hsub : (extChartAt I α).symm ⁻¹' I.boundary M ∩ (extChartAt I α).target ⊆
      frontier (range I) := by
    intro z hz
    have hs := (extChartAt I α).map_target hz.2
    have hf := (I.isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas H α) (by simpa only [extChartAt_source] using hs)).mp hz.1
    change (extChartAt I α) ((extChartAt I α).symm z) ∈ frontier (extChartAt I α).target at hf
    rw [(extChartAt I α).right_inv hz.2] at hf
    rw [mem_frontier_iff_notMem_interior (extChartAt_target_subset_range α hz.2)]
    intro hint
    have hchart : (chartAt H α) ((extChartAt I α).symm z) ∈ (chartAt H α).target :=
      (chartAt H α).map_source (by simpa only [extChartAt_source] using hs)
    have hval : I ((chartAt H α) ((extChartAt I α).symm z)) = z :=
      (extChartAt I α).right_inv hz.2
    have hint' := (chartAt H α).mem_interior_extend_target hchart (hval.symm ▸ hint)
    rw [hval] at hint'
    exact (mem_frontier_iff_notMem_interior hz.2).mp hf hint'
  exact measure_mono_null hsub (modelHaar_frontier_range_eq_zero (I := I))

theorem riemannianVolumeMeasure_boundary_eq_zero
    [T2Space M] [SigmaCompactSpace M] [HasSmoothBoundary E H I]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g (I.boundary M) = 0 := by
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def, Measure.sum_apply]
  · apply ENNReal.tsum_eq_zero.mpr
    intro α
    exact withDensity_absolutelyContinuous _ _ (chartLocalMeasure_boundary_eq_zero g α)
  · exact (I.isClosed_boundary (by simp : (∞ : WithTop ℕ∞) ≠ 0)).measurableSet

end Measure
end Integral
end DifferentialGeometry
