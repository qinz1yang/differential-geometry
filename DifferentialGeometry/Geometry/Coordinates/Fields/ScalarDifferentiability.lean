import DifferentialGeometry.Geometry.Coordinates.Fields.Scalar

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

theorem mdifferentiableAt_of_differentiableAt_scalarOnE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {a : M} {z : E} {f : M → ℝ} (hz : z ∈ (extChartAt I a).target)
    (hf : DifferentiableAt ℝ (scalarOnE (I := I) a f) z) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I a).symm z) := by
  have hsource : (extChartAt I a).symm z ∈ (chartAt H a).source := by
    simpa only [extChartAt_source] using (extChartAt I a).map_target hz
  apply (mdifferentiableAt_iff_source_of_mem_source
    (I := I) (I' := 𝓘(ℝ, ℝ)) hsource).mpr
  have hf' : DifferentiableAt ℝ (f ∘ (extChartAt I a).symm) z := hf
  simpa only [(extChartAt I a).right_inv hz] using
    hf'.mdifferentiableAt.mdifferentiableWithinAt

end DifferentialGeometry.Tensor.Coordinates
