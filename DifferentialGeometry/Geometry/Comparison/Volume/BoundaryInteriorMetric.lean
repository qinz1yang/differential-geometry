import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryMetricChart
import DifferentialGeometry.Topology.Manifold.InteriorChart

/-!
On the genuine interior of an extended chart, its original metric tensor is the pullback
by the actual derivative of the inverse chart, without a boundaryless ambient assumption.
-/

set_option autoImplicit false

noncomputable section

open Manifold Set Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] {H : Type*}
  [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]

theorem boundaryChart_metric_inner_of_interior
    (g : SmoothRiemannianMetric I M) (p : M) {y : E}
    (hy : y ∈ interior (extChartAt I p).target) (v w : E) :
    metricFlatModelInChart g p y v w =
      g.inner ((extChartAt I p).symm y)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y v)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y w) := by
  have hyTarget := interior_subset hy
  have hsource : (extChartAt I p).symm y ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using (extChartAt I p).map_target hyTarget
  have hcoord : extChartAt I p ((extChartAt I p).symm y) = y :=
    (extChartAt I p).right_inv hyTarget
  have hframe := TangentBundle.symmL_trivializationAt (I := I) hsource
  rw [hcoord] at hframe
  have hrange : range I ∈ 𝓝 y :=
    mem_interior_iff_mem_nhds.mp (interior_mono (extChartAt_target_subset_range p) hy)
  rw [mfderivWithin_of_mem_nhds hrange] at hframe
  rw [metricFlatModelInChart_apply_of_target g p hyTarget, hframe]
  rfl

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
