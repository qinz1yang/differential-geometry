import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood
import DifferentialGeometry.Geometry.Metric.Distance.Completion

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_exists_sphere_point_near_endpoint (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (x : W) {rho : ℝ} (hrho : 0 ≤ rho)
    (hr : rho < dist (x : UniformSpace.Completion W) H.endpoint) :
    ∃ y : W, dist x y = rho ∧
      dist (y : UniformSpace.Completion W) H.endpoint <
        2 * (dist (x : UniformSpace.Completion W) H.endpoint - rho) := by
  exact Geometry.exists_sphere_point_near_completion_point g
    (fun x y => (edist_dist x y).trans (edist_eq_ofReal_dist g H x y).symm)
    H.endpoint x hrho hr

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
