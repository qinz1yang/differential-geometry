import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood
import DifferentialGeometry.Geometry.Metric.Distance.LocalCompletion

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_exists_local_complete_metric
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ p : W,
      dist (p : UniformSpace.Completion W) H.endpoint < d →
      ∃ (g' : SmoothRiemannianMetric I3 W) (r : ℝ) (U : Set W),
        0 < r ∧ RiemannianMetricComplete g' ∧ IsOpen U ∧
        Metric.closedBall p (4 * r) ⊆ U ∧
        (∀ z ∈ U, g'.inner z = g.inner z) ∧
        (∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v) ∧
        ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
          riemannianEDistOf g' x y = ENNReal.ofReal (dist x y) := by
  refine ⟨1, zero_lt_one, fun p _ => ?_⟩
  exact Geometry.exists_riemannianMetricComplete_eqOn_ball g
    (fun x y => (edist_dist x y).trans (edist_eq_ofReal_dist g H x y).symm) p

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
