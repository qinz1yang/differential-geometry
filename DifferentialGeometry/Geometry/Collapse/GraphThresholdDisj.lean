import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem exists_closed_graph_threshold_disj (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean :=
  exists_closed_graph_threshold_disj_of_finite_scales_disj
    (exists_closed_graph_threshold_of_finite_scales_disj K hK A hA)

theorem exists_graph_threshold_disj (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_closed_disj (exists_closed_graph_threshold_disj K hK A hA)
    (exists_boundary_graph_threshold K hK A hA)

end DifferentialGeometry.Geometry.Collapse
