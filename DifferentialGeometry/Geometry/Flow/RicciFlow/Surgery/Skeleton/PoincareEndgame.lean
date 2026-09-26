import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PinchingThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves


set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem uniformDebitSurgeryStep (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStep P₀ g₀ := by
  sorry

theorem noncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    NoncollapsingThroughSurgery P₀ g₀ := by
  sorry

theorem deepContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    DeepContinuation P₀ g₀ := by
  sorry

theorem capWindowContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CapWindowContinuation P₀ g₀ := by
  sorry

theorem crossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CrossingContinuation P₀ g₀ := by
  sorry

theorem canonicalNeighborhoodContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CanonicalNeighborhoodContinuation P₀ g₀ :=
  canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing P₀ g₀
    (deepContinuation P₀ g₀) (capWindowContinuation P₀ g₀) (crossingContinuation P₀ g₀)

theorem canonicalNeighborhoodsThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CanonicalNeighborhoodsThroughSurgery P₀ g₀ :=
  canonicalNeighborhoodsThroughSurgery_of_continuation_of_noncollapsing_of_pinching P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (noncollapsingThroughSurgery P₀ g₀)
    (canonicalNeighborhoodContinuation P₀ g₀)

theorem smoothPoincareConjecture_holds : smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods
    uniformDebitSurgeryStep canonicalNeighborhoodsThroughSurgery

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
