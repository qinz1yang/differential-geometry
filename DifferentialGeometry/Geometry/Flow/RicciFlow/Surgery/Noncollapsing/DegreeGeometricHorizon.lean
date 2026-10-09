import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SmallScaleFromDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalFromSmallScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.FiniteGeometricHorizon
set_option autoImplicit false
noncomputable section
open scoped Manifold
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem general_strong_canonical_of_history_degree
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hdegree : ∃ N : ℕ, 0 < N ∧ UniformHistoryDegreeBound P g N) :
    CanonicalNeighborhoodsThroughSurgeryStrong P g := by
  obtain ⟨N,hN,hbound⟩ := hdegree
  exact general_strong_canonical_of_small_scale P g
    (smallScaleNoncollapsingThroughSurgery_of_historyDegreeBound P g N hN hbound)

theorem finite_geometric_horizon_of_history_degree
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hdegree : ∃ N : ℕ, 0 < N ∧ UniformHistoryDegreeBound P g N) (B : ℝ) (hB : 0 < B) :
    ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
      (p : CutoffParameters), K.horizon = B ∧
      (InitialIdentification.atZero P g).IsPrefixOf A ∧
      Nonempty (∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin K.eventCount,
        GC.Surgery.ActualMetricEventGeometry (K.coreEvent i).toMetricCutCapEvent :=
  finite_geometric_horizon P g (general_strong_canonical_of_history_degree P g hdegree) B hB

end GC.GeneralFlow
