import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralInitialBound
set_option autoImplicit false
noncomputable section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u

theorem general_small_scale_noncollapsing (P : OrientedThreeStage.{u}) (g : P.Metric) :
    SmallScaleNoncollapsingThroughSurgery P g := by
  obtain ⟨N, hN, hb⟩ := general_uniform_history_degree P g
  exact smallScaleNoncollapsingThroughSurgery_of_historyDegreeBound P g N hN hb

theorem general_strong_canonical (P : OrientedThreeStage.{u}) (g : P.Metric) :
    CanonicalNeighborhoodsThroughSurgeryStrong P g :=
  general_strong_canonical_of_small_scale P g (general_small_scale_noncollapsing P g)

theorem general_finite_geometric_horizon
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
      (p : CutoffParameters), K.horizon = B ∧
      (InitialIdentification.atZero P g).IsPrefixOf A ∧
      Nonempty (∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin K.eventCount,
        GC.Surgery.ActualMetricEventGeometry (K.coreEvent i).toMetricCutCapEvent :=
  finite_geometric_horizon P g (general_strong_canonical P g) B hB

end GC.GeneralFlow
