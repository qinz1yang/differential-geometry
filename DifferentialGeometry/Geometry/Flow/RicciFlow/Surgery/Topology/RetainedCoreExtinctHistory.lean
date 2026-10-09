import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_poincare_controlled_extinction_of_retainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (H : RetainedCoreHistory.{u})
    (A : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory)
    (hbfr : ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing)
    (hctrl : ∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  letI : Nonempty
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Carrier :=
    inferInstanceAs (Nonempty M.Carrier)
  exists_poincare_controlled_extinction_of_observedHistory
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory A
    (fun i => (RetainedCoreEvent.toMetricCutCapEvent_hasCutCapCompletion (H.coreEvent i)
      (hbfr i)).some)
    (fun i =>
      RetainedCoreEvent.toMetricCutCapEvent_coreInclusionIsSmoothEmbedding (H.coreEvent i))
    (fun i => hctrl i)
    hempty

theorem RetainedCoreHistory.eventCount_pos_of_final_empty {P : OrientedThreeStage.{u}}
    {g : P.Metric} [Nonempty P.Carrier] (H : RetainedCoreHistory.{u})
    (A : InitialIdentification P g H.toHistory)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) : 0 < H.eventCount :=
  @ObservedHistory.eventCount_pos_of_final_empty H.toHistory A.initial_nonempty hempty

namespace ObservedHistory

theorem isEmpty_stage_last_of_restrict_last {H : ObservedHistory.{u}}
    (t : Icc (0 : ℝ) H.horizon)
    (h : IsEmpty ((H.restrict t).stage (Fin.last (H.restrict t).eventCount)).Carrier) :
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
  have he : (H.restrict t).stage (Fin.last (H.restrict t).eventCount) =
      H.stage (H.activeStage t) := rfl
  rw [he] at h
  have hlast : H.activeStage t = Fin.last H.eventCount := H.empty_stage_is_last (H.activeStage t)
  rw [hlast] at h
  exact h

end ObservedHistory

def HasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ (H : RetainedCoreHistory.{u})
    (_ : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory),
    (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
    (∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

theorem exists_poincare_controlled_extinction_of_hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) := by
  obtain ⟨H, A, hbfr, hctrl, hempty⟩ := h
  exact exists_poincare_controlled_extinction_of_retainedCoreHistory M g H A hbfr hctrl hempty

theorem RetainedCoreObservationTower.hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (hextinct : towerExtinct T.toObservationTower) :
    HasExtinctRetainedCoreHistory M g := by
  obtain ⟨b, hb, hempty⟩ := hextinct
  refine ⟨T.history (Nat.ceil b), T.initial (Nat.ceil b), ?_, ?_, ?_⟩
  · intro i
    exact hbfr (Nat.ceil b) i
  · intro i
    exact hctrl (Nat.ceil b) i
  · refine ObservedHistory.isEmpty_stage_last_of_restrict_last
      (H := (T.history (Nat.ceil b)).toHistory) ?_ ?_
    · refine ⟨b, hb, ?_⟩
      change b ≤ (T.history (Nat.ceil b)).horizon
      rw [T.horizon_eq]
      exact Nat.le_ceil b
    · simpa only [ObservationTower.observe, ObservationTower.atIndex,
        RetainedCoreObservationTower.toObservationTower] using hempty

theorem exists_retainedCoreHistory_extinct_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    ∃ (H : RetainedCoreHistory.{u}) (_ : InitialIdentification P g H.toHistory),
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
  refine ⟨(RetainedCoreObservationTower.empty P g).history 0,
    (RetainedCoreObservationTower.empty P g).initial 0, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g 0) i)
  · intro i
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g 0) i)
  · have hstage : ((RetainedCoreObservationTower.empty P g).history 0).stage
        (Fin.last ((RetainedCoreObservationTower.empty P g).history 0).eventCount) = P := rfl
    rw [hstage]
    exact hP

theorem not_isEmpty_carrier_of_connectedClosedOrientedManifold
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) :
    ¬ IsEmpty M.Carrier :=
  not_isEmpty_iff.mpr inferInstance

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
