import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurgeryContinuationTowerProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

private theorem appendEvent_toHistory_stage_zero (H : RetainedCoreHistory.{u})
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).toHistory.stage 0 = H.toHistory.stage 0 :=
  appendEvent_stage_castSucc H hs E hinit 0

private theorem appendEvent_toHistory_initialMetric_zero_heq (H : RetainedCoreHistory.{u})
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    HEq ((H.appendEvent hs E hinit).toHistory.initialMetric 0) (H.toHistory.initialMetric 0) :=
  appendEvent_initialMetric_castSucc_heq H hs E hinit 0

end RetainedCoreHistory

structure RetainedCoreEventChain (P : OrientedThreeStage.{u}) (g : P.Metric) where
  stage : ℕ → OrientedThreeStage.{u}
  metric : (n : ℕ) → (stage n).Metric
  stage_zero : stage 0 = P
  metric_zero : HEq (metric 0) g
  event : (n : ℕ) → RetainedCoreEvent (stage n) (stage (n + 1)) (n : ℝ) ((n : ℝ) + 1)
  event_initial : ∀ n : ℕ,
    (event n).toMetricCutCapEvent.incoming.flow.base.metric (n : ℝ) = metric n
  event_output : ∀ n : ℕ, (event n).toMetricCutCapEvent.outputMetric = metric (n + 1)

namespace RetainedCoreEventChain

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

private structure AlignedLayer (C : RetainedCoreEventChain P g) (n : ℕ) where
  history : RetainedCoreHistory.{u}
  eventCount_eq : history.eventCount = n
  horizon_eq : history.horizon = (n : ℝ)
  time_last_eq : history.time (Fin.last history.eventCount) = (n : ℝ)
  stage_last_eq : history.stage (Fin.last history.eventCount) = C.stage n
  metric_last_heq : HEq (history.initialMetric (Fin.last history.eventCount)) (C.metric n)
  initial : InitialIdentification P g history.toHistory

private theorem nextTimeLt (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    L.history.time (Fin.last L.history.eventCount) < ((n : ℝ) + 1) := by
  rw [L.time_last_eq]
  exact lt_add_one _

private def nextEvent (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    RetainedCoreEvent (L.history.stage (Fin.last L.history.eventCount)) (C.stage (n + 1))
      (L.history.time (Fin.last L.history.eventCount)) ((n : ℝ) + 1) :=
  RetainedCoreEvent.transport L.stage_last_eq.symm rfl L.time_last_eq.symm rfl (C.event n)

private theorem nextEvent_incoming_heq (C : RetainedCoreEventChain P g) (n : ℕ)
    (L : AlignedLayer C n) :
    HEq ((C.nextEvent n L).toMetricCutCapEvent.incoming.flow.base.metric
        (L.history.time (Fin.last L.history.eventCount)))
      (C.metric n) :=
  (RetainedCoreEvent.transport_incoming_metric_heq L.stage_last_eq.symm rfl
    L.time_last_eq.symm rfl (C.event n)
    (L.history.time (Fin.last L.history.eventCount))).trans
    ((heq_of_eq (congrArg
      (fun t : ℝ => (C.event n).toMetricCutCapEvent.incoming.flow.base.metric t)
      L.time_last_eq)).trans (heq_of_eq (C.event_initial n)))

private theorem nextInit (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextEvent n L).toMetricCutCapEvent.incoming.flow.base.metric
        (L.history.time (Fin.last L.history.eventCount)) =
      L.history.initialMetric (Fin.last L.history.eventCount) :=
  eq_of_heq ((C.nextEvent_incoming_heq n L).trans L.metric_last_heq.symm)

private def nextHistory (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    RetainedCoreHistory.{u} :=
  L.history.appendEvent (C.nextTimeLt n L) (C.nextEvent n L) (C.nextInit n L)

private theorem nextEventCountEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).eventCount = n + 1 := by
  rw [nextHistory, RetainedCoreHistory.appendEvent_eventCount, L.eventCount_eq]

private theorem nextStageZero (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).toHistory.stage 0 = L.history.toHistory.stage 0 :=
  RetainedCoreHistory.appendEvent_toHistory_stage_zero L.history (C.nextTimeLt n L)
    (C.nextEvent n L) (C.nextInit n L)

private theorem nextInitialMetricHeq (C : RetainedCoreEventChain P g) (n : ℕ)
    (L : AlignedLayer C n) :
    HEq ((C.nextHistory n L).toHistory.initialMetric 0) (L.history.toHistory.initialMetric 0) :=
  RetainedCoreHistory.appendEvent_toHistory_initialMetric_zero_heq L.history (C.nextTimeLt n L)
    (C.nextEvent n L) (C.nextInit n L)

private theorem nextHorizonEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).horizon = ((n + 1 : ℕ) : ℝ) := by
  rw [nextHistory, RetainedCoreHistory.appendEvent_horizon]
  push_cast
  ring

private theorem nextTimeLastEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).time (Fin.last (C.nextHistory n L).eventCount) = ((n + 1 : ℕ) : ℝ) := by
  rw [nextHistory]
  change (L.history.appendEvent (C.nextTimeLt n L) (C.nextEvent n L) (C.nextInit n L)).time
    (Fin.last (L.history.eventCount + 1)) = ((n + 1 : ℕ) : ℝ)
  rw [RetainedCoreHistory.appendEvent_time_last]
  push_cast
  ring

private theorem nextStageLastEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).stage (Fin.last (C.nextHistory n L).eventCount) = C.stage (n + 1) :=
  RetainedCoreHistory.appendEvent_stage_last L.history (C.nextTimeLt n L) (C.nextEvent n L)
    (C.nextInit n L)

private theorem nextMetricLastHeq (C : RetainedCoreEventChain P g) (n : ℕ)
    (L : AlignedLayer C n) :
    HEq ((C.nextHistory n L).initialMetric (Fin.last (C.nextHistory n L).eventCount))
      (C.metric (n + 1)) :=
  (RetainedCoreHistory.appendEvent_initialMetric_last_heq L.history (C.nextTimeLt n L)
      (C.nextEvent n L) (C.nextInit n L)).trans
    ((RetainedCoreEvent.transport_outputMetric_heq L.stage_last_eq.symm rfl L.time_last_eq.symm rfl
      (C.event n)).trans (heq_of_eq (C.event_output n)))

private def alignedLayerZero (C : RetainedCoreEventChain P g) : AlignedLayer C 0 where
  history := RetainedCoreHistory.atZero P g
  eventCount_eq := rfl
  horizon_eq := by simp
  time_last_eq := by simp
  stage_last_eq := C.stage_zero.symm
  metric_last_heq := C.metric_zero.symm
  initial := InitialIdentification.atZero P g

private def alignedLayerStep (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    AlignedLayer C (n + 1) where
  history := C.nextHistory n L
  eventCount_eq := C.nextEventCountEq n L
  horizon_eq := C.nextHorizonEq n L
  time_last_eq := C.nextTimeLastEq n L
  stage_last_eq := C.nextStageLastEq n L
  metric_last_heq := C.nextMetricLastHeq n L
  initial := InitialIdentification.ofStageZero L.initial (C.nextStageZero n L)
    (C.nextInitialMetricHeq n L)

private def alignedLayer (C : RetainedCoreEventChain P g) (n : ℕ) : AlignedLayer C n :=
  Nat.rec (alignedLayerZero C) (fun n L => alignedLayerStep C n L) n

private theorem alignedLayer_succ (C : RetainedCoreEventChain P g) (n : ℕ) :
    C.alignedLayer (n + 1) = C.alignedLayerStep n (C.alignedLayer n) := rfl

private theorem alignedLayer_prefix (C : RetainedCoreEventChain P g) (n : ℕ) :
    (C.alignedLayer n).history.toHistory.IsPrefixOf
      (C.alignedLayer (n + 1)).history.toHistory := by
  rw [alignedLayer_succ]
  refine RetainedCoreHistory.appendEvent_isPrefixOf (C.alignedLayer n).history (C.nextTimeLt n _)
    (C.nextEvent n _) (C.nextInit n _) ?_ ?_
  · rw [(C.alignedLayer n).horizon_eq]
    exact lt_add_one _
  · exact RetainedCoreHistory.appendEventCompatible_of_time_eq_horizon _ _
      ((C.alignedLayer n).time_last_eq.trans (C.alignedLayer n).horizon_eq.symm)

private theorem alignedLayer_initial_map_heq (C : RetainedCoreEventChain P g) (n : ℕ) :
    HEq ((C.alignedLayer (n + 1)).initial.map) ((C.alignedLayer n).initial.map) := by
  exact InitialIdentification.map_of_stageZero_heq (C.alignedLayer n).initial
    (C.nextStageZero n (C.alignedLayer n)) (C.nextInitialMetricHeq n (C.alignedLayer n))

def toRetainedCoreObservationTower (C : RetainedCoreEventChain P g) :
    RetainedCoreObservationTower P g where
  history n := (C.alignedLayer n).history
  horizon_eq n := (C.alignedLayer n).horizon_eq
  initial n := (C.alignedLayer n).initial
  successor n := by
    have hpref := C.alignedLayer_prefix n
    have hsp := hpref.presentation
    have hpoint : (⟨(C.alignedLayer n).history.horizon,
        (C.alignedLayer n).history.horizon_nonneg, hpref.horizon_le⟩
        : Icc (0 : ℝ) (C.alignedLayer (n + 1)).history.horizon) =
        ⟨(n : ℝ), Nat.cast_nonneg n, by
          have h : (n : ℝ) ≤ (C.alignedLayer (n + 1)).history.horizon := by
            rw [(C.alignedLayer (n + 1)).horizon_eq]
            exact_mod_cast Nat.le_succ n
          simpa using h⟩ :=
      Subtype.ext (C.alignedLayer n).horizon_eq
    rw [hpoint] at hsp
    exact hsp
  initial_successor n :=
    (heq_of_eq (InitialIdentification.restrict_map (C.alignedLayer (n + 1)).initial
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        have h : (n : ℝ) ≤ (C.alignedLayer (n + 1)).history.horizon := by
          rw [(C.alignedLayer (n + 1)).horizon_eq]
          exact_mod_cast Nat.le_succ n
        simpa using h⟩)).trans (C.alignedLayer_initial_map_heq n)

theorem toRetainedCoreObservationTower_history_eventCount (C : RetainedCoreEventChain P g)
    (n : ℕ) : (C.toRetainedCoreObservationTower.history n).eventCount = n :=
  (C.alignedLayer n).eventCount_eq

theorem toRetainedCoreObservationTower_history_stage_last (C : RetainedCoreEventChain P g)
    (n : ℕ) :
    (C.toRetainedCoreObservationTower.history n).stage
        (Fin.last (C.toRetainedCoreObservationTower.history n).eventCount) = C.stage n :=
  (C.alignedLayer n).stage_last_eq

theorem toRetainedCoreObservationTower_history_time_last_eq_horizon
    (C : RetainedCoreEventChain P g) (n : ℕ) :
    (C.toRetainedCoreObservationTower.history n).time
        (Fin.last (C.toRetainedCoreObservationTower.history n).eventCount) =
      (C.toRetainedCoreObservationTower.history n).horizon :=
  ((C.alignedLayer n).time_last_eq.trans (C.alignedLayer n).horizon_eq.symm)

end RetainedCoreEventChain

theorem hasSurgeryContinuationTower_of_retainedCoreEventChain {P : OrientedThreeStage.{u}}
    {g : P.Metric} (C : RetainedCoreEventChain P g)
    (hrecords : C.toRetainedCoreObservationTower.HasUniformCutoffRecords)
    (hbfr : C.toRetainedCoreObservationTower.hasBoundaryFrameReversing)
    (hctrl : C.toRetainedCoreObservationTower.hasPoincareStandardDiscarded) :
    HasSurgeryContinuationTower P g :=
  hasSurgeryContinuationTower_of_uniformCutoffRecords C.toRetainedCoreObservationTower
    hrecords hbfr hctrl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
