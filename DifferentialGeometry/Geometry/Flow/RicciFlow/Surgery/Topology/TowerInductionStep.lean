import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctEventModelConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurgeryContinuationTowerProducer

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem heq_apply_of_eq {α : Sort*} {β : α → Sort*} (f : (a : α) → β a) {a b : α}
    (h : a = b) : HEq (f a) (f b) := by
  cases h
  exact HEq.rfl

namespace MetricCutCapEvent

theorem heq_transport {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s) :
    HEq (MetricCutCapEvent.transport hP hQ ha hs E) E := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact HEq.rfl

theorem heq_incomingMetric {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (h : HEq E F) (τ : ℝ) :
    HEq (E.incoming.flow.base.metric τ) (F.incoming.flow.base.metric τ) := by
  cases h
  exact HEq.rfl

namespace SamePresentation

theorem of_eq {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (h : E = F) : E.SamePresentation F :=
  h ▸ MetricCutCapEvent.SamePresentation.refl E

theorem of_heq_of_eq {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s') (h : HEq E F) :
    E.SamePresentation F := by
  have h1 : MetricCutCapEvent.transport hP.symm hQ.symm ha.symm hs.symm F = E :=
    eq_of_heq ((MetricCutCapEvent.heq_transport hP.symm hQ.symm ha.symm hs.symm F).trans h.symm)
  rw [← h1]
  exact MetricCutCapEvent.transport_samePresentation hP.symm hQ.symm ha.symm hs.symm F

end SamePresentation

end MetricCutCapEvent

namespace ObservedHistory

theorem stageMetric_castSucc_apply {H : ObservedHistory.{u}} (i : Fin H.eventCount) (t : ℝ) :
    H.stageMetric i.castSucc t = (H.event i).incoming.flow.base.metric t := by
  rw [ObservedHistory.stageMetric]
  simp only [Fin.lastCases_castSucc]

end ObservedHistory

namespace RetainedCoreEvent

variable {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}

def transport (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s) : RetainedCoreEvent P' Q' a' s' := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact E

theorem transport_toMetricCutCapEvent (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s) :
    (transport hP hQ ha hs E).toMetricCutCapEvent =
      MetricCutCapEvent.transport hP hQ ha hs E.toMetricCutCapEvent := by
  cases hP
  cases hQ
  cases ha
  cases hs
  rfl

theorem transport_incoming_metric_heq (hP : P = P') (hQ : Q = Q') (ha : a = a')
    (hs : s = s') (E : RetainedCoreEvent P Q a s) (u : ℝ) :
    HEq ((transport hP hQ ha hs E).incoming.flow.base.metric u)
      (E.incoming.flow.base.metric u) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact HEq.rfl

theorem transport_outputMetric_heq (hP : P = P') (hQ : Q = Q') (ha : a = a')
    (hs : s = s') (E : RetainedCoreEvent P Q a s) :
    HEq (transport hP hQ ha hs E).outputMetric E.outputMetric := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact HEq.rfl

end RetainedCoreEvent

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}}

def extendCoreEventLast (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) :
    RetainedCoreEvent
      ((H.toHistory).extendStage Q E.outputMetric (Fin.last H.eventCount).castSucc)
      ((H.toHistory).extendStage Q E.outputMetric (Fin.last H.eventCount).succ)
      ((H.toHistory).extendTime s (Fin.last H.eventCount).castSucc)
      ((H.toHistory).extendTime s (Fin.last H.eventCount).succ) :=
  RetainedCoreEvent.transport
    (ObservedHistory.extendStage_castSucc H.toHistory Q E.outputMetric
      (Fin.last H.eventCount)).symm
    (ObservedHistory.extendStage_last H.toHistory Q E.outputMetric).symm
    (ObservedHistory.extendTime_castSucc H.toHistory s (Fin.last H.eventCount)).symm
    (ObservedHistory.extendTime_last H.toHistory s).symm E

def extendCoreEventCast (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) (i : Fin H.eventCount) :
    RetainedCoreEvent
      ((H.toHistory).extendStage Q E.outputMetric (i.castSucc).castSucc)
      ((H.toHistory).extendStage Q E.outputMetric (i.castSucc).succ)
      ((H.toHistory).extendTime s (i.castSucc).castSucc)
      ((H.toHistory).extendTime s (i.castSucc).succ) :=
  RetainedCoreEvent.transport
    (ObservedHistory.extendStage_castSucc H.toHistory Q E.outputMetric (i.castSucc)).symm
    (ObservedHistory.extendStage_castSucc H.toHistory Q E.outputMetric i.succ).symm
    (ObservedHistory.extendTime_castSucc H.toHistory s (i.castSucc)).symm
    (ObservedHistory.extendTime_castSucc H.toHistory s i.succ).symm (H.coreEvent i)

def extendCoreEventFamily (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) :
    (e : Fin (H.eventCount + 1)) →
      RetainedCoreEvent ((H.toHistory).extendStage Q E.outputMetric e.castSucc)
        ((H.toHistory).extendStage Q E.outputMetric e.succ)
        ((H.toHistory).extendTime s e.castSucc) ((H.toHistory).extendTime s e.succ) :=
  Fin.lastCases (H.extendCoreEventLast E) (fun i => H.extendCoreEventCast E i)

theorem extendCoreEventFamily_castSucc (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) (i : Fin H.eventCount) :
    H.extendCoreEventFamily E i.castSucc = H.extendCoreEventCast E i :=
  Fin.lastCases_castSucc i

theorem extendCoreEventFamily_last (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) :
    H.extendCoreEventFamily E (Fin.last H.eventCount) = H.extendCoreEventLast E :=
  Fin.lastCases_last

def appendEvent (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) : RetainedCoreHistory P where
  horizon := s
  horizon_nonneg := (ObservedHistory.time_nonneg (H.toHistory) (Fin.last H.eventCount)).trans hs.le
  eventCount := H.eventCount + 1
  time := (H.toHistory).extendTime s
  time_strictMono := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [ObservedHistory.extendTime_castSucc, ObservedHistory.extendTime_castSucc]
        exact H.time_strictMono (Fin.castSucc_lt_castSucc_iff.mp hij)
      · rw [ObservedHistory.extendTime_castSucc, ObservedHistory.extendTime_last]
        exact lt_of_le_of_lt (H.time_strictMono.monotone (Fin.le_last i')) hs
    · exact absurd hij (not_lt_of_ge (Fin.le_last j))
  time_zero := by
    have h0 : (0 : Fin (H.eventCount + 2)) = (0 : Fin (H.eventCount + 1)).castSucc := rfl
    rw [h0, ObservedHistory.extendTime_castSucc]
    exact H.time_zero
  time_le_horizon := by rw [ObservedHistory.extendTime_last]
  stage := (H.toHistory).extendStage Q E.outputMetric
  initialMetric := (H.toHistory).extendMetric Q E.outputMetric
  coreEvent := H.extendCoreEventFamily E
  event_initial := by
    intro e
    cases e using Fin.lastCases with
    | cast i =>
      rw [extendCoreEventFamily_castSucc, extendCoreEventCast,
        RetainedCoreEvent.transport_toMetricCutCapEvent]
      refine eq_of_heq ?_
      have htime : ((H.toHistory).event i).incoming.flow.base.metric
            ((H.toHistory).extendTime s (i.castSucc).castSucc) =
          ((H.toHistory).event i).incoming.flow.base.metric (H.time i.castSucc) := by
        rw [ObservedHistory.extendTime_castSucc (H.toHistory) s (i.castSucc)]
      exact (MetricCutCapEvent.transport_incoming_metric_heq _ _ _ _ ((H.toHistory).event i)
          ((H.toHistory).extendTime s (i.castSucc).castSucc)).trans
        ((heq_of_eq htime).trans ((heq_of_eq (H.event_initial i)).trans
          (ObservedHistory.extendMetric_castSucc_heq (H.toHistory) Q E.outputMetric
            (i.castSucc)).symm))
    | last =>
      rw [extendCoreEventFamily_last, extendCoreEventLast,
        RetainedCoreEvent.transport_toMetricCutCapEvent]
      refine eq_of_heq ?_
      have htime : E.toMetricCutCapEvent.incoming.flow.base.metric
            ((H.toHistory).extendTime s (Fin.last H.eventCount).castSucc) =
          E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) := by
        rw [ObservedHistory.extendTime_castSucc (H.toHistory) s (Fin.last H.eventCount)]
      exact (MetricCutCapEvent.transport_incoming_metric_heq _ _ _ _ E.toMetricCutCapEvent
          ((H.toHistory).extendTime s (Fin.last H.eventCount).castSucc)).trans
        ((heq_of_eq htime).trans ((heq_of_eq hinit).trans
          (ObservedHistory.extendMetric_castSucc_heq (H.toHistory) Q E.outputMetric
            (Fin.last H.eventCount)).symm))
  event_output := by
    intro e
    cases e using Fin.lastCases with
    | cast i =>
      rw [extendCoreEventFamily_castSucc, extendCoreEventCast,
        RetainedCoreEvent.transport_toMetricCutCapEvent]
      refine eq_of_heq ?_
      exact (MetricCutCapEvent.transport_outputMetric_heq _ _ _ _ ((H.toHistory).event i)).trans
        ((heq_of_eq (H.event_output i)).trans
          (ObservedHistory.extendMetric_castSucc_heq (H.toHistory) Q E.outputMetric
            i.succ).symm)
    | last =>
      rw [extendCoreEventFamily_last, extendCoreEventLast,
        RetainedCoreEvent.transport_toMetricCutCapEvent]
      refine eq_of_heq ?_
      exact (MetricCutCapEvent.transport_outputMetric_heq _ _ _ _ E.toMetricCutCapEvent).trans
        (ObservedHistory.extendMetric_last_heq (H.toHistory) Q E.outputMetric).symm
  finalSlab := fun h => absurd (by rw [ObservedHistory.extendTime_last] at h; exact h) (lt_irrefl s)
  final_initial := fun h =>
    False.elim (absurd (by rw [ObservedHistory.extendTime_last] at h; exact h) (lt_irrefl s))

theorem appendEvent_horizon (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).horizon = s := rfl

theorem appendEvent_eventCount (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).eventCount = H.eventCount + 1 := rfl

theorem appendEvent_time_apply (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (j : Fin (H.eventCount + 2)) :
    (H.appendEvent hs E hinit).time j = (H.toHistory).extendTime s j := rfl

theorem appendEvent_time_castSucc (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}}
    {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    (H.appendEvent hs E hinit).time i.castSucc = H.time i := by
  rw [appendEvent_time_apply, ObservedHistory.extendTime_castSucc]

theorem appendEvent_time_last (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).time (Fin.last (H.eventCount + 1)) = s := by
  rw [appendEvent_time_apply, ObservedHistory.extendTime_last]

theorem appendEvent_stage_apply (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (j : Fin (H.eventCount + 2)) :
    (H.appendEvent hs E hinit).stage j = (H.toHistory).extendStage Q E.outputMetric j := rfl

theorem appendEvent_stage_castSucc (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}}
    {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    (H.appendEvent hs E hinit).stage i.castSucc = H.stage i := by
  rw [appendEvent_stage_apply, ObservedHistory.extendStage_castSucc]

theorem appendEvent_stage_last (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).stage (Fin.last (H.eventCount + 1)) = Q := by
  rw [appendEvent_stage_apply, ObservedHistory.extendStage_last]

theorem appendEvent_initialMetric_castSucc_heq (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    HEq ((H.appendEvent hs E hinit).initialMetric i.castSucc) (H.initialMetric i) :=
  ObservedHistory.extendMetric_castSucc_heq (H.toHistory) Q E.outputMetric i

theorem appendEvent_initialMetric_last_heq (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    HEq ((H.appendEvent hs E hinit).initialMetric (Fin.last (H.eventCount + 1)))
      E.outputMetric :=
  ObservedHistory.extendMetric_last_heq (H.toHistory) Q E.outputMetric

theorem appendEvent_coreEvent_castSucc (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin H.eventCount) :
    (H.appendEvent hs E hinit).coreEvent i.castSucc = H.extendCoreEventCast E i :=
  extendCoreEventFamily_castSucc H E i

theorem appendEvent_coreEvent_last (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).coreEvent (Fin.last H.eventCount) = H.extendCoreEventLast E :=
  extendCoreEventFamily_last H E

theorem appendEvent_toHistory_eventCount (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).toHistory.eventCount = H.eventCount + 1 := rfl

theorem extendCoreEventFamily_toMetricCutCapEvent (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) (e : Fin (H.eventCount + 1)) :
    (H.extendCoreEventFamily E e).toMetricCutCapEvent =
      (H.toHistory).extendEventFamily E.toMetricCutCapEvent e := by
  cases e using Fin.lastCases with
  | cast i =>
    rw [extendCoreEventFamily_castSucc, extendCoreEventCast,
      ObservedHistory.extendEventFamily_castSucc, ObservedHistory.extendEventFamilyCast,
      RetainedCoreEvent.transport_toMetricCutCapEvent]
    rfl
  | last =>
    rw [extendCoreEventFamily_last, extendCoreEventLast,
      ObservedHistory.extendEventFamily_last, ObservedHistory.extendEventFamilyLast,
      RetainedCoreEvent.transport_toMetricCutCapEvent]
    rfl

theorem appendEvent_toHistory_time (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).toHistory.time = (H.toHistory).extendTime s := rfl

theorem appendEvent_toHistory_time_castSucc (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    (H.appendEvent hs E hinit).toHistory.time i.castSucc = H.time i := by
  rw [appendEvent_toHistory_time H hs E hinit, ObservedHistory.extendTime_castSucc]

theorem appendEvent_toHistory_time_last (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).toHistory.time (Fin.last (H.eventCount + 1)) = s := by
  rw [appendEvent_toHistory_time H hs E hinit, ObservedHistory.extendTime_last]

theorem activeStage_appendEvent_toHistory (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (hhor : H.horizon < s) :
    (H.appendEvent hs E hinit).toHistory.activeStage
        ⟨H.horizon, H.horizon_nonneg, hhor.le⟩ = (Fin.last H.eventCount).castSucc := by
  refine ObservedHistory.activeStage_eq_of_maximal (H.appendEvent hs E hinit).toHistory _ _ ?_ ?_
  · rw [appendEvent_toHistory_time_castSucc H hs E hinit (Fin.last H.eventCount)]
    exact H.time_le_horizon
  · intro k hk
    rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
    · have hk' : H.time i ≤ H.horizon := by
        rw [← appendEvent_toHistory_time_castSucc H hs E hinit i]
        exact hk
      have hle : i ≤ Fin.last H.eventCount := by
        have h := ObservedHistory.le_activeStage (H.toHistory)
          ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ i hk'
        rwa [(H.toHistory).activeStage_at_horizon] at h
      exact Fin.castSucc_le_castSucc_iff.mpr hle
    · exfalso
      have hk' : s ≤ H.horizon := by
        rw [← appendEvent_toHistory_time_last H hs E hinit]
        exact hk
      exact absurd hk' (not_le.mpr hhor)

theorem appendEvent_toHistory_restrict_eventCount (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (hhor : H.horizon < s) :
    ((H.appendEvent hs E hinit).toHistory.restrict
        ⟨H.horizon, H.horizon_nonneg, hhor.le⟩).eventCount = H.eventCount := by
  rw [ObservedHistory.restrict_eventCount, activeStage_appendEvent_toHistory H hs E hinit hhor]
  rfl

def extendHorizon (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) : RetainedCoreHistory P where
  horizon := T
  horizon_nonneg := H.horizon_nonneg.trans hT
  eventCount := H.eventCount
  time := H.time
  time_strictMono := H.time_strictMono
  time_zero := H.time_zero
  time_le_horizon := H.time_le_horizon.trans hT
  stage := H.stage
  initialMetric := H.initialMetric
  coreEvent := H.coreEvent
  event_initial := H.event_initial
  event_output := H.event_output
  finalSlab := fun _ => S
  final_initial := fun _ => hS

theorem extendHorizon_eventCount (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T hT S hS).eventCount = H.eventCount := rfl

theorem extendHorizon_horizon (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T hT S hS).horizon = T := rfl

theorem extendHorizon_time (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    (H.extendHorizon T hT S hS).time i = H.time i := rfl

theorem extendHorizon_stage (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    (H.extendHorizon T hT S hS).stage i = H.stage i := rfl

theorem extendHorizon_coreEvent (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin H.eventCount) :
    (H.extendHorizon T hT S hS).coreEvent i = H.coreEvent i := rfl

def appendEventCompatible (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) : Prop :=
  ∀ (h : H.time (Fin.last H.eventCount) < H.horizon) (τ : ℝ),
    τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon →
    E.incoming.flow.base.metric τ = (H.finalSlab h).flow.base.metric τ

theorem appendEventCompatible_of_time_eq_horizon (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (htime : H.time (Fin.last H.eventCount) = H.horizon) : H.appendEventCompatible E := by
  intro h
  exact absurd (htime ▸ h) (lt_irrefl H.horizon)

theorem exists_retainedCoreHistory_eventCount_zero (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ H : RetainedCoreHistory P, H.eventCount = 0 ∧ 0 < H.horizon := by
  obtain ⟨T, hT, S, hS⟩ := exists_closedSlab_of_metric P g 0
  exact ⟨RetainedCoreHistory.ofClosedSlab g hT S hS, rfl, hT⟩

theorem exists_retainedCoreHistory_eventCount_one (P : OrientedThreeStage.{u}) (g : P.Metric)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : 0 < s) (E : RetainedCoreEvent P Q 0 s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric 0 = g) :
    ∃ H : RetainedCoreHistory P, H.eventCount = 1 ∧ H.horizon = s :=
  ⟨(RetainedCoreHistory.atZero P g).appendEvent hs E hinit, rfl, rfl⟩

theorem exists_retainedCoreHistory_eventCount_one_of_isEmpty_output
    (P : OrientedThreeStage.{u}) (g : P.Metric) {Q D N : OrientedThreeStage.{u}} {s : ℝ}
    (hs : 0 < s) (X : SmoothCutCapTransition P Q D N) [IsEmpty Q.Carrier]
    (G : P.IncomingSlab 0 s) (L : G.TerminalLimitMetric) (hinit : G.flow.base.metric 0 = g) :
    ∃ H : RetainedCoreHistory P, H.eventCount = 1 ∧ H.horizon = s :=
  exists_retainedCoreHistory_eventCount_one P g hs
    (RetainedCoreEvent.ofEmptyOutput X G L (OrientedThreeStage.metricOfIsEmpty Q)) hinit

end RetainedCoreHistory

namespace ObservedHistory

theorem appendEvent_isPrefixOf (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hhor : H.horizon < s)
    (hslab : ∀ (h : H.time (Fin.last H.eventCount) < H.horizon) (τ : ℝ),
      τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon →
      E.incoming.flow.base.metric τ = (H.finalSlab h).flow.base.metric τ) :
    H.IsPrefixOf (H.appendEvent hs E hinit) := by
  let K := H.appendEvent hs E hinit
  let b : Icc (0 : ℝ) K.horizon := ⟨H.horizon, H.horizon_nonneg, hhor.le⟩
  have ha : K.activeStage b = (Fin.last H.eventCount).castSucc :=
    activeStage_appendEvent H hs E hinit hhor
  have hc : (K.restrict b).eventCount = H.eventCount := by
    rw [restrict_eventCount, ha]
    rfl
  have hidxT (j : Fin ((K.restrict b).eventCount + 1)) :
      Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (K.activeStage b).isLt) 1) j
        = (Fin.cast (congrArg (· + 1) hc) j).castSucc :=
    Fin.ext rfl
  have hidxE (i : Fin ((K.restrict b).eventCount)) :
      Fin.castLE (Nat.le_of_lt_succ (K.activeStage b).isLt) i
        = (Fin.cast hc i).castSucc :=
    Fin.ext rfl
  have hidxLast : Fin.cast (congrArg (· + 1) hc) (Fin.last (K.restrict b).eventCount) =
      Fin.last H.eventCount :=
    Fin.ext hc
  have htime (j : Fin ((K.restrict b).eventCount + 1)) :
      (K.restrict b).time j = H.time (Fin.cast (congrArg (· + 1) hc) j) :=
    (restrict_time_apply K b j).trans
      ((eq_of_heq (heq_apply_of_eq K.time (hidxT j))).trans
        ((appendEvent_time_apply H hs E hinit _).trans
          (extendTime_castSucc H s (Fin.cast (congrArg (· + 1) hc) j))))
  have hlast : (K.restrict b).time (Fin.last (K.restrict b).eventCount) =
      H.time (Fin.last H.eventCount) :=
    (htime (Fin.last (K.restrict b).eventCount)).trans (congrArg H.time hidxLast)
  have hstage (j : Fin ((K.restrict b).eventCount + 1)) :
      (K.restrict b).stage j = H.stage (Fin.cast (congrArg (· + 1) hc) j) :=
    (restrict_stage_apply K b j).trans
      ((eq_of_heq (heq_apply_of_eq K.stage (hidxT j))).trans
        ((appendEvent_stage_apply H hs E hinit _).trans
          (extendStage_castSucc H Q E.outputMetric (Fin.cast (congrArg (· + 1) hc) j))))
  have hinitm (j : Fin ((K.restrict b).eventCount + 1)) :
      HEq ((K.restrict b).initialMetric j)
        (H.initialMetric (Fin.cast (congrArg (· + 1) hc) j)) :=
    (restrict_initialMetric_heq K b j).trans
      ((heq_apply_of_eq K.initialMetric (hidxT j)).trans
        (appendEvent_initialMetric_castSucc_heq H hs E hinit
          (Fin.cast (congrArg (· + 1) hc) j)))
  have hevent (i : Fin ((K.restrict b).eventCount)) :
      ((K.restrict b).event i).SamePresentation (H.event (Fin.cast hc i)) :=
    MetricCutCapEvent.SamePresentation.of_heq_of_eq (hstage i.castSucc) (hstage i.succ)
      (htime i.castSucc) (htime i.succ)
      ((restrict_event K b i).trans
        ((heq_of_eq (appendEvent_event_apply H hs E hinit
            (Fin.castLE (Nat.le_of_lt_succ (K.activeStage b).isLt) i))).trans
          ((heq_apply_of_eq (H.extendEventFamily E) (hidxE i)).trans
            ((heq_of_eq (extendEventFamily_castSucc H E (Fin.cast hc i))).trans
              (MetricCutCapEvent.heq_transport _ _ _ _
                (H.event (Fin.cast hc i)))))))
  have hmetric (j : Fin ((K.restrict b).eventCount + 1))
      (τ : ℝ) (hτ : τ ∈ (K.restrict b).stageDomain j) :
      HEq ((K.restrict b).stageMetric j τ)
        (H.stageMetric (Fin.cast (congrArg (· + 1) hc) j) τ) := by
    refine (K.restrict_stageMetric b j τ hτ).trans ?_
    refine (heq_apply_of_eq (fun x => K.stageMetric x τ) (hidxT j)).trans ?_
    generalize hk : Fin.cast (congrArg (· + 1) hc) j = k
    cases k using Fin.lastCases with
    | cast i =>
      refine (heq_of_eq (stageMetric_castSucc_apply (H := K) i.castSucc τ)).trans ?_
      refine (MetricCutCapEvent.heq_incomingMetric
        ((heq_of_eq (appendEvent_event_apply H hs E hinit i.castSucc)).trans
          (heq_of_eq (extendEventFamily_castSucc H E i))) τ).trans ?_
      exact (MetricCutCapEvent.transport_incoming_metric_heq _ _ _ _ (H.event i) τ).trans
        (heq_of_eq (stageMetric_castSucc_apply (H := H) i τ)).symm
    | last =>
      refine (heq_of_eq (stageMetric_castSucc_apply (H := K) (Fin.last H.eventCount) τ)).trans ?_
      refine (MetricCutCapEvent.heq_incomingMetric
        (heq_of_eq (appendEvent_event_last H hs E hinit)) τ).trans ?_
      refine (MetricCutCapEvent.transport_incoming_metric_heq _ _ _ _ E τ).trans ?_
      rw [ObservedHistory.stageMetric, Fin.lastCases_last]
      have hjval : j.val = (K.restrict b).eventCount := by
        have hv := congrArg Fin.val hk
        simp only [Fin.val_cast, Fin.val_last] at hv
        rw [hv]
        exact hc.symm
      have hj : j = Fin.last (K.restrict b).eventCount := Fin.ext hjval
      have hτ' : τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon := by
        have h1 := hτ
        rw [hj] at h1
        simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc] at h1
        rw [hlast, ObservedHistory.restrict_horizon] at h1
        exact h1
      split_ifs with h
      · exact heq_of_eq (hslab h τ hτ')
      · have hτtime : τ = H.time (Fin.last H.eventCount) :=
          le_antisymm (hτ'.2.trans (not_lt.mp h)) hτ'.1
        subst hτtime
        exact heq_of_eq hinit
  refine ⟨hhor.le, ?_⟩
  exact
    { horizon_eq := rfl
      count_eq := hc
      time_eq := htime
      stage_eq := hstage
      initialMetric_heq := hinitm
      event_eq := hevent
      metric_heq := hmetric }

end ObservedHistory

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}}

theorem appendEvent_toHistory_samePresentation (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    ObservedHistory.SamePresentation (H.appendEvent hs E hinit).toHistory
      ((H.toHistory).appendEvent hs E.toMetricCutCapEvent hinit) := by
  let K := (H.toHistory).appendEvent hs E.toMetricCutCapEvent hinit
  have hKtime : K.time = (H.toHistory).extendTime s := rfl
  have hKstage : K.stage = (H.toHistory).extendStage Q E.outputMetric := rfl
  have hKinitial : K.initialMetric = (H.toHistory).extendMetric Q E.outputMetric := rfl
  have hKevent : K.event = (H.toHistory).extendEventFamily E.toMetricCutCapEvent := rfl
  have hcnt : (H.appendEvent hs E hinit).toHistory.eventCount = K.eventCount :=
    (appendEvent_toHistory_eventCount H hs E hinit).trans
      (ObservedHistory.appendEvent_eventCount (H.toHistory) hs E.toMetricCutCapEvent hinit).symm
  have htime (j : Fin ((H.appendEvent hs E hinit).toHistory.eventCount + 1)) :
      (H.appendEvent hs E hinit).toHistory.time j =
        K.time (Fin.cast (congrArg (· + 1) hcnt) j) := by
    rw [appendEvent_toHistory_time H hs E hinit, hKtime]
    exact congrArg ((H.toHistory).extendTime s) (Fin.ext (by simp))
  have hstage (j : Fin ((H.appendEvent hs E hinit).toHistory.eventCount + 1)) :
      (H.appendEvent hs E hinit).toHistory.stage j =
        K.stage (Fin.cast (congrArg (· + 1) hcnt) j) := by
    rw [show (H.appendEvent hs E hinit).toHistory.stage =
        (H.toHistory).extendStage Q E.outputMetric from rfl, hKstage]
    exact congrArg ((H.toHistory).extendStage Q E.outputMetric) (Fin.ext (by simp))
  have hinitm (j : Fin ((H.appendEvent hs E hinit).toHistory.eventCount + 1)) :
      HEq ((H.appendEvent hs E hinit).toHistory.initialMetric j)
        (K.initialMetric (Fin.cast (congrArg (· + 1) hcnt) j)) := by
    rw [show (H.appendEvent hs E hinit).toHistory.initialMetric =
        (H.toHistory).extendMetric Q E.outputMetric from rfl, hKinitial]
    exact heq_apply_of_eq (fun x => (H.toHistory).extendMetric Q E.outputMetric x)
      (Fin.ext (by simp))
  have hevHeq (i : Fin ((H.appendEvent hs E hinit).toHistory.eventCount)) :
      HEq ((H.appendEvent hs E hinit).toHistory.event i) (K.event (Fin.cast hcnt i)) := by
    have hidx : i = Fin.cast hcnt i := Fin.ext (by simp)
    refine (heq_of_eq (show (H.appendEvent hs E hinit).toHistory.event i =
      (H.extendCoreEventFamily E i).toMetricCutCapEvent from rfl)).trans ?_
    refine (heq_of_eq (extendCoreEventFamily_toMetricCutCapEvent H E i)).trans ?_
    refine (heq_apply_of_eq
      (fun x => (H.toHistory).extendEventFamily E.toMetricCutCapEvent x) hidx).trans ?_
    exact (heq_of_eq (congrArg
      (fun g => g (Fin.cast hcnt i)) hKevent)).symm
  have hevent (i : Fin ((H.appendEvent hs E hinit).toHistory.eventCount)) :
      ((H.appendEvent hs E hinit).toHistory.event i).SamePresentation
        (K.event (Fin.cast hcnt i)) :=
    MetricCutCapEvent.SamePresentation.of_heq_of_eq (hstage i.castSucc) (hstage i.succ)
      (htime i.castSucc) (htime i.succ) (hevHeq i)
  have hmetric (j : Fin ((H.appendEvent hs E hinit).toHistory.eventCount + 1))
      (τ : ℝ) (hτ : τ ∈ (H.appendEvent hs E hinit).toHistory.stageDomain j) :
      HEq ((H.appendEvent hs E hinit).toHistory.stageMetric j τ)
        (K.stageMetric (Fin.cast (congrArg (· + 1) hcnt) j) τ) := by
    cases j using Fin.lastCases with
    | cast i =>
      refine (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply
        (H := (H.appendEvent hs E hinit).toHistory) i τ)).trans ?_
      exact (MetricCutCapEvent.heq_incomingMetric (hevHeq i) τ).trans
        (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply (H := K)
          (Fin.cast hcnt i) τ)).symm
    | last =>
      have hidxlast : Fin.last (H.appendEvent hs E hinit).toHistory.eventCount =
          Fin.last K.eventCount :=
        Fin.ext hcnt
      have hidxlast' : Fin.cast (congrArg (· + 1) hcnt)
          (Fin.last (H.appendEvent hs E hinit).toHistory.eventCount) = Fin.last K.eventCount :=
        Fin.ext hcnt
      have hL : (H.appendEvent hs E hinit).toHistory.stageMetric
          (Fin.last (H.appendEvent hs E hinit).toHistory.eventCount) τ =
          (H.appendEvent hs E hinit).toHistory.initialMetric
            (Fin.last (H.appendEvent hs E hinit).toHistory.eventCount) := by
        have hLtime : (H.appendEvent hs E hinit).toHistory.time
            (Fin.last (H.appendEvent hs E hinit).toHistory.eventCount) = s :=
          appendEvent_toHistory_time_last H hs E hinit
        have hLhor : (H.appendEvent hs E hinit).toHistory.horizon = s :=
          appendEvent_horizon H hs E hinit
        rw [ObservedHistory.stageMetric, Fin.lastCases_last]
        split_ifs with h
        · exact absurd (by rw [hLtime, hLhor] at h; exact h) (lt_irrefl s)
        · rfl
      have hR : K.stageMetric (Fin.last K.eventCount) τ =
          K.initialMetric (Fin.last K.eventCount) := by
        have hRtime : K.time (Fin.last K.eventCount) = s :=
          ObservedHistory.appendEvent_time_last (H.toHistory) hs E.toMetricCutCapEvent hinit
        have hRhor : K.horizon = s :=
          ObservedHistory.appendEvent_horizon (H.toHistory) hs E.toMetricCutCapEvent hinit
        rw [ObservedHistory.stageMetric, Fin.lastCases_last]
        split_ifs with h
        · exact absurd (by rw [hRtime, hRhor] at h; exact h) (lt_irrefl s)
        · rfl
      rw [hidxlast', hL, hR, hKinitial,
        show (H.appendEvent hs E hinit).toHistory.initialMetric =
          (H.toHistory).extendMetric Q E.outputMetric from rfl]
      exact heq_apply_of_eq (fun x => (H.toHistory).extendMetric Q E.outputMetric x)
        hidxlast
  exact
    { horizon_eq := (appendEvent_horizon H hs E hinit).trans
        (ObservedHistory.appendEvent_horizon (H.toHistory) hs E.toMetricCutCapEvent hinit).symm
      count_eq := hcnt
      time_eq := htime
      stage_eq := hstage
      initialMetric_heq := hinitm
      event_eq := hevent
      metric_heq := hmetric }

theorem appendEvent_isPrefixOf (H : RetainedCoreHistory P) {Q : OrientedThreeStage.{u}}
    {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hhor : H.horizon < s) (hcompat : H.appendEventCompatible E) :
    (H.toHistory).IsPrefixOf (H.appendEvent hs E hinit).toHistory := by
  have hprefix := ObservedHistory.appendEvent_isPrefixOf (H.toHistory) hs
    E.toMetricCutCapEvent hinit hhor hcompat
  refine ⟨hhor.le, ?_⟩
  exact (ObservedHistory.SamePresentation.restrict (H.appendEvent hs E hinit).toHistory
    (appendEvent_toHistory_samePresentation H hs E hinit)
    ⟨H.horizon, H.horizon_nonneg, hhor.le⟩).trans hprefix.presentation

theorem atZero_appendEvent_isPrefixOf (P : OrientedThreeStage.{u}) (g : P.Metric)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : 0 < s)
    (E : RetainedCoreEvent P Q 0 s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric 0 = g) :
    (RetainedCoreHistory.atZero P g).toHistory.IsPrefixOf
      ((RetainedCoreHistory.atZero P g).appendEvent hs E hinit).toHistory :=
  appendEvent_isPrefixOf (RetainedCoreHistory.atZero P g) hs E hinit hs
    (appendEventCompatible_of_time_eq_horizon (RetainedCoreHistory.atZero P g) E rfl)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
