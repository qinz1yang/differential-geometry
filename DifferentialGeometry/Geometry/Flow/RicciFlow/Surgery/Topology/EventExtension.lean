import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

def transport {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s) : MetricCutCapEvent P' Q' a' s' :=
  hs ▸ ha ▸ hQ ▸ hP ▸ E

theorem transport_incoming_metric_heq {P Q P' Q' : OrientedThreeStage.{u}}
    {a s a' s' : ℝ} (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s) (u : ℝ) :
    HEq ((transport hP hQ ha hs E).incoming.flow.base.metric u)
      (E.incoming.flow.base.metric u) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact HEq.rfl

theorem transport_outputMetric_heq {P Q P' Q' : OrientedThreeStage.{u}}
    {a s a' s' : ℝ} (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s) :
    HEq (transport hP hQ ha hs E).outputMetric E.outputMetric := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact HEq.rfl

theorem transport_samePresentation {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s) : (transport hP hQ ha hs E).SamePresentation E where
  incomingStage_eq := hP.symm
  outgoingStage_eq := hQ.symm
  leftTime_eq := ha.symm
  eventTime_eq := hs.symm
  discarded_eq := by cases hP; cases hQ; cases ha; cases hs; rfl
  capped_eq := by cases hP; cases hQ; cases ha; cases hs; rfl
  transition_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl
  incomingMetric_heq := by
    cases hP; cases hQ; cases ha; cases hs
    intro t _
    exact HEq.rfl
  terminalRegion_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl
  terminalMetric_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl
  outputMetric_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl
  old_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl
  oldCharts_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl
  oldTerminal_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl
  oldOutput_heq := by cases hP; cases hQ; cases ha; cases hs; exact HEq.rfl


end MetricCutCapEvent

namespace ObservedHistory

def extendTime (H : ObservedHistory.{u}) (t : ℝ) : Fin (H.eventCount + 2) → ℝ :=
  Fin.lastCases t H.time

theorem extendTime_castSucc (H : ObservedHistory.{u}) (t : ℝ)
    (i : Fin (H.eventCount + 1)) : H.extendTime t i.castSucc = H.time i :=
  Fin.lastCases_castSucc i

theorem extendTime_last (H : ObservedHistory.{u}) (t : ℝ) :
    H.extendTime t (Fin.last (H.eventCount + 1)) = t :=
  Fin.lastCases_last

def extendStagePkg (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u}) (gQ : Q.Metric) :
    Fin (H.eventCount + 2) → Sigma fun S : OrientedThreeStage.{u} => S.Metric :=
  Fin.lastCases ⟨Q, gQ⟩ fun i => ⟨H.stage i, H.initialMetric i⟩

def extendStage (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u}) (gQ : Q.Metric) :
    Fin (H.eventCount + 2) → OrientedThreeStage.{u} :=
  fun j => (H.extendStagePkg Q gQ j).1

def extendMetric (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u}) (gQ : Q.Metric) :
    (j : Fin (H.eventCount + 2)) → (H.extendStage Q gQ j).Metric :=
  fun j => (H.extendStagePkg Q gQ j).2

theorem extendStagePkg_castSucc (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u})
    (gQ : Q.Metric) (i : Fin (H.eventCount + 1)) :
    H.extendStagePkg Q gQ i.castSucc = ⟨H.stage i, H.initialMetric i⟩ :=
  Fin.lastCases_castSucc i

theorem extendStagePkg_last (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u})
    (gQ : Q.Metric) :
    H.extendStagePkg Q gQ (Fin.last (H.eventCount + 1)) = ⟨Q, gQ⟩ :=
  Fin.lastCases_last

theorem extendStage_castSucc (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u})
    (gQ : Q.Metric) (i : Fin (H.eventCount + 1)) :
    H.extendStage Q gQ i.castSucc = H.stage i := by
  rw [extendStage, extendStagePkg_castSucc]

theorem extendStage_last (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u})
    (gQ : Q.Metric) : H.extendStage Q gQ (Fin.last (H.eventCount + 1)) = Q := by
  rw [extendStage, extendStagePkg_last]

theorem extendMetric_castSucc_heq (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u})
    (gQ : Q.Metric) (i : Fin (H.eventCount + 1)) :
    HEq (H.extendMetric Q gQ i.castSucc) (H.initialMetric i) := by
  simp only [extendMetric, extendStage]
  exact (Sigma.ext_iff.mp (extendStagePkg_castSucc H Q gQ i)).2

theorem extendMetric_last_heq (H : ObservedHistory.{u}) (Q : OrientedThreeStage.{u})
    (gQ : Q.Metric) :
    HEq (H.extendMetric Q gQ (Fin.last (H.eventCount + 1))) gQ := by
  simp only [extendMetric, extendStage]
  exact (Sigma.ext_iff.mp (extendStagePkg_last H Q gQ)).2

def extendEventFamilyLast (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t) :
    MetricCutCapEvent (H.extendStage Q E.outputMetric (Fin.last H.eventCount).castSucc)
      (H.extendStage Q E.outputMetric (Fin.last H.eventCount).succ)
      (H.extendTime t (Fin.last H.eventCount).castSucc)
      (H.extendTime t (Fin.last H.eventCount).succ) :=
  MetricCutCapEvent.transport
    (extendStage_castSucc H Q E.outputMetric (Fin.last H.eventCount)).symm
    (extendStage_last H Q E.outputMetric).symm
    (extendTime_castSucc H t (Fin.last H.eventCount)).symm
    (extendTime_last H t).symm E

def extendEventFamilyCast (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t) (i : Fin H.eventCount) :
    MetricCutCapEvent (H.extendStage Q E.outputMetric (i.castSucc).castSucc)
      (H.extendStage Q E.outputMetric (i.castSucc).succ)
      (H.extendTime t (i.castSucc).castSucc) (H.extendTime t (i.castSucc).succ) :=
  MetricCutCapEvent.transport
    (extendStage_castSucc H Q E.outputMetric (i.castSucc)).symm
    (extendStage_castSucc H Q E.outputMetric i.succ).symm
    (extendTime_castSucc H t (i.castSucc)).symm
    (extendTime_castSucc H t i.succ).symm (H.event i)

def extendEventFamily (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t) :
    (e : Fin (H.eventCount + 1)) →
      MetricCutCapEvent (H.extendStage Q E.outputMetric e.castSucc)
        (H.extendStage Q E.outputMetric e.succ)
        (H.extendTime t e.castSucc) (H.extendTime t e.succ) :=
  Fin.lastCases (H.extendEventFamilyLast E) (fun i => H.extendEventFamilyCast E i)

theorem extendEventFamily_castSucc (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}}
    {t : ℝ} (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t) (i : Fin H.eventCount) :
    H.extendEventFamily E i.castSucc = H.extendEventFamilyCast E i :=
  Fin.lastCases_castSucc i

theorem extendEventFamily_last (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}}
    {t : ℝ} (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t) :
    H.extendEventFamily E (Fin.last H.eventCount) = H.extendEventFamilyLast E :=
  Fin.lastCases_last

def appendEvent (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) : ObservedHistory.{u} where
  horizon := t
  horizon_nonneg := (H.time_nonneg (Fin.last H.eventCount)).trans ht.le
  eventCount := H.eventCount + 1
  time := H.extendTime t
  time_strictMono := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [extendTime_castSucc, extendTime_castSucc]
        exact H.time_strictMono (Fin.castSucc_lt_castSucc_iff.mp hij)
      · rw [extendTime_castSucc, extendTime_last]
        exact lt_of_le_of_lt (H.time_strictMono.monotone (Fin.le_last i')) ht
    · exact absurd hij (not_lt_of_ge (Fin.le_last j))
  time_zero := by
    have h0 : (0 : Fin (H.eventCount + 2)) = (0 : Fin (H.eventCount + 1)).castSucc := rfl
    rw [h0, extendTime_castSucc, H.time_zero]
  time_le_horizon := by
    rw [extendTime_last]
  stage := H.extendStage Q E.outputMetric
  initialMetric := H.extendMetric Q E.outputMetric
  event := H.extendEventFamily E
  event_initial := by
    intro e
    cases e using Fin.lastCases with
    | cast i =>
      rw [extendEventFamily_castSucc]
      refine eq_of_heq ?_
      have htime : (H.event i).incoming.flow.base.metric (H.extendTime t (i.castSucc).castSucc) =
          (H.event i).incoming.flow.base.metric (H.time i.castSucc) := by
        rw [extendTime_castSucc]
      exact (MetricCutCapEvent.transport_incoming_metric_heq _ _ _ _ (H.event i)
          (H.extendTime t (i.castSucc).castSucc)).trans
        ((heq_of_eq htime).trans ((heq_of_eq (H.event_initial i)).trans
          (extendMetric_castSucc_heq H Q E.outputMetric (i.castSucc)).symm))
    | last =>
      rw [extendEventFamily_last]
      refine eq_of_heq ?_
      have htime : E.incoming.flow.base.metric (H.extendTime t (Fin.last H.eventCount).castSucc) =
          E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) := by
        rw [extendTime_castSucc]
      exact (MetricCutCapEvent.transport_incoming_metric_heq _ _ _ _ E
          (H.extendTime t (Fin.last H.eventCount).castSucc)).trans
        ((heq_of_eq htime).trans ((heq_of_eq hinit).trans
          (extendMetric_castSucc_heq H Q E.outputMetric (Fin.last H.eventCount)).symm))
  event_output := by
    intro e
    cases e using Fin.lastCases with
    | cast i =>
      rw [extendEventFamily_castSucc]
      refine eq_of_heq ?_
      exact (MetricCutCapEvent.transport_outputMetric_heq _ _ _ _ (H.event i)).trans
        ((heq_of_eq (H.event_output i)).trans
          (extendMetric_castSucc_heq H Q E.outputMetric i.succ).symm)
    | last =>
      rw [extendEventFamily_last]
      refine eq_of_heq ?_
      exact (MetricCutCapEvent.transport_outputMetric_heq _ _ _ _ E).trans
        (extendMetric_last_heq H Q E.outputMetric).symm
  finalSlab := fun h => absurd (by rw [extendTime_last] at h; exact h) (lt_irrefl t)
  final_initial := fun h => False.elim (absurd (by rw [extendTime_last] at h; exact h) (lt_irrefl t))


theorem appendEvent_horizon (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent ht E hinit).horizon = t := rfl

theorem appendEvent_eventCount (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent ht E hinit).eventCount = H.eventCount + 1 := rfl

theorem appendEvent_time_apply (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (j : Fin (H.eventCount + 2)) :
    (H.appendEvent ht E hinit).time j = H.extendTime t j := rfl

theorem appendEvent_time_castSucc (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    (H.appendEvent ht E hinit).time i.castSucc = H.time i := by
  rw [appendEvent_time_apply, extendTime_castSucc]

theorem appendEvent_time_last (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent ht E hinit).time (Fin.last (H.eventCount + 1)) = t := by
  rw [appendEvent_time_apply, extendTime_last]

theorem appendEvent_event_apply (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (e : Fin (H.eventCount + 1)) :
    (H.appendEvent ht E hinit).event e = H.extendEventFamily E e := rfl

theorem appendEvent_event_last (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent ht E hinit).event (Fin.last H.eventCount) = H.extendEventFamilyLast E := by
  rw [appendEvent_event_apply, extendEventFamily_last]


theorem appendEvent_horizon_le (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (hhor : H.horizon < t) :
    H.horizon ≤ (H.appendEvent ht E hinit).horizon := by
  rw [appendEvent_horizon]
  exact hhor.le

def appendEventHorizonPoint (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (hhor : H.horizon < t) :
    Icc (0 : ℝ) (H.appendEvent ht E hinit).horizon :=
  ⟨H.horizon, H.horizon_nonneg, appendEvent_horizon_le H ht E hinit hhor⟩

theorem activeStage_appendEvent (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (hhor : H.horizon < t) :
    (H.appendEvent ht E hinit).activeStage (appendEventHorizonPoint H ht E hinit hhor) =
      (Fin.last H.eventCount).castSucc := by
  refine (H.appendEvent ht E hinit).activeStage_eq_of_maximal _ _ ?_ ?_
  · rw [appendEvent_time_castSucc]
    exact H.time_le_horizon
  · intro k hk
    rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
    · have hcnt : (H.appendEvent ht E hinit).eventCount = H.eventCount + 1 := rfl
      have hk' : H.time (Fin.cast hcnt i) ≤ H.horizon := by
        rw [← appendEvent_time_castSucc H ht E hinit (Fin.cast hcnt i)]
        exact hk
      have hle : Fin.cast hcnt i ≤ Fin.last H.eventCount := by
        simpa only [H.activeStage_at_horizon] using
          H.le_activeStage ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ (Fin.cast hcnt i) hk'
      exact Fin.castSucc_le_castSucc_iff.mpr hle
    · exfalso
      have hk' : t ≤ H.horizon := by
        rw [← appendEvent_time_last H ht E hinit]
        exact hk
      exact absurd hk' (not_le.mpr hhor)

theorem appendEvent_restrict_eventCount (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}}
    {t : ℝ} (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (hhor : H.horizon < t) :
    ((H.appendEvent ht E hinit).restrict
        (appendEventHorizonPoint H ht E hinit hhor)).eventCount = H.eventCount := by
  rw [restrict_eventCount, activeStage_appendEvent]
  rfl



theorem restrict_time_apply (K : ObservedHistory.{u}) (b : Icc (0 : ℝ) K.horizon)
    (m : Fin ((K.activeStage b).val + 1)) :
    (K.restrict b).time m =
      K.time (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (K.activeStage b).isLt) 1) m) :=
  rfl

theorem restrict_stage_apply (K : ObservedHistory.{u}) (b : Icc (0 : ℝ) K.horizon)
    (m : Fin ((K.activeStage b).val + 1)) :
    (K.restrict b).stage m =
      K.stage (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (K.activeStage b).isLt) 1) m) :=
  rfl

theorem restrict_initialMetric_heq (K : ObservedHistory.{u}) (b : Icc (0 : ℝ) K.horizon)
    (m : Fin ((K.activeStage b).val + 1)) :
    HEq ((K.restrict b).initialMetric m)
      (K.initialMetric
        (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (K.activeStage b).isLt) 1) m)) :=
  HEq.rfl

theorem restrict_event_apply (K : ObservedHistory.{u}) (b : Icc (0 : ℝ) K.horizon)
    (i : Fin (K.activeStage b).val) :
    (K.restrict b).event i =
      K.event (Fin.castLE (Nat.le_of_lt_succ (K.activeStage b).isLt) i) :=
  rfl

theorem appendEvent_stage_apply (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (j : Fin (H.eventCount + 2)) :
    (H.appendEvent ht E hinit).stage j = H.extendStage Q E.outputMetric j := rfl

theorem appendEvent_stage_castSucc (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    (H.appendEvent ht E hinit).stage i.castSucc = H.stage i := by
  rw [appendEvent_stage_apply, extendStage_castSucc]

theorem appendEvent_initialMetric_castSucc_heq (H : ObservedHistory.{u})
    {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin (H.eventCount + 1)) :
    HEq ((H.appendEvent ht E hinit).initialMetric i.castSucc) (H.initialMetric i) :=
  extendMetric_castSucc_heq H Q E.outputMetric i



theorem appendEvent_spec (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {t : ℝ}
    (ht : H.time (Fin.last H.eventCount) < t)
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) t)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent ht E hinit).eventCount = H.eventCount + 1 ∧
      (H.appendEvent ht E hinit).horizon = t ∧
      (H.appendEvent ht E hinit).time (Fin.last H.eventCount).castSucc =
        H.time (Fin.last H.eventCount) ∧
      (H.appendEvent ht E hinit).time (Fin.last (H.eventCount + 1)) = t ∧
      (H.appendEvent ht E hinit).event (Fin.last H.eventCount) = H.extendEventFamilyLast E := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rw [appendEvent_time_castSucc]
  · exact appendEvent_time_last H ht E hinit
  · exact appendEvent_event_last H ht E hinit

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
