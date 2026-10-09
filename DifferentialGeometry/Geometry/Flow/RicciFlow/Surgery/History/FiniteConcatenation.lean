import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SurgeryEventControl
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

structure ConcatenationLayer
    (H : RetainedCoreHistory.{u}) (K : RetainedCoreHistory.{u})
    (i : Fin (K.eventCount+1)) where
  history : RetainedCoreHistory.{u}
  isPrefix : H.toHistory.IsPrefixOf history.toHistory
  count_eq : history.eventCount = H.eventCount + i.val
  stage_eq : history.stage (Fin.last history.eventCount) = K.stage i
  time_eq : history.time (Fin.last history.eventCount) =
    K.time i + H.time (Fin.last H.eventCount)
  metric_heq : HEq (history.initialMetric (Fin.last history.eventCount)) (K.initialMetric i)
  control : HistoryEventControl history
  horizon_le : history.horizon ≤ max H.horizon
    (K.time i + H.time (Fin.last H.eventCount))

def concatenation_start
    (H : RetainedCoreHistory.{u}) (K : RetainedCoreHistory.{u})
    (hH : HistoryEventControl H)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount))) :
    ConcatenationLayer H K 0 where
  history := H
  isPrefix := ObservedHistory.IsPrefixOf.refl _
  count_eq := by simp
  stage_eq := hs.symm
  time_eq := by rw [K.time_zero,zero_add]
  metric_heq := hm.symm
  control := hH
  horizon_le := le_max_left _ _

def concatenation_step
    {H : RetainedCoreHistory.{u}} {K : RetainedCoreHistory.{u}}
    (hK : HistoryEventControl K) (i : Fin K.eventCount)
    (L : ConcatenationLayer H K i.castSucc) : ConcatenationLayer H K i.succ := by
  let c := H.time (Fin.last H.eventCount)
  let E₀ := translate_retained_event (K.coreEvent i) c
  let E := RetainedCoreEvent.transport L.stage_eq.symm rfl L.time_eq.symm rfl E₀
  have hinit : E.incoming.flow.base.metric
      (L.history.time (Fin.last L.history.eventCount)) =
      L.history.initialMetric (Fin.last L.history.eventCount) := by
    apply eq_of_heq
    exact (RetainedCoreEvent.transport_incoming_metric_heq L.stage_eq.symm rfl
      L.time_eq.symm rfl E₀ (L.history.time (Fin.last L.history.eventCount))).trans
      ((heq_of_eq (congrArg (fun t => E₀.incoming.flow.base.metric t) L.time_eq)).trans
      ((heq_of_eq (translated_event_initial (K.coreEvent i) c)).trans
      ((heq_of_eq (K.event_initial i)).trans L.metric_heq.symm)))
  have hE : SurgeryEventControl E := event_control_transport _ _ _ _ E₀
    (event_control_translate (K.coreEvent i) (hK i) c)
  let J := L.history.appendEvent E.incoming.lt E hinit
  have ht : J.time (Fin.last J.eventCount) = K.time i.succ + c :=
    L.history.appendEvent_time_last E.incoming.lt E hinit
  exact {
    history := J
    isPrefix := L.isPrefix.trans (actual_singular_event_preserves_prefix L.history E hinit hE.1)
    count_eq := by
      change L.history.eventCount+1 = H.eventCount+i.succ.val
      rw [L.count_eq]
      simp only [Fin.val_castSucc,Fin.val_succ]
      omega
    stage_eq := L.history.appendEvent_stage_last E.incoming.lt E hinit
    time_eq := ht
    metric_heq := (L.history.appendEvent_initialMetric_last_heq E.incoming.lt E hinit).trans
      ((RetainedCoreEvent.transport_outputMetric_heq L.stage_eq.symm rfl
        L.time_eq.symm rfl E₀).trans (heq_of_eq (K.event_output i)))
    control := history_control_append L.history L.control E hinit hE
    horizon_le := le_max_right _ _ }

theorem concatenation_layers
    (H : RetainedCoreHistory.{u}) (K : RetainedCoreHistory.{u})
    (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount))) :
    ∀ i : Fin (K.eventCount+1), Nonempty (ConcatenationLayer H K i) := by
  intro i
  induction i using Fin.induction with
  | zero => exact ⟨concatenation_start H K hH hs hm⟩
  | succ i ih => exact ⟨concatenation_step hK i (Classical.choice ih)⟩

end GC.GeneralFlow
