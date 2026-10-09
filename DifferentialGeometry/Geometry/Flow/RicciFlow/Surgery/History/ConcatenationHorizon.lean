import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.FiniteConcatenation
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

def transport_closed_slab {P P' : OrientedThreeStage.{u}} {a b a' b' : ℝ}
    (hP : P = P') (ha : a = a') (hb : b = b') (S : P.ClosedSlab a b) :
    P'.ClosedSlab a' b' := by
  cases hP
  cases ha
  cases hb
  exact S

theorem transport_closed_metric {P P' : OrientedThreeStage.{u}} {a b a' b' : ℝ}
    (hP : P = P') (ha : a = a') (hb : b = b') (S : P.ClosedSlab a b) (t : ℝ) :
    HEq ((transport_closed_slab hP ha hb S).flow.base.metric t) (S.flow.base.metric t) := by
  cases hP
  cases ha
  cases hb
  exact HEq.rfl

theorem finite_history_concatenation
    (H : RetainedCoreHistory.{u}) (K : RetainedCoreHistory.{u})
    (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)))
    (hB : H.horizon ≤ K.horizon + H.time (Fin.last H.eventCount)) :
    ∃ J : RetainedCoreHistory.{u},
      H.toHistory.IsPrefixOf J.toHistory ∧
      J.horizon = K.horizon + H.time (Fin.last H.eventCount) ∧
      J.eventCount = H.eventCount + K.eventCount ∧ HistoryEventControl J ∧
      J.stage (Fin.last J.eventCount) = K.stage (Fin.last K.eventCount) ∧
      HEq (J.initialMetric (Fin.last J.eventCount)) (K.initialMetric (Fin.last K.eventCount)) := by
  let L := Classical.choice (concatenation_layers H K hH hK hs hm (Fin.last K.eventCount))
  let c := H.time (Fin.last H.eventCount)
  have hhor : L.history.horizon ≤ K.horizon+c :=
    L.horizon_le.trans (max_le hB (by linarith [K.time_le_horizon]))
  rcases K.time_le_horizon.lt_or_eq with ht | ht
  · let S₀ := (K.finalSlab ht).timeTranslate c
    let S := transport_closed_slab L.stage_eq.symm L.time_eq.symm rfl S₀
    have hi : S.flow.base.metric (L.history.time (Fin.last L.history.eventCount)) =
        L.history.initialMetric (Fin.last L.history.eventCount) := by
      apply eq_of_heq
      exact (transport_closed_metric L.stage_eq.symm L.time_eq.symm rfl S₀ _).trans
        ((heq_of_eq (congrArg (fun t => S₀.flow.base.metric t) L.time_eq)).trans
        ((heq_of_eq ((K.finalSlab ht).timeTranslate_initial_metric c)).trans
        ((heq_of_eq (K.final_initial ht)).trans L.metric_heq.symm)))
    let J := L.history.extendHorizon (K.horizon+c) hhor S hi
    refine ⟨J,L.isPrefix.trans (actual_closed_extension_preserves_prefix L.history hhor S hi),
      rfl,L.count_eq,history_control_extend L.history L.control hhor S hi,
      L.stage_eq,L.metric_heq⟩
  · have heq : L.history.horizon = K.horizon+c := by
      apply le_antisymm hhor
      rw [← ht,← L.time_eq]
      exact L.history.time_le_horizon
    exact ⟨L.history,L.isPrefix,heq,L.count_eq,L.control,L.stage_eq,L.metric_heq⟩

theorem marked_finite_history_concatenation {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory)
    (K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)))
    (hB : H.horizon ≤ K.horizon + H.time (Fin.last H.eventCount)) :
    ∃ (J : RetainedCoreHistory.{u}) (A' : InitialIdentification P g J.toHistory),
      A.IsPrefixOf A' ∧ J.horizon = K.horizon + H.time (Fin.last H.eventCount) ∧
      J.eventCount = H.eventCount + K.eventCount ∧ HistoryEventControl J ∧
      ∀ i, GC.Surgery.ActualMetricEventGeometry (J.coreEvent i).toMetricCutCapEvent := by
  obtain ⟨J,hp,hj,hn,hc,-,-⟩ := finite_history_concatenation H K hH hK hs hm hB
  obtain ⟨A',ha⟩ := marking_of_actual_prefix A hp
  exact ⟨J,A',ha,hj,hn,hc,fun i => controlled_event_geometry (J.coreEvent i) (hc i)⟩

end GC.GeneralFlow
