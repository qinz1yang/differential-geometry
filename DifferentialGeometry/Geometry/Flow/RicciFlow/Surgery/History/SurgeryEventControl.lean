import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.EventTimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MarkedContinuation
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

def SurgeryEventControl {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) : Prop :=
  E.incoming.SingularEndpoint ∧ E.transition.boundaryFrameReversing ∧
    E.toMetricCutCapEvent.poincareStandardDiscarded

def HistoryEventControl  (H : RetainedCoreHistory.{u}) : Prop :=
  ∀ i, SurgeryEventControl (H.coreEvent i)

theorem event_control_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s) (h : SurgeryEventControl E) :
    SurgeryEventControl (RetainedCoreEvent.transport hP hQ ha hs E) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact h

theorem event_control_translate {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (h : SurgeryEventControl E) (c : ℝ) :
    SurgeryEventControl (translate_retained_event E c) :=
  ⟨(translated_event_singular E c).mpr h.1,h.2⟩

theorem controlled_event_geometry {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (h : SurgeryEventControl E) :
    GC.Surgery.ActualMetricEventGeometry E.toMetricCutCapEvent :=
  GC.Surgery.actual_metric_event_geometry E.toMetricCutCapEvent h.2.1 h.2.2

theorem history_control_append {Q : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hi : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (hE : SurgeryEventControl E) :
    HistoryEventControl (H.appendEvent E.incoming.lt E hi) := by
  intro i
  cases i using Fin.lastCases with
  | last =>
    change SurgeryEventControl (H.extendCoreEventFamily E (Fin.last H.eventCount))
    rw [H.extendCoreEventFamily_last]
    exact event_control_transport _ _ _ _ E hE
  | cast i =>
    change SurgeryEventControl (H.extendCoreEventFamily E i.castSucc)
    rw [H.extendCoreEventFamily_castSucc]
    exact event_control_transport _ _ _ _ (H.coreEvent i) (hH i)

theorem history_control_extend
    (H : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) {T : ℝ}
    (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab
      (H.time (Fin.last H.eventCount)) T)
    (hi : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    HistoryEventControl (H.extendHorizon T hT S hi) := hH

end GC.GeneralFlow
