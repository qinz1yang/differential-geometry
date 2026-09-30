import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ConcatenationHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalProduction
set_option autoImplicit false
noncomputable section
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem general_controlled_history_extension
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory)
    (hH : HistoryEventControl H) (B : ℝ) (hB : H.horizon < B) :
    ∃ (J : RetainedCoreHistory.{u}) (A' : InitialIdentification P g J.toHistory),
      J.horizon = B ∧ A.IsPrefixOf A' ∧ HistoryEventControl J ∧
      ∀ i, GC.Surgery.ActualMetricEventGeometry (J.coreEvent i).toMetricCutCapEvent := by
  let Q := H.stage (Fin.last H.eventCount)
  let m := H.initialMetric (Fin.last H.eventCount)
  let c := H.time (Fin.last H.eventCount)
  have hlen : 0 < B-c := sub_pos.mpr (H.time_le_horizon.trans_lt hB)
  obtain ⟨K,A₀,p,hKB,hprefix,⟨records⟩,hbfr,hdisc,-⟩ :=
    general_finite_geometric_horizon Q m (B-c) hlen
  have hs : K.stage 0 = H.stage (Fin.last H.eventCount) := by
    simpa only [Fin.cast_zero,ObservedHistory.restrict_stage_zero]
      using hprefix.1.presentation.stage_eq 0
  have hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)) := by
    simpa only [Fin.cast_zero,ObservedHistory.restrict_initialMetric_zero,
      ObservedHistory.restrict_stage_zero] using hprefix.1.presentation.initialMetric_heq 0
  have hK : HistoryEventControl K := fun i => ⟨(records i).singular,hbfr i,hdisc i⟩
  have htarget : K.horizon+c = B := by rw [hKB];ring
  have hbefore : H.horizon ≤ K.horizon + H.time (Fin.last H.eventCount) := by
    rw [htarget]
    exact hB.le
  obtain ⟨J,A',ha,hj,-,hc,hgeom⟩ :=
    marked_finite_history_concatenation H A K hH hK hs hm hbefore
  exact ⟨J,A',hj.trans htarget,ha,hc,hgeom⟩

end GC.GeneralFlow
