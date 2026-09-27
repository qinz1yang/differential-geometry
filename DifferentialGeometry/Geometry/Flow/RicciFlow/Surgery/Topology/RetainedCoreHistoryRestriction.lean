import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

namespace RetainedCoreHistory
variable {P : OrientedThreeStage.{u}}

def restrict (H : RetainedCoreHistory P)
    (t : Icc (0 : ℝ) H.horizon) : RetainedCoreHistory P := by
  let K := H.toHistory.restrict t
  let k := H.toHistory.activeStage t
  have hk : k.val ≤ H.eventCount := Nat.le_of_lt_succ k.isLt
  let cast : Fin (k.val + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.add_le_add_right hk 1)
  refine {
    horizon := K.horizon
    horizon_nonneg := K.horizon_nonneg
    eventCount := K.eventCount
    time := K.time
    time_strictMono := K.time_strictMono
    time_zero := K.time_zero
    time_le_horizon := K.time_le_horizon
    stage := K.stage
    initialMetric := K.initialMetric
    coreEvent := fun i => ?_
    event_initial := ?_
    event_output := ?_
    finalSlab := K.finalSlab
    final_initial := K.final_initial }
  · let j : Fin H.eventCount := Fin.castLE (Nat.le_of_lt_succ k.isLt) i
    exact RetainedCoreEvent.transport
      (ObservedHistory.restrict_stage_apply H.toHistory t i.castSucc).symm
      (ObservedHistory.restrict_stage_apply H.toHistory t i.succ).symm
      (ObservedHistory.restrict_time_apply H.toHistory t i.castSucc).symm
      (ObservedHistory.restrict_time_apply H.toHistory t i.succ).symm
      (H.coreEvent j)
  · intro i
    let j : Fin H.eventCount := Fin.castLE (Nat.le_of_lt_succ k.isLt) i
    have hE := RetainedCoreEvent.transport_incoming_metric_heq
      (ObservedHistory.restrict_stage_apply H.toHistory t i.castSucc).symm
      (ObservedHistory.restrict_stage_apply H.toHistory t i.succ).symm
      (ObservedHistory.restrict_time_apply H.toHistory t i.castSucc).symm
      (ObservedHistory.restrict_time_apply H.toHistory t i.succ).symm
      (H.coreEvent j) (K.time i.castSucc)
    have htime : K.time i.castSucc = H.time j.castSucc := by
      exact ObservedHistory.restrict_time_apply H.toHistory t i.castSucc
    have hinit : HEq (K.initialMetric i.castSucc) (H.initialMetric j.castSucc) :=
      ObservedHistory.restrict_initialMetric_heq H.toHistory t i.castSucc
    exact eq_of_heq (hE.trans ((heq_of_eq (congrArg
      (fun s : ℝ => (H.coreEvent j).toMetricCutCapEvent.incoming.flow.base.metric s)
      htime)).trans ((heq_of_eq (H.event_initial j)).trans hinit.symm)))
  · intro i
    let j : Fin H.eventCount := Fin.castLE (Nat.le_of_lt_succ k.isLt) i
    have hE := RetainedCoreEvent.transport_outputMetric_heq
      (ObservedHistory.restrict_stage_apply H.toHistory t i.castSucc).symm
      (ObservedHistory.restrict_stage_apply H.toHistory t i.succ).symm
      (ObservedHistory.restrict_time_apply H.toHistory t i.castSucc).symm
      (ObservedHistory.restrict_time_apply H.toHistory t i.succ).symm
      (H.coreEvent j)
    have hout := H.event_output j
    have hmetric : HEq (K.initialMetric i.succ) (H.initialMetric j.succ) :=
      ObservedHistory.restrict_initialMetric_heq H.toHistory t i.succ
    exact eq_of_heq (hE.trans ((heq_of_eq hout).trans hmetric.symm))

@[simp] theorem restrict_toHistory (H : RetainedCoreHistory P)
    (t : Icc (0 : ℝ) H.horizon) :
    (H.restrict t).toHistory = H.toHistory.restrict t := rfl

end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
