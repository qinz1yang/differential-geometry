import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_stage_incomingSlab_metric
    (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) (hj : H.time j < H.stageEndTime j) :
    ∃ G : (H.stage j).IncomingSlab (H.time j) (H.stageEndTime j),
      ∀ t, G.flow.base.metric t = H.stageMetric j t := by
  cases j using Fin.lastCases with
  | last =>
      rw [H.stageEndTime_last]
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by simpa only [H.stageEndTime_last] using hj
      refine ⟨(H.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfinal]
      rfl
  | cast i =>
      rw [H.stageEndTime_castSucc]
      refine ⟨(H.event i).incoming, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_castSucc]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
