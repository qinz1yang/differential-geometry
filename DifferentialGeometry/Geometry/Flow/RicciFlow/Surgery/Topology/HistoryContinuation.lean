import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MaximalSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.exists_extension_or_singular_incomingSlab
    (H : RetainedCoreHistory.{u})
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {B : ℝ} (hB : H.horizon < B) :
    (∃ K : RetainedCoreHistory.{u}, K.horizon = B ∧
      H.toHistory.IsPrefixOf K.toHistory ∧ K.eventCount = H.eventCount) ∨
      ∃ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s),
        s ≤ B ∧ G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) ∧ G.SingularEndpoint := by
  have hab : H.time (Fin.last H.eventCount) < B := htime.trans_lt hB
  obtain ⟨G, hinit⟩ | ⟨s, G, hs, hinit, hsing⟩ :=
    (H.stage (Fin.last H.eventCount)).exists_closedSlab_or_singular_incomingSlab_from_time
      (H.initialMetric (Fin.last H.eventCount)) hab
  · let K := H.extendHorizon B hB.le G hinit
    have hcompat := H.extendHorizonCompatible_of_time_eq_horizon B G hinit htime
    exact Or.inl ⟨K, rfl, H.extendHorizon_isPrefixOf B hB.le G hinit hcompat, rfl⟩
  · exact Or.inr ⟨s, G, hs, hinit, hsing⟩

theorem RetainedCoreHistory.exists_extension_or_oneStepIncoming
    (H : RetainedCoreHistory.{u})
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    (parameters : CutoffParameters) {B : ℝ} (hB : H.horizon < B) :
    (∃ K : RetainedCoreHistory.{u}, K.horizon = B ∧
      H.toHistory.IsPrefixOf K.toHistory ∧ K.eventCount = H.eventCount) ∨
      ∃ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s)
        (L : G.TerminalLimitMetric) (D : OneStepIncoming.{u}),
        H.horizon < s ∧ s ≤ B ∧
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) ∧
        D.stage = H.stage (Fin.last H.eventCount) ∧
        D.startTime = H.time (Fin.last H.eventCount) ∧ D.endTime = s ∧
        HEq D.slab G ∧ HEq D.terminal L ∧ D.parameters = parameters ∧
        HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)) := by
  rcases H.exists_extension_or_singular_incomingSlab htime hB with h | ⟨s, G, hs, hinit, hsing⟩
  · exact Or.inl h
  · obtain ⟨L⟩ := G.nonempty_terminalLimitMetric
    let D : OneStepIncoming.{u} := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := htime.symm ▸ H.horizon_nonneg
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := parameters }
    exact Or.inr ⟨s, G, L, D, htime ▸ G.lt, hs, hinit, rfl, rfl, rfl,
      HEq.rfl, HEq.rfl, rfl, heq_of_eq hinit⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
