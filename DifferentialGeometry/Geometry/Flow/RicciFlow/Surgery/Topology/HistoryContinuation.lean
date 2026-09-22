import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MaximalSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.exists_extension_or_singular_incomingSlab
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {B : ℝ} (hB : H.horizon < B) :
    (∃ K : RetainedCoreHistory P, K.horizon = B ∧
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
