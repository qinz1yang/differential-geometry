import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SlabCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryContinuation
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- A bounded number of possible events forces continuation of the actual observation. -/
theorem RetainedCoreHistory.exists_closedSlab_extension_of_eventCount_bounded
    (H : RetainedCoreHistory.{u}) (S : Set (RetainedCoreHistory.{u}))
    (hH : H ∈ S) {B : ℝ} {N : ℕ}
    (hprefix : ∀ K ∈ S, H.toHistory.IsPrefixOf K.toHistory)
    (hhorizon : ∀ K ∈ S, K.horizon ≤ B)
    (hcount : ∀ K ∈ S, K.eventCount ≤ N)
    (hproduce : ∀ K ∈ S, K.horizon < B →
      ∀ (s : ℝ) (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s),
      s ≤ B →
      G.flow.base.metric (K.time (Fin.last K.eventCount)) =
        K.initialMetric (Fin.last K.eventCount) → G.SingularEndpoint →
      ∃ (Q : OrientedThreeStage.{u})
        (E : RetainedCoreEvent (K.stage (Fin.last K.eventCount)) Q
          (K.time (Fin.last K.eventCount)) s)
        (hinit : E.incoming.flow.base.metric (K.time (Fin.last K.eventCount)) =
          K.initialMetric (Fin.last K.eventCount)),
        E.incoming = G ∧ K.appendEvent E.incoming.lt E hinit ∈ S) :
    ∃ J ∈ S, J.horizon = B ∨
      ∃ (hB : J.horizon ≤ B)
        (G : (J.stage (Fin.last J.eventCount)).ClosedSlab
          (J.time (Fin.last J.eventCount)) B)
        (hG : G.flow.base.metric (J.time (Fin.last J.eventCount)) =
          J.initialMetric (Fin.last J.eventCount)),
        H.toHistory.IsPrefixOf (J.extendHorizon B hB G hG).toHistory := by
  classical
  have hfinite : (RetainedCoreHistory.eventCount '' S).Finite := by
    apply (Set.finite_Iic N).subset
    rintro n ⟨K, hK, rfl⟩
    exact hcount K hK
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image
    (RetainedCoreHistory.eventCount '' S) id hfinite ⟨H.eventCount, H, hH, rfl⟩
  obtain ⟨K, hK, rfl⟩ := hn
  have hmaxK : ∀ L ∈ S, L.eventCount ≤ K.eventCount :=
    fun L hL => hmax _ ⟨L, hL, rfl⟩
  rcases eq_or_lt_of_le (hhorizon K hK) with heq | hlt
  · exact ⟨K, hK, Or.inl heq⟩
  obtain ⟨G, hinit⟩ | ⟨s, G, hs, hinit, hsing⟩ :=
    (K.stage (Fin.last K.eventCount)).exists_closedSlab_or_singular_incomingSlab_from_time
      (K.initialMetric (Fin.last K.eventCount)) (K.time_le_horizon.trans_lt hlt)
  · refine ⟨K, hK, Or.inr ⟨hlt.le, G, hinit, ?_⟩⟩
    exact (hprefix K hK).trans
      (GC.GeneralFlow.actual_closed_extension_preserves_prefix K hlt.le G hinit)
  · obtain ⟨Q, E, hE, -, hmem⟩ := hproduce K hK hlt s G hs hinit hsing
    have hbad := hmaxK (K.appendEvent E.incoming.lt E hE) hmem
    change K.eventCount + 1 ≤ K.eventCount at hbad
    omega

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
