import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReconstructionSlots
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.LateOrEmpty
namespace GC.Surgery
open DifferentialGeometry.Topology
set_option autoImplicit false
universe u

theorem exists_classified_reconstruction
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q) :
    ∃ R : CutCapSumData E,
      Function.Bijective (presentationComponentEquiv E ∘ componentSlot R) ∧
      ∀ s : (Σ w : R.Group, Fin (R.factors w).length),
        (∃ q : Q.Carrier,
          presentationComponentEquiv E (componentSlot R s) =
            ConnectedComponents.mk (Sum.inl q) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (E.capped.component (componentSlot R s)).toClosedOrientedManifold
            (Q.component (ConnectedComponents.mk q)).toClosedOrientedManifold)) ∨
        (∃ d : E.discarded.Carrier,
          presentationComponentEquiv E (componentSlot R s) =
            ConnectedComponents.mk (Sum.inr d) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (E.capped.component (componentSlot R s)).toClosedOrientedManifold
            (E.discarded.component (ConnectedComponents.mk d)).toClosedOrientedManifold)) := by
  obtain ⟨R⟩ := actual_cutCapSumData E
  exact ⟨R, actual_target_slot_bijective R,
    fun s => cap_component_retained_or_discarded E (componentSlot R s)⟩

end GC.Surgery

namespace GC.Surgery
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
set_option autoImplicit false
universe u

theorem marked_late_or_empty_prefixes
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) :
    (∃ (a : ℝ) (ha : 0 ≤ a) (A : InitialIdentification P g (T.observe a ha)),
      A = T.observeInitial a ha ∧
      (∀ (b : ℝ) (hb : 0 ≤ b), a ≤ b →
        IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier) ∧
      (∀ s ∈ T.eventTimes, s ≤ a)) ∨
    (∀ B : ℝ, ∃ (t : ℝ) (ht : 0 < t)
      (A : InitialIdentification P g (T.observe t ht.le)), B < t ∧ t ∉ T.eventTimes ∧
      (T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount) < t ∧
      A = T.observeInitial t ht.le ∧
      Nonempty ((T.observe t ht.le).stage (Fin.last (T.observe t ht.le).eventCount)).Carrier) := by
  rcases late_nonempty_or_absorbing_empty T with ⟨a, ha, hempty, hevents⟩ | hlate
  · exact Or.inl ⟨a, ha, T.observeInitial a ha, rfl, hempty, hevents⟩
  · right
    intro B
    obtain ⟨t, ht, hB, hn, hs, hnonempty⟩ := hlate B
    exact ⟨t, ht, T.observeInitial t ht.le, hB, hn, hs, rfl, hnonempty⟩

end GC.Surgery
