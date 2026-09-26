import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower
set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_regularCrossing_or_cap
    (hOld : E.old = E.transition.trace.retainedCore) (q : Q.Carrier) :
    (∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q) ∨
      ∃ (b : E.RetainedBoundaryIndex) (z : ThreeBall),
        E.transition.trace.presentation (E.transition.trace.capping.cap b.val z) = Sum.inl q := by
  by_cases hcap : q ∈ E.capRegion
  · obtain ⟨b, z, hb⟩ := hcap
    have hret : E.RetainedBoundary b := by
      rw [E.retainedBoundary_iff_capRetained b]
      rcases E.transition.trace.cap_retained_or_discarded b with h | h
      · exact h
      · obtain ⟨d, hd⟩ := h z
        exact (Sum.inr_ne_inl (hd.trans hb)).elim
    exact Or.inr ⟨⟨b, hret⟩, z, hb⟩
  · exact Or.inl (E.exists_regularCrossing_of_not_mem_capRegion hOld hcap)

theorem regularCrossing_or_cap_of_admissible_node
    (hOld : E.old = E.transition.trace.retainedCore) {p : P.Carrier} {q : Q.Carrier}
    (hnode : ∃ z : E.old, z.val.val = p ∧ E.oldOutput z = q) :
    E.RegularCrossing p q ∨
      ∃ (b : E.RetainedBoundaryIndex) (z : ThreeBall),
        E.transition.trace.presentation (E.transition.trace.capping.cap b.val z) = Sum.inl q := by
  rcases E.exists_regularCrossing_or_cap hOld q with ⟨x, hx⟩ | hcap
  · obtain ⟨z, hp, hq⟩ := hnode
    have hpx : p = x.val := hp.symm.trans ((E.oldOutput_eq_iff_of_regularCrossing z hx).mp hq)
    exact Or.inl (hpx.symm ▸ hx)
  · exact Or.inr hcap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
