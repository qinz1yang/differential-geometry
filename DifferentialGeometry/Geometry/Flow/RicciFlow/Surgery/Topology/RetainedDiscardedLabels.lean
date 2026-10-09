import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapReconstruction
import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
namespace GC.Surgery
open DifferentialGeometry.Topology
open scoped Manifold ContDiff
set_option autoImplicit false
universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

noncomputable def presentationComponentEquiv : ConnectedComponents E.capped.Carrier ≃
    ConnectedComponents (Q.Carrier ⊕ E.discarded.Carrier) where
  toFun := E.presentation.continuous.connectedComponentsMap
  invFun := E.presentation.symm.continuous.connectedComponentsMap
  left_inv K := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe K
    rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk,
      E.presentation.symm_apply_apply]
  right_inv K := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe K
    rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk,
      E.presentation.apply_symm_apply]

theorem presentationComponentEquiv_actual (x : E.capped.Carrier) :
    presentationComponentEquiv E (ConnectedComponents.mk x) =
      ConnectedComponents.mk (E.presentation x) := rfl

theorem retained_discarded_component_ne (q : Q.Carrier) (d : E.discarded.Carrier) :
    ConnectedComponents.mk (Sum.inl q : Q.Carrier ⊕ E.discarded.Carrier) ≠
      ConnectedComponents.mk (Sum.inr d) := by
  intro h
  have hx : (Sum.inr d : Q.Carrier ⊕ E.discarded.Carrier) ∈
      connectedComponent (Sum.inl q) := ConnectedComponents.coe_eq_coe'.mp h.symm
  have hin : (Sum.inr d : Q.Carrier ⊕ E.discarded.Carrier) ∈ Set.range Sum.inl :=
    isPreconnected_connectedComponent.subset_isClopen
      (isClopen_range_inl (X := Q.Carrier) (Y := E.discarded.Carrier))
      ⟨Sum.inl q, mem_connectedComponent, ⟨q, rfl⟩⟩ hx
  obtain ⟨x, hx⟩ := hin
  exact Sum.inl_ne_inr hx

theorem cap_component_retained_or_discarded (K : ConnectedComponents E.capped.Carrier) :
    (∃ q : Q.Carrier,
      presentationComponentEquiv E K = ConnectedComponents.mk (Sum.inl q) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (E.capped.component K).toClosedOrientedManifold
        (Q.component (ConnectedComponents.mk q)).toClosedOrientedManifold)) ∨
    (∃ d : E.discarded.Carrier,
      presentationComponentEquiv E K = ConnectedComponents.mk (Sum.inr d) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (E.capped.component K).toClosedOrientedManifold
        (E.discarded.component (ConnectedComponents.mk d)).toClosedOrientedManifold)) := by
  let e : ClosedOrientedManifold.OrientedDiffeomorph E.capped
      (ClosedOrientedManifold.sum Q E.discarded) :=
    ⟨E.presentation, E.presentation_preservesOrientation⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe K
  rcases h : E.presentation x with q | d
  · left
    refine ⟨q, ?_, ?_⟩
    · exact congrArg ConnectedComponents.mk h
    · have hc : e.1.continuous.connectedComponentsMap (ConnectedComponents.mk x) =
          ConnectedComponents.mk (Sum.inl q) := congrArg ConnectedComponents.mk h
      refine ⟨(e.component (ConnectedComponents.mk x)).trans ?_⟩
      rw [hc]
      exact ClosedOrientedManifold.sumComponentInlOrientedDiffeomorph q
  · right
    refine ⟨d, ?_, ?_⟩
    · exact congrArg ConnectedComponents.mk h
    · have hc : e.1.continuous.connectedComponentsMap (ConnectedComponents.mk x) =
          ConnectedComponents.mk (Sum.inr d) := congrArg ConnectedComponents.mk h
      refine ⟨(e.component (ConnectedComponents.mk x)).trans ?_⟩
      rw [hc]
      exact ClosedOrientedManifold.sumComponentInrOrientedDiffeomorph d

noncomputable def reconstructedComponentEquiv (R : CutCapSumData E) :
    (Σ w : R.Group, {K // K ∈ R.factors w}) ≃
      ConnectedComponents (Q.Carrier ⊕ E.discarded.Carrier) :=
  R.componentEquiv.trans (presentationComponentEquiv E)

theorem reconstructed_component_coverage (R : CutCapSumData E)
    (C : ConnectedComponents (Q.Carrier ⊕ E.discarded.Carrier)) :
    ∃! x : (Σ w : R.Group, {K // K ∈ R.factors w}),
      presentationComponentEquiv E x.2.1 = C := by
  exact (reconstructedComponentEquiv E R).bijective.existsUnique C

theorem terminal_component_coverage [IsEmpty Q.Carrier]
    (K : ConnectedComponents E.capped.Carrier) :
    ∃ d : E.discarded.Carrier,
      presentationComponentEquiv E K = ConnectedComponents.mk (Sum.inr d) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (E.capped.component K).toClosedOrientedManifold
        (E.discarded.component (ConnectedComponents.mk d)).toClosedOrientedManifold) := by
  rcases cap_component_retained_or_discarded E K with ⟨q, _⟩ | hd
  · exact isEmptyElim q
  · exact hd

theorem terminal_discarded_nonempty [IsEmpty Q.Carrier] :
    Nonempty E.discarded.Carrier := by
  classical
  obtain ⟨R⟩ := actual_cutCapSumData E
  let x := Classical.choice E.source_nonempty
  let w := (R.reconstruct x).1
  obtain ⟨K, _⟩ := List.exists_mem_of_ne_nil (R.factors w) (R.nonempty_factors w)
  obtain ⟨d, _⟩ := terminal_component_coverage E K
  exact ⟨d⟩

end GC.Surgery
