import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded
import DifferentialGeometry.Topology.Connected.Sum
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open Set Function

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private local instance (M : ClosedOrientedManifold.{u} 3) : LocallyConnectedSpace M.Carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M.Carrier

private local instance : ChartedSpace (EuclideanHalfSpace 3) E.tubes.core := E.capping.coreCharts

noncomputable def sourceHomeomorphOfIsEmptyIndex [IsEmpty E.tubes.Index] :
    M.Carrier ≃ₜ Q.Carrier ⊕ E.discarded.Carrier :=
  ((Homeomorph.setCongr E.tubes.core_eq_univ_of_isEmpty_index).trans
    (Homeomorph.Set.univ M.Carrier)).symm.trans
    ((E.capping.core_embedding.isEmbedding.toHomeomorphOfSurjective
      (range_eq_univ.mp E.range_coreInclusion_eq_univ_of_isEmpty_index)).trans
        E.presentation.toHomeomorph)

@[simp]
theorem sourceHomeomorphOfIsEmptyIndex_apply [IsEmpty E.tubes.Index]
    (x : E.tubes.core) :
    E.sourceHomeomorphOfIsEmptyIndex x.val = E.presentation (E.capping.coreInclusion x) := rfl

@[simp]
theorem sourceHomeomorphOfIsEmptyIndex_symm_apply_presentation_coreInclusion
    [IsEmpty E.tubes.Index] (x : E.tubes.core) :
    E.sourceHomeomorphOfIsEmptyIndex.symm (E.presentation (E.capping.coreInclusion x)) = x.val :=
  E.sourceHomeomorphOfIsEmptyIndex.symm_apply_apply x.val

theorem mem_retainedCore_iff_sourceHomeomorphOfIsEmptyIndex_mem_range_inl
    [IsEmpty E.tubes.Index] (x : E.tubes.core) :
    x ∈ E.retainedCore ↔ E.sourceHomeomorphOfIsEmptyIndex x.val ∈
      range (Sum.inl : Q.Carrier → Q.Carrier ⊕ E.discarded.Carrier) := by
  simp only [sourceHomeomorphOfIsEmptyIndex_apply, retainedCore, mem_ofPred_eq, mem_range]
  exact exists_congr fun _ => eq_comm

private def componentEquivOfIsEmptyIndex [IsEmpty E.tubes.Index] :
    ConnectedComponents M.Carrier ≃
      ConnectedComponents Q.Carrier ⊕ ConnectedComponents E.discarded.Carrier :=
  let e := E.sourceHomeomorphOfIsEmptyIndex
  ({ toFun := e.continuous.connectedComponentsMap
     invFun := e.symm.continuous.connectedComponentsMap
     left_inv := by
       intro c
       obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
       simp only [Continuous.connectedComponentsMap_mk, e.symm_apply_apply]
     right_inv := by
       intro c
       obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
       simp only [Continuous.connectedComponentsMap_mk, e.apply_symm_apply] } :
    ConnectedComponents M.Carrier ≃ ConnectedComponents (Q.Carrier ⊕ E.discarded.Carrier)).trans
      ConnectedComponents.sumEquiv

theorem card_connectedComponents_output_add_discarded_eq_of_isEmpty_index
    [IsEmpty E.tubes.Index] :
    Nat.card (ConnectedComponents Q.Carrier) + Nat.card (ConnectedComponents E.discarded.Carrier) =
      Nat.card (ConnectedComponents M.Carrier) := by
  let e := E.componentEquivOfIsEmptyIndex
  rw [← Nat.card_sum, Nat.card_congr e]

theorem card_connectedComponents_output_lt_of_isEmpty_index
    [IsEmpty E.tubes.Index] :
    Nat.card (ConnectedComponents Q.Carrier) < Nat.card (ConnectedComponents M.Carrier) := by
  have hD : Nonempty E.discarded.Carrier :=
    E.nontrivial.resolve_left (not_nonempty_iff.mpr inferInstance)
  let _ := hD
  have hpos := Nat.card_pos (α := ConnectedComponents E.discarded.Carrier)
  have heq := E.card_connectedComponents_output_add_discarded_eq_of_isEmpty_index
  omega

theorem isEmpty_output_of_preconnected_of_isEmpty_index
    [IsEmpty E.tubes.Index] [PreconnectedSpace M.Carrier] : IsEmpty Q.Carrier := by
  let e := E.componentEquivOfIsEmptyIndex
  let _ := Equiv.subsingleton e.symm
  have hD : Nonempty E.discarded.Carrier :=
    E.nontrivial.resolve_left (not_nonempty_iff.mpr inferInstance)
  obtain ⟨d⟩ := hD
  refine ⟨fun q => ?_⟩
  have h : (Sum.inl (ConnectedComponents.mk q) :
      ConnectedComponents Q.Carrier ⊕ ConnectedComponents E.discarded.Carrier) =
      Sum.inr (ConnectedComponents.mk d) :=
    Subsingleton.elim _ _
  exact Sum.inl_ne_inr h

end SphericalCutCapTransition

end DifferentialGeometry.Topology
