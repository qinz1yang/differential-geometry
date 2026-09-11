import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected
import DifferentialGeometry.Topology.SphereSeparation.ComplementPair

set_option autoImplicit false

open Function Set

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem finTwo_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  refine Fin.cases (Or.inl rfl) (fun j => ?_) i
  exact Fin.cases (Or.inr rfl) (fun k => Fin.elim0 k) j

noncomputable def complementPairOfComponentCount
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {S : Set X} (hopen : IsOpen Sᶜ)
    (hcount : Nonempty (ConnectedComponents (Sᶜ : Set X) ≃ Fin 2)) :
    ComplementPair S := by
  let e : ConnectedComponents (Sᶜ : Set X) ≃ Fin 2 := Classical.choice hcount
  let c0 : ConnectedComponents (Sᶜ : Set X) := e.symm 0
  let c1 : ConnectedComponents (Sᶜ : Set X) := e.symm 1
  let x0 : (Sᶜ : Set X) := Classical.choose (ConnectedComponents.surjective_coe c0)
  let x1 : (Sᶜ : Set X) := Classical.choose (ConnectedComponents.surjective_coe c1)
  have hx0 : (x0 : ConnectedComponents (Sᶜ : Set X)) = c0 :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c0)
  have hx1 : (x1 : ConnectedComponents (Sᶜ : Set X)) = c1 :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c1)
  have he0 : e (x0 : ConnectedComponents (Sᶜ : Set X)) = 0 := by
    rw [hx0]
    simp [c0]
  have he1 : e (x1 : ConnectedComponents (Sᶜ : Set X)) = 1 := by
    rw [hx1]
    simp [c1]
  have hcomponents_ne : connectedComponent x0 ≠ connectedComponent x1 := by
    rw [← ConnectedComponents.coe_ne_coe]
    intro hEq
    have := congrArg e hEq
    simp [he0, he1] at this
  exact
    { left := connectedComponentIn Sᶜ x0
      right := connectedComponentIn Sᶜ x1
      isOpen_left := hopen.connectedComponentIn
      isOpen_right := hopen.connectedComponentIn
      isConnected_left := isConnected_connectedComponentIn_iff.mpr x0.2
      isConnected_right := isConnected_connectedComponentIn_iff.mpr x1.2
      disjoint := by
        rw [connectedComponentIn_eq_image x0.2, connectedComponentIn_eq_image x1.2]
        exact (connectedComponent_disjoint hcomponents_ne).image
          (f := (Subtype.val : (Sᶜ : Set X) → X)) (u := Set.univ)
          Subtype.coe_injective.injOn (subset_univ _) (subset_univ _)
      union_eq_compl := by
        apply Set.Subset.antisymm
        · exact union_subset (connectedComponentIn_subset _ _)
            (connectedComponentIn_subset _ _)
        · intro x hx
          let y : (Sᶜ : Set X) := ⟨x, hx⟩
          have hy0 : e (y : ConnectedComponents (Sᶜ : Set X)) = 0 →
              x ∈ connectedComponentIn Sᶜ x0 := by
            intro hlabel
            have hquot : (y : ConnectedComponents (Sᶜ : Set X)) = x0 :=
              e.injective (hlabel.trans he0.symm)
            rw [connectedComponentIn_eq_image x0.2]
            exact ⟨y, ConnectedComponents.coe_eq_coe'.mp hquot, rfl⟩
          have hy1 : e (y : ConnectedComponents (Sᶜ : Set X)) = 1 →
              x ∈ connectedComponentIn Sᶜ x1 := by
            intro hlabel
            have hquot : (y : ConnectedComponents (Sᶜ : Set X)) = x1 :=
              e.injective (hlabel.trans he1.symm)
            rw [connectedComponentIn_eq_image x1.2]
            exact ⟨y, ConnectedComponents.coe_eq_coe'.mp hquot, rfl⟩
          have hlabel : e (y : ConnectedComponents (Sᶜ : Set X)) = 0 ∨
              e (y : ConnectedComponents (Sᶜ : Set X)) = 1 := by
            generalize hz : e (y : ConnectedComponents (Sᶜ : Set X)) = z
            have hzcase : z = 0 ∨ z = 1 := by
              refine Fin.cases (Or.inl rfl) (fun i => ?_) z
              exact Fin.cases (Or.inr rfl) (fun j => Fin.elim0 j) i
            exact hzcase
          rcases hlabel with hlabel | hlabel
          · exact Or.inl (hy0 hlabel)
          · exact Or.inr (hy1 hlabel) }

noncomputable def connectedComponentsComplEquivFinTwo
    {X : Type*} [TopologicalSpace X] {S : Set X} (d : SphereSides S) :
    ConnectedComponents (Sᶜ : Set X) ≃ Fin 2 := by
  let B : Set (Sᶜ : Set X) := Subtype.val ⁻¹' d.compactSide
  let E : Set (Sᶜ : Set X) := Subtype.val ⁻¹' d.endSide
  have hBopen : IsOpen B := d.isOpen_compactSide.preimage continuous_subtype_val
  have hEopen : IsOpen E := d.isOpen_endSide.preimage continuous_subtype_val
  have hBcompl : Bᶜ = E := by
    ext x
    have hxSides : x.1 ∈ d.compactSide ∪ d.endSide := by
      rw [d.union_eq_compl]
      exact x.2
    constructor
    · intro hx
      rcases hxSides with hxB | hxE
      · exact False.elim (hx hxB)
      · exact hxE
    · intro hxE hxB
      exact Set.disjoint_left.1 d.disjoint hxB hxE
  have hEcompl : Eᶜ = B := by
    rw [← hBcompl, compl_compl]
  have hBclopen : IsClopen B :=
    ⟨isOpen_compl_iff.mp (hBcompl ▸ hEopen), hBopen⟩
  have hEclopen : IsClopen E :=
    ⟨isOpen_compl_iff.mp (hEcompl ▸ hBopen), hEopen⟩
  have hBimage : Subtype.val '' B = d.compactSide := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, d.compactSide_subset_compl hx⟩, hx, rfl⟩
  have hEimage : Subtype.val '' E = d.endSide := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, d.endSide_subset_compl hx⟩, hx, rfl⟩
  have hBconnected : IsConnected B := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := d.compactSide_nonempty
      exact ⟨⟨x, d.compactSide_subset_compl hx⟩, hx⟩
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hBimage]
      exact d.isConnected_compactSide.isPreconnected
  have hEconnected : IsConnected E := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := d.endSide_nonempty
      exact ⟨⟨x, d.endSide_subset_compl hx⟩, hx⟩
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hEimage]
      exact d.isConnected_endSide.isPreconnected
  let U : Fin 2 → Set (Sᶜ : Set X) := Fin.cases B (fun _ => E)
  apply ConnectedComponents.equivOfIsClopenOfIsConnected
    (U := U)
  · intro i
    rcases finTwo_eq_zero_or_one i with rfl | rfl
    · exact hBclopen
    · exact hEclopen
  · intro i j hij
    rcases finTwo_eq_zero_or_one i with rfl | rfl <;>
      rcases finTwo_eq_zero_or_one j with rfl | rfl
    · exact False.elim (hij rfl)
    · exact d.disjoint.preimage Subtype.val
    · exact (d.disjoint.preimage Subtype.val).symm
    · exact False.elim (hij rfl)
  · ext x
    constructor
    · rintro ⟨i, hi⟩
      trivial
    · intro _
      have hxSides : x.1 ∈ d.compactSide ∪ d.endSide := by
        rw [d.union_eq_compl]
        exact x.2
      rcases hxSides with hxB | hxE
      · exact Set.mem_iUnion.2 ⟨0, hxB⟩
      · exact Set.mem_iUnion.2 ⟨1, hxE⟩
  · intro i
    rcases finTwo_eq_zero_or_one i with rfl | rfl
    · exact hBconnected
    · exact hEconnected

end DifferentialGeometry.Topology.SphereSeparation
