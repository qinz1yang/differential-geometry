import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexNeighborhood
import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarCommonRefinement
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementRestriction

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_subcomplex_neighborhood_preserving_expansions
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    {A U : Set E} (hA : IsCompact A) (hAK : A ⊆ K.space)
    (hU : IsOpen U) (hAU : A ⊆ U) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ P J D : SimplicialComplex ℝ E,
      P.faces.Finite ∧ P.space = K.space ∧ simplicialRefines P K ∧
      (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      J.faces.Finite ∧ J.faces ⊆ P.faces ∧ J.space = L.space ∧ simplicialRefines J L ∧
      D.faces.Finite ∧ D.faces ⊆ P.faces ∧ D.space ⊆ U ∧ A ⊆ D.space ∧
      (Subtype.val ⁻¹' A : Set P.space) ⊆ interior (Subtype.val ⁻¹' D.space) ∧
      ∀ S C, FiniteSimplexExpansionIn K S C → FiniteSimplexExpansionIn P S C := by
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA.isClosed hU hAU
  let N := K.space ∩ closure V
  have hN : IsCompact N := (isCompact_space_of_finite_faces K hK).inter_right isClosed_closure
  have hNU : N ⊆ U := fun _ hx => hVU hx.2
  obtain ⟨Q, hQ, hQspace, -, hnear⟩ :=
    exists_subdivision_faces_near_compact K hK hN hU hNU
  obtain ⟨P, hP, hPspace, hPK, hPQ, hPdim, hexp⟩ :=
    exists_common_refinement_preserving_expansions K Q hK hQ hQspace.symm.subset hd
  let J := complexRestriction P L
  have hJspace : J.space = L.space :=
    complexRestriction_space_of_refines P K L hPK hPspace hLK
  let D := simplicialNeighborhood P N
  have hDspace : D.space ⊆ U := by
    apply simplicialNeighborhood_space_subset P N U
    intro s hs hmeet
    obtain ⟨t, ht, hst⟩ := hPQ s hs
    apply hst.trans (hnear t ht ?_)
    obtain ⟨x, hxs, hxN⟩ := hmeet
    exact ⟨x, hst hxs, hxN⟩
  refine ⟨P, J, D, hP, hPspace, hPK, hPdim,
    complexRestriction_finite_faces P L hP, complexRestriction_faces_subset P L,
    hJspace, complexRestriction_refines_right P L,
    simplicialNeighborhood_finite_faces P hP N,
    simplicialNeighborhood_faces_subset P N, hDspace, ?_, ?_, hexp⟩
  · intro x hx
    apply subset_simplicialNeighborhood P N
    exact ⟨⟨hAK hx, subset_closure (hAV hx)⟩, hPspace.symm ▸ hAK hx⟩
  · have hVsub : (Subtype.val ⁻¹' V : Set P.space) ⊆ Subtype.val ⁻¹' D.space := by
      intro x hx
      apply subset_simplicialNeighborhood P N
      exact ⟨⟨hPspace ▸ x.2, subset_closure hx⟩, x.2⟩
    exact (preimage_mono hAV).trans
      ((hV.preimage continuous_subtype_val).subset_interior_iff.mpr hVsub)

end DifferentialGeometry.Topology.Engulfing
