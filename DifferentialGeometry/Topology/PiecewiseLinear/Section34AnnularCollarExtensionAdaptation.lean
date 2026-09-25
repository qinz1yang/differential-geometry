import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionInitial
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexMesh

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_selected_dual_cells_of_derived_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite Γ.faces] (hΓR : Γ.faces ⊆ R.faces) :
    ∃ d : Finset {v : E // ({v} : Finset E) ∈ (barycentricSubdivision R).faces},
      (derivedNeighborhood R Γ).space =
        section34AnnularCollarBase (barycentricSubdivision R) d := by
  let F := {s : Finset E // s ∈ Γ.faces}
  let _ : Fintype F := Fintype.ofFinite F
  let c : F → {v : E // ({v} : Finset E) ∈ (barycentricSubdivision R).faces} := fun s =>
    ⟨s.1.centroid ℝ id, singleton_centroid_mem_barycentricSubdivision R (hΓR s.2)⟩
  let d := Finset.univ.image c
  refine ⟨d, ?_⟩
  rw [← iUnion_derivedNeighborhoodCell_space R Γ hΓR]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    apply mem_iUnion₂.mpr
    refine ⟨c ⟨s, hs⟩, Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [derivedNeighborhoodCell_eq_dualCell R (hΓR hs)] at hxs
    exact hxs
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hv
    refine mem_iUnion₂.mpr ⟨s.1, s.2, ?_⟩
    rw [derivedNeighborhoodCell_eq_dualCell R (hΓR s.2)]
    exact hxv

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_adapted_boundary_collar_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Geometry.SimplicialComplex ℝ E) [Finite H.faces]
    (hH : IsCombinatorialManifoldWithBoundary 2 H) {P : Set E}
    (hP : P ∈ 𝓝ˢ[H.space] (boundaryComplex 2 H).space) :
    ∃ H' L : Geometry.SimplicialComplex ℝ E, IsSubdivision H' H ∧
      H'.faces.Finite ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ H.space ∩ P ∧
      (∀ x ∈ (boundaryComplex 2 H).space, L.space ∈ 𝓝[H.space] x) ∧
      ∃ d : Finset {v : E // ({v} : Finset E) ∈ H'.faces},
        L.space = section34AnnularCollarBase H' d := by
  let B := boundaryComplex 2 H
  let _ : Finite B.faces := (boundaryComplex_faces_finite 2 H).to_subtype
  obtain ⟨O, hO, hBO, hOP⟩ := mem_nhdsSetWithin.mp hP
  obtain ⟨δ, hδ, hthick⟩ := (isPolyhedron_space B).isCompact.exists_cthickening_subset_open hO hBO
  obtain ⟨R, hRH, hRfin, hdiam, hΓsub⟩ :=
    exists_isSubdivision_diam_lt_restrict_isSubdivision H B (boundaryComplex_faces_subset 2 H) hδ
  let _ : Finite R.faces := hRfin.to_subtype
  let Γ := PiecewiseLinear.restrict R B.space
  let _ : Finite Γ.faces := (restrict_faces_finite R B.space).to_subtype
  have hΓspace : Γ.space = B.space := hΓsub.space_eq
  have hΓR : Γ.faces ⊆ R.faces := restrict_faces_subset R B.space
  let L := PiecewiseLinear.derivedNeighborhood R Γ
  have hLH : L.space ⊆ H.space := (derivedNeighborhood_space_subset R Γ).trans hRH.space_eq.subset
  have hLO : L.space ⊆ O := by
    apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst z hzt
    apply hthick
    apply Metric.mem_cthickening_of_dist_le z (s.centroid ℝ id) δ B.space
      (hΓspace.subset (Γ.convexHull_subset_space hs
        (s.centroid_mem_convexHull (Γ.nonempty_of_mem_faces hs))))
    exact ((Metric.dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded
      hzt hst).trans_lt (hdiam t ht)).le
  refine ⟨PiecewiseLinear.barycentricSubdivision R, L,
    (barycentricSubdivision_isSubdivision R).trans hRH,
    Set.toFinite _, derivedNeighborhood_faces_finite R Γ,
    (hH.of_isSubdivision hRH).derivedNeighborhood Γ,
    fun x hx => ⟨hLH hx, hOP ⟨hLO hx, hLH hx⟩⟩, ?_, ?_⟩
  · intro x hx
    rw [← hRH.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin hΓR (hΓspace.symm.subset hx)
  · exact exists_selected_dual_cells_of_derived_neighborhood R Γ hΓR

end DifferentialGeometry.Topology.PiecewiseLinear
