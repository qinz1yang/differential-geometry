/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetRecognitionOfTiling

open Set Function Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.inter_subset_boundaries_of_dim_lt
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    {A AB B BB D : Set M} {d : ℕ} (hA : IsPLCellOn 3 A AB) (hB : IsPLCellOn 3 B BB)
    (hI : IsPLCellOn d (A ∩ B) D) (hd : d < 3) : A ∩ B ⊆ AB ∩ BB := by
  have hIempty := hI.interior_eq_empty_of_lt hd
  intro x hx
  rw [hA.boundary_eq_frontier, hB.boundary_eq_frontier,
    hA.isCompact.isClosed.frontier_eq, hB.isCompact.isClosed.frontier_eq]
  refine ⟨⟨hx.1, fun hxi => ?_⟩, hx.2, fun hxi => ?_⟩
  · obtain ⟨z, hzA, hzB⟩ := mem_closure_iff.mp (hB.subset_closure_interior hx.2)
      _ isOpen_interior hxi
    have hz : z ∈ interior (A ∩ B) := by rw [interior_inter]; exact ⟨hzA, hzB⟩
    simp only [hIempty, mem_empty_iff_false] at hz
  · obtain ⟨z, hzB, hzA⟩ := mem_closure_iff.mp (hA.subset_closure_interior hx.1)
      _ isOpen_interior hxi
    have hz : z ∈ interior (A ∩ B) := by rw [interior_inter]; exact ⟨hzA, hzB⟩
    simp only [hIempty, mem_empty_iff_false] at hz

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem exists_section34GraphSplitCell_boundary_endpoints
    [FiniteDimensional ℝ Ea] [T2Space M]
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifold 3 𝒦'.complex) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧
      section34GraphSplitCell 𝒦 𝒦' e =
        section34GraphVertexCell 𝒦 𝒦' w ∩ section34GraphVertexCell 𝒦 𝒦' w' ∧
      section34GraphSplitCell 𝒦 𝒦' e ⊆
        section34GraphVertexBoundary 𝒦 𝒦' w ∩ section34GraphVertexBoundary 𝒦 𝒦' w' := by
  obtain ⟨w, w', hne, hunion, hinter⟩ := exists_section34GraphSplitCell_endpoints hsub hmap e
  refine ⟨w, w', hne, hunion, hinter, ?_⟩
  rw [hinter]
  apply (isPLCellOn_section34GraphVertexCell hsub hmap
    hK.isCombinatorialManifoldWithBoundary w).inter_subset_boundaries_of_dim_lt
      (isPLCellOn_section34GraphVertexCell hsub hmap hK.isCombinatorialManifoldWithBoundary w')
      (hinter ▸ isPLCellOn_section34GraphSplitCell hK e) (by omega)

theorem section34GraphSplitCell_subset_vertex_boundary
    [FiniteDimensional ℝ Ea] [T2Space M]
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifold 3 𝒦'.complex)
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') (hwe : w.1 ⊆ e.1) :
    section34GraphSplitCell 𝒦 𝒦' e ⊆ section34GraphVertexBoundary 𝒦 𝒦' w := by
  classical
  obtain ⟨v, z, -, hunion, -, hbd⟩ :=
    exists_section34GraphSplitCell_boundary_endpoints hsub hmap hK e
  have hc : w.1.centroid ℝ id ∈ (v.1 : Set Ea) ∪ (z.1 : Set Ea) := by
    rw [← hunion]
    apply hwe
    rw [section34VertexIndex_eq_singleton_centroid w]
    simp only [Finset.centroid_singleton, id_eq, Finset.mem_singleton]
  have hcases : w = v ∨ w = z := by
    rcases hc with hc | hc
    · left
      apply Subtype.ext
      rw [section34VertexIndex_eq_singleton_centroid w,
        section34VertexIndex_eq_singleton_centroid v]
      rw [section34VertexIndex_eq_singleton_centroid v, Finset.coe_singleton,
        mem_singleton_iff] at hc
      exact congrArg (fun p => ({p} : Finset Ea)) hc
    · right
      apply Subtype.ext
      rw [section34VertexIndex_eq_singleton_centroid w,
        section34VertexIndex_eq_singleton_centroid z]
      rw [section34VertexIndex_eq_singleton_centroid z, Finset.coe_singleton,
        mem_singleton_iff] at hc
      exact congrArg (fun p => ({p} : Finset Ea)) hc
  rcases hcases with rfl | rfl
  · exact hbd.trans inter_subset_left
  · exact hbd.trans inter_subset_right

theorem exists_section34GraphSplitCell_of_vertex_inter_nonempty
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (w z : Section34VertexIndex 𝒦 𝒦') (hwz : w ≠ z)
    (hne : (section34GraphVertexCell 𝒦 𝒦' w ∩ section34GraphVertexCell 𝒦 𝒦' z).Nonempty) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (z.1 : Set Ea) ∧
      section34GraphSplitCell 𝒦 𝒦' e =
        section34GraphVertexCell 𝒦 𝒦' w ∩ section34GraphVertexCell 𝒦 𝒦' z := by
  classical
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let v := w.1.centroid ℝ id
  let u := z.1.centroid ℝ id
  have hvu : v ≠ u := by
    intro h
    apply hwz
    apply Subtype.ext
    rw [section34VertexIndex_eq_singleton_centroid w,
      section34VertexIndex_eq_singleton_centroid z]
    exact congrArg (fun p => ({p} : Finset Ea)) h
  have hv : {v} ∈ L.faces := singleton_centroid_mem_section34GraphCore w
  have hu : {u} ∈ L.faces := singleton_centroid_mem_section34GraphCore z
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 := fun s hs => hcore.card_le
    (fun t ht => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp ht).2) hs
  have heL : {v, u} ∈ L.faces := by
    by_contra he
    have hdis := 𝒦'.disjoint_image_graphDualCell L (restrict_faces_subset _ _) hcard hv hu hvu he
    exact hne.ne_empty (disjoint_iff_inter_eq_empty.mp hdis)
  let e : Section34EdgeIndex 𝒦 𝒦' :=
    ⟨{v, u}, heL.1, Finset.card_pair hvu, by
      rintro _ ⟨x, hx, rfl⟩
      exact heL.2 hx⟩
  refine ⟨e, ?_, ?_⟩
  · rw [section34VertexIndex_eq_singleton_centroid w,
      section34VertexIndex_eq_singleton_centroid z]
    simp only [e, v, u, Finset.coe_pair, Finset.coe_singleton, singleton_union]
  · exact (𝒦'.image_graphDualCell_inter L (restrict_faces_subset _ _) hcard hvu heL).symm

theorem pairwise_disjoint_interior_section34GraphVertexCell
    [FiniteDimensional ℝ Ea] [T2Space M]
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifold 3 𝒦'.complex) :
    Pairwise (Disjoint on fun w : Section34VertexIndex 𝒦 𝒦' =>
      interior (section34GraphVertexCell 𝒦 𝒦' w)) := by
  intro w z hwz
  change Disjoint (interior (section34GraphVertexCell 𝒦 𝒦' w))
    (interior (section34GraphVertexCell 𝒦 𝒦' z))
  rw [Set.disjoint_left]
  intro x hxw hxz
  obtain ⟨e, -, heq⟩ := exists_section34GraphSplitCell_of_vertex_inter_nonempty hsub hmap w z
    hwz ⟨x, interior_subset hxw, interior_subset hxz⟩
  have hcell := isPLCellOn_section34GraphVertexCell hsub hmap
    hK.isCombinatorialManifoldWithBoundary
  have hbd := (hcell w).inter_subset_boundaries_of_dim_lt (hcell z)
    (heq ▸ isPLCellOn_section34GraphSplitCell hK e) (by omega)
      ⟨interior_subset hxw, interior_subset hxz⟩
  have hx : x ∈ section34GraphVertexCell 𝒦 𝒦' w \ section34GraphVertexBoundary 𝒦 𝒦' w :=
    (hcell w).sdiff_boundary_eq_interior.symm ▸ hxw
  exact hx.2 hbd.1

end DifferentialGeometry.Topology.PiecewiseLinear
