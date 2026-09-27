/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteManifoldFaces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ControlledVertexCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RefinedResidualDisks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

noncomputable def section34GraphResidualCell (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
    (t : Finset Ea) : Set M :=
  closure (simplexBody 𝒦 t \ ⋃ w : Section34VertexIndex 𝒦 𝒦',
    section34GraphVertexCell 𝒦 𝒦' w)

variable [T2Space M] {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

omit [T2Space M] in
private theorem isCompact_simplexBody_of_mem_faces {t : Finset Ea}
    (ht : t ∈ 𝒦.complex.faces) : IsCompact (simplexBody 𝒦 t) :=
  (t.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
    (𝒦.continuousOn.mono (𝒦.complex.convexHull_subset_space ht))

theorem section34GraphResidualCell_subset_simplexBody {t : Finset Ea}
    (ht : t ∈ 𝒦.complex.faces) : section34GraphResidualCell 𝒦 𝒦' t ⊆ simplexBody 𝒦 t :=
  closure_minimal sdiff_subset (isCompact_simplexBody_of_mem_faces ht).isClosed

theorem isCompact_section34GraphResidualCell {t : Finset Ea}
    (ht : t ∈ 𝒦.complex.faces) : IsCompact (section34GraphResidualCell 𝒦 𝒦' t) :=
  (isCompact_simplexBody_of_mem_faces ht).of_isClosed_subset isClosed_closure
    (section34GraphResidualCell_subset_simplexBody ht)

theorem section34GraphResidualCell_subset {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    section34GraphResidualCell 𝒦 𝒦' t ⊆ U := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := section34GraphResidualCell_subset_simplexBody ht hx
  exact 𝒦.bijOn.mapsTo (𝒦.complex.convexHull_subset_space ht hy)

theorem locallyFinite_section34GraphResidualCell
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) (k : ℕ) :
    ∀ x ∈ U, ∃ V ∈ 𝓝 x, {s : Section34SimplexIndex 𝒦 k |
      (section34GraphResidualCell 𝒦 𝒦' s.1 ∩ V).Nonempty}.Finite := by
  have hlf : LocallyFinite fun s : Section34SimplexIndex 𝒦 k =>
      (Subtype.val : U → M) ⁻¹' simplexBody 𝒦 s.1 := by
    let f : Section34SimplexIndex 𝒦 k → 𝒦.complex.faces := fun s => ⟨s.1, s.2.1⟩
    apply (locallyFinite_simplexBody_subtype 𝒦).comp_injective (g := f)
    intro s t hst
    exact Subtype.ext (congrArg (fun r : 𝒦.complex.faces => r.1) hst)
  intro x hx
  obtain ⟨V, hV, hfin⟩ := hlf ⟨x, hx⟩
  rw [nhds_subtype_eq_comap] at hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
  refine ⟨W, hW, hfin.subset ?_⟩
  rintro s ⟨y, hy, hyW⟩
  exact ⟨⟨y, section34GraphResidualCell_subset s.2.1 hy⟩,
    section34GraphResidualCell_subset_simplexBody s.2.1 hy, hWV hyW⟩

theorem eq_iUnion_section34GraphVertexCell_union_residuals [FiniteDimensional ℝ Ea]
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex) :
    U = (⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w) ∪
      ⋃ t : Section34SimplexIndex 𝒦 4, section34GraphResidualCell 𝒦 𝒦' t.1 := by
  apply Subset.antisymm
  · intro x hx
    by_cases hxN : x ∈ ⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w
    · exact Or.inl hxN
    · obtain ⟨p, hp, rfl⟩ := 𝒦.bijOn.surjOn hx
      obtain ⟨s, hs, hps⟩ := 𝒦.complex.mem_space_iff.mp hp
      obtain ⟨t, ht, hst, hcard⟩ := 𝒦.exists_face_superset_card_eq hK hs
      refine Or.inr (mem_iUnion.mpr ⟨⟨t, ht, hcard⟩, subset_closure ⟨?_, hxN⟩⟩)
      exact ⟨p, convexHull_mono (Finset.coe_subset.mpr hst) hps, rfl⟩
  · refine union_subset (iUnion_subset fun w => ?_)
      (iUnion_subset fun t => section34GraphResidualCell_subset t.2.1)
    exact (section34GraphVertexCell_subset_carrierSupport w).trans
      ((locallyFinite_section34CarrierSupport 𝒦').1 w.1)

open Classical in
theorem image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    𝒦'.map '' closure (convexHull ℝ (t : Set Ea) \
      (derivedNeighborhood 𝒦'.complex
        (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦))).space) =
      section34GraphResidualCell 𝒦 𝒦' t := by
  let P := convexHull ℝ (t : Set Ea)
  let N := (derivedNeighborhood 𝒦'.complex
    (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦))).space
  have hPc : IsCompact P := t.finite_toSet.isCompact_convexHull ℝ
  have hcl : closure (P \ N) ⊆ P := closure_minimal sdiff_subset hPc.isClosed
  have hPK : P ⊆ 𝒦'.complex.space :=
    (𝒦.complex.convexHull_subset_space ht).trans hsub.space_eq.symm.subset
  have hNK : N ⊆ 𝒦'.complex.space := derivedNeighborhood_space_subset _ _
  have himage : 𝒦'.map '' closure (P \ N) = closure (𝒦'.map '' (P \ N)) :=
    image_closure_of_isCompact (hPc.of_isClosed_subset isClosed_closure hcl)
      (𝒦'.continuousOn.mono (hcl.trans hPK))
  have hdiff : 𝒦'.map '' (P \ N) = simplexBody 𝒦 t \ 𝒦'.map '' N := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxP, hxN⟩, rfl⟩
      refine ⟨⟨x, hxP, by rw [hmap]⟩, ?_⟩
      rintro ⟨z, hzN, hzx⟩
      exact hxN (𝒦'.bijOn.injOn (hNK hzN) (hPK hxP) hzx ▸ hzN)
    · rintro ⟨⟨x, hxP, hxy⟩, hyN⟩
      have hxy' : 𝒦'.map x = y := by simpa only [hmap] using hxy
      exact ⟨x, ⟨hxP, fun hxN => hyN ⟨x, hxN, hxy'⟩⟩, hxy'⟩
  change 𝒦'.map '' closure (P \ N) = _
  rw [himage, hdiff, section34GraphResidualCell, iUnion_section34GraphVertexCell]

theorem exists_isPLCellOn_section34GraphResidualTriangle [FiniteDimensional ℝ Ea]
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) :
    ∃ B, IsPLCellOn 2 (section34GraphResidualCell 𝒦 𝒦' s.1) B := by
  classical
  let N := (derivedNeighborhood 𝒦'.complex
    (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦))).space
  have hball := isPLBall_closure_triangle_sdiff_graph_derivedNeighborhood_of_subdivision
    hsub hmap s
  have hcl : closure (convexHull ℝ (s.1 : Set Ea) \ N) ⊆ convexHull ℝ (s.1 : Set Ea) :=
    closure_minimal sdiff_subset (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  obtain ⟨B, hB⟩ := 𝒦'.exists_isPLCellOn_image
    (hcl.trans ((𝒦.complex.convexHull_subset_space s.2.1).trans hsub.space_eq.symm.subset))
    (by omega) hball
  rw [image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap s.2.1] at hB
  exact ⟨B, hB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
