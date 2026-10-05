import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem vertex_inter_residual_mem_closure_boundary_sdiff
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.faces ⊆ K.faces)
    {x : E} (hxA : {x} ∈ A.faces)
    (hxR : {x} ∈ (subcomplexGeneratedBy K A.facesᶜ).faces) :
    x ∈ closure ((boundaryComplex 3 A).space \ (boundaryComplex 3 K).space) := by
  classical
  let B := boundaryComplex 3 A
  let D := boundaryComplex 3 K
  let I := restrict B D.space
  let LA := SimplicialComplex.geometricLink A {x}
  let LK := SimplicialComplex.geometricLink K {x}
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 A).to_subtype
  let _ : Finite D.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite LA.faces :=
    ((Set.toFinite A.faces).subset (geometricLink_faces_subset A {x})).to_subtype
  let _ : Finite LK.faces :=
    ((Set.toFinite K.faces).subset (geometricLink_faces_subset K {x})).to_subtype
  have hBA : B.faces ⊆ A.faces := boundaryComplex_faces_subset 3 A
  have hBK : B.faces ⊆ K.faces := hBA.trans hAK
  have hDK : D.faces ⊆ K.faces := boundaryComplex_faces_subset 3 K
  have hLAK : LA.space ⊆ LK.space := space_mono_of_faces_subset
    (fun _ ht => ⟨ht.1, ht.2.1, hAK ht.2.2⟩)
  have hnot := not_geometricLink_space_subset_of_mem_subcomplexGeneratedBy_compl K A hAK
    hxA hxR
  have hxspace : x ∈ A.space := A.subset_space hxA (Finset.mem_singleton_self x)
  have hxres : x ∈ closure (K.space \ A.space) := by
    rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy K K A Subset.rfl hAK]
    exact (subcomplexGeneratedBy K A.facesᶜ).subset_space hxR (Finset.mem_singleton_self x)
  have hxB : x ∈ B.space := inter_closure_sdiff_space_subset_boundaryComplex K A hK hA hAK
    ⟨hxspace, hxres⟩
  by_contra hxcl
  have hDnear : D.space ∈ 𝓝[B.space] x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hxcl)]
      with y hyB hycl
    by_contra hyD
    exact hycl (subset_closure ⟨hyB, hyD⟩)
  have hxD : x ∈ D.space := mem_of_mem_nhdsWithin hxB hDnear
  have hIspace : I.space = B.space ∩ D.space :=
    restrict_space_eq_inter_of_faces_subset K B D hBK hDK
  have hInear : I.space ∈ 𝓝[B.space] x := by
    rw [hIspace]
    exact Filter.inter_mem self_mem_nhdsWithin hDnear
  have hlink := geometricLink_eq_of_space_mem_nhdsWithin (restrict_faces_subset B D.space)
    hInear
  have hID : I.faces ⊆ D.faces := fun _ hs =>
    ((mem_restrict_faces_iff_of_faces_subset K B D hBK hDK).mp hs).2
  have hbound : (boundaryComplex 2 LA).space ⊆ (boundaryComplex 2 LK).space := by
    rw [← geometricLink_boundaryComplex, ← geometricLink_boundaryComplex, ← hlink]
    exact space_mono_of_faces_subset fun _ hs => ⟨hs.1, hs.2.1, hID hs.2.2⟩
  have hAball : IsPLBall 2 LA.space :=
    (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision A A hA
      (IsSubdivision.refl _) hxA).mpr hxB
  have hKball : IsPLBall 2 LK.space :=
    (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision K K hK
      (IsSubdivision.refl _) (hAK hxA)).mpr hxD
  have hbdEq := eq_of_subset_of_isPLSphere
    (isPLSphere_boundaryComplex_space_of_isPLBall LA hAball)
    (isPLSphere_boundaryComplex_space_of_isPLBall LK hKball) hbound
  have heq := eq_of_isPLBall_of_boundaryComplex_subset LK hKball hAball hLAK
    (hbdEq.symm.subset.trans (boundaryComplex_space_subset 2 LA))
  exact hnot heq.symm.subset

open Classical in
theorem inter_closure_sdiff_eq_closure_boundary_sdiff_three
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.space ⊆ K.space) :
    A.space ∩ closure (K.space \ A.space) =
      closure ((boundaryComplex 3 A).space \ (boundaryComplex 3 K).space) := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hxA, hxR⟩
    obtain ⟨R, hR, hRfin, hxRvertex⟩ := exists_isSubdivision_singleton_mem K (hAK hxA)
    let _ : Finite R.faces := hRfin.to_subtype
    obtain ⟨T, hT, hTfin, hTA⟩ := exists_isSubdivision_restrict_isSubdivision R A
      (hR.space_eq.symm ▸ hAK)
    let _ : Finite T.faces := hTfin.to_subtype
    let B := restrict T A.space
    let C := subcomplexGeneratedBy T B.facesᶜ
    let _ : Finite B.faces := (restrict_faces_finite T A.space).to_subtype
    have hBT := restrict_faces_subset T A.space
    have hxT : {x} ∈ T.faces := hT.singleton_mem hxRvertex
    have hxB : {x} ∈ B.faces := ⟨hxT, by simpa using hxA⟩
    have hCspace : C.space = closure (K.space \ A.space) := by
      rw [show C = subcomplexGeneratedBy T B.facesᶜ from rfl,
        ← closure_space_sdiff_space_eq_subcomplexGeneratedBy T T B Subset.rfl hBT,
        hTA.space_eq, hT.space_eq, hR.space_eq]
    have hxC : {x} ∈ C.faces := mem_faces_of_mem_openSimplex_of_mem_space
      (subcomplexGeneratedBy_faces_subset T B.facesᶜ) hxT (mem_openSimplex_singleton x)
      (hCspace.symm ▸ hxR)
    have hx := vertex_inter_residual_mem_closure_boundary_sdiff T B
      (hK.of_isSubdivision (hT.trans hR)) (hA.of_isSubdivision hTA) hBT hxB hxC
    rwa [boundaryComplex_space_of_isSubdivision K T hK (hT.trans hR),
      boundaryComplex_space_of_isSubdivision A B hA hTA] at hx
  · let _ : Finite (boundaryComplex 3 A).faces :=
      (boundaryComplex_faces_finite 3 A).to_subtype
    apply closure_minimal _ ((isPolyhedron_space A).isClosed.inter isClosed_closure)
    rintro x ⟨hxB, hxKbd⟩
    refine ⟨boundaryComplex_space_subset 3 A hxB, ?_⟩
    by_contra hxcl
    have hnear : A.space ∈ 𝓝[K.space] x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hxcl)]
        with y hyK hycl
      by_contra hyA
      exact hycl (subset_closure ⟨hyK, hyA⟩)
    exact hxKbd ((mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K A hK hA hAK
      (boundaryComplex_space_subset 3 A hxB) hnear).mp hxB)

end DifferentialGeometry.Topology.PiecewiseLinear
