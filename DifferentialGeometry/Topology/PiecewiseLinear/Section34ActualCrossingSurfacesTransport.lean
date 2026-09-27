import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualCrossingSurfacesNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.PLCompactModelEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLHomeomorphInto.exists_annular_surface_complex_in_model {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {S B J O : Set M} (hS : IsPLCellOn 3 S B)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJB : J ⊆ B)
    (hJP : J ⊆ interior (u '' P)) (hO : O ∈ 𝓝ˢ[B] J)
    (hOP : O ⊆ interior (u '' P)) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
    ∃ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (N : Set (EuclideanSpace ℝ (Fin 3))), ∃ hKfin : K.faces.Finite,
      let _ : Finite K.faces := hKfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 K ∧ IsOrientable 2 K ∧
      K.space ⊆ interior P ∧ u '' K.space ⊆ B ∩ O ∧
      IsPLSphere 1 (Function.invFunOn u P '' J) ∧
      Function.invFunOn u P '' J ⊆ K.space ∧
      Disjoint (Function.invFunOn u P '' J) (boundaryComplex 2 K).space ∧
      IsOpen N ∧ Function.invFunOn u P '' J ⊆ N ∧ N ⊆ interior P ∧
      N ∩ K.space = N ∩ u ⁻¹' B := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨Q, C, v, A, -, V, hAfin, hQ, hv, -, hvfront, -, hvC, hCA,
    hA, horA, hAS, -, -, hCbd, hAO, hV, hJV, hVtrace⟩ :=
    hS.exists_boundary_annular_neighborhood hJ hJB hO
  let _ : Finite A.faces := hAfin.to_subtype
  have hAP : A.space ⊆ Q := hAS.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hvA : IsPLHomeomorphInto 3 v A.space :=
    (hv.isPLOn.mono_of_isPolyhedron (isPolyhedron_space A) hAP).isPLHomeomorphInto_model
      (isPolyhedron_space A).isCompact (hv.injOn.mono hAP)
  have hAU : v '' A.space ⊆ u '' P := hAO.trans (hOP.trans interior_subset)
  let τ := Function.invFunOn u P
  let f := τ ∘ v
  have hf := hvA.isPLHomeomorphOn_invFunOn_comp (isPolyhedron_space A) hu hAU
  have hfpoly : IsPolyhedron (f '' A.space) :=
    (isPolyhedron_space A).image_of_isPiecewiseAffineOn hf.isPiecewiseAffineOn hf.bijOn.injOn
  obtain ⟨K, hKfin, hKspace⟩ := hfpoly.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hfK : IsPLHomeomorphOn f A.space K.space := hKspace.symm ▸ hf
  have hK := hA.of_isPLHomeomorphOn hfK
  have horK : IsOrientable 2 K := (isOrientable_iff_of_isPLHomeomorphOn hA hfK).mp horA
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτint : MapsTo τ (interior (u '' P)) (interior P) := by
    intro x hx
    rw [← hu.image_interior] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hleft (interior_subset hy)]
    exact hy
  have hKint : K.space ⊆ interior P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hKspace.subset hx
    exact hτint (hOP (hAO ⟨y, hy, rfl⟩))
  have hback : u '' K.space = v '' A.space := by
    rw [hKspace, image_image]
    exact image_congr fun x hx => hright (hAU ⟨x, hx, rfl⟩)
  have hJimage : f '' C = τ '' J := by rw [image_comp, hvC]
  have hJK : τ '' J ⊆ K.space := hJimage ▸
    (image_mono hCA).trans hfK.image_eq.subset
  have hJKbd : Disjoint (τ '' J) (boundaryComplex 2 K).space := by
    rw [← hJimage, boundaryComplex_space_of_isPLHomeomorphOn A K hA hfK]
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyA := boundaryComplex_space_subset 2 A hy
    have heq := hfK.bijOn.injOn hyA (hCA hx) hyx
    exact disjoint_left.mp hCbd hx (heq ▸ hy)
  let N := interior P ∩ u ⁻¹' V
  have hN : IsOpen N := (hu.continuousOn.mono interior_subset).isOpen_inter_preimage
    isOpen_interior hV
  have hJN : τ '' J ⊆ N := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hτint (hJP hx), ?_⟩
    change u (τ x) ∈ V
    rw [hright (interior_subset (hJP hx))]
    exact hJV hx
  refine ⟨K, N, hKfin, hK, horK, hKint, ?_,
    hu.isPLSphere_invFunOn_image hJ (hJP.trans interior_subset), hJK, hJKbd,
    hN, hJN, inter_subset_left, ?_⟩
  · rw [hback]
    exact subset_inter (hvfront ▸ image_mono hAS) hAO
  · apply Subset.antisymm
    · rintro x ⟨hxN, hxK⟩
      refine ⟨hxN, ?_⟩
      have hxv : u x ∈ v '' A.space := hback ▸ mem_image_of_mem u hxK
      obtain ⟨y, hy, hyx⟩ := hxv
      change u x ∈ B
      rw [← hyx]
      exact hvfront ▸ mem_image_of_mem v (hAS hy)
    · rintro x ⟨hxN, hxB⟩
      have hxW : u x ∈ v '' A.space := (hVtrace.subset ⟨hxN.2, hxB⟩).2
      obtain ⟨y, hy, hyx⟩ := hback.symm.subset hxW
      have heq := hu.injOn (interior_subset (hKint hy)) (interior_subset hxN.1) hyx
      exact ⟨hxN, heq ▸ hy⟩

open Classical in
theorem IsPLHomeomorphInto.exists_spherical_surface_complex_in_model {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {S B : Set M} (hS : IsPLCellOn 3 S B)
    (hSP : S ⊆ u '' P) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      ∃ hKfin : K.faces.Finite, let _ : Finite K.faces := hKfin.to_subtype
      IsPLSphere 2 K.space ∧ IsCombinatorialManifold 2 K ∧ IsOrientable 2 K ∧
      K.space = Function.invFunOn u P '' B ∧ K.space ⊆ P ∧ u '' K.space = B ∧
      (boundaryComplex 2 K).space = ∅ := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨q, hq, hqb⟩ := hS.exists_isPLHomeomorphOn_invFunOn hu hSP
  have hSphere : IsPLSphere 2 (Function.invFunOn u P '' B) :=
    hqb.symm ▸ hq.isPLSphere_image_stdSimplexBoundary
  obtain ⟨K, hKfin, hKspace⟩ := hSphere.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hKSphere : IsPLSphere 2 K.space := hKspace.symm ▸ hSphere
  have hK := hKSphere.isCombinatorialManifold
  have hBP := hS.boundary_subset.trans hSP
  refine ⟨K, hKfin, hKSphere, hK, isOrientable_of_isPLSphere hKSphere, hKspace, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hKspace.subset hx
    exact hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hBP hy)
  · rw [hKspace, image_image]
    exact (image_congr fun x hx =>
      hu.injOn.bijOn_image.invOn_invFunOn.2 (hBP hx)).trans (image_id' B)
  · rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp

end DifferentialGeometry.Topology.PiecewiseLinear
