/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_bicollar_of_isPLSphere_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hor : IsOrientable 2 K)
    {J U : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hBd : Disjoint J (boundaryComplex 2 K).space) (hU : U ∈ 𝓝ˢ[K.space] J) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧
      W ⊆ K.space \ (boundaryComplex 2 K).space ∧ W ⊆ U ∧ W ∈ 𝓝ˢ[K.space] J ∧
      IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W ∧ ∀ x ∈ J, ρ (x, 0) = x := by
  classical
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  obtain ⟨O, hO, hJO, hOU⟩ := mem_nhdsSetWithin.mp hU
  have hJO' : J ⊆ O \ (boundaryComplex 2 K).space := fun x hx =>
    ⟨hJO hx, fun hxB => disjoint_left.mp hBd hx hxB⟩
  obtain ⟨N, _, _, hNK, hNO, hNnhds, H, hH⟩ := exists_annular_neighborhood K hK hor hJ hJK
    (hO.sdiff (isPolyhedron_space (boundaryComplex 2 K)).isClosed) hJO'
  have hJN : J ⊆ N.space := fun x hx => mem_of_mem_nhdsWithin (hJK hx) (hNnhds x hx)
  have hNint : N.space ⊆ K.space \ (boundaryComplex 2 K).space := fun x hx =>
    ⟨hNK hx, (hNO hx).2⟩
  have hNU : N.space ⊆ U := fun x hx => hOU ⟨(hNO hx).1, hNK hx⟩
  let D : Set (Fin 3 → ℝ) := Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
  let C : Set (Fin 3 → ℝ) := stdSimplexBoundary 2
  let A := C ×ˢ Icc (0 : ℝ) 1
  let B := D ×ˢ {(0 : ℝ), 1} ∪ A
  let f := Function.invFunOn H A
  have hf : IsPLHomeomorphOn f N.space A := hH.symm
  have hfJ := hf.restrict hJ.isPolyhedron hJN
  have hJ' : IsPLSphere 1 (f '' J) := hJ.of_isPLHomeomorphOn hfJ
  have hD : IsPLBall 2 D := isPLBall_stdSimplex 2
  have hB : IsPLSphere 2 B := by
    simpa only [image_id] using hD.isPolyhedron.isPLHomeomorphOn_id.isPLSphere_prism_boundary
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M, hMfin, hMspace⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite M.faces := hMfin.to_subtype
  have hM : IsPLSphere 2 M.space := hMspace.symm ▸ hB
  have hAM : A ⊆ M.space := subset_union_right.trans hMspace.symm.subset
  have hJ'M : f '' J ⊆ M.space :=
    ((image_mono hJN).trans hf.image_eq.subset).trans hAM
  have hApoint : ∀ y ∈ f '' J, A ∈ 𝓝[M.space] y := by
    rintro y ⟨x, hx, rfl⟩
    exact hf.image_mem_nhdsWithin_of_notMem_boundaryComplex K M hK
      hM.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hAM (hJK hx)
      (fun hxB => disjoint_left.mp hBd hx hxB) (hNnhds x hx)
  have hAnhds : A ∈ 𝓝ˢ[M.space] (f '' J) := by
    have hpre : ((↑) : M.space → (Fin 3 → ℝ) × ℝ) ⁻¹' A ∈
        𝓝ˢ (((↑) : M.space → (Fin 3 → ℝ) × ℝ) ⁻¹' (f '' J)) :=
      mem_nhdsSet_iff_forall.mpr fun x hx =>
        preimage_coe_mem_nhds_subtype.mpr (hApoint x hx)
    have h := mem_nhdsSet_subtype_iff_nhdsSetWithin.mp hpre
    rwa [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      inter_eq_right.mpr hAM, inter_eq_right.mpr hJ'M] at h
  obtain ⟨V, σ, hV, _, hVA, hVnhds, hσ, hσ0⟩ :=
    hM.exists_bicollar_of_isPLSphere_one hJ' hJ'M hAnhds
  have hHV := hH.restrict hV hVA
  let W := H '' V
  let ρ := H ∘ σ ∘ Prod.map f (id : ℝ → ℝ)
  have hWint : W ⊆ K.space \ (boundaryComplex 2 K).space := by
    rintro y ⟨x, hx, rfl⟩
    exact hNint (hH.bijOn.mapsTo (hVA hx))
  have hWU : W ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    exact hNU (hH.bijOn.mapsTo (hVA hx))
  have hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W :=
    ((hfJ.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hσ).trans hHV
  have hWpoint : ∀ x ∈ J, W ∈ 𝓝[K.space] x := by
    intro x hx
    obtain ⟨O', hO', hJ'O', hO'V⟩ := mem_nhdsSetWithin.mp hVnhds
    have hVpoint : V ∈ 𝓝[M.space] f x :=
      mem_nhdsWithin.mpr ⟨O', hO', hJ'O' (mem_image_of_mem f hx), hO'V⟩
    have h := hHV.image_mem_nhdsWithin_of_isCombinatorialManifold M K
      hM.isCombinatorialManifold hK (hWint.trans sdiff_subset)
      (hJ'M (mem_image_of_mem f hx)) hVpoint
    rwa [hH.bijOn.invOn_invFunOn.2 (hJN hx)] at h
  have hWnhds : W ∈ 𝓝ˢ[K.space] J := by
    have hpre : ((↑) : K.space → E) ⁻¹' W ∈ 𝓝ˢ (((↑) : K.space → E) ⁻¹' J) :=
      mem_nhdsSet_iff_forall.mpr fun x hx => preimage_coe_mem_nhds_subtype.mpr (hWpoint x hx)
    have h := mem_nhdsSet_subtype_iff_nhdsSetWithin.mp hpre
    rwa [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      inter_eq_right.mpr (hWint.trans sdiff_subset), inter_eq_right.mpr hJK] at h
  refine ⟨W, ρ, hV.image_of_isPiecewiseAffineOn hHV.isPiecewiseAffineOn hHV.bijOn.injOn,
    hWint, hWU, hWnhds, hρ, ?_⟩
  intro x hx
  change H (σ (f x, 0)) = x
  rw [hσ0 _ (mem_image_of_mem f hx)]
  exact hH.bijOn.invOn_invFunOn.2 (hJN hx)

theorem IsCombinatorialManifold.exists_bicollar_of_isPLSphere_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {J U : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] J) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧ W ⊆ K.space ∧ W ⊆ U ∧
      W ∈ 𝓝ˢ[K.space] J ∧ IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ J, ρ (x, 0) = x := by
  classical
  have hBd : Disjoint J (boundaryComplex 2 K).space := by
    apply disjoint_left.mpr
    intro x _ hxB
    obtain ⟨s, hs, _⟩ := (boundaryComplex 2 K).mem_space_iff.mp hxB
    rw [hK.boundaryComplex_faces_eq_empty K] at hs
    exact hs.elim
  obtain ⟨W, ρ, hW, hWK, hWU, hWnhds, hρ, hρ0⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_bicollar_of_isPLSphere_one K hor hJ hJK hBd hU
  exact ⟨W, ρ, hW, hWK.trans sdiff_subset, hWU, hWnhds, hρ, hρ0⟩

end DifferentialGeometry.Topology.PiecewiseLinear
