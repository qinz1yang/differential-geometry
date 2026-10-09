/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryLocalEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPiecewiseAffineOn.mem_boundaryComplex_iff_of_isLocalHomeomorph
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    {f : E → F} (hf : IsPiecewiseAffineOn f K.space) (hmap : MapsTo f K.space L.space)
    (hloc : IsLocalHomeomorph (hmap.restrict f K.space L.space)) {x : E} (hx : x ∈ K.space) :
    f x ∈ (boundaryComplex (n + 1) L).space ↔ x ∈ (boundaryComplex (n + 1) K).space := by
  let q := hmap.restrict f K.space L.space
  have hinjloc : IsLocallyInjective (K.space.domRestrict f) :=
    hloc.isLocallyInjective.comp_left (Subtype.val_injective (p := (· ∈ L.space)))
  obtain ⟨U, hU, hinj⟩ := Covering.isLocallyInjective_domRestrict_iff.mp hinjloc x hx
  obtain ⟨D, hD, hDKU, hDnhds⟩ := hK.exists_isPLBall_subset_of_mem_nhdsWithin hx hU
  have hxD : x ∈ D := mem_of_mem_nhdsWithin hx hDnhds
  obtain ⟨J, hJfinite, hJspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite J.faces := hJfinite.to_subtype
  have hJball : IsPLBall (n + 1) J.space := hJspace.symm ▸ hD
  have hJ := hJball.isCombinatorialManifoldWithBoundary
  have hJK : J.space ⊆ K.space := hJspace.symm ▸ hDKU.trans inter_subset_left
  have hJU : J.space ⊆ U := hJspace.symm ▸ hDKU.trans inter_subset_right
  have hxJ : x ∈ J.space := hJspace.symm ▸ hxD
  have hJnhds : J.space ∈ 𝓝[K.space] x := hJspace.symm ▸ hDnhds
  obtain ⟨N, hNfinite, hNspace, hpl⟩ := exists_isPLHomeomorphOn_image J
    (hf.mono_of_isPolyhedron (isPolyhedron_space J) hJK) (hinj.mono hJU)
  let _ : Finite N.faces := hNfinite.to_subtype
  have hN := hJ.of_isPLHomeomorphOn hpl
  have hNL : N.space ⊆ L.space := by
    rw [hNspace]
    exact image_subset_iff.mpr (hmap.mono_left hJK)
  have hNnhds : N.space ∈ 𝓝[L.space] f x := by
    have hsub : (Subtype.val ⁻¹' J.space : Set K.space) ∈ 𝓝 (⟨x, hx⟩ : K.space) :=
      preimage_coe_mem_nhds_subtype.mpr hJnhds
    have himg := hloc.isOpenMap.image_mem_nhds hsub
    have heq : ((↑) : L.space → F) '' (q '' (Subtype.val ⁻¹' J.space)) = N.space := by
      rw [hNspace]
      apply Subset.antisymm
      · rintro y ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro y ⟨w, hw, rfl⟩
        exact ⟨q ⟨w, hJK hw⟩, ⟨⟨w, hJK hw⟩, hw, rfl⟩, rfl⟩
    have h := mem_nhds_subtype_iff_nhdsWithin.mp himg
    change ((↑) : L.space → F) '' (q '' (Subtype.val ⁻¹' J.space)) ∈ 𝓝[L.space] f x at h
    rwa [heq] at h
  have hsource := mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K J hK hJ
    hJK hxJ hJnhds
  have htarget := mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin L N hL hN
    hNL (hpl.bijOn.mapsTo hxJ) hNnhds
  have hlocal := mem_boundaryComplex_space_iff_of_isPLHomeomorphOn J N hJ hpl hxJ
  exact htarget.symm.trans (hlocal.trans hsource)

open Classical in
theorem IsPiecewiseAffineOn.mem_boundaryComplex_iff_of_isCoveringMap
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    {f : E → F} (hf : IsPiecewiseAffineOn f K.space) (hmap : MapsTo f K.space L.space)
    (hcov : IsCoveringMap (hmap.restrict f K.space L.space)) {x : E} (hx : x ∈ K.space) :
    f x ∈ (boundaryComplex (n + 1) L).space ↔ x ∈ (boundaryComplex (n + 1) K).space :=
  hf.mem_boundaryComplex_iff_of_isLocalHomeomorph K L hK hL hmap hcov.isLocalHomeomorph hx

open Classical in
theorem IsPiecewiseAffineOn.preimage_boundaryComplex_eq_of_isCoveringMap
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    {f : E → F} (hf : IsPiecewiseAffineOn f K.space) (hmap : MapsTo f K.space L.space)
    (hcov : IsCoveringMap (hmap.restrict f K.space L.space)) :
    K.space ∩ f ⁻¹' (boundaryComplex (n + 1) L).space =
      (boundaryComplex (n + 1) K).space := by
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact (hf.mem_boundaryComplex_iff_of_isCoveringMap K L hK hL hmap hcov hx).mp hfx
  · intro hx
    have hxK := boundaryComplex_space_subset (n + 1) K hx
    exact ⟨hxK, (hf.mem_boundaryComplex_iff_of_isCoveringMap K L hK hL hmap hcov hxK).mpr hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
