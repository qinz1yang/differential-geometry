/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.EmbeddedProjection
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPiecewiseAffineOn.preimage_boundaryComplex_subset_of_isLocallyInjective
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    {f : E → F} (hf : IsPiecewiseAffineOn f K.space) (hmap : MapsTo f K.space L.space)
    (hloc : IsLocallyInjective (K.space.domRestrict f)) :
    K.space ∩ f ⁻¹' (boundaryComplex (n + 1) L).space ⊆ (boundaryComplex (n + 1) K).space := by
  rintro x ⟨hx, hfx⟩
  obtain ⟨U, hU, hinj⟩ := Covering.isLocallyInjective_domRestrict_iff.mp hloc x hx
  obtain ⟨D, hD, hDKU, hDnhds⟩ := hK.exists_isPLBall_subset_of_mem_nhdsWithin hx hU
  have hxD : x ∈ D := mem_of_mem_nhdsWithin hx hDnhds
  obtain ⟨J, hJfinite, hJspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite J.faces := hJfinite.to_subtype
  have hJball : IsPLBall (n + 1) J.space := hJspace.symm ▸ hD
  have hJ := hJball.isCombinatorialManifoldWithBoundary
  have hJK : J.space ⊆ K.space := hJspace.symm ▸ hDKU.trans inter_subset_left
  have hJU : J.space ⊆ U := hJspace.symm ▸ hDKU.trans inter_subset_right
  have hxJ : x ∈ J.space := hJspace.symm ▸ hxD
  obtain ⟨N, hNfinite, hNspace, hNpl⟩ := exists_isPLHomeomorphOn_image J
    (hf.mono_of_isPolyhedron (isPolyhedron_space J) hJK) (hinj.mono hJU)
  let _ : Finite N.faces := hNfinite.to_subtype
  have hN := hJ.of_isPLHomeomorphOn hNpl
  have hNL : N.space ⊆ L.space := by
    rw [hNspace]
    exact image_subset_iff.mpr (hmap.mono_left hJK)
  have hfxN : f x ∈ (boundaryComplex (n + 1) N).space :=
    inter_boundaryComplex_space_subset_of_subset L N hL hN hNL ⟨hNpl.bijOn.mapsTo hxJ, hfx⟩
  have hxJboundary := (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn J N hJ hNpl hxJ).mp hfxN
  exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K J hK hJ hJK hxJ
    (hJspace.symm ▸ hDnhds)).mp hxJboundary

end DifferentialGeometry.Topology.PiecewiseLinear
