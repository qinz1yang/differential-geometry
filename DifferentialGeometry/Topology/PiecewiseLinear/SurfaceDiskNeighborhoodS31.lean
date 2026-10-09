/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitEndpointDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_isPLBall_surface_disk_neighborhood
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {D U : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ N : Set E, IsPLBall 2 N ∧ N ⊆ K.space ∩ U ∧ N ∈ 𝓝ˢ[K.space] D := by
  classical
  obtain ⟨O, hO, hDO, hOU⟩ := mem_nhdsSetWithin.mp hU
  obtain ⟨K', M, hK', hK'fin, hMK', hM, hMO, hMnhds⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood
      hD.isPolyhedron.isCompact hDK hO hDO
  let _ : Finite M.faces := (hK'fin.subset hMK').to_subtype
  have hDM : D ⊆ M.space := fun x hx => mem_of_mem_nhdsWithin (hDK hx) (hMnhds x hx)
  have hMK : M.space ⊆ K.space := hK'.space_eq ▸ space_mono_of_faces_subset hMK'
  obtain ⟨R, A, L, φ, ψ, hR, hRfin, hAR, hAfin, hAD, hLfin, hL, hIso, -⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar M hD hDM
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let N := (PiecewiseLinear.derivedNeighborhood R A).space
  have hN : IsPLBall 2 N :=
    (hM.of_isSubdivision hR).isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface
      hAR hL hIso
  have hNM : N ⊆ M.space := (derivedNeighborhood_space_subset R A).trans hR.space_eq.subset
  refine ⟨N, hN, fun x hx => ⟨hMK (hNM hx), hOU ⟨hMO (hNM hx), hMK (hNM hx)⟩⟩, ?_⟩
  have hlocal : ∀ x ∈ D, N ∈ 𝓝[K.space] x := by
    intro x hx
    have hNR : N ∈ 𝓝[R.space] x := derivedNeighborhood_mem_nhdsWithin hAR (hAD.symm ▸ hx)
    rw [hR.space_eq] at hNR
    exact nhdsWithin_le_of_mem (hMnhds x hx) hNR
  have hpre : (Subtype.val : K.space → E) ⁻¹' N ∈
      𝓝ˢ ((Subtype.val : K.space → E) ⁻¹' D) :=
    mem_nhdsSet_iff_forall.mpr fun x hx => preimage_coe_mem_nhds_subtype.mpr (hlocal x hx)
  have h := mem_nhdsSet_subtype_iff_nhdsSetWithin.mp hpre
  simpa only [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hDK,
    inter_eq_left.mpr (hNM.trans hMK)] using h

end DifferentialGeometry.Topology.PiecewiseLinear
