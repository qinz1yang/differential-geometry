/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.exists_connected_neighborhood
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {C U : Set E}
    (hC : IsCompact C) (hconn : IsConnected C) (hCK : C ⊆ K.space)
    (hU : U ∈ 𝓝ˢ[K.space] C) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) L ∧ IsConnected L.space ∧
      L.space ⊆ K.space ∧ L.space ⊆ U ∧ ∀ x ∈ C, L.space ∈ 𝓝[K.space] x := by
  obtain ⟨O, hO, hCO, hOU⟩ := mem_nhdsSetWithin.mp hU
  obtain ⟨R, N, hR, hRfin, hNR, hN, hNO, hNnhds⟩ :=
    hK.exists_isSubdivision_neighborhood hC hCK hO hCO
  let _ : Finite N.faces := (hRfin.subset hNR).to_subtype
  let _ : LocallyConnectedSpace N.space := locallyConnectedSpace_space N
  have hNK : N.space ⊆ K.space := hR.space_eq ▸ space_mono_of_faces_subset hNR
  have hCN : C ⊆ N.space := fun x hx => mem_of_mem_nhdsWithin (hCK hx) (hNnhds x hx)
  obtain ⟨p, hp⟩ := hconn.nonempty
  let L := restrict N (connectedComponentIn N.space p)
  have hLN : L.space = connectedComponentIn N.space p := restrict_connectedComponentIn_space N p
  have hCL : C ⊆ connectedComponentIn N.space p :=
    hconn.isPreconnected.subset_connectedComponentIn hp hCN
  have hLsub : L.space ⊆ N.space := hLN ▸ connectedComponentIn_subset N.space p
  have hopen : IsOpen (((↑) : N.space → E) ⁻¹' connectedComponentIn N.space p) := by
    rw [connectedComponentIn_eq_image (hCN hp), Set.preimage_image_eq _ Subtype.val_injective]
    exact isOpen_connectedComponent
  refine ⟨L, restrict_faces_finite N _, hN.restrict_connectedComponentIn p,
    hLN.symm ▸ (isConnected_connectedComponentIn_iff.mpr (hCN hp)), hLsub.trans hNK,
    fun x hx => hOU ⟨hNO (hLsub hx), hNK (hLsub hx)⟩, ?_⟩
  intro x hx
  have hrel : L.space ∈ 𝓝[N.space] x := by
    rw [hLN]
    exact preimage_coe_mem_nhds_subtype.mp (hopen.mem_nhds (show
      (⟨x, hCN hx⟩ : N.space) ∈ ((↑) : N.space → E) ⁻¹'
        connectedComponentIn N.space p from hCL hx))
  have hle : 𝓝[K.space] x ≤ 𝓝[N.space] x :=
    le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr (hNnhds x hx))
  exact hle hrel

end DifferentialGeometry.Topology.PiecewiseLinear
