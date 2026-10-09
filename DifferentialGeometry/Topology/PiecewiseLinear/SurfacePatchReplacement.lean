/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.BicollaredReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceBicollarSubspace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceRegionInSolidTorus

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialManifold.separates_of_connected_surface_patch
    (L : Geometry.SimplicialComplex ℝ E3) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    {U S M R : Set E3} (hU : IsOpen U) (hS : IsTopologicalSolidTorus S)
    (hSU : S ⊆ U) (hLS : L.space ⊆ interior S)
    (hR : IsClosed (((↑) : U → E3) ⁻¹' R)) (hout : M \ L.space = R \ L.space)
    (hpatch : IsPreconnected (L.space \ R)) {a b : E3}
    (haS : a ∉ S) (hbS : b ∉ S)
    (hsep : Separates (((↑) : U → E3) ⁻¹' M) (((↑) : U → E3) ⁻¹' {a})
      (((↑) : U → E3) ⁻¹' {b})) :
    Separates (((↑) : U → E3) ⁻¹' R) (((↑) : U → E3) ⁻¹' {a})
      (((↑) : U → E3) ⁻¹' {b}) := by
  classical
  let _ : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  obtain ⟨N, hNfin, -, -, hfront, hreg, -, -, hNS⟩ :=
    hL.exists_filling_interior_solidTorus L hconn hS hLS
  let _ : Finite N.faces := hNfin.to_subtype
  let A : Set U := ((↑) : U → E3) ⁻¹' N.space
  have hNclosed := (isPolyhedron_space N).isClosed
  have hAc : IsClosed A := hNclosed.preimage continuous_subtype_val
  have hLN : L.space ⊆ N.space := hfront.symm.subset.trans hNclosed.frontier_subset
  have hLU : L.space ⊆ U := hLS.trans (interior_subset.trans hSU)
  have hfr : frontier A = ((↑) : U → E3) ⁻¹' L.space := by
    dsimp only [A]
    rw [← hU.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val, hfront]
  have hAreg : A ⊆ closure (interior A) := by
    dsimp only [A]
    rw [← hU.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      continuous_subtype_val,
      ← hU.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val]
    exact preimage_mono hreg.symm.subset
  have hbi : IsBicollared (frontier A) :=
    hfr.symm ▸ hL.isBicollared_preimage_open L hconn hU hLU
  have hpatch' : IsPreconnected (frontier A \ (((↑) : U → E3) ⁻¹' R)) := by
    rw [hfr, ← preimage_sdiff]
    apply hpatch.preimage_of_isOpenMap Subtype.val_injective hU.isOpenMap_subtype_val
    simpa only [Subtype.range_coe] using sdiff_subset.trans hLU
  have hout' : (((↑) : U → E3) ⁻¹' M) \ A = (((↑) : U → E3) ⁻¹' R) \ A := by
    ext x
    constructor
    · intro hx
      exact ⟨(hout.subset ⟨hx.1, fun hxl => hx.2 (hLN hxl)⟩).1, hx.2⟩
    · intro hx
      exact ⟨(hout.symm.subset ⟨hx.1, fun hxl => hx.2 (hLN hxl)⟩).1, hx.2⟩
  apply hsep.of_bicollared_frontier_replacement hR hAc hAreg hbi hpatch' hout'
  · intro x hx hxA
    change (x : E3) = a at hx
    exact haS (hx ▸ interior_subset (hNS hxA))
  · intro x hx hxA
    change (x : E3) = b at hx
    exact hbS (hx ▸ interior_subset (hNS hxA))

end DifferentialGeometry.Topology.PiecewiseLinear
