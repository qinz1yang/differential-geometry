/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceBicollarSubspace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceRegionInSolidTorus

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialManifold.isConnected_exterior_in_open
    (L R : Geometry.SimplicialComplex ℝ E3) [Finite L.faces] [Finite R.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    {U : Set E3} (hU : IsOpen U) (hUc : IsConnected U) (hRU : R.space ⊆ U)
    (hfront : frontier R.space = L.space) (hint : (interior R.space).Nonempty)
    (hout : (U \ R.space).Nonempty) :
    IsConnected ((((↑) : U → E3) ⁻¹' R.space)ᶜ) := by
  let _ : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUc
  let _ : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  let A : Set U := ((↑) : U → E3) ⁻¹' R.space
  have hAc : IsClosed A := (isPolyhedron_space R).isClosed.preimage continuous_subtype_val
  have hLU : L.space ⊆ U := hfront.symm.subset.trans
    ((isPolyhedron_space R).isClosed.frontier_subset.trans hRU)
  have hfr : frontier A = ((↑) : U → E3) ⁻¹' L.space := by
    dsimp only [A]
    rw [← hU.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val, hfront]
  let e : (((↑) : U → E3) ⁻¹' L.space) ≃ₜ L.space :=
    (Topology.IsEmbedding.subtypeVal : IsEmbedding ((↑) : U → E3)).homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe] using hLU)
  let _ : CompactSpace L.space := isCompact_iff_compactSpace.mp (isPolyhedron_space L).isCompact
  let _ : CompactSpace (((↑) : U → E3) ⁻¹' L.space) := e.symm.compactSpace
  have hcompact : IsCompact (((↑) : U → E3) ⁻¹' L.space) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hconnected : IsConnected (((↑) : U → E3) ⁻¹' L.space) :=
    isConnected_iff_connectedSpace.mpr
      (e.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp hconn))
  have hAi : (interior A).Nonempty := by
    obtain ⟨x, hx⟩ := hint
    have hsub : ((↑) : U → E3) ⁻¹' interior R.space ⊆ interior A :=
      interior_maximal (preimage_mono interior_subset)
        (isOpen_interior.preimage continuous_subtype_val)
    exact ⟨⟨x, hRU (interior_subset hx)⟩, hsub hx⟩
  have hAe : Aᶜ.Nonempty := by
    obtain ⟨x, hxU, hxR⟩ := hout
    exact ⟨⟨x, hxU⟩, hxR⟩
  exact Topology.isConnected_compl_of_isBicollared_frontier hAc
    (hfr.symm ▸ hcompact) (hfr.symm ▸ hconnected) hAi hAe
    (hfr.symm ▸ hL.isBicollared_preimage_open L hconn hU hLU)

theorem IsCombinatorialManifold.not_separates_in_open_of_subset_solidTorus
    (L : Geometry.SimplicialComplex ℝ E3) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    {U S : Set E3} (hU : IsOpen U) (hUc : IsConnected U)
    (hS : IsTopologicalSolidTorus S) (hSU : S ⊆ U) (hLS : L.space ⊆ interior S)
    {a b : E3} (haU : a ∈ U) (hbU : b ∈ U) (haS : a ∉ S) (hbS : b ∉ S) :
    ¬ Separates (((↑) : U → E3) ⁻¹' L.space) (((↑) : U → E3) ⁻¹' {a})
      (((↑) : U → E3) ⁻¹' {b}) := by
  classical
  obtain ⟨R, hRfin, -, -, hfront, -, hRi, -, hRS⟩ :=
    hL.exists_filling_interior_solidTorus L hconn hS hLS
  let _ : Finite R.faces := hRfin.to_subtype
  have hRU : R.space ⊆ U := hRS.trans (interior_subset.trans hSU)
  have haR : a ∉ R.space := fun hx => haS (interior_subset (hRS hx))
  have hbR : b ∉ R.space := fun hx => hbS (interior_subset (hRS hx))
  have hext := hL.isConnected_exterior_in_open L R hconn hU hUc hRU hfront hRi.nonempty
    ⟨a, haU, haR⟩
  have hLR : L.space ⊆ R.space := hfront.symm.subset.trans
    (isPolyhedron_space R).isClosed.frontier_subset
  let a' : U := ⟨a, haU⟩
  let b' : U := ⟨b, hbU⟩
  have ha' : a' ∈ (((↑) : U → E3) ⁻¹' R.space)ᶜ := haR
  have hb' : b' ∈ (((↑) : U → E3) ⁻¹' R.space)ᶜ := hbR
  have hsame : b' ∈ connectedComponentIn ((((↑) : U → E3) ⁻¹' L.space)ᶜ) a' :=
    hext.isPreconnected.subset_connectedComponentIn ha'
      (compl_subset_compl.mpr (preimage_mono hLR)) hb'
  intro hsep
  exact hsep.not_mem_connectedComponentIn (show a' ∈ ((↑) : U → E3) ⁻¹' {a} from rfl)
    (show b' ∈ ((↑) : U → E3) ⁻¹' {b} from rfl) hsame

end DifferentialGeometry.Topology.PiecewiseLinear
