/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceInteriorFrontierOpen

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_connected_neighborhood_pair_sdiff {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) {x : E3} (hx : x ∈ Eint) (hxP : x ≠ P) {U : Set E3}
    (hU : U ∈ 𝓝 x) :
    ∃ C ∈ 𝓝 x, C ⊆ U ∧ ∃ A B : Set E3, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ Ec ∧
      C ∩ Ec ⊆ closure A ∧ C ∩ Ec ⊆ closure B := by
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨L, hLfin, hL, hag⟩ := exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff
    (ι := Unit) {()} (M := fun _ => Eint) (Cc := fun _ => {x}) (P := fun _ => P)
    (fun _ _ => hpc.isOpenCell) (fun _ _ => hpc.regular)
    (fun i _ j _ hij => (hij (Subsingleton.elim i j)).elim)
    (fun _ _ => isCompact_singleton)
    (fun _ _ => singleton_subset_iff.mpr ⟨hx, hxP⟩)
  have : Finite L.faces := hLfin.to_subtype
  have hagx : ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ y ∈ Eint :=
    hag () (Finset.mem_singleton_self _) x (mem_singleton x)
  have hxL : x ∈ L.space := hagx.self_of_nhds.mpr hx
  have hxB : x ∉ (boundaryComplex 2 L).space := by
    intro hxB
    obtain ⟨R, hRL, hRfin, hxR⟩ := exists_isSubdivision_singleton_mem L hxL
    have : Finite R.faces := hRfin.to_subtype
    obtain ⟨ψ⟩ := hpc.isOpenCell
    have hsph := isPLSphere_one_geometricLink_of_homeomorph R Metric.isOpen_ball ψ hxR
      (by rw [hRL.space_eq]; exact hagx)
    have hball := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision (n := 1)
      L R hL hRL hxR).mpr hxB
    exact hball.not_isPLSphere hsph
  obtain ⟨W, hWp, hW, hxW⟩ := eventually_nhds_iff.mp hagx
  have hbdc : IsClosed Ebd := by
    obtain ⟨φ⟩ := hpc.isSphere
    exact (isCompact_iff_compactSpace.mpr φ.symm.compactSpace).isClosed
  have hxbd : x ∉ Ebd := fun h => Set.disjoint_left.mp hpc.disjointRim hx h
  have hU' : U ∩ W ∩ Ebdᶜ ∈ 𝓝 x :=
    Filter.inter_mem (Filter.inter_mem hU (hW.mem_nhds hxW)) (hbdc.isOpen_compl.mem_nhds hxbd)
  obtain ⟨C, hC, hCU, A, B, hA, hB, hAB, hcA, hcB⟩ :=
    exists_connected_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary L hL
      (by simp) ⟨hxL, hxB⟩ hU'
  have hCL : ∀ y ∈ C, (y ∈ L.space ↔ y ∈ Ec) := by
    intro y hy
    rw [hWp y (hCU hy).1.2, hpc.carrierEq]
    exact ⟨Or.inl, fun h => h.resolve_right (hCU hy).2⟩
  refine ⟨C, hC, fun y hy => (hCU hy).1.1, A, B, hA, hB, ?_, ?_, ?_⟩
  · rw [hAB]
    ext y
    exact ⟨fun h => ⟨h.1, fun hy => h.2 ((hCL y h.1).mpr hy)⟩,
      fun h => ⟨h.1, fun hy => h.2 ((hCL y h.1).mp hy)⟩⟩
  · exact fun y hy => hcA ⟨hy.1, (hCL y hy.1).mpr hy.2⟩
  · exact fun y hy => hcB ⟨hy.1, (hCL y hy.1).mpr hy.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
