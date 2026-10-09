/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.SeparatingComponent
import DifferentialGeometry.Topology.Connected.SeparatorLocation
import DifferentialGeometry.Topology.Homology.BettiNumber
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import Mathlib.Data.Nat.Find

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_neighborhood {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {C U : Set E}
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) N ∧
      C ⊆ interior N.space ∧ N.space ⊆ U := by
  obtain ⟨T, hT, hTcard, hCT⟩ :=
    exists_affineIndependent_openSimplex_superset (n + 1) hdim hC.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall (n + 1) K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hCK : C ⊆ interior K.space := hCT.trans hint.symm.subset
  obtain ⟨R, N, -, hRfin, hNR, hN, hNU, hnhds⟩ :=
    hKball.isCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood
      hC (hCK.trans interior_subset) hU hCU
  refine ⟨N, hRfin.subset hNR, hN, ?_, hNU⟩
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  have h := hnhds x hx
  rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hCK hx))] at h

open Classical in
theorem exists_connected_separating_surface
    (hdim : Module.finrank ℝ E = 3) {A B U : Set E}
    (hA : IsCompact A) (hAc : IsConnected A) (hB : IsClosed B) (hBc : IsConnected B)
    (hAB : Disjoint A B) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (hLfin : L.faces.Finite),
      letI := hLfin.to_subtype
      IsCombinatorialManifold 2 L ∧ IsConnected L.space ∧
      IsOrientable 2 L ∧ IsTwoSided L.space ∧
      L.space ⊆ U ∧ Separates L.space A B := by
  obtain ⟨N, hNfin, hN, hAN, hNU⟩ :=
    exists_isCombinatorialManifoldWithBoundary_neighborhood hdim hA
      (hU.inter hB.isOpen_compl) (fun x hx => ⟨hAU hx, disjoint_left.mp hAB hx⟩)
  let _ : Finite N.faces := hNfin.to_subtype
  let D := boundaryComplex 3 N
  let _ : Finite D.faces := (boundaryComplex_faces_finite 3 N).to_subtype
  let _ : Finite (ConnectedComponents D.space) := finite_connectedComponents_space D
  have hD : IsCombinatorialManifold 2 D := isCombinatorialManifold_boundaryComplex N hN
  have hfront : frontier N.space = D.space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdim N hN
  have hsep : Separates D.space A B := by
    rw [← hfront]
    apply separates_frontier hAN
    rw [(isPolyhedron_space N).isClosed.isOpen_compl.interior_eq]
    exact fun x hxB hxN => (hNU hxN).2 hxB
  obtain ⟨p, hp, hsep⟩ := exists_separating_component
    (isPolyhedron_space D).isClosed hAc hBc hsep
  let L := restrict D (connectedComponentIn D.space p)
  let _ : Finite L.faces := (restrict_faces_finite D _).to_subtype
  have hLspace : L.space = connectedComponentIn D.space p :=
    restrict_connectedComponentIn_space D p
  have hL : IsCombinatorialManifold 2 L := hD.restrict_connectedComponentIn p
  have hLc : IsConnected L.space :=
    hLspace.symm ▸ isConnected_connectedComponentIn_iff.mpr hp
  refine ⟨L, Set.toFinite _, hL, hLc, hL.isOrientable_of_finrank_eq_three L hdim hLc,
    hL.isTwoSided L hdim hLc, ?_, hLspace.symm ▸ hsep⟩
  intro x hx
  have hxD := connectedComponentIn_subset D.space p (hLspace ▸ hx)
  rw [← hfront] at hxD
  exact (hNU ((isPolyhedron_space N).isClosed.frontier_subset hxD)).1

open Classical in
theorem exists_connected_separating_surface_bettiOne_min
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ F = 3) {A B U : Set F}
    (hA : IsCompact A) (hAc : IsConnected A) (hB : IsClosed B) (hBc : IsConnected B)
    (hAB : Disjoint A B) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ (L : Geometry.SimplicialComplex ℝ F) (hLfin : L.faces.Finite),
      letI := hLfin.to_subtype
      IsCombinatorialManifold 2 L ∧ IsConnected L.space ∧
      IsOrientable 2 L ∧ IsTwoSided L.space ∧ L.space ⊆ U ∧ Separates L.space A B ∧
      ∀ (M : Geometry.SimplicialComplex ℝ F), M.faces.Finite →
        IsCombinatorialManifold 2 M → IsConnected M.space → M.space ⊆ U →
        Separates M.space A B → Homology.bettiOne L.space ≤ Homology.bettiOne M.space := by
  let P : ℕ → Prop := fun n => ∃ L : Geometry.SimplicialComplex ℝ F,
    L.faces.Finite ∧ IsCombinatorialManifold 2 L ∧ IsConnected L.space ∧
      L.space ⊆ U ∧ Separates L.space A B ∧ Homology.bettiOne L.space = n
  obtain ⟨L, hLfin, hL, hLc, -, -, hLU, hLsep⟩ :=
    exists_connected_separating_surface hdim hA hAc hB hBc hAB hU hAU
  have hP : ∃ n, P n := ⟨Homology.bettiOne L.space, L, hLfin, hL, hLc, hLU, hLsep, rfl⟩
  obtain ⟨N, hNfin, hN, hNc, hNU, hNsep, hNβ⟩ := Nat.find_spec hP
  let _ : Finite N.faces := hNfin.to_subtype
  refine ⟨N, hNfin, hN, hNc, hN.isOrientable_of_finrank_eq_three N hdim hNc,
    hN.isTwoSided N hdim hNc, hNU, hNsep, ?_⟩
  intro M hMfin hM hMc hMU hMsep
  rw [hNβ]
  exact Nat.find_min' hP ⟨M, hMfin, hM, hMc, hMU, hMsep, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
