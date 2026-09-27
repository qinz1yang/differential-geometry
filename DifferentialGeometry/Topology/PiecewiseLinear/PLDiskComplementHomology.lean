/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.CompactChainSupport
import DifferentialGeometry.Topology.Homology.ComplementHomeomorphHomology
import DifferentialGeometry.Topology.Homology.ConvexComplementFirstHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDiskNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_ball_neighborhood_of_disk
    {D U : Set (EuclideanSpace ℝ (Fin 3))} (hD : IsPLBall 2 D)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ N : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 N ∧ D ⊆ N ∧ N ⊆ U := by
  classical
  obtain ⟨T, hT, hTcard, hDT⟩ := exists_affineIndependent_openSimplex_superset 3 (by simp)
    hD.isPolyhedron.isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKsp : K.space = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKsp.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hDK : D ⊆ K.space := by
    rw [hKsp]
    exact hDT.trans (openSimplex_subset_convexHull T)
  obtain ⟨K', M, -, hK'fin, hMK', hM, hMU, hMnhds⟩ :=
    hKball.isCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood
      hD.isPolyhedron.isCompact hDK hU hDU
  let _ : Finite M.faces := (hK'fin.subset hMK').to_subtype
  have hDM : D ⊆ M.space := fun x hx => mem_of_mem_nhdsWithin (hDK hx) (hMnhds x hx)
  obtain ⟨R, A, -, -, -, -, -, hN, hDN, hNM, -⟩ :=
    hM.exists_isPLBall_derivedNeighborhood_disk hD hDM
  exact ⟨_, hN, hDN, hNM.trans hMU⟩

theorem IsPLBall.subsingleton_integralFirstHomology_complement
    {B : Set (EuclideanSpace ℝ (Fin 3))} (hB : IsPLBall 3 B) :
    Subsingleton (integralSingularHomology 1 (Bᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨T, e, hT, hcard, -, he, -⟩ :=
    hB.isPLSphere_frontier.isSimplyEmbedded.2 univ convex_univ isOpen_univ (subset_univ _)
  have hP := (hasPushProperty_convexHull_simplex T hT hcard).1
  have hfront : frontier (e '' B) =
      frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) := by
    rw [← e.image_frontier, he]
  have hint : (interior (e '' B)).Nonempty := by
    rw [← e.image_interior]
    exact hB.interior_nonempty.image e
  have heq := DifferentialGeometry.Analysis.IsCompact.eq_of_frontier_eq_convex_closed
    (hB.isPolyhedron.isCompact.image e.continuous) hint (convex_convexHull ℝ _)
    hP.isPolyhedron.isCompact.isClosed hfront
  apply (subsingleton_integralComplementHomology_iff 1 e B).mpr
  rw [heq]
  obtain ⟨p, hp⟩ := hP.nonempty
  exact subsingleton_integralFirstHomology_complement_of_bounded_starConvex hp
    ((convex_convexHull ℝ _).starConvex hp) hP.isPolyhedron.isCompact.isBounded

namespace TorusLinking

theorem subsingleton_firstHomology_complement_of_isPLDisk
    {Δ : Set (EuclideanSpace ℝ (Fin 3))} (hΔ : IsPLBall 2 Δ) :
    Subsingleton (integralSingularHomology 1 (Δᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  apply subsingleton_integralSingularHomology_of_compact_carriers 0
  intro K hK hKD
  obtain ⟨N, hN, hDN, hNK⟩ := exists_ball_neighborhood_of_disk hΔ hK.isClosed.isOpen_compl
    (fun x hx hKx => hKD hKx hx)
  exact ⟨Nᶜ, fun x hx hNx => hNK hNx hx, compl_subset_compl.mpr hDN,
    hN.subsingleton_integralFirstHomology_complement⟩

end TorusLinking

end DifferentialGeometry.Topology.PiecewiseLinear
