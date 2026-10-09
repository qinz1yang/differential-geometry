/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_eqOn_boundary_disk_in_polyhedron
    {M C D U : Set (EuclideanSpace ℝ (Fin 3))}
    (hM : IsPolyhedron M) (hC : IsPLBall 3 C) (hCM : C ⊆ M)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDC : D ⊆ C) (hDM : D ⊆ frontier M)
    (hU : IsOpen U) (hUC : U ∩ M ⊆ C)
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g D D) (hfix : EqOn g id (r '' stdSimplexBoundary 2))
    (hfixU : EqOn g id (D \ U)) :
    ∃ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn G M M ∧ EqOn G g D ∧ EqOn G id (closure (M \ C)) := by
  have hDfront : D ⊆ frontier C := by
    intro x hx
    exact ⟨subset_closure (hDC hx), fun hxi => (hDM hx).2 (interior_mono hCM hxi)⟩
  obtain ⟨f, hf, hfg, hfid⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_eqOn_boundary
    hC.isPLSphere_frontier hr hDfront hg hfix
  obtain ⟨k, hk, hkf⟩ := exists_isPLHomeomorphOn_of_frontier hC hC hf
  have hkfix : EqOn k id (frontier C \ U) := by
    intro x hx
    rw [hkf hx.1]
    by_cases hxD : x ∈ D
    · exact (hfg hxD).trans (hfixU ⟨hxD, hx.2⟩)
    · exact hfid (subset_closure ⟨hx.1, hxD⟩)
  obtain ⟨G, hG, hGk, hGid⟩ := hk.exists_extension_on_polyhedron hC.isPolyhedron hM hCM
    hU hUC hkfix
  exact ⟨G, hG, (hGk.mono hDC).trans ((hkf.mono hDfront).trans hfg), hGid⟩

theorem exists_isPLHomeomorphOn_extension_boundary_patch
    {M C U : Set (EuclideanSpace ℝ (Fin 3))}
    (hM : IsPolyhedron M) (hC : IsPLBall 3 C) (hCM : C ⊆ M)
    (hB : IsPLBall 2 (C ∩ frontier M)) (hU : IsOpen U) (hUC : U ∩ M ⊆ C)
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (C ∩ frontier M) (C ∩ frontier M))
    (hfix : EqOn g id ((C ∩ frontier M) \ U)) :
    ∃ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn G M M ∧ EqOn G g (C ∩ frontier M) ∧
      EqOn G id (closure (M \ C)) := by
  have hBfront : C ∩ frontier M ⊆ frontier C := by
    rintro x ⟨hxC, hxM⟩
    exact ⟨subset_closure hxC, fun hxi => hxM.2 (interior_mono hCM hxi)⟩
  have hlocal : frontier C ∩ U ⊆ C ∩ frontier M := by
    rintro x ⟨hxC, hxU⟩
    have hxC' : x ∈ C := hC.isPolyhedron.isClosed.frontier_subset hxC
    refine ⟨hxC', subset_closure (hCM hxC'), ?_⟩
    intro hxM
    apply hxC.2
    exact interior_maximal
      (fun y hy => hUC ⟨hy.1, interior_subset hy.2⟩)
      (hU.inter isOpen_interior) ⟨hxU, hxM⟩
  have hcomp : closure (frontier C \ (C ∩ frontier M)) ⊆ Uᶜ := by
    apply closure_minimal ?_ hU.isClosed_compl
    rintro x ⟨hxC, hxB⟩ hxU
    exact hxB (hlocal ⟨hxC, hxU⟩)
  obtain ⟨r, hr⟩ := hB
  have hrfix : EqOn g id (r '' stdSimplexBoundary 2) := by
    rw [← hC.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hBfront]
    exact fun _ hx => hfix ⟨hx.1, hcomp hx.2⟩
  exact exists_isPLHomeomorphOn_eqOn_boundary_disk_in_polyhedron hM hC hCM hr
    inter_subset_left inter_subset_right hU hUC hg hrfix hfix

end DifferentialGeometry.Topology.PiecewiseLinear
