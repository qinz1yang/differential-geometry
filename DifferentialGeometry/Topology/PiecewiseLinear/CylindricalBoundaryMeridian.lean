/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem exists_closed_boundary_diagram_of_stdSimplex
    (M : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M.space) :
    ∃ g : (Fin 3 → ℝ) × ℝ → E3,
      IsCylindricalDiagram g (stdSimplexBoundary 2) (frontier M.space) ∧
      (∀ x ∈ stdSimplexBoundary 2, g (x, 0) = g (x, 1)) ∧
      g '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) =
        f '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) := by
  classical
  let _ : DecidableEq (Fin 3 → ℝ) := fun a b => Classical.propDecidable (a = b)
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨D, hDfin, hDsp⟩ := (isPLBall_stdSimplex 2).isPolyhedron.exists_simplicialComplex
  have : Finite D.faces := hDfin.to_subtype
  have hD : IsPLBall 2 D.space := hDsp.symm ▸ isPLBall_stdSimplex 2
  have hid : IsPLHomeomorphOn id (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D.space := by
    rw [hDsp]
    exact (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
  have hDb : (boundaryComplex 2 D).space = stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D hid,
      simplexBoundary_stdVertices_space, image_id]
  have hfD : IsCylindricalDiagram f D.space M.space := hDsp.symm ▸ hf
  have hfront := hfD.frontier_eq_image_side D M hD hM (by simp)
  rw [hDb] at hfront
  have hside := hfD.boundary D hD.isCombinatorialManifoldWithBoundary
  rw [hDb, ← hfront] at hside
  have hJ : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  have hconn : IsConnected (frontier M.space) := by
    rw [hside.image_eq.symm]
    exact (hJ.isConnected.prod (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))).image _
      hside.isPiecewiseAffineOn.continuousOn
  let L := boundaryComplex 3 M
  have : Finite L.faces := (boundaryComplex_faces_finite 3 M).to_subtype
  have hL : IsCombinatorialManifold 2 L := isCombinatorialManifold_boundaryComplex M hM
  have hLsp : L.space = frontier M.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) (by simp) M hM).symm
  have hLc : IsConnected L.space := hLsp.symm ▸ hconn
  have hLo := hL.isOrientable_euclidean_three L hLc
  obtain ⟨g, hg, hends, heq⟩ := hside.exists_eq_ends_of_isOrientable L
    hL.isCombinatorialManifoldWithBoundary hLo hLsp.symm.subset
    (c := 0) le_rfl (by norm_num)
  refine ⟨g, hg, hends, ?_⟩
  apply Set.EqOn.image_eq
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  change t = 0 at ht
  subst t
  exact heq (x, 0) ⟨hx, le_rfl, le_rfl⟩

theorem IsCylindricalDiagram.boundary_slice_is_essential
    (M : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M.space) :
    IsConnected (frontier M.space \ f '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)})) ∧
      ¬ ∃ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ frontier M.space ∧
          f '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) = r '' stdSimplexBoundary 2 := by
  obtain ⟨g, hg, hends, hbase⟩ := exists_closed_boundary_diagram_of_stdSimplex M hM hf
  have hJ : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  have ht : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rw [← hbase]
    exact hg.isConnected_sdiff_slice hJ.isConnected ht
  · rintro ⟨D, r, hr, hDT, hDr⟩
    have hsub : g '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) ⊆ D := by
      rw [hbase, hDr]
      exact hr.image_eq ▸ image_mono (fun x hx => hx.1)
    have hn := (IsPLBall.nullhomotopic_inclusion ⟨r, hr⟩ hsub hDT).comp_left
      ((hg.isPLHomeomorphOn_slice hJ.isPolyhedron ht).homeomorph :
        C(stdSimplexBoundary 2, g '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)})))
    apply hg.not_nullhomotopic_slice hJ hends ht
    convert hn using 1
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
