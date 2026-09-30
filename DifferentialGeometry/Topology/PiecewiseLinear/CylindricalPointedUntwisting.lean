/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalManifold
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalClassification
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexPointedPseudoIsotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsCylindricalDiagram.isPLPseudoIsotopicToId_endMap_of_finrank_eq_three
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P)
    (hdim : Module.finrank ℝ F = 3) {u : E → E}
    (hu : IsPLHomeomorphOn u P P) (hfu : ∀ x ∈ P, f (x, 0) = f (u x, 1)) :
    IsPLPseudoIsotopicToId u P := by
  classical
  have hS : IsPolyhedron S := by
    rw [← hf.image_eq]
    exact hf.isPiecewiseAffineOn.isPolyhedron_image
      (hP.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
  obtain ⟨M, hMfin, hMsp⟩ := hS.exists_simplicialComplex
  let _ : Finite M.faces := hMfin.to_subtype
  have hfM : IsCylindricalDiagram f P M.space := hMsp.symm ▸ hf
  have hM := hfM.isCombinatorialManifoldWithBoundary M hP
  obtain ⟨T, -, hTcard, hMT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space M).isCompact.isBounded
  have hor : IsOrientable 3 M := isOrientable_of_space_subset_convexHull M hM T hTcard
    (hMT.trans (openSimplex_subset_convexHull T))
  exact hfM.isPLPseudoIsotopicToId_endMap hP M hM hor hu hfu

theorem IsCylindricalDiagram.exists_endMap_id_preserving_stdCenter
    {S : Set F} {f : (Fin 3 → ℝ) × ℝ → F}
    (hf : IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) S)
    (hdim : Module.finrank ℝ F = 3)
    (hclosed : f (stdCenter 1, 0) = f (stdCenter 1, 1)) :
    ∃ g : (Fin 3 → ℝ) × ℝ → F,
      IsCylindricalDiagram g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) S ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), g (x, 0) = g (x, 1)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, g (stdCenter 1, t) = f (stdCenter 1, t) := by
  have hP := (isPLBall_stdSimplex 2).isPolyhedron
  obtain ⟨u, hu, hfu⟩ := hf.exists_isPLHomeomorphOn_endMap hP
  have hp : stdCenter 1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    constructor
    · intro i
      norm_num [stdCenter]
    · norm_num [stdCenter, Fin.sum_univ_three]
  have hup : u (stdCenter 1) = stdCenter 1 :=
    hf.eq_of_eq_top (hu.bijOn.mapsTo hp) hp ((hfu _ hp).symm.trans hclosed)
  have hiso := hf.isPLPseudoIsotopicToId_endMap_of_finrank_eq_three
    (isPLBall_stdSimplex 2) hdim hu hfu
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, hΨp⟩ := hiso.exists_isPLHomeomorphOn_fixed_stdCenter hup
  refine ⟨f ∘ Ψ, hf.comp_of_ends hP.isPLHomeomorphOn_id hu hΨ hΨ0 hΨ1,
    fun x hx => ?_, fun t ht => ?_⟩
  · change f (Ψ (x, 0)) = f (Ψ (x, 1))
    rw [hΨ0 x hx, hΨ1 x hx]
    exact hfu x hx
  · change f (Ψ (stdCenter 1, t)) = f (stdCenter 1, t)
    rw [hΨp t ht]

end DifferentialGeometry.Topology.PiecewiseLinear
