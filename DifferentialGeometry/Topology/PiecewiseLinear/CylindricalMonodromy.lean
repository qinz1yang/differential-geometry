/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding

/-! Boundary monodromy of orientable disk cylindrical diagrams. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {S : Set F}

open Classical in
theorem boundary (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces]
    {n : ℕ} (hD : IsCombinatorialManifoldWithBoundary (n + 1) D)
    (hf : IsCylindricalDiagram f D.space S) :
    IsCylindricalDiagram f (boundaryComplex (n + 1) D).space
      (f '' ((boundaryComplex (n + 1) D).space ×ˢ Icc (0 : ℝ) 1)) := by
  let _ : Finite (boundaryComplex (n + 1) D).faces :=
    (boundaryComplex_faces_finite (n + 1) D).to_subtype
  have hBsub := boundaryComplex_space_subset (n + 1) D
  have hBpoly := isPolyhedron_space (boundaryComplex (n + 1) D)
  obtain ⟨u, hu, hfu⟩ := hf.exists_isPLHomeomorphOn_endMap (isPolyhedron_space D)
  have huB : IsPLHomeomorphOn u (boundaryComplex (n + 1) D).space
      (boundaryComplex (n + 1) D).space := by
    have h := hu.restrict hBpoly hBsub
    rwa [← boundaryComplex_space_of_isPLHomeomorphOn D D hD hu] at h
  refine ⟨hf.isPiecewiseAffineOn.mono_of_isPolyhedron
    (hBpoly.prod isHPolytope_Icc.isPolyhedron) (prod_mono hBsub Subset.rfl), rfl, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = 1 := ht
      subst t
      obtain ⟨z, hz, hzx⟩ := huB.bijOn.surjOn hx
      refine ⟨(z, 0), ⟨hz, rfl⟩, ?_⟩
      simpa only [hzx] using hfu z (hBsub hz)
    · rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = 0 := ht
      subst t
      exact ⟨(u x, 1), ⟨huB.bijOn.mapsTo hx, rfl⟩, (hfu x (hBsub hx)).symm⟩
  · intro x hx y hy hxy
    exact hf.eq_or_endpoints x ⟨hBsub hx.1, hx.2⟩ y ⟨hBsub hy.1, hy.2⟩ hxy

open Classical in
theorem boundary_isPLCirclePositive
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f D.space M.space) {v : E → E}
    (hv : IsPLHomeomorphOn v D.space D.space)
    (hfv : ∀ x ∈ D.space, f (x, 1) = f (v x, 0)) :
    IsPLCirclePositive (boundaryComplex 2 D).space v := by
  let _ : Finite (boundaryComplex 2 D).faces := (boundaryComplex_faces_finite 2 D).to_subtype
  let _ : Finite (boundaryComplex 3 M).faces := (boundaryComplex_faces_finite 3 M).to_subtype
  have hBsub := boundaryComplex_space_subset 2 D
  have hvB : IsPLHomeomorphOn v (boundaryComplex 2 D).space
      (boundaryComplex 2 D).space := by
    have h := hv.restrict (isPolyhedron_space _) hBsub
    rwa [← boundaryComplex_space_of_isPLHomeomorphOn D D
      hD.isCombinatorialManifoldWithBoundary hv] at h
  exact isPLCirclePositive_of_isOrientable_cylindricalDiagram (boundaryComplex 3 M)
    (isCombinatorialManifold_boundaryComplex M hM).isCombinatorialManifoldWithBoundary
    (IsOrientable.boundary M hM hor) (isPLSphere_boundaryComplex_space_of_isPLBall D hD)
    (hf.boundary D hD.isCombinatorialManifoldWithBoundary)
    (hf.image_side_subset_boundaryComplex D M hD hM) hvB (fun x hx => hfv x (hBsub hx))

open Classical in
theorem boundary_isPLCirclePositive_of_bottom_eq_top
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f D.space M.space) {u : E → E}
    (hu : IsPLHomeomorphOn u D.space D.space)
    (hfu : ∀ x ∈ D.space, f (x, 0) = f (u x, 1)) :
    IsPLCirclePositive (boundaryComplex 2 D).space u := by
  let _ : Finite (boundaryComplex 2 D).faces := (boundaryComplex_faces_finite 2 D).to_subtype
  have hBsub := boundaryComplex_space_subset 2 D
  have hvB : IsPLHomeomorphOn (Function.invFunOn u D.space) (boundaryComplex 2 D).space
      (boundaryComplex 2 D).space := by
    have h := hu.symm.restrict (isPolyhedron_space _) hBsub
    rwa [← boundaryComplex_space_of_isPLHomeomorphOn D D
      hD.isCombinatorialManifoldWithBoundary hu.symm] at h
  have hfv : ∀ x ∈ D.space, f (x, 1) = f (Function.invFunOn u D.space x, 0) := by
    intro x hx
    have h := hfu (Function.invFunOn u D.space x) (hu.symm.bijOn.mapsTo hx)
    rw [hu.bijOn.invOn_invFunOn.2 hx] at h
    exact h.symm
  have hpos := hf.boundary_isPLCirclePositive D M hD hM hor hu.symm hfv
  have huB : MapsTo u (boundaryComplex 2 D).space (boundaryComplex 2 D).space := by
    intro x hx
    exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn D D
      hD.isCombinatorialManifoldWithBoundary hu (hBsub hx)).mpr hx
  exact hpos.of_leftInverse hvB.bijOn huB
    (fun x hx => hu.bijOn.invOn_invFunOn.2 (hBsub hx))

end IsCylindricalDiagram

end DifferentialGeometry.Topology.PiecewiseLinear
