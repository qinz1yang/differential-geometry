/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PlanarJordan.StripExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

theorem isHPolytope_planeRect (a b c d : ℝ) : IsHPolytope (planeRect a b c d) := by
  let L : Plane ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have heq : L.symm.toLinearEquiv.toAffineEquiv '' (Icc a b ×ˢ Icc c d) =
      planeRect a b c d := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h0 : (L.symm w) 0 = w.1 := congrArg Prod.fst (L.apply_symm_apply w)
      have h1 : (L.symm w) 1 = w.2 := congrArg Prod.snd (L.apply_symm_apply w)
      change a ≤ (L.symm w) 0 ∧ (L.symm w) 0 ≤ b ∧
        c ≤ (L.symm w) 1 ∧ (L.symm w) 1 ≤ d
      rw [h0, h1]
      exact ⟨hw.1.1, hw.1.2, hw.2.1, hw.2.2⟩
    · intro hv
      exact ⟨L v, ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩, L.symm_apply_apply v⟩
  rw [← heq]
  exact (isHPolytope_Icc.prod isHPolytope_Icc).image_affineEquiv _

theorem exists_simplicialComplex_planeRect (a b c d : ℝ) :
    ∃ K : Geometry.SimplicialComplex ℝ Plane,
      K.faces.Finite ∧ K.space = planeRect a b c d :=
  (isHPolytope_planeRect a b c d).isPolyhedron.exists_simplicialComplex

end DifferentialGeometry.Topology.PiecewiseLinear
