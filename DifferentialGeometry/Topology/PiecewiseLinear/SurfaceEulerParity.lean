/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryEuler
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceFilling
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceHomology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.even_eulerChar_of_finrank_eq_three
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hdim : Module.finrank ℝ E = 3)
    (hSc : IsConnected S.space) : Even (eulerChar S) := by
  obtain ⟨R, hRfin, hR, hbd, _, _, _, _⟩ :=
    hS.exists_isCombinatorialManifoldWithBoundary_boundaryComplex S hdim hSc
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (boundaryComplex 3 R).faces := (boundaryComplex_faces_finite 3 R).to_subtype
  have heq : eulerChar S = eulerChar (boundaryComplex 3 R) := by
    rw [eulerChar_eq_singular S ℚ, eulerChar_eq_singular (boundaryComplex 3 R) ℚ, hbd]
  refine ⟨eulerChar R, ?_⟩
  rw [heq, eulerChar_boundaryComplex_eq_two_mul R hR, two_mul]

theorem IsCombinatorialManifold.even_bettiOne_of_finrank_eq_three
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hdim : Module.finrank ℝ E = 3)
    (hSc : IsConnected S.space) : Even (Homology.bettiOne S.space) := by
  obtain ⟨k, hk⟩ := hS.even_eulerChar_of_finrank_eq_three S hdim hSc
  have hEuler := hS.eulerChar_eq_two_sub_bettiOne_of_isOrientable S hSc
    (hS.isOrientable_of_finrank_eq_three S hdim hSc)
  have hnonneg : 0 ≤ 1 - k := by omega
  refine ⟨(1 - k).toNat, ?_⟩
  have hcast := Int.toNat_of_nonneg hnonneg
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
