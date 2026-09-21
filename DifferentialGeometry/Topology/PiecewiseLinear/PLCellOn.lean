/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361

/-!
# Piecewise linear cells with a named intrinsic boundary

`IsPLCellOn d S B` says that `S` is a piecewise linear `d`-cell of a piecewise linear
`3`-manifold with *intrinsic* boundary `B`: there is a piecewise linear parametrisation `r` of
the standard `d`-simplex onto a polyhedron `P` of `ℝ³`, and a piecewise linear embedding `u` of
`P`, with `S = u '' P` and `B = u '' (r '' stdSimplexBoundary d)`.  The intrinsic boundary is
read off the parametrisation and is in general not the ambient frontier of `S`; the two agree
only in codimension zero.

Only compactness and nonemptiness of the cell are available here.  The invariance of domain
package that Section 34 uses silently is still owed to this file: uniqueness of the intrinsic
boundary, `IsPLCellOn d S B → IsPLCellOn d S B' → B = B'`; its agreement with the ambient
frontier in codimension zero, `IsPLCellOn 3 S B → B = frontier S`; and distinctness of the
dimensions, so that one set is not both a `1`-cell and a `2`-cell.  The natural tool for the
second, `IsPLHomeomorphInto.image_frontier`, asks for an open domain, whereas `IsPLCellOn`
supplies a compact polyhedral ball only.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def IsPLCellOn (d : ℕ) (S B : Set M) : Prop :=
  ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (u : EuclideanSpace ℝ (Fin 3) → M),
    IsPLHomeomorphOn r (stdSimplex ℝ (Fin (d + 1))) P ∧ IsPLHomeomorphInto 3 u P ∧
      S = u '' P ∧ B = u '' (r '' stdSimplexBoundary d)

theorem IsPLCellOn.isCompact {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) : IsCompact S := by
  obtain ⟨P, r, u, hr, hu, hcell, -⟩ := hS
  rw [hcell]
  exact ((IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact).image_of_continuousOn hu.continuousOn

theorem IsPLCellOn.nonempty {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) : S.Nonempty := by
  obtain ⟨P, r, u, hr, -, hcell, -⟩ := hS
  rw [hcell]
  exact (IsPLBall.nonempty ⟨r, hr⟩).image u

end DifferentialGeometry.Topology.PiecewiseLinear
