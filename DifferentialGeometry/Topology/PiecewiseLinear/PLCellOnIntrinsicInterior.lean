/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.sdiff_boundary_nonempty {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] {d : ℕ} {S B : Set M} (hcell : IsPLCellOn d S B) :
    (S \ B).Nonempty := by
  obtain ⟨P, r, u, hr, hu, rfl, rfl⟩ := hcell
  cases d with
  | zero =>
      rw [stdSimplexBoundary_zero, image_empty, image_empty, sdiff_empty]
      exact (show IsPLBall 0 P from ⟨r, hr⟩).nonempty.image u
  | succ d =>
      have hbd : r '' stdSimplexBoundary (d + 1) ⊆ P := by
        rintro _ ⟨x, hx, rfl⟩
        exact hr.bijOn.mapsTo hx.1
      rw [← hu.injOn.image_sdiff_subset hbd]
      exact hr.isConnected_sdiff_image_stdSimplexBoundary.nonempty.image u

end DifferentialGeometry.Topology.PiecewiseLinear
