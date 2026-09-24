/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere

/-!
# Connected boundaries of positive-dimensional PL cells

The intrinsic boundary of a cell of dimension at least two is connected, by transporting
the standard boundary sphere through its cell parametrization.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isConnected_boundary {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {n : ℕ} {S B : Set M}
    (h : IsPLCellOn (n + 2) S B) : IsConnected B := by
  obtain ⟨P, r, u, hr, hu, -, rfl⟩ := h
  have hsub : r '' stdSimplexBoundary (n + 2) ⊆ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hr.bijOn.mapsTo hz.1
  exact (hr.isPLSphere_image_stdSimplexBoundary (n := n + 1)).isConnected.image u
    (hu.continuousOn.mono hsub)

end DifferentialGeometry.Topology.PiecewiseLinear
