/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnIntrinsicInterior

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.closure_sdiff_boundary {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) :
    closure (S \ B) = S := by
  have hSc := hS.isCompact.isClosed
  cases d with
  | zero =>
    have hB : B = ∅ := by
      obtain ⟨P, r, u, -, -, -, hB⟩ := hS
      rw [hB, stdSimplexBoundary_zero, image_empty, image_empty]
    rw [hB, sdiff_empty, hSc.closure_eq]
  | succ n =>
    refine Subset.antisymm (closure_minimal sdiff_subset hSc) ?_
    obtain ⟨P, r, u, hr, hu, hSE, hBE⟩ := hS
    have hBd : r '' stdSimplexBoundary (n + 1) ⊆ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hr.bijOn.mapsTo hx.1
    rw [hSE, hBE, ← hu.injOn.image_sdiff_subset hBd]
    have hcl := hr.closure_sdiff_image_stdSimplexBoundary (n := n)
    calc u '' P = u '' closure (P \ r '' stdSimplexBoundary (n + 1)) := by rw [hcl]
      _ ⊆ closure (u '' (P \ r '' stdSimplexBoundary (n + 1))) :=
        ContinuousOn.image_closure (by rw [hcl]; exact hu.continuousOn)

end DifferentialGeometry.Topology.PiecewiseLinear
