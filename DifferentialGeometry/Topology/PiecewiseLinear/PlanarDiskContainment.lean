/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AffineSubspaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Analysis.Convex.CompactFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.subset_convex_of_boundary_subset_of_subset_affineSubspace
    {n : ℕ} {D W : Set E} {q : (Fin (n + 2) → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D)
    (s : AffineSubspace ℝ E) (hs : Module.finrank ℝ s.direction = n + 1) (hDs : D ⊆ s)
    (hW : Convex ℝ W) (hWo : IsOpen W) (hJW : q '' stdSimplexBoundary (n + 1) ⊆ W) : D ⊆ W := by
  have hD : IsPLBall (n + 1) D := ⟨q, hq⟩
  obtain ⟨A, B, hA, hBA⟩ := exists_isPLHomeomorphOn_affine_of_subset_affineSubspace
    (F := EuclideanSpace ℝ (Fin (n + 1))) hD.isPolyhedron s (hD.nonempty.mono hDs)
    (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using hs) hDs
  have hfront := (hq.trans hA).image_stdSimplexBoundary_eq_frontier
  have htarget : frontier (A '' D) ⊆ B ⁻¹' W := by
    rw [← hfront]
    rintro y ⟨x, hx, rfl⟩
    change B (A (q x)) ∈ W
    rw [show B (A (q x)) = q x from hBA (hq.bijOn.mapsTo hx.1)]
    exact hJW (mem_image_of_mem q hx)
  have hsub : A '' D ⊆ B ⁻¹' W :=
    DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_convex_open
      (hD.of_isPLHomeomorphOn hA).isPolyhedron.isCompact (hW.affine_preimage B)
      (hWo.preimage B.continuous_of_finiteDimensional) htarget
  intro x hx
  have h := hsub (mem_image_of_mem A hx)
  change B (A x) ∈ W at h
  rwa [show B (A x) = x from hBA hx] at h

end DifferentialGeometry.Topology.PiecewiseLinear
