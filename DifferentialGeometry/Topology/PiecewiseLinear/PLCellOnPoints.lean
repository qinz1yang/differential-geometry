/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnEndpoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.boundary_eq_empty
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B : Set M} (h : IsPLCellOn 0 S B) : B = ∅ := by
  obtain ⟨P, r, u, -, -, -, hB⟩ := h
  simpa only [stdSimplexBoundary_zero, image_empty] using hB

theorem LocallyFinitePLPieceIn.isPLCellOn_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} (T : LocallyFinitePLPieceIn E 3 M U) {x : E} (hx : x ∈ T.complex.space) :
    IsPLCellOn 0 {T.map x} ∅ := by
  have hball : IsPLBall 0 ({x} : Set E) :=
    ⟨fun _ => x, isPLHomeomorphOn_const_stdSimplex_fin_one x⟩
  obtain ⟨B, hB⟩ := T.exists_isPLCellOn_image (singleton_subset_iff.mpr hx) (by omega) hball
  rw [image_singleton] at hB
  exact hB.boundary_eq_empty ▸ hB

end DifferentialGeometry.Topology.PiecewiseLinear
