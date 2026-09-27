/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_simplex_subdivision_graphDualCell_diam_lt [FiniteDimensional ℝ E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    {N : ℕ} (hcard : ∀ s ∈ L.faces, s.card ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ T L' : Geometry.SimplicialComplex ℝ E, T.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) T ∧ IsSubdivision L' L ∧
      L'.faces ⊆ T.faces ∧ L.space ⊆ interior T.space ∧ (∀ s ∈ L'.faces, s.card ≤ N) ∧
      ∀ v, Metric.diam (graphDualCell T L' v).space < ε := by
  classical
  obtain ⟨Δ, hΔ, hΔcard, hLΔ⟩ := exists_affineIndependent_openSimplex_superset (n + 1) hn
    (SimplicialComplex.isCompact_geometricSpace L).isBounded
  let _ : Finite (simplexComplex Δ hΔ).faces := (simplexComplex_faces_finite Δ hΔ).to_subtype
  have hΔsp : (simplexComplex Δ hΔ).space = convexHull ℝ (Δ : Set E) :=
    simplexComplex_space Δ hΔ (Finset.card_pos.mp (by omega))
  obtain ⟨L₀, T₀, -, hT₀fin, hL₀, hT₀, hmap, -⟩ := exists_isSubdivision_affineMap L
    (simplexComplex Δ hΔ) (AffineMap.id ℝ E) fun x hx => by
      rw [hΔsp]
      exact openSimplex_subset_convexHull Δ (hLΔ hx)
  let _ : Finite T₀.faces := hT₀fin.to_subtype
  have hL₀T₀ : L₀.faces ⊆ T₀.faces := fun s hs => by simpa using hmap s hs
  obtain ⟨T, L', hT, hL', hTfin, hL'T, hcard', hdiam⟩ :=
    exists_isSubdivision_graphDualCell_diam_lt T₀ L₀ hL₀T₀ (fun s hs => hL₀.card_le hcard hs) hε
  let _ : Finite T.faces := hTfin.to_subtype
  have hTsp : T.space = convexHull ℝ (Δ : Set E) := by
    rw [hT.space_eq, hT₀.space_eq, hΔsp]
  refine ⟨T, L', hTfin, ?_, hL'.trans hL₀, hL'T, ?_, hcard', hdiam⟩
  · apply IsPLBall.isCombinatorialManifoldWithBoundary
    rw [hTsp]
    exact isPLBall_convexHull_of_affineIndependent Δ hΔ hΔcard
  · rw [hTsp, interior_convexHull_eq_openSimplex hΔ (by rw [hΔcard, hn])]
    exact hLΔ

end DifferentialGeometry.Topology.PiecewiseLinear
