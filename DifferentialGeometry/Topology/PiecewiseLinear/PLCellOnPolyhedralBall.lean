/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundarySphere
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isPolyhedralBall {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {d : ℕ} {C B : Set M} (hC : IsPLCellOn d C B) : IsPolyhedralBall (n := 3) d C := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hC
  have hP : IsPLBall d P := ⟨r, hr⟩
  obtain ⟨T, -, hTP⟩ := hu.exists_pLPiece_of_isPolyhedron hP.isPolyhedron
  exact ⟨⟨3, T⟩, hTP.symm ▸ hP⟩

theorem IsPolyhedralBall.exists_isPLCellOn {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {d : ℕ} {C : Set M} (hC : IsPolyhedralBall (n := 3) d C) (hd : d ≤ 3) :
    ∃ B : Set M, IsPLCellOn d C B := by
  obtain ⟨-, -, ⟨P, r, -, hr, -, -, -⟩, -⟩ := exists_isPLCellOn_of_le_three d hd
  obtain ⟨T, q, hq⟩ := hC
  have hP : IsPLBall d P := ⟨r, hr⟩
  have hf := hr.symm.trans hq
  have hpl := T.piece.isPLOn_comp hf.isPiecewiseAffineOn hf.bijOn.mapsTo
  have hinj := T.piece.bijOn.injOn.comp hf.bijOn.injOn hf.bijOn.mapsTo
  have hu := hpl.isPLHomeomorphInto hP.isPolyhedron.isCompact hinj
  refine ⟨(T.piece.map ∘ (q ∘ Function.invFunOn r _)) '' (r '' stdSimplexBoundary d),
    P, r, T.piece.map ∘ (q ∘ Function.invFunOn r _), hr, hu, ?_, rfl⟩
  rw [image_comp, hf.image_eq, T.piece.bijOn.image_eq]

theorem IsPolyhedralBall.isPLCellOn {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C : Set M} (hC : IsPolyhedralBall (n := 3) 3 C) :
    IsPLCellOn 3 C (frontier C) := by
  obtain ⟨B, hB⟩ := hC.exists_isPLCellOn le_rfl
  exact hB.boundary_eq_frontier ▸ hB

end DifferentialGeometry.Topology.PiecewiseLinear
