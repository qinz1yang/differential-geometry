/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

/-! # PLCell On Boundary Sphere -/

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_pLPiece_of_isPolyhedron {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [HasGroupoid M (plGroupoid n)] {P : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → M} (hu : IsPLHomeomorphInto n u P)
    (hP : IsPolyhedron P) :
    ∃ T : PLPieceIn (EuclideanSpace ℝ (Fin n)) n M (u '' P),
      T.map = u ∧ T.complex.space = P := by
  obtain ⟨K, hfin, hKP⟩ := hP.exists_simplicialComplex
  rw [← hKP] at hu ⊢
  refine ⟨{
    complex := K
    finite_faces := hfin
    map := u
    bijOn := hu.injOn.bijOn_image
    continuousOn := hu.continuousOn
    isPiecewiseAffineOn_chart := ?_
    isPiecewiseAffineOn_chart_symm := ?_ }, rfl, rfl⟩
  · intro e he x hx
    have hlocal := IsPLWithinAt.mono_of_mem_nhdsWithin (hu.isPLOn x hx.1) inter_subset_left
      (Filter.inter_mem self_mem_nhdsWithin
        ((hu.continuousOn x hx.1).preimage_mem_nhdsWithin (e.open_source.mem_nhds hx.2)))
    exact ((isPLWithinAt_iff_of_mem_maximalAtlas
      (StructureGroupoid.chart_mem_maximalAtlas (plGroupoid n) x) (mem_chart_source _ x)
      (StructureGroupoid.subset_maximalAtlas (plGroupoid n) he) hx.2).mp hlocal).2
  · intro e he y hy
    have hinv := hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn (e.symm y) hy.2
    have hcoord := ((isPLWithinAt_iff_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas (plGroupoid n) he) (e.map_target hy.1)
      (StructureGroupoid.chart_mem_maximalAtlas (plGroupoid n)
        (Function.invFunOn u K.space (e.symm y))) (mem_chart_source _ _)).mp hinv).2
    change IsPiecewiseAffineWithinAt (Function.invFunOn u K.space ∘ e.symm)
      (e.symm ⁻¹' (u '' K.space)) (e (e.symm y)) at hcoord
    rw [e.right_inv hy.1] at hcoord
    simpa only [inter_comm] using hcoord.inter_of_mem_nhds (e.open_target.mem_nhds hy.1)

theorem IsPLCellOn.isPolyhedralSphere_boundary {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {Y Yb : Set M} (h : IsPLCellOn 3 Y Yb) : IsPolyhedralSphere (n := 3) 2 Yb := by
  obtain ⟨P, r, u, hr, hu, -, rfl⟩ := h
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  rw [hr.image_stdSimplexBoundary]
  obtain ⟨T, hTu, hTP⟩ := hu.exists_pLPiece_of_isPolyhedron hP.isPolyhedron
  have hbd := hP.isPLSphere_frontier
  obtain ⟨S, hSP, -⟩ := T.exists_restrict_of_isPolyhedron hbd.isPolyhedron
    (hTP.symm ▸ hP.isPolyhedron.isClosed.frontier_subset)
  have hresult : IsPolyhedralSphere (n := 3) 2 (T.map '' frontier P) :=
    ⟨⟨3, S⟩, hSP.symm ▸ hbd⟩
  simpa only [hTu] using hresult

end DifferentialGeometry.Topology.PiecewiseLinear
