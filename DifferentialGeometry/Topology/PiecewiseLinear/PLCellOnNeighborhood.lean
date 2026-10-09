/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLCellOn_subset_of_mem_nhds {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {x : M} {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ C : Set M, IsPLCellOn 3 C (frontier C) ∧ x ∈ interior C ∧ C ⊆ N := by
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.mp hN
  obtain ⟨P, hP, hPt, hPnhds, hPO⟩ :=
    exists_isHPolytope_image_symm_mem_nhds_subset (n := 3) hO hxO
  let e := chartAt (EuclideanSpace ℝ (Fin 3)) x
  have hPnhds' : P ∈ 𝓝 (e x) := by
    rw [← e.image_symm_image_of_subset_target hPt]
    exact e.image_mem_nhds (mem_chart_source _ x) hPnhds
  have hball : IsPLBall 3 P := by
    simpa only [finrank_euclideanSpace_fin] using
      hP.isPLBall ⟨e x, mem_interior_iff_mem_nhds.mpr hPnhds'⟩
  have hEpl : IsPLOn 3 3 e.symm P :=
    (isPLOn_chart_symm x).mono_of_isPolyhedron hP.isPolyhedron hPt
  have hEemb : IsPLHomeomorphInto 3 e.symm P :=
    hEpl.isPLHomeomorphInto hP.isCompact (injOn_symm_of_subset_target e hPt)
  obtain ⟨r, hr⟩ := hball
  have hmodel : IsPLCellOn 3 P (r '' stdSimplexBoundary 3) :=
    isPLCellOn_id_of_isPLBall hr
  rw [hmodel.boundary_eq_frontier] at hmodel
  have hcell : IsPLCellOn 3 (e.symm '' P) (frontier (e.symm '' P)) := by
    rw [← (hmodel.image_boundary_interior hEemb).1]
    exact hmodel.image hEemb
  exact ⟨e.symm '' P, hcell, mem_interior_iff_mem_nhds.mpr hPnhds, hPO.trans hON⟩

end DifferentialGeometry.Topology.PiecewiseLinear
