/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLTorus.isBicollared {T : Set (EuclideanSpace ℝ (Fin 3))}
    (hT : IsPLTorus T) : IsBicollared T := by
  obtain ⟨L, hLfin, hLcomb, hLc, hLspace⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hpoly : IsPolyhedralManifold (n := 3) 2 T := by
    have hLt : L.space ⊆
        (chartAt (EuclideanSpace ℝ (Fin 3)) (0 : EuclideanSpace ℝ (Fin 3))).target := by
      rw [chartAt_self_eq]
      exact subset_univ _
    have h : IsPolyhedralManifold (n := 3) 2
        ((chartAt (EuclideanSpace ℝ (Fin 3)) (0 : EuclideanSpace ℝ (Fin 3))).symm ''
          L.space) :=
      ⟨⟨3, chartPieceOfComplex _ (chart_mem_atlas _ _) L hLt⟩, hLcomb⟩
    rw [← hLspace]
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, image_id] using h
  exact hpoly.isBicollared (hpoly.isTwoSided (hLspace ▸ hLc))

end DifferentialGeometry.Topology.PiecewiseLinear
