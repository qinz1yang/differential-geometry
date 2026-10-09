/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLAt_of_mem_maximalAtlas {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ (plGroupoid n).maximalAtlas M) {y : M} (hy : y ∈ c.source) :
    IsPLAt n n c y := by
  change ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty n n) c univ y
  rw [StructureGroupoid.liftPropWithinAt_self_target]
  refine ⟨(c.continuousAt hy).continuousWithinAt, ?_⟩
  have hye : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).source := mem_chart_source _ y
  have hT : (chartAt (EuclideanSpace ℝ (Fin n)) y).symm ≫ₕ c ∈ plGroupoid n :=
    StructureGroupoid.compatible_of_mem_maximalAtlas_right hc
  have hyT : chartAt (EuclideanSpace ℝ (Fin n)) y y ∈
      ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm ≫ₕ c).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    refine ⟨(chartAt (EuclideanSpace ℝ (Fin n)) y).map_source hye, ?_⟩
    change (chartAt (EuclideanSpace ℝ (Fin n)) y).symm (chartAt (EuclideanSpace ℝ (Fin n)) y y) ∈
      c.source
    rw [(chartAt (EuclideanSpace ℝ (Fin n)) y).left_inv hye]
    exact hy
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := (mem_plGroupoid_iff.mp hT).1 _ hyT
  rw [preimage_univ]
  refine ⟨ι, hι, C, A, fun i => ⟨(hC i).1, subset_univ _, (hC i).2.2⟩, ?_⟩
  rw [nhdsWithin_univ]
  rwa [((chartAt (EuclideanSpace ℝ (Fin n)) y).symm ≫ₕ c).open_source.nhdsWithin_eq hyT] at hCx

theorem IsPLCellOn.exists_isPLHomeomorphOn_image_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hSc : S ⊆ c.source) :
    ∃ q : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) (c '' S) ∧
        c '' B = q '' stdSimplexBoundary d := by
  obtain ⟨P, r, u, hr, hu, rfl, rfl⟩ := hS
  have hP : IsPolyhedron P := IsPLBall.isPolyhedron ⟨r, hr⟩
  have hcu : IsPLOn 3 3 (c ∘ u) P := fun x hx =>
    IsPLAt.comp_isPLWithinAt (isPLAt_of_mem_maximalAtlas hc (hSc ⟨x, hx, rfl⟩))
      (hu.isPLOn x hx)
  have hpa : IsPiecewiseAffineOn (c ∘ u) P := isPLOn_iff_isPiecewiseAffineOn.mp hcu
  have hinj : InjOn (c ∘ u) P := fun x hx y hy hxy =>
    hu.injOn hx hy (c.injOn (hSc ⟨x, hx, rfl⟩) (hSc ⟨y, hy, rfl⟩) hxy)
  have h := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP hpa hinj.bijOn_image
  refine ⟨(c ∘ u) ∘ r, ?_, ?_⟩
  · rw [← image_comp]
    exact hr.trans h
  · rw [image_comp, image_comp]

theorem IsPLCellOn.isPLBall_image_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M} (hS : IsPLCellOn 3 S B)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hSc : S ⊆ c.source) :
    IsPLBall 3 (c '' S) ∧ c '' B = frontier (c '' S) := by
  obtain ⟨q, hq, hB⟩ := hS.exists_isPLHomeomorphOn_image_chart hc hSc
  exact ⟨⟨q, hq⟩, hB.trans (IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hq)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
