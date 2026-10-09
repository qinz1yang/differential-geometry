/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnClosure

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]

theorem IsPLCellOn.exists_preconnected_sdiff_boundary {n : ℕ} {D B : Set M}
    (hD : IsPLCellOn (n + 1) D B) {x : M} (hx : x ∈ D)
    {O : Set M} (hO : O ∈ 𝓝 x) :
    ∃ L : Set M, L ⊆ O ∧ L ⊆ D \ B ∧ IsPreconnected L ∧
      ∃ O' : Set M, IsOpen O' ∧ x ∈ O' ∧ O' ∩ (D \ B) ⊆ L := by
  obtain ⟨P, r, u, hr, hu, hDP, hBP⟩ := hD
  let q := u ∘ r
  have hqc : ContinuousOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) :=
    hu.continuousOn.comp hr.isPiecewiseAffineOn.continuousOn hr.bijOn.mapsTo
  have hqi : InjOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) :=
    hu.injOn.comp hr.bijOn.injOn hr.bijOn.mapsTo
  have hqD : q '' Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) = D := by
    rw [image_comp, hr.image_eq, ← hDP]
  have hbd : r '' stdSimplexBoundary (n + 1) ⊆ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hr.bijOn.mapsTo hz.1
  have hqI : q '' openSimplex (stdVertices n) = D \ B := by
    rw [image_comp, hr.image_openSimplex_stdVertices,
      hu.injOn.image_sdiff_subset hbd, ← hDP, ← hBP]
  obtain ⟨b, hb, rfl⟩ := hqD.symm ▸ hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hqc b hb).preimage_mem_nhdsWithin hO)
  obtain ⟨T, hT, hTeq⟩ := exists_isOpen_inter_image_eq_of_isCompact
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin (n + 2))) hqc hqi
    (Metric.isOpen_ball (x := b) (ε := ε))
  have hsub : Metric.ball b ε ∩ openSimplex (stdVertices n) ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) :=
    inter_subset_right.trans openSimplex_stdVertices_subset_stdSimplex
  refine ⟨q '' (Metric.ball b ε ∩ openSimplex (stdVertices n)), ?_, ?_, ?_,
    T, hT, ?_, ?_⟩
  · rintro _ ⟨z, ⟨hzr, hzo⟩, rfl⟩
    exact hball ⟨hzr, openSimplex_stdVertices_subset_stdSimplex hzo⟩
  · rw [← hqI]
    exact image_mono inter_subset_right
  · exact ((convex_ball b ε).inter (convex_openSimplex _)).isPreconnected.image q
      (hqc.mono hsub)
  · have hm : q b ∈ q '' (Metric.ball b ε ∩ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) :=
      ⟨b, ⟨Metric.mem_ball_self hε, hb⟩, rfl⟩
    rw [← hTeq] at hm
    exact hm.1
  · rw [← hqI]
    rintro _ ⟨hyT, z, hzo, rfl⟩
    have hzΔ : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) :=
      openSimplex_stdVertices_subset_stdSimplex hzo
    have hm : q z ∈ T ∩ q '' Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) := ⟨hyT, z, hzΔ, rfl⟩
    rw [hTeq] at hm
    obtain ⟨w, ⟨hwr, hwΔ⟩, hwz⟩ := hm
    have hwz' : w = z := hqi hwΔ hzΔ hwz
    rw [hwz'] at hwr
    exact ⟨z, ⟨hwr, hzo⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
