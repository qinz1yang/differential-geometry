/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalCellWithInterior.isOpenTopologicalCell
    {n : ℕ} {X : Type*} [TopologicalSpace X] {C I : Set X}
    (h : IsTopologicalCellWithInterior n C I) : IsOpenTopologicalCell n I := by
  obtain ⟨φ, hI⟩ := h
  let B : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {q | ‖(q : EuclideanSpace ℝ (Fin n))‖ < 1}
  have hBI : Subtype.val '' (φ '' B) = I := by
    simpa only [B] using hI.symm
  have hBB : Subtype.val '' B = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    ext x
    simp only [mem_image, mem_ball, dist_zero_right, B, mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hx
      exact ⟨⟨x, by simpa [Metric.mem_closedBall, dist_zero_right] using hx.le⟩,
        hx, rfl⟩
  let eI : B ≃ₜ I :=
    (φ.image B).trans ((Topology.IsEmbedding.subtypeVal.homeomorphImage (φ '' B)).trans
      (Homeomorph.setCongr hBI))
  let eB : B ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage B).trans (Homeomorph.setCongr hBB)
  exact ⟨eI.symm.trans eB⟩

theorem IsTopologicalCellWithInterior.isTopologicalSphere_boundary
    {X : Type*} [TopologicalSpace X] {C I : Set X}
    (h : IsTopologicalCellWithInterior 2 C I) : IsTopologicalSphere 1 (C \ I) := by
  obtain ⟨φ, hI⟩ := h
  let S : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    {q | ‖(q : EuclideanSpace ℝ (Fin 2))‖ = 1}
  have hSC : Subtype.val '' (φ '' S) = C \ I := by
    ext x
    constructor
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨(φ q).property, ?_⟩
      rw [hI]
      rintro ⟨z, ⟨p, hp, rfl⟩, heq⟩
      have hpq : p = q := φ.injective (Subtype.ext heq)
      exact (ne_of_lt hp) (hpq ▸ hq)
    · rintro ⟨hxC, hxI⟩
      let q := φ.symm ⟨x, hxC⟩
      have hqnot : ¬ ‖(q : EuclideanSpace ℝ (Fin 2))‖ < 1 := by
        intro hq
        apply hxI
        rw [hI]
        exact ⟨φ q, ⟨q, hq, rfl⟩, by simp [q]⟩
      have hqle : ‖(q : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := by
        simpa only [dist_zero_right] using (Metric.mem_closedBall.mp q.property)
      have hqeq : ‖(q : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
        le_antisymm hqle (le_of_not_gt hqnot)
      exact ⟨φ q, ⟨q, hqeq, rfl⟩, by simp [q]⟩
  have hSS : Subtype.val '' S = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      change ‖(q : EuclideanSpace ℝ (Fin 2))‖ = 1 at hq
      simpa [Metric.mem_sphere, dist_zero_right] using hq
    · intro hx
      have hxnorm : ‖x‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hx
      exact ⟨⟨x, by simpa [Metric.mem_closedBall, dist_zero_right] using hxnorm.le⟩,
        hxnorm, rfl⟩
  let eR : S ≃ₜ ↥(C \ I) :=
    (φ.image S).trans ((Topology.IsEmbedding.subtypeVal.homeomorphImage (φ '' S)).trans
      (Homeomorph.setCongr hSC))
  let eS : S ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage S).trans (Homeomorph.setCongr hSS)
  exact ⟨eR.symm.trans eS⟩

end DifferentialGeometry.Topology.PiecewiseLinear
