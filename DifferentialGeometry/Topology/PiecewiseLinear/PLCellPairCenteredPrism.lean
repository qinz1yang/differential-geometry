/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallPairCenteredPrism
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_centered_prism_of_cell_pair_in_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {C₁ B₁ C₂ B₂ D DB : Set M}
    (h₁ : IsPLCellOn 3 C₁ B₁) (h₂ : IsPLCellOn 3 C₂ B₂)
    (hD : IsPLCellOn 2 D DB)
    (hmeet : C₁ ∩ C₂ = D) (hD₁ : D ⊆ B₁) (hD₂ : D ⊆ B₂)
    {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M)
    (hC₁c : C₁ ⊆ c.source) (hC₂c : C₂ ⊆ c.source) :
    ∃ (r : (Fin 3 → ℝ) → E3) (ρ : (Fin 3 → ℝ) × ℝ → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (c '' D) ∧
      IsPLHomeomorphOn ρ
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) (c '' (C₁ ∪ C₂)) ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ρ (x, 0) = r x) ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = c '' C₁ ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = c '' C₂ := by
  have hDc : D ⊆ c.source := by
    rw [← hmeet]
    exact inter_subset_left.trans hC₁c
  obtain ⟨hC₁, hB₁⟩ := h₁.isPLBall_image_chart hc hC₁c
  obtain ⟨hC₂, hB₂⟩ := h₂.isPLBall_image_chart hc hC₂c
  obtain ⟨r, hr, -⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hD₁' : c '' D ⊆ frontier (c '' C₁) := by
    rw [← hB₁]
    exact image_mono hD₁
  have hD₂' : c '' D ⊆ frontier (c '' C₂) := by
    rw [← hB₂]
    exact image_mono hD₂
  have hcmeet : c '' C₁ ∩ c '' C₂ = c '' D := by
    rw [← c.injOn.image_inter hC₁c hC₂c, hmeet]
  obtain ⟨ρ, hρ, hρzero, hρ₁, hρ₂⟩ :=
    exists_centered_prism_of_ball_pair_inter_disk hC₁ hC₂ hr hcmeet hD₁' hD₂'
  refine ⟨r, ρ, hr, ?_, hρzero, hρ₁, hρ₂⟩
  rwa [image_union]

end DifferentialGeometry.Topology.PiecewiseLinear
