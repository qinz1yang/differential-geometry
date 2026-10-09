/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTetraCircle
import DifferentialGeometry.Topology.PiecewiseLinear.TwoBallPocket

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_isPLBall_frontier_eq_of_four_disks {B₁ B₂ : Set E3} (hB₁ : IsPLBall 3 B₁)
    (hB₂ : IsPLBall 3 B₂) {H D : Fin 4 → Set E3}
    {rH qD : Fin 4 → (Fin 3 → ℝ) → E3} {γ₁ γ₂ : Fin 4 → ℝ → E3}
    (hrH : ∀ k, IsPLHomeomorphOn (rH k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (H k))
    (hHdisj : Pairwise fun k l => Disjoint (H k) (H l)) (h12 : B₁ ∩ B₂ = ⋃ k, H k)
    (hH₁ : ∀ k, H k ⊆ frontier B₁) (hH₂ : ∀ k, H k ⊆ frontier B₂)
    (hHint : ∀ k, H k \ rH k '' stdSimplexBoundary 2 ⊆ interior (B₁ ∪ B₂))
    (hqD : ∀ k, IsPLHomeomorphOn (qD k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D k))
    (hDdisj : Pairwise fun k l => Disjoint (D k) (D l))
    (hγ₁ : ∀ k, IsPLHomeomorphOn (γ₁ k) (Icc 0 1) (D k ∩ B₁))
    (hγ₂ : ∀ k, IsPLHomeomorphOn (γ₂ k) (Icc 0 1) (D k ∩ B₂))
    (hDb : ∀ k, qD k '' stdSimplexBoundary 2 = D k ∩ B₁ ∪ D k ∩ B₂)
    (hint₁ : ∀ k, D k ∩ B₁ ∩ (D k ∩ B₂) = {γ₁ k 0, γ₁ k 1})
    (hint₂ : ∀ k, D k ∩ B₁ ∩ (D k ∩ B₂) = {γ₂ k 0, γ₂ k 1})
    (hDfr₁ : ∀ k, D k ∩ B₁ ⊆ frontier B₁)
    (hDfr₂ : ∀ k, D k ∩ B₂ ⊆ frontier B₂)
    (hout : ∀ k, D k ∩ H k = {γ₁ k 1})
    (hin : ∀ k, D (k + 1) ∩ H k = {γ₁ (k + 1) 0})
    (hfar : ∀ k l, l ≠ k → l + 1 ≠ k → D k ∩ H l = ∅)
    (hbout : ∀ k, γ₁ k 1 ∈ rH k '' stdSimplexBoundary 2)
    (hbin : ∀ k, γ₁ (k + 1) 0 ∈ rH k '' stdSimplexBoundary 2) :
    ∃ R A Ω : Set E3, IsPLBall 3 R ∧ frontier R = A ∪ (⋃ k, D k) ∪ Ω ∧
      A ⊆ frontier B₁ ∧ Ω ⊆ frontier B₂ ∧
      (∃ qA : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn qA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
        ∀ k, D k ∩ B₁ ⊆ qA '' stdSimplexBoundary 2) ∧
      (∃ qΩ : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn qΩ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ω ∧
        ∀ k, D k ∩ B₂ ⊆ qΩ '' stdSimplexBoundary 2) ∧
      Ω ∩ B₁ ⊆ A ∧ A ∩ B₂ ⊆ Ω ∧ Disjoint (interior R) (B₁ ∪ B₂) := by
  have hB₁c := hB₁.isPolyhedron.isClosed
  have hHB₁ : ∀ k, H k ⊆ B₁ := fun k => (hH₁ k).trans hB₁c.frontier_subset
  obtain ⟨X, Y, qX, qY, β, σ, hqX, hqY, hXY, hXYi, hσ, hβb, hXH, hqXb, hqYb⟩ :=
    exists_split_of_four_runs (r := fun k => D k ∩ B₁) hB₁ hrH hH₁ hHdisj hγ₁ hDfr₁
      (fun k l hkl => (hDdisj hkl).mono inter_subset_left inter_subset_left)
      (fun k => by
        rw [← hout k]
        ext z
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hHB₁ k h.2⟩, h.2⟩⟩)
      (fun k => by
        rw [← hin k]
        ext z
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hHB₁ k h.2⟩, h.2⟩⟩)
      (fun k l h1 h2 =>
        subset_eq_empty (inter_subset_inter_left _ inter_subset_left) (hfar k l h1 h2))
      hbout hbin
  obtain ⟨R, A, Ω, qA, qΩ, hR, hRf, hAXY, hqA, hqAb, hqΩ, hqΩb, hΩB₂, hΩB₁, hdisj⟩ :=
    exists_isPLBall_frontier_eq_of_two_balls hB₁ hB₂ hrH hHdisj h12 hH₁ hH₂ hHint
      hqD hDdisj hγ₁ hγ₂ (fun _ => rfl) (fun _ => rfl) hDb hint₁ hint₂ hDfr₁ hDfr₂
      hqX hqY hXY hXYi hσ hβb hXH hqXb hqYb
  have hAB₁ : A ⊆ frontier B₁ := by
    rw [← hXY]
    rcases hAXY with rfl | rfl
    · exact subset_union_left.trans subset_union_left
    · exact subset_union_right.trans subset_union_left
  refine ⟨R, A, Ω, hR, hRf, hAB₁, hΩB₂, ⟨qA, hqA, fun k => ?_⟩,
    ⟨qΩ, hqΩ, fun k => ?_⟩, ?_, ?_, hdisj⟩
  · rw [hqAb]
    exact (subset_iUnion (fun k => D k ∩ B₁) k).trans subset_union_left
  · rw [hqΩb]
    exact (subset_iUnion (fun k => D k ∩ B₂) k).trans subset_union_left
  · rw [hΩB₁]
    exact iUnion_subset fun k => inter_subset_left
  · rintro z ⟨hzA, hz2⟩
    have hz12 : z ∈ B₁ ∩ B₂ := ⟨hB₁c.frontier_subset (hAB₁ hzA), hz2⟩
    rw [h12] at hz12
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz12
    have hzb : z ∈ qΩ '' stdSimplexBoundary 2 := by
      rw [hqΩb]
      exact Or.inr (mem_iUnion.mpr ⟨k, hzA, hk⟩)
    rw [← hqΩ.image_eq]
    exact image_mono (fun x hx => hx.1) hzb

end DifferentialGeometry.Topology.PiecewiseLinear
