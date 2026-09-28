/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLSphere_pair_of_spanning_disk {S D : Set E} (hS : IsPLSphere 2 S)
    {g : (Fin 3 → ℝ) → E} (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hSD : S ∩ D = g '' stdSimplexBoundary 2) :
    ∃ D₁ D₂ : Set E, D₁ ∪ D₂ = S ∧ D₁ ∩ D₂ = g '' stdSimplexBoundary 2 ∧
      (∃ f₁ f₂ : (Fin 3 → ℝ) → E,
        IsPLHomeomorphOn f₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
        IsPLHomeomorphOn f₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ ∧
        f₁ '' stdSimplexBoundary 2 = g '' stdSimplexBoundary 2 ∧
        f₂ '' stdSimplexBoundary 2 = g '' stdSimplexBoundary 2) ∧
      IsPLSphere 2 (D₁ ∪ D) ∧ IsPLSphere 2 (D₂ ∪ D) ∧
      (D₁ ∪ D) ∩ (D₂ ∪ D) = D ∧
      ((D₁ ∪ D) ∪ (D₂ ∪ D)) \ (D \ (g '' stdSimplexBoundary 2)) = S := by
  let J := g '' stdSimplexBoundary 2
  have hJ : IsPLSphere 1 J := hg.isPLSphere_image_stdSimplexBoundary
  have hJS : J ⊆ S := hSD.symm.subset.trans inter_subset_left
  have hJD : J ⊆ D := hSD.symm.subset.trans inter_subset_right
  obtain ⟨D₁, D₂, hunion, hinter, f₁, f₂, hf₁, hf₂, hf₁J, hf₂J⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS hJ hJS
  have hD₁S : D₁ ⊆ S := subset_union_left.trans hunion.subset
  have hD₂S : D₂ ⊆ S := subset_union_right.trans hunion.subset
  have hD₁D : D₁ ∩ D = J := by
    apply Subset.antisymm
    · rintro x ⟨hx₁, hxD⟩
      exact hSD.subset ⟨hD₁S hx₁, hxD⟩
    · intro x hx
      exact ⟨(hinter.symm ▸ hx).1, hJD hx⟩
  have hD₂D : D₂ ∩ D = J := by
    apply Subset.antisymm
    · rintro x ⟨hx₂, hxD⟩
      exact hSD.subset ⟨hD₂S hx₂, hxD⟩
    · intro x hx
      exact ⟨(hinter.symm ▸ hx).2, hJD hx⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨f₁, hf₁⟩
  have hD₂ : IsPLBall 2 D₂ := ⟨f₂, hf₂⟩
  obtain ⟨H₁, hH₁, -⟩ := exists_isPLHomeomorphOn_replace_ball hD₁.isPolyhedron hf₂ hg
    hf₂J rfl hinter hD₁D
  obtain ⟨H₂, hH₂, -⟩ := exists_isPLHomeomorphOn_replace_ball hD₂.isPolyhedron hf₁ hg
    hf₁J rfl ((inter_comm D₂ D₁).trans hinter) hD₂D
  have hS₁ : IsPLSphere 2 (D₁ ∪ D) :=
    (hunion.symm ▸ hS).of_isPLHomeomorphOn hH₁
  have hS₂ : IsPLSphere 2 (D₂ ∪ D) :=
    (((union_comm D₂ D₁).trans hunion).symm ▸ hS).of_isPLHomeomorphOn hH₂
  refine ⟨D₁, D₂, hunion, hinter, ⟨f₁, f₂, hf₁, hf₂, hf₁J, hf₂J⟩, hS₁, hS₂, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx₁ | hxD, hx₂ | hxD⟩
      · exact hJD (hinter ▸ ⟨hx₁, hx₂⟩)
      · exact hxD
      · exact hxD
      · exact hxD
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩
  · have hu : (D₁ ∪ D) ∪ (D₂ ∪ D) = S ∪ D := by
      rw [← hunion]
      ext x
      simp only [mem_union]
      tauto
    rw [hu]
    ext x
    constructor
    · rintro ⟨hxS | hxD, hnot⟩
      · exact hxS
      · exact hJS (by by_contra hxJ; exact hnot ⟨hxD, hxJ⟩)
    · intro hxS
      exact ⟨Or.inl hxS, fun hx => hx.2 (hSD ▸ ⟨hxS, hx.1⟩)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
