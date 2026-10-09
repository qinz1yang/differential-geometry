/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.exists_eq_singleton {S B : Set M} (h : IsPLCellOn 0 S B) :
    ∃ x : M, S = {x} := by
  obtain ⟨P, r, u, hr, -, hS, -⟩ := h
  refine ⟨u (r (fun _ => 1)), ?_⟩
  have hsimplex : Convexity.StdSimplex.coordinateSet ℝ (Fin 1) =
      {fun _ : Fin 1 => (1 : ℝ)} := by
    ext x
    constructor
    · intro hx
      rw [mem_singleton_iff]
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [Fin.sum_univ_one] using hx.2
    · intro hx
      rw [mem_singleton_iff] at hx
      subst x
      exact ⟨fun i => by simp, by simp⟩
  rw [hS, ← hr.bijOn.image_eq, hsimplex, image_singleton, image_singleton]

theorem IsPLCellOn.exists_boundary_eq_pair {S B : Set M} (h : IsPLCellOn 1 S B) :
    ∃ x y : M, x ≠ y ∧ B = {x, y} := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := h
  have hleft : (![1, 0] : Fin 2 → ℝ) ∈ stdSimplexBoundary 1 := by
    rw [stdSimplexBoundary_one_eq_pair]
    exact mem_insert _ _
  have hright : (![0, 1] : Fin 2 → ℝ) ∈ stdSimplexBoundary 1 := by
    rw [stdSimplexBoundary_one_eq_pair]
    exact mem_insert_of_mem _ (mem_singleton _)
  refine ⟨u (r ![1, 0]), u (r ![0, 1]), ?_, ?_⟩
  · intro heq
    have hvec := hr.bijOn.injOn hleft.1 hright.1
      (hu.injOn (hr.bijOn.mapsTo hleft.1) (hr.bijOn.mapsTo hright.1) heq)
    have hzero := congrFun hvec 0
    norm_num at hzero
  · rw [hB, stdSimplexBoundary_one_eq_pair, image_pair, image_pair]

theorem IsPLCellOn.eq_or_eq_of_subset_boundary {S B P P₁ P₂ D D₁ D₂ : Set M}
    (hS : IsPLCellOn 1 S B) (hP : IsPLCellOn 0 P D)
    (hP₁ : IsPLCellOn 0 P₁ D₁) (hP₂ : IsPLCellOn 0 P₂ D₂)
    (hPB : P ⊆ B) (hP₁B : P₁ ⊆ B) (hP₂B : P₂ ⊆ B) (hne : P₁ ≠ P₂) :
    P = P₁ ∨ P = P₂ := by
  obtain ⟨z, rfl⟩ := hP.exists_eq_singleton
  obtain ⟨z₁, rfl⟩ := hP₁.exists_eq_singleton
  obtain ⟨z₂, rfl⟩ := hP₂.exists_eq_singleton
  obtain ⟨x, y, -, rfl⟩ := hS.exists_boundary_eq_pair
  simp only [singleton_subset_iff, mem_insert_iff, mem_singleton_iff] at hPB hP₁B hP₂B
  have hz₁₂ : z₁ ≠ z₂ := fun h => hne (congrArg singleton h)
  rcases hPB with rfl | rfl <;> rcases hP₁B with rfl | rfl <;>
    rcases hP₂B with rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact (hz₁₂ rfl).elim

end DifferentialGeometry.Topology.PiecewiseLinear
