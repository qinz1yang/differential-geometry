/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcSplit
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.exists_arcs_in_chart_of_boundary_partition {D DB A B : Set M}
    (hD : IsPLCellOn 2 D DB) (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = DB)
    {p q : M} (hpq : p ≠ q) (hcap : A ∩ B = {p, q})
    (hAne : (A \ {p, q}).Nonempty) (hBne : (B \ {p, q}).Nonempty)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hDc : D ⊆ c.source) :
    (∃ γ₁ : ℝ → EuclideanSpace ℝ (Fin 3), IsPLHomeomorphOn γ₁ (Icc 0 1) (c '' A) ∧
      γ₁ 0 = c p ∧ γ₁ 1 = c q) ∧
    ∃ γ₂ : ℝ → EuclideanSpace ℝ (Fin 3), IsPLHomeomorphOn γ₂ (Icc 0 1) (c '' B) ∧
      γ₂ 0 = c p ∧ γ₂ 1 = c q := by
  have hAD : A ⊆ D := subset_union_left.trans (hAB.subset.trans hD.boundary_subset)
  have hBD : B ⊆ D := subset_union_right.trans (hAB.subset.trans hD.boundary_subset)
  have hAc : A ⊆ c.source := hAD.trans hDc
  have hBc : B ⊆ c.source := hBD.trans hDc
  have hpA : p ∈ A := (hcap.symm.subset (mem_insert p {q})).1
  have hqA : q ∈ A := (hcap.symm.subset (mem_insert_of_mem p (mem_singleton q))).1
  have hpc := hAc hpA
  have hqc := hAc hqA
  have hpqi : c p ≠ c q := fun h => hpq (c.injOn hpc hqc h)
  have hAi : IsClosed (c '' A) :=
    ((hD.isCompact.of_isClosed_subset hA hAD).image_of_continuousOn
      (c.continuousOn.mono hAc)).isClosed
  have hBi : IsClosed (c '' B) :=
    ((hD.isCompact.of_isClosed_subset hB hBD).image_of_continuousOn
      (c.continuousOn.mono hBc)).isClosed
  obtain ⟨r, hr, hrb⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hcircle : IsPLSphere 1 (c '' DB) := by
    rw [hrb]
    exact ⟨r, hr.restrict isPolyhedron_stdSimplexBoundary_two fun x hx => hx.1⟩
  have hABi : c '' A ∪ c '' B = c '' DB := by rw [← image_union, hAB]
  have hcapi : c '' A ∩ c '' B = {c p, c q} := by
    have hi : c '' (A ∩ B) = c '' A ∩ c '' B := c.injOn.image_inter hAc hBc
    rw [← hi, hcap, image_pair]
  have hne : ∀ T : Set M, T ⊆ c.source → (T \ {p, q}).Nonempty →
      (c '' T \ {c p, c q}).Nonempty := by
    rintro T hTc ⟨z, hzT, hzne⟩
    refine ⟨c z, mem_image_of_mem c hzT, fun hz => hzne ?_⟩
    rcases hz with hz | hz
    · exact Or.inl (c.injOn (hTc hzT) hpc hz)
    · exact Or.inr (c.injOn (hTc hzT) hqc (mem_singleton_iff.mp hz))
  refine ⟨hcircle.exists_isPLHomeomorphOn_Icc_of_union_eq_of_inter_eq_pair hAi hBi hABi hpqi
    hcapi (hne A hAc hAne) (hne B hBc hBne), ?_⟩
  rw [union_comm] at hABi
  rw [inter_comm] at hcapi
  exact hcircle.exists_isPLHomeomorphOn_Icc_of_union_eq_of_inter_eq_pair hBi hAi hABi hpqi
    hcapi (hne B hBc hBne) (hne A hAc hAne)

end DifferentialGeometry.Topology.PiecewiseLinear
