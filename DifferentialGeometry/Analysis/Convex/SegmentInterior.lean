/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Convex.Topology

open Set

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

theorem Convex.openSegment_subset_interior_or_disjoint {C : Set E} (hC : Convex 𝕜 C)
    {p q : E} (hp : p ∈ C) (hq : q ∈ C) :
    openSegment 𝕜 p q ⊆ interior C ∨ Disjoint (openSegment 𝕜 p q) (interior C) := by
  by_cases hmeet : (openSegment 𝕜 p q ∩ interior C).Nonempty
  · obtain ⟨z, hz, hzC⟩ := hmeet
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t, -, rfl⟩ := hz
    exact Or.inl ((openSegment_subset_union p q ⟨t, rfl⟩).trans
      (insert_subset_iff.mpr ⟨hzC, union_subset
        (hC.openSegment_self_interior_subset_interior hp hzC)
        (hC.openSegment_interior_self_subset_interior hzC hq)⟩))
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))
