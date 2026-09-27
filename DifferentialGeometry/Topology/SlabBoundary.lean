/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Tauto

open Set

namespace DifferentialGeometry.Topology

theorem frontier_inter_of_isClosed {X : Type*} [TopologicalSpace X] {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q) :
    frontier (P ∩ Q) = (frontier P ∩ Q) ∪ (P ∩ frontier Q) := by
  ext x
  simp only [frontier, hP.closure_eq, hQ.closure_eq, (hP.inter hQ).closure_eq,
    interior_inter, mem_sdiff, mem_inter_iff, mem_union]
  tauto

theorem frontier_inter_preimage_Icc_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsClosed P) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {a b : ℝ} (hab : a ≤ b) :
    frontier (P ∩ ℓ ⁻¹' Icc a b) = (frontier P ∩ ℓ ⁻¹' Icc a b) ∪ (P ∩ ℓ ⁻¹' {a, b}) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) h
  have hopen : IsOpenMap ℓ := ℓ.toLinearMap.isOpenMap_of_finiteDimensional (LinearMap.surjective
      hlinear)
  rw [frontier_inter_of_isClosed hP (isClosed_Icc.preimage ℓ.continuous),
    ← hopen.preimage_frontier_eq_frontier_preimage ℓ.continuous, frontier_Icc hab]

theorem frontier_inter_preimage_Iic_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsClosed P) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (a : ℝ) :
    frontier (P ∩ ℓ ⁻¹' Iic a) = (frontier P ∩ ℓ ⁻¹' Iic a) ∪ (P ∩ {x | ℓ x = a}) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) h
  have hopen : IsOpenMap ℓ := ℓ.toLinearMap.isOpenMap_of_finiteDimensional (LinearMap.surjective
      hlinear)
  rw [frontier_inter_of_isClosed hP (isClosed_Iic.preimage ℓ.continuous),
    ← hopen.preimage_frontier_eq_frontier_preimage ℓ.continuous, frontier_Iic]
  ext x
  simp only [mem_union, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]

theorem frontier_inter_preimage_Ici_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsClosed P) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (a : ℝ) :
    frontier (P ∩ ℓ ⁻¹' Ici a) = (frontier P ∩ ℓ ⁻¹' Ici a) ∪ (P ∩ {x | ℓ x = a}) := by
  have h := frontier_inter_preimage_Iic_of_ne_zero hP (-ℓ) (neg_ne_zero.mpr hℓ) (-a)
  have hset : (-ℓ) ⁻¹' Iic (-a) = ℓ ⁻¹' Ici a := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_apply, neg_le_neg_iff]
  simpa only [hset, neg_apply, neg_inj] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frontier_sublevel_inter_frontier_slab {P : Set E} (hP : IsClosed P)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    frontier (P ∩ ℓ ⁻¹' Iic a) ∩ frontier (P ∩ ℓ ⁻¹' Icc a b) = P ∩ {x | ℓ x = a} := by
  rw [frontier_inter_preimage_Iic_of_ne_zero hP ℓ hℓ,
    frontier_inter_preimage_Icc_of_ne_zero hP ℓ hℓ hab]
  ext x
  have hfront : x ∈ frontier P → x ∈ P := fun hx => hP.frontier_subset hx
  simp only [mem_inter_iff, mem_union, mem_preimage, mem_Iic, mem_Icc,
    mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hl, hr⟩
    have hxP : x ∈ P := hl.elim (fun hx => hfront hx.1) (fun hx => hx.1)
    have hle : ℓ x ≤ a := hl.elim (fun hx => hx.2) (fun hx => hx.2.le)
    have hge : a ≤ ℓ x := hr.elim (fun hx => hx.2.1) (fun hx =>
      hx.2.elim (fun heq => heq.ge) (fun heq => heq.symm ▸ hab))
    exact ⟨hxP, le_antisymm hle hge⟩
  · rintro ⟨hxP, hxa⟩
    exact ⟨Or.inr ⟨hxP, hxa⟩, Or.inr ⟨hxP, Or.inl hxa⟩⟩

theorem frontier_sublevel_slab_union_sdiff {P : Set E} (hP : IsClosed P)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {a b : ℝ} (hab : a < b) :
    (frontier (P ∩ ℓ ⁻¹' Iic a) ∪ frontier (P ∩ ℓ ⁻¹' Icc a b)) \
        ((P ∩ {x | ℓ x = a}) \ (frontier P ∩ {x | ℓ x = a})) =
      frontier (P ∩ ℓ ⁻¹' Iic b) := by
  rw [frontier_inter_preimage_Iic_of_ne_zero hP ℓ hℓ,
    frontier_inter_preimage_Icc_of_ne_zero hP ℓ hℓ hab.le,
    frontier_inter_preimage_Iic_of_ne_zero hP ℓ hℓ]
  ext x
  simp only [mem_sdiff, mem_inter_iff, mem_union, mem_preimage, mem_Iic, mem_Icc,
    mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨h, hkeep⟩
    have h_at_a (hxP : x ∈ P) (hxa : ℓ x = a) : x ∈ frontier P := by
      by_contra hnot
      exact hkeep ⟨⟨hxP, hxa⟩, fun h => hnot h.1⟩
    rcases h with (h | h) | (h | h)
    · exact Or.inl ⟨h.1, h.2.trans hab.le⟩
    · exact Or.inl ⟨h_at_a h.1 h.2, h.2.symm ▸ hab.le⟩
    · exact Or.inl ⟨h.1, h.2.2⟩
    · rcases h.2 with ha | hb
      · exact Or.inl ⟨h_at_a h.1 ha, ha.symm ▸ hab.le⟩
      · exact Or.inr ⟨h.1, hb⟩
  · rintro (h | h)
    · refine ⟨?_, fun he => he.2 ⟨h.1, he.1.2⟩⟩
      rcases le_total (ℓ x) a with hxa | hax
      · exact Or.inl (Or.inl ⟨h.1, hxa⟩)
      · exact Or.inr (Or.inl ⟨h.1, hax, h.2⟩)
    · refine ⟨Or.inr (Or.inr ⟨h.1, Or.inr h.2⟩), ?_⟩
      rintro ⟨⟨-, hxa⟩, -⟩
      exact hab.ne (hxa.symm.trans h.2)

theorem frontier_sublevel_inter_frontier_superlevel {P : Set E} (hP : IsClosed P)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (a : ℝ) :
    frontier (P ∩ ℓ ⁻¹' Iic a) ∩ frontier (P ∩ ℓ ⁻¹' Ici a) = P ∩ {x | ℓ x = a} := by
  rw [frontier_inter_preimage_Iic_of_ne_zero hP ℓ hℓ,
    frontier_inter_preimage_Ici_of_ne_zero hP ℓ hℓ]
  ext x
  have hfront : x ∈ frontier P → x ∈ P := fun hx => hP.frontier_subset hx
  simp only [mem_inter_iff, mem_union, mem_preimage, mem_Iic, mem_Ici, mem_ofPred_eq]
  constructor
  · rintro ⟨hl, hr⟩
    have hxP : x ∈ P := hl.elim (fun hx => hfront hx.1) (fun hx => hx.1)
    have hle : ℓ x ≤ a := hl.elim (fun hx => hx.2) (fun hx => hx.2.le)
    have hge : a ≤ ℓ x := hr.elim (fun hx => hx.2) (fun hx => hx.2.ge)
    exact ⟨hxP, le_antisymm hle hge⟩
  · rintro ⟨hxP, hxa⟩
    exact ⟨Or.inr ⟨hxP, hxa⟩, Or.inr ⟨hxP, hxa⟩⟩

theorem frontier_sublevel_union_superlevel_sdiff {P : Set E} (hP : IsClosed P)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (a : ℝ) :
    (frontier (P ∩ ℓ ⁻¹' Iic a) ∪ frontier (P ∩ ℓ ⁻¹' Ici a)) \
        ((P ∩ {x | ℓ x = a}) \ (frontier P ∩ {x | ℓ x = a})) = frontier P := by
  rw [frontier_inter_preimage_Iic_of_ne_zero hP ℓ hℓ,
    frontier_inter_preimage_Ici_of_ne_zero hP ℓ hℓ]
  ext x
  have hfront : x ∈ frontier P → x ∈ P := fun hx => hP.frontier_subset hx
  have horder : ℓ x ≤ a ∨ a ≤ ℓ x := le_total _ _
  simp only [mem_sdiff, mem_inter_iff, mem_union, mem_preimage, mem_Iic, mem_Ici, mem_ofPred_eq]
  tauto

end DifferentialGeometry.Topology
