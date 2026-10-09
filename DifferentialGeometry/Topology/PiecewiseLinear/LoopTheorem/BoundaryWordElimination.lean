/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Tactic.Group
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskBoundaryWord

namespace DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordElimination

variable {G : Type*} [Group G]

theorem boundaryWord_caseThree (σ τ ν φ : G) :
    σ * τ * ν * φ =
      σ * ν⁻¹ * ((σ * φ)⁻¹ * (σ * φ * ν * τ * (σ * ν⁻¹)⁻¹) * (σ * φ)) := by
  group

theorem boundaryWord_caseFour (σ τ ν φ : G) :
    σ * τ * ν * φ =
      σ * ν * (φ⁻¹ * ((σ * τ⁻¹ * ν * φ⁻¹)⁻¹ * (σ * ν)) * φ) := by
  group

theorem boundaryWord_mem_of_caseThree_mem {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h₁ : σ * ν⁻¹ ∈ N) (h₂ : σ * φ * ν * τ ∈ N) : σ * τ * ν * φ ∈ N := by
  rw [boundaryWord_caseThree]
  exact N.mul_mem h₁ (‹N.Normal›.conj_mem' _ (N.mul_mem h₂ (N.inv_mem h₁)) (σ * φ))

theorem boundaryWord_mem_of_caseFour_mem {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h₁ : σ * ν ∈ N) (h₂ : σ * τ⁻¹ * ν * φ⁻¹ ∈ N) : σ * τ * ν * φ ∈ N := by
  rw [boundaryWord_caseFour]
  exact N.mul_mem h₁ (‹N.Normal›.conj_mem' _ (N.mul_mem (N.inv_mem h₂) h₁) φ)

theorem boundaryWord_mem_normalClosure_caseThree (σ τ ν φ : G) :
    σ * τ * ν * φ ∈ Subgroup.normalClosure {σ * ν⁻¹, σ * φ * ν * τ} :=
  boundaryWord_mem_of_caseThree_mem (Subgroup.subset_normalClosure (by simp))
    (Subgroup.subset_normalClosure (by simp))

theorem boundaryWord_mem_normalClosure_caseFour (σ τ ν φ : G) :
    σ * τ * ν * φ ∈ Subgroup.normalClosure {σ * ν, σ * τ⁻¹ * ν * φ⁻¹} :=
  boundaryWord_mem_of_caseFour_mem (Subgroup.subset_normalClosure (by simp))
    (Subgroup.subset_normalClosure (by simp))

theorem notMem_or_notMem_of_caseThree {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h : σ * τ * ν * φ ∉ N) : σ * ν⁻¹ ∉ N ∨ σ * φ * ν * τ ∉ N := by
  by_cases h₁ : σ * ν⁻¹ ∈ N
  · exact Or.inr fun h₂ => h (boundaryWord_mem_of_caseThree_mem h₁ h₂)
  · exact Or.inl h₁

theorem notMem_or_notMem_of_caseFour {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h : σ * τ * ν * φ ∉ N) : σ * ν ∉ N ∨ σ * τ⁻¹ * ν * φ⁻¹ ∉ N := by
  by_cases h₁ : σ * ν ∈ N
  · exact Or.inr fun h₂ => h (boundaryWord_mem_of_caseFour_mem h₁ h₂)
  · exact Or.inl h₁

theorem exists_descends_and_notMem {α : Type*} {N : Subgroup G} {w : G} (descends : α → Prop)
    (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁) (hd₂ : descends c₂)
    (helim : word c₁ ∈ N → word c₂ ∈ N → w ∈ N) (hw : w ∉ N) :
    ∃ c, descends c ∧ word c ∉ N := by
  by_cases h₁ : word c₁ ∈ N
  · exact ⟨c₂, hd₂, fun h₂ => hw (helim h₁ h₂)⟩
  · exact ⟨c₁, hd₁, h₁⟩

theorem exists_complexity_lt_and_notMem {α : Type*} {N : Subgroup G} {w : G}
    (complexity : α → ℕ) (n : ℕ) (word : α → G) (c₁ c₂ : α) (hd₁ : complexity c₁ < n)
    (hd₂ : complexity c₂ < n) (helim : word c₁ ∈ N → word c₂ ∈ N → w ∈ N) (hw : w ∉ N) :
    ∃ c, complexity c < n ∧ word c ∉ N :=
  exists_descends_and_notMem (fun c => complexity c < n) word c₁ c₂ hd₁ hd₂ helim hw

theorem exists_descends_and_notMem_caseThree {α : Type*} {N : Subgroup G} [N.Normal]
    {σ τ ν φ : G} (descends : α → Prop) (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁)
    (hd₂ : descends c₂) (hw₁ : word c₁ = σ * ν⁻¹) (hw₂ : word c₂ = σ * φ * ν * τ)
    (hw : σ * τ * ν * φ ∉ N) :
    ∃ c, descends c ∧ word c ∉ N :=
  exists_descends_and_notMem descends word c₁ c₂ hd₁ hd₂
    (fun h₁ h₂ => boundaryWord_mem_of_caseThree_mem (hw₁ ▸ h₁) (hw₂ ▸ h₂)) hw

theorem exists_descends_and_notMem_caseFour {α : Type*} {N : Subgroup G} [N.Normal]
    {σ τ ν φ : G} (descends : α → Prop) (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁)
    (hd₂ : descends c₂) (hw₁ : word c₁ = σ * ν) (hw₂ : word c₂ = σ * τ⁻¹ * ν * φ⁻¹)
    (hw : σ * τ * ν * φ ∉ N) :
    ∃ c, descends c ∧ word c ∉ N :=
  exists_descends_and_notMem descends word c₁ c₂ hd₁ hd₂
    (fun h₁ h₂ => boundaryWord_mem_of_caseFour_mem (hw₁ ▸ h₁) (hw₂ ▸ h₂)) hw

theorem not_conjugacyClassMeets_or_of_caseThree {N : Subgroup G} [N.Normal] (σ τ ν φ : G)
    (h : ¬conjugacyClassMeets (ConjClasses.mk (σ * τ * ν * φ)) N) :
    ¬conjugacyClassMeets (ConjClasses.mk (σ * ν⁻¹)) N ∨
      ¬conjugacyClassMeets (ConjClasses.mk (σ * φ * ν * τ)) N := by
  have hmk : ∀ g : G, conjugacyClassMeets (ConjClasses.mk g) N ↔ g ∈ N := fun g =>
    NormalSystem.conjugacyClassMeets_mk_iff_mem g N
  rcases notMem_or_notMem_of_caseThree (fun hm => h ((hmk _).mpr hm)) with h₁ | h₂
  · exact Or.inl fun hc => h₁ ((hmk _).mp hc)
  · exact Or.inr fun hc => h₂ ((hmk _).mp hc)

theorem not_conjugacyClassMeets_or_of_caseFour {N : Subgroup G} [N.Normal] (σ τ ν φ : G)
    (h : ¬conjugacyClassMeets (ConjClasses.mk (σ * τ * ν * φ)) N) :
    ¬conjugacyClassMeets (ConjClasses.mk (σ * ν)) N ∨
      ¬conjugacyClassMeets (ConjClasses.mk (σ * τ⁻¹ * ν * φ⁻¹)) N := by
  have hmk : ∀ g : G, conjugacyClassMeets (ConjClasses.mk g) N ↔ g ∈ N := fun g =>
    NormalSystem.conjugacyClassMeets_mk_iff_mem g N
  rcases notMem_or_notMem_of_caseFour (fun hm => h ((hmk _).mpr hm)) with h₁ | h₂
  · exact Or.inl fun hc => h₁ ((hmk _).mp hc)
  · exact Or.inr fun hc => h₂ ((hmk _).mp hc)

theorem exists_descends_and_not_conjugacyClassMeets {α : Type*} {N : Subgroup G} [N.Normal]
    {w : G} (descends : α → Prop) (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁)
    (hd₂ : descends c₂) (helim : word c₁ ∈ N → word c₂ ∈ N → w ∈ N)
    (hw : ¬conjugacyClassMeets (ConjClasses.mk w) N) :
    ∃ c, descends c ∧ ¬conjugacyClassMeets (ConjClasses.mk (word c)) N := by
  have hmk : ∀ g : G, conjugacyClassMeets (ConjClasses.mk g) N ↔ g ∈ N := fun g =>
    NormalSystem.conjugacyClassMeets_mk_iff_mem g N
  obtain ⟨c, hc, hcn⟩ := exists_descends_and_notMem descends word c₁ c₂ hd₁ hd₂ helim
    (fun hm => hw ((hmk w).mpr hm))
  exact ⟨c, hc, fun hmeet => hcn ((hmk (word c)).mp hmeet)⟩

end DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordElimination
