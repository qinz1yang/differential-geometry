/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Logic.Relation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Λ M : Type*} {step : Λ → Λ → Prop} {dim : Λ → ℕ} {tc tcBd : Λ → Set M}

theorem eq_or_dim_lt_of_reflTransGen (hdim : ∀ m l, step m l → dim m < dim l) {m l : Λ}
    (h : Relation.ReflTransGen step m l) : m = l ∨ dim m < dim l := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | hlt
    · exact Or.inr (hdim _ _ hbc)
    · exact Or.inr (hlt.trans (hdim _ _ hbc))

theorem subset_of_reflTransGen_of_step (hstep : ∀ m l, step m l → tc m ⊆ tcBd l)
    (hsub : ∀ l, tcBd l ⊆ tc l) {m l : Λ} (h : Relation.ReflTransGen step m l) :
    tc m ⊆ tc l := by
  induction h with
  | refl => exact Subset.rfl
  | tail _ hbc ih => exact ih.trans ((hstep _ _ hbc).trans (hsub _))

theorem exists_reflTransGen_mem_sdiff_boundary (hdim : ∀ m l, step m l → dim m < dim l)
    (hbd : ∀ l, tcBd l ⊆ ⋃ m, ⋃ (_ : step m l), tc m) (l : Λ) {y : M} (hy : y ∈ tc l) :
    ∃ k, Relation.ReflTransGen step k l ∧ y ∈ tc k ∧ y ∉ tcBd k := by
  suffices key : ∀ n, ∀ l, dim l = n → y ∈ tc l →
      ∃ k, Relation.ReflTransGen step k l ∧ y ∈ tc k ∧ y ∉ tcBd k from key _ l rfl hy
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl hyl
    by_cases hyb : y ∈ tcBd l
    · obtain ⟨m, hml, hym⟩ := mem_iUnion₂.mp (hbd l hyb)
      obtain ⟨k, hk, hyk, hyk'⟩ := ih (dim m) (hl ▸ hdim m l hml) m rfl hym
      exact ⟨k, hk.tail hml, hyk, hyk'⟩
    · exact ⟨l, Relation.ReflTransGen.refl, hyl, hyb⟩

theorem boundary_eq_and_inter_eq_of_step {F : Λ → Set Λ}
    (hF : ∀ l m, m ∈ F l ↔ Relation.ReflTransGen step m l)
    (hdim : ∀ m l, step m l → dim m < dim l) (hstep : ∀ m l, step m l → tc m ⊆ tcBd l)
    (hbd : ∀ l, tcBd l ⊆ ⋃ m, ⋃ (_ : step m l), tc m) (hsub : ∀ l, tcBd l ⊆ tc l)
    (hmeet : ∀ k k', k ≠ k' → tc k ∩ tc k' ⊆ tcBd k ∪ tcBd k') :
    (∀ l, tcBd l = ⋃ m ∈ F l \ {l}, tc m) ∧ ∀ l m, tc l ∩ tc m = ⋃ k ∈ F l ∩ F m, tc k := by
  refine ⟨fun l => Subset.antisymm (fun y hy => ?_) (iUnion₂_subset fun m hm => ?_),
    fun l m => Subset.antisymm (fun y hy => ?_) (iUnion₂_subset fun k hk => ?_)⟩
  · obtain ⟨m, hml, hym⟩ := mem_iUnion₂.mp (hbd l hy)
    refine mem_iUnion₂.mpr ⟨m, ⟨(hF l m).mpr (Relation.ReflTransGen.single hml),
      fun h => ?_⟩, hym⟩
    rw [mem_singleton_iff] at h
    subst h
    exact lt_irrefl _ (hdim _ _ hml)
  · obtain ⟨hml, hne⟩ := hm
    rcases Relation.ReflTransGen.cases_tail ((hF l m).mp hml) with h | ⟨c, hmc, hcl⟩
    · exact absurd (mem_singleton_iff.mpr h.symm) hne
    · exact (subset_of_reflTransGen_of_step hstep hsub hmc).trans (hstep c l hcl)
  · obtain ⟨k, hkl, hyk, hyk'⟩ := exists_reflTransGen_mem_sdiff_boundary hdim hbd l hy.1
    obtain ⟨k', hkm, hyk'', hyk'''⟩ := exists_reflTransGen_mem_sdiff_boundary hdim hbd m hy.2
    by_cases hkk : k = k'
    · subst hkk
      exact mem_iUnion₂.mpr ⟨k, ⟨(hF l k).mpr hkl, (hF m k).mpr hkm⟩, hyk⟩
    · rcases hmeet k k' hkk ⟨hyk, hyk''⟩ with h | h
      · exact absurd h hyk'
      · exact absurd h hyk'''
  · exact subset_inter (subset_of_reflTransGen_of_step hstep hsub ((hF l k).mp hk.1))
      (subset_of_reflTransGen_of_step hstep hsub ((hF m k).mp hk.2))

end DifferentialGeometry.Topology.PiecewiseLinear
