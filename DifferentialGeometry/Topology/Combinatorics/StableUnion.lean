/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Lattice.Fold

namespace Set

theorem exists_iUnion_inter_eq_of_eventually_eq {α ι : Type*}
    {S B : ι → Set α} {Q : ℕ → ι → Set α} {U : Set α}
    (hQ : ∀ n i, Q n i ⊆ S i)
    (hevent : ∀ i, ∃ N : ℕ, ∀ n ≥ N, Q n i = B i)
    (hfinite : {i | (S i ∩ U).Nonempty}.Finite) :
    ∃ N : ℕ, ∀ n ≥ N, (⋃ i, Q n i) ∩ U = (⋃ i, B i) ∩ U := by
  classical
  choose cutoff hcutoff using hevent
  have hB (i : ι) : B i ⊆ S i :=
    fun _ hx => hQ (cutoff i) i ((hcutoff i (cutoff i) le_rfl).symm ▸ hx)
  refine ⟨hfinite.toFinset.sup cutoff, ?_⟩
  intro n hn
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    obtain ⟨i, hix⟩ := mem_iUnion.mp hx
    have hi : i ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr ⟨x, hQ n i hix, hxU⟩
    have heq := hcutoff i n ((Finset.le_sup hi).trans hn)
    exact ⟨mem_iUnion.mpr ⟨i, heq ▸ hix⟩, hxU⟩
  · rintro ⟨hx, hxU⟩
    obtain ⟨i, hix⟩ := mem_iUnion.mp hx
    have hi : i ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr ⟨x, hB i hix, hxU⟩
    have heq := hcutoff i n ((Finset.le_sup hi).trans hn)
    exact ⟨mem_iUnion.mpr ⟨i, heq.symm ▸ hix⟩, hxU⟩

end Set
