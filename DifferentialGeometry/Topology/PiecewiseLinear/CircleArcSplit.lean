/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.PLArcChainUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_isPLHomeomorphOn_Icc_of_union_eq_of_inter_eq_pair {S A B : Set E}
    (hS : IsPLSphere 1 S) (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = S) {p q : E}
    (hpq : p ≠ q) (hAB2 : A ∩ B = {p, q}) (hAne : (A \ {p, q}).Nonempty)
    (hBne : (B \ {p, q}).Nonempty) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) A ∧ γ 0 = p ∧ γ 1 = q := by
  have hpqA : ({p, q} : Set E) ⊆ A := by
    rw [← hAB2]
    exact inter_subset_left
  have hpS : p ∈ S := by
    rw [← hAB]
    exact Or.inl (hpqA (mem_insert p {q}))
  have hqS : q ∈ S := by
    rw [← hAB]
    exact Or.inl (hpqA (mem_insert_of_mem p rfl))
  obtain ⟨α, α', a, a', ha, ha', ha0, ha1, ha'0, ha'1, hu, hi⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hpS hqS hpq
  have hpqα : ({p, q} : Set E) ⊆ α := by
    rw [← hi]
    exact inter_subset_left
  have hpqα' : ({p, q} : Set E) ⊆ α' := by
    rw [← hi]
    exact inter_subset_right
  have hO : IsPreconnected (α \ {p, q}) := by
    have h := (ha.isConnected_sdiff_endpoints zero_lt_one).isPreconnected
    rwa [ha0, ha1] at h
  have hO' : IsPreconnected (α' \ {p, q}) := by
    have h := (ha'.isConnected_sdiff_endpoints zero_lt_one).isPreconnected
    rwa [ha'0, ha'1] at h
  have hcover : ∀ T : Set E, T ⊆ S → IsPreconnected (T \ {p, q}) →
      T \ {p, q} ⊆ A ∨ T \ {p, q} ⊆ B := by
    intro T hT hTc
    refine isPreconnected_iff_subset_of_disjoint_closed.mp hTc A B hA hB ?_ ?_
    · intro x hx
      have hxS := hT hx.1
      rw [← hAB] at hxS
      exact hxS
    · rw [hAB2]
      exact disjoint_sdiff_left.inter_eq
  have hSsplit : ∀ x ∈ S, x ∉ ({p, q} : Set E) → x ∈ α \ {p, q} ∨ x ∈ α' \ {p, q} := by
    intro x hx hxpq
    rw [← hu] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, hxpq⟩
    · exact Or.inr ⟨hx, hxpq⟩
  have hαS : α ⊆ S := by
    rw [← hu]
    exact subset_union_left
  have hα'S : α' ⊆ S := by
    rw [← hu]
    exact subset_union_right
  have hsame : ∀ C : Set E, α \ {p, q} ⊆ C → α' \ {p, q} ⊆ C → ∀ x ∈ S, x ∉ ({p, q} : Set E) →
      x ∈ C := by
    intro C h1 h2 x hx hxpq
    rcases hSsplit x hx hxpq with h | h
    · exact h1 h
    · exact h2 h
  have hAS : A ⊆ S := by
    rw [← hAB]
    exact subset_union_left
  have hBS : B ⊆ S := by
    rw [← hAB]
    exact subset_union_right
  have hexact : ∀ (γ : ℝ → E) (C C' : Set E), IsPLHomeomorphOn γ (Icc 0 1) C → γ 0 = p →
      γ 1 = q → ({p, q} : Set E) ⊆ C → C \ {p, q} ⊆ A → C' \ {p, q} ⊆ B →
      (∀ x ∈ S, x ∉ ({p, q} : Set E) → x ∈ C \ {p, q} ∨ x ∈ C' \ {p, q}) →
      ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) A ∧ γ 0 = p ∧ γ 1 = q := by
    intro γ C C' hγ hγ0 hγ1 hpqC hCA hC'B hsplit
    have hCeq : A = C := by
      apply Subset.antisymm
      · intro x hxA
        by_cases hxpq : x ∈ ({p, q} : Set E)
        · exact hpqC hxpq
        · rcases hsplit x (hAS hxA) hxpq with h | h
          · exact h.1
          · exact absurd (hAB2.subset ⟨hxA, hC'B h⟩) hxpq
      · intro x hxC
        by_cases hxpq : x ∈ ({p, q} : Set E)
        · exact hpqA hxpq
        · exact hCA ⟨hxC, hxpq⟩
    rw [hCeq]
    exact ⟨γ, hγ, hγ0, hγ1⟩
  rcases hcover α hαS hO with h1 | h1 <;> rcases hcover α' hα'S hO' with h2 | h2
  · exfalso
    obtain ⟨x, hxB, hxpq⟩ := hBne
    exact hxpq (hAB2.subset ⟨hsame A h1 h2 x (hBS hxB) hxpq, hxB⟩)
  · exact hexact a α α' ha ha0 ha1 hpqα h1 h2 hSsplit
  · refine hexact a' α' α ha' ha'0 ha'1 hpqα' h2 h1 fun x hx hxpq => ?_
    rcases hSsplit x hx hxpq with h | h
    · exact Or.inr h
    · exact Or.inl h
  · exfalso
    obtain ⟨x, hxA, hxpq⟩ := hAne
    exact hxpq (hAB2.subset ⟨hxA, hsame B h1 h2 x (hAS hxA) hxpq⟩)

theorem isPLSphere_one_iUnion_union_iUnion_of_fin_four {r β : Fin 4 → Set E}
    {ρ σ : Fin 4 → ℝ → E} (hρ : ∀ k, IsPLHomeomorphOn (ρ k) (Icc 0 1) (r k))
    (hσ : ∀ k, IsPLHomeomorphOn (σ k) (Icc 0 1) (β k)) (hσ0 : ∀ k, σ k 0 = ρ k 1)
    (hσ1 : ∀ k, σ k 1 = ρ (k + 1) 0) (hrβ : ∀ k, r k ∩ β k = {ρ k 1})
    (hβr : ∀ k, β k ∩ r (k + 1) = {σ k 1}) (hrr : ∀ k l, k ≠ l → Disjoint (r k) (r l))
    (hββ : ∀ k l, k ≠ l → Disjoint (β k) (β l))
    (hrβfar : ∀ k l, l ≠ k → l + 1 ≠ k → Disjoint (r k) (β l)) :
    IsPLSphere 1 ((⋃ k, r k) ∪ ⋃ k, β k) := by
  let A : ℕ → Set E := fun i =>
    if i % 2 = 0 then r (Fin.ofNat 4 (i / 2)) else β (Fin.ofNat 4 (i / 2))
  let γ : ℕ → ℝ → E := fun i =>
    if i % 2 = 0 then ρ (Fin.ofNat 4 (i / 2)) else σ (Fin.ofNat 4 (i / 2))
  have h := isPLSphere_one_biUnion_of_cycle (A := A) (γ := γ) 5
    (fun i hi => by
      interval_cases i
      all_goals first
        | exact hρ _
        | exact hσ _)
    (fun i hi => by
      interval_cases i
      all_goals first
        | exact hσ0 _
        | exact (hσ1 0).symm
        | exact (hσ1 1).symm
        | exact (hσ1 2).symm)
    (by exact hσ1 3)
    (fun i hi => by
      interval_cases i
      all_goals first
        | exact hrβ _
        | exact hβr _)
    (by
      have h3 := hβr 3
      rw [hσ1 3] at h3
      rw [inter_comm]
      exact h3)
    (fun i j hj hij hne => by
      have hi7 : i < 7 := by omega
      interval_cases j <;> interval_cases i
      all_goals first
        | exact absurd hij (by omega)
        | exact absurd rfl hne
        | exact hrr _ _ (by decide)
        | exact hββ _ _ (by decide)
        | exact hrβfar _ _ (by decide) (by decide)
        | exact (hrβfar _ _ (by decide) (by decide)).symm)
  convert h using 1
  ext x
  simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · refine ⟨2 * k.val, by omega, ?_⟩
      have h2 : (2 * k.val) % 2 = 0 := by omega
      have h3 : Fin.ofNat 4 ((2 * k.val) / 2) = k := Fin.ext (by rw [Fin.val_ofNat]; omega)
      have hA : A (2 * k.val) = r k := by
        dsimp only [A]
        rw [ite_eq_left h2, h3]
      rw [hA]
      exact hk
    · refine ⟨2 * k.val + 1, by omega, ?_⟩
      have h2 : (2 * k.val + 1) % 2 ≠ 0 := by omega
      have h3 : Fin.ofNat 4 ((2 * k.val + 1) / 2) = k := Fin.ext (by rw [Fin.val_ofNat]; omega)
      have hA : A (2 * k.val + 1) = β k := by
        dsimp only [A]
        rw [ite_eq_right h2, h3]
      rw [hA]
      exact hk
  · rintro ⟨i, -, hx⟩
    by_cases h2 : i % 2 = 0
    · dsimp only [A] at hx
      rw [ite_eq_left h2] at hx
      exact Or.inl ⟨_, hx⟩
    · dsimp only [A] at hx
      rw [ite_eq_right h2] at hx
      exact Or.inr ⟨_, hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
