/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcSplit
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCircleCapSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Cycle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLSphere_one_iUnion_union_iUnion_of_cycle {m : ℕ} {r β : Fin (m + 2) → Set E}
    {ρ σ : Fin (m + 2) → ℝ → E} (hρ : ∀ k, IsPLHomeomorphOn (ρ k) (Icc 0 1) (r k))
    (hσ : ∀ k, IsPLHomeomorphOn (σ k) (Icc 0 1) (β k)) (hσ0 : ∀ k, σ k 0 = ρ k 1)
    (hσ1 : ∀ k, σ k 1 = ρ (k + 1) 0) (hrβ : ∀ k, r k ∩ β k = {ρ k 1})
    (hβr : ∀ k, β k ∩ r (k + 1) = {σ k 1}) (hrr : ∀ k l, k ≠ l → Disjoint (r k) (r l))
    (hββ : ∀ k l, k ≠ l → Disjoint (β k) (β l))
    (hrβfar : ∀ k l, l ≠ k → l + 1 ≠ k → Disjoint (r k) (β l)) :
    IsPLSphere 1 ((⋃ k, r k) ∪ ⋃ k, β k) := by
  let f : ℕ → Fin (m + 2) := fun i => Fin.ofNat (m + 2) (i / 2)
  let A : ℕ → Set E := fun i => if i % 2 = 0 then r (f i) else β (f i)
  let γ : ℕ → ℝ → E := fun i => if i % 2 = 0 then ρ (f i) else σ (f i)
  have hAe : ∀ i, i % 2 = 0 → A i = r (f i) := fun i h => ite_eq_left h
  have hAo : ∀ i, i % 2 ≠ 0 → A i = β (f i) := fun i h => ite_eq_right h
  have hγe : ∀ i, i % 2 = 0 → γ i = ρ (f i) := fun i h => ite_eq_left h
  have hγo : ∀ i, i % 2 ≠ 0 → γ i = σ (f i) := fun i h => ite_eq_right h
  have hfv : ∀ i, i / 2 < m + 2 → (f i).val = i / 2 := fun i hi => by
    change (i / 2) % (m + 2) = i / 2
    exact Nat.mod_eq_of_lt hi
  have hfe : ∀ i, i % 2 = 0 → f (i + 1) = f i := fun i h => by
    change Fin.ofNat (m + 2) ((i + 1) / 2) = Fin.ofNat (m + 2) (i / 2)
    congr 1
    omega
  have hfo : ∀ i, i % 2 ≠ 0 → f (i + 1) = f i + 1 := fun i h => by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one]
    change ((i + 1) / 2) % (m + 2) = ((i / 2) % (m + 2) + 1) % (m + 2)
    rw [show (i + 1) / 2 = i / 2 + 1 by omega, Nat.add_mod (i / 2) 1,
      Nat.one_mod_eq_one.mpr (by omega)]
  have hlast : f (2 * m + 3) + 1 = f 0 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one, hfv _ (by omega), hfv _ (by omega)]
    rw [show (2 * m + 3) / 2 + 1 = m + 2 by omega, Nat.mod_self]
  have hne : ∀ i j, i / 2 < m + 2 → j / 2 < m + 2 → i / 2 ≠ j / 2 → f i ≠ f j :=
    fun i j hi hj h h' => h (by rw [← hfv i hi, ← hfv j hj, h'])
  have h := isPLSphere_one_biUnion_of_cycle (A := A) (γ := γ) (2 * m + 1)
    (fun i hi => by
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rw [hγe i h, hAe i h]
        exact hρ _
      · rw [hγo i (by omega), hAo i (by omega)]
        exact hσ _)
    (fun i hi => by
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rw [hγo (i + 1) (by omega), hγe i h, hfe i h]
        exact hσ0 _
      · rw [hγe (i + 1) (by omega), hγo i (by omega), hfo i (by omega)]
        exact (hσ1 _).symm)
    (by
      rw [hγo (2 * m + 1 + 2) (by omega), hγe 0 (by omega), hσ1, ← hlast])
    (fun i hi => by
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rw [hAe i h, hAo (i + 1) (by omega), hγe i h, hfe i h]
        exact hrβ _
      · rw [hAo i (by omega), hAe (i + 1) (by omega), hγo i (by omega), hfo i (by omega)]
        exact hβr _)
    (by
      rw [hAe 0 (by omega), hAo (2 * m + 1 + 2) (by omega), hγe 0 (by omega), inter_comm,
        ← hlast]
      have h3 := hβr (f (2 * m + 1 + 2))
      rw [hσ1] at h3
      exact h3)
    (fun i j hj hij hne' => by
      have hi2 : i / 2 < m + 2 := by omega
      have hj2 : j / 2 < m + 2 := by omega
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
        rcases Nat.mod_two_eq_zero_or_one j with hj' | hj'
      · rw [hAe i hi, hAe j hj']
        exact hrr _ _ (hne i j hi2 hj2 (by omega))
      · rw [hAe i hi, hAo j (by omega)]
        refine hrβfar _ _ (hne j i hj2 hi2 (by omega)) fun h' => ?_
        have hv := congrArg Fin.val h'
        rw [Fin.val_add, Fin.val_one, hfv j hj2, hfv i hi2] at hv
        rcases Nat.lt_or_ge (j / 2 + 1) (m + 2) with h'' | h''
        · rw [Nat.mod_eq_of_lt h''] at hv
          omega
        · rw [show j / 2 + 1 = m + 2 by omega, Nat.mod_self] at hv
          exact hne' (by rw [Prod.mk.injEq]; omega)
      · rw [hAo i (by omega), hAe j hj']
        refine (hrβfar _ _ (hne i j hi2 hj2 (by omega)) fun h' => ?_).symm
        have hv := congrArg Fin.val h'
        rw [Fin.val_add, Fin.val_one, hfv j hj2, hfv i hi2,
          Nat.mod_eq_of_lt (by omega : i / 2 + 1 < m + 2)] at hv
        omega
      · rw [hAo i (by omega), hAo j (by omega)]
        exact hββ _ _ (hne i j hi2 hj2 (by omega)))
  convert h using 1
  ext x
  simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · refine ⟨2 * k.val, by omega, ?_⟩
      have h3 : f (2 * k.val) = k := Fin.ext (by rw [hfv _ (by omega)]; omega)
      rw [hAe _ (by omega), h3]
      exact hk
    · refine ⟨2 * k.val + 1, by omega, ?_⟩
      have h3 : f (2 * k.val + 1) = k := Fin.ext (by rw [hfv _ (by omega)]; omega)
      rw [hAo _ (by omega), h3]
      exact hk
  · rintro ⟨i, -, hx⟩
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
    · rw [hAe i h2] at hx
      exact Or.inl ⟨_, hx⟩
    · rw [hAo i (by omega)] at hx
      exact Or.inr ⟨_, hx⟩

end Cycle

theorem exists_split_of_runs {m : ℕ} {B₁ : Set E3} (hB₁ : IsPLBall 3 B₁)
    {H r : Fin (m + 2) → Set E3}
    {rH : Fin (m + 2) → (Fin 3 → ℝ) → E3} {ρ : Fin (m + 2) → ℝ → E3}
    (hrH : ∀ k, IsPLHomeomorphOn (rH k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (H k))
    (hHB : ∀ k, H k ⊆ frontier B₁) (hHdisj : Pairwise fun k l => Disjoint (H k) (H l))
    (hρ : ∀ k, IsPLHomeomorphOn (ρ k) (Icc 0 1) (r k)) (hrB : ∀ k, r k ⊆ frontier B₁)
    (hrr : Pairwise fun k l => Disjoint (r k) (r l))
    (hout : ∀ k, r k ∩ H k = {ρ k 1}) (hin : ∀ k, r (k + 1) ∩ H k = {ρ (k + 1) 0})
    (hfar : ∀ k l, l ≠ k → l + 1 ≠ k → r k ∩ H l = ∅)
    (hbout : ∀ k, ρ k 1 ∈ rH k '' stdSimplexBoundary 2)
    (hbin : ∀ k, ρ (k + 1) 0 ∈ rH k '' stdSimplexBoundary 2) :
    ∃ (X Y : Set E3) (qX qY : (Fin 3 → ℝ) → E3) (β : Fin (m + 2) → Set E3)
      (σ τ : Fin (m + 2) → ℝ → E3),
      IsPLHomeomorphOn qX (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X ∧
      IsPLHomeomorphOn qY (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Y ∧
      X ∪ Y ∪ (⋃ k, H k) = frontier B₁ ∧ X ∩ Y = ⋃ k, r k ∧
      (∀ k, IsPLHomeomorphOn (σ k) (Icc 0 1) (β k) ∧ σ k 0 = ρ k 1 ∧ σ k 1 = ρ (k + 1) 0) ∧
      (∀ k, IsPLHomeomorphOn (τ k) (Icc 0 1) (closure (rH k '' stdSimplexBoundary 2 \ β k)) ∧
        τ k 0 = ρ k 1 ∧ τ k 1 = ρ (k + 1) 0) ∧
      (∀ k, β k ⊆ rH k '' stdSimplexBoundary 2) ∧
      (∀ k, (X ∩ H k = β k ∧ Y ∩ H k = closure (rH k '' stdSimplexBoundary 2 \ β k)) ∨
        (X ∩ H k = closure (rH k '' stdSimplexBoundary 2 \ β k) ∧ Y ∩ H k = β k)) ∧
      qX '' stdSimplexBoundary 2 = (⋃ k, r k) ∪ ⋃ k, (X ∩ H k) ∧
      qY '' stdSimplexBoundary 2 = (⋃ k, r k) ∪ ⋃ k, (Y ∩ H k) := by
  have hbH : ∀ k, rH k '' stdSimplexBoundary 2 ⊆ H k := fun k => by
    rw [← (hrH k).image_eq]
    exact image_mono fun x hx => hx.1
  have hne : ∀ k, ρ k 1 ≠ ρ (k + 1) 0 := by
    intro k h
    have h1 : ρ k 1 ∈ r k := (hρ k).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
    have h2 : ρ (k + 1) 0 ∈ r (k + 1) := (hρ (k + 1)).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    have hk : k ≠ k + 1 := by
      intro hk
      have hv := congrArg Fin.val hk
      rw [Fin.val_add, Fin.val_one] at hv
      rcases Nat.lt_or_ge (k.val + 1) (m + 2) with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at hv
        omega
      · have hk2 : k.val + 1 = m + 2 := by omega
        rw [hk2, Nat.mod_self] at hv
        omega
    exact Set.disjoint_left.mp (hrr hk) h1 (h ▸ h2)
  have harc : ∀ k, ∃ (β : Set E3) (σ τ : ℝ → E3), IsPLHomeomorphOn σ (Icc 0 1) β ∧
      σ 0 = ρ k 1 ∧ σ 1 = ρ (k + 1) 0 ∧ β ⊆ rH k '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn τ (Icc 0 1) (closure (rH k '' stdSimplexBoundary 2 \ β)) ∧
      τ 0 = ρ k 1 ∧ τ 1 = ρ (k + 1) 0 := by
    intro k
    obtain ⟨A, B', γ, δ', h⟩ := exists_arc_decomposition_of_isPLSphere_one
      ((hrH k).isPLSphere_image_stdSimplexBoundary (n := 1)) (hbout k) (hbin k) (hne k)
    obtain ⟨hγ, hδ, hγ0, hγ1, hδ0, hδ1, hAB, hABi⟩ := h
    have hcl : closure (rH k '' stdSimplexBoundary 2 \ A) = B' := by
      have hdiff : rH k '' stdSimplexBoundary 2 \ A = B' \ {δ' 0, δ' 1} := by
        rw [← hAB, hδ0, hδ1, ← hABi]
        ext z
        simp only [mem_sdiff, mem_union, mem_inter_iff]
        tauto
      rw [hdiff]
      exact hδ.closure_sdiff_endpoints zero_lt_one
    refine ⟨A, γ, δ', hγ, hγ0, hγ1, ?_, ?_, hδ0, hδ1⟩
    · rw [← hAB]
      exact subset_union_left
    · rw [hcl]
      exact hδ
  choose β σ τ hσ hσ0 hσ1 hβb hτ hτ0 hτ1 using harc
  have hβH : ∀ k, β k ⊆ H k := fun k => (hβb k).trans (hbH k)
  have hρ0 : ∀ k, ρ k 0 ∈ r k := fun k => (hρ k).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hρ1 : ∀ k, ρ k 1 ∈ r k := fun k => (hρ k).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hσ0m : ∀ k, σ k 0 ∈ β k := fun k => (hσ k).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hσ1m : ∀ k, σ k 1 ∈ β k := fun k => (hσ k).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hrβ : ∀ k, r k ∩ β k = {ρ k 1} := by
    intro k
    apply Subset.antisymm
    · rw [← hout k]
      exact inter_subset_inter_right _ (hβH k)
    · rintro z rfl
      exact ⟨hρ1 k, hσ0 k ▸ hσ0m k⟩
  have hβr : ∀ k, β k ∩ r (k + 1) = {σ k 1} := by
    intro k
    rw [hσ1 k]
    apply Subset.antisymm
    · rw [← hin k, inter_comm (β k)]
      exact inter_subset_inter_right _ (hβH k)
    · rintro z rfl
      exact ⟨hσ1 k ▸ hσ1m k, hρ0 (k + 1)⟩
  have hJ := isPLSphere_one_iUnion_union_iUnion_of_cycle hρ hσ hσ0 hσ1 hrβ hβr
    (fun k l hkl => hrr hkl) (fun k l hkl => (hHdisj hkl).mono (hβH k) (hβH l))
    (fun k l h1 h2 => by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact subset_eq_empty (inter_subset_inter_right _ (hβH l)) (hfar k l h1 h2))
  set J := (⋃ k, r k) ∪ ⋃ k, β k
  have hJS : J ⊆ frontier B₁ :=
    union_subset (iUnion_subset hrB) (iUnion_subset fun k => (hβH k).trans (hHB k))
  have hends : ∀ k, ({σ k 0, σ k 1} : Set E3) ⊆ ⋃ l, r l := by
    intro k z hz
    rcases hz with rfl | hz
    · exact mem_iUnion.mpr ⟨k, hσ0 k ▸ hρ1 k⟩
    · rw [mem_singleton_iff.mp hz, hσ1 k]
      exact mem_iUnion.mpr ⟨k + 1, hρ0 (k + 1)⟩
  have hrHl : ∀ k l, r k ∩ H l ⊆ {σ l 0, σ l 1} := by
    intro k l z hz
    by_cases hlk : l = k
    · subst hlk
      rw [hout l] at hz
      rw [mem_singleton_iff.mp hz, ← hσ0 l]
      exact mem_insert _ _
    · by_cases hlk' : l + 1 = k
      · subst hlk'
        rw [hin l] at hz
        rw [mem_singleton_iff.mp hz, ← hσ1 l]
        exact mem_insert_of_mem _ (mem_singleton _)
      · rw [hfar k l hlk hlk'] at hz
        exact hz.elim
  have hHJ : ∀ k, H k ∩ J = β k := by
    intro k
    apply Subset.antisymm
    · rintro z ⟨hzH, hz | hz⟩
      · obtain ⟨l, hl⟩ := mem_iUnion.mp hz
        rcases hrHl l k ⟨hl, hzH⟩ with h | h
        · rw [h]
          exact hσ0m k
        · rw [mem_singleton_iff.mp h]
          exact hσ1m k
      · obtain ⟨l, hl⟩ := mem_iUnion.mp hz
        by_cases hlk : l = k
        · rw [← hlk]
          exact hl
        · exact absurd hzH (Set.disjoint_left.mp (hHdisj hlk) (hβH l hl))
    · intro z hz
      exact ⟨hβH k hz, Or.inr (mem_iUnion.mpr ⟨k, hz⟩)⟩
  obtain ⟨X, Y, qX, qY, hqX, hqY, hXY, hXYi, hXH, hqXb, hqYb⟩ :=
    hB₁.isPLSphere_frontier.exists_split_of_circle_caps hJ hJS hrH hHB hHdisj hσ hβb hHJ
  have hJβ : J \ ⋃ k, (β k \ {σ k 0, σ k 1}) = ⋃ k, r k := by
    apply Subset.antisymm
    · rintro z ⟨hz | hz, hzn⟩
      · exact hz
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
        by_contra hzr
        exact hzn (mem_iUnion.mpr ⟨k, hk, fun h => hzr (hends k h)⟩)
    · intro z hz
      refine ⟨Or.inl hz, fun h => ?_⟩
      obtain ⟨l, hl, hln⟩ := mem_iUnion.mp h
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact hln (hrHl k l ⟨hk, hβH l hl⟩)
  rw [hJβ] at hXYi hqXb hqYb
  exact ⟨X, Y, qX, qY, β, σ, τ, hqX, hqY, hXY, hXYi, fun k => ⟨hσ k, hσ0 k, hσ1 k⟩,
    fun k => ⟨hτ k, hτ0 k, hτ1 k⟩, hβb, hXH, hqXb, hqYb⟩

end DifferentialGeometry.Topology.PiecewiseLinear
