import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Set

theorem IsCompact.exists_pos_sublevel_subset {M : Type*} [TopologicalSpace M]
    {K U : Set M} (hK : IsCompact K) {f : M → ℝ} (hf : ContinuousOn f K)
    (hU : IsOpen U) {a : ℝ} (hsub : K ∩ f ⁻¹' Iic a ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ K ∩ f ⁻¹' Iic (a + ε) ⊆ U := by
  by_cases hne : (K ∩ Uᶜ).Nonempty
  · obtain ⟨q, hq, hqmin⟩ :=
      (hK.inter_right hU.isClosed_compl).exists_isMinOn hne (hf.mono inter_subset_left)
    have haq : a < f q := lt_of_not_ge (fun h => hq.2 (hsub ⟨hq.1, h⟩))
    refine ⟨(f q - a) / 2, by linarith, ?_⟩
    rintro x ⟨hxK, hxf⟩
    by_contra hxU
    have hle : f q ≤ f x := hqmin ⟨hxK, hxU⟩
    change f x ≤ a + (f q - a) / 2 at hxf
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    rintro x ⟨hx, _⟩
    by_contra hxU
    exact hne ⟨x, hx, hxU⟩

theorem IsCompact.exists_pos_superlevel_subset {M : Type*} [TopologicalSpace M]
    {K U : Set M} (hK : IsCompact K) {f : M → ℝ} (hf : ContinuousOn f K)
    (hU : IsOpen U) {a : ℝ} (hsub : K ∩ f ⁻¹' Ici a ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ K ∩ f ⁻¹' Ici (a - ε) ⊆ U := by
  obtain ⟨ε, hε, hlow⟩ := hK.exists_pos_sublevel_subset hf.neg hU
    (a := -a) (by
      rintro x ⟨hxK, hxf⟩
      change -f x ≤ -a at hxf
      exact hsub ⟨hxK, neg_le_neg_iff.mp hxf⟩)
  refine ⟨ε, hε, ?_⟩
  rintro x ⟨hxK, hxf⟩
  apply hlow
  refine ⟨hxK, ?_⟩
  change -f x ≤ -a + ε
  change a - ε ≤ f x at hxf
  linarith

theorem Continuous.exists_sublevel_subset_of_unique_minimum {M : Type*} [TopologicalSpace M]
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) {p : M}
    (hmin : ∀ x, x ≠ p → f p < f x) {U : Set M} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ f ⁻¹' Iic (f p + ε) ⊆ U := by
  obtain ⟨ε, hε, hlow⟩ := isCompact_univ.exists_pos_sublevel_subset hf.continuousOn hU
    (a := f p) (by
      rintro x ⟨_, hx⟩
      have heq : x = p := by
        by_contra hne
        exact (hmin x hne).not_ge hx
      exact heq ▸ hp)
  exact ⟨ε, hε, fun _ hx => hlow ⟨mem_univ _, hx⟩⟩

theorem Continuous.exists_superlevel_subset_of_unique_maximum {M : Type*} [TopologicalSpace M]
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) {p : M}
    (hmax : ∀ x, x ≠ p → f x < f p) {U : Set M} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ f ⁻¹' Ici (f p - ε) ⊆ U := by
  obtain ⟨ε, hε, hhigh⟩ := isCompact_univ.exists_pos_superlevel_subset hf.continuousOn hU
    (a := f p) (by
      rintro x ⟨_, hx⟩
      have heq : x = p := by
        by_contra hne
        exact (hmax x hne).not_ge hx
      exact heq ▸ hp)
  exact ⟨ε, hε, fun _ hx => hhigh ⟨mem_univ _, hx⟩⟩
