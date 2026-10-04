import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointLevelKernels

/-!
# Kernel for LFR24: a second height is strictly increasing along the band fibres

`strictMonoOn_comp_hittingTime_of_rate`: let `Φ` be a flow along which two heights `η` and `F`
grow at positive rates on orbit segments inside `U ⊇ η⁻¹[a, b]`. For a point `p` of the band and
hitting times `τ s` of the levels `s ∈ [a, b]` (with the usual specification: `η (Φ (τ s) p) = s` and
the orbit between times `0` and `τ s` stays at heights between `η p` and `s`), the function
`s ↦ F (Φ (τ s) p)` is strictly increasing on `[a, b]`. With `exists_embedding_level_of_band_product`
this makes every level `{F = s₀}` crossing the band a cross-section homeomorphic to the base level
(used for LFR24's core levels `{F = s}`, `s ∈ [3, 6]`).
-/

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Collapse

/-- Points between two hitting times lie in the union of the two orbit segments from time `0`. -/
theorem mem_uIcc_or_mem_uIcc_of_mem_Icc_min_max {t t' u : ℝ} (hu : u ∈ Icc (min t t') (max t t')) :
    u ∈ uIcc 0 t ∨ u ∈ uIcc 0 t' := by
  rcases le_total 0 u with h0 | h0
  · by_cases h1 : u ≤ t
    · exact Or.inl (mem_uIcc.2 (Or.inl ⟨h0, h1⟩))
    · refine Or.inr (mem_uIcc.2 (Or.inl ⟨h0, ?_⟩))
      have h2 := hu.2
      rcases le_total t t' with h | h
      · rwa [max_eq_right h] at h2
      · rw [max_eq_left h] at h2
        exact absurd h2 h1
  · by_cases h1 : t ≤ u
    · exact Or.inl (mem_uIcc.2 (Or.inr ⟨h1, h0⟩))
    · refine Or.inr (mem_uIcc.2 (Or.inr ⟨?_, h0⟩))
      have h2 := hu.1
      rcases le_total t t' with h | h
      · rw [min_eq_left h] at h2
        exact absurd h2 h1
      · rwa [min_eq_right h] at h2

/-- **A second height increases strictly along each band fibre.** -/
theorem strictMonoOn_comp_hittingTime_of_rate {X : Type*} {Φ : ℝ → X → X}
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η F : X → ℝ} {U : Set X} {κ κ' : ℝ}
    (hκ : 0 < κ) (hκ' : 0 < κ')
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    (hFrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → F x + κ' * t ≤ F (Φ t x))
    {a b : ℝ} (hU : ∀ x, η x ∈ Icc a b → x ∈ U) {p : X} (hp : η p ∈ Icc a b) {τ : ℝ → ℝ}
    (hlev : ∀ s ∈ Icc a b, η (Φ (τ s) p) = s)
    (hseg : ∀ s ∈ Icc a b, ∀ u ∈ uIcc 0 (τ s), η (Φ u p) ∈ uIcc (η p) s) :
    StrictMonoOn (fun s => F (Φ (τ s) p)) (Icc a b) := by
  intro s hs s' hs' hss'
  have hband : ∀ u ∈ Icc (min (τ s) (τ s')) (max (τ s) (τ s')), Φ u p ∈ U := by
    intro u hu
    apply hU
    rcases mem_uIcc_or_mem_uIcc_of_mem_Icc_min_max hu with h | h
    · exact uIcc_subset_Icc hp hs (hseg s hs u h)
    · exact uIcc_subset_Icc hp hs' (hseg s' hs' u h)
  have htt : τ s < τ s' := by
    by_contra hcon
    rcases (le_of_not_gt hcon).eq_or_lt with heq | hlt
    · have : s' = s := by rw [← hlev s hs, ← hlev s' hs', heq]
      exact absurd this (ne_of_gt hss')
    · have h := lt_of_rate_of_lt hΦadd hκ hrate hlt fun u hu =>
        hband u ⟨by rw [min_eq_right hlt.le]; exact hu.1, by rw [max_eq_left hlt.le]; exact hu.2⟩
      rw [hlev s hs, hlev s' hs'] at h
      exact absurd h (not_lt.2 hss'.le)
  exact lt_of_rate_of_lt hΦadd hκ' hFrate htt fun u hu =>
    hband u ⟨by rw [min_eq_left htt.le]; exact hu.1, by rw [max_eq_right htt.le]; exact hu.2⟩

end DifferentialGeometry.Geometry.Collapse
