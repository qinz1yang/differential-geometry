import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition

section

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_iteratedFDeriv_bound_of_eventually_bounded {U : Set E} (hU : IsOpen U) {Φ : ℕ → E → F}
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M := by
  classical
  intro r K hK hKU
  obtain ⟨M, hM⟩ := hbdd r K hK hKU
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hM
  have hfin : ∀ k : ℕ, ∃ Mₖ : ℝ,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ Mₖ := fun k => by
    obtain ⟨Mₖ, hMₖ⟩ := hK.exists_bound_of_continuousOn
      (((hΦ k).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
        hU.uniqueDiffOn).mono hKU)
    exact ⟨Mₖ, fun x hx => by
      rw [← iteratedFDerivWithin_of_isOpen r hU (hKU hx)]
      exact hMₖ x hx⟩
  choose Mₖ hMₖ using hfin
  let S : Finset ℝ := (Finset.range (k₀ + 1)).image Mₖ
  have hSne : S.Nonempty :=
    ⟨Mₖ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos k₀), rfl⟩⟩
  refine ⟨max M (S.max' hSne), fun k x hx => ?_⟩
  rcases lt_or_ge k (k₀ + 1) with hk | hk
  · have hm : Mₖ k ∈ S := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    exact (hMₖ k x hx).trans
      ((Finset.le_max' S (Mₖ k) hm).trans (le_max_right M (S.max' hSne)))
  · exact (hk₀ k (Nat.le_of_succ_le hk) x hx).trans (le_max_left M (S.max' hSne))

theorem MapCInfConvergenceOnCompacts.exists_iteratedFDeriv_bound
    {U : Set E} (hU : IsOpen U) {Φ : ℕ → E → F} {Φinf : E → F}
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (⊤ : ℕ∞) Φinf U)
    (hconv : MapCInfConvergenceOnCompacts U Φ Φinf)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℕ → ℝ, (∀ p, 0 ≤ C p) ∧
      ∀ p k z, z ∈ K → ‖iteratedFDeriv ℝ p (Φ k) z‖ ≤ C p := by
  have hev : ∀ p : ℕ, ∀ L : Set E, IsCompact L → L ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ L, ‖iteratedFDeriv ℝ p (Φ k) z‖ ≤ M := by
    intro p L hL hLU
    obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hΦinf hU (by exact_mod_cast le_top)).mono hLU)
    exact ⟨M + 1, TendstoUniformlyOn.eventually_norm_le
      (hconv.tendstoUniformlyOn_iteratedFDeriv hU hL hLU hΦ hΦinf p) hM⟩
  have hall := exists_iteratedFDeriv_bound_of_eventually_bounded hU hΦ hev
  choose C hC using fun p => hall p K hK hKU
  exact ⟨fun p => max 0 (C p), (fun _ => le_max_left _ _),
    fun p k z hz => (hC p k z hz).trans (le_max_right _ _)⟩

end DifferentialGeometry.CheegerGromovCompactness

end
