import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenfunctionComplex_EG

/-!
# Norm form of the stability hypothesis on a planar domain (S-W-EIG, G4)

`‖L‖² = (L 1)² + (L I)²` for `L : ℂ →L[ℝ] ℝ`, so the stability inequality
`0 ≤ ∫_Ω (‖dφ‖² + W φ²)` of a conformal-coordinate stability theorem is exactly the hypothesis of
`exists_positive_first_eigenfunction_complex_EG`; the two integrands are integrable for
`φ ∈ C_c^∞(Ω)`, so the single integral splits.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem clm_complex_apply_EG (L : ℂ →L[ℝ] ℝ) (z : ℂ) : L z = z.re * L 1 + z.im * L Complex.I := by
  have h : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul]
  rfl

theorem norm_sq_clm_complex_EG (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
  set s := Real.sqrt ((L 1) ^ 2 + (L Complex.I) ^ 2) with hs
  have hs2 : s ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  apply le_antisymm
  · rw [← hs2]
    apply pow_le_pow_left₀ (norm_nonneg _)
    apply L.opNorm_le_bound hs0
    intro z
    rw [Real.norm_eq_abs, clm_complex_apply_EG]
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    apply abs_le_of_sq_le_sq _ (mul_nonneg hs0 (norm_nonneg _))
    rw [mul_pow, hz, hs2]
    nlinarith [sq_nonneg (z.re * L Complex.I - z.im * L 1)]
  · by_cases h0 : s = 0
    · rw [← hs2, h0]
      simp
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      let z : ℂ := ⟨L 1 / s, L Complex.I / s⟩
      have hz : ‖z‖ = 1 := by
        rw [Complex.norm_def, Complex.normSq_apply]
        simp only [z]
        rw [Real.sqrt_eq_one]
        field_simp
        nlinarith [hs2]
      have hLz : L z = s := by
        rw [clm_complex_apply_EG]
        simp only [z]
        field_simp
        nlinarith [hs2]
      have hle : s ≤ ‖L‖ := by
        have := L.le_opNorm z
        rw [hz, mul_one, hLz, Real.norm_eq_abs, abs_of_pos hspos] at this
        exact this
      rw [← hs2]
      exact pow_le_pow_left₀ hspos.le hle 2

theorem integrable_gradSq_EG {Ω : Set ℂ} {φ : ℂ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun z => ‖fderiv ℝ φ z‖ ^ 2) (volume.restrict Ω) := by
  have hcont : Continuous (fun z => ‖fderiv ℝ φ z‖ ^ 2) :=
    ((hφ.continuous_fderiv (by simp)).norm).pow 2
  have hcs : HasCompactSupport (fun z => ‖fderiv ℝ φ z‖ ^ 2) :=
    (hc.fderiv (𝕜 := ℝ)).norm.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact (hcont.integrable_of_hasCompactSupport hcs).restrict

theorem integrable_weight_sq_complex_EG {Ω U : Set ℂ} (hU : IsOpen U) (hΩU : Ω ⊆ U)
    {W : ℂ → ℝ} (hW : ContinuousOn W U) {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => W z * φ z ^ 2) (volume.restrict Ω) := by
  have hcont : Continuous (fun z => W z * φ z ^ 2) := by
    rw [← continuousOn_univ]
    have h1 : ContinuousOn (fun z => W z * φ z ^ 2) U := hW.mul (hφ.pow 2).continuousOn
    have h2 : ContinuousOn (fun z => W z * φ z ^ 2) (tsupport φ)ᶜ := by
      refine continuousOn_const.congr (fun z hz => ?_) (f := fun _ => (0 : ℝ))
      have : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [this]
    have hcover : (Set.univ : Set ℂ) ⊆ U ∪ (tsupport φ)ᶜ := by
      intro z _
      by_cases hz : z ∈ tsupport φ
      · exact Or.inl (hΩU (hs hz))
      · exact Or.inr hz
    exact (h1.union_of_isOpen h2 hU (isClosed_tsupport φ).isOpen_compl).mono hcover
  have hcs : HasCompactSupport (fun z => W z * φ z ^ 2) := by
    apply hc.mono
    intro z hz
    by_contra h
    apply hz
    have : φ z = 0 := Function.notMem_support.mp h
    simp [this]
  exact (hcont.integrable_of_hasCompactSupport hcs).restrict

theorem integral_norm_form_EG {Ω U : Set ℂ} (hU : IsOpen U) (hΩU : Ω ⊆ U)
    {W : ℂ → ℝ} (hW : ContinuousOn W U) {φ : ℂ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ z in Ω, (‖fderiv ℝ φ z‖ ^ 2 + W z * φ z ^ 2)) =
      (∫ z in Ω, ((fderiv ℝ φ z 1) ^ 2 + (fderiv ℝ φ z Complex.I) ^ 2)) +
        ∫ z in Ω, W z * φ z ^ 2 := by
  rw [integral_add (integrable_gradSq_EG hφ hc)
    (integrable_weight_sq_complex_EG hU hΩU hW hφ.continuous hc hs)]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  exact norm_sq_clm_complex_EG _

/-- Norm form of the stability hypothesis: `0 ≤ ∫_Ω ‖dφ‖² + W φ²` for `φ ∈ C_c^∞(Ω)`. -/
theorem exists_positive_first_eigenfunction_complex_norm_EG
    {Ω U : Set ℂ} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩc : IsPreconnected Ω)
    (hne : Ω.Nonempty) (hU : IsOpen U) (hΩU : closure Ω ⊆ U) {ρ W : ℂ → ℝ}
    (hρs : ContDiffOn ℝ (⊤ : ℕ∞) ρ U) (hWs : ContDiffOn ℝ (⊤ : ℕ∞) W U)
    (hρpos : ∀ z ∈ closure Ω, 0 < ρ z)
    (hstab : ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      0 ≤ ∫ z in Ω, (‖fderiv ℝ φ z‖ ^ 2 + W z * φ z ^ 2)) :
    ∃ (u : ℂ → ℝ) (μ : ℝ), ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧ (∀ z ∈ Ω, 0 < u z) ∧ 0 ≤ μ ∧
      (∫ z in Ω, ρ z * u z ^ 2) = 1 ∧
      (∀ z ∈ Ω, -Laplacian.laplacian u z + W z * u z = μ * ρ z * u z) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        μ * (∫ z in Ω, ρ z * φ z ^ 2) ≤ ∫ z in Ω, (‖fderiv ℝ φ z‖ ^ 2 + W z * φ z ^ 2) := by
  have hΩU' : Ω ⊆ U := subset_closure.trans hΩU
  have hWc : ContinuousOn W U := hWs.continuousOn
  obtain ⟨u, μ, hu, hpos, hμ, hN, hEq, hmin⟩ :=
    exists_positive_first_eigenfunction_complex_EG hΩ hΩb hΩc hne hU hΩU hρs hWs hρpos
      (fun φ h1 h2 h3 => by
        have := hstab φ h1 h2 h3
        rwa [integral_norm_form_EG hU hΩU' hWc h1 h2 h3] at this)
  refine ⟨u, μ, hu, hpos, hμ, hN, hEq, fun φ h1 h2 h3 => ?_⟩
  rw [integral_norm_form_EG hU hΩU' hWc h1 h2 h3]
  exact hmin φ h1 h2 h3

end DifferentialGeometry.Analysis.Sobolev.Euclidean
