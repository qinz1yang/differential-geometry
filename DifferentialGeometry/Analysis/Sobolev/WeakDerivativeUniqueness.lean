import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

theorem ae_eq_of_integral_contDiff_mul_eq_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {S : Set E} (hS : IsOpen S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {f g : E → ℝ} (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ)
    (hfg : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, f x * φ x ∂μ) = ∫ x, g x * φ x ∂μ) :
    f =ᵐ[μ] g := by
  have hz : ∀ᵐ x ∂μ, x ∈ S → (f - g) x = 0 := by
    apply hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub hg).locallyIntegrableOn S)
    intro φ hφ hφc hφs
    have hi := hf.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    have hj := hg.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    simp only [smul_eq_mul] at hi hj
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    simp_rw [mul_comm (φ _)]
    rw [integral_sub hi hj, hfg φ hφ hφc hφs, sub_self]
  filter_upwards [hz, hμS] with x hx hxs
  exact sub_eq_zero.mp (hx hxs)

theorem lp_eq_of_integral_contDiff_mul_eq_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsLocallyFiniteMeasure μ] {S : Set E}
    (hS : IsOpen S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : Lp ℝ p μ}
    (hfg : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, f x * φ x ∂μ) = ∫ x, g x * φ x ∂μ) : f = g := by
  apply Lp.ext
  exact ae_eq_of_integral_contDiff_mul_eq_on hS hμS
    ((Lp.memLp f).locallyIntegrable hp) ((Lp.memLp g).locallyIntegrable hp) hfg

theorem lp_eq_of_weak_deriv_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsLocallyFiniteMeasure μ] {S : Set E}
    (hS : IsOpen S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {U : E → ℝ} {R R' : Lp ℝ p μ} (v : E)
    (hR : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, R x * φ x ∂μ)
    (hR' : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, R' x * φ x ∂μ) :
    R = R' := by
  apply lp_eq_of_integral_contDiff_mul_eq_on hS hμS hp
  intro φ hφ hφc hφs
  exact neg_injective ((hR φ hφ hφc hφs).symm.trans (hR' φ hφ hφc hφs))

end DifferentialGeometry.Analysis.Sobolev
