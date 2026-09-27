import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeUniqueness
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem ae_mem_interior_time_prod
    {E : Type*} [MeasurableSpace E] {ν : Measure E} [SFinite ν]
    {T a b : ℝ} {Ω : Set E} (hΩ : MeasurableSet Ω) :
    ∀ᵐ p ∂((timeMeasure T).restrict (Icc a b)).prod (ν.restrict Ω),
      p ∈ Ioo a b ×ˢ Ω := by
  have htime : (timeMeasure T).restrict (Icc a b) =
      (timeMeasure T).restrict (Ioo a b) := by
    apply Measure.restrict_congr_set
    exact ae_mono Measure.restrict_le_self Ioo_ae_eq_Icc.symm
  rw [htime]
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod hΩ)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem hΩ] with x hx
  exact ⟨ht, hx⟩

theorem lp_eq_of_weak_time_deriv_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ν : Measure E} [IsLocallyFiniteMeasure ν]
    {T a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {U : ℝ × E → ℝ}
    {R R' : Lp ℝ p (((timeMeasure T).restrict (Icc a b)).prod (ν.restrict Ω))}
    (hR : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ x, U x * fderiv ℝ φ x (1, 0)
        ∂((timeMeasure T).restrict (Icc a b)).prod (ν.restrict Ω)) =
      -∫ x, R x * φ x ∂((timeMeasure T).restrict (Icc a b)).prod (ν.restrict Ω))
    (hR' : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ x, U x * fderiv ℝ φ x (1, 0)
        ∂((timeMeasure T).restrict (Icc a b)).prod (ν.restrict Ω)) =
      -∫ x, R' x * φ x ∂((timeMeasure T).restrict (Icc a b)).prod (ν.restrict Ω)) :
    R = R' :=
  DifferentialGeometry.Analysis.Sobolev.lp_eq_of_weak_deriv_integral
    (isOpen_Ioo.prod hΩ) (ae_mem_interior_time_prod hΩ.measurableSet) hp (1, 0) hR hR'

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
