import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]

theorem exists_lp_weak_deriv_of_ae_eq_finite_sum
    {ι : Type*} (s : Finset ι) {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (v : E)
    (U : E → ℝ) (Y DY : ι → Lp ℝ p μ) (A : ι → E → ℝ)
    (hA : ∀ i ∈ s, MemLp (A i) ∞ μ)
    (hDA : ∀ i ∈ s, MemLp (fun x => fderiv ℝ (A i) x v) ∞ μ)
    (hAsmooth : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (A i) Ω)
    (hY : ∀ i ∈ s, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, Y i x * fderiv ℝ φ x v ∂μ) = -∫ x, DY i x * φ x ∂μ)
    (hU : U =ᵐ[μ] fun x => ∑ i ∈ s, A i x * Y i x) :
    ∃ DU : Lp ℝ p μ,
      (DU =ᵐ[μ] fun x => ∑ i ∈ s,
        (A i x * DY i x + fderiv ℝ (A i) x v * Y i x)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, DU x * φ x ∂μ := by
  let Q := fun i x => A i x * DY i x + fderiv ℝ (A i) x v * Y i x
  have hQ (i) (hi : i ∈ s) : MemLp (Q i) p μ :=
    ((hA i hi).mul (Lp.memLp (DY i))).add ((hDA i hi).mul (Lp.memLp (Y i)))
  have hsum : MemLp (fun x => ∑ i ∈ s, Q i x) p μ :=
    memLp_finsetSum s hQ
  let DU := hsum.toLp (fun x => ∑ i ∈ s, Q i x)
  refine ⟨DU, hsum.coeFn_toLp, ?_⟩
  intro φ hφ hφc hφs
  have hI (i) (hi : i ∈ s) : Integrable (fun x => A i x * Y i x * fderiv ℝ φ x v) μ :=
    ((hA i hi).mul (r := p) (Lp.memLp (Y i))).locallyIntegrable hp
      |>.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ v)
  have hJ (i) (hi : i ∈ s) : Integrable (fun x => Q i x * φ x) μ :=
    (hQ i hi).locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  calc
    (∫ x, U x * fderiv ℝ φ x v ∂μ) =
        ∫ x, (∑ i ∈ s, A i x * Y i x) * fderiv ℝ φ x v ∂μ := by
      apply integral_congr_ae
      filter_upwards [hU] with x hx
      rw [hx]
    _ = ∑ i ∈ s, ∫ x, A i x * Y i x * fderiv ℝ φ x v ∂μ := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum s hI
    _ = -∑ i ∈ s, ∫ x, Q i x * φ x ∂μ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_weak_product_deriv hΩ v
        ((Lp.memLp (Y i)).locallyIntegrable hp) ((Lp.memLp (DY i)).locallyIntegrable hp)
        (hAsmooth i hi) (hY i hi) hφ hφc hφs
    _ = -(∫ x, (∑ i ∈ s, Q i x) * φ x ∂μ) := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum s hJ]
    _ = -∫ x, DU x * φ x ∂μ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hsum.coeFn_toLp] with x hx
      rw [hx]

end DifferentialGeometry.Analysis.Sobolev
