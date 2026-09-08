import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SourceFormula
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal BigOperators
namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem ae_eq_of_gradient_source_test_decomposition
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {Ω : Set E} (hΩ : IsOpen Ω)
    {J : Set ℝ} (hJ : IsOpen J) (hμJ : ∀ᵐ t ∂μ, t ∈ J)
    {F Fdiv Fsrc corr : Lp ℝ 2 (μ.prod (volume.restrict Ω))}
    {ρ : ℝ × E → ℝ} {A : Fin d → Fin d → ℝ × E → ℝ}
    {H : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω))}
    {DA : Fin d → Fin d → ℝ × E → ℝ} {V : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω))}
    {S : ℝ × E → ℝ} {k : Fin d}
    (hmain : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω)) =
        (∑ i, ∑ j, ∫ p, A i j p * H i k p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) -
          ∫ p, F p * φ p ∂μ.prod (volume.restrict Ω))
    (hbridge : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω)) =
        (∑ i, ∑ j, ∫ p, (A i j p * H i k p + DA i j p * V i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) +
          ∫ p, S p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂μ.prod (volume.restrict Ω) +
          ∫ p, corr p * φ p ∂μ.prod (volume.restrict Ω))
    (hsplit : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∑ i, ∑ j, ∫ p, (A i j p * H i k p + DA i j p * V i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) =
        (∑ i, ∑ j, ∫ p, A i j p * H i k p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) +
        ∑ i, ∑ j, ∫ p, DA i j p * V i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω))
    (hDtest : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ p, Fdiv p * φ p ∂μ.prod (volume.restrict Ω)) =
        -∑ i, ∑ j, ∫ p, DA i j p * V i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω))
    (hStest : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ p, Fsrc p * φ p ∂μ.prod (volume.restrict Ω)) =
        -∫ p, S p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂μ.prod (volume.restrict Ω)) :
    F =ᵐ[μ.prod (volume.restrict Ω)] fun p => Fdiv p + Fsrc p - corr p := by
  have hmem : ∀ᵐ p ∂μ.prod (volume.restrict Ω), p ∈ J ×ˢ Ω := by
    apply (Measure.ae_prod_iff_ae_ae (hJ.measurableSet.prod hΩ.measurableSet)).mpr
    filter_upwards [hμJ] with t ht
    exact (ae_restrict_mem hΩ.measurableSet).mono fun x hx => ⟨ht, hx⟩
  have hFli : LocallyIntegrable (F : ℝ × E → ℝ) (μ.prod (volume.restrict Ω)) :=
    (Lp.memLp F).locallyIntegrable (by norm_num)
  have hGli : LocallyIntegrable (fun p => Fdiv p + Fsrc p - corr p)
      (μ.prod (volume.restrict Ω)) :=
    (((Lp.memLp Fdiv).add (Lp.memLp Fsrc)).sub (Lp.memLp corr)).locallyIntegrable (by norm_num)
  apply ae_eq_of_integral_contDiff_mul_eq_on (hJ.prod hΩ) hmem hFli hGli
  intro φ hφ hφc hφs
  have hm := hmain φ hφ hφc hφs
  have hb := hbridge φ hφ hφc hφs
  have hs := hsplit φ hφ hφc hφs
  have hd := hDtest φ hφ hφc hφs
  have hsrc := hStest φ hφ hφc hφs
  have hφint (W : Lp ℝ 2 (μ.prod (volume.restrict Ω))) : Integrable (fun p => W p * φ p) (μ.prod (volume.restrict Ω)) :=
    (Lp.memLp W).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
  have hcand : (∫ p, (Fdiv p + Fsrc p - corr p) * φ p ∂μ.prod (volume.restrict Ω)) =
      (∫ p, Fdiv p * φ p ∂μ.prod (volume.restrict Ω)) + ∫ p, Fsrc p * φ p ∂μ.prod (volume.restrict Ω) - ∫ p, corr p * φ p ∂μ.prod (volume.restrict Ω) := by
    let gD : ℝ × E → ℝ := fun p => Fdiv p * φ p
    let gS : ℝ × E → ℝ := fun p => Fsrc p * φ p
    let gC : ℝ × E → ℝ := fun p => corr p * φ p
    have hDint : Integrable gD (μ.prod (volume.restrict Ω)) := by exact hφint Fdiv
    have hSint : Integrable gS (μ.prod (volume.restrict Ω)) := by exact hφint Fsrc
    have hCint : Integrable gC (μ.prod (volume.restrict Ω)) := by exact hφint corr
    calc
      (∫ p, (Fdiv p + Fsrc p - corr p) * φ p ∂μ.prod (volume.restrict Ω)) =
          ∫ p, (gD p + gS p - gC p) ∂μ.prod (volume.restrict Ω) := by
            apply integral_congr_ae
            filter_upwards with p
            simp [gD, gS, gC, sub_mul, add_mul]
      _ = (∫ p, gD p ∂μ.prod (volume.restrict Ω)) + ∫ p, gS p ∂μ.prod (volume.restrict Ω) - ∫ p, gC p ∂μ.prod (volume.restrict Ω) := by
            have hsub := integral_sub (hDint.add hSint) hCint
            have hadd := integral_add hDint hSint
            have hadd' : (∫ a, (gD + gS) a ∂μ.prod (volume.restrict Ω)) =
                (∫ a, gD a ∂μ.prod (volume.restrict Ω)) + ∫ a, gS a ∂μ.prod (volume.restrict Ω) := by
              simpa only [Pi.add_apply] using hadd
            rw [hadd'] at hsub
            simpa only [Pi.add_apply, Pi.sub_apply] using hsub
      _ = _ := by rfl
  rw [hcand]
  have hmainEq : (∫ p, F p * φ p ∂μ.prod (volume.restrict Ω)) =
      -(∑ i, ∑ j, ∫ p, DA i j p * V i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) -
        ∫ p, S p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂μ.prod (volume.restrict Ω) -
        ∫ p, corr p * φ p ∂μ.prod (volume.restrict Ω) := by
    linarith [hm, hb, hs]
  rw [hmainEq, hd, hsrc]
  ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
