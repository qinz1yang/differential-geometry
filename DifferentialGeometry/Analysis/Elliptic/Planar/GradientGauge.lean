import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.WeakGaugeContinuous
import DifferentialGeometry.Analysis.Elliptic.Planar.WeakFirstOrderReduction

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ComplexConjugate

namespace DifferentialGeometry.Analysis

/-- The selected gauge cancels the weak equation of the actual augmented gradient.
The local coefficient identity and the ambient coefficient bound are explicit
receiving obligations; neither the scalar nor the selected gauge is replaced. -/
theorem actual_planarGradientSection_inverse_gauge_weak_equation
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (P : C(closedBall a R, (ℂ × ℂ) →L[ℂ] ℂ × ℂ))
    (P₀ A : ℂ → (ℂ × ℂ) →L[ℂ] ℂ × ℂ)
    (hrep : ∀ z : closedBall a R, P₀ z = P z)
    (hA : AEStronglyMeasurable A volume)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hC : 0 ≤ C)
    (hnear : ∀ z ∈ closedBall a R, ‖P₀ z - 1‖ ≤ δ)
    (hbound : ∀ z, ‖A z‖ ≤ C)
    (hPweak : ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a R →
      (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) =
      -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ))))
    (v S : ℂ → ℝ) (hv : ContDiffOn ℝ 1 v (ball a R))
    (hS : LocallyIntegrableOn S (ball a R) volume)
    (hscalar : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a R →
      (∫ z in ball a R, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) =
        ∫ z in ball a R, S z * φ z)
    (hcoefficient : ∀ z ∈ ball a R, A z (planarGradientSection v z) =
      (-(S z : ℂ) / 4, conj (planarComplexGradient v z))) :
    ContinuousOn (fun z => Ring.inverse (P₀ z) (planarGradientSection v z))
        (ball a (R / 2)) ∧
      ∀ (φ : ℂ → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball a (R / 2) →
        (∫ z, complexDbar φ z • Ring.inverse (P₀ z) (planarGradientSection v z)) = 0 := by
  have hDv := hv.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hgrad : ContinuousOn (planarComplexGradient v) (ball a R) :=
    Complex.equivRealProdCLM.symm.continuous.comp_continuousOn
      (((hDv.clm_apply continuousOn_const).div_const 2).prodMk
        ((hDv.clm_apply continuousOn_const).neg.div_const 2))
  have hsection : ContinuousOn (planarGradientSection v) (ball a R) :=
    hgrad.prodMk (Complex.continuous_ofReal.comp_continuousOn hv.continuousOn)
  apply disk_gauge_inverse_continuous_section_weak_equation a R hR P P₀ A
    hrep hA hδ0 hδ hC hnear hbound hPweak (planarGradientSection v) hsection
  intro φ hφ hc hs
  have hh := (integral_realTestDbar_smul_planarGradientSection_of_weak_laplacian
    isOpen_ball hv hS hscalar hφ hc hs).2.2
  rw [hh]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ ball a R
  · rw [hcoefficient z hz]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))]
    simp only [Complex.ofReal_zero, zero_smul]

end DifferentialGeometry.Analysis
