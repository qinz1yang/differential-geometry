import DifferentialGeometry.Analysis.Calculus.LocallyLipschitzExponentialProduct
import DifferentialGeometry.Analysis.Integration.Integral.WeightedTimeDerivative
import Mathlib.Analysis.Calculus.FDeriv.Prod


noncomputable section

namespace DifferentialGeometry.Analysis

open Filter MeasureTheory Set
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {mu : Measure E} [SFinite mu]

theorem integral_exp_neg_mul_time_deriv_add_cometric_nonneg
    {a b : ℝ} (hab : a ≤ b) {Ω : Set (ℝ × E)}
    (w c : ℝ → ℝ) (ell rho R phi : ℝ × E → ℝ)
    (B : ℝ × E → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hw : ∀ z ∈ Ω, 0 ≤ w z.1)
    (hwLip : LocallyLipschitzOn Ω (fun z ↦ w z.1))
    (hellLip : LocallyLipschitzOn Ω ell)
    (hwTime : LocallyLipschitzOn (uIcc a b) w)
    (hellTime : ∀ᵐ x ∂mu,
      LocallyLipschitzOn (uIcc a b) (fun t ↦ ell (t, x)))
    (hwDeriv : ∀ᵐ t ∂volume.restrict (uIoc a b), HasDerivAt w (-c t * w t) t)
    (hellDiff : ∀ᵐ z ∂(volume.restrict (uIoc a b)).prod mu,
      DifferentiableAt ℝ (fun t ↦ ell (t, z.2)) z.1 ∧
      DifferentiableAt ℝ (fun x ↦ ell (z.1, x)) z.2)
    (hrho : ∀ᵐ x ∂mu, AbsolutelyContinuousOnInterval (fun t ↦ rho (t, x)) a b)
    (hrhoDeriv : ∀ᵐ x ∂mu,
      deriv (fun t ↦ rho (t, x)) =ᵐ[volume.restrict (uIoc a b)]
        fun t ↦ R (t, x) * rho (t, x))
    (hphi : ContDiff ℝ 1 phi) (hphiCompact : HasCompactSupport phi)
    (hphiSupport : tsupport phi ⊆ Ω) (hphiNonneg : ∀ z, 0 ≤ phi z)
    (hphiBoundary : ∀ᵐ x ∂mu, phi (a, x) = 0 ∧ phi (b, x) = 0)
    (hweak : ∀ psi : ℝ × E → ℝ, LocallyLipschitzOn Ω psi →
      HasCompactSupport psi → tsupport psi ⊆ Ω → (∀ z, 0 ≤ psi z) →
      Integrable (fun z ↦ rho z *
        ((deriv (fun t ↦ ell (t, z.2)) z.1 +
          B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
            (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2) - R z + c z.1) * psi z +
          B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
            (fderiv ℝ (fun x ↦ psi (z.1, x)) z.2)))
        ((volume.restrict (uIoc a b)).prod mu) →
      0 ≤ ∫ z, rho z *
        ((deriv (fun t ↦ ell (t, z.2)) z.1 +
          B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
            (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2) - R z + c z.1) * psi z +
          B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
            (fderiv ℝ (fun x ↦ psi (z.1, x)) z.2))
        ∂(volume.restrict (uIoc a b)).prod mu)
    (hspace : Integrable (fun z ↦ rho z * (w z.1 * Real.exp (-ell z)) *
      B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
        (fderiv ℝ (fun x ↦ phi (z.1, x)) z.2))
      ((volume.restrict (uIoc a b)).prod mu))
    (htime : Integrable (fun z ↦ rho z *
      (deriv (fun t ↦ w t * Real.exp (-ell (t, z.2))) z.1 +
        R z * (w z.1 * Real.exp (-ell z))) * phi z)
      ((volume.restrict (uIoc a b)).prod mu))
    (htest : Integrable (fun z ↦ rho z * (w z.1 * Real.exp (-ell z)) *
      deriv (fun t ↦ phi (t, z.2)) z.1)
      ((volume.restrict (uIoc a b)).prod mu)) :
    0 ≤ ∫ z, rho z * (w z.1 * Real.exp (-ell z)) *
      (deriv (fun t ↦ phi (t, z.2)) z.1 +
        B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
          (fderiv ℝ (fun x ↦ phi (z.1, x)) z.2))
      ∂(volume.restrict (uIoc a b)).prod mu := by
  let nu := (volume.restrict (uIoc a b)).prod mu
  let u : ℝ × E → ℝ := fun z ↦ w z.1 * Real.exp (-ell z)
  let psi : ℝ × E → ℝ := fun z ↦ u z * phi z
  let spatial : ℝ × E → ℝ := fun z ↦ rho z * u z *
    B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
      (fderiv ℝ (fun x ↦ phi (z.1, x)) z.2)
  let temporal : ℝ × E → ℝ := fun z ↦ rho z *
    (deriv (fun t ↦ u (t, z.2)) z.1 + R z * u z) * phi z
  let tested : ℝ × E → ℝ := fun z ↦ rho z * u z *
    deriv (fun t ↦ phi (t, z.2)) z.1
  let residual : ℝ × E → ℝ := fun z ↦ rho z *
    ((deriv (fun t ↦ ell (t, z.2)) z.1 +
      B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
        (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2) - R z + c z.1) * psi z +
      B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
        (fderiv ℝ (fun x ↦ psi (z.1, x)) z.2))
  have hpsiLip : LocallyLipschitzOn Ω psi :=
    locallyLipschitzOn_mul_exp_neg_mul hwLip hellLip
      hphi.locallyLipschitz.locallyLipschitzOn
  have hpsiCompact : HasCompactSupport psi := hphiCompact.mul_left
  have hpsiSupport : tsupport psi ⊆ Ω :=
    tsupport_mul_subset_right.trans hphiSupport
  have hpsiNonneg : ∀ z, 0 ≤ psi z :=
    mul_exp_neg_mul_nonneg_of_tsupport_subset hw hphiNonneg hphiSupport
  have hphiSpace (t : ℝ) (x : E) : DifferentiableAt ℝ (fun y ↦ phi (t, y)) x :=
    (hphi.differentiable (by norm_num)).differentiableAt.comp x
      ((differentiableAt_const (c := t)).prodMk differentiableAt_id)
  have hnormProd : ∀ᵐ z ∂nu, HasDerivAt w (-c z.1 * w z.1) z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hwDeriv
  have hresidual : residual =ᵐ[nu] fun z ↦ spatial z - temporal z := by
    filter_upwards [hellDiff, hnormProd] with z hz hwz
    have huSpace : DifferentiableAt ℝ (fun x ↦ u (z.1, x)) z.2 :=
      (differentiableAt_const (c := w z.1)).mul hz.2.neg.exp
    have huDeriv : fderiv ℝ (fun x ↦ u (z.1, x)) z.2 =
        -(u z • fderiv ℝ (fun x ↦ ell (z.1, x)) z.2) := by
      simpa only [u, fderiv_const_apply, smul_zero, zero_sub] using
        fderiv_mul_exp_neg (differentiableAt_const (c := w z.1)) hz.2
    have hpsiDeriv : fderiv ℝ (fun x ↦ psi (z.1, x)) z.2 =
        u z • fderiv ℝ (fun x ↦ phi (z.1, x)) z.2 +
          phi z • (-(u z • fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)) := by
      rw [show (fun x ↦ psi (z.1, x)) =
        (fun x ↦ u (z.1, x) * phi (z.1, x)) from rfl]
      rw [fderiv_fun_mul huSpace (hphiSpace z.1 z.2), huDeriv]
    have huTimeDeriv : deriv (fun t ↦ u (t, z.2)) z.1 =
        -u z * (deriv (fun t ↦ ell (t, z.2)) z.1 + c z.1) := by
      have hh := hwz.mul hz.1.hasDerivAt.neg.exp
      change HasDerivAt (fun t => u (t, z.2)) _ z.1 at hh
      rw [hh.deriv]
      dsimp only [u, Pi.neg_apply]
      ring
    dsimp only [residual, spatial, temporal]
    rw [hpsiDeriv, huTimeDeriv]
    dsimp only [psi]
    simp only [map_add, map_smul, map_neg, smul_eq_mul]
    ring
  have hspatial : Integrable spatial nu := hspace
  have htemporal : Integrable temporal nu := htime
  have htested : Integrable tested nu := htest
  have hresInt : Integrable residual nu :=
    (hspatial.sub htemporal).congr hresidual.symm
  have hnonneg : 0 ≤ ∫ z, residual z ∂nu :=
    hweak psi hpsiLip hpsiCompact hpsiSupport hpsiNonneg hresInt
  have huLip : ∀ᵐ x ∂mu,
      LocallyLipschitzOn (uIcc a b) (fun t ↦ u (t, x)) :=
    hellTime.mono fun x hx ↦ locallyLipschitzOn_mul_exp_neg hwTime hx
  have hphiTime : ∀ᵐ x ∂mu,
      AbsolutelyContinuousOnInterval (fun t ↦ phi (t, x)) a b := by
    apply Eventually.of_forall
    intro x
    have hc : ContDiff ℝ 1 (fun t ↦ phi (t, x)) :=
      hphi.comp (contDiff_id.prodMk contDiff_const)
    exact hc.locallyLipschitz.locallyLipschitzOn.absolutelyContinuousOnInterval
  have hparts := integral_integral_weighted_time_deriv_of_locallyLipschitzOn
    huLip hrho hphiTime hrhoDeriv hphiBoundary htime htest
  have htemporalEq : (∫ z, temporal z ∂nu) = -(∫ z, tested z ∂nu) := by
    rw [integral_prod temporal htemporal, integral_prod tested htested]
    simpa only [intervalIntegral.integral_of_le hab, uIoc_of_le hab,
      temporal, tested, u] using hparts
  have hresEq : (∫ z, residual z ∂nu) =
      (∫ z, spatial z ∂nu) + ∫ z, tested z ∂nu := by
    rw [integral_congr_ae hresidual, integral_sub hspatial htemporal,
      htemporalEq, sub_neg_eq_add]
  rw [hresEq] at hnonneg
  have hfinal : (∫ z, spatial z ∂nu) + ∫ z, tested z ∂nu =
      ∫ z, rho z * u z *
        (deriv (fun t ↦ phi (t, z.2)) z.1 +
          B z (fderiv ℝ (fun x ↦ ell (z.1, x)) z.2)
            (fderiv ℝ (fun x ↦ phi (z.1, x)) z.2)) ∂nu := by
    rw [← integral_add hspatial htested]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      dsimp only [spatial, tested]
      ring
  rwa [hfinal] at hnonneg

end DifferentialGeometry.Analysis
