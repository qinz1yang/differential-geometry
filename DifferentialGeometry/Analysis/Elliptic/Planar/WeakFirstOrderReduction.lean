import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate

namespace DifferentialGeometry.Analysis

private theorem integrable_continuousOn_mul_test
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f φ : ℂ → ℝ}
    (hf : ContinuousOn f Ω) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => f z * φ z) :=
  ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hΩ
    (tsupport_mul_subset_right.trans hs)).integrable_of_hasCompactSupport hc.mul_left

private theorem integrable_locallyIntegrableOn_mul_test
    {Ω : Set ℂ} {f φ : ℂ → ℝ}
    (hf : LocallyIntegrableOn f Ω) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => f z * φ z) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f φ).trans (subset_tsupport φ))).mp
  exact (hf.integrableOn_compact_subset hs hc).mul_continuousOn hφ.continuousOn hc

private theorem integral_mul_fderiv_test
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v φ : ℂ → ℝ}
    (hv : ContDiffOn ℝ 1 v Ω) (e : ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ z, v z * fderiv ℝ φ z e) = -∫ z, fderiv ℝ v z e * φ z := by
  have hDv : ContinuousOn (fun z => fderiv ℝ v z e) Ω :=
    (hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hDφ : Continuous (fun z => fderiv ℝ φ z e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_continuousOn_mul_test hΩ hDv hφ.continuous hc hs)
    (integrable_continuousOn_mul_test hΩ hv.continuousOn hDφ
      (hc.fderiv_apply ℝ e) ((tsupport_fderiv_apply_subset ℝ e).trans hs))
    (integrable_continuousOn_mul_test hΩ hv.continuousOn hφ.continuous hc hs)
    (fun z hz => (hv.contDiffAt (hΩ.mem_nhds (hs hz))).differentiableAt one_ne_zero)
    (fun z _ => hφ.differentiable (by simp) z)

/-- The weak scalar equation `Δv + S = 0` gives the weak `∂bar` equation for the
literal augmented gradient of the same `C¹` scalar. The first component of the
right-hand side is `-S/4` and the second is the conjugate complex gradient.
Mixed derivatives are commuted weakly; no classical second derivative is assumed. -/
theorem integral_realTestDbar_smul_planarGradientSection_of_weak_laplacian
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v S : ℂ → ℝ}
    (hv : ContDiffOn ℝ 1 v Ω) (hS : LocallyIntegrableOn S Ω)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ z in Ω, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) =
      ∫ z in Ω, S z * φ z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z : ℂ =>
      (((fderiv ℝ φ z 1 : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
        planarGradientSection v z) ∧
    Integrable (fun z : ℂ =>
      (φ z : ℂ) • (-(S z : ℂ) / 4, conj (planarComplexGradient v z))) ∧
    (∫ z : ℂ,
      (((fderiv ℝ φ z 1 : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
        planarGradientSection v z) =
      -(∫ z : ℂ,
        (φ z : ℂ) • (-(S z : ℂ) / 4, conj (planarComplexGradient v z))) := by
  let u : ℂ → ℝ := fun z => fderiv ℝ v z 1
  let t : ℂ → ℝ := fun z => fderiv ℝ v z Complex.I
  let x : ℂ → ℝ := fun z => fderiv ℝ φ z 1
  let y : ℂ → ℝ := fun z => fderiv ℝ φ z Complex.I
  let D : ℂ → ℂ := fun z => ((x z : ℂ) + Complex.I * (y z : ℂ)) / 2
  let g := planarComplexGradient v
  have hu : ContinuousOn u Ω :=
    (hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have ht : ContinuousOn t Ω :=
    (hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hx : Continuous x :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hy : Continuous y :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hxc : HasCompactSupport x := hc.fderiv_apply ℝ 1
  have hyc : HasCompactSupport y := hc.fderiv_apply ℝ Complex.I
  have hxs : tsupport x ⊆ Ω := (tsupport_fderiv_apply_subset ℝ 1).trans hs
  have hys : tsupport y ⊆ Ω := (tsupport_fderiv_apply_subset ℝ Complex.I).trans hs
  have hux := integrable_continuousOn_mul_test hΩ hu hx hxc hxs
  have hty := integrable_continuousOn_mul_test hΩ ht hy hyc hys
  have huy := integrable_continuousOn_mul_test hΩ hu hy hyc hys
  have htx := integrable_continuousOn_mul_test hΩ ht hx hxc hxs
  have hvx := integrable_continuousOn_mul_test hΩ hv.continuousOn hx hxc hxs
  have hvy := integrable_continuousOn_mul_test hΩ hv.continuousOn hy hyc hys
  have hup := integrable_continuousOn_mul_test hΩ hu hφ.continuous hc hs
  have htp := integrable_continuousOn_mul_test hΩ ht hφ.continuous hc hs
  have hSp := integrable_locallyIntegrableOn_mul_test hS hφ.continuous hc hs
  have hcomm : (∫ z, u z * y z) = ∫ z, t z * x z :=
    Sobolev.integral_weak_deriv_fderiv_comm (Ω := Ω) (μ := volume) 1 Complex.I
      (fun ψ hψ hψc hψs => integral_mul_fderiv_test hΩ hv 1 hψ hψc hψs)
      (fun ψ hψ hψc hψs => integral_mul_fderiv_test hΩ hv Complex.I hψ hψc hψs)
      hφ hc hs
  have hcurl : (∫ z, u z * y z - t z * x z) = 0 := by
    rw [integral_sub huy htx, hcomm, sub_self]
  have hpde : (∫ z, u z * x z + t z * y z) = ∫ z, S z * φ z := by
    have hh := hweak φ hφ hc hs
    change (∫ z in Ω, u z * x z + t z * y z) = ∫ z in Ω, S z * φ z at hh
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero] at hh
    · exact hh
    · intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), mul_zero]
    · intro z hz
      have hzx : x z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hxs h))
      have hzy : y z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hys h))
      rw [hzx, hzy, mul_zero, mul_zero, add_zero]
  have hgrad (z : ℂ) :
      D z * g z = (((u z * x z + t z * y z : ℝ) : ℂ) / 4) +
        Complex.I * (((u z * y z - t z * x z : ℝ) : ℂ) / 4) := by
    apply Complex.ext <;>
      simp [D, g, planarComplexGradient, u, t, Complex.mul_re, Complex.mul_im] <;> ring
  have hvalue (z : ℂ) :
      D z * (v z : ℂ) = (((v z * x z : ℝ) : ℂ) / 2) +
        Complex.I * (((v z * y z : ℝ) : ℂ) / 2) := by
    simp only [D, Complex.ofReal_mul]
    ring
  have hconj (z : ℂ) :
      (φ z : ℂ) * conj (g z) = (((u z * φ z : ℝ) : ℂ) / 2) +
        Complex.I * (((t z * φ z : ℝ) : ℂ) / 2) := by
    apply Complex.ext <;>
      simp [g, planarComplexGradient, u, t, Complex.mul_re, Complex.mul_im] <;> ring
  have hsource (z : ℂ) :
      (φ z : ℂ) * (-(S z : ℂ) / 4) = -(((S z * φ z : ℝ) : ℂ) / 4) := by
    simp only [Complex.ofReal_mul]
    ring
  have hgi : Integrable (fun z => D z * g z) := by
    simp_rw [hgrad]
    exact ((hux.add hty).ofReal.div_const 4).add
      (((huy.sub htx).ofReal.div_const 4).const_mul Complex.I)
  have hvi : Integrable (fun z => D z * (v z : ℂ)) := by
    simp_rw [hvalue]
    exact (hvx.ofReal.div_const 2).add ((hvy.ofReal.div_const 2).const_mul Complex.I)
  have hfi : Integrable (fun z => (φ z : ℂ) * (-(S z : ℂ) / 4)) := by
    simp_rw [hsource]
    exact (hSp.ofReal.div_const 4).neg
  have hci : Integrable (fun z => (φ z : ℂ) * conj (g z)) := by
    simp_rw [hconj]
    exact (hup.ofReal.div_const 2).add ((htp.ofReal.div_const 2).const_mul Complex.I)
  have hfirst : (∫ z, D z * g z) = -∫ z, (φ z : ℂ) * (-(S z : ℂ) / 4) := by
    simp_rw [hgrad, hsource]
    have hsplit :
        (∫ z, (((u z * x z + t z * y z : ℝ) : ℂ) / 4) +
          Complex.I * (((u z * y z - t z * x z : ℝ) : ℂ) / 4)) =
        (∫ z, (((u z * x z + t z * y z : ℝ) : ℂ) / 4)) +
          ∫ z, Complex.I * (((u z * y z - t z * x z : ℝ) : ℂ) / 4) := by
      simpa only [Pi.add_apply, Pi.sub_apply] using!
        integral_add ((hux.add hty).ofReal.div_const 4)
          (((huy.sub htx).ofReal.div_const 4).const_mul Complex.I)
    rw [hsplit, integral_const_mul, integral_div, integral_div, integral_complex_ofReal,
      integral_complex_ofReal, hpde, hcurl, integral_neg, integral_div,
      integral_complex_ofReal]
    simp
  have hsecond : (∫ z, D z * (v z : ℂ)) = -∫ z, (φ z : ℂ) * conj (g z) := by
    have hxv : (∫ z, v z * x z) = -∫ z, u z * φ z :=
      integral_mul_fderiv_test hΩ hv 1 hφ hc hs
    have hyv : (∫ z, v z * y z) = -∫ z, t z * φ z :=
      integral_mul_fderiv_test hΩ hv Complex.I hφ hc hs
    simp_rw [hvalue, hconj]
    have hsplitv :
        (∫ z, (((v z * x z : ℝ) : ℂ) / 2) +
          Complex.I * (((v z * y z : ℝ) : ℂ) / 2)) =
        (∫ z, (((v z * x z : ℝ) : ℂ) / 2)) +
          ∫ z, Complex.I * (((v z * y z : ℝ) : ℂ) / 2) := by
      simpa only [Pi.add_apply] using!
        integral_add (hvx.ofReal.div_const 2)
          ((hvy.ofReal.div_const 2).const_mul Complex.I)
    have hsplitg :
        (∫ z, (((u z * φ z : ℝ) : ℂ) / 2) +
          Complex.I * (((t z * φ z : ℝ) : ℂ) / 2)) =
        (∫ z, (((u z * φ z : ℝ) : ℂ) / 2)) +
          ∫ z, Complex.I * (((t z * φ z : ℝ) : ℂ) / 2) := by
      simpa only [Pi.add_apply] using!
        integral_add (hup.ofReal.div_const 2)
          ((htp.ofReal.div_const 2).const_mul Complex.I)
    rw [hsplitv, hsplitg]
    simp only [integral_const_mul, integral_div, integral_complex_ofReal, hxv, hyv,
      Complex.ofReal_neg]
    ring
  change Integrable (fun z => (D z * g z, D z * (v z : ℂ))) ∧
    Integrable (fun z => ((φ z : ℂ) * (-(S z : ℂ) / 4),
      (φ z : ℂ) * conj (g z))) ∧ _
  refine ⟨hgi.prodMk hvi, hfi.prodMk hci, ?_⟩
  change (∫ z, (D z * g z, D z * (v z : ℂ))) =
    -(∫ z, ((φ z : ℂ) * (-(S z : ℂ) / 4), (φ z : ℂ) * conj (g z)))
  rw [integral_pair hgi hvi, integral_pair hfi hci, hfirst, hsecond]
  rfl

end DifferentialGeometry.Analysis
