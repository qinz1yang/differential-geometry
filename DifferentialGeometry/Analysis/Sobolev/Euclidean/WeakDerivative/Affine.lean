import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeAffine
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace DeGiorgi

open scoped InnerProductSpace

theorem HasWeakGrad.integral_mul_fderiv
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {U : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : HasWeakGrad G U Ω) (hU : LocallyIntegrableOn U Ω volume)
    (hG : LocallyIntegrableOn G Ω volume) (v : EuclideanSpace ℝ (Fin d))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, U x * fderiv ℝ φ x v) = -∫ x in Ω, ⟪G x, v⟫_ℝ * φ x := by
  have hint {W ψ : EuclideanSpace ℝ (Fin d) → ℝ}
      (hW : LocallyIntegrableOn W Ω volume) (hψ : Continuous ψ)
      (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
      Integrable (fun x => W x * ψ x) (volume.restrict Ω) := by
    apply Integrable.mono_measure _ Measure.restrict_le_self
    apply (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport (fun x => W x * ψ x)).trans tsupport_mul_subset_right)).mp
    exact (hW.integrableOn_compact_subset hψs hψc).mul_continuousOn hψ.continuousOn hψc
  have hUi (i : Fin d) := hint hU
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hφs)
  have hGi (i : Fin d) : Integrable (fun x => G x i * φ x) (volume.restrict Ω) :=
    hint ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).locallyIntegrableOn_comp hG) hφ.continuous hφc hφs
  have hv : (∑ i, v i • EuclideanSpace.single i 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hd (x) : fderiv ℝ φ x v = ∑ i, v i * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← hv]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hg (x) : ⟪G x, v⟫_ℝ = ∑ i, v i * G x i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  simp only [hd, hg, Finset.mul_sum, Finset.sum_mul]
  have hl (i x) : U x * (v i * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      v i * (U x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by ring
  simp_rw [hl, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hUi i).const_mul (v i)),
    integral_finsetSum _ (fun i _ => (hGi i).const_mul (v i))]
  simp only [integral_const_mul, h _ φ hφ hφc hφs, mul_neg, Finset.sum_neg_distrib]

theorem HasWeakGrad.comp_affineEquiv
    {d m : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin m))
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {U : EuclideanSpace ℝ (Fin m) → ℝ}
    {G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (h : HasWeakGrad G U Ω) (hU : LocallyIntegrableOn U Ω volume)
    (hG : LocallyIntegrableOn G Ω volume) :
    HasWeakGrad (fun x => e.toContinuousAffineMap.contLinear.adjoint (G (e x)))
      (U ∘ e) (e ⁻¹' Ω) := by
  intro i
  have hw := DifferentialGeometry.Analysis.Sobolev.weak_deriv_comp_affineEquiv e
    (μ := volume) (ν := volume) (EuclideanSpace.single i 1)
    (fun φ hφ hφc hφs => h.integral_mul_fderiv hU hG
      (e.toAffineEquiv.linear (EuclideanSpace.single i 1)) hφ hφc hφs)
  have he (y : EuclideanSpace ℝ (Fin m)) :
      ⟪G y, e.toAffineEquiv.linear (EuclideanSpace.single i 1)⟫_ℝ =
        (e.toContinuousAffineMap.contLinear.adjoint (G y)) i := by
    rw [← EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  simpa only [HasWeakPartialDeriv, he, Function.comp_apply] using hw

end DeGiorgi
