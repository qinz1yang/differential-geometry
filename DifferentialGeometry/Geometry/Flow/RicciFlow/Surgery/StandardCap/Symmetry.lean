import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Pullback.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory DifferentialGeometry
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem mfderiv_linearIsometryEquiv (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (f : E3 → E3) x v =
      (show TangentSpace (𝓡 3) (f x) from f v) := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (f : E3 → E3) x v = f v
  exact congrArg (fun D : E3 →L[ℝ] E3 => D v) f.toContinuousLinearEquiv.hasFDerivAt.fderiv

theorem metric_pullback_linearIsometryEquiv (f : E3 ≃ₗᵢ[ℝ] E3) :
    Diffeomorph.pullbackMetric metric f.toContinuousLinearEquiv.toDiffeomorph = metric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change metric.inner (f x)
    (mfderiv (𝓡 3) (𝓡 3) (f : E3 → E3) x v)
    (mfderiv (𝓡 3) (𝓡 3) (f : E3 → E3) x w) = metric.inner x v w
  rw [mfderiv_linearIsometryEquiv, mfderiv_linearIsometryEquiv]
  exact metric_inner_linearIsometry f.toLinearIsometry x v w

private theorem edist_linearIsometryEquiv_le (f : E3 ≃ₗᵢ[ℝ] E3) (x y : E3) :
    riemannianEDistOf metric (f x) (f y) ≤ riemannianEDistOf metric x y := by
  have hf : ContMDiff (𝓡 3) (𝓡 3) 1 (f : E3 → E3) :=
    f.toContinuousLinearEquiv.contDiff.contMDiff
  rw [edistOf_iInf metric x y]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let η : Path (f x) (f y) := γ.map f.continuous
  have hη : ContMDiff (𝓡∂ 1) (𝓡 3) 1 η := hf.comp hγ
  have hle : riemannianEDistOf metric (f x) (f y) ≤
      ∫⁻ t, ENNReal.ofReal (Real.sqrt
        (metric.inner (η t) (mfderiv (𝓡∂ 1) (𝓡 3) η t 1) (mfderiv (𝓡∂ 1) (𝓡 3) η t 1))) := by
    rw [edistOf_iInf]
    exact iInf_le_of_le η (iInf_le_of_le hη le_rfl)
  apply hle.trans_eq
  apply lintegral_congr
  intro t
  have hd : mfderiv (𝓡∂ 1) (𝓡 3) η t 1 = f (mfderiv (𝓡∂ 1) (𝓡 3) γ t 1) := by
    change mfderiv (𝓡∂ 1) (𝓡 3) ((f : E3 → E3) ∘ γ) t 1 = _
    rw [mfderiv_comp t (hf.mdifferentiable one_ne_zero (γ t))
      (hγ.mdifferentiable one_ne_zero t), ContinuousLinearMap.comp_apply,
      mfderiv_linearIsometryEquiv]
  rw [hd]
  exact congrArg (fun r : ℝ => ENNReal.ofReal (Real.sqrt r))
    (metric_inner_linearIsometry f.toLinearIsometry (γ t) _ _)

theorem edist_linearIsometryEquiv (f : E3 ≃ₗᵢ[ℝ] E3) (x y : E3) :
    riemannianEDistOf metric (f x) (f y) = riemannianEDistOf metric x y := by
  apply le_antisymm (edist_linearIsometryEquiv_le f x y)
  simpa only [f.symm_apply_apply] using edist_linearIsometryEquiv_le f.symm (f x) (f y)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
