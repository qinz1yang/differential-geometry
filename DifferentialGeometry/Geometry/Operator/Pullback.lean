import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
import DifferentialGeometry.Geometry.Metric.PullbackCross

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [T2Space M]

theorem gradientFun_pullbackCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (f : N → Real) (x : M)
    (hf : MDifferentiableAt J 𝓘(Real, Real) f (Φ x)) :
    gradientFun (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
        (f ∘ (Φ : M → N)) x =
      (Φ.mfderivToContinuousLinearEquiv (by simp) x).symm
        (gradientFun (I := J) g f (Φ x)) := by
  have he : mfderiv I J (Φ : M → N) x =
      (Φ.mfderivToContinuousLinearEquiv (by simp) x :
        TangentSpace I x →L[Real] TangentSpace J (Φ x)) :=
    (Φ.mfderivToContinuousLinearEquiv_coe (by simp) (x := x)).symm
  apply (metricFlatEquiv (I := I)
    (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ) x).injective
  ext w
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, gradientFun_eq,
    inner_metricSharp, Diffeomorph.pullbackMetricCross_inner, he,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    gradientFun_eq, inner_metricSharp]
  change mvfderiv (I := I) (f ∘ (Φ : M → N)) x w =
    mvfderiv (I := J) f (Φ x)
      ((Φ.mfderivToContinuousLinearEquiv (by simp) x) w)
  rw [mvfderiv_comp_apply x hf (Φ.contMDiff.mdifferentiableAt (by simp)) w]
  simp only [he]
  rfl

end DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable [SigmaCompactSpace N] [T2Space N] [J.Boundaryless]

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem hessFun_pullbackCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (f : C^∞⟮J, N; Real⟯) (x : M) (v w : TangentSpace I x) :
    hessFun (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
        (f.comp Φ.toContMDiffMap) x v w =
      hessFun (I := J) g f (Φ x)
        (mfderiv I J (Φ : M → N) x v)
        (mfderiv I J (Φ : M → N) x w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  let gΦ := Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ
  let fΦ : C^∞⟮I, M; Real⟯ := f.comp Φ.toContMDiffMap
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun y => gradientFun (I := I) gΦ fΦ y,
      gradFun_contMDiff_total_section (I := I) gΦ fΦ.contMDiff⟩
  let Z : ContMDiffSection J F (∞ : WithTop ℕ∞)
      (TangentSpace J : N → Type _) :=
    ⟨fun q => gradientFun (I := J) g f q,
      gradFun_contMDiff_total_section (I := J) g f.contMDiff⟩
  have hpush :
      (fun q : N => pushFwdSectionCross (I := I) (J := J) Φ Y q) =
        fun q : N => Z q := by
    funext q
    rw [show q = Φ (Φ.symm q) from (Φ.apply_symm_apply q).symm]
    rw [pushFwdSectionCross_apply_at_image]
    have hgrad := gradientFun_pullbackCross
      (I := I) (J := J) g Φ f (Φ.symm q)
      (f.contMDiff.mdifferentiableAt (by simp))
    have hY : Y (Φ.symm q) =
        (Φ.mfderivToContinuousLinearEquiv (by simp) (Φ.symm q)).symm
          (Z (Φ (Φ.symm q))) := by
      change gradientFun (I := I) gΦ (fun y => fΦ y) (Φ.symm q) = _
      rw [show (fun y => fΦ y) = f ∘ (Φ : M → N) by rfl]
      simpa [Z, gΦ] using hgrad
    rw [hY, ← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (Φ.mfderivToContinuousLinearEquiv (by simp) (Φ.symm q)).apply_symm_apply _
  rw [hessFun_eq_cov_grad (I := I) gΦ fΦ.contMDiff x v w]
  rw [hessFun_eq_cov_grad (I := J) g f.contMDiff (Φ x)
    (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x w)]
  change gΦ.inner x
      ((metricCov (I := I) (M := M) gΦ).toFun (fun y => Y y) x v) w = _
  rw [Diffeomorph.pullbackMetricCross_inner]
  rw [metricCov_pullbackCross (I := I) (J := J) g Φ Y x v]
  rw [hpush]
  rfl

end DifferentialGeometry.Geometry.Operator
