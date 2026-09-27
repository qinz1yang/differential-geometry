import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Operator.Pullback

namespace DifferentialGeometry.Geometry.Operator

open scoped _root_.Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem normGradSqFun_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F)
    (f : M → ℝ) (x : M) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    normGradSqFun (g.transContinuousLinearEquiv e) f x = normGradSqFun g f x := by
  let Φ := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm
  change normGradSqFun (Diffeomorph.pullbackMetricCross g Φ) (f ∘ Φ) x = _
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  exact normGradSqFun_localPull g Φ Φ.isLocalDiffeomorph f x hf

theorem mfderiv_gradientFun_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F)
    (f : M → ℝ) (x : M) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    mfderiv (I.transContinuousLinearEquiv e) I id x (gradientFun (g.transContinuousLinearEquiv e) f x) =
      gradientFun g f x := by
  let Φ := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm
  change mfderiv (I.transContinuousLinearEquiv e) I Φ x
    (gradientFun (Diffeomorph.pullbackMetricCross g Φ) (f ∘ Φ) x) = _
  rw [gradientFun_pullbackCross g Φ f x hf,
    ← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (Φ.mfderivToContinuousLinearEquiv (by simp) x).apply_symm_apply _

end

end DifferentialGeometry.Geometry.Operator
