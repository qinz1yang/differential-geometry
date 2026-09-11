import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Topology.Manifold.ModelWithCorners

namespace DifferentialGeometry.SmoothRiemannianMetric

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) :
    SmoothRiemannianMetric (I.transContinuousLinearEquiv e) M :=
  Diffeomorph.pullbackMetricCross g (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm

omit [FiniteDimensional ℝ E] in
theorem transContinuousLinearEquiv_inner
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F)
    (x : M) (v w : TangentSpace (I.transContinuousLinearEquiv e) x) :
    (g.transContinuousLinearEquiv e).inner x v w =
      g.inner x (mfderiv (I.transContinuousLinearEquiv e) I id x v)
        (mfderiv (I.transContinuousLinearEquiv e) I id x w) :=
  Diffeomorph.pullbackMetricCross_inner g
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm x v w

theorem pullback_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) :
    Diffeomorph.pullbackMetricCross (g.transContinuousLinearEquiv e)
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e) = g := by
  rw [transContinuousLinearEquiv, Diffeomorph.pullbackMetricCross_trans]
  have hΦ : (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).trans
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm =
        Diffeomorph.refl I M ∞ := by ext x; rfl
  rw [hΦ, Diffeomorph.pullbackMetricCross_refl]

end

end DifferentialGeometry.SmoothRiemannianMetric
