import DifferentialGeometry.Geometry.Curvature.PositiveSectional
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

theorem sectional_quotient_localPull (g : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (x : M)
    (v w : TangentSpace I x) :
    let h := localPullMetric g f hf
    metricRm04StandardAt h x v w w v /
        (h.inner x v v * h.inner x w w - h.inner x v w ^ 2) =
      metricRm04StandardAt g (f x) (mfderiv I J f x v) (mfderiv I J f x w)
          (mfderiv I J f x w) (mfderiv I J f x v) /
        (g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) *
          g.inner (f x) (mfderiv I J f x w) (mfderiv I J f x w) -
          g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) ^ 2) := by
  dsimp only
  rw [metricRm04StandardAt_localPullMetric, localPullMetric_inner,
    localPullMetric_inner, localPullMetric_inner]

theorem HasPositiveSectionalCurvature.localPull {g : SmoothRiemannianMetric J N}
    (hg : HasPositiveSectionalCurvature g) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) :
    HasPositiveSectionalCurvature (localPullMetric g f hf) := by
  intro x v w hvw
  rw [metricRm04StandardAt_localPullMetric]
  apply hg
  let D := hf.mfderivToContinuousLinearEquiv (by decide) x
  have hD : LinearIndependent ℝ (D.toLinearMap ∘ ![v, w]) :=
    hvw.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr D.injective)
  convert hD using 1
  ext i
  fin_cases i <;> rfl

end DifferentialGeometry.Geometry
