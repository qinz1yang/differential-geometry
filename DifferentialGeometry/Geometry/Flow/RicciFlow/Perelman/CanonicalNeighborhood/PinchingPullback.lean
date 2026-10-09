import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature

variable {E F H JH M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace JH]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F JH}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace JH N] [IsManifold J ∞ N] [T2Space N]
  {D : Geometry.Curvature.RealTimeInterval}

theorem PhiAlmostNonnegative.localPullback
    {S : SolutionOn (I := J) (M := N) D} {W : Set ℝ} {Phi : ℝ → ℝ}
    (hS : PhiAlmostNonnegative S W Phi)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) :
    PhiAlmostNonnegative (S.localPullback f hf) W Phi := by
  intro t ht x
  change curvatureOperatorLowerBoundAt
    (localPullMetric (S.base.metric t) f hf) x
    (metricAlgebraicCurvatureTensorAt (localPullMetric (S.base.metric t) f hf) x)
    (Phi (metricScalarAt (localPullMetric (S.base.metric t) f hf) x))
  rw [metricScalarAt_localPull, curvatureOperatorLowerBoundAt_localPullMetric_iff]
  exact hS t ht (f x)

end DifferentialGeometry.PDE.RicciFlow.Perelman
