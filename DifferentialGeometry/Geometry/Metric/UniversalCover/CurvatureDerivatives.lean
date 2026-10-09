import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

section UniversalCoverLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem curvDerivNorm_liftedMetric
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x' : UniversalCover M) :
    curvDerivNorm (I := I) m (UniversalCover.liftedMetric (I := I) g) x' =
      curvDerivNorm (I := I) m g (UniversalCover.proj x') := by
  let hf : IsLocalDiffeomorph I I ∞ (UniversalCover.proj : UniversalCover M → M) :=
    UniversalCover.proj_localDiffeo (I := I) (M := M)
  have hmetric : UniversalCover.liftedMetric (I := I) g =
      localPullMetric g UniversalCover.proj hf := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, (UniversalCover.hasMFDerivAt_proj (I := I) y).mfderiv]
    rfl
  rw [hmetric]
  exact curvDerivNorm_localPullMetric g UniversalCover.proj hf m x'

end UniversalCoverLift

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
