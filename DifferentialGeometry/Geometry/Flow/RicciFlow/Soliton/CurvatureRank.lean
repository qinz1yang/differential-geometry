import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalMetric_metricCurvatureOperatorRankAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (hdim : Module.finrank ℝ E = 3) :
    metricCurvatureOperatorRankAt
        (canonicalMetric g f sigma hcomplete hsol ht) x hdim =
      metricCurvatureOperatorRankAt g
        (canonicalFlowDiffeomorph g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) hdim := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Φ := canonicalFlowDiffeomorph g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  have hdim' (y : M) : Module.finrank ℝ (TangentSpace I y) = 3 := by
    rw [show Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E from rfl]
    exact hdim
  rw [canonicalMetric, ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetricCross_eq_localPullMetric,
    metricCurvatureOperatorRankAt_localPull _ _ _ _ (hdim' x) (hdim' (Φ x)),
    metricCurvatureOperatorRankAt_scaleMetric _ _ _ _ (hdim' (Φ x))]

end DifferentialGeometry.PDE.RicciFlow.Soliton
