import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelBallTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open KappaSolutions
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {D : RealTimeInterval}

private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)

theorem FlowMetricBall.isSpatiallyKappaNoncollapsed_pullback
    (S : SolutionOn (I := J) (M := N) D) (Phi : M ≃ₘ⟮I, J⟯ N)
    {kappa : ℝ} {time : D.FlowTime}
    (hNC : ∀ B : FlowMetricBall S time, B.IsSpatiallyKappaNoncollapsed kappa)
    (B : FlowMetricBall (S.pullback Phi) time) :
    B.IsSpatiallyKappaNoncollapsed kappa := by
  intro hB
  let B' : FlowMetricBall S time := ⟨Phi B.center, B.radius, B.radius_pos⟩
  have hB' : B'.IsSpatiallyRmControlled := by
    intro y hy
    change y ∈ riemannianBallOf (I := J) (S.base.metric (time : ℝ))
      (Phi B.center) B.radius at hy
    rw [← image_riemannianBallOf_pullbackMetricCross
      (S.base.metric (time : ℝ)) Phi B.center B.radius] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzB : z ∈ B.set := hz
    have h := hB z hzB
    change B.radius ^ 4 * normSq0S (I := I)
      (Diffeomorph.pullbackMetricCross (S.base.metric (time : ℝ)) Phi) z 4
      (metricRm04At (I := I)
        (Diffeomorph.pullbackMetricCross (S.base.metric (time : ℝ)) Phi) z) ≤ 1 at h
    rw [DifferentialGeometry.CheegerGromovCompactness.riemannNormSq_cross] at h
    exact h
  have hNC' := hNC B' hB'
  refine ⟨hNC'.1, ?_⟩
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F :=
    (Diffeomorph.mfderivToContinuousLinearEquiv Phi (by decide) B.center).toLinearEquiv.finrank_eq
  change ENNReal.ofReal kappa * ENNReal.ofReal B.radius ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := M)
      (Diffeomorph.pullbackMetricCross (S.base.metric (time : ℝ)) Phi)
      (riemannianBallOf (I := I)
        (Diffeomorph.pullbackMetricCross (S.base.metric (time : ℝ)) Phi) B.center B.radius)
  rw [hdim, riemannianBallOf_volume_pullbackMetricCross]
  exact hNC'.2

end DifferentialGeometry.PDE.RicciFlow.Perelman
