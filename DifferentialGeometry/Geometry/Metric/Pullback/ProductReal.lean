import DifferentialGeometry.Geometry.Metric.Pullback.Euclidean
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem Diffeomorph.pullbackMetric_euclidean_translation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (c : E) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := E))
      (Topology.translateDiffeomorph c) = euclideanMetric := by
  have hd (x : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (Topology.translateDiffeomorph c) x = ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun y : E => y + c) x = ContinuousLinearMap.id ℝ E
    exact ((hasFDerivAt_id x).add_const c).fderiv
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner, hd, euclideanMetric_inner, euclideanMetric_inner]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem Diffeomorph.pullbackMetricCross_prod_real_translation
    (g : SmoothRiemannianMetric I M) (c : ℝ) :
    Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ)))
      ((Diffeomorph.refl I M ∞).prodCongr (Topology.translateDiffeomorph c)) =
        g.prod (euclideanMetric (E := ℝ)) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl,
    Diffeomorph.pullbackMetric_euclidean_translation]

theorem Diffeomorph.pullbackMetricCross_prod_real_reflection
    (g : SmoothRiemannianMetric I M) :
    Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ)))
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv.toDiffeomorph) =
      g.prod (euclideanMetric (E := ℝ)) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl,
    LinearIsometryEquiv.pullbackMetric_euclidean]

end DifferentialGeometry
