import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem curvCovDeriv_eq_of_metric_eventuallyEq
    (g h : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner y v w) (m : ℕ) :
    curvCovDeriv g m x = curvCovDeriv h m x := by
  obtain ⟨s, hs, hopen, hxs⟩ := mem_nhds_iff.mp hmetric
  let U : Opens M := ⟨s, hopen⟩
  let y : U := ⟨x, hxs⟩
  have heq : g.restrictOpen U = h.restrictOpen U :=
    SmoothRiemannianMetric.ext_inner (fun z v w => hs z.property v w)
  ext slots
  exact (curvCovDeriv_restrictOpen g U m y slots).symm.trans
    ((congrArg (fun k : SmoothRiemannianMetric I U => curvCovDeriv k m y slots) heq).trans
      (curvCovDeriv_restrictOpen h U m y slots))

theorem curvDerivNorm_eq_of_metric_eventuallyEq
    (g h : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner y v w) (m : ℕ) :
    curvDerivNorm m g x = curvDerivNorm m h x := by
  obtain ⟨s, hs, hopen, hxs⟩ := mem_nhds_iff.mp hmetric
  let U : Opens M := ⟨s, hopen⟩
  let y : U := ⟨x, hxs⟩
  have heq : g.restrictOpen U = h.restrictOpen U :=
    SmoothRiemannianMetric.ext_inner (fun z v w => hs z.property v w)
  exact (curvDerivNorm_restrictOpen g U m y).symm.trans
    ((congrArg (fun k : SmoothRiemannianMetric I U => curvDerivNorm m k y) heq).trans
      (curvDerivNorm_restrictOpen h U m y))

theorem curvDerivNormSq_eq_of_metric_eventuallyEq
    (g h : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner y v w) (m : ℕ) :
    curvDerivNormSq m g x = curvDerivNormSq m h x := by
  have hh := congrArg (fun t : ℝ => t ^ 2)
    (curvDerivNorm_eq_of_metric_eventuallyEq g h x hmetric m)
  simpa only [curvDerivNorm, curvDerivNormSq,
    Real.sq_sqrt (Tensor0SBundle.normSq0S_nonneg _ _ _ _)] using hh


end DifferentialGeometry.CheegerGromovCompactness
