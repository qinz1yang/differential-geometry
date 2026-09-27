import DifferentialGeometry.Geometry.Metric.Family.TimeComposition

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem MetricFamilySmoothOn.timeShift
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (τ : ℝ) :
    MetricFamilySmoothOn (D.timeShift τ) (fun t => g (t + τ)) :=
  hg.comp_time (contDiff_id.add contDiff_const).contDiffOn
    (continuous_id.add continuous_const).continuousOn (fun _ hs => hs) (fun _ hs => hs)

end DifferentialGeometry.Geometry.Curvature
