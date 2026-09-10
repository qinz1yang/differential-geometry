import DifferentialGeometry.Geometry.Metric.Construction.Existence

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem nonempty_smoothRiemannianMetric_of_compact [CompactSpace M] [T2Space M] :
    Nonempty (Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :=
  DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric

end DifferentialGeometry.Geometry
