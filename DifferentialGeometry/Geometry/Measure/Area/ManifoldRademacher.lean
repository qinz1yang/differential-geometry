import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource












noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M]

theorem exists_open_ae_mdifferentiableAt_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (z : ℂ) : ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᵐ w ∂volume, w ∈ U → MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u w :=
  exists_open_ae_mdifferentiableAt_of_metric_lipschitz g hu z



theorem ae_mdifferentiableAt_of_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    ∀ᵐ z ∂volume, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z :=
  ae_mdifferentiableAt_of_metric_lipschitz g hu

end DifferentialGeometry.Geometry
