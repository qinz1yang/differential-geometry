import DifferentialGeometry.Geometry.Metric.LipschitzCurveIntegration



noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def riemannianCurveLength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) : ℝ := (riemannianCurveELength g γ a b).toReal

theorem riemannianCurveLength_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) : 0 ≤ riemannianCurveLength g γ a b := ENNReal.toReal_nonneg



theorem riemannianCurveLength_eq_integral [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y) (a b : ℝ) :
    riemannianCurveLength g γ a b = ∫ t in Icc a b, riemannianCurveSpeed g γ t := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (riemannianCurveSpeed_nonneg g γ))
    (aestronglyMeasurable_riemannianCurveSpeed g hγ).restrict).symm

end DifferentialGeometry.Geometry
