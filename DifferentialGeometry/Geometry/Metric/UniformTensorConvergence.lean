import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence







noncomputable section

open Bundle Set Filter Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]



theorem eventually_metric_quad_bounds_of_uniform_convergence
    (G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : MetricCPConvergenceOn (I := 𝓘(ℝ, E)) Set.univ 0 G g g) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      (1 - δ) * g.inner x v v ≤ (G j).inner x v v ∧
        (G j).inner x v v ≤ (1 + δ) * g.inner x v v := by
  let d : ℝ := Module.finrank ℝ E
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  obtain ⟨j₀, hj₀⟩ := hG (δ / (d + 1)) (by positivity)
  filter_upwards [eventually_ge_atTop j₀] with j hj x v
  have hnorm := (metricDerivNorm_le_metricDerivNormSupOn (G j) g x).trans (hj₀ j hj).le
  have hcoef : d * metricDerivNorm 0 (G j) g g x ≤ δ := by
    calc
      _ ≤ d * (δ / (d + 1)) := mul_le_mul_of_nonneg_left hnorm hd
      _ ≤ (d + 1) * (δ / (d + 1)) := by gcongr; linarith
      _ = δ := mul_div_cancel₀ δ (by positivity)
  have hgv : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · subst v; simp only [map_zero, le_refl]
    · exact (g.pos x v hv).le
  have hb := metricQuadFormDiff_le_metricDerivNorm (G j) g g x v
  change |(G j).inner x v v - g.inner x v v| ≤ d * metricDerivNorm 0 (G j) g g x * g.inner x v v at hb
  have herr := abs_le.mp (hb.trans (mul_le_mul_of_nonneg_right hcoef hgv))
  constructor <;> nlinarith only [herr.1, herr.2]

end DifferentialGeometry.Geometry
