import DifferentialGeometry.Geometry.Metric.CurveLength
import DifferentialGeometry.Geometry.Metric.ScalarCurveComparison
import DifferentialGeometry.Analysis.Calculus.Variation.Lipschitz
import DifferentialGeometry.Topology.Connected.FiniteEDistance









noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianDistance_le_curveLength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (hab : a ≤ b) :
    (riemannianEDistOf g (γ a) (γ b)).toReal ≤ riemannianCurveLength g γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hγ' : LipschitzWith C γ := hγ
  let ν : ℝ → ℝ := fun t => dist (γ a) (γ t)
  have hν : LipschitzWith C ν := by
    simpa only [one_mul, ν, Function.comp_def] using! (LipschitzWith.dist_right (γ a)).comp hγ'
  have hνac := hν.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hae : ∀ᵐ t ∂volume, deriv ν t ≤ riemannianCurveSpeed g γ t := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ, hν.ae_differentiableAt_real]
      with t ht hνt
    apply (le_abs_self _).trans (abs_deriv_le_of_riemannian_distance_bound g ht hνt ?_)
    intro y
    change |dist (γ a) (γ y) - dist (γ a) (γ t)| ≤ (edist (γ t) (γ y)).toReal
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    simpa only [dist_comm] using abs_dist_sub_le (γ y) (γ t) (γ a)
  let : IsFiniteMeasure (volume.restrict (uIcc a b)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using ((isCompact_uIcc : IsCompact (uIcc a b)).measure_lt_top (μ := volume))⟩
  have hspeed : IntervalIntegrable (riemannianCurveSpeed g γ) volume a b :=
    (integrableOn_riemannianCurveSpeed g hγ (uIcc a b)).intervalIntegrable
  have hle := intervalIntegral.integral_mono_ae hab hνac.intervalIntegrable_deriv hspeed hae
  rw [hνac.integral_deriv_eq_sub] at hle
  have hlen : (∫ t in a..b, riemannianCurveSpeed g γ t) = riemannianCurveLength g γ a b := by
    rw [riemannianCurveLength_eq_integral g hγ,
      intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [hlen] at hle
  change (edist (γ a) (γ b)).toReal ≤ _
  simpa only [ν, dist_self, sub_zero, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hle

end DifferentialGeometry.Geometry
