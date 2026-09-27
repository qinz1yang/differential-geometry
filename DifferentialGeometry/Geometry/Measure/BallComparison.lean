import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false
noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_ball_le_of_inner_bounds
    (g h : SmoothRiemannianMetric I M) {C D : ℝ} (hC : 0 < C) (hD : 0 < D)
    (p : M) (r : ℝ)
    (hlower : ∀ x ∈ riemannianBallOf g p r, ∀ v : TangentSpace I x,
      g.inner x v v ≤ C * h.inner x v v)
    (hupper : ∀ x : M, ∀ v : TangentSpace I x,
      h.inner x v v ≤ D * g.inner x v v) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p r) ≤
      ENNReal.ofReal (Real.sqrt (C ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure I M h (riemannianBallOf h p (Real.sqrt D * r)) := by
  have hmeas : MeasurableSet (riemannianBallOf g p r) :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g p)
      continuous_const).measurableSet
  have hsub : riemannianBallOf g p r ⊆ riemannianBallOf h p (Real.sqrt D * r) := by
    intro x hx
    change riemannianEDistOf h p x < ENNReal.ofReal (Real.sqrt D * r)
    have hdist := edistOf_le_of_quad g h hD hupper p x
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg D)]
    exact hdist.trans_lt ((ENNReal.mul_lt_mul_iff_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hD)))
      ENNReal.ofReal_ne_top).mpr hx)
  exact (riemannianVolumeMeasure_apply_le_of_inner_le h g hC hmeas hlower).trans
    (mul_le_mul' le_rfl (measure_mono hsub))

section

theorem riemannianVolumeMeasure_ball_ge_scaleMetric_iff
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) (κ : ℝ≥0∞) :
    κ * ENNReal.ofReal (Real.sqrt c * r) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure I M (scaleMetric c hc g)
        (riemannianBallOf (scaleMetric c hc g) p (Real.sqrt c * r)) ↔
    κ * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  rw [riemannianBallOf_scaleMetric, volume_scale_apply,
    ENNReal.ofReal_mul (Real.sqrt_nonneg c), mul_pow]
  rw [← mul_assoc, mul_comm κ, mul_assoc]
  exact ENNReal.mul_le_mul_iff_right
    (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc))))
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

end

end DifferentialGeometry.Geometry.Measure
