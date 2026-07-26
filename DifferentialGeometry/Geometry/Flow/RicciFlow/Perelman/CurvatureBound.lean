import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing
import DifferentialGeometry.Geometry.Curvature.ScalarNormBound

set_option autoImplicit false

/-!
# Curvature control on Perelman flow balls

This file extracts the scalar-curvature bound needed by the cutoff W-form
estimate from the invariant Riemann norm control in `FlowMetricBall`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle Tensor0SBundle MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- Riemann control on a flow ball gives the corresponding scalar upper bound
at every point of its backward parabolic cylinder. -/
theorem scalar_le_of_rm
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : ℝ} (ht : t ∈ Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ))
    {x : M} (hx : x ∈ B.setAt t) :
    DifferentialGeometry.Integral.Connection.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4) := by
  have hnorm : FlowMetricBall.rmNormSq S t x ≤ 1 / B.radius ^ 4 := by
    apply (le_div_iff₀ (pow_pos B.radius_pos 4)).2
    simpa only [mul_comm] using hB.2 t ht x hx
  have hscalar :=
    DifferentialGeometry.Integral.Connection.scalar_abs_le_rm
      (I := I) (M := M) (S.base.metric t) x
  have hscalar' :
      |DifferentialGeometry.Integral.Connection.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| ≤
        (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
          Real.sqrt (FlowMetricBall.rmNormSq S t x) := by
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04] using hscalar
  calc
    DifferentialGeometry.Integral.Connection.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x ≤
        |DifferentialGeometry.Integral.Connection.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| := le_abs_self _
    _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (FlowMetricBall.rmNormSq S t x) := hscalar'
    _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnorm) (sq_nonneg _)

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
