import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing
import DifferentialGeometry.Geometry.Curvature.ScalarNormBound
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem scalar_le_of_rm
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : ℝ} (ht : t ∈ Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ))
    {x : M} (hx : x ∈ B.setAt t) :
    DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4) := by
  have hnorm : FlowMetricBall.rmNormSq S t x ≤ 1 / B.radius ^ 4 := by
    apply (le_div_iff₀ (pow_pos B.radius_pos 4)).2
    simpa only [mul_comm] using hB.2 t ht x hx
  have hscalar :=
    DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
      (I := I) (M := M) (S.base.metric t) x
  have hscalar' :
      |DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| ≤
        (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
          Real.sqrt (FlowMetricBall.rmNormSq S t x) := by
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04] using hscalar
  calc
    DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x ≤
        |DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| := le_abs_self _
    _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (FlowMetricBall.rmNormSq S t x) := hscalar'
    _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnorm) (sq_nonneg _)

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
