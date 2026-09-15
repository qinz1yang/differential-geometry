import DifferentialGeometry.Geometry.Operator.Laplacian.AddCircle
import DifferentialGeometry.Geometry.Metric.Scaling

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

namespace AddCircle

theorem metricCoefficient_scaleMetric_flatMetric
    (a : ℝ) (ha : 0 < a) (z : AddCircle (1 : ℝ)) :
    metricCoefficient (scaleMetric a ha flatMetric) z = a := by
  rw [metricCoefficient_apply, scaleMetric_inner, flatMetric_parameterTangent_unit, mul_one]

theorem laplacian_scaleMetric_flatMetric_coe
    (a : ℝ) (ha : 0 < a) {f : AddCircle (1 : ℝ) → ℝ}
    {x : ℝ} (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 f (x : AddCircle (1 : ℝ))) :
    laplacian (LeviCivita (scaleMetric a ha flatMetric)) (scaleMetric a ha flatMetric)
      f (x : AddCircle (1 : ℝ)) =
        a⁻¹ * deriv (deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) x := by
  rw [laplacian_coe _ hf]
  simp only [scaleMetric_inner, flatMetric_parameterTangent_unit, mul_one,
    deriv_const, zero_div, zero_mul, sub_zero]

end AddCircle
