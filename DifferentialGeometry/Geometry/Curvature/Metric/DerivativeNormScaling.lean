import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormTensor
import DifferentialGeometry.Geometry.Metric.Tensor.Scaling

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem curvatureDerivativeNorm_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (k : ℕ) (x : M) :
    curvatureDerivativeNorm (scaleMetric c hc g) k x =
      (Real.sqrt c)⁻¹ ^ (k + 2) * curvatureDerivativeNorm g k x := by
  have hmetric :
      scaleMetric ((Real.sqrt c) ^ 2) (sq_pos_of_pos (Real.sqrt_pos.mpr hc)) g =
        scaleMetric c hc g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    simp only [scaleMetric_inner, Real.sq_sqrt hc.le]
  have hscale := Geometry.Tensor.sqrt_normSq0S_iterCov_metricRm04_scaleMetric_sq
    g (Real.sqrt c) (Real.sqrt_pos.mpr hc) k x
  rw [hmetric] at hscale
  simpa only [curvatureDerivativeNorm, tensor0SFiberNorm,
    iteratedMetricCovariantDerivative_rm04_eq, iteratedCurvatureTensor_eq_iterCov,
    Nat.add_comm 2 k] using hscale

theorem curvatureDerivativeNorm_scaleMetric_inv (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (k : ℕ) (x : M) :
    curvatureDerivativeNorm (scaleMetric c⁻¹ (inv_pos.mpr hc) g) k x =
      (Real.sqrt c) ^ (k + 2) * curvatureDerivativeNorm g k x := by
  simpa only [Real.sqrt_inv, inv_inv] using
    curvatureDerivativeNorm_scaleMetric g c⁻¹ (inv_pos.mpr hc) k x

end DifferentialGeometry.Geometry.Curvature
