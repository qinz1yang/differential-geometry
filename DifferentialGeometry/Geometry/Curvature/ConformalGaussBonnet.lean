import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.GreenIdentity
import DifferentialGeometry.Geometry.Curvature.ConformalPlane
import DifferentialGeometry.Geometry.Curvature.ConformalCircle








noncomputable section

open Set MeasureTheory InnerProductSpace Bundle Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis



theorem gaussBonnet_conformalDisk {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      planeGaussianCurvature (conformalEuclideanMetric f hf) z *
        tangentTwoJacobian (conformalEuclideanMetric f hf) (x := z) (1 : ℂ) Complex.I) +
    (∫ θ in -Real.pi..Real.pi,
      let z := Complex.polarCoord.symm (1, θ)
      conformalCircleGeodesicCurvature f hf z *
        Real.sqrt ((conformalEuclideanMetric f hf).inner z (Complex.I * z) (Complex.I * z))) =
      2 * Real.pi := by
  have hz (θ : ℝ) : ‖Complex.polarCoord.symm (1, θ)‖ = 1 := by
    simp
  simp only [planeGaussianCurvature_mul_areaDensity hf,
    conformalCircleGeodesicCurvature_mul_arclength hf (hz _)]
  rw [integral_neg, integral_laplacian_closedBall
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (by norm_num)]
  simp only [one_mul]
  have hint : IntervalIntegrable (fun θ : ℝ =>
      fderiv ℝ f (Complex.polarCoord.symm (1, θ)) (Complex.polarCoord.symm (1, θ)))
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm (1, θ)) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    exact ((hf.continuous_fderiv (by simp)).comp hp).clm_apply hp
  rw [intervalIntegral.integral_add intervalIntegrable_const hint,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

end DifferentialGeometry.Geometry
