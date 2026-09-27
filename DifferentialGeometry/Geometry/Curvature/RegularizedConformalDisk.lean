import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Boundary
import DifferentialGeometry.Geometry.Curvature.ConformalGaussBonnet







noncomputable section

open Set MeasureTheory InnerProductSpace Bundle Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis DifferentialGeometry


def regularizedConformalMetric (a f : ℂ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    (ε : ℝ) (hε : ε ≠ 0) : SmoothRiemannianMetric 𝓘(ℝ, ℂ) ℂ :=
  conformalEuclideanMetric (regularizedConformalLogFactor a f ε)
    (contDiff_regularizedConformalLogFactor ha hf han hε)


theorem regularizedConformalMetric_inner {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (z v w : ℂ) :
    (regularizedConformalMetric a f ha hf han ε hε).inner z v w =
      regularizedConformalCoefficient a f ε z * inner ℝ v w := by
  rw [regularizedConformalMetric, conformalEuclideanMetric_inner,
    exp_two_regularizedConformalLogFactor (han z) hε]



theorem regularizedConformalMetric_curvatureDensity {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I =
      -(1 / 2 : ℝ) * Laplacian.laplacian
        (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z := by
  rw [regularizedConformalMetric, planeGaussianCurvature_mul_areaDensity,
    laplacian_regularizedConformalLogFactor
      (ha.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (han z) hε]
  ring



theorem regularizedConformalMetric_curvatureDensity_le {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I ≤
      (if a z = 0 then 0 else regularizedConformalWeight a f ε z *
        (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q)) z)) +
      (1 - regularizedConformalWeight a f ε z) * (-Laplacian.laplacian f z) := by
  rw [regularizedConformalMetric_curvatureDensity ha hf han hε]
  exact regularizedConformal_curvature_le
    (ha.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (Filter.Eventually.of_forall han) hε



theorem regularizedConformalMetric_boundaryDensity {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) {z : ℂ} (hz : ‖z‖ = 1)
    (hfν : fderiv ℝ f z z = -1) :
    conformalCircleGeodesicCurvature (regularizedConformalLogFactor a f ε)
        (contDiff_regularizedConformalLogFactor ha hf han hε) z *
      Real.sqrt ((regularizedConformalMetric a f ha hf han ε hε).inner z
        (Complex.I * z) (Complex.I * z)) =
      regularizedConformalWeight a f ε z *
        (1 + (1 / 2 : ℝ) * fderiv ℝ (fun q => Real.log (a q)) z z) := by
  rw [regularizedConformalMetric, conformalCircleGeodesicCurvature_mul_arclength _ hz]
  have hd : DifferentiableAt ℝ
      (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z := by
    exact ((ha.differentiable (by simp) z).add
      (((hf.differentiable (by simp) z).const_mul 2).exp.const_mul (ε ^ 2))).log
        (regularizedConformalCoefficient_pos (f := f) (han z) hε).ne'
  unfold regularizedConformalLogFactor
  rw [(hd.hasFDerivAt.const_mul (1 / 2 : ℝ)).fderiv]
  exact regularizedConformal_boundary_density (ha.differentiable (by simp) z)
    (hf.differentiable (by simp) z) (Filter.Eventually.of_forall han) hfν hε

end DifferentialGeometry.Geometry
