import DifferentialGeometry.Geometry.Connection.ConformalEuclidean
import Mathlib.Analysis.SpecialFunctions.Complex.Circle







noncomputable section

open Bundle Manifold InnerProductSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry.Connection



def conformalCircleTangent (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  Real.exp (-f z) • (Complex.I * z)


def conformalCircleNormal (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  -Real.exp (-f z) • z


def conformalCircleGeodesicCurvature (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (z : ℂ) : ℝ :=
  (conformalEuclideanMetric f hf).inner z
    (LeviCivita (conformalEuclideanMetric f hf)
      (conformalCircleTangent f) z (conformalCircleTangent f z))
    (conformalCircleNormal f z)

private theorem conformal_exp_cancel (r : ℝ) :
    Real.exp (2 * r) * Real.exp (-r) ^ 2 = 1 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  ring_nf
  exact Real.exp_zero


theorem conformalCircleTangent_unit {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (conformalEuclideanMetric f hf).inner z
      (conformalCircleTangent f z) (conformalCircleTangent f z) = 1 := by
  rw [conformalEuclideanMetric_inner]
  unfold conformalCircleTangent
  erw [real_inner_smul_left, real_inner_smul_right]
  simp only [
    real_inner_self_eq_norm_sq, norm_mul, Complex.norm_I, hz, one_pow, mul_one]
  nlinarith [conformal_exp_cancel (f z)]


theorem conformalCircleNormal_unit {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (conformalEuclideanMetric f hf).inner z
      (conformalCircleNormal f z) (conformalCircleNormal f z) = 1 := by
  rw [conformalEuclideanMetric_inner]
  unfold conformalCircleNormal
  erw [real_inner_smul_left, real_inner_smul_right]
  simp only [
    real_inner_self_eq_norm_sq, hz, one_pow, mul_one]
  nlinarith [conformal_exp_cancel (f z)]


theorem conformalCircle_orthogonal {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    (conformalEuclideanMetric f hf).inner z
      (conformalCircleTangent f z) (conformalCircleNormal f z) = 0 := by
  rw [conformalEuclideanMetric_inner]
  unfold conformalCircleTangent conformalCircleNormal
  erw [real_inner_smul_left, real_inner_smul_right]
  simp [Complex.inner, Complex.mul_re, Complex.mul_im, mul_comm]

private theorem fderiv_conformalCircleTangent {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    fderiv ℝ (conformalCircleTangent f) z v =
      Real.exp (-f z) • (Complex.I * v) -
        (Real.exp (-f z) * fderiv ℝ f z v) • (Complex.I * z) := by
  have h := ((hf.hasFDerivAt.neg.exp).smul
    ((hasFDerivAt_id z).const_mul Complex.I)).fderiv
  change fderiv ℝ (conformalCircleTangent f) z = _ at h
  rw [h]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, _root_.neg_apply, smul_eq_mul, mul_neg, neg_smul,
    sub_eq_add_neg]
  rfl


theorem conformalCircleGeodesicCurvature_eq {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ℂ} (hz : ‖z‖ = 1) :
    conformalCircleGeodesicCurvature f hf z =
      Real.exp (-f z) * (1 + fderiv ℝ f z z) := by
  have hfd := hf.differentiable (by simp) z
  have hT : DifferentiableAt ℝ (conformalCircleTangent f) z :=
    hfd.neg.exp.smul (differentiableAt_id.const_mul Complex.I)
  have horth : inner ℝ (Complex.I * z) z = 0 := by
    simp [Complex.inner, Complex.mul_re, Complex.mul_im, mul_comm]
  have hnorm : inner ℝ z z = 1 := by rw [real_inner_self_eq_norm_sq, hz, one_pow]
  have hInorm : inner ℝ (Complex.I * z) (Complex.I * z) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_mul, Complex.norm_I, hz]
    norm_num
  rw [conformalCircleGeodesicCurvature]
  erw [leviCivita_conformalEuclidean hf hT, conformalEuclideanMetric_inner,
    fderiv_conformalCircleTangent hfd]
  unfold conformalEuclideanCorrection conformalCircleTangent conformalCircleNormal
  have hrot : Complex.I * (Real.exp (-f z) • (Complex.I * z)) =
      -Real.exp (-f z) • z := by
    rw [mul_smul_comm, ← mul_assoc, Complex.I_mul_I]
    simp
  rw [hrot]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    horth, hnorm, hInorm, inner_gradient_left]
  calc
    _ = (Real.exp (2 * f z) * Real.exp (-f z) ^ 2) *
        Real.exp (-f z) * (1 + fderiv ℝ f z z) := by ring
    _ = _ := by rw [conformal_exp_cancel, one_mul]


theorem conformalCircle_arclengthDensity {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {z : ℂ} (hz : ‖z‖ = 1) :
    Real.sqrt ((conformalEuclideanMetric f hf).inner z (Complex.I * z) (Complex.I * z)) =
      Real.exp (f z) := by
  rw [conformalEuclideanMetric_inner, real_inner_self_eq_norm_sq, norm_mul,
    Complex.norm_I, hz]
  simp only [one_pow, mul_one]
  rw [show 2 * f z = f z + f z by ring, Real.exp_add]
  exact Real.sqrt_mul_self (Real.exp_pos _).le



theorem conformalCircleGeodesicCurvature_mul_arclength {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : ‖z‖ = 1) :
    conformalCircleGeodesicCurvature f hf z *
      Real.sqrt ((conformalEuclideanMetric f hf).inner z (Complex.I * z) (Complex.I * z)) =
      1 + fderiv ℝ f z z := by
  rw [conformalCircleGeodesicCurvature_eq hf hz, conformalCircle_arclengthDensity hf hz,
    Real.exp_neg]
  field_simp

end DifferentialGeometry.Geometry
