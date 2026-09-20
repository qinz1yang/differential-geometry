import DifferentialGeometry.Analysis.Integration.Integral.IsometricDerivative
import DifferentialGeometry.Analysis.Complex.CircleRotation
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem quadratic_sum_comp_rotation
    (B : F →L[ℝ] F →L[ℝ] ℝ) (L : ℂ →L[ℝ] F) (ζ : Circle) :
    B (L (rotation ζ 1)) (L (rotation ζ 1)) +
      B (L (rotation ζ Complex.I)) (L (rotation ζ Complex.I)) =
        B (L 1) (L 1) + B (L Complex.I) (L Complex.I) := by
  have hζ : (ζ : ℂ) = (ζ : ℂ).re • (1 : ℂ) + (ζ : ℂ).im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im (ζ : ℂ)).symm
  have hζI : (ζ : ℂ) * Complex.I = -(ζ : ℂ).im • (1 : ℂ) + (ζ : ℂ).re • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hs : (ζ : ℂ).re ^ 2 + (ζ : ℂ).im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq (ζ : ℂ)
    simp only [Complex.normSq_apply, Circle.norm_coe, one_pow] at h
    nlinarith
  have hL1 := congrArg L hζ
  have hLI := congrArg L hζI
  simp only [map_add, map_smul] at hL1 hLI
  rw [rotation_apply, rotation_apply, mul_one, hL1, hLI]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  calc
    _ = ((ζ : ℂ).re ^ 2 + (ζ : ℂ).im ^ 2) *
      (B (L 1) (L 1) + B (L Complex.I) (L Complex.I)) := by ring
    _ = _ := by rw [hs, one_mul]

theorem integral_quadratic_fderiv_comp_rotation_preimage
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (ζ : Circle) (s : Set ℂ) :
    (∫ z in rotation ζ ⁻¹' s,
      (A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z 1)
          (fderiv ℝ (f ∘ rotation ζ) z 1) +
        A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z Complex.I)
          (fderiv ℝ (f ∘ rotation ζ) z Complex.I)) / 2) =
      ∫ z in s,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  let e := rotation ζ
  have hd (z : ℂ) : fderiv ℝ (f ∘ rotation ζ) z =
      (fderiv ℝ f (rotation ζ z)).comp (rotation ζ).toContinuousLinearMap :=
    e.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := z)
  have hp (z : ℂ) :
      (A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z 1)
          (fderiv ℝ (f ∘ rotation ζ) z 1) +
        A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z Complex.I)
          (fderiv ℝ (f ∘ rotation ζ) z Complex.I)) / 2 =
      (A (f (rotation ζ z)) (fderiv ℝ f (rotation ζ z) 1) (fderiv ℝ f (rotation ζ z) 1) +
        A (f (rotation ζ z)) (fderiv ℝ f (rotation ζ z) Complex.I)
          (fderiv ℝ f (rotation ζ z) Complex.I)) / 2 := by
    rw [hd]
    change (A (f (rotation ζ z)) (fderiv ℝ f (rotation ζ z) (rotation ζ 1))
      (fderiv ℝ f (rotation ζ z) (rotation ζ 1)) +
      A (f (rotation ζ z)) (fderiv ℝ f (rotation ζ z) (rotation ζ Complex.I))
        (fderiv ℝ f (rotation ζ z) (rotation ζ Complex.I))) / 2 = _
    rw [quadratic_sum_comp_rotation (A (f (rotation ζ z)))
      (fderiv ℝ f (rotation ζ z)) ζ]
  simp_rw [hp]
  exact e.measurePreserving.setIntegral_preimage_emb e.toMeasurableEquiv.measurableEmbedding
    (fun z : ℂ => (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2) s

theorem integral_quadratic_fderiv_comp_rotation_closedBall
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (ζ : Circle) (R : ℝ) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
      (A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z 1)
          (fderiv ℝ (f ∘ rotation ζ) z 1) +
        A (f (rotation ζ z)) (fderiv ℝ (f ∘ rotation ζ) z Complex.I)
          (fderiv ℝ (f ∘ rotation ζ) z Complex.I)) / 2) =
      ∫ z in Metric.closedBall (0 : ℂ) R,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  have hs : rotation ζ ⁻¹' Metric.closedBall (0 : ℂ) R = Metric.closedBall (0 : ℂ) R := by
    ext z
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  simpa only [hs] using integral_quadratic_fderiv_comp_rotation_preimage A f ζ
    (Metric.closedBall (0 : ℂ) R)

end DifferentialGeometry.Analysis

end
