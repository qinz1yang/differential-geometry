import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem parameterDerivativeHs_comp_parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    (parameterDerivativeHs g n).comp
        ((tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)).comp
            (parameterSecondDerivativeHs g (n + 1))) =
      (parameterSecondDerivativeHs g n).comp
        ((tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num)).comp
            ((parameterDerivativeHs g (n + 2)).comp
              (tensorHsInclusion (g := g) (r := 0) (s := 0)
                (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by
                  push_cast
                  linarith)))) := by
  apply DFunLike.coe_injective
  apply (ccToHsLin_dense g 0 (by positivity :
    (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 2)).equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext S
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
  rw [parameterSecondDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterSecondDerivativeHs_apply_ccTensorToHs]

theorem parameterDerivativeHs_parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2)) :
    parameterDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)
          (parameterSecondDerivativeHs g (n + 1) u)) =
      parameterSecondDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num)
          (parameterDerivativeHs g (n + 2)
            (tensorHsInclusion
              (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by
                push_cast
                linarith) u))) :=
  DFunLike.congr_fun (parameterDerivativeHs_comp_parameterSecondDerivativeHs g n) u

theorem parameterDerivativeHsPi_comp_parameterSecondDerivativeHsPi
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    (parameterDerivativeHsPi (ι := ι) g n).comp
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num))).comp
              (parameterSecondDerivativeHsPi g (n + 1))) =
      (parameterSecondDerivativeHsPi g n).comp
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num))).comp
              ((parameterDerivativeHsPi g (n + 2)).comp
                (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                  tensorHsInclusion (g := g) (r := 0) (s := 0)
                    (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by
                      push_cast
                      linarith))))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact parameterDerivativeHs_parameterSecondDerivativeHs g n (u i)

end AddCircle
