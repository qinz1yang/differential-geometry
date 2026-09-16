import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem tensorHsInclusion_scalarHsMul_parameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    J (scalarHsMul g 1 (by norm_num) a (parameterDerivativeHs g 1 u)) =
      scalarH0ContinuousMul g (C a) (Z (parameterDerivativeHs g 0
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 1) u))) := by
  intro J C Z
  rw [tensorHsInclusion_scalarHsMul_zero, parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
  congr 1

theorem tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    J (scalarHsMul g 1 (by norm_num) a (parameterSecondDerivativeHs g 1 u)) =
      scalarH0ContinuousMul g (C a) (Z (parameterSecondDerivativeHs g 0
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2) u))) := by
  intro J C Z
  rw [tensorHsInclusion_scalarHsMul_zero, parameterSecondDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
  congr 1

end AddCircle
