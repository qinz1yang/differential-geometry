import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0SmoothMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian

noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem parameterDerivativeParabolicForcing_eq_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (b : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (f₀ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))
    (v : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) :
    let a := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) a₂
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    let q : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianPrincipalCoefficient g, (laplacianPrincipalCoefficient g).2.continuous⟩
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
    parameterDerivativeParabolicForcing g a b f₀ v =
      scalarH0ContinuousMul g (C a - q) (Z (parameterSecondDerivativeHs g 0 v)) +
        scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂) - d)
          (Z (parameterDerivativeHs g 0 (J v))) +
        parameterDerivativeParabolicForcing g a b f₀ 0 := by
  intro a C Z J q d
  let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
  let R := (parameterDerivativeHs g 1).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2))
  let J₁₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
  have ha : Z (D a) = J₁₀ (parameterDerivativeHs g 1 a₂) := by
    simp only [D, a, ContinuousLinearMap.comp_apply]
    rw [← tensorHsInclusion_trans_apply,
      parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
    exact (tensorHsInclusion_trans_apply _ _ _).symm
  have hv : J₁₀ (R v) = Z (parameterDerivativeHs g 0 (J v)) := by
    have h := parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2) v)
    rw [← tensorHsInclusion_trans_apply] at h
    change _ = Z (parameterDerivativeHs g 0 (J v))
    rw [h]
    exact tensorHsInclusion_trans_apply _ _ _
  have hcross : scalarH0ContinuousMul g (C (R v)) (Z (D a)) =
      scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂))
        (Z (parameterDerivativeHs g 0 (J v))) := by
    rw [ha, scalarH0ContinuousMul_scalarH1ToContinuous_comm, hv]
  have hL : Z (tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ) v) =
      scalarH0ContinuousMul g q (Z (parameterSecondDerivativeHs g 0 v)) +
        scalarH0ContinuousMul g d (Z (parameterDerivativeHs g 0 (J v))) := by
    rw [tensorScaleLaplacian_eq_principal_add_drift]
    simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
    rw [tensorHsInclusion_appHs_scalarCc_zero, tensorHsInclusion_appHs_scalarCc_zero]
  have hf : parameterDerivativeParabolicForcing g a b f₀ v =
      scalarH0ContinuousMul g (C a) (Z (parameterSecondDerivativeHs g 0 v)) +
        scalarH0ContinuousMul g (C (R v)) (Z (D a)) -
          Z (tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((0 : ℕ) : ℝ) v) +
        parameterDerivativeParabolicForcing g a b f₀ 0 := by
    simp only [parameterDerivativeParabolicForcing, map_zero, zero_apply,
      add_zero, zero_add, sub_zero, C, Z, R, D]
  rw [hf, hcross, hL]
  simp only [map_sub, sub_apply]
  abel

end AddCircle
