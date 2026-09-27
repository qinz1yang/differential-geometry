import DifferentialGeometry.Geometry.Operator.Laplacian.AddCircleScaling
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.RankZeroRealization

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

namespace AddCircle

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem rawTensorConnLapSmooth_scaleMetric_flatMetric
    (a : ℝ) (ha : 0 < a)
    (S : SmoothCcTensor (scaleMetric a ha flatMetric) 0 0) :
    rawTensorConnLapSmooth (scaleMetric a ha flatMetric) 0 0 S =
      a⁻¹ • parameterDerivativeCcTensor (scaleMetric a ha flatMetric)
        (parameterDerivativeCcTensor (scaleMetric a ha flatMetric) S) := by
  apply SmoothCcTensor.ext
  rw [← TensorRSField.lift_scalar0 (rawTensorConnLapSmooth (scaleMetric a ha flatMetric) 0 0 S).toSection,
    ← TensorRSField.lift_scalar0
      (a⁻¹ • parameterDerivativeCcTensor (scaleMetric a ha flatMetric)
        (parameterDerivativeCcTensor (scaleMetric a ha flatMetric) S)).toSection]
  congr 2
  funext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [SmoothCcTensor.toSection_smul, TensorRSField.scalar0_smul]
  change TensorRSField.scalar0 (rawTensorConnLapSmooth _ 0 0 S).toSection
    (x : AddCircle (1 : ℝ)) = a⁻¹ * _
  rw [rawLap_cc_scalar, scalar0_parameterDerivativeCcTensor_twice_coe]
  rw [← laplacian_levi_eq _ (TensorRSField.scalar0_smooth S.toSection)]
  exact laplacian_scaleMetric_flatMetric_coe a ha
    ((TensorRSField.scalar0_smooth S.toSection).of_le (by decide : (2 : ℕ∞ω) ≤ ∞) _)

theorem tensorScaleLaplacian_scaleMetric_flatMetric
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    tensorScaleLaplacian (g := scaleMetric a ha flatMetric) (r := 0) (s := 0) (n : ℝ) =
      a⁻¹ • parameterSecondDerivativeHs (scaleMetric a ha flatMetric) n := by
  let g := scaleMetric a ha flatMetric
  let L := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)
  let R := a⁻¹ • parameterSecondDerivativeHs g n
  have heq : (L : _ → _) = R :=
    (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)).equalizer
      L.continuous R.continuous (by
        funext S
        simp only [Function.comp_apply, L, R, smul_apply, ccToHsLin_apply]
        rw [tensorScaleLaplacian_apply_ccTensorToHs,
          parameterSecondDerivativeHs_apply_ccTensorToHs,
          rawTensorConnLapSmooth_scaleMetric_flatMetric, ccTensorToHs_smul])
  exact ContinuousLinearMap.coeFn_injective heq

theorem piLpMap_tensorScaleLaplacian_scaleMetric_flatMetric
    {ι : Type*} (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := scaleMetric a ha flatMetric) (r := 0) (s := 0) (n : ℝ)) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        a⁻¹ • parameterSecondDerivativeHs (scaleMetric a ha flatMetric) n) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  change tensorScaleLaplacian (g := scaleMetric a ha flatMetric) (r := 0) (s := 0)
    (n : ℝ) (u i) = a⁻¹ • parameterSecondDerivativeHs (scaleMetric a ha flatMetric) n (u i)
  rw [tensorScaleLaplacian_scaleMetric_flatMetric, smul_apply]

end AddCircle
