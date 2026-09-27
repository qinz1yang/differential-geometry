import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.ContinuousMultiplication
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.ContinuousMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuousInjective

noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarH0ContinuousMul_smooth_product
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (S T : SmoothCcTensor g 0 0) :
    scalarH0ContinuousMul g (scalarH1ToContinuous g (ccTensorToHs g 0 1 S))
        (ccTensorToHs g 0 0 T) = ccTensorToHs g 0 0 (ccOperatorFieldComp g 0 0 0 S T) := by
  let f : C^∞⟮𝓘(ℝ, ℝ), M; ℝ⟯ :=
    ⟨TensorRSField.scalar0 S.toSection, TensorRSField.scalar0_smooth S.toSection⟩
  have hS : scalarCc g f = S := SmoothCcTensor.ext_scalar0 (scalar0_scalarCc g f)
  have hf : scalarH1ToContinuous g (ccTensorToHs g 0 1 S) = ⟨f, f.2.continuous⟩ := by
    ext x
    exact scalarH1ToContinuous_apply_ccTensorToHs g S x
  rw [hf, scalarH0ContinuousMul_ccTensorToHs, ← hS,
    operatorFieldComposition_zero_eq_operatorFieldApply, app_scalarCc]

theorem tensorHsInclusion_scalarHsMul_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (u v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    J (scalarHsMul g 1 (by norm_num) u v) = scalarH0ContinuousMul g (C u) (J v) := by
  intro J C
  let m := scalarHsMul g 1 (by norm_num)
  change J (m u v) = _
  refine (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq (J.continuous.comp (m.continuous.clm_apply continuous_const))
      (((scalarH0ContinuousMul g).continuous.comp C.continuous).clm_apply continuous_const)
  intro S
  refine (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on v ?_ ?_
  · exact isClosed_eq (J.continuous.comp (m (ccToHsLin g 0 ((1 : ℕ) : ℝ) S)).continuous)
      ((scalarH0ContinuousMul g (C (ccToHsLin g 0 ((1 : ℕ) : ℝ) S))).continuous.comp J.continuous)
  intro T
  simp only [ccToHsLin_apply, m, scalarHsMul_apply_ccTensorToHs, J, C,
    ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
    scalarH0ContinuousMul_smooth_product]

theorem scalarH0ContinuousMul_scalarH1ToContinuous_comm
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (u v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    scalarH0ContinuousMul g (C u) (J v) = scalarH0ContinuousMul g (C v) (J u) := by
  intro J C
  rw [← tensorHsInclusion_scalarHsMul_zero, ← tensorHsInclusion_scalarHsMul_zero]
  congr 1
  apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
  apply scalarH1ToContinuous_injective g
  apply ContinuousMap.ext
  intro x
  rw [scalarH1ToContinuous_scalarHsMul, scalarH1ToContinuous_scalarHsMul, mul_comm]

end DifferentialGeometry.Analysis.Spectral
