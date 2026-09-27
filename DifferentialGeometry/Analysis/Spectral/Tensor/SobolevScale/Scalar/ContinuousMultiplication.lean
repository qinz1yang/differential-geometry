import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarComposition
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

omit [SigmaCompactSpace M] in
private theorem scalar0_comp (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (S T : SmoothCcTensor g 0 0) (x : M) :
    TensorRSField.scalar0 (ccOperatorFieldComp g 0 0 0 S T).toSection x =
      TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x := by
  let f : C^∞⟮𝓘(ℝ, ℝ), M; ℝ⟯ :=
    ⟨TensorRSField.scalar0 S.toSection, TensorRSField.scalar0_smooth S.toSection⟩
  have hS : scalarCc g f = S := SmoothCcTensor.ext_scalar0 (scalar0_scalarCc g f)
  rw [← hS, operatorFieldComposition_zero_eq_operatorFieldApply, app_scalarCc,
    scalar0_smul_cc, scalar0_scalarCc]

theorem scalarH1ToContinuous_scalarHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (u v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) (x : M) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    scalarH1ToContinuous g (J (scalarHsMul g 1 (by norm_num) u v)) x =
      scalarH1ToContinuous g (J u) x * scalarH1ToContinuous g (J v) x := by
  let hn : Module.finrank ℝ ℝ / 2 + 1 ≤ 1 := by norm_num
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
  have heval : Continuous
      (fun u : TensorHs g 0 0 ((1 : ℕ) : ℝ) => scalarH1ToContinuous g (J u) x) :=
    (ContinuousMap.evalCLM ℝ x).continuous.comp
      ((scalarH1ToContinuous g).continuous.comp J.continuous)
  refine (ccToHsLin_dense g 0
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq
      (heval.comp ((scalarHsMul g 1 hn).continuous.clm_apply continuous_const))
      (heval.mul continuous_const)
  intro S
  refine (ccToHsLin_dense g 0
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on v ?_ ?_
  · exact isClosed_eq
      (heval.comp (scalarHsMul g 1 hn (ccToHsLin g 0 ((1 : ℕ) : ℝ) S)).continuous)
      (continuous_const.mul heval)
  intro T
  change scalarH1ToContinuous g (J (scalarHsMul g 1 hn
    (ccTensorToHs g 0 ((1 : ℕ) : ℝ) S)
    (ccTensorToHs g 0 ((1 : ℕ) : ℝ) T))) x = _
  simp only [scalarHsMul_apply_ccTensorToHs, J, tensorHsInclusion_ccTensorToHs,
    scalarH1ToContinuous_apply_ccTensorToHs, ccToHsLin_apply]
  exact scalar0_comp g S T x

end DifferentialGeometry.Analysis.Spectral
