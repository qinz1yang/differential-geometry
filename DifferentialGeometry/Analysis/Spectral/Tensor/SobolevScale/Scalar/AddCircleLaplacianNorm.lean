import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.LaplacianNorm

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 0,
      ‖ccTensorToHs g 0 ((n : ℝ) + 2) S‖ ≤
        C * (‖ccTensorToHs g 0 (n : ℝ) S‖ +
          ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖) := by
  let A := appHs g 0 0 n (scalarCc g (laplacianPrincipalCoefficient g))
  let B := appHs g 0 0 n (scalarCc g (laplacianDriftCoefficient g))
  let D := parameterDerivativeHs g n
  refine ⟨1 + ‖A‖ * ‖D‖ + ‖B‖, by positivity, ?_⟩
  intro S
  have hD : ‖ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S))‖ ≤
      ‖D‖ * ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖ := by
    have hh := (parameterDerivativeHs g n).le_opNorm
      (ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S))
    rw [parameterDerivativeHs_apply_ccTensorToHs] at hh
    exact hh
  have hB : ‖ccTensorToHs g 0 (n : ℝ) (parameterDerivativeCcTensor g S)‖ ≤
      ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖ :=
    ccToHs_norm_mono g 0 (by linarith) _
  have hmul (a : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯) (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 (n : ℝ) (scalarSmul g 0 0 a W)‖ ≤
        ‖appHs g 0 0 n (scalarCc g a)‖ * ‖ccTensorToHs g 0 (n : ℝ) W‖ := by
    have hh := (appHs g 0 0 n (scalarCc g a)).le_opNorm
      (ccTensorToHs g 0 (n : ℝ) W)
    rw [appHs_apply_ccTensorToHs, app_scalarCc] at hh
    exact hh
  have hsub (U V : SmoothCcTensor g 0 0) :
      ccTensorToHs g 0 (n : ℝ) (U - V) = ccTensorToHs g 0 (n : ℝ) U - ccTensorToHs g 0 (n : ℝ) V :=
    (ccToHsLin g 0 (n : ℝ)).map_sub U V
  calc
    ‖ccTensorToHs g 0 ((n : ℝ) + 2) S‖ =
        ‖ccTensorToHs g 0 (n : ℝ) (oneMinusConnLapSmooth g 0 0 S)‖ := by
      exact ccTensorToHs_add_two_norm_eq_oneMinusConnLap g 0 (n : ℝ) S
    _ ≤ ‖ccTensorToHs g 0 (n : ℝ) S‖ +
        ‖ccTensorToHs g 0 (n : ℝ) (rawTensorConnLapSmooth g 0 0 S)‖ := by
      rw [oneMinusConnLapSmooth, hsub]
      exact norm_sub_le _ _
    _ ≤ ‖ccTensorToHs g 0 (n : ℝ) S‖ +
        (‖A‖ * (‖D‖ * ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖) +
          ‖B‖ * ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖) := by
      rw [add_le_add_iff_left]
      rw [rawTensorConnLapSmooth_eq_principal_add_drift, ccTensorToHs_add]
      exact (norm_add_le _ _).trans (add_le_add
        ((hmul _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg A)))
        ((hmul _ _).trans (mul_le_mul_of_nonneg_left hB (norm_nonneg B))))
    _ ≤ _ := by
      nlinarith [norm_nonneg (ccTensorToHs g 0 (n : ℝ) S),
        norm_nonneg (ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)),
        mul_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg D))
          (norm_nonneg (ccTensorToHs g 0 (n : ℝ) S)),
        mul_nonneg (norm_nonneg B) (norm_nonneg (ccTensorToHs g 0 (n : ℝ) S))]

theorem exists_norm_ccTensorToHs_two_le_add_parameterDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 0,
      ‖ccTensorToHs g 0 2 S‖ ≤
        C * (‖ccTensorToHs g 0 0 S‖ +
          ‖ccTensorToHs g 0 1 (parameterDerivativeCcTensor g S)‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative g 0
  refine ⟨C, hC, fun S => ?_⟩
  have hn {a b : ℝ} (h : a = b) (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 a W‖ = ‖ccTensorToHs g 0 b W‖ :=
    congrArg (fun t : ℝ => ‖ccTensorToHs g 0 t W‖) h
  have h := hbound S
  rw [hn (show ((0 : ℕ) : ℝ) + 2 = 2 by norm_num),
    hn (show ((0 : ℕ) : ℝ) = 0 by norm_num),
    hn (show ((0 : ℕ) : ℝ) + 1 = 1 by norm_num)] at h
  exact h

end AddCircle
