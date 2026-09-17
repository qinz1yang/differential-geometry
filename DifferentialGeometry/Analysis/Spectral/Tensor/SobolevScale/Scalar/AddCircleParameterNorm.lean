import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacianNorm
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarNorm
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_norm_ccTensorToHs_add_two_le_parameter_derivatives
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 0) (B : ℝ),
      0 ≤ B →
      (∀ j ≤ 2, ‖ccTensorToHs g 0 (n : ℝ)
        ((parameterDerivativeCcTensor g)^[j] S)‖ ≤ B) →
      ‖ccTensorToHs g 0 ((n : ℝ) + 2) S‖ ≤ C * B := by
  let A := appHs g 0 0 n (scalarCc g (laplacianPrincipalCoefficient g))
  let D := appHs g 0 0 n (scalarCc g (laplacianDriftCoefficient g))
  refine ⟨1 + ‖A‖ + ‖D‖, by positivity, ?_⟩
  intro S B hB hbound
  have hmul (a : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯)
      (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 (n : ℝ) (scalarSmul g 0 0 a W)‖ ≤
        ‖appHs g 0 0 n (scalarCc g a)‖ * ‖ccTensorToHs g 0 (n : ℝ) W‖ := by
    have hh := (appHs g 0 0 n (scalarCc g a)).le_opNorm
      (ccTensorToHs g 0 (n : ℝ) W)
    rw [appHs_apply_ccTensorToHs, app_scalarCc] at hh
    exact hh
  have hsub (U V : SmoothCcTensor g 0 0) :
      ccTensorToHs g 0 (n : ℝ) (U - V) =
        ccTensorToHs g 0 (n : ℝ) U - ccTensorToHs g 0 (n : ℝ) V :=
    (ccToHsLin g 0 (n : ℝ)).map_sub U V
  have h0 := hbound 0 (by omega)
  have h1 := hbound 1 (by omega)
  have h2 := hbound 2 (by omega)
  simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply] at h0 h1 h2
  calc
    ‖ccTensorToHs g 0 ((n : ℝ) + 2) S‖ =
        ‖ccTensorToHs g 0 (n : ℝ) (oneMinusConnLapSmooth g 0 0 S)‖ :=
      ccTensorToHs_add_two_norm_eq_oneMinusConnLap g 0 (n : ℝ) S
    _ ≤ ‖ccTensorToHs g 0 (n : ℝ) S‖ +
        ‖ccTensorToHs g 0 (n : ℝ) (rawTensorConnLapSmooth g 0 0 S)‖ := by
      rw [oneMinusConnLapSmooth, hsub]
      exact norm_sub_le _ _
    _ ≤ B + (‖A‖ * B + ‖D‖ * B) := by
      apply add_le_add h0
      rw [rawTensorConnLapSmooth_eq_principal_add_drift, ccTensorToHs_add]
      exact (norm_add_le _ _).trans (add_le_add
        ((hmul _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg A)))
        ((hmul _ _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg D))))
    _ = _ := by ring

private theorem exists_norm_ccTensorToHs_three_le_parameter_derivatives
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 0) (B : ℝ),
      0 ≤ B →
      (∀ j ≤ 4, ‖(parameterDerivativeCcTensor g)^[j] S‖ ≤ B) →
      ‖ccTensorToHs g 0 3 S‖ ≤ C * B := by
  have hn {a b : ℝ} (h : a = b) (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 a W‖ = ‖ccTensorToHs g 0 b W‖ :=
    congrArg (fun t : ℝ => ‖ccTensorToHs g 0 t W‖) h
  obtain ⟨C₀, hC₀, hzero⟩ := hs_le_jet g 0 0
  simp_rw [hn (show ((0 : ℕ) : ℝ) = 0 by norm_num)] at hzero
  have hzero' (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 0 W‖ ≤ C₀ * ‖W‖ := by
    simpa only [Nat.cast_zero, zero_add, Finset.sum_range_one,
      iteratedCovGrad_zero] using hzero W
  obtain ⟨C₂, hC₂, htwo⟩ := exists_norm_ccTensorToHs_add_two_le_parameter_derivatives g 0
  obtain ⟨C₄, hC₄, hfour⟩ := exists_norm_ccTensorToHs_add_two_le_parameter_derivatives g 2
  simp_rw [hn (show ((0 : ℕ) : ℝ) = 0 by norm_num),
    hn (show ((0 : ℕ) : ℝ) + 2 = 2 by norm_num)] at htwo
  simp_rw [hn (show ((2 : ℕ) : ℝ) = 2 by norm_num),
    hn (show ((2 : ℕ) : ℝ) + 2 = 4 by norm_num)] at hfour
  refine ⟨C₄ * C₂ * C₀, by positivity, ?_⟩
  intro S B hB hbound
  have htwo' (j : ℕ) (hj : j ≤ 2) :
      ‖ccTensorToHs g 0 2 ((parameterDerivativeCcTensor g)^[j] S)‖ ≤
        C₂ * (C₀ * B) := by
    apply htwo _ _ (mul_nonneg hC₀ hB)
    intro k hk
    rw [← Function.iterate_add_apply]
    exact (hzero' _).trans (mul_le_mul_of_nonneg_left (hbound (k + j) (by omega)) hC₀)
  have hfour' : ‖ccTensorToHs g 0 4 S‖ ≤ C₄ * (C₂ * (C₀ * B)) := by
    apply hfour _ _ (by positivity)
    exact htwo'
  calc
    ‖ccTensorToHs g 0 3 S‖ ≤ ‖ccTensorToHs g 0 4 S‖ :=
      ccToHs_norm_mono g 0 (by norm_num) S
    _ ≤ C₄ * (C₂ * (C₀ * B)) := hfour'
    _ = _ := by ring

private theorem scalar0_iterate_parameterDerivativeCcTensor_coe
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) (j : ℕ) (x : ℝ) :
    TensorRSField.scalar0 ((parameterDerivativeCcTensor g)^[j] S).toSection
        (x : AddCircle (1 : ℝ)) =
      iteratedDeriv j (fun y : ℝ => TensorRSField.scalar0 S.toSection
        (y : AddCircle (1 : ℝ))) x := by
  induction j generalizing x with
  | zero => simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero]
  | succ j ih =>
      rw [Function.iterate_succ_apply', scalar0_parameterDerivativeCcTensor_coe,
        iteratedDeriv_succ]
      simp_rw [ih]

theorem exists_norm_ccTensorToHs_three_le_iteratedDeriv
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 0) (B : ℝ),
      0 ≤ B →
      (∀ j ≤ 4, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv j (fun y : ℝ => TensorRSField.scalar0 S.toSection
          (y : AddCircle (1 : ℝ))) x| ≤ B) →
      ‖ccTensorToHs g 0 3 S‖ ≤ C * B := by
  obtain ⟨C₁, hC₁, hspec⟩ := exists_norm_ccTensorToHs_three_le_parameter_derivatives g
  obtain ⟨C₂, hC₂, hL2⟩ := SmoothCcTensor.exists_norm_le_mul_of_scalar0_bound g
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro S B hB hbound
  have hnorm (j : ℕ) (hj : j ≤ 4) :
      ‖(parameterDerivativeCcTensor g)^[j] S‖ ≤ C₂ * B := by
    apply hL2 _ _ hB
    intro z
    have hz : z ∈ (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Ioc (0 : ℝ) 1 := by
      rw [show (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Ioc 0 1 = Set.univ by
        simpa only [zero_add] using coe_image_Ioc_eq (1 : ℝ) (0 : ℝ)]
      exact Set.mem_univ z
    obtain ⟨x, hx, rfl⟩ := hz
    rw [scalar0_iterate_parameterDerivativeCcTensor_coe]
    exact hbound j hj x ⟨hx.1.le, hx.2⟩
  calc
    ‖ccTensorToHs g 0 3 S‖ ≤ C₁ * (C₂ * B) :=
      hspec S (C₂ * B) (mul_nonneg hC₂ hB) hnorm
    _ = _ := by ring

theorem exists_norm_sub_ccTensorToHs_three_le_iteratedDeriv
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S T : SmoothCcTensor g 0 0) (B : ℝ),
      0 ≤ B →
      (∀ j ≤ 4, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv j (fun y : ℝ => TensorRSField.scalar0 S.toSection
          (y : AddCircle (1 : ℝ))) x -
          iteratedDeriv j (fun y : ℝ => TensorRSField.scalar0 T.toSection
            (y : AddCircle (1 : ℝ))) x| ≤ B) →
      ‖ccTensorToHs g 0 3 S - ccTensorToHs g 0 3 T‖ ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_ccTensorToHs_three_le_iteratedDeriv g
  refine ⟨C, hC, ?_⟩
  intro S T B hB hST
  have hsub : ccTensorToHs g 0 3 (S - T) =
      ccTensorToHs g 0 3 S - ccTensorToHs g 0 3 T :=
    (ccToHsLin g 0 3).map_sub S T
  rw [← hsub]
  apply hbound _ _ hB
  intro j hj x hx
  have hS : ContDiff ℝ ∞ (fun y : ℝ => TensorRSField.scalar0 S.toSection
      (y : AddCircle (1 : ℝ))) :=
    contMDiff_iff_contDiff.mp ((TensorRSField.scalar0_smooth S.toSection).comp contMDiff_coe)
  have hT : ContDiff ℝ ∞ (fun y : ℝ => TensorRSField.scalar0 T.toSection
      (y : AddCircle (1 : ℝ))) :=
    contMDiff_iff_contDiff.mp ((TensorRSField.scalar0_smooth T.toSection).comp contMDiff_coe)
  simp only [SmoothCcTensor.toSection_sub, TensorRSField.scalar0_sub, Pi.sub_apply]
  rw [iteratedDeriv_fun_sub (hS.of_le (by exact_mod_cast le_top)).contDiffAt
    (hT.of_le (by exact_mod_cast le_top)).contDiffAt]
  exact hST j hj x hx

end AddCircle

end
