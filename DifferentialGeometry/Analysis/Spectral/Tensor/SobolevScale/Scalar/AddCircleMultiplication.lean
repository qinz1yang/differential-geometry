import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion

noncomputable section
open scoped Manifold ContDiff
namespace AddCircle
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalar0_comp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S T : SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
    TensorRSField.scalar0 (ccOperatorFieldComp g 0 0 0 S T).toSection x =
      TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x := by
  let f : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
    ⟨TensorRSField.scalar0 S.toSection, TensorRSField.scalar0_smooth S.toSection⟩
  have hS : scalarCc g f = S := SmoothCcTensor.ext_scalar0 (scalar0_scalarCc g f)
  rw [← hS, operatorFieldComposition_zero_eq_operatorFieldApply, app_scalarCc,
    scalar0_smul_cc, scalar0_scalarCc]

theorem parameterDerivativeCcTensor_ccOperatorFieldComp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S T : SmoothCcTensor g 0 0) :
    parameterDerivativeCcTensor g (ccOperatorFieldComp g 0 0 0 S T) =
      ccOperatorFieldComp g 0 0 0 S (parameterDerivativeCcTensor g T) +
        ccOperatorFieldComp g 0 0 0 T (parameterDerivativeCcTensor g S) := by
  apply SmoothCcTensor.ext_scalar0
  funext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  simp only [scalar0_parameterDerivativeCcTensor_coe, SmoothCcTensor.toSection_add,
    TensorRSField.scalar0_add, Pi.add_apply, scalar0_comp]
  have hS : DifferentiableAt ℝ
      (fun t : ℝ => TensorRSField.scalar0 S.toSection (t : AddCircle (1 : ℝ))) x := by
    exact ((((TensorRSField.scalar0_smooth S.toSection).comp contMDiff_coe).contDiff).differentiable
        (by simp) x)
  have hT : DifferentiableAt ℝ
      (fun t : ℝ => TensorRSField.scalar0 T.toSection (t : AddCircle (1 : ℝ))) x := by
    exact ((((TensorRSField.scalar0_smooth T.toSection).comp contMDiff_coe).contDiff).differentiable
        (by simp) x)
  rw [deriv_fun_mul hS hT]
  ring

theorem parameterDerivativeHs_scalarHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let D := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).comp
        ((parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ))))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    D (scalarHsMul g 1 (by norm_num) u v) =
      scalarH0ContinuousMul g (C u) (D v) + scalarH0ContinuousMul g (C v) (D u) := by
  intro D C
  let m := scalarHsMul g 1 (by norm_num)
  have hD (S : SmoothCcTensor g 0 0) :
      D (ccTensorToHs g 0 ((1 : ℕ) : ℝ) S) =
        ccTensorToHs g 0 0 (parameterDerivativeCcTensor g S) := by
    simp only [D, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
      parameterDerivativeHs_apply_ccTensorToHs]
  have hC (S : SmoothCcTensor g 0 0) :
      C (ccTensorToHs g 0 ((1 : ℕ) : ℝ) S) =
        scalarH1ToContinuous g (ccTensorToHs g 0 1 S) := by
    simp only [C, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs]
  have hmul0 (S T : SmoothCcTensor g 0 0) :
      scalarH0ContinuousMul g (scalarH1ToContinuous g (ccTensorToHs g 0 1 S))
        (ccTensorToHs g 0 0 T) = ccTensorToHs g 0 0 (ccOperatorFieldComp g 0 0 0 S T) := by
    have h := tensorHsInclusion_scalarHsMul_zero g
      (ccTensorToHs g 0 ((1 : ℕ) : ℝ) S) (ccTensorToHs g 0 ((1 : ℕ) : ℝ) T)
    dsimp only at h
    simp only [scalarHsMul_apply_ccTensorToHs, ContinuousLinearMap.comp_apply,
      tensorHsInclusion_ccTensorToHs] at h
    exact h.symm
  change D (m u v) = _
  refine (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact D.continuous.comp (m.continuous.clm_apply continuous_const)
    · exact (((scalarH0ContinuousMul g).continuous.comp C.continuous).clm_apply
        continuous_const).add ((scalarH0ContinuousMul g (C v)).continuous.comp D.continuous)
  intro S
  refine (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on v ?_ ?_
  · apply isClosed_eq
    · exact D.continuous.comp (m (ccToHsLin g 0 ((1 : ℕ) : ℝ) S)).continuous
    · exact ((scalarH0ContinuousMul g (C (ccToHsLin g 0 ((1 : ℕ) : ℝ) S))).continuous.comp
        D.continuous).add (((scalarH0ContinuousMul g).continuous.comp C.continuous).clm_apply
          continuous_const)
  intro T
  simp only [ccToHsLin_apply, m, scalarHsMul_apply_ccTensorToHs, hD, hC,
    hmul0, parameterDerivativeCcTensor_ccOperatorFieldComp,
    ccTensorToHs_add]

theorem parameterDerivativeHs_scalarHsMul_of_one_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n)
    (u v : TensorHs g 0 0 ((n + 1 : ℕ) : ℝ)) :
    let D := (parameterDerivativeHs g n).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n)
    let m := scalarHsMul g n (by simpa using hn)
    D (scalarHsMul g (n + 1) (by simp) u v) =
      m (J u) (D v) + m (J v) (D u) := by
  intro D J m
  let M := scalarHsMul g (n + 1) (by simp)
  have hD (S : SmoothCcTensor g 0 0) :
      D (ccTensorToHs g 0 ((n + 1 : ℕ) : ℝ) S) =
        ccTensorToHs g 0 (n : ℝ) (parameterDerivativeCcTensor g S) := by
    simp only [D, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
      parameterDerivativeHs_apply_ccTensorToHs]
  have hJ (S : SmoothCcTensor g 0 0) :
      J (ccTensorToHs g 0 ((n + 1 : ℕ) : ℝ) S) =
        ccTensorToHs g 0 (n : ℝ) S := by
    simp only [J, tensorHsInclusion_ccTensorToHs]
  change D (M u v) = _
  refine (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact D.continuous.comp (M.continuous.clm_apply continuous_const)
    · exact ((m.continuous.comp J.continuous).clm_apply continuous_const).add
        ((m (J v)).continuous.comp D.continuous)
  intro S
  refine (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))).induction_on v ?_ ?_
  · apply isClosed_eq
    · exact D.continuous.comp (M (ccToHsLin g 0 ((n + 1 : ℕ) : ℝ) S)).continuous
    · exact ((m (J (ccToHsLin g 0 ((n + 1 : ℕ) : ℝ) S))).continuous.comp
        D.continuous).add ((m.continuous.comp J.continuous).clm_apply continuous_const)
  intro T
  simp only [ccToHsLin_apply, M, m, scalarHsMul_apply_ccTensorToHs, hD, hJ,
    parameterDerivativeCcTensor_ccOperatorFieldComp, ccTensorToHs_add]


theorem norm_parameterDerivativeHs_scalarHsMul_of_one_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n)
    (u v : TensorHs g 0 0 ((n + 1 : ℕ) : ℝ)) :
    let D := (parameterDerivativeHs g n).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n)
    let m := scalarHsMul g n (by simpa using hn)
    ‖D (scalarHsMul g (n + 1) (by simp) u v)‖ ≤
      ‖m‖ * (‖J u‖ * ‖D v‖ + ‖J v‖ * ‖D u‖) := by
  intro D J m
  rw [parameterDerivativeHs_scalarHsMul_of_one_le g hn u v]
  calc
    ‖m (J u) (D v) + m (J v) (D u)‖ ≤
        ‖m (J u) (D v)‖ + ‖m (J v) (D u)‖ := norm_add_le _ _
    _ ≤ ‖m‖ * ‖J u‖ * ‖D v‖ + ‖m‖ * ‖J v‖ * ‖D u‖ :=
      add_le_add (m.le_opNorm₂ _ _) (m.le_opNorm₂ _ _)
    _ = ‖m‖ * (‖J u‖ * ‖D v‖ + ‖J v‖ * ‖D u‖) := by ring


theorem parameterSecondDerivativeHs_scalarHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u v : TensorHs g 0 0 ((2 : ℕ) : ℝ)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
    let Q := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g 0).comp (tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))))
    let m := scalarH0ContinuousMul g
    Q (scalarHsMul g 2 (by norm_num) u v) =
      m (C (J u)) (Q v) + (2 : ℝ) • m (C (D u)) (Z (D v)) +
        m (C (J v)) (Q u) := by
  intro J Z C D Q m
  let D₀ := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).comp
      ((parameterDerivativeHs g 0).comp (tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ))))
  have hQ (w : TensorHs g 0 0 ((2 : ℕ) : ℝ)) : D₀ (D w) = Q w := by
    simp only [D₀, D, Q, parameterSecondDerivativeHs, ContinuousLinearMap.comp_apply]
    rw [← tensorHsInclusion_trans_apply]
  have hJ (w : TensorHs g 0 0 ((2 : ℕ) : ℝ)) : D₀ (J w) = Z (D w) := by
    have h := parameterDerivativeHs_tensorHsInclusion g (by decide : 0 ≤ 1)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)) w)
    have hh := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))) h
    simpa only [D₀, D, J, Z, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using hh
  have hfirst := parameterDerivativeHs_scalarHsMul_of_one_le g (by decide : 1 ≤ 1) u v
  change D (scalarHsMul g 2 (by norm_num) u v) =
    scalarHsMul g 1 (by norm_num) (J u) (D v) +
      scalarHsMul g 1 (by norm_num) (J v) (D u) at hfirst
  have h := congrArg D₀ hfirst
  rw [map_add] at h
  have hleft := parameterDerivativeHs_scalarHsMul g (J u) (D v)
  have hright := parameterDerivativeHs_scalarHsMul g (J v) (D u)
  change D₀ (scalarHsMul g 1 (by norm_num) (J u) (D v)) =
    m (C (J u)) (D₀ (D v)) + m (C (D v)) (D₀ (J u)) at hleft
  change D₀ (scalarHsMul g 1 (by norm_num) (J v) (D u)) =
    m (C (J v)) (D₀ (D u)) + m (C (D u)) (D₀ (J v)) at hright
  rw [hQ, hleft, hright, hQ, hQ, hJ, hJ] at h
  have hcomm := scalarH0ContinuousMul_scalarH1ToContinuous_comm g (D v) (D u)
  change m (C (D v)) (Z (D u)) = m (C (D u)) (Z (D v)) at hcomm
  rw [hcomm] at h
  rw [h]
  module

end AddCircle
