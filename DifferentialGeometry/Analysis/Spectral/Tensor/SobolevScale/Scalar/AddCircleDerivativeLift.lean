import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.FractionalPower
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.ApplicationInclusion

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def derivativeHsNext
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 2) →L[ℝ] TensorHs g 0 0 ((n + 1 : ℕ) : ℝ) :=
  (parameterDerivativeHs g (n + 1)).comp
    (tensorHsInclusion (by push_cast; linarith :
      ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2))

private theorem parameterSecondDerivativeHs_eq_inclusion_derivativeHsNext
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u v : TensorHs g 0 0 ((n : ℝ) + 2))
    (h : derivativeHsNext g n u =
      tensorHsInclusion (by push_cast; linarith : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2) v) :
    parameterSecondDerivativeHs g n u =
      tensorHsInclusion (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
        (derivativeHsNext g n v) := by
  have hc := parameterDerivativeHs_tensorHsInclusion g (Nat.le_succ n)
    (tensorHsInclusion (by push_cast; linarith :
      ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2) v)
  simp only [← tensorHsInclusion_trans_apply] at hc
  change parameterDerivativeHs g n
    (tensorHsInclusion (by norm_num : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))
      (derivativeHsNext g n u)) = _
  rw [h, ← tensorHsInclusion_trans_apply]
  exact hc

private theorem parameterDerivativeHs_inclusion_eq_of_derivativeHsNext
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u v : TensorHs g 0 0 ((n : ℝ) + 2))
    (h : derivativeHsNext g n u =
      tensorHsInclusion (by push_cast; linarith : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2) v) :
    parameterDerivativeHs g n
      (tensorHsInclusion (by linarith : (n : ℝ) + 1 ≤ (n : ℝ) + 2) u) =
    tensorHsInclusion (by linarith : (n : ℝ) ≤ (n : ℝ) + 2) v := by
  have hc := parameterDerivativeHs_tensorHsInclusion g (Nat.le_succ n)
    (tensorHsInclusion (by push_cast; linarith :
      ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2) u)
  simp only [← tensorHsInclusion_trans_apply] at hc
  change _ = tensorHsInclusion _ (derivativeHsNext g n u) at hc
  rw [h, ← tensorHsInclusion_trans_apply] at hc
  exact hc

private def parameterDerivativeLaplacianLift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 2) →L[ℝ] TensorHs g 0 0 ((n + 1 : ℕ) : ℝ) :=
  (appHs g 0 0 (n + 1) (scalarCc g (laplacianPrincipalCoefficient g))).comp
    (derivativeHsNext g n) +
  (appHs g 0 0 (n + 1) (scalarCc g (laplacianDriftCoefficient g))).comp
    (tensorHsInclusion (by push_cast; linarith :
      ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2))

private theorem tensorHsInclusion_parameterDerivativeLaplacianLift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u v : TensorHs g 0 0 ((n : ℝ) + 2))
    (h : derivativeHsNext g n u =
      tensorHsInclusion (by push_cast; linarith : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2) v) :
    tensorHsInclusion (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
      (parameterDerivativeLaplacianLift g n v) = tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ) u := by
  have hQ := parameterSecondDerivativeHs_eq_inclusion_derivativeHsNext g n u v h
  have hD := parameterDerivativeHs_inclusion_eq_of_derivativeHsNext g n u v h
  rw [tensorScaleLaplacian_eq_principal_add_drift]
  simp only [parameterDerivativeLaplacianLift, add_apply,
    ContinuousLinearMap.comp_apply, map_add,
    tensorHsInclusion_appHs g 0 0 (Nat.le_succ n),
    ← tensorHsInclusion_trans_apply]
  rw [← hQ, ← hD]

private def parameterDerivativeReconstructionState
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 2) →L[ℝ]
      TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2) :=
  (tensorHsEquivOfFractionalPower (g := g) (r := 0) (s := 0)
    ((n + 1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ) + 2)).toLinearIsometry.toContinuousLinearMap.comp
      (tensorHsInclusion (by push_cast; linarith : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2))

private def parameterDerivativeReconstructionDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 2) →L[ℝ]
      TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2) :=
  (tensorHsEquivOfFractionalPower (g := g) (r := 0) (s := 0)
    ((n + 1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ) + 2)).toLinearIsometry.toContinuousLinearMap.comp
      (parameterDerivativeLaplacianLift g n)

private theorem tensorHsInclusion_parameterDerivativeReconstruction
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u v : TensorHs g 0 0 ((n : ℝ) + 2))
    (h : derivativeHsNext g n u =
      tensorHsInclusion (by push_cast; linarith : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2) v) :
    tensorHsInclusion (by push_cast; linarith :
      (n : ℝ) + 2 ≤ ((n + 1 : ℕ) : ℝ) + 2)
      (parameterDerivativeReconstructionState g n u -
        parameterDerivativeReconstructionDerivative g n v) = u := by
  have hL := tensorHsInclusion_parameterDerivativeLaplacianLift g n u v h
  apply TensorHs.ext
  funext i
  have hLi := congrArg (fun z => z.coeff i) hL
  simp only [tensorHsInclusion_coeff_apply, tensorScaleLaplacian_coeff] at hLi
  change (tensorHsInclusion _
    ((tensorHsEquivOfFractionalPower (g := g) (r := 0) (s := 0)
      ((n + 1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ) + 2))
        (tensorHsInclusion _ u) -
     (tensorHsEquivOfFractionalPower (g := g) (r := 0) (s := 0)
      ((n + 1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ) + 2))
        (parameterDerivativeLaplacianLift g n v))).coeff i = u.coeff i
  rw [← map_sub, tensorHsInclusion_coeff_apply, tensorHsEquivOfFractionalPower_coeff]
  change tensorSobolevWeight i _ *
    ((tensorHsInclusion _ u).coeff i - (parameterDerivativeLaplacianLift g n v).coeff i) = _
  rw [tensorHsInclusion_coeff_apply, hLi]
  have hbase : 1 + TensorEigenIdx.lambda i ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_one_add_lambda i))
  rw [show ((((n + 1 : ℕ) : ℝ) - (((n + 1 : ℕ) : ℝ) + 2)) / 2) = -1 by ring,
    tensorSobolevWeight, Real.rpow_neg (by linarith [one_le_one_add_lambda i]), Real.rpow_one]
  field_simp; ring

theorem exists_tensorHsInclusion_eq_of_parameterDerivative_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u v : TensorHs g 0 0 ((n : ℝ) + 2))
    (h : parameterDerivativeHs g (n + 1)
      (tensorHsInclusion (by push_cast; linarith :
        ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2) u) =
      tensorHsInclusion (by push_cast; linarith : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2) v) :
    ∃ w : TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2),
      tensorHsInclusion (by push_cast; linarith :
        (n : ℝ) + 2 ≤ ((n + 1 : ℕ) : ℝ) + 2) w = u :=
  ⟨parameterDerivativeReconstructionState g n u - parameterDerivativeReconstructionDerivative g n v,
    tensorHsInclusion_parameterDerivativeReconstruction g n u v h⟩

open MeasureTheory Filter
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem exists_timeL2_tensorHsInclusion_eq_of_parameterDerivative_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T σ : ℝ} (hσ : σ ≤ ((n + 1 : ℕ) : ℝ))
    (u v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) T)
    (h : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
      tensorHsInclusion hσ (parameterDerivativeHs g (n + 1)
        (tensorHsInclusion (by push_cast; linarith :
          ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2) (u t i))) =
      tensorHsInclusion (hσ.trans (by push_cast; linarith :
        ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2)) (v t i)) :
    ∃ w : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2))) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : (n : ℝ) + 2 ≤ ((n + 1 : ℕ) : ℝ) + 2))).compLpL
            2 (timeMeasure T) w = u := by
  let A := ContinuousLinearMap.piLpMap 2 (fun _ : ι => parameterDerivativeReconstructionState g n)
  let B := ContinuousLinearMap.piLpMap 2 (fun _ : ι => parameterDerivativeReconstructionDerivative g n)
  let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : (n : ℝ) + 2 ≤ ((n + 1 : ℕ) : ℝ) + 2))
  let w := A.compLpL 2 (timeMeasure T) u - B.compLpL 2 (timeMeasure T) v
  refine ⟨w, ?_⟩
  change K.compLpL 2 (timeMeasure T) w = u
  apply Lp.ext
  filter_upwards [K.coeFn_compLpL w, Lp.coeFn_sub (A.compLpL 2 (timeMeasure T) u)
    (B.compLpL 2 (timeMeasure T) v), A.coeFn_compLpL u, B.coeFn_compLpL v, h]
    with t hK hw hA hB ht
  rw [hK]
  rw [show w t = A (u t) - B (v t) by exact hw.trans (congrArg₂ (· - ·) hA hB)]
  apply PiLp.ext
  intro i
  have hi : derivativeHsNext g n (u t i) =
      tensorHsInclusion (by push_cast; linarith :
        ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2) (v t i) := by
    apply tensorHsInclusion_injective hσ
    rw [← tensorHsInclusion_trans_apply]
    exact ht i
  exact tensorHsInclusion_parameterDerivativeReconstruction g n (u t i) (v t i) hi

end AddCircle
