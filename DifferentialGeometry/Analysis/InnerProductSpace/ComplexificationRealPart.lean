import DifferentialGeometry.Analysis.InnerProductSpace.Complexification

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace TensorProduct

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable def ofRealLI : H →ₗᵢ[ℝ] ℂ ⊗[ℝ] H where
  toLinearMap := (mkL ℝ ℂ H 1).toLinearMap
  norm_map' x := by
    change ‖(1 : ℂ) ⊗ₜ[ℝ] x‖ = ‖x‖
    simp only [norm_tmul, norm_one, one_mul]

@[simp] theorem ofRealLI_apply (x : H) : ofRealLI H x = 1 ⊗ₜ[ℝ] x := rfl

noncomputable def realPartL : (ℂ ⊗[ℝ] H) →L[ℝ] H :=
  (lidIsometry ℝ H).toLinearIsometry.toContinuousLinearMap ∘L
    mapL Complex.reCLM (ContinuousLinearMap.id ℝ H)

@[simp] theorem realPartL_tmul (z : ℂ) (x : H) :
    realPartL H (z ⊗ₜ[ℝ] x) = z.re • x := rfl

theorem norm_realPartL_apply_le (u : ℂ ⊗[ℝ] H) : ‖realPartL H u‖ ≤ ‖u‖ := by
  have hr : ‖Complex.reCLM‖ ≤ (1 : ℝ) :=
    Complex.reCLM.opNorm_le_bound zero_le_one fun z => by
      simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z
  have hm : ‖mapL Complex.reCLM (ContinuousLinearMap.id ℝ H)‖ ≤ (1 : ℝ) := by
    calc
      _ ≤ ‖Complex.reCLM‖ * ‖ContinuousLinearMap.id ℝ H‖ := norm_mapL_le _ _
      _ ≤ 1 * 1 := mul_le_mul hr ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  change ‖(lidIsometry ℝ H) (mapL Complex.reCLM (ContinuousLinearMap.id ℝ H) u)‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  exact ((mapL Complex.reCLM (ContinuousLinearMap.id ℝ H)).le_opNorm u).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (norm_nonneg u))

theorem norm_realPartL_le : ‖realPartL H‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_realPartL_apply_le H u

theorem realPartL_ofRealLI (x : H) : realPartL H (ofRealLI H x) = x := by
  rw [ofRealLI_apply, realPartL_tmul, Complex.one_re, one_smul]

end TensorProduct

namespace ContinuousLinearMap

variable (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

noncomputable def realPartOperator :
    ((ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] K)) →L[ℝ] (H →L[ℝ] K) :=
  (compL ℝ H (ℂ ⊗[ℝ] K) K (TensorProduct.realPartL K)).comp
    (((compL ℝ H (ℂ ⊗[ℝ] H) (ℂ ⊗[ℝ] K)).flip
      (TensorProduct.ofRealLI H).toContinuousLinearMap).comp
      (restrictScalarsL ℂ (ℂ ⊗[ℝ] H) (ℂ ⊗[ℝ] K) ℝ ℝ))

@[simp] theorem realPartOperator_apply
    (T : (ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] K)) (x : H) :
    realPartOperator H K T x = TensorProduct.realPartL K (T (1 ⊗ₜ[ℝ] x)) := rfl

theorem norm_realPartOperator_apply_le
    (T : (ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] K)) : ‖realPartOperator H K T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖realPartOperator H K T x‖ ≤ ‖T (1 ⊗ₜ[ℝ] x)‖ :=
      TensorProduct.norm_realPartL_apply_le K _
    _ ≤ ‖T‖ * ‖1 ⊗ₜ[ℝ] x‖ := T.le_opNorm _
    _ = ‖T‖ * ‖x‖ := by simp only [TensorProduct.norm_tmul, norm_one, one_mul]

theorem norm_realPartOperator_le : ‖realPartOperator H K‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa only [one_mul] using norm_realPartOperator_apply_le H K T

@[simp] theorem realPartOperator_complexify (A : H →L[ℝ] K) :
    realPartOperator H K A.complexify = A := by
  ext x
  simp only [realPartOperator_apply, complexify_tmul, TensorProduct.realPartL_tmul,
    Complex.one_re, one_smul]

theorem realPartOperator_comp_complexify :
    (realPartOperator H K).comp
      (complexifyₗᵢ (H := H) (K := K)).toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (H →L[ℝ] K) := by
  ext A x
  exact congrArg (fun B : H →L[ℝ] K => B x) (realPartOperator_complexify H K A)

end ContinuousLinearMap
