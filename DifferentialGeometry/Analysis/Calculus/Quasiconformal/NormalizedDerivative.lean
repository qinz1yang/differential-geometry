/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.DerivativeEccentricity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.NormalizedDerivative


open DerivativeEccentricity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

def normalizedTensor (A : E →L[ℝ] E) : E →L[ℝ] E :=
  (‖A‖ ^ 2)⁻¹ • (ContinuousLinearMap.adjoint A).comp A

omit [Nontrivial E] in
theorem inner_normalizedTensor (A : E →L[ℝ] E) (u v : E) :
    inner ℝ (normalizedTensor A u) v = (‖A‖ ^ 2)⁻¹ * inner ℝ (A u) (A v) := by
  simp only [normalizedTensor, smul_apply,
    real_inner_smul_left, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

omit [Nontrivial E] in
theorem normalizedTensor_nonneg (A : E →L[ℝ] E) (u : E) :
    0 ≤ inner ℝ (normalizedTensor A u) u := by
  rw [inner_normalizedTensor, real_inner_self_eq_norm_sq]
  positivity

omit [Nontrivial E] in
theorem norm_normalizedTensor (A : E →L[ℝ] E) (hA : A ≠ 0) :
    ‖normalizedTensor A‖ = 1 := by
  rw [normalizedTensor, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),
    ContinuousLinearMap.norm_adjoint_comp_self, ← pow_two,
    inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hA))]

omit [Nontrivial E] in
theorem normalizedTensor_zero : normalizedTensor (0 : E →L[ℝ] E) = 0 := by
  simp [normalizedTensor]

theorem normalizedTensor_id : normalizedTensor (ContinuousLinearMap.id ℝ E) =
    ContinuousLinearMap.id ℝ E := by
  ext1 u
  apply ext_inner_right ℝ
  intro v
  simp [inner_normalizedTensor]

omit [FiniteDimensional ℝ E] in
theorem inner_conformal (S : E →L[ℝ] E) (hS : IsConformalMap S) (u v : E) :
    inner ℝ (S u) (S v) = ‖S‖ ^ 2 * inner ℝ u v := by
  obtain ⟨c, _, R, rfl⟩ := hS
  simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map, norm_smul,
    LinearIsometry.norm_toContinuousLinearMap, mul_one, Real.norm_eq_abs, sq_abs]
  ring

theorem normalizedTensor_conformal_left (A S : E →L[ℝ] E) (hS : IsConformalMap S) :
    normalizedTensor (S.comp A) = normalizedTensor A := by
  have hS0 : ‖S‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hS.ne_zero)
  ext1 u
  apply ext_inner_right ℝ
  intro v
  rw [inner_normalizedTensor, inner_normalizedTensor, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, inner_conformal S hS,
    norm_comp_conformal_left A S hS, mul_pow, mul_inv_rev]
  rw [← mul_assoc, mul_assoc (‖A‖ ^ 2)⁻¹, inv_mul_cancel₀ hS0, mul_one]

theorem normalizedTensor_smul (A : E →L[ℝ] E) {c : ℝ} (hc : c ≠ 0) :
    normalizedTensor (c • A) = normalizedTensor A := by
  have hS : IsConformalMap (c • ContinuousLinearMap.id ℝ E) :=
    ⟨c, hc, LinearIsometry.id, rfl⟩
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using
    normalizedTensor_conformal_left A (c • ContinuousLinearMap.id ℝ E) hS

theorem normalizedTensor_isometric_right (A : E →L[ℝ] E) (R : E ≃ₗᵢ[ℝ] E) :
    normalizedTensor (A.comp R.toContinuousLinearEquiv.toContinuousLinearMap) =
      (ContinuousLinearMap.adjoint R.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((normalizedTensor A).comp R.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext1 u
  apply ext_inner_right ℝ
  intro v
  simp only [inner_normalizedTensor, norm_comp_isometryEquiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem normalizedTensor_eq_id_iff (A : E →L[ℝ] E) (hA : A ≠ 0) :
    normalizedTensor A = ContinuousLinearMap.id ℝ E ↔ IsConformalMap A := by
  constructor
  · intro hT
    have hn : ‖A‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hA)
    apply (isConformalMap_iff A).mpr
    refine ⟨‖A‖ ^ 2, sq_pos_of_pos (norm_pos_iff.mpr hA), fun u v => ?_⟩
    have he := inner_normalizedTensor A u v
    rw [hT, ContinuousLinearMap.id_apply] at he
    have hh := congrArg (fun r : ℝ => ‖A‖ ^ 2 * r) he
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at hh
    exact hh.symm
  · intro hAconf
    have h := normalizedTensor_conformal_left (ContinuousLinearMap.id ℝ E) A hAconf
    simpa only [ContinuousLinearMap.comp_id, normalizedTensor_id] using h

omit [Nontrivial E] in
theorem measurable_normalizedTensor : Measurable (normalizedTensor (E := E)) := by
  have hc : Continuous (fun A : E →L[ℝ] E => (ContinuousLinearMap.adjoint A).comp A) :=
    ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
  exact ((measurable_id.norm.pow_const 2).inv).smul hc.measurable

variable [MeasurableSpace E] [BorelSpace E]

def chartTensor (F : E → E) (x : E) : E →L[ℝ] E := normalizedTensor (fderiv ℝ F x)

omit [Nontrivial E] in
theorem measurable_chartTensor (F : E → E) : Measurable (chartTensor F) :=
  measurable_normalizedTensor.comp (measurable_fderiv ℝ F)


end DifferentialGeometry.NormalizedDerivative
