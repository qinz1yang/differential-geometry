import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import DifferentialGeometry.Analysis.Integration.Measure.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_quadratic_fderiv_comp_smul
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) {c : ℝ} (hc : c ≠ 0) (s : Set ℂ) :
    (∫ z in s,
      (A (f (c • z)) (fderiv ℝ (fun w => f (c • w)) z 1)
          (fderiv ℝ (fun w => f (c • w)) z 1) +
        A (f (c • z)) (fderiv ℝ (fun w => f (c • w)) z Complex.I)
          (fderiv ℝ (fun w => f (c • w)) z Complex.I)) / 2) =
      ∫ z in c • s,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  let e : ℂ → ℝ := fun z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  have he (z : ℂ) :
      (A (f (c • z)) (fderiv ℝ (fun w => f (c • w)) z 1)
          (fderiv ℝ (fun w => f (c • w)) z 1) +
        A (f (c • z)) (fderiv ℝ (fun w => f (c • w)) z Complex.I)
          (fderiv ℝ (fun w => f (c • w)) z Complex.I)) / 2 = c ^ 2 * e (c • z) := by
    simp only [fderiv_comp_smul, smul_apply, map_smul,
      smul_eq_mul, e]
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.setIntegral_comp_smul volume e s hc]
  simp only [Complex.finrank_real_complex, smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg c))]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc), one_mul]

theorem integral_quadratic_fderiv_comp_smul_closedBall
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) {a R : ℝ}
    (ha : 0 < a) (hR : 0 < R) :
    (∫ z in Metric.closedBall (0 : ℂ) a,
      (A (f ((R / a) • z)) (fderiv ℝ (fun w => f ((R / a) • w)) z 1)
          (fderiv ℝ (fun w => f ((R / a) • w)) z 1) +
        A (f ((R / a) • z)) (fderiv ℝ (fun w => f ((R / a) • w)) z Complex.I)
          (fderiv ℝ (fun w => f ((R / a) • w)) z Complex.I)) / 2) =
      ∫ z in Metric.closedBall (0 : ℂ) R,
        (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  rw [integral_quadratic_fderiv_comp_smul A f (div_pos hR ha).ne',
    smul_closedBall' (div_pos hR ha).ne', smul_zero, Real.norm_eq_abs,
    abs_of_pos (div_pos hR ha), div_mul_cancel₀ _ ha.ne']

end DifferentialGeometry.Analysis

end

noncomputable section
open Set MeasureTheory

namespace DifferentialGeometry.Analysis

theorem integral_sq_mul_comp_add_smul_plane
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (b : EuclideanSpace ℝ (Fin 2))
    {a : ℝ} (ha : a ≠ 0) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    (∫ x in (fun y => b + a • y) ⁻¹' S, a ^ 2 * f (b + a • x)) = ∫ x in S, f x := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
    (MeasurableEquiv.smul₀ a ha).trans (MeasurableEquiv.addLeft b)
  have hmap : (volume.restrict (e ⁻¹' S)).map e =
      ENNReal.ofReal |(a ^ 2)⁻¹| • volume.restrict S := by
    have he : (e : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) =
        fun x => b + a • x := rfl
    rw [he]
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      Measure.map_add_smul_restrict_addHaar volume b ha S
  change (∫ x in e ⁻¹' S, a ^ 2 * f (e x)) = _
  rw [integral_const_mul, ← integral_map_equiv e, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, ← mul_assoc]
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a)), mul_inv_cancel₀ (pow_ne_zero 2 ha), one_mul]

theorem integral_quadratic_comp_add_smul_plane
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : EuclideanSpace ℝ (Fin 2) → F →L[ℝ] F →L[ℝ] ℝ)
    (G : EuclideanSpace ℝ (Fin 2) → F) (b : EuclideanSpace ℝ (Fin 2))
    {a : ℝ} (ha : a ≠ 0) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    (∫ x in (fun y => b + a • y) ⁻¹' S,
      A (b + a • x) (a • G (b + a • x)) (a • G (b + a • x))) =
      ∫ x in S, A x (G x) (G x) := by
  convert integral_sq_mul_comp_add_smul_plane (fun x => A x (G x) (G x)) b ha S using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

end DifferentialGeometry.Analysis

end

noncomputable section
open Set MeasureTheory

namespace DifferentialGeometry.Analysis



theorem preimage_smul_ball_zero_plane {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (fun x : EuclideanSpace ℝ (Fin 2) => a • x) ⁻¹' Metric.ball 0 R =
      Metric.ball 0 (R / a) := by
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha]
  rw [lt_div_iff₀ ha, mul_comm a]

theorem preimage_smul_closedBall_zero_plane {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (fun x : EuclideanSpace ℝ (Fin 2) => a • x) ⁻¹' Metric.closedBall 0 R =
      Metric.closedBall 0 (R / a) := by
  ext x
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha]
  rw [le_div_iff₀ ha, mul_comm a]

end DifferentialGeometry.Analysis

end

noncomputable section
open Set MeasureTheory

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem preimage_add_smul_ball_plane (b z : V) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (fun x : V => b + a • x) ⁻¹' Metric.ball (b + a • z) R =
      Metric.ball z (R / a) := by
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_add_left, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos ha]
  rw [lt_div_iff₀ ha, mul_comm a]

theorem preimage_add_smul_closedBall_plane (b z : V) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (fun x : V => b + a • x) ⁻¹' Metric.closedBall (b + a • z) R =
      Metric.closedBall z (R / a) := by
  ext x
  simp only [mem_preimage, Metric.mem_closedBall, dist_add_left, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos ha]
  rw [le_div_iff₀ ha, mul_comm a]

end DifferentialGeometry.Analysis

end
