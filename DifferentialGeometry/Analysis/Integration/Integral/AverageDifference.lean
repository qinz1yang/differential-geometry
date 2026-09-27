import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous.Energy
import Mathlib.MeasureTheory.Integral.Average

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_setAverage_sub_const_sq_le {s : Set X} {f : X → F}
    (hs : 0 < μ.real s) (hf : MemLp f 2 (μ.restrict s)) (m : F) :
    ‖(⨍ x in s, f x ∂μ) - m‖ ^ 2 ≤
      (μ.real s)⁻¹ * ∫ x in s, ‖f x - m‖ ^ 2 ∂μ := by
  have hsfinite : μ s ≠ ∞ := (ENNReal.toReal_pos_iff.mp hs).2.ne
  let : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hsfinite
  have hfm : MemLp (fun x => f x - m) 2 (μ.restrict s) := hf.sub (memLp_const m)
  have hfi : IntegrableOn f s μ := hf.integrable (by norm_num)
  have hsub : (∫ x in s, f x - m ∂μ) = (∫ x in s, f x ∂μ) - μ.real s • m := by
    rw [integral_sub hfi (integrable_const m), setIntegral_const]
  have heq : (⨍ x in s, f x ∂μ) - m =
      (μ.real s)⁻¹ • ∫ x in s, f x - m ∂μ := by
    rw [setAverage_eq, hsub, smul_sub, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  have hnonneg : 0 ≤ ∫ x in s, ‖f x - m‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hnorm : ‖∫ x in s, f x - m ∂μ‖ ^ 2 ≤ (∫ x in s, ‖f x - m‖ ∂μ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr (norm_integral_le_integral_norm _)
  have hcs : (∫ x in s, ‖f x - m‖ ∂μ) ^ 2 ≤
      μ.real s * ∫ x in s, ‖f x - m‖ ^ 2 ∂μ := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      integral_sq_le_measure_mul_integral_sq hfm.norm
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs.le), mul_pow]
  calc
    _ ≤ ((μ.real s)⁻¹) ^ 2 *
        (μ.real s * ∫ x in s, ‖f x - m‖ ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hcs) (sq_nonneg _)
    _ = (μ.real s)⁻¹ * ∫ x in s, ‖f x - m‖ ^ 2 ∂μ := by field_simp

theorem norm_setAverage_sub_setAverage_sq_le {s t : Set X} {f : X → F}
    (hst : s ⊆ t) (hs : 0 < μ.real s) (ht : μ t ≠ ∞)
    (hf : MemLp f 2 (μ.restrict t)) :
    ‖(⨍ x in s, f x ∂μ) - (⨍ x in t, f x ∂μ)‖ ^ 2 ≤
      (μ.real s)⁻¹ * ∫ x in t, ‖f x - ⨍ y in t, f y ∂μ‖ ^ 2 ∂μ := by
  let : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.mpr ht
  have hfs : MemLp f 2 (μ.restrict s) := hf.mono_measure (Measure.restrict_mono_set μ hst)
  have hosc : IntegrableOn (fun x => ‖f x - ⨍ y in t, f y ∂μ‖ ^ 2) t μ :=
    (hf.sub (memLp_const _)).norm.integrable_sq
  apply (norm_setAverage_sub_const_sq_le hs hfs (⨍ y in t, f y ∂μ)).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
  exact setIntegral_mono_set hosc (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (Filter.Eventually.of_forall hst)

end DifferentialGeometry.Analysis

end
