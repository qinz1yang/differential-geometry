import DifferentialGeometry.Analysis.ODE.Gronwall.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.ODE

theorem eq_exp_mul_of_integral_eq
    {T c x : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (heq : ∀ t ∈ Icc (0 : ℝ) T,
      f t = x + ∫ s in (0 : ℝ)..t, c * f s) :
    ∀ t ∈ Icc (0 : ℝ) T, f t = Real.exp (c * t) * x := by
  let g : ℝ → ℝ := fun t => Real.exp (c * t) * x
  have hg : Continuous g := by fun_prop
  have hgd (t : ℝ) : HasDerivAt g (c * g t) t := by
    simpa only [g, id_eq, mul_one, mul_assoc, mul_left_comm] using
      (((hasDerivAt_id t).const_mul c).exp.mul_const x)
  have hgi (t : ℝ) : g t = x + ∫ s in (0 : ℝ)..t, c * g s := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hgd s) ((continuous_const.mul hg).intervalIntegrable 0 t)
    rw [h]
    simp only [g, mul_zero, Real.exp_zero, one_mul]
    ring
  have hdiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      f t - g t = ∫ s in (0 : ℝ)..t, c * (f s - g s) := by
    have hft : IntervalIntegrable (fun s => c * f s) volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1
        ((continuousOn_const.mul hf).mono (Icc_subset_Icc le_rfl ht.2))
    have hgt : IntervalIntegrable (fun s => c * g s) volume 0 t :=
      (continuous_const.mul hg).intervalIntegrable _ _
    rw [heq t ht, hgi t, show (fun s => c * (f s - g s)) =
      (fun s => c * f s - c * g s) by funext s; ring,
      intervalIntegral.integral_sub hft hgt]
    ring
  have hbound : ∀ t ∈ Icc (0 : ℝ) T,
      ‖f t - g t‖ ≤ 0 + ‖c‖ * ∫ s in (0 : ℝ)..t, ‖f s - g s‖ := by
    intro t ht
    rw [hdiff t ht, zero_add]
    calc
      _ ≤ ∫ s in (0 : ℝ)..t, ‖c * (f s - g s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ = ‖c‖ * ∫ s in (0 : ℝ)..t, ‖f s - g s‖ := by
        simp only [norm_mul, intervalIntegral.integral_const_mul]
  have hgr := gronwall_integral_le hT (norm_nonneg c)
    ((hf.sub hg.continuousOn).norm) hbound
  intro t ht
  have hz : ‖f t - g t‖ = 0 := by
    have h := hgr t ht
    simp only [zero_mul] at h
    exact le_antisymm h (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end DifferentialGeometry.Analysis.ODE
