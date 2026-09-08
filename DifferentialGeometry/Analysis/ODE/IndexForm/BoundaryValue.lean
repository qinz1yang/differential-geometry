import DifferentialGeometry.Analysis.ODE.IndexForm.Basic
import DifferentialGeometry.Analysis.Sobolev.Interval.Poincare

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem IsJacobiFieldOn.eq_zero_of_endpoints_eq_zero
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {a b κ : ℝ}
    (hsol : IsJacobiFieldOn R a b y v)
    (hab : a ≤ b) (hya : y a = 0) (hyb : y b = 0)
    (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2)
    (hupper : ∀ t ∈ Ioo a b, ⟪R t (y t), y t⟫ ≤ κ * ‖y t‖ ^ 2) :
    EqOn y (fun _ => 0) (Icc a b) := by
  obtain hab | rfl := hab.lt_or_eq
  · by_contra hne
    have hyint : IntervalIntegrable (fun t => (⟪y t, y t⟫ : ℝ)) volume a b :=
      (hsol.contOn_fst.inner hsol.contOn_fst).intervalIntegrable_of_Icc hab.le
    have hvint : IntervalIntegrable (fun t => (⟪v t, v t⟫ : ℝ)) volume a b :=
      (hsol.contOn_snd.inner hsol.contOn_snd).intervalIntegrable_of_Icc hab.le
    have hlower : ContinuousOn (fun t => (⟪v t, v t⟫ : ℝ) - κ * ⟪y t, y t⟫)
        (Icc a b) :=
      (hsol.contOn_snd.inner hsol.contOn_snd).sub
        ((hsol.contOn_fst.inner hsol.contOn_fst).const_mul κ)
    have hmono : (∫ t in a..b, (⟪v t, v t⟫ : ℝ) - κ * ⟪y t, y t⟫) ≤
        ⟪v b, y b⟫ - ⟪v a, y a⟫ := by
      apply intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab.le
        (hsol.contOn_snd.inner hsol.contOn_fst)
        (fun t ht => (hsol.hasDerivAt_inner hsol.deriv_fst ht).hasDerivWithinAt)
        (hlower.integrableOn_Icc)
      intro t ht
      unfold indexIntegrand
      simp only [real_inner_self_eq_norm_sq]
      exact sub_le_sub_left (hupper t ht) _
    rw [hya, hyb, inner_zero_right, inner_zero_right, sub_self,
      intervalIntegral.integral_sub hvint (hyint.const_mul κ),
      intervalIntegral.integral_const_mul] at hmono
    have hp := poincare_interval_lt_of_eq_zero_left hab hsol.deriv_fst hsol.contOn_snd hya
      hne hκ
    linarith
  · intro t ht
    have ht : t = a := le_antisymm ht.2 ht.1
    simpa only [ht] using hya

end DifferentialGeometry.Analysis.ODE
