import DifferentialGeometry.Analysis.ODE.IndexForm.Basic
import DifferentialGeometry.Analysis.Sobolev.Interval.Poincare

set_option autoImplicit false

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem IsJacobiFieldOn.inner_velocity_position_at_right_pos
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {κ : ℝ}
    (hR : ContinuousOn R (Set.Icc (0 : ℝ) 1))
    (hsol : IsJacobiFieldOn R 0 1 y v)
    (hy0 : y 0 = 0) (hy1 : y 1 ≠ 0)
    (hκ0 : 0 ≤ κ) (hκπ : κ < (Real.pi / 2) ^ 2)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ⟪R t (y t), y t⟫ ≤ κ * ‖y t‖ ^ 2) :
    0 < ⟪v 1, y 1⟫ := by
  let p : ℝ := Real.pi / 2
  let a : ℝ := Real.sqrt ((κ + p ^ 2) / 2)
  have hp : 0 < p := by
    dsimp only [p]
    exact div_pos Real.pi_pos (by norm_num)
  have havg : 0 < (κ + p ^ 2) / 2 := by
    have hpSq : 0 < p ^ 2 := sq_pos_of_pos hp
    positivity
  have ha : 0 < a := by
    exact Real.sqrt_pos.2 havg
  have haSq : a ^ 2 = (κ + p ^ 2) / 2 := by
    exact Real.sq_sqrt havg.le
  have hκp : κ < p ^ 2 := by
    simpa only [p] using hκπ
  have hap : a < p := by
    nlinarith [haSq]
  have hκa : κ < a ^ 2 := by
    rw [haSq]
    linarith
  have hpoincare :
      a ^ 2 * (∫ t in (0 : ℝ)..1, (⟪y t, y t⟫ : ℝ)) <
        ∫ t in (0 : ℝ)..1, (⟪v t, v t⟫ : ℝ) :=
    poincare_interval_lt_of_eq_zero_left zero_lt_one hsol.deriv_fst hsol.contOn_snd hy0
      (by intro hz; exact hy1 (hz (by simp)))
      (by
        have hapi : a < Real.pi / 2 := hap
        simpa only [sub_zero, one_pow, mul_one] using
          (show a ^ 2 < (Real.pi / 2) ^ 2 from by nlinarith))
  have hyEnergy_nonneg :
      0 ≤ ∫ t in (0 : ℝ)..1, (⟪y t, y t⟫ : ℝ) :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ =>
      real_inner_self_nonneg
  have hκenergy :
      κ * (∫ t in (0 : ℝ)..1, (⟪y t, y t⟫ : ℝ)) <
        ∫ t in (0 : ℝ)..1, (⟪v t, v t⟫ : ℝ) :=
    (mul_le_mul_of_nonneg_right hκa.le hyEnergy_nonneg).trans_lt hpoincare
  have hyInt :
      IntervalIntegrable (fun t => (⟪y t, y t⟫ : ℝ)) volume (0 : ℝ) 1 :=
    (hsol.contOn_fst.inner hsol.contOn_fst).intervalIntegrable_of_Icc
      zero_le_one
  have hvInt :
      IntervalIntegrable (fun t => (⟪v t, v t⟫ : ℝ)) volume (0 : ℝ) 1 :=
    (hsol.contOn_snd.inner hsol.contOn_snd).intervalIntegrable_of_Icc
      zero_le_one
  have hlower_pos :
      0 < ∫ t in (0 : ℝ)..1,
        ((⟪v t, v t⟫ : ℝ) - κ * (⟪y t, y t⟫ : ℝ)) := by
    rw [intervalIntegral.integral_sub hvInt (hyInt.const_mul κ),
      intervalIntegral.integral_const_mul]
    linarith
  have hlowerInt :
      IntervalIntegrable
        (fun t => (⟪v t, v t⟫ : ℝ) - κ * (⟪y t, y t⟫ : ℝ))
        volume (0 : ℝ) 1 := by
    have hcont :
        ContinuousOn
          (fun t => (⟪v t, v t⟫ : ℝ) - κ * (⟪y t, y t⟫ : ℝ))
          (Set.Icc (0 : ℝ) 1) :=
      (hsol.contOn_snd.inner hsol.contOn_snd).sub
        ((hsol.contOn_fst.inner hsol.contOn_fst).const_mul κ)
    exact hcont.intervalIntegrable_of_Icc zero_le_one
  have hindexInt :
      IntervalIntegrable (indexIntegrand R y v y v) volume (0 : ℝ) 1 :=
    (contOn_indexIntegrand hR hsol.contOn_fst hsol.contOn_snd
      hsol.contOn_fst hsol.contOn_snd).intervalIntegrable_of_Icc zero_le_one
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (⟪v t, v t⟫ : ℝ) - κ * (⟪y t, y t⟫ : ℝ) ≤
        indexIntegrand R y v y v t := by
    intro t ht
    unfold indexIntegrand
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    linarith [hupper t ht]
  have hmono :
      (∫ t in (0 : ℝ)..1,
          ((⟪v t, v t⟫ : ℝ) - κ * (⟪y t, y t⟫ : ℝ))) ≤
        indexForm R 0 1 y v y v := by
    simpa only [indexForm_def] using
      intervalIntegral.integral_mono_on zero_le_one hlowerInt hindexInt hpoint
  have hform_pos : 0 < indexForm R 0 1 y v y v :=
    hlower_pos.trans_le hmono
  rw [hsol.indexForm_eq_sub zero_le_one hR hsol.deriv_fst hsol.contOn_snd,
    hy0, inner_zero_right, sub_zero] at hform_pos
  exact hform_pos

end DifferentialGeometry.Analysis.ODE
