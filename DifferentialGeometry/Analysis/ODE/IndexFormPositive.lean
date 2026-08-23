import DifferentialGeometry.Analysis.ODE.IndexForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

set_option autoImplicit false

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private def endWeight (a d t : ℝ) : ℝ :=
  a * Real.tan (Real.pi / 2 - a * (t + d))

private theorem hasDerivAt_endWeight
    {a d t : ℝ}
    (hangle :
      Real.pi / 2 - a * (t + d) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (endWeight a d) (-a ^ 2 - (endWeight a d t) ^ 2) t := by
  let θ : ℝ := Real.pi / 2 - a * (t + d)
  have hcos : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo hangle).ne'
  have hshift : HasDerivAt (fun s : ℝ => s + d) 1 t :=
    (hasDerivAt_id t).add_const d
  have harg :
      HasDerivAt (fun s : ℝ => Real.pi / 2 - a * (s + d)) (-a) t := by
    convert (hasDerivAt_const t (Real.pi / 2)).sub
      (hshift.const_mul a) using 1
    ring
  have htan :
      HasDerivAt
        (fun s : ℝ => Real.tan (Real.pi / 2 - a * (s + d)))
        ((1 / Real.cos θ ^ 2) * (-a)) t := by
    simpa only [θ] using (Real.hasDerivAt_tan hcos).comp t harg
  have hscaled := htan.const_mul a
  convert hscaled using 1
  · rw [endWeight, Real.tan_eq_sin_div_cos]
    change
      -a ^ 2 - (a * (Real.sin θ / Real.cos θ)) ^ 2 =
        a * (1 / Real.cos θ ^ 2 * -a)
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem left_poincare_lt
    {a : ℝ} (ha : 0 < a) (haπ : a < Real.pi / 2)
    {y v : ℝ → F}
    (hy : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt y (v t) (Set.Icc (0 : ℝ) 1) t)
    (hv : ContinuousOn v (Set.Icc (0 : ℝ) 1))
    (hy0 : y 0 = 0) (hy1 : y 1 ≠ 0) :
    a ^ 2 * (∫ t in (0 : ℝ)..1, (⟪y t, y t⟫ : ℝ)) <
      ∫ t in (0 : ℝ)..1, (⟪v t, v t⟫ : ℝ) := by
  let d : ℝ := (Real.pi / 2 - a) / (2 * a)
  let φ : ℝ → ℝ := endWeight a d
  let Q : ℝ → ℝ := fun t => φ t * (⟪y t, y t⟫ : ℝ)
  let dQ : ℝ → ℝ := fun t =>
    (-a ^ 2 - (φ t) ^ 2) * (⟪y t, y t⟫ : ℝ) +
      φ t * ((⟪v t, y t⟫ : ℝ) + (⟪y t, v t⟫ : ℝ))
  let S : ℝ → ℝ := fun t =>
    (⟪v t - φ t • y t, v t - φ t • y t⟫ : ℝ)
  have hd : 0 < d := by
    exact div_pos (sub_pos.mpr haπ) (mul_pos (by norm_num) ha)
  have had : a * (1 + d) < Real.pi / 2 := by
    have ha0 : a ≠ 0 := ha.ne'
    have had_eq : a * d = (Real.pi / 2 - a) / 2 := by
      dsimp only [d]
      field_simp
    calc
      a * (1 + d) = a + a * d := by ring
      _ = a + (Real.pi / 2 - a) / 2 := by rw [had_eq]
      _ < Real.pi / 2 := by linarith
  have hangle : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.pi / 2 - a * (t + d) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro t ht
    have htd : 0 < t + d := add_pos_of_nonneg_of_pos ht.1 hd
    have htd_le : t + d ≤ 1 + d := by
      simpa only [add_comm] using add_le_add_right ht.2 d
    have hmul_pos : 0 < a * (t + d) := mul_pos ha htd
    have hmul_lt : a * (t + d) < Real.pi / 2 :=
      (mul_le_mul_of_nonneg_left htd_le ha.le).trans_lt had
    constructor <;> linarith [Real.pi_pos]
  have hφderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ (-a ^ 2 - (φ t) ^ 2) t := by
    intro t ht
    exact hasDerivAt_endWeight (hangle t ht)
  have hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hφderiv t ht).continuousAt.continuousWithinAt
  have hycont : ContinuousOn y (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hy t ht).continuousWithinAt
  have hQderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Q (dQ t) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hinner := (hy t ht).inner ℝ (hy t ht)
    have hprod := (hφderiv t ht).hasDerivWithinAt.mul hinner
    simpa only [Q, dQ, Pi.mul_apply, real_inner_comm (y t) (v t)] using hprod
  have hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1) :=
    hφcont.mul (hycont.inner hycont)
  have hdQcont : ContinuousOn dQ (Set.Icc (0 : ℝ) 1) :=
    ((continuousOn_const.sub (hφcont.pow 2)).mul (hycont.inner hycont)).add
      (hφcont.mul ((hv.inner hycont).add (hycont.inner hv)))
  have hdQint : IntervalIntegrable dQ volume (0 : ℝ) 1 :=
    (by
      have hcont : ContinuousOn dQ (Set.uIcc (0 : ℝ) 1) := by
        simpa only [uIcc_of_le zero_le_one] using hdQcont
      exact hcont.intervalIntegrable)
  have hFTC :
      (∫ t in (0 : ℝ)..1, dQ t) = Q 1 - Q 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      zero_le_one hQcont
    · intro t ht
      exact
        ((hQderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
    · exact hdQint
  have hQ0 : Q 0 = 0 := by
    simp only [Q, hy0, inner_zero_right, mul_zero]
  have hφ1 : 0 < φ 1 := by
    have hθ := hangle 1 ⟨zero_le_one, le_rfl⟩
    exact mul_pos ha
      (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [hθ.1]) hθ.2)
  have hQ1 : 0 < Q 1 :=
    mul_pos hφ1 ((real_inner_self_pos).2 hy1)
  have hSint : IntervalIntegrable S volume (0 : ℝ) 1 := by
    have hcont : ContinuousOn S (Set.Icc (0 : ℝ) 1) :=
      (hv.sub (hφcont.smul hycont)).inner
        (hv.sub (hφcont.smul hycont))
    have hcont' : ContinuousOn S (Set.uIcc (0 : ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using hcont
    exact hcont'.intervalIntegrable
  have hSnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, S t :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ =>
      real_inner_self_nonneg
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (⟪v t, v t⟫ : ℝ) - a ^ 2 * (⟪y t, y t⟫ : ℝ) =
        S t + dQ t := by
    intro t _
    simp only [S, dQ, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (y t) (v t)]
    ring
  have henergy :
      (∫ t in (0 : ℝ)..1,
          ((⟪v t, v t⟫ : ℝ) - a ^ 2 * (⟪y t, y t⟫ : ℝ))) =
        (∫ t in (0 : ℝ)..1, S t) + ∫ t in (0 : ℝ)..1, dQ t := by
    rw [intervalIntegral.integral_congr
      (g := fun t => S t + dQ t)
      (fun t ht => hpoint t (by
        simpa only [uIcc_of_le zero_le_one] using ht))]
    exact intervalIntegral.integral_add hSint hdQint
  have henergy_pos :
      0 < ∫ t in (0 : ℝ)..1,
        ((⟪v t, v t⟫ : ℝ) - a ^ 2 * (⟪y t, y t⟫ : ℝ)) := by
    rw [henergy, hFTC, hQ0, sub_zero]
    exact add_pos_of_nonneg_of_pos hSnonneg hQ1
  have hvint :
      IntervalIntegrable (fun t => (⟪v t, v t⟫ : ℝ)) volume (0 : ℝ) 1 :=
    (by
      have hcont : ContinuousOn (fun t => (⟪v t, v t⟫ : ℝ))
          (Set.uIcc (0 : ℝ) 1) := by
        simpa only [uIcc_of_le zero_le_one] using hv.inner hv
      exact hcont.intervalIntegrable)
  have hyint :
      IntervalIntegrable (fun t => (⟪y t, y t⟫ : ℝ)) volume (0 : ℝ) 1 :=
    (by
      have hcont : ContinuousOn (fun t => (⟪y t, y t⟫ : ℝ))
          (Set.uIcc (0 : ℝ) 1) := by
        simpa only [uIcc_of_le zero_le_one] using hycont.inner hycont
      exact hcont.intervalIntegrable)
  rw [intervalIntegral.integral_sub hvint (hyint.const_mul (a ^ 2)),
    intervalIntegral.integral_const_mul] at henergy_pos
  linarith

theorem IsJacobiSolOn.end_pair_pos
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {κ : ℝ}
    (hR : ContinuousOn R (Set.Icc (0 : ℝ) 1))
    (hsol : IsJacobiSolOn R 0 1 y v)
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
    left_poincare_lt ha hap hsol.deriv_fst hsol.contOn_snd hy0 hy1
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
