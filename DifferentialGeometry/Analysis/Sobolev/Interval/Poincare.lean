import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis

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
    change HasDerivAt ((fun _ : ℝ => Real.pi / 2) - fun s => a * (s + d)) (-a) t
    simpa only [zero_sub, mul_one] using
      (hasDerivAt_const t (Real.pi / 2)).sub (hshift.const_mul a)
  have htan :
      HasDerivAt
        (fun s : ℝ => Real.tan (Real.pi / 2 - a * (s + d)))
        ((1 / Real.cos θ ^ 2) * (-a)) t := by
    change HasDerivAt (Real.tan ∘ fun s : ℝ => Real.pi / 2 - a * (s + d))
      ((1 / Real.cos θ ^ 2) * (-a)) t
    exact (Real.hasDerivAt_tan hcos).comp t harg
  have hscaled := htan.const_mul a
  change HasDerivAt (fun y => a * Real.tan (Real.pi / 2 - a * (y + d)))
    (-a ^ 2 - (endWeight a d t) ^ 2) t
  apply hscaled.congr_deriv
  rw [endWeight, Real.tan_eq_sin_div_cos]
  change a * (1 / Real.cos θ ^ 2 * -a) =
    -a ^ 2 - (a * (Real.sin θ / Real.cos θ)) ^ 2
  field_simp [hcos]
  nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem poincare_unit_interval_subcritical
    {a : ℝ} (ha : 0 < a) (haπ : a < Real.pi / 2)
    {y v : ℝ → F}
    (hy : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt y (v t) (Set.Icc (0 : ℝ) 1) t)
    (hv : ContinuousOn v (Set.Icc (0 : ℝ) 1))
    (hy0 : y 0 = 0) :
    a ^ 2 * (∫ t in (0 : ℝ)..1, (⟪y t, y t⟫ : ℝ)) ≤
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
    change HasDerivWithinAt (φ * fun t => (⟪y t, y t⟫ : ℝ)) (dQ t)
      (Set.Icc (0 : ℝ) 1) t
    simpa only [dQ, real_inner_comm (y t) (v t)] using hprod
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
  have hQ1 : 0 ≤ Q 1 :=
    mul_nonneg hφ1.le real_inner_self_nonneg
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
  have henergy_nonneg :
      0 ≤ ∫ t in (0 : ℝ)..1,
        ((⟪v t, v t⟫ : ℝ) - a ^ 2 * (⟪y t, y t⟫ : ℝ)) := by
    rw [henergy, hFTC, hQ0, sub_zero]
    exact add_nonneg hSnonneg hQ1
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
    intervalIntegral.integral_const_mul] at henergy_nonneg
  linarith

private theorem poincare_unit_interval
    {y v : ℝ → F}
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt y (v t) (Icc (0 : ℝ) 1) t)
    (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    (hy0 : y 0 = 0) :
    (Real.pi / 2) ^ 2 * (∫ t in (0 : ℝ)..1, (⟪y t, y t⟫ : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (⟪v t, v t⟫ : ℝ) := by
  let Y : ℝ := ∫ t in (0 : ℝ)..1, (⟪y t, y t⟫ : ℝ)
  let V : ℝ := ∫ t in (0 : ℝ)..1, (⟪v t, v t⟫ : ℝ)
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg zero_le_one
    (fun _ _ => real_inner_self_nonneg)
  have hY : 0 ≤ Y := intervalIntegral.integral_nonneg zero_le_one
    (fun _ _ => real_inner_self_nonneg)
  change (Real.pi / 2) ^ 2 * Y ≤ V
  by_contra hbad
  have hlt : V < (Real.pi / 2) ^ 2 * Y := lt_of_not_ge hbad
  have hYpos : 0 < Y := by
    by_contra hyzero
    have : Y = 0 := le_antisymm (le_of_not_gt hyzero) hY
    rw [this, mul_zero] at hlt
    exact (not_lt_of_ge hV) hlt
  have hquot : V / Y < (Real.pi / 2) ^ 2 := (div_lt_iff₀ hYpos).mpr hlt
  obtain ⟨c, hc, hcp⟩ := exists_between hquot
  have hcpos : 0 < c := (div_nonneg hV hY).trans_lt hc
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
  have hsqrt2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hcpos.le
  have hsqrtpi : Real.sqrt c < Real.pi / 2 := by
    have : 0 < Real.pi / 2 := by positivity
    nlinarith
  have hp := poincare_unit_interval_subcritical
    hsqrt hsqrtpi hy hv hy0
  change Real.sqrt c ^ 2 * Y ≤ V at hp
  rw [hsqrt2] at hp
  have hcV : V < c * Y := (div_lt_iff₀ hYpos).mp hc
  exact (not_lt_of_ge hp) hcV

theorem poincare_interval_of_eq_zero_left
    {a b : ℝ} (hab : a ≤ b) {y v : ℝ → F}
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv : ContinuousOn v (Icc a b)) (hya : y a = 0) :
    (Real.pi / 2) ^ 2 * (∫ t in a..b, (⟪y t, y t⟫ : ℝ)) ≤
      (b - a) ^ 2 * ∫ t in a..b, (⟪v t, v t⟫ : ℝ) := by
  obtain hab | rfl := hab.lt_or_eq
  · let c := b - a
    have hc : 0 < c := sub_pos.mpr hab
    have hmap : MapsTo (fun t : ℝ => c * t + a) (Icc 0 1) (Icc a b) := by
      intro t ht
      constructor <;> dsimp only [c] <;> nlinarith [mul_nonneg hc.le ht.1,
        mul_le_mul_of_nonneg_left ht.2 hc.le]
    have hder : ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun t => y (c * t + a)) (c • v (c * t + a)) (Icc 0 1) t := by
      intro t ht
      exact (hy _ (hmap ht)).scomp t
        ((hasDerivAt_const_mul c).add_const a).hasDerivWithinAt hmap
    have hcont : ContinuousOn (fun t => c • v (c * t + a)) (Icc (0 : ℝ) 1) :=
      (hv.comp (continuousOn_const.mul continuousOn_id |>.add continuousOn_const) hmap).const_smul c
    have hzero : y (c * 0 + a) = 0 := by simpa using hya
    have hp := poincare_unit_interval hder hcont hzero
    have hY : (∫ t in (0 : ℝ)..1, (⟪y (c * t + a), y (c * t + a)⟫ : ℝ)) =
        c⁻¹ * ∫ t in a..b, (⟪y t, y t⟫ : ℝ) := by
      simpa only [mul_zero, zero_add, mul_one, c, sub_add_cancel, smul_eq_mul] using
        intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
          (fun t => (⟪y t, y t⟫ : ℝ)) hc.ne' a
    have hV : (∫ t in (0 : ℝ)..1, (⟪c • v (c * t + a), c • v (c * t + a)⟫ : ℝ)) =
        c ^ 2 * (c⁻¹ * ∫ t in a..b, (⟪v t, v t⟫ : ℝ)) := by
      have hvscale : (∫ t in (0 : ℝ)..1, (⟪v (c * t + a), v (c * t + a)⟫ : ℝ)) =
          c⁻¹ * ∫ t in a..b, (⟪v t, v t⟫ : ℝ) := by
        simpa only [mul_zero, zero_add, mul_one, c, sub_add_cancel, smul_eq_mul] using
          intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
            (fun t => (⟪v t, v t⟫ : ℝ)) hc.ne' a
      calc
        _ = ∫ t in (0 : ℝ)..1, c ^ 2 * (⟪v (c * t + a), v (c * t + a)⟫ : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          simp only [inner_smul_left, inner_smul_right, conj_trivial]
          ring
        _ = c ^ 2 * ∫ t in (0 : ℝ)..1, (⟪v (c * t + a), v (c * t + a)⟫ : ℝ) :=
          intervalIntegral.integral_const_mul _ _
        _ = _ := by rw [hvscale]
    rw [hY, hV] at hp
    have hm := mul_le_mul_of_nonneg_left hp hc.le
    have hle : (Real.pi / 2) ^ 2 * (c * c⁻¹) *
          (∫ t in a..b, (⟪y t, y t⟫ : ℝ)) ≤
        c ^ 2 * (c * c⁻¹) * ∫ t in a..b, (⟪v t, v t⟫ : ℝ) := by
      nlinarith only [hm]
    simpa only [mul_inv_cancel₀ hc.ne', mul_one, c] using hle
  · simp

theorem poincare_interval_lt_of_eq_zero_left
    {a b κ : ℝ} (hab : a < b) {y v : ℝ → F}
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv : ContinuousOn v (Icc a b)) (hya : y a = 0)
    (hy_ne : ¬ EqOn y (fun _ => 0) (Icc a b))
    (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2) :
    κ * (∫ t in a..b, (⟪y t, y t⟫ : ℝ)) <
      ∫ t in a..b, (⟪v t, v t⟫ : ℝ) := by
  have hycont : ContinuousOn y (Icc a b) := fun t ht => (hy t ht).continuousWithinAt
  have hyint : IntervalIntegrable (fun t => (⟪y t, y t⟫ : ℝ)) volume a b :=
    (hycont.inner hycont).intervalIntegrable_of_Icc hab.le
  have hY : 0 < ∫ t in a..b, (⟪y t, y t⟫ : ℝ) := by
    have hnonneg : 0 ≤ ∫ t in a..b, (⟪y t, y t⟫ : ℝ) :=
      intervalIntegral.integral_nonneg hab.le (fun _ _ => real_inner_self_nonneg)
    apply lt_of_le_of_ne hnonneg
    intro heq
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Filter.Eventually.of_forall (fun t => (real_inner_self_nonneg : 0 ≤ ⟪y t, y t⟫)))
      hyint).mp heq.symm
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae
    have hyae : y =ᵐ[volume.restrict (Icc a b)] (fun _ => 0) := by
      filter_upwards [hae] with t ht
      exact inner_self_eq_zero.mp ht
    have hyzero := Measure.eqOn_Icc_of_ae_eq volume hab.ne hyae hycont continuousOn_const
    exact hy_ne hyzero
  have hp := poincare_interval_of_eq_zero_left hab.le hy hv hya
  have hgap := mul_lt_mul_of_pos_right hκ hY
  apply lt_of_mul_lt_mul_left (a := (b - a) ^ 2) ?_ (sq_nonneg _)
  nlinarith only [hp, hgap]

end DifferentialGeometry.Analysis
