import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.ODE

open Set Filter
open scoped Topology

theorem gronwall_nonneg_on_of_deriv_ge_mul
    {u β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hβ_at : ∀ t ∈ Set.Icc a b, ContinuousAt β t)
    (hβ_meas : MeasureTheory.StronglyMeasurable β)
    (hu_cont : ∀ t ∈ Set.Icc a b, ContinuousAt u t)
    (hu_deriv : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ u t)
    (hineq : ∀ t ∈ Set.Icc a b, β t * u t ≤ deriv u t)
    (ha : 0 ≤ u a) :
    ∀ t ∈ Set.Icc a b, 0 ≤ u t := by
  have hβ_on : ∀ t ∈ Set.Icc a b, ContinuousOn β (Set.Icc a t) := by
    intro t ht x hx
    exact (hβ_at x ⟨hx.1, hx.2.trans ht.2⟩).continuousWithinAt
  let B : ℝ → ℝ := fun t => ∫ s in a..t, β s
  have hB_cont : ContinuousOn B (Set.Icc a b) := by
    have hcont : ContinuousOn β (Set.uIcc a b) := by
      rw [uIcc_of_le hab]
      intro t ht
      exact (hβ_at t ht).continuousWithinAt
    have hprim := intervalIntegral.continuousOn_primitive_interval
      (f := β) (a := a) (b := b) (μ := MeasureTheory.volume)
      (hcont.integrableOn_Icc (μ := MeasureTheory.volume))
    simpa [B, uIcc_of_le hab] using hprim
  have hB_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt B (β t) t := by
    intro t ht
    exact intervalIntegral.integral_hasDerivAt_right
      (ContinuousOn.intervalIntegrable_of_Icc ht.1 (hβ_on t ht))
      hβ_meas.stronglyMeasurableAtFilter
      (hβ_at t ht)
  let e : ℝ → ℝ := fun t => u t * Real.exp (-B t)
  have he_cont : ContinuousOn e (Set.Icc a b) := by
    intro t ht
    exact ((hu_cont t ht).continuousWithinAt).mul
      (((Real.continuous_exp.continuousAt).comp
        (continuousAt_neg.comp (hB_deriv t ht).continuousAt)).continuousWithinAt)
  have he_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt e ((deriv u t - β t * u t) * Real.exp (-B t)) t := by
    intro t ht
    have hu' : HasDerivAt u (deriv u t) t := (hu_deriv t ht).hasDerivAt
    have hB' : HasDerivAt B (β t) t := hB_deriv t ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-B s))
        (Real.exp (-B t) * -β t) t :=
      HasDerivAt.comp (x := t) (h := fun s : ℝ => -B s)
        (Real.hasDerivAt_exp (-B t)) (hB'.neg)
    have hprod := hu'.mul hexp
    dsimp [e]
    have hval : deriv u t * Real.exp (-B t) + -(u t * (Real.exp (-B t) * β t)) =
        (deriv u t - β t * u t) * Real.exp (-B t) := by
      ring
    simpa [hval] using hprod
  have he_mono : MonotoneOn e (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) he_cont ?_ ?_
    · intro t ht
      exact (he_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h := he_deriv t (interior_subset ht)
      rw [h.deriv]
      exact mul_nonneg (sub_nonneg.mpr (hineq t (interior_subset ht)))
        (Real.exp_pos _).le
  intro t ht
  have hm := he_mono ⟨le_rfl, hab⟩ ht ht.1
  have he_a : e a = u a := by
    simp [e, B]
  have he_t : 0 ≤ e t := by
    calc
      0 ≤ u a := ha
      _ = e a := he_a.symm
      _ ≤ e t := hm
  have hrec : u t = e t * Real.exp (B t) := by
    dsimp [e]
    rw [mul_assoc]
    nth_rewrite 1 [show Real.exp (-B t) * Real.exp (B t) = 1 by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]]
    ring
  rw [hrec]
  exact mul_nonneg he_t (Real.exp_pos _).le

theorem barrier_nonneg_on_of_derivPos_or_constAfter_of_zero
    {u : ℝ → ℝ} {a b : ℝ}
    (hu_cont : ∀ t ∈ Set.Icc a b, ContinuousAt u t)
    (ha : 0 ≤ u a)
    (hzero : ∀ t ∈ Set.Icc a b, u t = 0 →
      (DifferentiableAt ℝ u t ∧ 0 < deriv u t) ∨ ∀ s ∈ Set.Icc t b, u s = 0) :
    ∀ t ∈ Set.Icc a b, 0 ≤ u t := by
  intro t₁ ht₁
  by_contra hneg
  have hneg' : u t₁ < 0 := lt_of_not_ge hneg
  let Z : Set ℝ := {t | t ∈ Set.Icc a t₁ ∧ 0 ≤ u t}
  have hZne : Z.Nonempty := ⟨a, ⟨⟨le_rfl, ht₁.1⟩, ha⟩⟩
  have hZbdd : BddAbove Z := ⟨t₁, by intro t ht; exact ht.1.2⟩
  let t₀ : ℝ := sSup Z
  have ht₀_le_t₁ : t₀ ≤ t₁ := by
    exact csSup_le hZne (by intro t ht; exact ht.1.2)
  have ht₀_ge_a : a ≤ t₀ := by
    exact le_csSup hZbdd ⟨⟨le_rfl, ht₁.1⟩, ha⟩
  have hu₀_nonneg : 0 ≤ u t₀ := by
    by_contra hneg₀
    have hneg₀' : u t₀ < 0 := lt_of_not_ge hneg₀
    have ht₀mem : t₀ ∈ Set.Icc a b := ⟨ht₀_ge_a, ht₀_le_t₁.trans ht₁.2⟩
    have ht₀_gt_a : a < t₀ := by
      by_contra hle
      have heq : t₀ = a := le_antisymm (le_of_not_gt hle) ht₀_ge_a
      exact not_lt_of_ge (heq ▸ ha) hneg₀'
    have hnhds : Set.Iio (0 : ℝ) ∈ nhds (u t₀) := Iio_mem_nhds hneg₀'
    rcases Metric.mem_nhds_iff.mp ((hu_cont t₀ ht₀mem).preimage_mem_nhds hnhds) with
      ⟨ε, hε, hball⟩
    have hsSup_le : sSup Z ≤ t₀ - ε := by
      refine csSup_le hZne ?_
      intro z hz
      have hzpos : 0 ≤ u z := hz.2
      have hznot : z ∉ Metric.ball t₀ ε := by
        intro hzb
        exact not_lt_of_ge hzpos (hball hzb)
      by_contra hzge
      have hzge' : t₀ + ε ≤ z := by
        by_contra hzgt'
        have hz_in : z ∈ Metric.ball t₀ ε := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          exact ⟨by linarith, by linarith⟩
        exact hznot hz_in
      have hzle_t₀ : z ≤ sSup Z := le_csSup hZbdd hz
      linarith
    have hlt₀ : t₀ - ε < sSup Z := by linarith
    exact not_lt_of_ge hsSup_le hlt₀
  have ht₀_lt_t₁ : t₀ < t₁ := by
    by_contra hge
    have hle : t₁ ≤ t₀ := le_of_not_gt hge
    have heq : t₀ = t₁ := le_antisymm ht₀_le_t₁ hle
    exact not_lt_of_ge (heq ▸ hu₀_nonneg) hneg'
  have ht₀mem_ab : t₀ ∈ Set.Icc a b := ⟨ht₀_ge_a, ht₀_le_t₁.trans ht₁.2⟩
  have hu₀_nonpos : u t₀ ≤ 0 := by
    by_contra hpos
    have hpos' : 0 < u t₀ := lt_of_not_ge hpos
    have hnhds : Set.Ioi (0 : ℝ) ∈ nhds (u t₀) := Ioi_mem_nhds hpos'
    rcases Metric.mem_nhds_iff.mp ((hu_cont t₀ ht₀mem_ab).preimage_mem_nhds hnhds) with
      ⟨ε, hε, hball⟩
    let t₂ : ℝ := min (t₀ + ε / 2) ((t₀ + t₁) / 2)
    have ht₂_gt : t₀ < t₂ := by
      dsimp [t₂]
      exact lt_min (by linarith) (by linarith)
    have ht₂_lt : t₂ < t₁ := by
      dsimp [t₂]
      exact (min_le_right _ _).trans_lt (by linarith)
    have ht₂_ball : t₂ ∈ Metric.ball t₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr ht₂_gt.le)]
      dsimp [t₂]
      exact (sub_le_sub_right (min_le_left _ _) t₀).trans_lt (by linarith)
    have hu₂_pos : 0 < u t₂ := hball ht₂_ball
    have ht₂_mem : t₂ ∈ Z := ⟨⟨ht₀_ge_a.trans ht₂_gt.le, ht₂_lt.le⟩, hu₂_pos.le⟩
    have hle : t₂ ≤ sSup Z := le_csSup hZbdd ht₂_mem
    exact not_lt_of_ge hle ht₂_gt
  have hu₀ : u t₀ = 0 := le_antisymm hu₀_nonpos hu₀_nonneg
  have hlt_after : ∀ t ∈ Set.Ioc t₀ t₁, u t < 0 := by
    intro t ht
    by_contra hnn
    have hun : 0 ≤ u t := le_of_not_gt hnn
    have ht_mem : t ∈ Z := ⟨⟨ht₀_ge_a.trans ht.1.le, ht.2⟩, hun⟩
    have hle : t ≤ sSup Z := le_csSup hZbdd ht_mem
    exact not_lt_of_ge hle ht.1
  rcases hzero t₀ ht₀mem_ab hu₀ with ⟨hdiff, hdpos⟩ | hconst
  · have hd := hdiff.hasDerivAt
    have htend := hd.tendsto_slope_zero_right
    have hev := htend.eventually (Ioi_mem_nhds (half_lt_self hdpos))
    rcases Metric.mem_nhdsWithin_iff.mp hev with ⟨ε, hε, hball⟩
    let t₂ : ℝ := min (t₀ + ε / 2) ((t₀ + t₁) / 2)
    have ht₂_gt : t₀ < t₂ := by
      dsimp [t₂]
      exact lt_min (by linarith) (by linarith)
    have ht₂_lt : t₂ < t₁ := by
      dsimp [t₂]
      exact (min_le_right _ _).trans_lt (by linarith)
    have hincr_ball : t₂ - t₀ ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      rw [abs_of_nonneg (sub_nonneg.mpr ht₂_gt.le)]
      dsimp [t₂]
      exact (sub_le_sub_right (min_le_left _ _) t₀).trans_lt (by linarith)
    have hspos : (t₂ - t₀)⁻¹ • (u (t₀ + (t₂ - t₀)) - u t₀) ∈
        Set.Ioi ((deriv u t₀) / 2) :=
      hball ⟨hincr_ball, sub_pos.mpr ht₂_gt⟩
    have hspos' : (t₂ - t₀)⁻¹ • (u t₂ - u t₀) ∈ Set.Ioi ((deriv u t₀) / 2) := by
      have harg : t₀ + (t₂ - t₀) = t₂ := by ring
      simpa [harg] using hspos
    have huslope : 0 < (t₂ - t₀)⁻¹ • (u t₂ - 0) := by
      simpa [hu₀] using lt_of_lt_of_le (half_pos hdpos) (le_of_lt hspos')
    have hu₂ : 0 < u t₂ := by
      have hmul := mul_pos huslope (sub_pos.mpr ht₂_gt)
      have hrec : (t₂ - t₀)⁻¹ • (u t₂ - 0) * (t₂ - t₀) = u t₂ := by
        rw [show (t₂ - t₀)⁻¹ • (u t₂ - 0) = (u t₂ - 0) / (t₂ - t₀) by
          rw [div_eq_mul_inv, mul_comm, ← smul_eq_mul]]
        rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt ht₂_gt)), sub_zero]
      rwa [hrec] at hmul
    have hlt₂ := hlt_after t₂ ⟨ht₂_gt, ht₂_lt.le⟩
    exact not_lt_of_gt hu₂ hlt₂
  · have hu₁ : u t₁ = 0 := hconst t₁ ⟨ht₀_le_t₁, ht₁.2⟩
    exact (lt_irrefl (0 : ℝ)) (hu₁.symm ▸ hneg')

end DifferentialGeometry.Analysis.ODE
