import DifferentialGeometry.Analysis.Integration.Holder.Weighted
import DifferentialGeometry.Analysis.Parabolic.Moser.Iteration
import DifferentialGeometry.Analysis.Parabolic.Moser.LogTail
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Geometry.Operator

variable {α : Type*} [MeasurableSpace α]

def bombieriGiustiExponent (p₀ c₀ β : ℝ) : ℝ :=
  (p₀⁻¹ + β / (2 * Real.log (β / (2 * c₀))))⁻¹

theorem bombieriGiustiExponent_pos
    {p₀ c₀ β : ℝ} (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hβ : 2 * c₀ < β) :
    0 < bombieriGiustiExponent p₀ c₀ β := by
  have hβ_pos : 0 < β := (mul_pos (by norm_num) hc₀).trans hβ
  have hratio : 1 < β / (2 * c₀) := (one_lt_div (mul_pos (by norm_num) hc₀)).2 hβ
  have hlog : 0 < Real.log (β / (2 * c₀)) := Real.log_pos hratio
  exact inv_pos.mpr (add_pos (inv_pos.mpr hp₀)
    (div_pos hβ_pos (mul_pos (by norm_num) hlog)))

theorem bombieriGiustiExponent_lt
    {p₀ c₀ β : ℝ} (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hβ : 2 * c₀ < β) :
    bombieriGiustiExponent p₀ c₀ β < p₀ := by
  have hβ_pos : 0 < β := (mul_pos (by norm_num) hc₀).trans hβ
  have hratio : 1 < β / (2 * c₀) := (one_lt_div (mul_pos (by norm_num) hc₀)).2 hβ
  have hlog : 0 < Real.log (β / (2 * c₀)) := Real.log_pos hratio
  have hterm : 0 < β / (2 * Real.log (β / (2 * c₀))) :=
    div_pos hβ_pos (mul_pos (by norm_num) hlog)
  have hdenom : 0 < p₀⁻¹ + β / (2 * Real.log (β / (2 * c₀))) :=
    add_pos (inv_pos.mpr hp₀) hterm
  have hinv := (inv_lt_inv₀ hdenom (inv_pos.mpr hp₀)).2
    (lt_add_of_pos_right p₀⁻¹ hterm)
  simpa only [bombieriGiustiExponent, inv_inv] using hinv

theorem bombieriGiustiExponent_inv_sub
    (p₀ c₀ β : ℝ) :
    1 / bombieriGiustiExponent p₀ c₀ β - 1 / p₀ =
      β / (2 * Real.log (β / (2 * c₀))) := by
  simp only [bombieriGiustiExponent, one_div, inv_inv]
  ring

theorem lt_bombieriGiustiExponent_inv_sub
    {p₀ c₀ β : ℝ} (hc₀ : 0 < c₀) (hβ : 2 * c₀ < β) :
    c₀ < 1 / bombieriGiustiExponent p₀ c₀ β - 1 / p₀ := by
  rw [bombieriGiustiExponent_inv_sub]
  let x := β / (2 * c₀)
  have hx : 1 < x := (one_lt_div (mul_pos (by norm_num) hc₀)).2 hβ
  have hx_pos : 0 < x := zero_lt_one.trans hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hlog_lt : Real.log x < x :=
    (Real.log_lt_sub_one_of_pos hx_pos hx.ne').trans (sub_lt_self x one_pos)
  have hmul : c₀ * (2 * Real.log x) < β := by
    calc
      c₀ * (2 * Real.log x) < c₀ * (2 * x) := by
        exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hlog_lt (by norm_num)) hc₀
      _ = β := by
        dsimp only [x]
        field_simp [hc₀.ne']
  exact (lt_div_iff₀ (mul_pos (by norm_num) hlog_pos)).2 (by
    simpa only [x] using hmul)

theorem bombieriGiustiExponent_lt_one
    {p₀ c₀ β : ℝ} (hp₀ : 0 < p₀) (hc₀ : 1 ≤ c₀) (hβ : 2 * c₀ < β) :
    bombieriGiustiExponent p₀ c₀ β < 1 := by
  have hc₀_pos : 0 < c₀ := zero_lt_one.trans_le hc₀
  have hp := bombieriGiustiExponent_pos hp₀ hc₀_pos hβ
  have hgap := lt_bombieriGiustiExponent_inv_sub (p₀ := p₀) hc₀_pos hβ
  have hinv : 1 < 1 / bombieriGiustiExponent p₀ c₀ β := by
    have hp₀_inv : 0 < 1 / p₀ := div_pos one_pos hp₀
    linarith
  have h := one_div_lt_one_div_of_lt one_pos hinv
  simpa only [one_div_one, one_div_div, div_one] using h

theorem bombieriGiustiExponent_lt_mul
    {p₀ c₀ β η : ℝ}
    (hp₀ : 0 < p₀) (hη : 0 < η) (hc₀ : 0 < c₀)
    (hc₀η : 1 / (η * p₀) ≤ c₀) (hβ : 2 * c₀ < β) :
    bombieriGiustiExponent p₀ c₀ β < η * p₀ := by
  have hηp₀ : 0 < η * p₀ := mul_pos hη hp₀
  have hp := bombieriGiustiExponent_pos hp₀ hc₀ hβ
  have hgap := lt_bombieriGiustiExponent_inv_sub (p₀ := p₀) hc₀ hβ
  have hinv : 1 / (η * p₀) < 1 / bombieriGiustiExponent p₀ c₀ β := by
    have hp₀_inv : 0 < 1 / p₀ := div_pos one_pos hp₀
    linarith
  exact (inv_lt_inv₀ hηp₀ hp).mp (by
    simpa only [one_div] using hinv)

theorem bombieriGiusti_tail_power
    {p₀ c₀ β : ℝ} (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hβ : 2 * c₀ < β) :
    let p := bombieriGiustiExponent p₀ c₀ β
    (2 * c₀ / β) ^ (1 - p / p₀) = Real.exp (-p * β / 2) := by
  let p := bombieriGiustiExponent p₀ c₀ β
  have hp : 0 < p := bombieriGiustiExponent_pos hp₀ hc₀ hβ
  have hβ_pos : 0 < β := (mul_pos (by norm_num) hc₀).trans hβ
  have hbase : 0 < 2 * c₀ / β := div_pos (mul_pos (by norm_num) hc₀) hβ_pos
  have hbase_inv : 2 * c₀ / β = (β / (2 * c₀))⁻¹ := by
    field_simp [hc₀.ne', hβ_pos.ne']
  have hlog : Real.log (2 * c₀ / β) = -Real.log (β / (2 * c₀)) := by
    rw [hbase_inv, Real.log_inv]
  have hexponent : 1 - p / p₀ =
      p * (1 / p - 1 / p₀) := by
    field_simp [hp.ne', hp₀.ne']
  change (2 * c₀ / β) ^ (1 - p / p₀) = Real.exp (-p * β / 2)
  rw [Real.rpow_def_of_pos hbase, hlog, hexponent]
  congr 1
  rw [show 1 / p - 1 / p₀ =
      β / (2 * Real.log (β / (2 * c₀))) by
    simpa only [p] using bombieriGiustiExponent_inv_sub p₀ c₀ β]
  have hlog_pos : 0 < Real.log (β / (2 * c₀)) := by
    exact Real.log_pos ((one_lt_div (mul_pos (by norm_num) hc₀)).2 hβ)
  field_simp [hlog_pos.ne']

theorem integral_rpow_le_of_log_superlevel
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    {p q level tail : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hfq : Integrable (fun x => f x ^ q) μ)
    (htail : μ.real {x | level < Real.log (f x)} ≤ tail) :
    (∫ x, f x ^ p ∂μ) ≤
      Real.exp (p * level) * μ.real Set.univ +
        (∫ x, f x ^ q ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
  let S : Set α := {x | level < Real.log (f x)}
  let ν : Measure α := μ.restrict S
  letI : IsFiniteMeasure ν := by
    dsimp only [ν]
    infer_instance
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.log
  have hf_nonneg : 0 ≤ᵐ[μ] f := ae_of_all μ fun x => (hf_pos x).le
  have hfp := DifferentialGeometry.Integral.integrable_rpow_of_integrable_rpow
    hp hpq hf.aemeasurable hf_nonneg hfq
  have hratio_nonneg : 0 ≤ p / q := div_nonneg hp hq.le
  have htail_exp_nonneg : 0 ≤ 1 - p / q := sub_nonneg.mpr ((div_le_one hq).2 hpq)
  have hhigh := DifferentialGeometry.Integral.integral_rpow_le_integral_rpow_mul_measure
    (μ := ν) hp hq hpq
    (ae_of_all ν fun x => (hf_pos x).le)
    (hfq.mono_measure Measure.restrict_le_self)
  have hq_mono : (∫ x, f x ^ q ∂ν) ≤ ∫ x, f x ^ q ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all μ fun x => Real.rpow_nonneg (hf_pos x).le q) hfq
  have hmeasure : ν.real Set.univ ≤ tail := by
    simpa only [ν, measureReal_restrict_apply_univ, S] using htail
  have hhigh' : (∫ x in S, f x ^ p ∂μ) ≤
      (∫ x, f x ^ q ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
    have hq_int_nonneg : 0 ≤ ∫ x, f x ^ q ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (hf_pos x).le q
    have hnu_int_nonneg : 0 ≤ ∫ x, f x ^ q ∂ν :=
      integral_nonneg fun x => Real.rpow_nonneg (hf_pos x).le q
    calc
      (∫ x in S, f x ^ p ∂μ) ≤
          (∫ x, f x ^ q ∂ν) ^ (p / q) * ν.real Set.univ ^ (1 - p / q) := by
            simpa only [ν] using hhigh
      _ ≤ (∫ x, f x ^ q ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
        exact mul_le_mul
          (Real.rpow_le_rpow hnu_int_nonneg hq_mono hratio_nonneg)
          (Real.rpow_le_rpow ENNReal.toReal_nonneg hmeasure htail_exp_nonneg)
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (Real.rpow_nonneg hq_int_nonneg _)
  have hlow_point : ∀ᵐ x ∂μ.restrict Sᶜ,
      f x ^ p ≤ Real.exp (p * level) := by
    filter_upwards [ae_restrict_mem hS.compl] with x hx
    have hxlog : Real.log (f x) ≤ level := by
      exact le_of_not_gt (by simpa only [S, Set.mem_setOf_eq, Set.mem_compl_iff] using hx)
    rw [Real.rpow_def_of_pos (hf_pos x)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlow : (∫ x in Sᶜ, f x ^ p ∂μ) ≤
      Real.exp (p * level) * μ.real Set.univ := by
    calc
      (∫ x in Sᶜ, f x ^ p ∂μ) ≤ ∫ _x in Sᶜ, Real.exp (p * level) ∂μ := by
        exact integral_mono_ae
          (hfp.mono_measure Measure.restrict_le_self)
          (integrable_const _)
          hlow_point
      _ = μ.real Sᶜ * Real.exp (p * level) := by simp
      _ ≤ μ.real Set.univ * Real.exp (p * level) := by
        exact mul_le_mul_of_nonneg_right
          (measureReal_mono (μ := μ) (Set.subset_univ _) (measure_ne_top μ _))
          (Real.exp_pos _).le
      _ = Real.exp (p * level) * μ.real Set.univ := mul_comm _ _
  rw [← integral_add_compl hS hfp]
  exact add_le_add hhigh' hlow |>.trans_eq (add_comm _ _)

theorem integral_neg_rpow_le_of_log_sublevel
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    {p q level tail : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hfq : Integrable (fun x => f x ^ (-q)) μ)
    (htail : μ.real {x | level < -(Real.log (f x))} ≤ tail) :
    (∫ x, f x ^ (-p) ∂μ) ≤
      Real.exp (p * level) * μ.real Set.univ +
        (∫ x, f x ^ (-q) ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
  have hinv_q : Integrable (fun x => (f x)⁻¹ ^ q) μ := by
    simpa only [Real.inv_rpow (hf_pos _).le, ← Real.rpow_neg (hf_pos _).le] using hfq
  have h := integral_rpow_le_of_log_superlevel μ (fun x => (f x)⁻¹)
    hp hq hpq hf.inv (fun x => inv_pos.mpr (hf_pos x)) hinv_q
    (by simpa only [Real.log_inv] using htail)
  simpa only [Real.inv_rpow (hf_pos _).le, ← Real.rpow_neg (hf_pos _).le] using h

theorem integral_rpow_le_two_exp_half_of_log_superlevel_tail
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    {p₀ c₀ β : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hβ : 2 * c₀ < β)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hf₀ : Integrable (fun x => f x ^ p₀) μ)
    (hintegral_pos : 0 < ∫ x, f x ^ p₀ ∂μ)
    (hmass : μ.real Set.univ ≤ 1)
    (hβ_eq : β = Real.log ((∫ x, f x ^ p₀ ∂μ) ^ (1 / p₀)))
    (htail : μ.real {x | β / 2 < Real.log (f x)} ≤ 2 * c₀ / β) :
    let p := bombieriGiustiExponent p₀ c₀ β
    (∫ x, f x ^ p ∂μ) ≤ 2 * Real.exp (p * β / 2) := by
  let p := bombieriGiustiExponent p₀ c₀ β
  let J := ∫ x, f x ^ p₀ ∂μ
  have hp : 0 < p := bombieriGiustiExponent_pos hp₀ hc₀ hβ
  have hp_le : p ≤ p₀ := (bombieriGiustiExponent_lt hp₀ hc₀ hβ).le
  have hJpos : 0 < J := by simpa only [J] using hintegral_pos
  have hβ_eq' : β = Real.log (J ^ (1 / p₀)) := by simpa only [J] using hβ_eq
  have hbound := integral_rpow_le_of_log_superlevel μ f hp.le hp₀ hp_le
    hf hf_pos hf₀ htail
  have hJpower : J ^ (p / p₀) = Real.exp (p * β) := by
    calc
      J ^ (p / p₀) = J ^ ((1 / p₀) * p) := by
        congr 1
        ring
      _ = (J ^ (1 / p₀)) ^ p := Real.rpow_mul hJpos.le _ _
      _ = Real.exp (p * Real.log (J ^ (1 / p₀))) := by
        rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos hJpos _)]
        congr 1
        ring
      _ = Real.exp (p * β) := by rw [hβ_eq']
  have htailpower : (2 * c₀ / β) ^ (1 - p / p₀) =
      Real.exp (-p * β / 2) := by
    simpa only [p] using bombieriGiusti_tail_power hp₀ hc₀ hβ
  have hhigh : J ^ (p / p₀) * (2 * c₀ / β) ^ (1 - p / p₀) =
      Real.exp (p * β / 2) := by
    rw [hJpower, htailpower, ← Real.exp_add]
    congr 1
    ring
  have hlow : Real.exp (p * (β / 2)) * μ.real Set.univ ≤
      Real.exp (p * β / 2) := by
    calc
      Real.exp (p * (β / 2)) * μ.real Set.univ ≤
          Real.exp (p * (β / 2)) * 1 :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
      _ = Real.exp (p * β / 2) := by ring_nf
  change (∫ x, f x ^ p ∂μ) ≤ 2 * Real.exp (p * β / 2)
  calc
    (∫ x, f x ^ p ∂μ) ≤
        Real.exp (p * (β / 2)) * μ.real Set.univ +
          J ^ (p / p₀) * (2 * c₀ / β) ^ (1 - p / p₀) := by
      simpa only [J] using hbound
    _ ≤ Real.exp (p * β / 2) + Real.exp (p * β / 2) := by
      exact add_le_add hlow hhigh.le
    _ = 2 * Real.exp (p * β / 2) := by ring

theorem integral_rpow_root_le_of_log_superlevel_tail
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    {p₀ c₀ β : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hβ : 2 * c₀ < β)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hf₀ : Integrable (fun x => f x ^ p₀) μ)
    (hintegral_pos : 0 < ∫ x, f x ^ p₀ ∂μ)
    (hmass : μ.real Set.univ ≤ 1)
    (hβ_eq : β = Real.log ((∫ x, f x ^ p₀ ∂μ) ^ (1 / p₀)))
    (htail : μ.real {x | β / 2 < Real.log (f x)} ≤ 2 * c₀ / β) :
    let p := bombieriGiustiExponent p₀ c₀ β
    (∫ x, f x ^ p ∂μ) ^ (1 / p) ≤
      2 ^ (1 / p) * Real.exp (β / 2) := by
  let p := bombieriGiustiExponent p₀ c₀ β
  have hp : 0 < p := bombieriGiustiExponent_pos hp₀ hc₀ hβ
  have hbound := integral_rpow_le_two_exp_half_of_log_superlevel_tail
    μ f hp₀ hc₀ hβ hf hf_pos hf₀ hintegral_pos hmass hβ_eq htail
  have hintegral_nonneg : 0 ≤ ∫ x, f x ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (hf_pos x).le p
  have hroot := Real.rpow_le_rpow hintegral_nonneg hbound
    (div_nonneg zero_le_one hp.le)
  change (∫ x, f x ^ p ∂μ) ^ (1 / p) ≤
    2 ^ (1 / p) * Real.exp (β / 2)
  calc
    (∫ x, f x ^ p ∂μ) ^ (1 / p) ≤
        (2 * Real.exp (p * β / 2)) ^ (1 / p) := hroot
    _ = 2 ^ (1 / p) * Real.exp (p * β / 2) ^ (1 / p) := by
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le]
    _ = 2 ^ (1 / p) * Real.exp (β / 2) := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      field_simp [hp.ne']

theorem bombieriGiusti_log_contraction
    {p₀ c₀ βInner βOuter reverseCost : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hβOuter : 2 * c₀ < βOuter)
    (hreverseCost : 0 < reverseCost)
    (hreverse :
      let p := bombieriGiustiExponent p₀ c₀ βOuter
      Real.exp βInner ≤
        reverseCost ^ (1 / p - 1 / p₀) *
          (2 ^ (1 / p) * Real.exp (βOuter / 2)))
    (herror :
      let p := bombieriGiustiExponent p₀ c₀ βOuter
      (1 / p - 1 / p₀) * Real.log reverseCost +
          (1 / p) * Real.log 2 ≤ βOuter / 4) :
    βInner ≤ 3 * βOuter / 4 := by
  let p := bombieriGiustiExponent p₀ c₀ βOuter
  have hp : 0 < p := bombieriGiustiExponent_pos hp₀ hc₀ hβOuter
  have hreverse' : Real.exp βInner ≤
      reverseCost ^ (1 / p - 1 / p₀) *
        (2 ^ (1 / p) * Real.exp (βOuter / 2)) := by
    simpa only [p] using hreverse
  have herror' :
      (1 / p - 1 / p₀) * Real.log reverseCost +
          (1 / p) * Real.log 2 ≤ βOuter / 4 := by
    simpa only [p] using herror
  have hidentity :
      reverseCost ^ (1 / p - 1 / p₀) *
          (2 ^ (1 / p) * Real.exp (βOuter / 2)) =
        Real.exp
          ((1 / p - 1 / p₀) * Real.log reverseCost +
            (1 / p) * Real.log 2 + βOuter / 2) := by
    rw [Real.rpow_def_of_pos hreverseCost, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hidentity] at hreverse'
  have hlog := Real.exp_le_exp.mp hreverse'
  linarith

theorem bombieriGiusti_log_error
    (p₀ c₀ β reverseCost : ℝ) :
    let p := bombieriGiustiExponent p₀ c₀ β
    (1 / p - 1 / p₀) * Real.log reverseCost +
        (1 / p) * Real.log 2 =
      β / (2 * Real.log (β / (2 * c₀))) *
          (Real.log reverseCost + Real.log 2) +
        Real.log 2 / p₀ := by
  let p := bombieriGiustiExponent p₀ c₀ β
  have hgap : 1 / p - 1 / p₀ =
      β / (2 * Real.log (β / (2 * c₀))) := by
    simpa only [p] using bombieriGiustiExponent_inv_sub p₀ c₀ β
  have hinv : 1 / p =
      1 / p₀ + β / (2 * Real.log (β / (2 * c₀))) := by
    linarith
  change (1 / p - 1 / p₀) * Real.log reverseCost +
      (1 / p) * Real.log 2 =
    β / (2 * Real.log (β / (2 * c₀))) *
        (Real.log reverseCost + Real.log 2) + Real.log 2 / p₀
  rw [hgap, hinv]
  ring

def bombieriGiustiThreshold (p₀ c₀ reverseCost : ℝ) : ℝ :=
  max
    (2 * c₀ * Real.exp
      (4 * (Real.log reverseCost + Real.log 2)))
    (8 * Real.log 2 / p₀)

theorem bombieriGiustiThreshold_eq_max_pow
    {p₀ c₀ reverseCost : ℝ} (hreverseCost : 0 < reverseCost) :
    bombieriGiustiThreshold p₀ c₀ reverseCost =
      max (32 * c₀ * reverseCost ^ 4) (8 * Real.log 2 / p₀) := by
  have hreversePow :
      Real.exp (4 * Real.log reverseCost) = reverseCost ^ 4 := by
    rw [show 4 * Real.log reverseCost =
        Real.log reverseCost + Real.log reverseCost +
          Real.log reverseCost + Real.log reverseCost by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hreverseCost]
    ring
  have htwoPow : Real.exp (4 * Real.log 2) = (2 : ℝ) ^ 4 := by
    rw [show 4 * Real.log 2 =
        Real.log 2 + Real.log 2 + Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  unfold bombieriGiustiThreshold
  congr 1
  rw [show 4 * (Real.log reverseCost + Real.log 2) =
      4 * Real.log reverseCost + 4 * Real.log 2 by ring,
    Real.exp_add, hreversePow, htwoPow]
  ring

theorem summable_geometric_mul_bombieriGiustiThreshold_of_polynomial_le
    {p₀ c₀ C : ℝ} {reverseCost : ℕ → ℝ} (degree : ℕ)
    (hp₀ : 0 < p₀) (hc₀ : 0 ≤ c₀) (hC : 1 ≤ C)
    (hreverseCost : ∀ k, 1 ≤ reverseCost k)
    (hbound : ∀ k, reverseCost k ≤ C * (k + 1 : ℝ) ^ degree) :
    Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k *
      (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4)) := by
  let r : ℝ := 3 / 4
  let constant : ℝ := 8 * Real.log 2 / p₀
  let coefficient : ℝ := 32 * c₀ * C ^ 4
  have hr_nonneg : 0 ≤ r := by norm_num [r]
  have hr_norm : ‖r‖ < 1 := by norm_num [r, Real.norm_eq_abs]
  have hC_nonneg : 0 ≤ C := zero_le_one.trans hC
  have hconstant : 0 ≤ constant := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hp₀.le
  have hcoefficient : 0 ≤ coefficient := by
    exact mul_nonneg (mul_nonneg (by norm_num) hc₀) (pow_nonneg hC_nonneg 4)
  have hpoly : Summable (fun k : ℕ =>
      r ^ k * (k + 1 : ℝ) ^ (4 * degree)) :=
    summable_geometric_mul_nat_add_pow (by norm_num [r]) hr_norm (4 * degree)
  have hgeom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_norm_lt_one hr_norm
  have hmajor : Summable (fun k : ℕ => r ^ k *
      ((coefficient * (k + 1 : ℝ) ^ (4 * degree) + constant) / 4)) := by
    refine ((hpoly.mul_right (coefficient / 4)).add
      (hgeom.mul_right (constant / 4))).congr ?_
    intro k
    ring
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg hr_nonneg k)
      (div_nonneg
        ((mul_nonneg (mul_nonneg (by norm_num) hc₀)
          (Real.exp_pos _).le).trans (le_max_left _ _)) (by norm_num)))
  · intro k
    have hcost_nonneg : 0 ≤ reverseCost k :=
      zero_le_one.trans (hreverseCost k)
    have hcost_pow : reverseCost k ^ 4 ≤
        (C * (k + 1 : ℝ) ^ degree) ^ 4 :=
      pow_le_pow_left₀ hcost_nonneg (hbound k) 4
    have hpower : (C * (k + 1 : ℝ) ^ degree) ^ 4 =
        C ^ 4 * (k + 1 : ℝ) ^ (4 * degree) := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, Nat.mul_comm degree 4]
    have hfirst : 32 * c₀ * reverseCost k ^ 4 ≤
        coefficient * (k + 1 : ℝ) ^ (4 * degree) := by
      dsimp only [coefficient]
      calc
        32 * c₀ * reverseCost k ^ 4 ≤
            32 * c₀ * (C * (k + 1 : ℝ) ^ degree) ^ 4 :=
          mul_le_mul_of_nonneg_left hcost_pow
            (mul_nonneg (by norm_num) hc₀)
        _ = 32 * c₀ *
            (C ^ 4 * (k + 1 : ℝ) ^ (4 * degree)) := by rw [hpower]
        _ = 32 * c₀ * C ^ 4 * (k + 1 : ℝ) ^ (4 * degree) := by ring
    have hthreshold : bombieriGiustiThreshold p₀ c₀ (reverseCost k) ≤
        coefficient * (k + 1 : ℝ) ^ (4 * degree) + constant := by
      rw [bombieriGiustiThreshold_eq_max_pow
        (zero_lt_one.trans_le (hreverseCost k))]
      apply max_le
      · exact hfirst.trans (le_add_of_nonneg_right hconstant)
      · exact le_add_of_nonneg_left
          (mul_nonneg hcoefficient (pow_nonneg (by positivity) _))
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hthreshold (by norm_num))
      (pow_nonneg hr_nonneg k)
  · simpa only [r, constant, coefficient] using hmajor

theorem two_mul_le_bombieriGiustiThreshold
    {p₀ c₀ reverseCost : ℝ}
    (hc₀ : 0 ≤ c₀) (hreverseCost : 1 ≤ reverseCost) :
    2 * c₀ ≤ bombieriGiustiThreshold p₀ c₀ reverseCost := by
  have hlog : 0 ≤ Real.log reverseCost + Real.log 2 :=
    add_nonneg (Real.log_nonneg hreverseCost) (Real.log_nonneg (by norm_num))
  calc
    2 * c₀ = 2 * c₀ * 1 := by ring
    _ ≤ 2 * c₀ * Real.exp
        (4 * (Real.log reverseCost + Real.log 2)) := by
      exact mul_le_mul_of_nonneg_left
        ((Real.one_le_exp_iff).2 (mul_nonneg (by norm_num) hlog))
        (mul_nonneg (by norm_num) hc₀)
    _ ≤ bombieriGiustiThreshold p₀ c₀ reverseCost := le_max_left _ _

theorem bombieriGiusti_log_error_le_of_threshold_lt
    {p₀ c₀ β reverseCost : ℝ}
    (hc₀ : 0 < c₀) (hreverseCost : 1 ≤ reverseCost)
    (hβ : bombieriGiustiThreshold p₀ c₀ reverseCost < β) :
    let p := bombieriGiustiExponent p₀ c₀ β
    (1 / p - 1 / p₀) * Real.log reverseCost +
        (1 / p) * Real.log 2 ≤ β / 4 := by
  let L := Real.log reverseCost + Real.log 2
  have hlogReverse : 0 ≤ Real.log reverseCost := Real.log_nonneg hreverseCost
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by
    dsimp only [L]
    linarith
  have hfirst :
      2 * c₀ * Real.exp (4 * L) < β :=
    (le_max_left
      (2 * c₀ * Real.exp (4 * L)) (8 * Real.log 2 / p₀)).trans_lt hβ
  have hβ_pos : 0 < β :=
    (mul_pos (mul_pos (by norm_num) hc₀) (Real.exp_pos _)).trans hfirst
  have hratio : Real.exp (4 * L) < β / (2 * c₀) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hc₀)).2
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hfirst
  have hlogRatio : 4 * L < Real.log (β / (2 * c₀)) := by
    have h := Real.log_lt_log (Real.exp_pos _) hratio
    simpa only [Real.log_exp] using h
  have hlogRatio_pos : 0 < Real.log (β / (2 * c₀)) :=
    (mul_pos (by norm_num) hL).trans hlogRatio
  have hfraction :
      L / (2 * Real.log (β / (2 * c₀))) ≤ 1 / 8 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlogRatio_pos)).2
    nlinarith
  have hmain :
      β / (2 * Real.log (β / (2 * c₀))) * L ≤ β / 8 := by
    calc
      β / (2 * Real.log (β / (2 * c₀))) * L =
          β * (L / (2 * Real.log (β / (2 * c₀)))) := by ring
      _ ≤ β * (1 / 8) := mul_le_mul_of_nonneg_left hfraction hβ_pos.le
      _ = β / 8 := by ring
  have hsecond : 8 * Real.log 2 / p₀ < β :=
    (le_max_right
      (2 * c₀ * Real.exp (4 * L)) (8 * Real.log 2 / p₀)).trans_lt hβ
  have hsecond' : 8 * (Real.log 2 / p₀) < β := by
    calc
      8 * (Real.log 2 / p₀) = 8 * Real.log 2 / p₀ := by ring
      _ < β := hsecond
  have htail : Real.log 2 / p₀ ≤ β / 8 := by
    linarith
  dsimp only
  rw [bombieriGiusti_log_error]
  dsimp only [L] at hmain
  linarith

theorem bombieriGiusti_hole_filling_step
    {p₀ c₀ βInner βOuter threshold reverseCost : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hthreshold : 2 * c₀ ≤ threshold)
    (hmono : βInner ≤ βOuter)
    (hreverseCost : 0 < reverseCost)
    (hreverse : threshold < βOuter →
      let p := bombieriGiustiExponent p₀ c₀ βOuter
      Real.exp βInner ≤
        reverseCost ^ (1 / p - 1 / p₀) *
          (2 ^ (1 / p) * Real.exp (βOuter / 2)))
    (herror : threshold < βOuter →
      let p := bombieriGiustiExponent p₀ c₀ βOuter
      (1 / p - 1 / p₀) * Real.log reverseCost +
          (1 / p) * Real.log 2 ≤ βOuter / 4) :
    βInner ≤ 3 / 4 * βOuter + threshold / 4 := by
  by_cases hhigh : threshold < βOuter
  · have hβOuter : 2 * c₀ < βOuter := hthreshold.trans_lt hhigh
    have hcontract := bombieriGiusti_log_contraction hp₀ hc₀ hβOuter
      hreverseCost (hreverse hhigh) (herror hhigh)
    have hthreshold_nonneg : 0 ≤ threshold :=
      (mul_pos (by norm_num) hc₀).le.trans hthreshold
    calc
      βInner ≤ 3 * βOuter / 4 := hcontract
      _ = 3 / 4 * βOuter := by ring
      _ ≤ 3 / 4 * βOuter + threshold / 4 :=
        le_add_of_nonneg_right (div_nonneg hthreshold_nonneg (by norm_num))
  · have hβOuter : βOuter ≤ threshold := le_of_not_gt hhigh
    calc
      βInner ≤ βOuter := hmono
      _ ≤ 3 / 4 * βOuter + threshold / 4 := by linarith

theorem bombieriGiusti_summable_hole_filling
    {p₀ c₀ : ℝ} {β threshold reverseCost : ℕ → ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hβ_bdd : BddAbove (Set.range β))
    (hthreshold : ∀ k, 2 * c₀ ≤ threshold k)
    (hmono : ∀ k, β k ≤ β (k + 1))
    (hreverseCost : ∀ k, 0 < reverseCost k)
    (hreverse : ∀ k, threshold k < β (k + 1) →
      let p := bombieriGiustiExponent p₀ c₀ (β (k + 1))
      Real.exp (β k) ≤
        reverseCost k ^ (1 / p - 1 / p₀) *
          (2 ^ (1 / p) * Real.exp (β (k + 1) / 2)))
    (herror : ∀ k, threshold k < β (k + 1) →
      let p := bombieriGiustiExponent p₀ c₀ (β (k + 1))
      (1 / p - 1 / p₀) * Real.log (reverseCost k) +
          (1 / p) * Real.log 2 ≤ β (k + 1) / 4)
    (hsummable : Summable
      (fun k : ℕ => (3 / 4 : ℝ) ^ k * (threshold k / 4))) :
    β 0 ≤ ∑' k : ℕ, (3 / 4 : ℝ) ^ k * (threshold k / 4) := by
  apply summable_hole_filling hβ_bdd (by norm_num) (by norm_num)
    (fun k => div_nonneg
      ((mul_pos (by norm_num) hc₀).le.trans (hthreshold k)) (by norm_num))
    hsummable
  intro k
  exact bombieriGiusti_hole_filling_step hp₀ hc₀ (hthreshold k) (hmono k)
    (hreverseCost k) (hreverse k) (herror k)

theorem bombieriGiusti_summable_threshold_hole_filling
    {p₀ c₀ : ℝ} {β reverseCost : ℕ → ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hreverseCost : ∀ k, 1 ≤ reverseCost k)
    (hβ_bdd : BddAbove (Set.range β))
    (hmono : ∀ k, β k ≤ β (k + 1))
    (hreverse : ∀ k,
      bombieriGiustiThreshold p₀ c₀ (reverseCost k) < β (k + 1) →
        let p := bombieriGiustiExponent p₀ c₀ (β (k + 1))
        Real.exp (β k) ≤
          reverseCost k ^ (1 / p - 1 / p₀) *
            (2 ^ (1 / p) * Real.exp (β (k + 1) / 2)))
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4))) :
    β 0 ≤ ∑' k : ℕ, (3 / 4 : ℝ) ^ k *
      (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4) := by
  exact bombieriGiusti_summable_hole_filling hp₀ hc₀ hβ_bdd
    (fun k => two_mul_le_bombieriGiustiThreshold hc₀.le (hreverseCost k))
    hmono (fun k => zero_lt_one.trans_le (hreverseCost k)) hreverse
    (fun k hk => bombieriGiusti_log_error_le_of_threshold_lt
      hc₀ (hreverseCost k) hk)
    hsummable

theorem bombieriGiusti_hole_filling
    {p₀ c₀ reverseCost : ℝ} {β : ℕ → ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hreverseCost : 1 ≤ reverseCost)
    (hβ_bdd : BddAbove (Set.range β))
    (hmono : ∀ k, β k ≤ β (k + 1))
    (hreverse : ∀ k,
      bombieriGiustiThreshold p₀ c₀ reverseCost < β (k + 1) →
        let p := bombieriGiustiExponent p₀ c₀ (β (k + 1))
        Real.exp (β k) ≤
          reverseCost ^ (1 / p - 1 / p₀) *
            (2 ^ (1 / p) * Real.exp (β (k + 1) / 2))) :
    β 0 ≤ bombieriGiustiThreshold p₀ c₀ reverseCost := by
  let threshold := bombieriGiustiThreshold p₀ c₀ reverseCost
  have hgeometric : Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsummable : Summable
      (fun k : ℕ => (3 / 4 : ℝ) ^ k * (threshold / 4)) :=
    Summable.mul_right (threshold / 4) hgeometric
  have hbound := bombieriGiusti_summable_hole_filling hp₀ hc₀ hβ_bdd
    (threshold := fun _ => threshold) (reverseCost := fun _ => reverseCost)
    (fun _ => two_mul_le_bombieriGiustiThreshold hc₀.le hreverseCost)
    hmono (fun _ => zero_lt_one.trans_le hreverseCost)
    (fun k hk => hreverse k hk)
    (fun _ hk => bombieriGiusti_log_error_le_of_threshold_lt hc₀ hreverseCost hk)
    hsummable
  calc
    β 0 ≤ ∑' k : ℕ, (3 / 4 : ℝ) ^ k * (threshold / 4) := hbound
    _ = (∑' k : ℕ, (3 / 4 : ℝ) ^ k) * (threshold / 4) :=
      hgeometric.tsum_mul_right (threshold / 4)
    _ = threshold := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    _ = bombieriGiustiThreshold p₀ c₀ reverseCost := rfl

theorem integral_rpow_root_le_exp_tsum_bombieriGiustiThreshold
    (mu : ℕ → Measure α) [∀ k, IsFiniteMeasure (mu k)]
    (f : α → ℝ) (reverseCost : ℕ → ℝ) {p₀ c₀ : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hreverseCost : ∀ k, 1 ≤ reverseCost k)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hintegrable : ∀ k, Integrable (fun x => f x ^ p₀) (mu k))
    (hmoment_pos : ∀ k, 0 < ∫ x, f x ^ p₀ ∂(mu k))
    (hmass : ∀ k, (mu k).real Set.univ ≤ 1)
    (hmoment_mono : ∀ k,
      (∫ x, f x ^ p₀ ∂(mu k)) ≤ ∫ x, f x ^ p₀ ∂(mu (k + 1)))
    (hβ_bdd : BddAbove (Set.range (fun k =>
      Real.log ((∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀)))))
    (htail : ∀ k r, 0 < r →
      (mu k).real {x | r < Real.log (f x)} ≤ c₀ / r)
    (hreverse : ∀ k {p : ℝ}, 0 < p → p < p₀ →
      (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) ≤
        reverseCost k ^ (1 / p - 1 / p₀) *
          (∫ x, f x ^ p ∂(mu (k + 1))) ^ (1 / p))
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4))) :
    (∫ x, f x ^ p₀ ∂(mu 0)) ^ (1 / p₀) ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4)) := by
  let beta : ℕ → ℝ := fun k =>
    Real.log ((∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀))
  have hnorm_pos : ∀ k,
      0 < (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) := fun k =>
    Real.rpow_pos_of_pos (hmoment_pos k) _
  have hbeta_mono : ∀ k, beta k ≤ beta (k + 1) := by
    intro k
    have hmoment_le : (∫ x, f x ^ p₀ ∂(mu k)) ≤
        ∫ x, f x ^ p₀ ∂(mu (k + 1)) := hmoment_mono k
    have hnorm_le :
        (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) ≤
          (∫ x, f x ^ p₀ ∂(mu (k + 1))) ^ (1 / p₀) :=
      Real.rpow_le_rpow (hmoment_pos k).le hmoment_le
        (div_pos one_pos hp₀).le
    exact Real.log_le_log (hnorm_pos k) hnorm_le
  have hbound := bombieriGiusti_summable_threshold_hole_filling
    hp₀ hc₀ hreverseCost
    (β := beta) (by simpa only [beta] using hβ_bdd) hbeta_mono
    (fun k hk => by
      let p := bombieriGiustiExponent p₀ c₀ (beta (k + 1))
      have hthreshold := two_mul_le_bombieriGiustiThreshold
        (p₀ := p₀) (reverseCost := reverseCost k) hc₀.le (hreverseCost k)
      have hbeta_outer : 2 * c₀ < beta (k + 1) := hthreshold.trans_lt hk
      have hp : 0 < p := bombieriGiustiExponent_pos hp₀ hc₀ hbeta_outer
      have hpp₀ : p < p₀ := bombieriGiustiExponent_lt hp₀ hc₀ hbeta_outer
      have htail_half :
          (mu (k + 1)).real {x | beta (k + 1) / 2 < Real.log (f x)} ≤
            2 * c₀ / beta (k + 1) := by
        calc
          (mu (k + 1)).real
              {x | beta (k + 1) / 2 < Real.log (f x)} ≤
              c₀ / (beta (k + 1) / 2) :=
            htail (k + 1) (beta (k + 1) / 2)
              (div_pos ((mul_pos (by norm_num) hc₀).trans hbeta_outer)
                (by norm_num))
          _ = 2 * c₀ / beta (k + 1) := by
            field_simp [((mul_pos (by norm_num) hc₀).trans hbeta_outer).ne']
      have htail_norm := integral_rpow_root_le_of_log_superlevel_tail
        (mu (k + 1)) f hp₀ hc₀ hbeta_outer hf hf_pos
          (hintegrable (k + 1)) (hmoment_pos (k + 1)) (hmass (k + 1))
          rfl htail_half
      have hreverse_norm := hreverse k hp hpp₀
      change Real.exp (beta k) ≤
        reverseCost k ^ (1 / p - 1 / p₀) *
          (2 ^ (1 / p) * Real.exp (beta (k + 1) / 2))
      calc
        Real.exp (beta k) =
            (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) := by
          exact Real.exp_log (hnorm_pos k)
        _ ≤ reverseCost k ^ (1 / p - 1 / p₀) *
            (∫ x, f x ^ p ∂(mu (k + 1))) ^ (1 / p) := hreverse_norm
        _ ≤ reverseCost k ^ (1 / p - 1 / p₀) *
            (2 ^ (1 / p) * Real.exp (beta (k + 1) / 2)) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa only [p] using htail_norm)
            (Real.rpow_nonneg (zero_le_one.trans (hreverseCost k)) _))
    hsummable
  calc
    (∫ x, f x ^ p₀ ∂(mu 0)) ^ (1 / p₀) = Real.exp (beta 0) := by
      exact (Real.exp_log (hnorm_pos 0)).symm
    _ ≤ Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4)) :=
      Real.exp_le_exp.mpr hbound

theorem integral_rpow_root_le_exp_bombieriGiustiThreshold
    (mu : ℕ → Measure α) [∀ k, IsFiniteMeasure (mu k)]
    (f : α → ℝ) {p₀ c₀ reverseCost : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hreverseCost : 1 ≤ reverseCost)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hintegrable : ∀ k, Integrable (fun x => f x ^ p₀) (mu k))
    (hmoment_pos : ∀ k, 0 < ∫ x, f x ^ p₀ ∂(mu k))
    (hmass : ∀ k, (mu k).real Set.univ ≤ 1)
    (hmoment_mono : ∀ k,
      (∫ x, f x ^ p₀ ∂(mu k)) ≤ ∫ x, f x ^ p₀ ∂(mu (k + 1)))
    (hβ_bdd : BddAbove (Set.range (fun k =>
      Real.log ((∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀)))))
    (htail : ∀ k r, 0 < r →
      (mu k).real {x | r < Real.log (f x)} ≤ c₀ / r)
    (hreverse : ∀ k {p : ℝ}, 0 < p → p < p₀ →
      (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) ≤
        reverseCost ^ (1 / p - 1 / p₀) *
          (∫ x, f x ^ p ∂(mu (k + 1))) ^ (1 / p)) :
    (∫ x, f x ^ p₀ ∂(mu 0)) ^ (1 / p₀) ≤
      Real.exp (bombieriGiustiThreshold p₀ c₀ reverseCost) := by
  let threshold := bombieriGiustiThreshold p₀ c₀ reverseCost
  have hgeometric : Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsummable : Summable
      (fun k : ℕ => (3 / 4 : ℝ) ^ k * (threshold / 4)) :=
    Summable.mul_right (threshold / 4) hgeometric
  have hbound := integral_rpow_root_le_exp_tsum_bombieriGiustiThreshold
    mu f (fun _ => reverseCost) hp₀ hc₀ (fun _ => hreverseCost)
      hf hf_pos hintegrable hmoment_pos hmass hmoment_mono hβ_bdd htail
      (fun k {p} hp hpp₀ => hreverse k (p := p) hp hpp₀) hsummable
  have hsum : (∑' k : ℕ, (3 / 4 : ℝ) ^ k * (threshold / 4)) = threshold := by
    rw [hgeometric.tsum_mul_right (threshold / 4),
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  calc
    (∫ x, f x ^ p₀ ∂(mu 0)) ^ (1 / p₀) ≤
        Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k * (threshold / 4)) := by
      simpa only [threshold] using hbound
    _ = Real.exp (bombieriGiustiThreshold p₀ c₀ reverseCost) := by
      rw [hsum]

theorem integral_rpow_root_le_exp_tsum_bombieriGiustiThreshold_of_dominated
    (mu : ℕ → Measure α) [∀ k, IsFiniteMeasure (mu k)]
    (nu : Measure α) [IsFiniteMeasure nu]
    (f : α → ℝ) (reverseCost : ℕ → ℝ) {p₀ c₀ : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hreverseCost : ∀ k, 1 ≤ reverseCost k)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hnu_integrable : Integrable (fun x => f x ^ p₀) nu)
    (hmoment_pos : ∀ k, 0 < ∫ x, f x ^ p₀ ∂(mu k))
    (hmass : ∀ k, (mu k).real Set.univ ≤ 1)
    (hmu : ∀ k, mu k ≤ mu (k + 1))
    (hdominated : ∀ k, mu k ≤ nu)
    (htail : ∀ k r, 0 < r →
      (mu k).real {x | r < Real.log (f x)} ≤ c₀ / r)
    (hreverse : ∀ k {p : ℝ}, 0 < p → p < p₀ →
      (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) ≤
        reverseCost k ^ (1 / p - 1 / p₀) *
          (∫ x, f x ^ p ∂(mu (k + 1))) ^ (1 / p))
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4))) :
    (∫ x, f x ^ p₀ ∂(mu 0)) ^ (1 / p₀) ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4)) := by
  have hintegrable : ∀ k, Integrable (fun x => f x ^ p₀) (mu k) := fun k =>
    hnu_integrable.mono_measure (hdominated k)
  have hβ_bdd : BddAbove (Set.range (fun k =>
      Real.log ((∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀)))) := by
    refine ⟨Real.log ((∫ x, f x ^ p₀ ∂nu) ^ (1 / p₀)), ?_⟩
    rintro _ ⟨k, rfl⟩
    have hmoment_le : (∫ x, f x ^ p₀ ∂(mu k)) ≤ ∫ x, f x ^ p₀ ∂nu := by
      exact integral_mono_measure (hdominated k)
        (ae_of_all nu fun x => Real.rpow_nonneg (hf_pos x).le p₀)
        hnu_integrable
    have hnorm_le :
        (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) ≤
          (∫ x, f x ^ p₀ ∂nu) ^ (1 / p₀) :=
      Real.rpow_le_rpow (hmoment_pos k).le hmoment_le
        (div_pos one_pos hp₀).le
    exact Real.log_le_log (Real.rpow_pos_of_pos (hmoment_pos k) _) hnorm_le
  exact integral_rpow_root_le_exp_tsum_bombieriGiustiThreshold
    mu f reverseCost hp₀ hc₀ hreverseCost hf hf_pos hintegrable
      hmoment_pos hmass
      (fun k => integral_mono_measure (hmu k)
        (ae_of_all (mu (k + 1)) fun x => Real.rpow_nonneg (hf_pos x).le p₀)
        (hintegrable (k + 1)))
      hβ_bdd htail hreverse hsummable

theorem integral_rpow_root_le_exp_bombieriGiustiThreshold_of_dominated
    (mu : ℕ → Measure α) [∀ k, IsFiniteMeasure (mu k)]
    (nu : Measure α) [IsFiniteMeasure nu]
    (f : α → ℝ) {p₀ c₀ reverseCost : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀) (hreverseCost : 1 ≤ reverseCost)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hnu_integrable : Integrable (fun x => f x ^ p₀) nu)
    (hmoment_pos : ∀ k, 0 < ∫ x, f x ^ p₀ ∂(mu k))
    (hmass : ∀ k, (mu k).real Set.univ ≤ 1)
    (hmu : ∀ k, mu k ≤ mu (k + 1))
    (hdominated : ∀ k, mu k ≤ nu)
    (htail : ∀ k r, 0 < r →
      (mu k).real {x | r < Real.log (f x)} ≤ c₀ / r)
    (hreverse : ∀ k {p : ℝ}, 0 < p → p < p₀ →
      (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) ≤
        reverseCost ^ (1 / p - 1 / p₀) *
          (∫ x, f x ^ p ∂(mu (k + 1))) ^ (1 / p)) :
    (∫ x, f x ^ p₀ ∂(mu 0)) ^ (1 / p₀) ≤
      Real.exp (bombieriGiustiThreshold p₀ c₀ reverseCost) := by
  have hintegrable : ∀ k, Integrable (fun x => f x ^ p₀) (mu k) := fun k =>
    hnu_integrable.mono_measure (hdominated k)
  have hβ_bdd : BddAbove (Set.range (fun k =>
      Real.log ((∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀)))) := by
    refine ⟨Real.log ((∫ x, f x ^ p₀ ∂nu) ^ (1 / p₀)), ?_⟩
    rintro _ ⟨k, rfl⟩
    have hmoment_le : (∫ x, f x ^ p₀ ∂(mu k)) ≤ ∫ x, f x ^ p₀ ∂nu := by
      exact integral_mono_measure (hdominated k)
        (ae_of_all nu fun x => Real.rpow_nonneg (hf_pos x).le p₀)
        hnu_integrable
    have hnorm_le :
        (∫ x, f x ^ p₀ ∂(mu k)) ^ (1 / p₀) ≤
          (∫ x, f x ^ p₀ ∂nu) ^ (1 / p₀) :=
      Real.rpow_le_rpow (hmoment_pos k).le hmoment_le
        (div_pos one_pos hp₀).le
    exact Real.log_le_log (Real.rpow_pos_of_pos (hmoment_pos k) _) hnorm_le
  exact integral_rpow_root_le_exp_bombieriGiustiThreshold mu f hp₀ hc₀
    hreverseCost hf hf_pos hintegrable hmoment_pos hmass
      (fun k => integral_mono_measure (hmu k)
        (ae_of_all (mu (k + 1)) fun x => Real.rpow_nonneg (hf_pos x).le p₀)
        (hintegrable (k + 1)))
      hβ_bdd htail hreverse

open Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold
    {g : SmoothRiemannianMetric I M}
    (cutoff : ℕ → SmoothScalar g) (outer : SmoothScalar g)
    (f : ℝ × M → ℝ) (reverseCost : ℕ → ℝ)
    (a b : ℕ → ℝ) {p₀ c₀ c d : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hreverseCost : ∀ k, 1 ≤ reverseCost k)
    (hf : Continuous f) (hf_pos : ∀ z, 0 < f z)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M) (cutoff k) (a k) (b k) ≠ 0)
    (hmass : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (cutoff k) (a k) (b k)).real Set.univ ≤ 1)
    (hstart : ∀ k, a (k + 1) ≤ a k)
    (hend : ∀ k, b k ≤ b (k + 1))
    (hcutoff : ∀ k x,
      (cutoff k).toFun x ^ 2 ≤ (cutoff (k + 1)).toFun x ^ 2)
    (hc : ∀ k, c ≤ a k) (hd : ∀ k, b k ≤ d)
    (houter : ∀ k x, (cutoff k).toFun x ^ 2 ≤ outer.toFun x ^ 2)
    (htail : ∀ k r, 0 < r →
      (localizedSpacetimeMeasure (I := I) (M := M)
        (cutoff k) (a k) (b k)).real {z | r < Real.log (f z)} ≤ c₀ / r)
    (hreverse : ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (cutoff k) (fun t x => f (t, x)) p₀ (a k) (b k) ≤
        reverseCost k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (cutoff (k + 1)) (fun t x => f (t, x)) p
              (a (k + 1)) (b (k + 1)))
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4))) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (cutoff 0) (fun t x => f (t, x)) p₀ (a 0) (b 0) ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀ (reverseCost k) / 4)) := by
  let mu : ℕ → Measure (ℝ × M) := fun k =>
    localizedSpacetimeMeasure (I := I) (M := M) (cutoff k) (a k) (b k)
  let nu : Measure (ℝ × M) :=
    localizedSpacetimeMeasure (I := I) (M := M) outer c d
  have hnu_integrable : Integrable (fun z => f z ^ p₀) nu := by
    exact integrable_localizedSpacetimeRpow_of_continuous_pos
      (I := I) (M := M) outer (fun t x => f (t, x)) hf
        (fun t x => hf_pos (t, x)) p₀ c d
  have hmoment_pos : ∀ k, 0 < ∫ z, f z ^ p₀ ∂(mu k) := by
    intro k
    simpa only [mu] using localizedSpacetimeRpowMoment_pos
      (I := I) (M := M) (cutoff k) (fun t x => f (t, x)) hf
        (fun t x => hf_pos (t, x)) p₀ (a k) (b k) (hmeasure k)
  have hmu : ∀ k, mu k ≤ mu (k + 1) := by
    intro k
    exact localizedSpacetimeMeasure_mono (I := I) (M := M)
      (hstart k) (hend k) (hcutoff k)
  have hdominated : ∀ k, mu k ≤ nu := by
    intro k
    exact localizedSpacetimeMeasure_mono (I := I) (M := M)
      (hc k) (hd k) (houter k)
  have hbound :=
    integral_rpow_root_le_exp_tsum_bombieriGiustiThreshold_of_dominated
      mu nu f reverseCost hp₀ hc₀ hreverseCost hf.measurable hf_pos
        hnu_integrable hmoment_pos (by simpa only [mu] using hmass)
        hmu hdominated (by simpa only [mu] using htail)
        (by simpa only [localizedSpacetimeRpowNorm, mu] using hreverse)
        hsummable
  simpa only [localizedSpacetimeRpowNorm, localizedSpacetimeRpowMoment, mu] using
    hbound

theorem early_localizedSpacetimeMeasure_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ r : ℝ} (haτ : a ≤ τ) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ).real
        {z | r < Real.log
          (exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff
              u hu hpos τ) u z.1 z.2)} ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let rescaled := exponentialTimeRescale rate center u
  have hrescaled := contMDiff_exponentialTimeRescale rate center u hu
  have hrescaled_pos := exponentialTimeRescale_pos rate center u hpos
  let hlog := contMDiff_log_of_pos hrescaled hrescaled_pos
  rw [localizedSpacetimeMeasure_real_superlevel
    (I := I) (M := M) deviationCutoff haτ
      (fun z => Real.log (rescaled z.1 z.2)) hlog.continuous]
  simpa only [localizedSuperlevelMass, smoothScalarSlice_toFun, rescaled,
    rate, center, hlog] using
    integrated_early_centered_log_superlevel_tail_of_supersolution
      (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
        u hu hpos haτ hr hmass hpde

theorem late_localizedSpacetimeMeasure_neg_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b r : ℝ} (hτb : τ ≤ b) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b).real
        {z | r < -Real.log
          (exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff
              u hu hpos τ) u z.1 z.2)} ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let rescaled := exponentialTimeRescale rate center u
  have hrescaled := contMDiff_exponentialTimeRescale rate center u hu
  have hrescaled_pos := exponentialTimeRescale_pos rate center u hpos
  let hlog := contMDiff_log_of_pos hrescaled hrescaled_pos
  change (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b).real
      {z | r < -Real.log (rescaled z.1 z.2)} ≤
    2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r
  have hset : {z : ℝ × M | r < -Real.log (rescaled z.1 z.2)} =
      {z : ℝ × M | Real.log (rescaled z.1 z.2) < -r} := by
    apply Set.ext
    intro z
    simp only [mem_setOf_eq]
    constructor <;> intro hz <;> linarith
  rw [hset]
  rw [localizedSpacetimeMeasure_real_sublevel
    (I := I) (M := M) deviationCutoff hτb
      (fun z => Real.log (rescaled z.1 z.2)) hlog.continuous]
  simpa only [localizedSublevelMass, smoothScalarSlice_toFun, rescaled,
    rate, center, hlog] using
    integrated_late_centered_log_sublevel_tail_of_supersolution
      (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
        u hu hpos hτb hr hmass hpde

theorem early_localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : ℕ → SmoothScalar g) (outer averagingCutoff : SmoothScalar g)
    (reverseCost : ℕ → ℝ) (a b : ℕ → ℝ)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A τ : ℝ} (hp₀ : 0 < p₀)
    (hreverseCost : ∀ k, 1 ≤ reverseCost k)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M) (cutoff k) (a k) (b k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (cutoff k) (a k) (b k)).real Set.univ ≤ 1)
    (hstart : ∀ k, a (k + 1) ≤ a k)
    (hend : ∀ k, b k ≤ b (k + 1))
    (hcutoff : ∀ k x,
      (cutoff k).toFun x ^ 2 ≤ (cutoff (k + 1)).toFun x ^ 2)
    (hAτ : A ≤ τ) (hA : ∀ k, A ≤ a k) (hbτ : ∀ k, b k ≤ τ)
    (houter : ∀ k x, (cutoff k).toFun x ^ 2 ≤ outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t)
    (hreverse : ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M) (cutoff k)
          (exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff
              u hu hpos τ) u) p₀ (a k) (b k) ≤
        reverseCost k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M) (cutoff (k + 1))
            (exponentialTimeRescale
              (logCenterDrift (I := I) (M := M) g averagingCutoff)
              (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                u hu hpos τ) u) p (a (k + 1)) (b (k + 1)))
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (reverseCost k) / 4))) :
    localizedSpacetimeRpowNorm (I := I) (M := M) (cutoff 0)
        (exponentialTimeRescale
          (logCenterDrift (I := I) (M := M) g averagingCutoff)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff
            u hu hpos τ) u) p₀ (a 0) (b 0) ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (reverseCost k) / 4)) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
    u hu hpos τ
  let v := exponentialTimeRescale rate center u
  let c₀ := 2 * C * cutoffMass (I := I) (M := M) averagingCutoff
  have hc₀ : 0 < c₀ := mul_pos (mul_pos (by norm_num) hC) hmass
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  apply localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold
    (I := I) (M := M) cutoff outer (fun z => v z.1 z.2) reverseCost a b
      (p₀ := p₀) (c₀ := c₀) (c := A) (d := τ) hp₀ hc₀ hreverseCost
      hv.continuous (fun z => hvpos z.1 z.2) hmeasure hmeasure_le_one
      hstart hend hcutoff hA hbτ houter
  · intro k r hr
    let S : Set (ℝ × M) := {z | r < Real.log (v z.1 z.2)}
    have hdom := localizedSpacetimeMeasure_mono (I := I) (M := M)
      (hA k) (hbτ k) (houter k)
    have hreal :
        (localizedSpacetimeMeasure (I := I) (M := M)
          (cutoff k) (a k) (b k)).real S ≤
        (localizedSpacetimeMeasure (I := I) (M := M) outer A τ).real S :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hdom S)
    exact hreal.trans (by
      simpa only [S, v, rate, center, c₀] using
        (early_localizedSpacetimeMeasure_log_superlevel_tail_of_supersolution
          (I := I) (M := M) g outer averagingCutoff C hC.le hP
            u hu hpos hAτ hr hmass hpde))
  · intro k p hp hpp₀
    simpa only [v, rate, center] using hreverse k hp hpp₀
  · simpa only [c₀] using hsummable

theorem late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_bombieriGiustiThreshold_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : ℕ → SmoothScalar g) (outer averagingCutoff : SmoothScalar g)
    (reverseCost : ℕ → ℝ) (a b : ℕ → ℝ)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ D : ℝ} (hp₀ : 0 < p₀)
    (hreverseCost : ∀ k, 1 ≤ reverseCost k)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M) (cutoff k) (a k) (b k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (cutoff k) (a k) (b k)).real Set.univ ≤ 1)
    (hstart : ∀ k, a (k + 1) ≤ a k)
    (hend : ∀ k, b k ≤ b (k + 1))
    (hcutoff : ∀ k x,
      (cutoff k).toFun x ^ 2 ≤ (cutoff (k + 1)).toFun x ^ 2)
    (hτD : τ ≤ D) (hτa : ∀ k, τ ≤ a k) (hbD : ∀ k, b k ≤ D)
    (houter : ∀ k x, (cutoff k).toFun x ^ 2 ≤ outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t)
    (hreverse : ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M) (cutoff k)
          (fun t x => (exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff
              u hu hpos τ) u t x)⁻¹) p₀ (a k) (b k) ≤
        reverseCost k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M) (cutoff (k + 1))
            (fun t x => (exponentialTimeRescale
              (logCenterDrift (I := I) (M := M) g averagingCutoff)
              (shiftedLogCenter (I := I) (M := M) g averagingCutoff
                u hu hpos τ) u t x)⁻¹) p (a (k + 1)) (b (k + 1)))
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (reverseCost k) / 4))) :
    localizedSpacetimeRpowNorm (I := I) (M := M) (cutoff 0)
        (fun t x => (exponentialTimeRescale
          (logCenterDrift (I := I) (M := M) g averagingCutoff)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff
            u hu hpos τ) u t x)⁻¹) p₀ (a 0) (b 0) ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (reverseCost k) / 4)) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
    u hu hpos τ
  let v := exponentialTimeRescale rate center u
  let vinv : ℝ → M → ℝ := fun t x => (v t x)⁻¹
  let c₀ := 2 * C * cutoffMass (I := I) (M := M) averagingCutoff
  have hc₀ : 0 < c₀ := mul_pos (mul_pos (by norm_num) hC) hmass
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvinv : Continuous (fun z : ℝ × M => vinv z.1 z.2) :=
    hv.continuous.inv₀ fun z => (hvpos z.1 z.2).ne'
  have hvinvpos : ∀ t x, 0 < vinv t x := fun t x => inv_pos.mpr (hvpos t x)
  apply localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold
    (I := I) (M := M) cutoff outer (fun z => vinv z.1 z.2) reverseCost a b
      (p₀ := p₀) (c₀ := c₀) (c := τ) (d := D) hp₀ hc₀ hreverseCost
      hvinv (fun z => hvinvpos z.1 z.2) hmeasure hmeasure_le_one
      hstart hend hcutoff hτa hbD houter
  · intro k r hr
    let S : Set (ℝ × M) := {z | r < Real.log (vinv z.1 z.2)}
    have hdom := localizedSpacetimeMeasure_mono (I := I) (M := M)
      (hτa k) (hbD k) (houter k)
    have hreal :
        (localizedSpacetimeMeasure (I := I) (M := M)
          (cutoff k) (a k) (b k)).real S ≤
        (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real S :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hdom S)
    exact hreal.trans (by
      simpa only [S, vinv, v, rate, center, c₀, Real.log_inv] using
        (late_localizedSpacetimeMeasure_neg_log_superlevel_tail_of_supersolution
          (I := I) (M := M) g outer averagingCutoff C hC.le hP
            u hu hpos hτD hr hmass hpde))
  · intro k p hp hpp₀
    simpa only [vinv, v, rate, center] using hreverse k hp hpp₀
  · simpa only [c₀] using hsummable

theorem early_integral_rpow_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q r a τ : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (haτ : a ≤ τ) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hq_int :
      let v := exponentialTimeRescale
        (logCenterDrift (I := I) (M := M) g averagingCutoff)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
      Integrable (fun z : ℝ × M => v z.1 z.2 ^ q)
        (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ)) :
    let v := exponentialTimeRescale
      (logCenterDrift (I := I) (M := M) g averagingCutoff)
      (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
    let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ
    (∫ z, v z.1 z.2 ^ p ∂ν) ≤
      Real.exp (p * r) * ν.real Set.univ +
        (∫ z, v z.1 z.2 ^ q ∂ν) ^ (p / q) *
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r) ^
            (1 - p / q) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let v := exponentialTimeRescale rate center u
  let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hv_pos := exponentialTimeRescale_pos rate center u hpos
  have htail := early_localizedSpacetimeMeasure_log_superlevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
      u hu hpos haτ hr hmass hpde
  simpa only [v, ν, rate, center] using
    integral_rpow_le_of_log_superlevel ν (fun z : ℝ × M => v z.1 z.2)
      hp hq hpq hv.continuous.measurable (fun z => hv_pos z.1 z.2) hq_int htail

theorem late_integral_neg_rpow_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q r τ b : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (hτb : τ ≤ b) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hq_int :
      let v := exponentialTimeRescale
        (logCenterDrift (I := I) (M := M) g averagingCutoff)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
      Integrable (fun z : ℝ × M => v z.1 z.2 ^ (-q))
        (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b)) :
    let v := exponentialTimeRescale
      (logCenterDrift (I := I) (M := M) g averagingCutoff)
      (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
    let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b
    (∫ z, v z.1 z.2 ^ (-p) ∂ν) ≤
      Real.exp (p * r) * ν.real Set.univ +
        (∫ z, v z.1 z.2 ^ (-q) ∂ν) ^ (p / q) *
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r) ^
            (1 - p / q) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let v := exponentialTimeRescale rate center u
  let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hv_pos := exponentialTimeRescale_pos rate center u hpos
  have htail := late_localizedSpacetimeMeasure_neg_log_superlevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
      u hu hpos hτb hr hmass hpde
  simpa only [v, ν, rate, center] using
    integral_neg_rpow_le_of_log_sublevel ν (fun z : ℝ × M => v z.1 z.2)
      hp hq hpq hv.continuous.measurable (fun z => hv_pos z.1 z.2) hq_int htail

end DifferentialGeometry.Analysis.Parabolic.Moser

end
