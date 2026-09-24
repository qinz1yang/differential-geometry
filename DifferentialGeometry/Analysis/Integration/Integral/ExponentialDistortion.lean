import DifferentialGeometry.Analysis.Asymptotics.ExponentialDistortion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp

open Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis.Measure

variable {X : Type*} [MeasurableSpace X]

private theorem exp_neg_integral_bounds
    (mu : Measure X) {f g : X → ℝ} {delta e : ℝ}
    (hf : AEMeasurable f mu) (hg : AEMeasurable g mu)
    (hquarter : Integrable (fun x => Real.exp (-(g x / 4))) mu)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) (hg0 : ∀ᵐ x ∂mu, 0 ≤ g x)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hfg : ∀ᵐ x ∂mu, f x ≤ (1 + delta) * g x + e)
    (hgf : ∀ᵐ x ∂mu, g x ≤ (1 + delta) * f x + e) :
    Integrable (fun x => Real.exp (-f x)) mu ∧
      Integrable (fun x => Real.exp (-g x)) mu ∧
      (∫ x, |Real.exp (-f x) - Real.exp (-g x)| ∂mu) ≤
        16 * (delta + e) * ∫ x, Real.exp (-(g x / 4)) ∂mu := by
  have hfm : AEStronglyMeasurable (fun x => Real.exp (-f x)) mu :=
    hf.neg.exp.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x => Real.exp (-g x)) mu :=
    hg.neg.exp.aestronglyMeasurable
  have hdiff : ∀ᵐ x ∂mu,
      |Real.exp (-f x) - Real.exp (-g x)| ≤
        16 * (delta + e) * Real.exp (-(g x / 4)) := by
    filter_upwards [hf0, hg0, hfg, hgf] with x hfx hgx hfgx hgfx
    exact Asymptotics.abs_exp_neg_sub_exp_neg_le
      hfx hgx hdelta hdelta1 he he1 hfgx hgfx
  have hscaled := hquarter.const_mul (16 * (delta + e))
  have hdiffInt : Integrable (fun x => Real.exp (-f x) - Real.exp (-g x)) mu :=
    hscaled.mono' (hfm.sub hgm) (by simpa only [Real.norm_eq_abs] using hdiff)
  have hgInt : Integrable (fun x => Real.exp (-g x)) mu :=
    hquarter.mono' hgm (by
      filter_upwards [hg0] with x hx
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.exp_le_exp.mpr (by linarith))
  have hfInt : Integrable (fun x => Real.exp (-f x)) mu :=
    (hdiffInt.add hgInt).congr (Eventually.of_forall fun x => sub_add_cancel _ _)
  refine ⟨hfInt, hgInt, ?_⟩
  have hInt := integral_mono_ae hdiffInt.abs hscaled hdiff
  simpa only [integral_const_mul] using hInt

theorem integral_abs_exp_neg_sub_exp_neg_le_of_mul_add_bounds
    (mu : Measure X) {f g : X → ℝ} {delta e : ℝ}
    (hf : AEMeasurable f mu) (hg : AEMeasurable g mu)
    (hquarter : Integrable (fun x => Real.exp (-(g x / 4))) mu)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) (hg0 : ∀ᵐ x ∂mu, 0 ≤ g x)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hfg : ∀ᵐ x ∂mu, f x ≤ (1 + delta) * g x + e)
    (hgf : ∀ᵐ x ∂mu, g x ≤ (1 + delta) * f x + e) :
    (∫ x, |Real.exp (-f x) - Real.exp (-g x)| ∂mu) ≤
      16 * (delta + e) * ∫ x, Real.exp (-(g x / 4)) ∂mu :=
  (exp_neg_integral_bounds mu hf hg hquarter hf0 hg0 hdelta hdelta1 he he1 hfg hgf).2.2

theorem abs_integral_exp_neg_sub_integral_exp_neg_le_of_mul_add_bounds
    (mu : Measure X) {f g : X → ℝ} {delta e : ℝ}
    (hf : AEMeasurable f mu) (hg : AEMeasurable g mu)
    (hquarter : Integrable (fun x => Real.exp (-(g x / 4))) mu)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) (hg0 : ∀ᵐ x ∂mu, 0 ≤ g x)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hfg : ∀ᵐ x ∂mu, f x ≤ (1 + delta) * g x + e)
    (hgf : ∀ᵐ x ∂mu, g x ≤ (1 + delta) * f x + e) :
    |(∫ x, Real.exp (-f x) ∂mu) - ∫ x, Real.exp (-g x) ∂mu| ≤
      16 * (delta + e) * ∫ x, Real.exp (-(g x / 4)) ∂mu := by
  obtain ⟨hfi, hgi, hbound⟩ :=
    exp_neg_integral_bounds mu hf hg hquarter hf0 hg0 hdelta hdelta1 he he1 hfg hgf
  rw [← integral_sub hfi hgi]
  exact abs_integral_le_integral_abs.trans hbound

theorem eventually_integrable_exp_neg_of_mul_add_bounds
    {iota : Type*} {l : Filter iota} (mu : iota → Measure X)
    (f g : iota → X → ℝ) (e : iota → ℝ) {C delta : ℝ}
    (hf : ∀ᶠ i in l, AEMeasurable (f i) (mu i))
    (hg : ∀ᶠ i in l, AEMeasurable (g i) (mu i))
    (hf0 : ∀ᶠ i in l, ∀ᵐ x ∂mu i, 0 ≤ f i x)
    (hg0 : ∀ᶠ i in l, ∀ᵐ x ∂mu i, 0 ≤ g i x)
    (hquarter : ∀ᶠ i in l,
      (∫⁻ x, ENNReal.ofReal (Real.exp (-(g i x / 4))) ∂mu i) ≤ ENNReal.ofReal C)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (he0 : ∀ᶠ i in l, 0 ≤ e i) (he : Tendsto e l (𝓝 0))
    (hfg : ∀ᶠ i in l, ∀ᵐ x ∂mu i, f i x ≤ (1 + delta) * g i x + e i)
    (hgf : ∀ᶠ i in l, ∀ᵐ x ∂mu i, g i x ≤ (1 + delta) * f i x + e i) :
    ∀ᶠ i in l, Integrable (fun x => Real.exp (-f i x)) (mu i) ∧
      Integrable (fun x => Real.exp (-g i x)) (mu i) := by
  have hevent : ∀ᶠ i in l, e i < 1 := he.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hf, hg, hf0, hg0, hquarter, he0, hevent, hfg, hgf]
    with i hfi hgi hfzi hgzi hQi hei he1 hfg_i hgf_i
  have hQnonneg : ∀ᵐ x ∂mu i, 0 ≤ Real.exp (-(g i x / 4)) :=
    Eventually.of_forall fun x => (Real.exp_pos _).le
  have hQmeas : AEStronglyMeasurable (fun x => Real.exp (-(g i x / 4))) (mu i) :=
    (hgi.div_const 4).neg.exp.aestronglyMeasurable
  have hQint : Integrable (fun x => Real.exp (-(g i x / 4))) (mu i) :=
    (lintegral_ofReal_ne_top_iff_integrable hQmeas hQnonneg).mp
      (hQi.trans_lt ENNReal.ofReal_lt_top).ne
  have h := exp_neg_integral_bounds (mu i) hfi hgi hQint hfzi hgzi
    hdelta hdelta1 hei he1.le hfg_i hgf_i
  exact ⟨h.1, h.2.1⟩

theorem tendsto_integral_exp_neg_sub_integral_exp_neg_zero
    {iota : Type*} {l : Filter iota} (mu : iota → Measure X)
    (f g : iota → X → ℝ) {C : ℝ}
    (hf : ∀ᶠ i in l, AEMeasurable (f i) (mu i))
    (hg : ∀ᶠ i in l, AEMeasurable (g i) (mu i))
    (hf0 : ∀ᶠ i in l, ∀ᵐ x ∂mu i, 0 ≤ f i x)
    (hg0 : ∀ᶠ i in l, ∀ᵐ x ∂mu i, 0 ≤ g i x)
    (hquarter : ∀ᶠ i in l,
      (∫⁻ x, ENNReal.ofReal (Real.exp (-(g i x / 4))) ∂mu i) ≤ ENNReal.ofReal C)
    (hcompare : ∀ delta > 0, ∃ e : iota → ℝ,
      Tendsto e l (𝓝 0) ∧ (∀ᶠ i in l, 0 ≤ e i) ∧
      (∀ᶠ i in l, ∀ᵐ x ∂mu i, f i x ≤ (1 + delta) * g i x + e i) ∧
      (∀ᶠ i in l, ∀ᵐ x ∂mu i, g i x ≤ (1 + delta) * f i x + e i)) :
    Tendsto (fun i => (∫ x, Real.exp (-f i x) ∂mu i) -
      ∫ x, Real.exp (-g i x) ∂mu i) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hCB : max C 0 ≤ B := by dsimp only [B]; linarith
  let delta := min (1 / 2 : ℝ) (epsilon / (64 * B))
  have hdelta : 0 < delta := lt_min (by norm_num) (div_pos hepsilon (by positivity))
  have hdelta1 : delta ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hsmall : delta * B ≤ epsilon / 64 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ)
      (epsilon / (64 * B))) hB.le
    have hcancel : (epsilon / (64 * B)) * B = epsilon / 64 := by
      field_simp [hB.ne']
    exact h.trans_eq hcancel
  obtain ⟨e, he, he0, hfg, hgf⟩ := hcompare delta hdelta
  have hevent : ∀ᶠ i in l, e i < delta :=
    he.eventually (gt_mem_nhds hdelta)
  filter_upwards [hf, hg, hf0, hg0, hquarter, he0, hevent,
    hfg, hgf] with i hfi hgi hfzi hgzi hQi hei hedi hfg_i hgf_i
  have hQnonneg : ∀ᵐ x ∂mu i, 0 ≤ Real.exp (-(g i x / 4)) :=
    Eventually.of_forall fun x => (Real.exp_pos _).le
  have hQmeas : AEStronglyMeasurable (fun x => Real.exp (-(g i x / 4))) (mu i) :=
    (hgi.div_const 4).neg.exp.aestronglyMeasurable
  have hQint : Integrable (fun x => Real.exp (-(g i x / 4))) (mu i) :=
    (lintegral_ofReal_ne_top_iff_integrable hQmeas hQnonneg).mp
      (hQi.trans_lt ENNReal.ofReal_lt_top).ne
  have hQbound : (∫ x, Real.exp (-(g i x / 4)) ∂mu i) ≤ max C 0 := by
    rw [integral_eq_lintegral_of_nonneg_ae hQnonneg hQmeas]
    simpa only [ENNReal.toReal_ofReal'] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hQi
  have he1 : e i ≤ 1 := hedi.le.trans hdelta1
  have hmass := abs_integral_exp_neg_sub_integral_exp_neg_le_of_mul_add_bounds
    (mu i) hfi hgi hQint hfzi hgzi hdelta.le hdelta1 hei he1 hfg_i hgf_i
  have hcoef : 0 ≤ 16 * (delta + e i) := by positivity
  have hbound := hmass.trans
    (mul_le_mul_of_nonneg_left (hQbound.trans hCB) hcoef)
  have herr : (delta + e i) * B ≤ 2 * (delta * B) := by
    nlinarith [mul_le_mul_of_nonneg_right hedi.le hB.le]
  have hfinal : |(∫ x, Real.exp (-f i x) ∂mu i) -
      ∫ x, Real.exp (-g i x) ∂mu i| < epsilon := by
    nlinarith
  simpa only [Real.dist_eq, sub_zero] using hfinal

end DifferentialGeometry.Analysis.Measure
