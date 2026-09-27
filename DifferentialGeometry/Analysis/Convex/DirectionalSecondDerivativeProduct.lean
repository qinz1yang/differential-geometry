import DifferentialGeometry.Analysis.Convex.DirectionalLocalIntegrability
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem second_central_difference_le_of_concaveOn_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ConcaveOn ℝ U (fun x => f x - B x x / 2))
    (x v : E) (r : ℝ) (hr : r ≠ 0) (hp : x + r • v ∈ U) (hm : x - r • v ∈ U) :
    (f (x + r • v) - 2 * f x + f (x - r • v)) / r ^ 2 ≤ B v v := by
  have hconc := hf.2 hp hm (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (x + r • v) + (1 / 2 : ℝ) • (x - r • v) = x := by
    module
  rw [hmid] at hconc
  simp only [smul_eq_mul, map_add, map_sub, map_smul,
    add_apply, sub_apply, smul_apply] at hconc
  apply (div_le_iff₀ (sq_pos_of_ne_zero hr)).mpr
  nlinarith [hconc]

theorem le_of_tendsto_second_central_difference_of_concaveOn_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ConcaveOn ℝ U (fun x => f x - B x x / 2)) (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (v : E) (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) {q : ℝ}
    (hlim : Tendsto
      (fun n => (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2)
      atTop (𝓝 q)) : q ≤ B v v := by
  apply le_of_tendsto hlim
  have hp : Tendsto (fun n => x + h n • v) atTop (𝓝 x) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hh.smul_const v)
  have hm : Tendsto (fun n => x - h n • v) atTop (𝓝 x) := by
    simpa only [zero_smul, sub_zero] using tendsto_const_nhds.sub (hh.smul_const v)
  filter_upwards [hp.eventually (hU.mem_nhds hx), hm.eventually (hU.mem_nhds hx)] with n hn hm
  exact second_central_difference_le_of_concaveOn_sub_quadratic
    B hf x v (h n) (hne n) hn hm

theorem exists_measurable_directional_second_derivative_prod_of_concave_sub_quadratic
    {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure T} {μ : Measure E}
    [Measure.IsAddHaarMeasure μ] {f : T × E → ℝ} {S : Set T} {U : Set E}
    (hfmeas : Measurable f) (hS : MeasurableSet S) (hU : IsOpen U)
    (B : T → E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - B t x x / 2))
    (v : E) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ q : T × E → ℝ, Measurable q ∧
      (∀ p, q p = limUnder atTop (fun n =>
        (U.indicator (fun x => f (p.1, x)) (p.2 + h n • v) -
          2 * U.indicator (fun x => f (p.1, x)) p.2 +
          U.indicator (fun x => f (p.1, x)) (p.2 - h n • v)) / (h n) ^ 2)) ∧
      (∀ t ∈ S, ∀ᵐ x ∂μ, x ∈ U → Tendsto
        (fun n => (f (t, x + h n • v) - 2 * f (t, x) + f (t, x - h n • v)) /
          (h n) ^ 2) atTop (𝓝 (q (t, x)))) ∧
      (∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
        (fun n => (f (p.1, p.2 + h n • v) - 2 * f p + f (p.1, p.2 - h n • v)) /
          (h n) ^ 2) atTop (𝓝 (q p))) ∧
      ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → q p ≤ B p.1 v v := by
  classical
  let F : T × E → ℝ := (univ ×ˢ U).indicator f
  have hFmeas : Measurable F := hfmeas.indicator (MeasurableSet.univ.prod hU.measurableSet)
  let D : ℕ → T × E → ℝ := fun n p =>
    (F (p.1, p.2 + h n • v) - 2 * F p + F (p.1, p.2 - h n • v)) / (h n) ^ 2
  have hDmeas : ∀ n, Measurable (D n) := by
    intro n
    exact (((hFmeas.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub
      (measurable_const.mul hFmeas)).add
        (hFmeas.comp (measurable_fst.prodMk (measurable_snd.sub_const _)))).div_const _
  let q : T × E → ℝ := fun p => limUnder atTop (fun n => D n p)
  have hqmeas : Measurable q :=
    (StronglyMeasurable.limUnder fun n => (hDmeas n).stronglyMeasurable).measurable
  have hFslice : ∀ t x, F (t, x) = U.indicator (fun y => f (t, y)) x := by
    intro t x
    by_cases hx : x ∈ U <;> simp [F, hx]
  have hqeq : ∀ p, q p = limUnder atTop (fun n =>
      (U.indicator (fun x => f (p.1, x)) (p.2 + h n • v) -
        2 * U.indicator (fun x => f (p.1, x)) p.2 +
        U.indicator (fun x => f (p.1, x)) (p.2 - h n • v)) / (h n) ^ 2) := by
    intro p
    simp only [q, D, hFslice]
  have hslice : ∀ t ∈ S, ∀ᵐ x ∂μ, x ∈ U → Tendsto
      (fun n => (f (t, x + h n • v) - 2 * f (t, x) + f (t, x - h n • v)) /
        (h n) ^ 2) atTop (𝓝 (q (t, x))) := by
    intro t ht
    obtain ⟨q', _, _, hq'eq, hq'diff⟩ :=
      exists_locallyIntegrableOn_directional_second_derivative_of_concave_sub_quadratic
        (μ := μ) hU (B t) (hf t ht) v h hh hne
    have heq : ∀ x, q' x = q (t, x) := fun x => (hq'eq x).trans (hqeq (t, x)).symm
    simpa only [heq] using hq'diff
  have hrawmeas : ∀ n, Measurable (fun p : T × E =>
      (f (p.1, p.2 + h n • v) - 2 * f p + f (p.1, p.2 - h n • v)) / (h n) ^ 2) := by
    intro n
    exact (((hfmeas.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub
      (measurable_const.mul hfmeas)).add
        (hfmeas.comp (measurable_fst.prodMk (measurable_snd.sub_const _)))).div_const _
  have hprod : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → Tendsto
      (fun n => (f (p.1, p.2 + h n • v) - 2 * f p + f (p.1, p.2 - h n • v)) /
        (h n) ^ 2) atTop (𝓝 (q p)) := by
    apply (Measure.ae_prod_iff_ae_ae ((hS.prod hU.measurableSet).imp
      (measurableSet_tendsto_fun hrawmeas hqmeas))).mpr
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ S
    · filter_upwards [hslice t ht] with x hx using fun htx => hx htx.2
    · exact Eventually.of_forall fun x htx => (ht htx.1).elim
  refine ⟨q, hqmeas, hqeq, hslice, hprod, ?_⟩
  filter_upwards [hprod] with p hp
  intro hpSU
  exact le_of_tendsto_second_central_difference_of_concaveOn_sub_quadratic
    (B p.1) (hf p.1 hpSU.1) hU hpSU.2 v h hh hne (hp hpSU)

end DifferentialGeometry.Analysis.Calculus
