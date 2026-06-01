import DifferentialGeometry.Analysis.Sobolev.Nirenberg.Coercivity

/-!
# Auxiliary infrastructure for cross-term bounds in the master inequality

This module assembles the pointwise estimates and integrability lemmas
needed to bound the cross-term and data-term integrals appearing in
`NirenbergCoercivity.nirenberg_master_inequality`.

## Strategy

Each of the cross terms `Cross_1`, `Cross_2`, `Cross_3` and each of the
data terms `c · u · v_test`, `f · v_test` is bounded by combining

1. a pointwise Young inequality
   `2 |a| |b| ≤ ε a² + (1/ε) b²`,
2. uniform pointwise bounds on the smooth coefficients `a^{ij}`, `c`, on
   `∇η`, `η`, on the translated/difference-quotient versions of `a^{ij}`,
3. a localised L² bound that controls the integral of `(D_h^k v)²` over a
   measurable set `K` by the integral of `(∂_k v)²` over the closed
   `|h|`-thickening of `K`.

This file establishes (1)–(3) in a uniform, `h`-independent way, and proves
the pointwise bound for one summand of `Cross_1` as a worked example. The
remaining integrated cross-term bounds and the headline absorbing inequality
are direct combinations of these pieces.

## Main components

### Localised L² bound

* `lintegral_sq_diffQuot_le_local` — `lintegral` form of the localised L²
  bound: `∫⁻ x in K, ‖D_h^k v(x)‖ₑ² ≤ ∫⁻ y in cthickening |h| K, ‖∂_k v(y)‖ₑ²`.
* `integral_sq_diffQuot_le_local` — real-valued version of the localised
  L² bound, requiring integrability of `(∂_k v)²` on the thickening.
* `integral_diffQuot_sq_on_tsupport_le` — specialisation: bounds
  `∫_{tsupport η} (D_h^k u)²` by `∫_{Ω'} (∂_k u)²` when
  `cthickening |h| (tsupport η) ⊆ Ω'`.

### Pointwise FTC and translation bounds

* `abs_diffQuot_le_of_bound`, `abs_diffQuot_a_le_of_bound_on_set` —
  pointwise FTC bounds for the difference quotient.
* `abs_translate_le_of_bound_on_set` — pointwise translation bound.

### Set-theoretic helpers

* `shift_in_omega'`, `singleton_cthick_subset` — relate the
  `|h|`-thickening of `tsupport η` to the localising set `Ω'`.

### Pointwise inequalities

* `two_abs_mul_le_eps_sq_add` — Young's inequality for absolute values.
* `cross_1_pointwise_bound` — worked example: pointwise bound for one
  summand of the `Cross_1` cross-term, split into ε-Young absorbing
  (`η² · (D_h^k ∂_i u)²`) plus a `tsupport η`-localised data piece
  (`(D_h^k u)²` weighted by an indicator).
* `cross_1_summand_continuous`, `cross_1_summand_compactSupport` —
  regularity of the `Cross_1` summand needed for integrability.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution
open DifferentialGeometry.Analysis.Sobolev.NirenbergCoercivity
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
/-- Localized L² lintegral bound for the difference quotient. -/
private theorem lintegral_sq_diffQuot_le_local
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {K : Set E} (_hK : MeasurableSet K) :
    ∫⁻ x in K, (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E) ≤
      ∫⁻ y in Metric.cthickening |h| K,
        (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure E) := by
  set e : E := EuclideanSpace.single k (1 : ℝ) with he
  set H : E → ℝ≥0∞ := fun y => (‖(fderiv ℝ v y) e‖ₑ : ℝ≥0∞) ^ 2 with hH_def
  have hfd_cont : Continuous (fun y : E => fderiv ℝ v y) :=
    hv.continuous_fderiv one_ne_zero
  have h_partial_cont : Continuous (fun y : E => (fderiv ℝ v y) e) :=
    hfd_cont.clm_apply continuous_const
  have hH_meas : Measurable H := by
    rw [hH_def]
    exact h_partial_cont.measurable.enorm.pow_const 2
  have hPair_meas :
      Measurable (fun p : E × ℝ => H (p.1 + (p.2 * h) • e)) := by
    have h1 : Measurable (fun p : E × ℝ => p.1) := measurable_fst
    have h2 : Measurable (fun p : E × ℝ => p.2) := measurable_snd
    have h3 : Measurable (fun p : E × ℝ => p.2 * h) :=
      h2.mul measurable_const
    have h4 : Measurable (fun p : E × ℝ => (p.2 * h) • e) :=
      h3.smul measurable_const
    have h5 : Measurable (fun p : E × ℝ => p.1 + (p.2 * h) • e) :=
      h1.add h4
    exact hH_meas.comp h5
  have hpt : ∀ x : E,
      (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ≤
        ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) := by
    intro x
    have hreal := sq_diffQuot_le_integral_sq_partialDeriv (d := d) hv k hh x
    have hLHS_eq :
        (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 =
          ENNReal.ofReal ((diffQuot k h v x) ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have hgamma_cont : Continuous (fun s : ℝ => x + (s * h) • e) :=
      continuous_const.add
        ((continuous_id.mul continuous_const).smul continuous_const)
    have hreal_int_cont : Continuous (fun s : ℝ =>
        ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) :=
      ((h_partial_cont.comp hgamma_cont)).pow 2
    have hreal_int :
        Integrable (fun s : ℝ => ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
      hreal_int_cont.integrableOn_Ioc (a := 0) (b := 1)
    have hConvert :
        ENNReal.ofReal
            (∫ s in Set.Ioc (0 : ℝ) 1,
              ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) =
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) := by
      rw [ofReal_integral_eq_lintegral_ofReal hreal_int
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
      refine lintegral_congr_ae ?_
      filter_upwards with s
      change ENNReal.ofReal (((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) =
        (‖(fderiv ℝ v (x + (s * h) • e)) e‖ₑ : ℝ≥0∞) ^ 2
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [hLHS_eq, ← hConvert]
    exact ENNReal.ofReal_le_ofReal hreal
  have h_step12 :
      ∫⁻ x in K, (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E) ≤
        ∫⁻ x in K,
          (∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e))
          ∂(volume : Measure E) := by
    refine lintegral_mono ?_
    intro x; exact hpt x
  have h_swap :
      ∫⁻ x in K,
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) ∂(volume : Measure ℝ)
          ∂(volume : Measure E) =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E)
          ∂(volume : Measure ℝ) := by
    exact lintegral_lintegral_swap hPair_meas.aemeasurable
  have hTrans : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 →
      ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E) ≤
        ∫⁻ y in Metric.cthickening |h| K, H y ∂(volume : Measure E) := by
    intro s hs
    have hMP : MeasurePreserving
        (fun x : E => x + (s * h) • e) volume volume :=
      measurePreserving_add_right volume _
    have hME : MeasurableEmbedding (fun x : E => x + (s * h) • e) :=
      (Homeomorph.addRight ((s * h) • e)).measurableEmbedding
    have h_change :
        ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E) =
          ∫⁻ y in (fun x : E => x + (s * h) • e) '' K, H y
            ∂(volume : Measure E) :=
      hMP.setLIntegral_comp_emb hME H K
    rw [h_change]
    have h_subset : (fun x : E => x + (s * h) • e) '' K ⊆
        Metric.cthickening |h| K := by
      intro y hy
      obtain ⟨x, hxK, hxy⟩ := hy
      refine Metric.mem_cthickening_of_dist_le _ x |h| K hxK ?_
      have hdist_eq : dist y x = ‖(s * h) • e‖ := by
        rw [dist_eq_norm, ← hxy]
        change ‖(x + (s * h) • e) - x‖ = ‖(s * h) • e‖
        rw [add_sub_cancel_left]
      rw [hdist_eq]
      have hsing_norm :
          ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
      have hs_nn : 0 ≤ s := le_of_lt hs.1
      have hs_le_one : s ≤ 1 := hs.2
      have habs_eq : |s * h| = s * |h| := by
        rw [abs_mul, abs_of_nonneg hs_nn]
      rw [habs_eq]
      have habs_h_nn : 0 ≤ |h| := abs_nonneg h
      calc s * |h| ≤ 1 * |h| :=
              mul_le_mul_of_nonneg_right hs_le_one habs_h_nn
        _ = |h| := one_mul _
    exact lintegral_mono_set h_subset
  calc ∫⁻ x in K, (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E)
      ≤ ∫⁻ x in K,
            (∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e))
            ∂(volume : Measure E) := h_step12
    _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E)
          ∂((volume : Measure ℝ)) := h_swap
    _ ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) 1,
            ∫⁻ y in Metric.cthickening |h| K, H y ∂(volume : Measure E)
          ∂((volume : Measure ℝ)) := by
        refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
        refine Filter.Eventually.of_forall ?_
        intro s hs
        exact hTrans s hs
    _ = ∫⁻ y in Metric.cthickening |h| K, H y ∂(volume : Measure E) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ]
        simp [Real.volume_Ioc]

omit [NeZero d] in
/-- Real-valued localized L² bound for the difference quotient: for smooth
`v` whose squared partial derivative is integrable on the closed
`|h|`-thickening of `K`, the integral of `(D_h^k v)²` over `K` is bounded
by the integral of `(∂_k v)²` over the thickening. -/
private theorem integral_sq_diffQuot_le_local
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {K : Set E} (hK : MeasurableSet K)
    (h_thick_int : Integrable
      (fun y : E => ((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2)
      ((volume : Measure E).restrict (Metric.cthickening |h| K))) :
    ∫ x in K, (diffQuot k h v x) ^ 2 ∂(volume : Measure E) ≤
      ∫ y in Metric.cthickening |h| K,
        ((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2
        ∂(volume : Measure E) := by
  set fL : E → ℝ := fun x => (diffQuot k h v x) ^ 2 with hfL_def
  set fR : E → ℝ := fun y => ((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2
    with hfR_def
  have hLHS_nonneg : ∀ x : E, 0 ≤ fL x := fun _ => sq_nonneg _
  have hRHS_nonneg : ∀ y : E, 0 ≤ fR y := fun _ => sq_nonneg _
  have h_lintegral := lintegral_sq_diffQuot_le_local (d := d) hv k hh hK
  have h_norm_LHS : ∀ x : E,
      (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (fL x) := by
    intro x
    change (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((diffQuot k h v x) ^ 2)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  have h_norm_RHS : ∀ y : E,
      (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2 =
        ENNReal.ofReal (fR y) := by
    intro y
    change (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  have h_lintegral_real :
      ∫⁻ x in K, ENNReal.ofReal (fL x) ∂(volume : Measure E) ≤
        ∫⁻ y in Metric.cthickening |h| K, ENNReal.ofReal (fR y)
          ∂(volume : Measure E) := by
    have h1 : (fun x : E => (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2) =
        fun x : E => ENNReal.ofReal (fL x) := by
      funext x; exact h_norm_LHS x
    have h2 : (fun y : E => (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2) =
        fun y : E => ENNReal.ofReal (fR y) := by
      funext y; exact h_norm_RHS y
    rw [← h1, ← h2]; exact h_lintegral
  have hRHS_fin : ∫⁻ y in Metric.cthickening |h| K, ENNReal.ofReal (fR y)
        ∂(volume : Measure E) ≠ ∞ := by
    have h := h_thick_int
    rw [← ofReal_integral_eq_lintegral_ofReal h
      (Filter.Eventually.of_forall hRHS_nonneg)]
    exact ENNReal.ofReal_ne_top
  have hLHS_fin : ∫⁻ x in K, ENNReal.ofReal (fL x) ∂(volume : Measure E) ≠ ∞ :=
    fun h_eq_top => hRHS_fin (le_antisymm le_top
      (by rw [← h_eq_top]; exact h_lintegral_real))
  have hL_meas : AEStronglyMeasurable fL ((volume : Measure E).restrict K) := by
    have hfL_cont : Continuous fL := by
      have hfL_cont : Continuous (diffQuot k h v) := by
        by_cases hh0 : h = 0
        · subst hh0
          rw [diffQuot_zero_h]
          exact continuous_const
        · have hv_cont : Continuous v := hv.continuous
          have h_translate :
              Continuous (fun x : E => v (x + h • EuclideanSpace.single k 1)) := by
            have h_add : Continuous (fun x : E => x + h • EuclideanSpace.single k 1) :=
              continuous_id.add continuous_const
            exact hv_cont.comp h_add
          have h_diff : Continuous (fun x : E =>
              v (x + h • EuclideanSpace.single k 1) - v x) :=
            h_translate.sub hv_cont
          have h_div : Continuous (fun x : E =>
              (v (x + h • EuclideanSpace.single k 1) - v x) / h) :=
            h_diff.div_const h
          have heq : (diffQuot k h v) =
              fun x : E => (v (x + h • EuclideanSpace.single k 1) - v x) / h := by
            funext x
            exact diffQuot_apply_of_ne (d := d) k hh0 v x
          rw [heq]; exact h_div
      exact hfL_cont.pow 2
    exact hfL_cont.aestronglyMeasurable
  have hL_int : Integrable fL ((volume : Measure E).restrict K) := by
    refine ⟨hL_meas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have h_eq : ∀ x : E, (‖fL x‖ₑ : ℝ≥0∞) = ENNReal.ofReal (fL x) := by
      intro x
      rw [Real.enorm_eq_ofReal (hLHS_nonneg x)]
    have heq_lin : ∫⁻ x in K, (‖fL x‖ₑ : ℝ≥0∞) ∂(volume : Measure E) =
        ∫⁻ x in K, ENNReal.ofReal (fL x) ∂(volume : Measure E) :=
      lintegral_congr (fun x => h_eq x)
    rw [heq_lin]
    exact lt_of_le_of_lt (le_refl _) (lt_of_le_of_ne le_top hLHS_fin)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hLHS_nonneg) hL_meas]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hRHS_nonneg) h_thick_int.aestronglyMeasurable]
  exact ENNReal.toReal_mono hRHS_fin h_lintegral_real

omit [NeZero d] in
/-- Pointwise FTC bound: for smooth `g`, the difference quotient
`D_h^k g(x)` is bounded in absolute value by the supremum of `|∂_k g|` on
the closed `|h|`-thickening of `{x}`. In our application, we take `K` to
be a compact set and combine with a uniform sup bound on `cthickening |h| K`. -/
private theorem abs_diffQuot_le_of_bound
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) (k : Fin d) (h : ℝ)
    {x : E} {M : ℝ}
    (hM : ∀ y ∈ Metric.cthickening |h| ({x} : Set E),
      |(fderiv ℝ g y) (EuclideanSpace.single k 1)| ≤ M) :
    |diffQuot k h g x| ≤ M := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    have hx0 : x ∈ Metric.cthickening |0| ({x} : Set E) := by
      have : x ∈ ({x} : Set E) := rfl
      exact self_subset_cthickening _ this
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x hx0)
    simp only [Pi.zero_apply, abs_zero]
    exact hM0
  set e : E := EuclideanSpace.single k (1 : ℝ) with he
  have hFTC := diffQuot_eq_integral_partialDeriv (d := d) hg k hh x
  rw [hFTC]
  have hpt : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 →
      |(fderiv ℝ g (x + (s * h) • e)) e| ≤ M := by
    intro s hs
    have hin : x + (s * h) • e ∈ Metric.cthickening |h| ({x} : Set E) := by
      refine Metric.mem_cthickening_of_dist_le _ x |h| ({x} : Set E) rfl ?_
      have hsing_norm : ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      have hdist_eq :
          dist (x + (s * h) • e) x = |s * h| := by
        rw [dist_eq_norm]
        change ‖(x + (s * h) • e) - x‖ = |s * h|
        rw [add_sub_cancel_left, norm_smul, hsing_norm, mul_one,
          Real.norm_eq_abs]
      rw [hdist_eq]
      have hs_nn : 0 ≤ s := le_of_lt hs.1
      have hs_le_one : s ≤ 1 := hs.2
      have habs_eq : |s * h| = s * |h| := by
        rw [abs_mul, abs_of_nonneg hs_nn]
      rw [habs_eq]
      have habs_h_nn : 0 ≤ |h| := abs_nonneg h
      calc s * |h| ≤ 1 * |h| :=
              mul_le_mul_of_nonneg_right hs_le_one habs_h_nn
        _ = |h| := one_mul _
    exact hM _ hin
  have hint_cont : Continuous (fun s : ℝ =>
      (fderiv ℝ g (x + (s * h) • e)) e) := by
    have hfd_cont : Continuous (fun y : E => fderiv ℝ g y) :=
      hg.continuous_fderiv one_ne_zero
    have hgamma_cont : Continuous (fun s : ℝ => x + (s * h) • e) :=
      continuous_const.add
        ((continuous_id.mul continuous_const).smul continuous_const)
    exact (hfd_cont.comp hgamma_cont).clm_apply continuous_const
  have hint_M : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 → 0 ≤ M :=
    fun s hs => le_trans (abs_nonneg _) (hpt s hs)
  have h1 : 0 ∈ Set.Ioc (0 : ℝ) 1 ∨ ¬ (0 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := em _
  have hM_nonneg : 0 ≤ M := by
    have hs1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_refl _⟩
    exact hint_M 1 hs1
  have h_int :
      Integrable (fun s : ℝ => (fderiv ℝ g (x + (s * h) • e)) e)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    hint_cont.integrableOn_Ioc (a := 0) (b := 1)
  have h_int_abs :
      Integrable (fun s : ℝ => |(fderiv ℝ g (x + (s * h) • e)) e|)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    h_int.abs
  have h_int_const :
      Integrable (fun _ : ℝ => M)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h_cont_M : Continuous (fun _ : ℝ => M) := continuous_const
    exact h_cont_M.integrableOn_Ioc (a := 0) (b := 1)
  have h_tri :
      |∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ g (x + (s * h) • e)) e| ≤
        ∫ s in Set.Ioc (0 : ℝ) 1, |(fderiv ℝ g (x + (s * h) • e)) e| := by
    exact abs_integral_le_integral_abs (μ := (volume : Measure ℝ).restrict _)
  have h_mono :
      ∫ s in Set.Ioc (0 : ℝ) 1, |(fderiv ℝ g (x + (s * h) • e)) e| ≤
        ∫ _s in Set.Ioc (0 : ℝ) 1, M := by
    refine integral_mono_ae h_int_abs h_int_const ?_
    refine ae_restrict_iff_subtype measurableSet_Ioc |>.mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro ⟨s, hs⟩
    exact hpt s hs
  have h_const_int :
      ∫ _s in Set.Ioc (0 : ℝ) 1, M = M := by
    rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Ioc]
  rw [h_const_int] at h_mono
  exact le_trans h_tri h_mono

omit [NeZero d] in
/-- For smooth coefficient `a` and `x` in a compact set whose
`|h|`-thickening lies in `K`, the absolute value of `D_h^k a(x)` is bounded
by the supremum of `|∂_k a|` on `K`. -/
theorem abs_diffQuot_a_le_of_bound_on_set
    {a : E → ℝ} (ha : ContDiff ℝ 1 a) (k : Fin d) (h : ℝ)
    {K : Set E} {M : ℝ}
    (hM : ∀ y ∈ K, |(fderiv ℝ a y) (EuclideanSpace.single k 1)| ≤ M)
    {x : E} (hx : Metric.cthickening |h| ({x} : Set E) ⊆ K) :
    |diffQuot k h a x| ≤ M := by
  refine abs_diffQuot_le_of_bound (d := d) ha k h ?_
  intro y hy
  exact hM y (hx hy)

omit [NeZero d] in
/-- The translation `(τ_h a)(x) = a(x + h e_k)`: if `x + h e_k ∈ K`, then
`|τ_h a(x)| ≤ sup_{y ∈ K} |a(y)|`. -/
private theorem abs_translate_le_of_bound_on_set
    {a : E → ℝ} (k : Fin d) (h : ℝ)
    {K : Set E} {M : ℝ}
    (hM : ∀ y ∈ K, |a y| ≤ M)
    {x : E} (hx : x + h • EuclideanSpace.single k 1 ∈ K) :
    |translate k h a x| ≤ M := by
  unfold translate
  exact hM _ hx

omit [NeZero d] in
/-- For `x ∈ tsupport η` and `|h| ≤ h₀` with
`Metric.cthickening h₀ (tsupport η) ⊆ Ω'`, the shifted point
`x + h e_k ∈ Ω'`. -/
private theorem shift_in_omega'
    (η : E → ℝ) (k : Fin d) {h h₀ : ℝ}
    {Ω' : Set E}
    (hh_supp_in_Ω' : Metric.cthickening h₀ (tsupport η) ⊆ Ω')
    (h_abs : |h| ≤ h₀)
    {x : E} (hx : x ∈ tsupport η) :
    x + h • EuclideanSpace.single k 1 ∈ Ω' := by
  refine hh_supp_in_Ω' ?_
  refine Metric.mem_cthickening_of_dist_le _ x h₀ (tsupport η) hx ?_
  have hsing_norm : ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
  have hdist_eq :
      dist (x + h • EuclideanSpace.single k 1) x = |h| := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hsing_norm, mul_one,
      Real.norm_eq_abs]
  rw [hdist_eq]
  exact h_abs

omit [NeZero d] in
/-- The cthickening of a singleton `{x}` is contained in any `K ⊇ Ω'`
provided `x ∈ tsupport η` and `Metric.cthickening h₀ (tsupport η) ⊆ Ω'`. -/
theorem singleton_cthick_subset
    (η : E → ℝ) {h h₀ : ℝ}
    {Ω' : Set E}
    (hh_supp_in_Ω' : Metric.cthickening h₀ (tsupport η) ⊆ Ω')
    (h_abs : |h| ≤ h₀)
    {x : E} (hx : x ∈ tsupport η) :
    Metric.cthickening |h| ({x} : Set E) ⊆ Ω' := by
  intro y hy
  rw [Metric.mem_cthickening_iff] at hy
  refine hh_supp_in_Ω' ?_
  rw [Metric.mem_cthickening_iff]
  have hsub : ({x} : Set E) ⊆ tsupport η := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]; exact hx
  have h_anti : Metric.infEDist y (tsupport η) ≤ Metric.infEDist y ({x} : Set E) :=
    Metric.infEDist_anti hsub
  refine le_trans h_anti ?_
  refine le_trans hy ?_
  exact_mod_cast ENNReal.ofReal_le_ofReal h_abs

/-- Young's inequality for nonnegative absolute values. -/
private lemma two_abs_mul_le_eps_sq_add (a b ε : ℝ) (hε : 0 < ε) :
    2 * |a| * |b| ≤ ε * a^2 + (1/ε) * b^2 := by
  have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsqrt_ne : Real.sqrt ε ≠ 0 := ne_of_gt hsqrt_pos
  set u : ℝ := Real.sqrt ε * |a|
  set v : ℝ := |b| / Real.sqrt ε
  have huv : 2 * u * v = 2 * |a| * |b| := by
    change 2 * (Real.sqrt ε * |a|) * (|b| / Real.sqrt ε) = 2 * |a| * |b|
    field_simp
  have hu_sq : u^2 = ε * a^2 := by
    change (Real.sqrt ε * |a|)^2 = ε * a^2
    rw [mul_pow, Real.sq_sqrt hε.le, sq_abs]
  have hv_sq : v^2 = (1/ε) * b^2 := by
    change (|b| / Real.sqrt ε)^2 = (1/ε) * b^2
    rw [div_pow, Real.sq_sqrt hε.le, sq_abs]
    field_simp
  calc 2 * |a| * |b| = 2 * u * v := huv.symm
    _ ≤ u^2 + v^2 := two_mul_le_add_sq u v
    _ = ε * a^2 + (1/ε) * b^2 := by rw [hu_sq, hv_sq]

/-- Pointwise bound for one summand of `Cross_1`. -/
private theorem cross_1_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} {Λ : ℝ}
    (h_Λ : ∀ i j : Fin d, ∀ x ∈ closure Ω', |B.a x i j| ≤ Λ)
    (i j k : Fin d) {h : ℝ}
    (hh_supp_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω')
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    |2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x| ≤
      ε * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
      (1/ε) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
  let _ := hu
  let _ := hη
  by_cases hx : x ∈ tsupport η
  · have h_shift_in : x + h • EuclideanSpace.single k 1 ∈ closure Ω' := by
      have h_shift_in_Ω' : x + h • EuclideanSpace.single k 1 ∈ Ω' :=
        shift_in_omega' (d := d) η k hh_supp_in_Ω' (le_refl _) hx
      exact subset_closure h_shift_in_Ω'
    have h_τa_bound : |translate k h (fun y => B.a y i j) x| ≤ Λ := by
      unfold translate
      exact h_Λ i j _ h_shift_in
    have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ N := by
      have hsing_norm :
          ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ = 1 := by simp
      have h_apply :
          ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤
            ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ :=
        (fderiv ℝ η x).le_opNorm _
      rw [hsing_norm, mul_one] at h_apply
      have h2 : ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤ N :=
        h_apply.trans (h_fderiv_eta x)
      rw [Real.norm_eq_abs] at h2
      exact h2
    have h_η_abs : |η x| ≤ 1 := by
      have h_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
      have h0 : 0 ≤ η x := h_in.1
      have h1 : η x ≤ 1 := h_in.2
      rw [abs_of_nonneg h0]; exact h1
    have h_η_nn : 0 ≤ η x := (hη_range ⟨x, rfl⟩).1
    set A : ℝ := η x *
      diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x
    set B' : ℝ := translate k h (fun y => B.a y i j) x *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
      diffQuot k h u x
    have h_eq_lhs :
        |2 * translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x| =
        2 * |A| * |B'| := by
      have hRHS :
          (η x) *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) *
            (translate k h (fun y => B.a y i j) x *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h u x) =
          translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x := by ring
      have h_AB' : A * B' =
          translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x := by
        change (η x) * _ * (translate k h _ x * _ * diffQuot k h u x) = _
        exact hRHS
      have h_2AB' : 2 * A * B' =
          2 * translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x := by
        have : 2 * (A * B') = 2 *
            (translate k h (fun y => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              diffQuot k h u x) := by rw [h_AB']
        linarith
      rw [← h_2AB']
      rw [show |2 * A * B'| = 2 * |A| * |B'| by
        rw [show (2 * A * B') = 2 * (A * B') by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
          abs_mul]
        ring]
    rw [h_eq_lhs]
    have h_young := two_abs_mul_le_eps_sq_add A B' ε hε
    refine h_young.trans ?_
    have hA_sq : A^2 = (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
      change ((η x) * _)^2 = _
      ring
    have hB'_sq_le : B'^2 ≤ Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
      have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
        rw [Set.indicator_of_mem hx]
      rw [h_indicator]
      change (translate k h (fun y => B.a y i j) x *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h u x)^2 ≤ _
      have h_τa_sq_le : (translate k h (fun y => B.a y i j) x)^2 ≤ Λ^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_τa_bound 2
      have h_dη_sq_le : ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 ≤ N^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_dη_bound 2
      have hΛ_nn : 0 ≤ Λ := by
        have h_x_in_Ω' : x ∈ Ω' :=
          hh_supp_in_Ω' (self_subset_cthickening _ hx)
        have h_x_in : x ∈ closure Ω' := subset_closure h_x_in_Ω'
        exact le_trans (abs_nonneg _) (h_Λ i j x h_x_in)
      have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
      have hΛ_sq_nn : 0 ≤ Λ^2 := sq_nonneg _
      have hN_sq_nn : 0 ≤ N^2 := sq_nonneg _
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u x)^2 := sq_nonneg _
      have h_τa_sq_nn : 0 ≤ (translate k h (fun y => B.a y i j) x)^2 := sq_nonneg _
      have h_dη_sq_nn : 0 ≤ ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 := sq_nonneg _
      have h_step1 : (translate k h (fun y => B.a y i j) x)^2 *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 *
            (diffQuot k h u x)^2 ≤
          Λ^2 * N^2 * (diffQuot k h u x)^2 := by
        have h_first :
            (translate k h (fun y => B.a y i j) x)^2 *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 ≤ Λ^2 * N^2 := by
          have hac := mul_le_mul h_τa_sq_le h_dη_sq_le h_dη_sq_nn hΛ_sq_nn
          exact hac
        exact mul_le_mul_of_nonneg_right h_first h_dq_sq_nn
      calc (translate k h (fun y => B.a y i j) x *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h u x)^2
          = (translate k h (fun y => B.a y i j) x)^2 *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 *
              (diffQuot k h u x)^2 := by ring
        _ ≤ Λ^2 * N^2 * (diffQuot k h u x)^2 := h_step1
        _ = Λ^2 * N^2 * 1 * (diffQuot k h u x)^2 := by rw [mul_one]
    have hε_pos : 0 < (1 : ℝ) / ε := one_div_pos.mpr hε
    have h_step :
        (1/ε) * B'^2 ≤ (1/ε) * (Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) :=
      mul_le_mul_of_nonneg_left hB'_sq_le hε_pos.le
    calc ε * A^2 + (1/ε) * B'^2
        ≤ ε * A^2 + (1/ε) * (Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) := by
            linarith
      _ = ε * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
          (1/ε) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 := by
            rw [hA_sq]; ring
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_LHS_zero : 2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x = 0 := by
      rw [h_η_zero]; ring
    rw [h_LHS_zero, abs_zero]
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    have h_t1_nn : 0 ≤ ε * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
      apply mul_nonneg
      · apply mul_nonneg hε.le (sq_nonneg _)
      · exact sq_nonneg _
    have h_t2_zero : (1/ε) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 = 0 := by
      rw [h_indicator]; ring
    linarith

/-- Continuity of `D_h^k u` for smooth `u` (h ≠ 0). -/
lemma continuous_diffQuot_smooth
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (diffQuot k h v) :=
  (contDiff_diffQuot_of_contDiff (d := d) hv k hh).continuous

/-- Auxiliary continuity: `(D_h^k v)²` is continuous for smooth `v`. -/
private lemma continuous_diffQuot_sq_smooth
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E => (diffQuot k h v x)^2) :=
  (continuous_diffQuot_smooth (d := d) hv k hh).pow 2

/-- The integrand of Cross_1 (one (i, j) summand) is continuous. -/
private lemma cross_1_summand_continuous
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) := by
  have h_a_cont : Continuous (fun x : E => B.a x i j) := B.continuous_a i j
  have h_translate_a : Continuous
      (translate k h (fun y => B.a y i j)) := by
    unfold translate
    exact h_a_cont.comp (continuous_id.add continuous_const)
  have h_diffQuot_partial_u : Continuous
      (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
      have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
        hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).contDiff
      exact h_apply_smooth.comp h_fderiv_smooth
    exact continuous_diffQuot_smooth (d := d) h_smooth k hh
  have h_diffQuot_u : Continuous (diffQuot k h u) :=
    continuous_diffQuot_smooth (d := d) hu k hh
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  have h_partial_η : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single j 1)) :=
    ((hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  refine (((((continuous_const.mul h_translate_a).mul hη.continuous).mul
    h_partial_η).mul h_diffQuot_partial_u).mul h_diffQuot_u)

/-- The integrand of Cross_1 has compact support (inherits from `η`). -/
private lemma cross_1_summand_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ)
    {η : E → ℝ} (hη_supp : HasCompactSupport η)
    (i j k : Fin d) (h : ℝ) :
    HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) := by
  have h_step1 : HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x)) :=
    hη_supp.mul_left
  have h_step2 : HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1))) := h_step1.mul_right
  have h_step3 : HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
    h_step2.mul_right
  exact h_step3.mul_right

/-- A bound for `∫_{tsupport η} (D_h^k u)²` in terms of `∫_{Ω'} (∂_k u)²`,
when `cthickening |h| (tsupport η) ⊆ Ω'`. -/
private theorem integral_diffQuot_sq_on_tsupport_le
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (η : E → ℝ)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_compact : IsCompact (closure Ω'))
    (hh_supp_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
      ∫ x in Ω', ((fderiv ℝ u x) (EuclideanSpace.single k 1))^2
        ∂(volume : Measure E) := by
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    isClosed_tsupport η |>.measurableSet
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have h_deriv_cont : Continuous (fun y : E =>
      ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2) := by
    have h_fderiv_cont : Continuous (fderiv ℝ u) :=
      hu_C1.continuous_fderiv (by norm_num)
    exact (h_fderiv_cont.clm_apply continuous_const).pow 2
  have h_thick_compact : IsCompact (Metric.cthickening |h| (tsupport η)) := by
    have h_thick_closed : IsClosed (Metric.cthickening |h| (tsupport η)) :=
      isClosed_cthickening
    have h_thick_subset_clO : Metric.cthickening |h| (tsupport η) ⊆ closure Ω' :=
      hh_supp_in_Ω'.trans subset_closure
    exact hΩ'_compact.of_isClosed_subset h_thick_closed h_thick_subset_clO
  have h_thick_int :
      Integrable (fun y : E =>
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2)
        ((volume : Measure E).restrict (Metric.cthickening |h| (tsupport η))) := by
    refine ContinuousOn.integrableOn_compact h_thick_compact ?_
    exact h_deriv_cont.continuousOn
  have h_local := integral_sq_diffQuot_le_local (d := d) hu_C1 k hh
    h_tsupp_meas h_thick_int
  have h_Ω'_meas : MeasurableSet Ω' := hΩ'.measurableSet
  have h_clΩ'_int :
      Integrable (fun y : E =>
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2)
        ((volume : Measure E).restrict (closure Ω')) :=
    ContinuousOn.integrableOn_compact hΩ'_compact h_deriv_cont.continuousOn
  have h_Ω'_int :
      Integrable (fun y : E =>
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2)
        ((volume : Measure E).restrict Ω') := by
    have : (volume : Measure E).restrict Ω' ≤ (volume : Measure E).restrict (closure Ω') :=
      Measure.restrict_mono subset_closure (le_refl _)
    exact h_clΩ'_int.mono_measure this
  have h_setIntegral_mono :
      ∫ y in Metric.cthickening |h| (tsupport η),
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2
          ∂(volume : Measure E) ≤
        ∫ y in Ω', ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2
          ∂(volume : Measure E) := by
    refine setIntegral_mono_set h_Ω'_int ?_ ?_
    · refine Filter.Eventually.of_forall ?_; intro x; exact sq_nonneg _
    · exact (Filter.Eventually.of_forall hh_supp_in_Ω').mono (fun _ h => h)
  exact h_local.trans h_setIntegral_mono

/-- The "η²-weighted absorbing integral" appearing in every cross-term
bound: `∫ η² · ∑_i (D_h^k ∂_i u)²`. This is the term we absorb on the LHS
in the master inequality after applying Young to all cross terms. -/
private noncomputable def absorbingIntegral
    (k : Fin d) (h : ℝ) (η u : E → ℝ) : ℝ :=
  ∫ x, (η x)^2 *
      ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
    ∂(volume : Measure E)

/-- The "Ω'-localized gradient L² norm squared": `∫_{Ω'} ∑_i (∂_i u)²`. -/
private noncomputable def gradL2sqOn (Ω' : Set E) (u : E → ℝ) : ℝ :=
  ∫ x in Ω',
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
    ∂(volume : Measure E)

omit [NeZero d] in
/-- The absorbing integral is nonnegative. -/
private lemma absorbingIntegral_nonneg
    (k : Fin d) (h : ℝ) (η u : E → ℝ) :
    0 ≤ absorbingIntegral (d := d) k h η u := by
  unfold absorbingIntegral
  refine integral_nonneg ?_
  intro x
  refine mul_nonneg (sq_nonneg _) ?_
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [NeZero d] in
/-- `gradL2sqOn` is nonnegative. -/
private lemma gradL2sqOn_nonneg (Ω' : Set E) (u : E → ℝ) :
    0 ≤ gradL2sqOn (d := d) Ω' u := by
  unfold gradL2sqOn
  refine integral_nonneg ?_
  intro x
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- For smooth `u` and `h ≠ 0`, `D_h^k(∂_i u)` is continuous. -/
private lemma continuous_diffQuot_partial_u
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (i k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single i (1 : ℝ))).contDiff
    exact h_apply_smooth.comp h_fderiv_smooth
  exact continuous_diffQuot_smooth (d := d) h_smooth k hh

omit [NeZero d] in
/-- Continuity of `(fderiv ℝ u) (EuclideanSpace.single i 1)` for smooth `u`. -/
private lemma continuous_partial_u
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) :
    Continuous (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) := by
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  exact (hu_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Compact-support version of integrability of `(η x)² · ∑_i (D_h^k(∂_i u) x)²`. -/
private lemma integrable_eta_sq_diffQuot_sum
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E => (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (volume : Measure E) := by
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_supp.mul_right
  have h_diffQuot_partial_cont : ∀ i : Fin d,
      Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) :=
    fun i => continuous_diffQuot_partial_u (d := d) hu i k hh
  have h_inner_cont : Continuous (fun x : E =>
      ∑ i : Fin d, (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    continuous_finset_sum _ (fun i _ => (h_diffQuot_partial_cont i).pow 2)
  have h_eta_sq_cont : Continuous (fun x : E => η x ^ 2) := hη.continuous.pow 2
  have h_prod_cont : Continuous (fun x : E => (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_cont.mul h_inner_cont
  have h_prod_supp : HasCompactSupport (fun x : E => (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_supp.mul_right
  exact h_prod_cont.integrable_of_hasCompactSupport h_prod_supp

/-- Integrability of the per-(i, j) integrand of Cross_1. -/
private lemma integrable_cross_1_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) volume := by
  have h_cont := cross_1_summand_continuous (d := d) B hu hη i j k hh
  have h_supp := cross_1_summand_compactSupport (d := d) B u hη_supp i j k h
  exact h_cont.integrable_of_hasCompactSupport h_supp

/-- A bound for `∫_{tsupport η} (D_h^k u)²` in terms of
`gradL2sqOn Ω' u`. -/
private theorem integral_diffQuot_sq_on_tsupport_le_gradL2sqOn
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (η : E → ℝ)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_compact : IsCompact (closure Ω'))
    (hh_supp_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
      gradL2sqOn (d := d) Ω' u := by
  have h_step1 := integral_diffQuot_sq_on_tsupport_le (d := d) hu k hh η hΩ'
    hΩ'_compact hh_supp_in_Ω'
  refine h_step1.trans ?_
  unfold gradL2sqOn
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have h_fderiv_cont : Continuous (fderiv ℝ u) :=
    hu_C1.continuous_fderiv (by norm_num)
  have h_partial_cont : ∀ i : Fin d,
      Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
    fun i => h_fderiv_cont.clm_apply continuous_const
  have h_partial_sq_cont : ∀ i : Fin d,
      Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
    fun i => (h_partial_cont i).pow 2
  have h_clΩ'_int : ∀ i : Fin d, Integrable
      (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      ((volume : Measure E).restrict (closure Ω')) :=
    fun i => ContinuousOn.integrableOn_compact hΩ'_compact (h_partial_sq_cont i).continuousOn
  have h_Ω'_int : ∀ i : Fin d, Integrable
      (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      ((volume : Measure E).restrict Ω') :=
    fun i => (h_clΩ'_int i).mono_measure (Measure.restrict_mono subset_closure (le_refl _))
  have h_sum_int : Integrable (fun x : E =>
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      ((volume : Measure E).restrict Ω') :=
    integrable_finset_sum _ (fun i _ => h_Ω'_int i)
  refine setIntegral_mono_on (h_Ω'_int k) h_sum_int hΩ'.measurableSet ?_
  intro x _
  refine Finset.single_le_sum (f := fun i =>
      ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ?_ (Finset.mem_univ k)
  intro i _
  exact sq_nonneg _

/-- Integrability of `(η x)² · (D_h^k(∂_i u) x)²`. -/
private lemma integrable_eta_sq_diffQuot_partial_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (i k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E => (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (volume : Measure E) := by
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_supp.mul_right
  have h_eta_sq_cont : Continuous (fun y : E => η y ^ 2) := hη.continuous.pow 2
  have h_diffQuot_cont :
      Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) :=
    continuous_diffQuot_partial_u (d := d) hu i k hh
  have h_cont : Continuous (fun x : E => (η x)^2 *
      (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_cont.mul (h_diffQuot_cont.pow 2)
  have h_supp : HasCompactSupport (fun x : E => (η x)^2 *
      (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_supp.mul_right
  exact h_cont.integrable_of_hasCompactSupport h_supp

/-- Integrability of `(c : ℝ) · η² · (D_h^k(∂_i u))²` (constant multiplier). -/
private lemma integrable_const_eta_sq_diffQuot_partial_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (i k : Fin d) {h : ℝ} (hh : h ≠ 0) (c : ℝ) :
    Integrable (fun x : E => c * (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (volume : Measure E) := by
  have h_base := integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp i k hh
  have h_eq : (fun x : E => c * (η x)^2 *
      (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) =
      (fun x : E => c * ((η x)^2 *
        (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)) := by
    funext x; ring
  rw [h_eq]
  exact h_base.const_mul c

/-- Integrability of `c · 𝟙_{tsupport η} · (D_h^k u)²`. -/
private lemma integrable_const_indicator_diffQuot_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη_supp : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) (c : ℝ) :
    Integrable (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2) (volume : Measure E) := by
  have h_diffQuot_u_cont : Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
    continuous_diffQuot_smooth (d := d) hu k hh
  have h_diffQuot_u_sq_cont : Continuous (fun x : E => (diffQuot k h u x)^2) :=
    h_diffQuot_u_cont.pow 2
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    isClosed_tsupport η |>.measurableSet
  have h_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_eq : (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2) =
      (fun x : E => Set.indicator (tsupport η)
        (fun y : E => c * (diffQuot k h u y)^2) x) := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
  rw [h_eq]
  have h_inner_cont : Continuous (fun y : E => c * (diffQuot k h u y)^2) :=
    continuous_const.mul h_diffQuot_u_sq_cont
  exact (ContinuousOn.integrableOn_compact h_tsupp_compact h_inner_cont.continuousOn).integrable_indicator
    h_tsupp_meas

/-- Conversion of `∫ c · 𝟙_K · f` to `c · ∫_K f`. -/
private lemma integral_const_indicator_eq
    {u : E → ℝ} (k : Fin d) (h : ℝ) (η : E → ℝ) (c : ℝ) :
    ∫ x, c * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 ∂(volume : Measure E) =
      c * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by
  have h_eq : (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2) =
      (fun x : E => c * ((Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * (diffQuot k h u x)^2)) := by
    funext x; ring
  rw [h_eq, integral_const_mul]
  congr 1
  rw [show (fun x : E => (Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * (diffQuot k h u x)^2) =
      (fun x : E => Set.indicator (tsupport η)
        (fun y : E => (diffQuot k h u y)^2) x) from by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
  rw [MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]

set_option linter.unusedVariables false in
/-- The first cross term is bounded by an absorbing piece plus a
gradient piece localised on `Ω'`. -/
theorem cross_1_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
            (DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j)) x *
            (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * ∫ x in Ω',
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
          ∂(volume : Measure E) := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    SmoothEllipticBilinearForm.bounded_a_on_compact (d := d) B hΩ'_compact
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  have hε'_pos : 0 < ε / d_real := div_pos hε hd_pos
  set C : ℝ := (1 / (ε / d_real)) * Λ^2 * N^2 * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    cross_1_pointwise_bound (d := d) B hu hη hη_range h_fderiv_eta
      hΛ i j k h_thick_in_Ω' hε'_pos x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        translate k h (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x
      ∂(volume : Measure E) with hS_def
  have h_neg_abs : |- S| = |S| := abs_neg S
  rw [h_neg_abs]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          translate k h (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          diffQuot k h u x
        ∂(volume : Measure E)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro i _
    exact Finset.abs_sum_le_sum_abs _ _
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) volume :=
    fun i j => integrable_cross_1_summand (d := d) B hu hη hη_supp i j k hh
  have h_first_int : ∀ i : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
    fun i => integrable_const_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp
      i k hh (ε / d_real)
  have h_indicator_int : Integrable (fun x : E =>
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_sq (d := d) hu hη_supp
      k hh ((1 / (ε / d_real)) * Λ^2 * N^2)
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    fun i _ => (h_first_int i).add h_indicator_int
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, 2 * translate k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∫ x, ((ε / d_real) * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => 2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          translate k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_eq :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) =
      ε * ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) +
      d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) := by
    have h_per_ij : ∀ i j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
          (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) =
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) +
        ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_first_int i) h_indicator_int]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_per_ij i j))]
    have h_step_b : ∀ i : Fin d, ∑ _j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        d_real * (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) := by
      intro i
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ i : Fin d, ∑ _j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        ∑ i : Fin d, d_real * (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => h_step_b i)]
    rw [← Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    rw [show (∑ _i : Fin d, ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        d_real * ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E)
        from by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have h_indicator_eq := integral_const_indicator_eq (d := d) k h η
      ((1 / (ε / d_real)) * Λ^2 * N^2) (u := u)
    rw [h_indicator_eq]
    have h_eta_sq_diffQuot_int : ∀ i : Fin d,
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) =
        (ε / d_real) * ∫ x, (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => (ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) =
          fun x : E => (ε / d_real) * ((η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
          from by funext x; ring]
      rw [integral_const_mul]
    rw [show (∑ i : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E)) =
        ∑ i : Fin d, (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_eta_sq_diffQuot_int i)]
    rw [← Finset.mul_sum]
    have h_first_int_per : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
      fun i => integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp i k hh
    have h_swap_sum : ∑ i : Fin d, ∫ x, (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) =
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) := by
      rw [← integral_finset_sum _ (fun i _ => h_first_int_per i)]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [Finset.mul_sum]
    rw [h_swap_sum]
    rw [mul_add]
    congr 1
    · rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hd_pos)]
    · ring
  rw [h_total_eq]
  have h_diffQuot_sq_le := integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d)
    hu k hh η hΩ' hΩ'_compact h_thick_in_Ω'
  unfold gradL2sqOn at h_diffQuot_sq_le
  have h_factor_nn : 0 ≤ (1 / (ε / d_real)) * Λ^2 * N^2 := by
    refine mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  have h_d_real_sq_nn : 0 ≤ d_real^2 := sq_nonneg _
  have h_C_eq : C = d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2) := by
    rw [hC_def]; ring
  have h_combine :
      d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
        ∂(volume : Measure E) := by
    rw [show d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        (d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2)) *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)
        from by ring, ← h_C_eq]
    refine mul_le_mul_of_nonneg_left h_diffQuot_sq_le ?_
    rw [h_C_eq]; exact mul_nonneg h_d_real_sq_nn h_factor_nn
  linarith

set_option linter.unusedVariables false in
/-- Pointwise bound for one summand of `Cross_2`. -/
private theorem cross_2_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    (i j k : Fin d)
    {Ω' : Set E} {M : ℝ} (hM_nn : 0 ≤ M)
    (h_M : ∀ i j : Fin d, ∀ x ∈ closure Ω',
      |(fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single k 1)| ≤ M)
    {h : ℝ}
    (hh_supp_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω')
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| ≤
      ε * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
      (M^2 / (4 * ε)) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
  classical
  by_cases hx : x ∈ tsupport η
  · have h_dq_a_bound : |diffQuot k h (fun y => B.a y i j) x| ≤ M :=
      abs_diffQuot_a_le_of_bound_on_set (d := d) (B.contDiff_a i j |>.of_le (by norm_cast)) k h
        (h_M i j) ((singleton_cthick_subset (d := d) η hh_supp_in_Ω' (le_refl _) hx).trans
          subset_closure)
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_le : η x ≤ 1 := h_η_in.2
    have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
    set A : ℝ := η x *
      diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x with hA_def
    set B' : ℝ := M * η x *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) with hB'_def
    have h2ε_pos : 0 < 2 * ε := by linarith
    have h_young := two_abs_mul_le_eps_sq_add A B' (2 * ε) h2ε_pos
    have h_AB_abs : |A * B'| ≤ ε * A^2 + (1/(4*ε)) * B'^2 := by
      have h1 : |A * B'| = |A| * |B'| := abs_mul A B'
      have h_double : 2 * (ε * A^2 + (1/(4*ε)) * B'^2) =
          2 * ε * A^2 + (1/(2*ε)) * B'^2 := by
        field_simp
        ring
      have h_ε_ne : ε ≠ 0 := ne_of_gt hε
      linarith [h_young, h_double]
    have h_lhs_bound :
        |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| ≤
          |A * B'| := by
      have h_lhs_abs_eq : |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| =
          |diffQuot k h (fun y => B.a y i j) x| * (η x)^2 *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| := by
        rw [abs_mul, abs_mul, abs_mul]
        rw [show |(η x)^2| = (η x)^2 from abs_of_nonneg h_η_sq_nn]
      have h_AB_abs_eq : |A * B'| =
          M * (η x)^2 * |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
          |diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| := by
        change |(η x * _) * (M * η x * _)| = _
        rw [show η x * diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x *
            (M * η x * (fderiv ℝ u x) (EuclideanSpace.single i 1)) =
          M * (η x)^2 * (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x from by
              rw [sq]; ring]
        rw [abs_mul, abs_mul, abs_mul]
        rw [abs_of_nonneg hM_nn, abs_of_nonneg h_η_sq_nn]
      rw [h_lhs_abs_eq, h_AB_abs_eq]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h_dq_a_bound h_η_sq_nn
    refine h_lhs_bound.trans ?_
    refine h_AB_abs.trans ?_
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    have hA_sq : A^2 = (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 := by
      change (η x * _)^2 = _; ring
    have hB'_sq_le : B'^2 ≤ M^2 * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
      change (M * η x * _)^2 ≤ _; nlinarith
    have h_4ε_pos : 0 < 4 * ε := by linarith
    have h_4ε_ne : (4 * ε) ≠ 0 := ne_of_gt h_4ε_pos
    have h_inv_4ε_nn : 0 ≤ 1 / (4 * ε) :=
      one_div_nonneg.mpr (by linarith)
    have h_step :
        (1/(4*ε)) * B'^2 ≤ (1/(4*ε)) * (M^2 * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
      mul_le_mul_of_nonneg_left hB'_sq_le h_inv_4ε_nn
    calc ε * A^2 + (1/(4*ε)) * B'^2
        ≤ ε * A^2 + (1/(4*ε)) *
            (M^2 * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by linarith
      _ = ε * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * ε)) * (η x)^2 * 1 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
            rw [hA_sq]
            have h_div_eq : 1 / (4 * ε) * (M^2 * (η x)^2 *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
                M^2 / (4 * ε) * (η x)^2 * 1 *
                  ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
              field_simp
            linarith [h_div_eq]
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    rw [h_indicator]
    have h_lhs_zero : diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x = 0 := by
      rw [h_η_zero]; ring
    rw [h_lhs_zero, abs_zero]
    have h_t1_nn : 0 ≤ ε * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 := by
      apply mul_nonneg
      · apply mul_nonneg hε.le (sq_nonneg _)
      · exact sq_nonneg _
    have h_t2_zero : (M^2 / (4 * ε)) * (η x)^2 * 0 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 = 0 := by ring
    linarith

/-- Continuity of the (i, j) summand of Cross_2. -/
private lemma cross_2_summand_continuous
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
  have h_dq_a : Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun y : E => B.a y i j)) :=
    continuous_diffQuot_smooth (d := d) (B.contDiff_a i j) k hh
  have h_eta_sq_cont : Continuous (fun x : E => (η x)^2) := hη.continuous.pow 2
  have h_partial_u : Continuous
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    continuous_partial_u (d := d) hu i
  have h_dq_partial_u : Continuous
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1))) :=
    continuous_diffQuot_partial_u (d := d) hu j k hh
  exact (((h_dq_a.mul h_eta_sq_cont).mul h_partial_u).mul h_dq_partial_u)

/-- The (i, j) summand of Cross_2 has compact support. -/
private lemma cross_2_summand_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) {η : E → ℝ} (hη_supp : HasCompactSupport η)
    (i j k : Fin d) (h : ℝ) :
    HasCompactSupport (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_supp.mul_right
  have h1 : HasCompactSupport (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2) :=
    h_eta_sq_supp.mul_left
  have h2 : HasCompactSupport (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
    h1.mul_right
  exact h2.mul_right

/-- Integrability of the (i, j) summand of Cross_2. -/
private lemma integrable_cross_2_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
      volume :=
  (cross_2_summand_continuous (d := d) B hu hη i j k hh).integrable_of_hasCompactSupport
    (cross_2_summand_compactSupport (d := d) B u hη_supp i j k h)

/-- Integrability of `c · η² · 𝟙_{tsupport η} · (∂_i u)²`. -/
private lemma integrable_const_eta_sq_indicator_partial_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (i : Fin d) (c : ℝ) :
    Integrable (fun x : E => c * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      (volume : Measure E) := by
  have h_partial_cont : Continuous
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    continuous_partial_u (d := d) hu i
  have h_eta_sq_cont : Continuous (fun x : E => (η x)^2) := hη.continuous.pow 2
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_supp.mul_right
  have h_eq : (fun x : E => c * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
      (fun x : E => c * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx]
      have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [h_η_zero]; ring
  rw [h_eq]
  have h_cont : Continuous (fun x : E => c * (η x)^2 *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
    (continuous_const.mul h_eta_sq_cont).mul (h_partial_cont.pow 2)
  have h_step1 : HasCompactSupport (fun x : E => c * (η x)^2) :=
    h_eta_sq_supp.mul_left
  have h_step2 : HasCompactSupport (fun x : E => c * (η x)^2 *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
    h_step1.mul_right
  exact h_cont.integrable_of_hasCompactSupport h_step2

set_option linter.unusedVariables false in
/-- The second cross term is bounded by an absorbing piece plus a
gradient piece localised on `Ω'`. -/
theorem cross_2_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x,
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x *
            (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * ∫ x in Ω',
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
          ∂(volume : Measure E) := by
  classical
  obtain ⟨M, hM_nn, h_M⟩ :=
    SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact (d := d) B k hΩ'_compact
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  have hε'_pos : 0 < ε / d_real := div_pos hε hd_pos
  set C : ℝ := (M^2 / (4 * (ε / d_real))) * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg (sq_nonneg _) ?_
    refine inv_nonneg.mpr (by linarith [hε'_pos])
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    cross_2_pointwise_bound (d := d) B hu hη hη_range i j k hM_nn h_M
      h_thick_in_Ω' hε'_pos x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        diffQuot k h (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
      ∂(volume : Measure E) with hS_def
  rw [abs_neg]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x,
          diffQuot k h (fun y : E => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
      volume :=
    fun i j => integrable_cross_2_summand (d := d) B hu hη hη_supp i j k hh
  have h_first_int : ∀ j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) volume :=
    fun j => integrable_const_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp
      j k hh (ε / d_real)
  have h_second_int : ∀ i : Fin d, Integrable (fun x : E =>
      (M^2 / (4 * (ε / d_real))) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume :=
    fun i => integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i
      (M^2 / (4 * (ε / d_real)))
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
      (M^2 / (4 * (ε / d_real))) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume :=
    fun i j => (h_first_int j).add (h_second_int i)
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E)| ≤
      ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
        (M^2 / (4 * (ε / d_real))) * (η x)^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x,
          diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_eq :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) =
      ε * ∫ x, (η x)^2 *
          ∑ j : Fin d, (diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
        ∂(volume : Measure E) +
      d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E)) := by
    have h_per_ij : ∀ i j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) =
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
          ∂(volume : Measure E) +
        ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_first_int j) (h_second_int i)]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
          ∫ x, ((ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
            (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) from
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_per_ij i j))]
    have h_inner_step : ∀ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) +
        d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
            (∫ x, (ε / d_real) * (η x)^2 *
                (diffQuot k h
                  (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
              ∂(volume : Measure E) +
            ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E))) =
        ∑ i : Fin d,
          ((∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
                (diffQuot k h
                  (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
              ∂(volume : Measure E)) +
          d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => h_inner_step i)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_first_eq : d_real * (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) =
        ε * ∫ x, (η x)^2 *
            ∑ j : Fin d, (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
          ∂(volume : Measure E) := by
      have h_pull_const : ∀ j : Fin d,
          ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) =
          (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) := by
        intro j
        rw [show (fun x : E => (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) =
            fun x : E => (ε / d_real) * ((η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) from
            by funext x; ring]
        rw [integral_const_mul]
      rw [show (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) =
          ∑ j : Fin d, (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) from
          Finset.sum_congr rfl (fun j _ => h_pull_const j)]
      rw [← Finset.mul_sum]
      have h_eta_sq_diffQuot_int : ∀ j : Fin d, Integrable (fun x : E =>
          (η x)^2 * (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) volume :=
        fun j => integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp j k hh
      rw [show (∑ j : Fin d, ∫ x, (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) =
          ∫ x, ∑ j : Fin d, ((η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2)
            ∂(volume : Measure E)
          from (integral_finset_sum _ (fun j _ => h_eta_sq_diffQuot_int j)).symm]
      have h_swap : (fun x : E => ∑ j : Fin d, ((η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2)) =
          fun x : E => (η x)^2 * ∑ j : Fin d, (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 := by
        funext x; rw [Finset.mul_sum]
      rw [h_swap, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hd_pos)]
    rw [h_first_eq]
    have h_second_eq :
        (∑ i : Fin d, d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        d_real * (∑ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h_second_eq]
    have h_pull_const_2 : ∀ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) =
        (M^2 / (4 * (ε / d_real))) * ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          fun x : E => (M^2 / (4 * (ε / d_real))) * ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) from by funext x; ring]
      rw [integral_const_mul]
    rw [show (∑ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        ∑ i : Fin d, (M^2 / (4 * (ε / d_real))) * ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_pull_const_2 i)]
    rw [← Finset.mul_sum]
    have h_inner_int : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume := by
      intro i
      have h := integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i 1
      have h_eq : (fun x : E => (1 : ℝ) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          (fun x : E => (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by
        funext x; ring
      rw [h_eq] at h; exact h
    rw [show (∑ i : Fin d, ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        ∫ x, ∑ i : Fin d, ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) from
        (integral_finset_sum _ (fun i _ => h_inner_int i)).symm]
    have h_swap : (fun x : E => ∑ i : Fin d, ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) =
        fun x : E => (η x)^2 *
            ∑ i : Fin d, ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by
      funext x; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    rw [h_swap]
  rw [h_total_eq]
  have h_M_factor_nn : 0 ≤ M^2 / (4 * (ε / d_real)) := by
    refine div_nonneg (sq_nonneg _) (by linarith)
  have h_d_real_ge_one : 1 ≤ d_real := by
    rw [hd_real]
    have hd_natpos : 0 < Fintype.card (Fin d) := Fintype.card_pos
    exact_mod_cast hd_natpos
  have h_ind_bound :
      ∫ x, (η x)^2 *
        ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
      ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
        ∂(volume : Measure E) := by
    have h_pointwise : ∀ x : E,
        (η x)^2 * ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ≤
        (Set.indicator Ω' (fun y : E => ∑ i : Fin d,
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2)) x := by
      intro x
      by_cases hx : x ∈ tsupport η
      · have hx_Ω' : x ∈ Ω' :=
          h_thick_in_Ω' (self_subset_cthickening _ hx)
        rw [Set.indicator_of_mem hx_Ω']
        have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
        have h_η_sq_le : (η x)^2 ≤ 1 := by
          have h_η_le : η x ≤ 1 := h_η_in.2
          have h_η_nn : 0 ≤ η x := h_η_in.1
          calc (η x)^2 ≤ (1 : ℝ)^2 := by
                  refine pow_le_pow_left₀ h_η_nn h_η_le 2
            _ = 1 := one_pow _
        have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
        have h_indicator_le_one : ∀ y : E,
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) y) ≤ 1 := by
          intro y
          by_cases hy : y ∈ tsupport η
          · rw [Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy]; norm_num
        have h_sum_le : ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ≤
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
          refine Finset.sum_le_sum ?_
          intro i _
          have h_le := h_indicator_le_one x
          have h_sq_nn : 0 ≤ ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := sq_nonneg _
          have h_step : (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ≤
              1 * ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 :=
            mul_le_mul_of_nonneg_right h_le h_sq_nn
          linarith
        have h_sum_nn : 0 ≤ ∑ i : Fin d,
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
          refine Finset.sum_nonneg ?_
          intro i _
          have h_ind_nn : 0 ≤ Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x := by
            by_cases hxx : x ∈ tsupport η
            · rw [Set.indicator_of_mem hxx]; norm_num
            · rw [Set.indicator_of_notMem hxx]
          exact mul_nonneg h_ind_nn (sq_nonneg _)
        calc (η x)^2 * (∑ i : Fin d,
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                  ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ≤
            1 * (∑ i : Fin d,
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                  ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
              mul_le_mul_of_nonneg_right h_η_sq_le h_sum_nn
          _ = ∑ i : Fin d,
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by ring
          _ ≤ ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := h_sum_le
      · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [h_η_zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, ge_iff_le]
        by_cases hx_Ω' : x ∈ Ω'
        · rw [Set.indicator_of_mem hx_Ω']
          exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
        · rw [Set.indicator_of_notMem hx_Ω']
    have h_lhs_int : Integrable (fun x : E =>
        (η x)^2 * ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume := by
      have h_each_int : ∀ i : Fin d, Integrable (fun x : E =>
          (η x)^2 * ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) volume := by
        intro i
        have h := integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i 1
        have h_eq : (fun x : E => (1 : ℝ) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
            (fun x : E => (η x)^2 *
              ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) := by
          funext x; ring
        rw [h_eq] at h; exact h
      have h_sum_int : Integrable (fun x : E => ∑ i : Fin d, (η x)^2 *
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) volume :=
        integrable_finset_sum (Finset.univ : Finset (Fin d)) (fun i _ => h_each_int i)
      have h_eq : (fun x : E => ∑ i : Fin d, (η x)^2 *
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) =
          (fun x : E => (η x)^2 * ∑ i : Fin d,
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) := by
        funext x; rw [Finset.mul_sum]
      rw [h_eq] at h_sum_int; exact h_sum_int
    have h_rhs_int : Integrable (fun y : E =>
        Set.indicator Ω' (fun z : E => ∑ i : Fin d,
          ((fderiv ℝ u z) (EuclideanSpace.single i 1))^2) y) volume := by
      have h_partial_sq_cont : ∀ i : Fin d,
          Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
        fun i => (continuous_partial_u (d := d) hu i).pow 2
      have h_sum_cont : Continuous (fun x : E =>
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
        continuous_finset_sum _ (fun i _ => h_partial_sq_cont i)
      have h_int_clΩ' : IntegrableOn (fun x : E =>
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) (closure Ω') volume :=
        ContinuousOn.integrableOn_compact hΩ'_compact h_sum_cont.continuousOn
      have h_int_Ω' : IntegrableOn (fun x : E =>
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) Ω' volume :=
        h_int_clΩ'.mono_set subset_closure
      exact h_int_Ω'.integrable_indicator hΩ'.measurableSet
    have h_int_le := integral_mono h_lhs_int h_rhs_int h_pointwise
    refine h_int_le.trans ?_
    rw [show (fun y : E => Set.indicator Ω' (fun z : E => ∑ i : Fin d,
            ((fderiv ℝ u z) (EuclideanSpace.single i 1))^2) y) =
        Set.indicator Ω' (fun z : E => ∑ i : Fin d,
          ((fderiv ℝ u z) (EuclideanSpace.single i 1))^2) from rfl]
    rw [MeasureTheory.integral_indicator hΩ'.measurableSet]
  have h_combine :
      d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
        ∂(volume : Measure E) := by
    have h_step1 : d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) ≤
        d_real * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      refine mul_le_mul_of_nonneg_left ?_ hd_nn
      exact mul_le_mul_of_nonneg_left h_ind_bound h_M_factor_nn
    refine h_step1.trans ?_
    have h_J_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) := by
      refine integral_nonneg ?_
      intro x
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h_step2 :
        d_real * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) ≤
        d_real^2 * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      have h_factor_nn :
          0 ≤ (M^2 / (4 * (ε / d_real))) *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) :=
        mul_nonneg h_M_factor_nn h_J_nn
      have h_d_le_d_sq : d_real ≤ d_real^2 := by
        have h := h_d_real_ge_one
        nlinarith
      exact mul_le_mul_of_nonneg_right h_d_le_d_sq h_factor_nn
    refine h_step2.trans ?_
    have h_C_eq : C = d_real^2 * (M^2 / (4 * (ε / d_real))) := by
      rw [hC_def]; ring
    rw [show d_real^2 * ((M^2 / (4 * (ε / d_real))) *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E)) =
      (d_real^2 * (M^2 / (4 * (ε / d_real)))) *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) from by ring]
    rw [← h_C_eq]
  linarith

/-- Pointwise bound for one summand of `Cross_3`. Uses `2 ab ≤ a² + b²`
applied to `|∂_i u|` and `|D_h^k u|`, after extracting bounds on
`|D_h^k a^{ij}|`, `η`, `|∂_j η|`. -/
private theorem cross_3_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ}
    {η : E → ℝ}
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    (i j k : Fin d)
    {Ω' : Set E} {M : ℝ} (hM_nn : 0 ≤ M)
    (h_M : ∀ i j : Fin d, ∀ x ∈ closure Ω',
      |(fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single k 1)| ≤ M)
    {h : ℝ}
    (hh_supp_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω') (x : E) :
    |2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x| ≤
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
  classical
  by_cases hx : x ∈ tsupport η
  · have h_dq_a_bound : |diffQuot k h (fun y => B.a y i j) x| ≤ M := by
      have hCD : ContDiff ℝ 1 (fun y : E => B.a y i j) :=
        (B.contDiff_a i j).of_le (by norm_cast)
      exact abs_diffQuot_a_le_of_bound_on_set (d := d) hCD k h
        (h_M i j) ((singleton_cthick_subset (d := d) η hh_supp_in_Ω' (le_refl _) hx).trans
          subset_closure)
    have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ N := by
      have hsing_norm :
          ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ = 1 := by simp
      have h_apply :
          ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤
            ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ :=
        (fderiv ℝ η x).le_opNorm _
      rw [hsing_norm, mul_one] at h_apply
      have h2 := h_apply.trans (h_fderiv_eta x)
      rw [Real.norm_eq_abs] at h2
      exact h2
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_le : η x ≤ 1 := h_η_in.2
    have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
    have h_lhs_eq :
        |2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h u x| =
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
            |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x| := by
      rw [show (2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h u x) =
          2 * (diffQuot k h (fun y => B.a y i j) x *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h u x * η x) from by ring]
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      rw [abs_of_nonneg h_η_nn]
      ring
    rw [h_lhs_eq]
    have h_step1 :
        2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
            |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x| ≤
          2 * M * (η x) * N *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x| := by
      have h_step1a :
          2 * |diffQuot k h (fun y => B.a y i j) x| ≤ 2 * M := by
        linarith
      have h_step1b :
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) ≤ 2 * M * (η x) :=
        mul_le_mul_of_nonneg_right h_step1a h_η_nn
      have h_step1c :
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤
            2 * M * (η x) * N := by
        have h_step1c1 : 0 ≤ 2 * M * (η x) :=
          mul_nonneg (mul_nonneg (by linarith) hM_nn) h_η_nn
        calc 2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤
            2 * M * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| := by
              exact mul_le_mul_of_nonneg_right h_step1b (abs_nonneg _)
          _ ≤ 2 * M * (η x) * N :=
              mul_le_mul_of_nonneg_left h_dη_bound h_step1c1
      have h_step1c1 : 0 ≤ 2 * M * (η x) * N :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hM_nn) h_η_nn) hN_nn
      have h_intermediate : 2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
              |(fderiv ℝ u x) (EuclideanSpace.single i 1)| ≤
            2 * M * (η x) * N *
              |(fderiv ℝ u x) (EuclideanSpace.single i 1)| :=
        mul_le_mul_of_nonneg_right h_step1c (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h_intermediate (abs_nonneg _)
    refine h_step1.trans ?_
    have h_young2 : 2 *
        |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
        |diffQuot k h u x| ≤
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2 := by
      have := two_abs_mul_le_eps_sq_add ((fderiv ℝ u x) (EuclideanSpace.single i 1))
        (diffQuot k h u x) 1 zero_lt_one
      simp at this
      linarith
    have h_MN_η_nn : 0 ≤ M * (η x) * N :=
      mul_nonneg (mul_nonneg hM_nn h_η_nn) hN_nn
    have h_step2 :
        2 * M * (η x) * N *
          |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
          |diffQuot k h u x| ≤
        M * (η x) * N *
          (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) := by
      have h_eq : 2 * M * (η x) * N *
          |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
          |diffQuot k h u x| =
          M * (η x) * N *
          (2 * |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x|) := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_left h_young2 h_MN_η_nn
    refine h_step2.trans ?_
    have h_step3 :
        M * (η x) * N *
          (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) ≤
        M * N *
          (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) := by
      have h_M_η_N_le : M * (η x) * N ≤ M * 1 * N := by
        refine mul_le_mul_of_nonneg_right ?_ hN_nn
        exact mul_le_mul_of_nonneg_left h_η_le hM_nn
      have h_M_N_eq : M * 1 * N = M * N := by ring
      have h_fact_nn : 0 ≤ ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          (diffQuot k h u x)^2 := by
        exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      calc M * (η x) * N *
              (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) ≤
          M * 1 * N *
            (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) :=
            mul_le_mul_of_nonneg_right h_M_η_N_le h_fact_nn
        _ = M * N *
            (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) := by
            rw [h_M_N_eq]
    refine h_step3.trans ?_
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    ring_nf
    rfl
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    have h_lhs_zero : 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x = 0 := by
      rw [h_η_zero]; ring
    rw [h_lhs_zero, abs_zero, h_indicator]
    have h_t1 : M * N * 0 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 = 0 := by ring
    have h_t2 : M * N * 0 * (diffQuot k h u x)^2 = 0 := by ring
    linarith

/-- Continuity of the (i, j) summand of Cross_3. -/
private lemma cross_3_summand_continuous
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) := by
  have h_dq_a : Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun y : E => B.a y i j)) :=
    continuous_diffQuot_smooth (d := d) (B.contDiff_a i j) k hh
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  have h_partial_η : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single j 1)) :=
    ((hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have h_partial_u : Continuous
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    continuous_partial_u (d := d) hu i
  have h_dq_u : Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
    continuous_diffQuot_smooth (d := d) hu k hh
  exact (((((continuous_const.mul h_dq_a).mul hη.continuous).mul h_partial_η).mul
    h_partial_u).mul h_dq_u)

/-- The (i, j) summand of Cross_3 has compact support. -/
private lemma cross_3_summand_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) {η : E → ℝ} (hη_supp : HasCompactSupport η)
    (i j k : Fin d) (h : ℝ) :
    HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) := by
  have h1 : HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x)) :=
    hη_supp.mul_left
  have h2 : HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1))) :=
    h1.mul_right
  have h3 : HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
    h2.mul_right
  exact h3.mul_right

/-- Integrability of the (i, j) summand of Cross_3. -/
private lemma integrable_cross_3_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) volume :=
  (cross_3_summand_continuous (d := d) B hu hη i j k hh).integrable_of_hasCompactSupport
    (cross_3_summand_compactSupport (d := d) B u hη_supp i j k h)

set_option linter.unusedVariables false in
/-- The third cross term is bounded by `C · ‖∇u‖²_{L²(Ω')}`. -/
theorem cross_3_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x *
            (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| ≤
        C * ∫ x in Ω',
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
          ∂(volume : Measure E) := by
  classical
  obtain ⟨M, hM_nn, h_M⟩ :=
    SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact (d := d) B k hΩ'_compact
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_ge_one : 1 ≤ d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  set C : ℝ := 2 * M * N * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg ?_ hN
    exact mul_nonneg (by linarith) hM_nn
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    cross_3_pointwise_bound (d := d) B (u := u) hη_range h_fderiv_eta i j k hM_nn h_M
      h_thick_in_Ω' x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        diffQuot k h (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x
      ∂(volume : Measure E) with hS_def
  rw [abs_neg]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          diffQuot k h (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x ∂(volume : Measure E)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) volume :=
    fun i j => integrable_cross_3_summand (d := d) B hu hη hη_supp i j k hh
  have h_pt_bound1_int : ∀ i : Fin d, Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume := by
    intro i
    have h := integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i 1
    have h_partial_cont : Continuous
        (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
      continuous_partial_u (d := d) hu i
    have h_partial_sq_cont : Continuous
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
      h_partial_cont.pow 2
    have h_tsupp_meas : MeasurableSet (tsupport η) :=
      isClosed_tsupport η |>.measurableSet
    have h_tsupp_compact : IsCompact (tsupport η) := hη_supp
    have h_eq : (fun x : E => M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
        Set.indicator (tsupport η)
          (fun y : E => M * N * ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2) := by
      funext x
      by_cases hx : x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
    rw [h_eq]
    have h_inner_cont : Continuous (fun y : E =>
        M * N * ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2) :=
      continuous_const.mul h_partial_sq_cont
    exact (ContinuousOn.integrableOn_compact h_tsupp_compact h_inner_cont.continuousOn).integrable_indicator
      h_tsupp_meas
  have h_pt_bound2_int : Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_sq (d := d) hu hη_supp k hh (M * N)
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    fun i j => (h_pt_bound1_int i).add h_pt_bound2_int
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∫ x, (M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
        M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_bound :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
        ∂(volume : Measure E) := by
    have h_split_integral : ∀ i j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) =
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_pt_bound1_int i) h_pt_bound2_int]
    have h_A_factor : ∀ i : Fin d,
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) =
        M * N * ∫ x in tsupport η,
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          fun x : E => M * N * ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) from by funext x; ring]
      rw [integral_const_mul]
      congr 1
      rw [show (fun x : E => (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          (fun x : E => Set.indicator (tsupport η)
            (fun y : E => ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2) x) from by
        funext x
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
      rw [MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]
    have h_B_factor :
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) =
        M * N * ∫ x in tsupport η,
          (diffQuot k h u x)^2 ∂(volume : Measure E) :=
      integral_const_indicator_eq (d := d) k h η (M * N) (u := u)
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
          ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_split_integral i j))]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
          (∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
          ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        ∑ i : Fin d, (∑ j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) +
        ∑ i : Fin d, (∑ j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_add_distrib]]
    have h_step1 : (∑ i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E))) =
        d_real * ∑ i : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      rw [show (∑ i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E))) =
          ∑ i : Fin d, d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) from
            Finset.sum_congr rfl (fun i _ => by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])]
      rw [← Finset.mul_sum]
    have h_step2 : (∑ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        d_real^2 * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      have h_inner : ∀ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) =
            d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) := by
        intro _i
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show (∑ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
          ∑ _i : Fin d, d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) from
            Finset.sum_congr rfl (fun i _ => h_inner i)]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ← hd_real]
      ring
    rw [h_step1, h_step2]
    rw [show (∑ i : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        ∑ i : Fin d, M * N * ∫ x in tsupport η,
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_A_factor i)]
    rw [h_B_factor]
    have h_MN_nn : 0 ≤ M * N := mul_nonneg hM_nn hN
    have h_d_le_d_sq : d_real ≤ d_real^2 := by nlinarith
    have h_J_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
      integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
    have h_partial_sq_cont : ∀ i : Fin d,
        Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
      fun i => (continuous_partial_u (d := d) hu i).pow 2
    have h_int_clΩ' : ∀ i : Fin d, IntegrableOn
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) (closure Ω') volume :=
      fun i => ContinuousOn.integrableOn_compact hΩ'_compact (h_partial_sq_cont i).continuousOn
    have h_int_Ω' : ∀ i : Fin d, IntegrableOn
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) Ω' volume :=
      fun i => (h_int_clΩ' i).mono_set subset_closure
    have h_tsupp_subset_Ω' : tsupport η ⊆ Ω' :=
      fun x hx => h_thick_in_Ω' (self_subset_cthickening _ hx)
    have h_int_tsupp : ∀ i : Fin d, IntegrableOn
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) (tsupport η) volume :=
      fun i => (h_int_Ω' i).mono_set h_tsupp_subset_Ω'
    have h_part_bound : ∀ i : Fin d,
        ∫ x in tsupport η, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      refine setIntegral_mono_set (h_int_Ω' i) ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      · exact Filter.Eventually.of_forall h_tsupp_subset_Ω'
    have h_sum_part_bound :
        ∑ i : Fin d, ∫ x in tsupport η,
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
        ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      have h_sum_eq :
          ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) =
          ∑ i : Fin d, ∫ x in Ω',
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
        exact integral_finset_sum (Finset.univ : Finset (Fin d)) (fun i _ => h_int_Ω' i)
      rw [h_sum_eq]
      exact Finset.sum_le_sum (fun i _ => h_part_bound i)
    have h_diff_bound :
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) :=
      integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d) hu k hh η hΩ'
        hΩ'_compact h_thick_in_Ω'
    have h_term1 :
        d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
        d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      rw [show (d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
          (d_real * (M * N)) * (∑ i : Fin d, ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) from by
        rw [← Finset.mul_sum]; ring]
      have h_step_a : (d_real * (M * N)) * (∑ i : Fin d, ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) ≤
          (d_real * (M * N)) * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
        refine mul_le_mul_of_nonneg_left h_sum_part_bound ?_
        exact mul_nonneg hd_nn h_MN_nn
      refine h_step_a.trans ?_
      rw [show d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) =
          (d_real^2 * (M * N)) * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) from by ring]
      refine mul_le_mul_of_nonneg_right ?_ h_J_nn
      exact mul_le_mul_of_nonneg_right h_d_le_d_sq h_MN_nn
    have h_term2 :
        d_real^2 * (M * N * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
        d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left h_diff_bound h_MN_nn
    have h_sum_le : d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
        d_real^2 * (M * N * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
        2 * (d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E))) := by linarith
    refine h_sum_le.trans ?_
    have h_C_eq : C = 2 * d_real^2 * M * N := by
      rw [hC_def]; ring
    rw [show 2 * (d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E))) =
        (2 * d_real^2 * M * N) *
          ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) from by ring]
    rw [← h_C_eq]
  exact h_total_bound

/-- The pointwise FDeriv expansion of `η² · D_h^k u`:
`∂_k(η² · D_h^k u)(x) = 2 η(x) · ∂_k η(x) · D_h^k u(x) + η(x)² · D_h^k(∂_k u)(x)`. -/
private lemma fderiv_eta_sq_diffQuot_apply
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
        (EuclideanSpace.single k 1) =
      2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
        diffQuot k h u x +
      η x ^ 2 * diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x := by
  have h_apply :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.fderiv_eta_sq_times_diffQuot_apply
      (d := d) hη hu k k hh x
  exact h_apply

/-- Pointwise bound for `(∂_k(η² · D_h^k u))² ≤ 8 N² · 𝟙_{tsupport η} · (D_h^k u)² +
2 η² · (D_h^k(∂_k u))²`. -/
private lemma fderiv_eta_sq_diffQuot_sq_bound
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
        (EuclideanSpace.single k 1))^2 ≤
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 +
      2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
  rw [fderiv_eta_sq_diffQuot_apply (d := d) hu hη k hh x]
  set A : ℝ := 2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
    diffQuot k h u x with hA_def
  set B' : ℝ := η x ^ 2 * diffQuot k h
    (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x with hB'_def
  have h_AB_sq : (A + B')^2 ≤ 2 * A^2 + 2 * B'^2 := by nlinarith [sq_nonneg (A - B')]
  refine h_AB_sq.trans ?_
  have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
  have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single k 1)| ≤ N := by
    have hsing_norm :
        ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
    have h_apply :
        ‖(fderiv ℝ η x) (EuclideanSpace.single k 1)‖ ≤
          ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ :=
      (fderiv ℝ η x).le_opNorm _
    rw [hsing_norm, mul_one] at h_apply
    have h2 := h_apply.trans (h_fderiv_eta x)
    rw [Real.norm_eq_abs] at h2
    exact h2
  by_cases hx : x ∈ tsupport η
  · have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_le : η x ≤ 1 := h_η_in.2
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_sq_le_one : (η x)^2 ≤ 1 := by
      calc (η x)^2 ≤ (1 : ℝ)^2 :=
              pow_le_pow_left₀ h_η_nn h_η_le 2
        _ = 1 := one_pow _
    have h_A_sq_bound : A^2 ≤ 4 * N^2 * (diffQuot k h u x)^2 := by
      change (2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
        diffQuot k h u x)^2 ≤ _
      have h_pow_2 : (2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
            diffQuot k h u x)^2 =
          4 * (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 *
            (diffQuot k h u x)^2 := by ring
      rw [h_pow_2]
      have h_dη_sq_le : ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ N^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_dη_bound 2
      have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u x)^2 := sq_nonneg _
      have h_step1 :
          4 * (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ 4 * 1 * N^2 := by
        have h1 : (η x)^2 ≤ 1 := h_η_sq_le_one
        have h2 : ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ N^2 := h_dη_sq_le
        have h_first : (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ 1 * N^2 := by
          exact mul_le_mul h1 h2 (sq_nonneg _) (le_of_lt (by linarith [sq_nonneg (η x)]))
        nlinarith
      calc 4 * (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 *
            (diffQuot k h u x)^2 ≤
          4 * 1 * N^2 * (diffQuot k h u x)^2 :=
            mul_le_mul_of_nonneg_right h_step1 h_dq_sq_nn
        _ = 4 * N^2 * (diffQuot k h u x)^2 := by ring
    have h_first : 2 * A^2 ≤ 8 * N^2 * 1 * (diffQuot k h u x)^2 := by
      have h := mul_le_mul_of_nonneg_left h_A_sq_bound (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have h_B'_sq : B'^2 = (η x)^4 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
      change (η x ^ 2 * _)^2 = _
      ring
    have h_B'_sq_le : 2 * B'^2 ≤ 2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
      rw [h_B'_sq]
      have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
      have h_dq_sq_nn : 0 ≤ (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := sq_nonneg _
      have h_4_eq : (η x)^4 = (η x)^2 * (η x)^2 := by ring
      rw [h_4_eq]
      have h_step :
          (η x)^2 * ((η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) ≤
            (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
        have h_inner_nn : 0 ≤ ((η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) :=
          mul_nonneg h_η_sq_nn h_dq_sq_nn
        nlinarith
      nlinarith
    linarith
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    rw [h_indicator]
    have h_A_zero : A = 0 := by rw [hA_def, h_η_zero]; ring
    have h_B'_zero : B' = 0 := by rw [hB'_def, h_η_zero]; ring
    rw [h_A_zero, h_B'_zero]
    rw [h_η_zero]
    have h_t1_zero : 8 * N^2 * 0 * (diffQuot k h u x)^2 = 0 := by ring
    have h_t2_zero : 2 * (0 : ℝ)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 = 0 := by ring
    have h_lhs_zero : (0 : ℝ)^2 + 2 * (0 : ℝ)^2 = 0 := by ring
    nlinarith [sq_nonneg (diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x),
      sq_nonneg (diffQuot k h u x)]

set_option maxHeartbeats 800000 in
/-- Bound: `‖v_test‖²_{L²} ≤ 8 N² · ∫_{tsupport η} (D_h^k u)² + 2 · ∫ η² · (D_h^k(∂_k u))²`. -/
private theorem v_test_sq_int_le
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u x)^2 ∂(volume : Measure E) ≤
      8 * N^2 *
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
      2 * ∫ x, (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
        ∂(volume : Measure E) := by
  set g : E → ℝ := fun y : E => η y ^ 2 * diffQuot k h u y with hg_def
  have hg_smooth : ContDiff ℝ 1 g := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
      contDiff_diffQuot_of_contDiff (d := d) hu k hh
    exact (h1.mul h2).of_le (by norm_cast)
  have hg_supp : HasCompactSupport g := by
    have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
      have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
        funext y; ring
      rw [heq]; exact hη_supp.mul_right
    exact h_eta_sq_supp.mul_right
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_thick_int : Integrable
      (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1)) ^ 2)
      ((volume : Measure E).restrict (Metric.cthickening |-h| (Set.univ : Set E))) := by
    have h_fderiv_g_cont : Continuous (fderiv ℝ g) :=
      hg_smooth.continuous_fderiv (by norm_num)
    have h_partial_cont : Continuous (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      h_fderiv_g_cont.clm_apply continuous_const
    have h_partial_sq_cont : Continuous (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) :=
      h_partial_cont.pow 2
    have h_partial_supp : HasCompactSupport
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) hg_supp (EuclideanSpace.single k 1)
    have h_partial_sq_supp : HasCompactSupport
        (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) := by
      have : (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) =
          (fun x : ℝ => x^2) ∘ (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) := by
        funext y; rfl
      rw [this]
      exact HasCompactSupport.comp_left h_partial_supp (by simp : (0 : ℝ)^2 = 0)
    exact (h_partial_sq_cont.integrable_of_hasCompactSupport h_partial_sq_supp).integrableOn
  have h_local := integral_sq_diffQuot_le_local (d := d) hg_smooth k hnh
    MeasurableSet.univ h_thick_int
  have h_v_test_eq : (fun x : E =>
      (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u x)^2) =
      fun x : E => (diffQuot k (-h) g x)^2 := by
    funext x
    change (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u x)^2 = _
    unfold DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
    rfl
  rw [h_v_test_eq]
  have h_lhs : ∫ x, (diffQuot k (-h) g x)^2 ∂(volume : Measure E) ≤
      ∫ y, ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2 ∂(volume : Measure E) := by
    have h_lhs_restrict : ∫ x in (Set.univ : Set E),
        (diffQuot k (-h) g x)^2 ∂(volume : Measure E) =
      ∫ x, (diffQuot k (-h) g x)^2 ∂(volume : Measure E) := by
      rw [Measure.restrict_univ]
    have h_rhs_restrict : ∫ y in Metric.cthickening |-h| (Set.univ : Set E),
        ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2 ∂(volume : Measure E) =
      ∫ y, ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2 ∂(volume : Measure E) := by
      have h_eq : Metric.cthickening |-h| (Set.univ : Set E) = Set.univ := by
        ext y
        constructor
        · intro _; trivial
        · intro _
          exact Metric.self_subset_cthickening _ trivial
      rw [h_eq, Measure.restrict_univ]
    rw [← h_lhs_restrict, ← h_rhs_restrict]
    exact h_local
  refine h_lhs.trans ?_
  have h_pointwise_bound : ∀ x : E,
      ((fderiv ℝ g x) (EuclideanSpace.single k 1))^2 ≤
        8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2 +
        2 * (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
    intro x
    exact fderiv_eta_sq_diffQuot_sq_bound (d := d) hu hη hη_range h_fderiv_eta k hh x
  have h_lhs_int : Integrable (fun x : E =>
      ((fderiv ℝ g x) (EuclideanSpace.single k 1))^2) volume := by
    have h_fderiv_g_cont : Continuous (fderiv ℝ g) :=
      hg_smooth.continuous_fderiv (by norm_num)
    have h_partial_cont : Continuous (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      h_fderiv_g_cont.clm_apply continuous_const
    have h_partial_sq_cont : Continuous (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) :=
      h_partial_cont.pow 2
    have h_partial_supp : HasCompactSupport
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) hg_supp (EuclideanSpace.single k 1)
    have h_partial_sq_supp : HasCompactSupport
        (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) := by
      have : (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) =
          (fun x : ℝ => x^2) ∘ (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) := by
        funext y; rfl
      rw [this]
      exact HasCompactSupport.comp_left h_partial_supp (by simp : (0 : ℝ)^2 = 0)
    exact h_partial_sq_cont.integrable_of_hasCompactSupport h_partial_sq_supp
  have h_t1_int : Integrable (fun x : E =>
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_sq (d := d) hu hη_supp k hh (8 * N^2)
  have h_t2_int : Integrable (fun x : E =>
      2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    integrable_const_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp k k hh 2
  have h_rhs_int : Integrable (fun x : E =>
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 +
      2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    h_t1_int.add h_t2_int
  have h_int_le := integral_mono h_lhs_int h_rhs_int h_pointwise_bound
  refine h_int_le.trans ?_
  rw [integral_add h_t1_int h_t2_int]
  have h_t1_eq : ∫ x, 8 * N^2 *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2 ∂(volume : Measure E) =
    8 * N^2 * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) :=
    integral_const_indicator_eq (d := d) k h η (8 * N^2) (u := u)
  rw [h_t1_eq]
  have h_t2_eq : ∫ x, 2 * (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ∂(volume : Measure E) =
    2 * ∫ x, (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ∂(volume : Measure E) := by
    rw [show (fun x : E => 2 * (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) =
        fun x : E => 2 * ((η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) from by
        funext x; ring]
    rw [integral_const_mul]
  rw [h_t2_eq]

/-- The test function has compact support contained in the |h|-thickening of `tsupport η`,
hence in `Ω'` for `|h| ≤ 1`. -/
private lemma v_test_supported_in_Ω'
    {u : E → ℝ}
    {η : E → ℝ}
    {Ω' : Set E}
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) {h : ℝ} (hh_le : |h| ≤ R₀) :
    tsupport (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u) ⊆ Ω' :=
  (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset
    (d := d) η u k h).trans (hh_supp_in_Ω' hh_le)

/-- Continuity of `v_test` for smooth `u`, `η` and `h ≠ 0`. -/
private lemma continuous_v_test
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u) :=
  (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.contDiff_nirenbergTestFunction
    hη hu k hh).continuous

/-- Compact support of `v_test`. -/
private lemma hasCompactSupport_v_test
    {u : E → ℝ} {η : E → ℝ} (hη_supp : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    HasCompactSupport (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u) :=
  DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasCompactSupport_nirenbergTestFunction
    hη_supp k h

set_option linter.unusedVariables false in
/-- The c-term `∫_Ω c · u · v_test` is bounded by an absorbing piece plus
`C · (‖∇u‖²_{L²(Ω')} + ‖u‖²_{L²(Ω')})`. -/
theorem c_term_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |∫ x in Ω, B.c x * u x *
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E)) := by
  classical
  obtain ⟨Mc, hMc_nn, h_Mc⟩ :=
    SmoothEllipticBilinearForm.bounded_c_on_compact (d := d) B hΩ'_compact
  set C : ℝ := max (4 * ε * N^2) (Mc^2 / (2 * ε)) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε.le
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  set v_test : E → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u with hv_test_def
  have h_v_test_supp : tsupport v_test ⊆ Ω' := v_test_supported_in_Ω' hh_supp_in_Ω' k hh_le
  have h_v_test_in_Ω : tsupport v_test ⊆ Ω := fun x hx =>
    hΩ'_closure (subset_closure (h_v_test_supp hx))
  have h_v_test_cont : Continuous v_test := continuous_v_test (d := d) hu hη k hh
  have h_v_test_supp_cmp : HasCompactSupport v_test :=
    hasCompactSupport_v_test (d := d) hη_supp k h
  have h_c_cont : Continuous B.c := B.continuous_c
  have h_u_cont : Continuous u := hu.continuous
  have h_v_test_zero_outside : ∀ x ∉ Ω, v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_in_Ω hy))
  have h_int_E : ∫ x in Ω, B.c x * u x * v_test x ∂(volume : Measure E) =
      ∫ x, B.c x * u x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero : ∀ x, x ∉ Ω → B.c x * u x * v_test x = 0 := by
      intro x hx
      rw [h_v_test_zero_outside x hx]; ring
    exact setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero
  rw [h_int_E]
  have h_v_test_zero_outside_Ω' : ∀ x ∉ Ω', v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_supp hy))
  have h_int_Ω' : ∫ x, B.c x * u x * v_test x ∂(volume : Measure E) =
      ∫ x in Ω', B.c x * u x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero : ∀ x, x ∉ Ω' → B.c x * u x * v_test x = 0 := by
      intro x hx
      rw [h_v_test_zero_outside_Ω' x hx]; ring
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
  rw [h_int_Ω']
  have h_pointwise_cu_v : ∀ x : E,
      |B.c x * u x * v_test x| ≤ (ε/2) * (v_test x)^2 + (1/(2*ε)) * (B.c x * u x)^2 := by
    intro x
    have h_y := two_abs_mul_le_eps_sq_add (v_test x) (B.c x * u x) ε hε
    have h_abs_eq : |B.c x * u x * v_test x| = |v_test x| * |B.c x * u x| := by
      rw [show (B.c x * u x * v_test x) = v_test x * (B.c x * u x) from by ring,
        abs_mul]
    rw [h_abs_eq]
    have h_ε_pos_inv : (1 : ℝ) / ε > 0 := one_div_pos.mpr hε
    have h_div_eq : (1 / ε) * (B.c x * u x)^2 = 2 * ((1 / (2 * ε)) * (B.c x * u x)^2) := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      field_simp
    have h_ε_eq : ε * (v_test x)^2 = 2 * ((ε / 2) * (v_test x)^2) := by ring
    linarith [h_y, h_div_eq, h_ε_eq]
  have h_v_test_sq_int_Ω' : IntegrableOn (fun x : E => (v_test x)^2) Ω' volume := by
    have h_int : Integrable (fun x : E => (v_test x)^2) volume :=
      (h_v_test_cont.pow 2).integrable_of_hasCompactSupport
        (h_v_test_supp_cmp.comp_left (g := fun x : ℝ => x^2) (by simp : (0 : ℝ)^2 = 0))
    exact h_int.integrableOn
  have h_cu_sq_int_Ω' : IntegrableOn (fun x : E => (B.c x * u x)^2) Ω' volume := by
    have h_cont : Continuous (fun x : E => (B.c x * u x)^2) :=
      (h_c_cont.mul h_u_cont).pow 2
    have h_cont_on : ContinuousOn (fun x : E => (B.c x * u x)^2) (closure Ω') :=
      h_cont.continuousOn
    exact (ContinuousOn.integrableOn_compact hΩ'_compact h_cont_on).mono_set subset_closure
  have h_cu_v_int_Ω' : IntegrableOn (fun x : E => B.c x * u x * v_test x) Ω' volume := by
    have h_cont : Continuous (fun x : E => B.c x * u x * v_test x) :=
      (h_c_cont.mul h_u_cont).mul h_v_test_cont
    have h_supp : HasCompactSupport (fun x : E => B.c x * u x * v_test x) :=
      h_v_test_supp_cmp.mul_left
    exact (h_cont.integrable_of_hasCompactSupport h_supp).integrableOn
  have h_rhs_int_Ω' : IntegrableOn (fun x : E =>
      (ε/2) * (v_test x)^2 + (1/(2*ε)) * (B.c x * u x)^2) Ω' volume := by
    refine (h_v_test_sq_int_Ω'.const_mul (ε/2)).add (h_cu_sq_int_Ω'.const_mul (1/(2*ε)))
  have h_step1 : |∫ x in Ω', B.c x * u x * v_test x ∂(volume : Measure E)| ≤
      ∫ x in Ω', |B.c x * u x * v_test x| ∂(volume : Measure E) :=
    abs_integral_le_integral_abs (μ := (volume : Measure E).restrict Ω')
  have h_step2 : ∫ x in Ω', |B.c x * u x * v_test x| ∂(volume : Measure E) ≤
      ∫ x in Ω',
        ((ε/2) * (v_test x)^2 + (1/(2*ε)) * (B.c x * u x)^2)
        ∂(volume : Measure E) := by
    refine integral_mono_ae h_cu_v_int_Ω'.abs h_rhs_int_Ω' ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise_cu_v x
  refine (h_step1.trans h_step2).trans ?_
  rw [integral_add (h_v_test_sq_int_Ω'.const_mul (ε/2)) (h_cu_sq_int_Ω'.const_mul (1/(2*ε)))]
  rw [show (fun x : E => (ε/2) * (v_test x)^2) =
      (fun x : E => (ε/2) * (v_test x)^2) from rfl]
  rw [integral_const_mul, integral_const_mul]
  have h_v_test_sq_Ω'_le_E :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      ∫ x, (v_test x)^2 ∂(volume : Measure E) := by
    have h_int_E : Integrable (fun x : E => (v_test x)^2) volume :=
      (h_v_test_cont.pow 2).integrable_of_hasCompactSupport
        (h_v_test_supp_cmp.comp_left (g := fun x : ℝ => x^2) (by simp : (0 : ℝ)^2 = 0))
    have h_v_test_sq_eq : ∫ x, (v_test x)^2 ∂(volume : Measure E) =
        ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) := by
      have h_eq_zero : ∀ x, x ∉ Ω' → (v_test x)^2 = 0 := by
        intro x hx
        rw [h_v_test_zero_outside_Ω' x hx]; ring
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
    rw [h_v_test_sq_eq]
  have h_v_test_bound := v_test_sq_int_le (d := d) hu hη hη_supp hη_range h_fderiv_eta k hh
  have h_cu_sq_bound : ∀ x ∈ Ω', (B.c x * u x)^2 ≤ Mc^2 * (u x)^2 := by
    intro x hx
    have h_x_in_clΩ' : x ∈ closure Ω' := subset_closure hx
    have h_c_le : |B.c x| ≤ Mc := h_Mc x h_x_in_clΩ'
    have h_c_sq_le : (B.c x)^2 ≤ Mc^2 := by
      rw [← sq_abs (B.c x)]; exact pow_le_pow_left₀ (abs_nonneg _) h_c_le 2
    have h_u_sq_nn : 0 ≤ (u x)^2 := sq_nonneg _
    calc (B.c x * u x)^2 = (B.c x)^2 * (u x)^2 := by ring
      _ ≤ Mc^2 * (u x)^2 := mul_le_mul_of_nonneg_right h_c_sq_le h_u_sq_nn
  have h_cu_sq_int_Ω'_le : ∫ x in Ω', (B.c x * u x)^2 ∂(volume : Measure E) ≤
      Mc^2 * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by
    have h_u_sq_int_Ω' : IntegrableOn (fun x : E => (u x)^2) Ω' volume := by
      have h_cont : Continuous (fun x : E => (u x)^2) := h_u_cont.pow 2
      have h_cont_on : ContinuousOn (fun x : E => (u x)^2) (closure Ω') := h_cont.continuousOn
      exact (ContinuousOn.integrableOn_compact hΩ'_compact h_cont_on).mono_set subset_closure
    have h_const_int : IntegrableOn (fun x : E => Mc^2 * (u x)^2) Ω' volume :=
      h_u_sq_int_Ω'.const_mul (Mc^2)
    have h_step : ∫ x in Ω', (B.c x * u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', Mc^2 * (u x)^2 ∂(volume : Measure E) :=
      setIntegral_mono_on h_cu_sq_int_Ω' h_const_int hΩ'.measurableSet h_cu_sq_bound
    rw [integral_const_mul] at h_step
    exact h_step
  have h_v_sq_le_8N_2I :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
          ∂(volume : Measure E) :=
    h_v_test_sq_Ω'_le_E.trans h_v_test_bound
  have h_diff_bound :
      ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d) hu k hh η hΩ'
      hΩ'_compact h_thick_in_Ω'
  have h_partial_le_sum : ∀ x : E,
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ≤
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum (f := fun i => (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have h_eta_sq_partial_int : Integrable (fun x : E =>
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp k k hh
  have h_eta_sq_sum_int : Integrable (fun x : E =>
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_sum (d := d) hu hη hη_supp k hh
  have h_partial_int_le :
      ∫ x, (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
        ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) :=
    integral_mono h_eta_sq_partial_int h_eta_sq_sum_int h_partial_le_sum
  have h_gradL2_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have h_uL2_nn : 0 ≤ ∫ x in Ω', (u x)^2 ∂(volume : Measure E) :=
    integral_nonneg (fun x => sq_nonneg _)
  have h_v_full_bound :
      (ε/2) * ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      4 * ε * N^2 *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) +
      ε * ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) := by
    have h_step_a := mul_le_mul_of_nonneg_left h_v_sq_le_8N_2I (by linarith : 0 ≤ ε/2)
    have h_step_b : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
          2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) ≤
        4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) := by
      have h1 : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) =
          4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by ring
      have h2 : (ε/2) * (2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) =
          ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) := by ring
      have h_diff_pos : 0 ≤ 4 * ε * N^2 := by
        refine mul_nonneg ?_ (sq_nonneg _)
        exact mul_nonneg (by linarith) hε.le
      have h_step_c : 4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
          4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_diff_bound h_diff_pos
      have h_step_d : ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) ≤
          ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_partial_int_le hε.le
      linarith [h1, h2]
    linarith
  have h_cu_full_bound :
      (1/(2*ε)) * ∫ x in Ω', (B.c x * u x)^2 ∂(volume : Measure E) ≤
      (Mc^2 / (2 * ε)) * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by
    have h_div_pos : 0 < 1/(2*ε) := by
      refine one_div_pos.mpr ?_; linarith
    have h_step := mul_le_mul_of_nonneg_left h_cu_sq_int_Ω'_le h_div_pos.le
    have h_eq : (1 / (2 * ε)) * (Mc ^ 2 * ∫ x in Ω', u x ^ 2 ∂(volume : Measure E)) =
        Mc^2 / (2*ε) * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by
      ring
    linarith [h_step, h_eq]
  have h_C_grad_le : 4 * ε * N^2 ≤ C := le_max_left _ _
  have h_C_uL2_le : Mc^2 / (2*ε) ≤ C := le_max_right _ _
  have h_combine :
      4 * ε * N^2 *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) +
      (Mc^2 / (2 * ε)) * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) ≤
      C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E)) := by
    have h_left_le := mul_le_mul_of_nonneg_right h_C_grad_le h_gradL2_nn
    have h_right_le := mul_le_mul_of_nonneg_right h_C_uL2_le h_uL2_nn
    have h_C_dist : C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E)) =
        C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E)) +
        C * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by ring
    linarith
  linarith

set_option linter.unusedVariables false in
/-- The f-term `∫_Ω f · v_test` is bounded by an absorbing piece plus
`C · (‖∇u‖²_{L²(Ω')} + ‖f‖²_{L²(Ω')})`. -/
theorem f_term_bound
    {Ω : Set E}
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : E → ℝ}, (∀ {Ω' : Set E}, IsCompact (closure Ω') →
        MemLp f 2 (volume.restrict Ω')) →
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |∫ x in Ω, f x *
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  set C : ℝ := max (4 * ε * N^2) (1 / (2 * ε)) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε.le
  refine ⟨C, hC_nn, ?_⟩
  intro f hf_l2_loc u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  set v_test : E → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u with hv_test_def
  have h_v_test_supp : tsupport v_test ⊆ Ω' := v_test_supported_in_Ω' hh_supp_in_Ω' k hh_le
  have h_v_test_cont : Continuous v_test := continuous_v_test (d := d) hu hη k hh
  have h_v_test_supp_cmp : HasCompactSupport v_test :=
    hasCompactSupport_v_test (d := d) hη_supp k h
  have h_v_test_zero_outside : ∀ x ∉ Ω, v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (hΩ'_closure (subset_closure (h_v_test_supp hy))))
  have h_v_test_zero_outside_Ω' : ∀ x ∉ Ω', v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_supp hy))
  have hf_memLp : MemLp f 2 (volume.restrict Ω') := hf_l2_loc hΩ'_compact
  have hf_sq_int_Ω' : IntegrableOn (fun x : E => (f x)^2) Ω' volume := hf_memLp.integrable_sq
  have h_int_E : ∫ x in Ω, f x * v_test x ∂(volume : Measure E) =
      ∫ x in Ω', f x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero_Ω : ∀ x, x ∉ Ω → f x * v_test x = 0 := by
      intro x hx; rw [h_v_test_zero_outside x hx]; ring
    have h_eq_zero_Ω' : ∀ x, x ∉ Ω' → f x * v_test x = 0 := by
      intro x hx; rw [h_v_test_zero_outside_Ω' x hx]; ring
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero_Ω,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero_Ω']
  rw [h_int_E]
  have h_pointwise : ∀ x : E,
      |f x * v_test x| ≤ (ε/2) * (v_test x)^2 + (1/(2*ε)) * (f x)^2 := by
    intro x
    have h_y := two_abs_mul_le_eps_sq_add (v_test x) (f x) ε hε
    have h_abs_eq : |f x * v_test x| = |v_test x| * |f x| := by
      rw [show (f x * v_test x) = v_test x * f x from by ring, abs_mul]
    rw [h_abs_eq]
    have h_div_eq : (1 / ε) * (f x)^2 = 2 * ((1 / (2 * ε)) * (f x)^2) := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      field_simp
    have h_ε_eq : ε * (v_test x)^2 = 2 * ((ε / 2) * (v_test x)^2) := by ring
    linarith [h_y, h_div_eq, h_ε_eq]
  have h_v_test_sq_int_Ω' : IntegrableOn (fun x : E => (v_test x)^2) Ω' volume := by
    have h_int : Integrable (fun x : E => (v_test x)^2) volume :=
      (h_v_test_cont.pow 2).integrable_of_hasCompactSupport
        (h_v_test_supp_cmp.comp_left (g := fun x : ℝ => x^2) (by simp : (0 : ℝ)^2 = 0))
    exact h_int.integrableOn
  have h_f_v_int_Ω' : IntegrableOn (fun x : E => f x * v_test x) Ω' volume := by
    have h_pointwise_abs : ∀ x : E,
        |f x * v_test x| ≤ (1/2) * ((f x)^2 + (v_test x)^2) := by
      intro x
      have h_y := two_abs_mul_le_eps_sq_add (f x) (v_test x) 1 zero_lt_one
      simp only [one_mul, div_one] at h_y
      have h_abs : |f x * v_test x| = |f x| * |v_test x| := abs_mul _ _
      linarith
    have h_rhs_int : IntegrableOn (fun x : E => (1/2) * ((f x)^2 + (v_test x)^2)) Ω' volume :=
      (hf_sq_int_Ω'.add h_v_test_sq_int_Ω').const_mul (1/2)
    have h_f_AEStrong : AEStronglyMeasurable f (volume.restrict Ω') :=
      hf_memLp.aestronglyMeasurable
    have h_v_AEStrong : AEStronglyMeasurable v_test (volume.restrict Ω') :=
      h_v_test_cont.aestronglyMeasurable
    have h_prod_AEStrong : AEStronglyMeasurable (fun x : E => f x * v_test x)
        (volume.restrict Ω') := h_f_AEStrong.mul h_v_AEStrong
    refine ⟨h_prod_AEStrong, ?_⟩
    refine HasFiniteIntegral.mono' h_rhs_int.hasFiniteIntegral ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs]
    have h_pt := h_pointwise_abs x
    have h_rhs_nn : 0 ≤ (1 : ℝ) / 2 * ((f x)^2 + (v_test x)^2) :=
      mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    exact h_pt
  have h_rhs_int_Ω' : IntegrableOn (fun x : E =>
      (ε/2) * (v_test x)^2 + (1/(2*ε)) * (f x)^2) Ω' volume := by
    refine (h_v_test_sq_int_Ω'.const_mul (ε/2)).add (hf_sq_int_Ω'.const_mul (1/(2*ε)))
  have h_step1 : |∫ x in Ω', f x * v_test x ∂(volume : Measure E)| ≤
      ∫ x in Ω', |f x * v_test x| ∂(volume : Measure E) :=
    abs_integral_le_integral_abs (μ := (volume : Measure E).restrict Ω')
  have h_step2 : ∫ x in Ω', |f x * v_test x| ∂(volume : Measure E) ≤
      ∫ x in Ω', ((ε/2) * (v_test x)^2 + (1/(2*ε)) * (f x)^2) ∂(volume : Measure E) := by
    refine integral_mono_ae h_f_v_int_Ω'.abs h_rhs_int_Ω' ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise x
  refine (h_step1.trans h_step2).trans ?_
  rw [integral_add (h_v_test_sq_int_Ω'.const_mul (ε/2)) (hf_sq_int_Ω'.const_mul (1/(2*ε)))]
  rw [integral_const_mul, integral_const_mul]
  have h_v_test_sq_Ω'_le_E :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      ∫ x, (v_test x)^2 ∂(volume : Measure E) := by
    have h_v_test_sq_eq : ∫ x, (v_test x)^2 ∂(volume : Measure E) =
        ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) := by
      have h_eq_zero : ∀ x, x ∉ Ω' → (v_test x)^2 = 0 := by
        intro x hx
        rw [h_v_test_zero_outside_Ω' x hx]; ring
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
    rw [h_v_test_sq_eq]
  have h_v_test_bound := v_test_sq_int_le (d := d) hu hη hη_supp hη_range h_fderiv_eta k hh
  have h_v_sq_le_8N_2I :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
          ∂(volume : Measure E) :=
    h_v_test_sq_Ω'_le_E.trans h_v_test_bound
  have h_diff_bound :
      ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d) hu k hh η hΩ'
      hΩ'_compact h_thick_in_Ω'
  have h_partial_le_sum : ∀ x : E,
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ≤
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum (f := fun i => (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have h_eta_sq_partial_int : Integrable (fun x : E =>
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp k k hh
  have h_eta_sq_sum_int : Integrable (fun x : E =>
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_sum (d := d) hu hη hη_supp k hh
  have h_partial_int_le :
      ∫ x, (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
        ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) :=
    integral_mono h_eta_sq_partial_int h_eta_sq_sum_int h_partial_le_sum
  have h_gradL2_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have h_fL2_nn : 0 ≤ ∫ x in Ω', (f x)^2 ∂(volume : Measure E) :=
    integral_nonneg (fun x => sq_nonneg _)
  have h_v_full_bound :
      (ε/2) * ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      4 * ε * N^2 *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) +
      ε * ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) := by
    have h_step_a := mul_le_mul_of_nonneg_left h_v_sq_le_8N_2I (by linarith : 0 ≤ ε/2)
    have h_step_b : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
          2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) ≤
        4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) := by
      have h1 : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) =
          4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by ring
      have h2 : (ε/2) * (2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) =
          ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) := by ring
      have h_diff_pos : 0 ≤ 4 * ε * N^2 := by
        refine mul_nonneg ?_ (sq_nonneg _)
        exact mul_nonneg (by linarith) hε.le
      have h_step_c : 4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
          4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_diff_bound h_diff_pos
      have h_step_d : ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) ≤
          ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_partial_int_le hε.le
      linarith [h1, h2]
    linarith
  have h_C_grad_le : 4 * ε * N^2 ≤ C := le_max_left _ _
  have h_C_fL2_le : 1 / (2 * ε) ≤ C := le_max_right _ _
  have h_combine :
      4 * ε * N^2 *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) +
      (1 / (2 * ε)) * ∫ x in Ω', (f x)^2 ∂(volume : Measure E) ≤
      C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
    have h_left_le := mul_le_mul_of_nonneg_right h_C_grad_le h_gradL2_nn
    have h_right_le := mul_le_mul_of_nonneg_right h_C_fL2_le h_fL2_nn
    have h_C_dist : C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) =
        C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E)) +
        C * ∫ x in Ω', (f x)^2 ∂(volume : Measure E) := by ring
    linarith
  linarith

/-- The headline absorbing inequality: combining the master inequality
(`nirenberg_master_inequality`) with the five cross-term bounds and
choosing `ε := λ/8` so that the four absorbing pieces sum to at most
`λ/2`, we obtain
  `λ · ∫ η² ‖D_h^k ∇u‖² ≤ (λ/2) · ∫ η² ‖D_h^k ∇u‖² +
    C · (‖∇u‖²_{L²(Ω')} + ‖u‖²_{L²(Ω')} + ‖f‖²_{L²(Ω')}).` -/
theorem nirenberg_master_inequality_after_young
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u f : E → ℝ}, B.IsSmoothWeakSolution u f →
        (∀ {Ω' : Set E}, IsCompact (closure Ω') →
          MemLp f 2 (volume.restrict Ω')) →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
        ∂(volume : Measure E) ≤
        (B.lam / 2) * ∫ x, (η x)^2 *
            ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  set ε_eff : ℝ := B.lam / 8 with hε_eff_def
  have hε_eff_pos : 0 < ε_eff := by
    rw [hε_eff_def]; exact div_pos B.hlam_pos (by norm_num)
  obtain ⟨C1, hC1_nn, hC1⟩ := cross_1_bound (d := d) B hη hη_supp hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hh_supp_in_Ω' k ε_eff hε_eff_pos
  obtain ⟨C2, hC2_nn, hC2⟩ := cross_2_bound (d := d) B hη hη_supp hη_range
    hΩ' hΩ'_closure hΩ'_compact hh_supp_in_Ω' k ε_eff hε_eff_pos
  obtain ⟨C3, hC3_nn, hC3⟩ := cross_3_bound (d := d) B hη hη_supp hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hh_supp_in_Ω' k
  obtain ⟨Cc, hCc_nn, hCc⟩ := c_term_bound (d := d) B hη hη_supp hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hη_in_Ω' hh_supp_in_Ω' k ε_eff hε_eff_pos
  obtain ⟨Cf, hCf_nn, hCf⟩ := f_term_bound (d := d) hη hη_supp hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hη_in_Ω' hh_supp_in_Ω' k ε_eff hε_eff_pos
  set C : ℝ := max (C1 + C2 + C3 + Cc + Cf) (max Cc Cf) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg hC1_nn hC2_nn) hC3_nn) hCc_nn) hCf_nn
  refine ⟨C, hC_nn, ?_⟩
  intro u f h_weak hf_l2_loc h hh hh_le
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := h_weak.1
  set I : ℝ := ∫ x, (η x)^2 *
      ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
    ∂(volume : Measure E) with hI_def
  set G : ℝ := ∫ x in Ω',
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
    ∂(volume : Measure E) with hG_def
  set U : ℝ := ∫ x in Ω', (u x)^2 ∂(volume : Measure E) with hU_def
  set F : ℝ := ∫ x in Ω', (f x)^2 ∂(volume : Measure E) with hF_def
  have hI_nn : 0 ≤ I := absorbingIntegral_nonneg (d := d) k h η u
  have hG_nn : 0 ≤ G := integral_nonneg
    (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hU_nn : 0 ≤ U := integral_nonneg (fun x => sq_nonneg _)
  have hF_nn : 0 ≤ F := integral_nonneg (fun x => sq_nonneg _)
  have h_thick_in_Ω : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
    (hh_supp_in_Ω' hh_le).trans (subset_closure.trans hΩ'_closure)
  have h_master := nirenberg_master_inequality (d := d) B h_weak hη hη_supp k hh h_thick_in_Ω
  have hC1_h := hC1 hu hh hh_le
  have hC2_h := hC2 hu hh hh_le
  have hC3_h := hC3 hu hh hh_le
  have hCc_h := hCc hu hh hh_le
  have hCf_h := hCf hf_l2_loc hu hh hh_le
  have h_4ε_eq : 4 * ε_eff = B.lam / 2 := by
    rw [hε_eff_def]; ring
  have h_combine : B.lam * I ≤
      4 * ε_eff * I + (C1 + C2 + C3 + Cc + Cf) * G + Cc * U + Cf * F := by
    have h_sum_bound :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∫ x in Ω, f x *
              DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x| +
          |∫ x in Ω, B.c x * u x *
              DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x| ≤
        (ε_eff * I + C1 * G) + (ε_eff * I + C2 * G) + (C3 * G) +
          (ε_eff * I + Cf * (G + F)) + (ε_eff * I + Cc * (G + U)) := by
      have h1 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_eff * I + C1 * G := hC1_h
      have h1' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_eff * I + C1 * G := by
        rw [← abs_neg]; exact h1
      have h2 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E)| ≤ ε_eff * I + C2 * G := hC2_h
      have h2' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E)| ≤ ε_eff * I + C2 * G := by
        rw [← abs_neg]; exact h2
      have h3 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := hC3_h
      have h3' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := by
        rw [← abs_neg]; exact h3
      linarith
    refine h_master.trans (h_sum_bound.trans ?_)
    have hCc_distrib : Cc * (G + U) = Cc * G + Cc * U := by ring
    have hCf_distrib : Cf * (G + F) = Cf * G + Cf * F := by ring
    linarith [hCc_distrib, hCf_distrib]
  rw [show (4 * ε_eff * I) = (B.lam / 2) * I from by rw [h_4ε_eq]] at h_combine
  have hC_grad_le : C1 + C2 + C3 + Cc + Cf ≤ C := le_max_left _ _
  have hC_Cc_le : Cc ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_Cf_le : Cf ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have h_step1 : (C1 + C2 + C3 + Cc + Cf) * G ≤ C * G :=
    mul_le_mul_of_nonneg_right hC_grad_le hG_nn
  have h_step2 : Cc * U ≤ C * U :=
    mul_le_mul_of_nonneg_right hC_Cc_le hU_nn
  have h_step3 : Cf * F ≤ C * F :=
    mul_le_mul_of_nonneg_right hC_Cf_le hF_nn
  have h_C_dist : C * (G + U + F) = C * G + C * U + C * F := by ring
  linarith

end DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
