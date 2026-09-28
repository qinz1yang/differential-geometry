/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.DiscreteSubset

/-!
# Hurwitz limits and injectivity

Extracted from Yury Kudryashov's Riemann mapping theorem draft,
Mathlib pull request 33505. Local compatibility changes are recorded in
MODIFICATIONS.md next to this source. Upstream comments are preserved.
-/

noncomputable section

open Set Metric Function Filter
open scoped Pointwise Topology ComplexConjugate Real BigOperators Uniformity

namespace Complex

theorem _root_.AnalyticOnNhd.exists_finset_eq_prod_smul_nonzero
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {s : Set 𝕜}
    (hfs : AnalyticOnNhd 𝕜 f s) (hs_comp : IsCompact s) (hs_conn : IsPreconnected s)
    (hf₀ : ¬EqOn f 0 s) :
    ∃ (t : Finset 𝕜), (∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0) ∧
      ∃ (g : 𝕜 → E), AnalyticOnNhd 𝕜 g s ∧
        (f = fun z ↦ (∏ x ∈ t, (z - x) ^ analyticOrderNatAt f x) • g z) ∧
        (∀ z ∈ s, g z ≠ 0) := by
  have hf_top : ∀ {f : 𝕜 → E}, AnalyticOnNhd 𝕜 f s → ¬EqOn f 0 s → ∀ x ∈ s,
      analyticOrderAt f x ≠ ⊤ := by
    intro f hfs hf₀ x hx hfx
    rw [analyticOrderAt_eq_top] at hfx
    exact hf₀ <| hfs.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs_conn hx hfx
  obtain ⟨t, hts⟩ : ∃ t : Finset 𝕜, ∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0 := by
    use hs_comp.finite_sdiff_of_mem_codiscreteWithin
      hfs.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top |>.toFinset
    simp only [Finite.mem_toFinset, Set.mem_sdiff, mem_ofPred_eq, not_or, analyticOrderAt_eq_zero,
      and_congr_right_iff]
    push Not
    intro x hx
    simp [hfs _ hx, hf_top hfs hf₀ x hx]
  use t, hts
  induction t using Finset.cons_induction generalizing f with
  | empty =>
    use f, hfs
    simpa using hts
  | cons a t hat iht =>
    simp only [Finset.mem_cons] at hts
    have has : a ∈ s := (hts a).mp (.inl rfl) |>.1
    -- TODO: upgrade `AnalyticAt.analyticOrderAt_ne_top`
    obtain ⟨g, hga, hg₀, hfg⟩ : ∃ g, AnalyticOnNhd 𝕜 g s ∧ g a ≠ 0 ∧
        f = fun z ↦ (z - a) ^ analyticOrderNatAt f a • g z := by
      classical
      rcases hfs a has |>.analyticOrderAt_ne_top |>.mp
        (hf_top hfs hf₀ a has) with ⟨g, hga, hg₀, hfg⟩
      set g' := update (fun z ↦ (z - a) ^ (-analyticOrderNatAt f a : ℤ) • f z) a (g a)
      have hgg' : g =ᶠ[𝓝 a] g' := by
        refine hfg.mono fun z hz ↦ ?_
        rcases eq_or_ne z a with rfl | hza
        · simp [g']
        · simp [g', hza, hz, sub_eq_zero]
      refine ⟨g', ?_, ?_, ?_⟩
      · intro z hz
        rcases eq_or_ne z a with rfl | hza
        · exact hga.congr hgg'
        · have : g' =ᶠ[𝓝 z] fun z ↦ (z - a) ^ (-analyticOrderNatAt f a : ℤ) • f z :=
            eventually_ne_nhds hza |>.mono fun w hw ↦ by simp [g', hw]
          rw [analyticAt_congr this]
          refine .smul (.zpow ?_ (by rwa [sub_ne_zero])) (hfs z hz)
          fun_prop
      · simp [g', hg₀]
      · ext z
        rcases eq_or_ne z a with rfl | hza
        · simpa [g'] using hfg.self_of_nhds
        · simp [g', hza, sub_eq_zero]
    have hgt : ∀ z, z ∈ t ↔ z ∈ s ∧ g z = 0 := by
      rw [hfg] at hts
      intro z
      rcases eq_or_ne z a with rfl | hza
      · simp [hg₀, hat]
      · simpa [hza, sub_eq_zero] using hts z
    have hgs₀ : ¬EqOn g 0 s := by
      intro hgs₀
      exact hg₀ <| hgs₀ has
    rcases iht hga hgs₀ hgt with ⟨g', hg's, hgg', hg'₀⟩
    use g', hg's, ?_, hg'₀
    ext z
    rw [congrFun hfg, congrFun hgg', Finset.prod_cons, mul_smul]
    congr 2
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    congr 1
    -- TODO: avoid unfolding `analyticOrderNatAt` by adding lemmas
    conv_rhs => rw [hfg, analyticOrderNatAt]
    rw [← Pi.smul_def', analyticOrderAt_smul]
    · suffices analyticOrderAt (fun z ↦ (z - a) ^ analyticOrderNatAt f a) x = 0 by
        rw [this]; simp [analyticOrderNatAt]
      rw [analyticOrderAt_eq_zero]
      right
      simp [sub_eq_zero, ne_of_mem_of_not_mem hx hat]
    · fun_prop
    · exact hga _ <| ((hts _).mp <| .inr hx).1

-- TODO: replace `AnalyticOnNhd` with `AnalyticOn`?
theorem circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf₀ : ∀ z ∈ sphere c R, f z ≠ 0) (hR : 0 ≤ R) :
    ∮ z in C(c, R), logDeriv f z = (2 * π * I) * ∑ᶠ z ∈ ball c R, analyticOrderNatAt f z := by
  rcases hf.exists_finset_eq_prod_smul_nonzero (isCompact_closedBall _ _) isPreconnected_closedBall
    (fun hf₀' ↦ ((NormedSpace.sphere_nonempty (x := c)).mpr hR).elim fun x hx ↦
      hf₀ x hx <| hf₀' <| sphere_subset_closedBall hx)
    with ⟨t, htR, g, hgR, hfg, hg₀⟩
  have hne : ∀ z ∈ sphere c R, ∀ w ∈ t, z - w ≠ 0 := by
    intro z hz w hw
    rw [sub_ne_zero]
    rintro rfl
    rw [htR] at hw
    exact hf₀ _ hz hw.2
  have ht_sub : ↑t ⊆ ball c R := by
    intro w hw
    rw [Finset.mem_coe, htR, ← sphere_union_ball, mem_union] at hw
    exact hw.1.resolve_left fun hw' ↦ hf₀ w hw' hw.2
  have hleft : EqOn (logDeriv f)
      (fun z ↦ (∑ w ∈ t, analyticOrderNatAt f w / (z - w)) + logDeriv g z) (sphere c R) := by
    intro z hz
    conv_lhs => rw [hfg]
    simp only [smul_eq_mul]
    rw [logDeriv_fun_mul, logDeriv_fun_prod]
    · congr 1
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [logDeriv_fun_pow (by fun_prop), logDeriv, Pi.div_apply, deriv_sub_const, deriv_id'']
      simp [div_eq_mul_inv]
    · intro w hw
      apply pow_ne_zero
      exact hne z hz w hw
    · intros
      fun_prop
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw ↦ pow_ne_zero _ (hne z hz w hw)
    · exact hg₀ z (sphere_subset_closedBall hz)
    · fun_prop
    · exact hgR _ (sphere_subset_closedBall hz) |>.differentiableAt
  rw [finsum_mem_eq_sum_of_subset (t := t), circleIntegral.integral_congr hR hleft]
  · have hdg : AnalyticOnNhd ℂ (logDeriv g) (closedBall c R) :=
      hgR.deriv.div hgR hg₀
    have hi : ∀ w ∈ t, CircleIntegrable (fun z ↦ analyticOrderNatAt f w / (z - w)) c R := by
      intro w hw
      simp only [div_eq_mul_inv]
      refine .const_mul (circleIntegrable_sub_inv_iff.mpr <| .inr fun hw' ↦ ?_) _
      rw [abs_of_nonneg hR] at hw'
      exact hne w hw' w hw (sub_self _)
    rw [circleIntegral.integral_add, circleIntegral.integral_fun_sum,
      DiffContOnCl.circleIntegral_eq_zero hR, add_zero, Nat.cast_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty]
      · exact ht_sub hw
      · fun_prop
      · intros; fun_prop
    · exact hdg.differentiableOn.diffContOnCl_ball subset_rfl
    · exact hi
    · exact .fun_sum _ hi
    · exact hdg.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hR
  · rintro z ⟨hzc, hz⟩
    rw [mem_support, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or,
      analyticOrderAt_eq_zero, not_or, not_not, ne_eq, not_not] at hz
    replace hz := hz.1.2
    rw [hfg, smul_eq_zero, Finset.prod_eq_zero_iff] at hz
    rcases hz.resolve_right (hg₀ z <| ball_subset_closedBall hzc) with ⟨w, hwt, hzw⟩
    have hzw₀ : z = w := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzw)
    simpa only [hzw₀, Finset.mem_coe] using hwt
  · exact ht_sub

theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn {ι : Type*} {U : Set ℂ}
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hF : ∀ᶠ i in l, ∀ x ∈ U, F i x ≠ 0)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U) :
    EqOn f 0 U ∨ ∀ x ∈ U, f x ≠ 0 := by
  have hfd : DifferentiableOn ℂ f U := hf.differentiableOn hFd hUo
  rw [or_iff_not_imp_left]
  intro hf₀ c hc hfc
  rcases hfd.analyticAt (hUo.mem_nhds hc) |>.eventually_eq_zero_or_eventually_ne_zero
    with hfc₀ | hfc₀
  · exact hf₀ <| hfd.analyticOnNhd hUo |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hc hfc₀
  · obtain ⟨R, hR₀, hRU, hfR⟩ : ∃ R > 0, closedBall c R ⊆ U ∧ ∀ w ∈ sphere c R, f w ≠ 0 := by
      rw [eventually_nhdsWithin_iff] at hfc₀
      rcases Metric.nhds_basis_closedBall.eventually_iff.mp (hfc₀.and <| hUo.eventually_mem hc)
        with ⟨R, hR₀, hR⟩
      refine ⟨R, hR₀, fun w hw ↦ (hR hw).2, fun w hw ↦ (hR <| sphere_subset_closedBall hw).1 ?_⟩
      exact ne_of_mem_sphere hw hR₀.ne'
    have hRU' : sphere c R ⊆ U := sphere_subset_closedBall.trans hRU
    have hlogDeriv : TendstoUniformlyOn (fun i ↦ logDeriv (F i)) (logDeriv f) l (sphere c R) := by
      simp only [logDeriv]
      have := (hf.deriv hFd hUo).mono hRU'
      rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_sphere c R)]
      refine this.fun_div₀ (hf.mono hRU') ?_ ?_ ?_
      · exact hfd.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU'
      · exact hfd.continuousOn.mono hRU'
      · exact hfR
    have hcirc : Tendsto (fun i ↦ ∮ z in C(c, R), logDeriv (F i) z) l
        (𝓝 (∮ z in C(c, R), logDeriv f z)) := by
      apply hlogDeriv.tendsto_circleIntegral_of_continuousOn hR₀.le
      filter_upwards [hF, hFd] with i hi₀ hiD
      refine .div ?_ (hiD.continuousOn.mono hRU') ?_
      · exact hiD.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU'
      · exact fun x hx ↦ hi₀ x (hRU' hx)
    have H₀ : ∀ᶠ i in l, ∮ (z : ℂ) in C(c, R), logDeriv (F i) z = 0 := by
      filter_upwards [hF, hFd] with i hi hid
      apply DiffContOnCl.circleIntegral_eq_zero hR₀.le
      exact (hid.deriv hUo).div hid hi |>.diffContOnCl_ball hRU
    have := hcirc.congr' H₀
    rw [tendsto_const_nhds_iff, eq_comm,
      circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd, mul_eq_zero] at this
    · replace this := this.resolve_left (by simp)
      norm_cast at this
      refine ne_of_gt ?_ this
      apply finsum_cond_pos
      · simp
      · use c
        suffices ∃ᶠ (x : ℂ) in 𝓝 c, f x ≠ 0 by
          simpa [pos_iff_ne_zero, analyticOrderNatAt, analyticOrderAt_eq_zero, hfc,
            analyticOrderAt_eq_top, hfd.analyticAt (hUo.mem_nhds hc), hR₀]
        rw [eventually_nhdsWithin_iff] at hfc₀
        refine Frequently.mp ?_ hfc₀
        rw [frequently_iff_neBot, ofPred_mem_eq, ← nhdsWithin]
        infer_instance
      · have := (isCompact_closedBall c R).finite_sdiff_of_mem_codiscreteWithin
          ((hfd.analyticOnNhd hUo).mono
            hRU).codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top
        refine this.subset ?_
        simp +contextual [subset_def, analyticOrderNatAt, le_of_lt]
    · exact hfd.analyticOnNhd hUo |>.mono hRU
    · exact hfR
    · exact hR₀.le

theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn {ι : Type*} {U : Set ℂ}
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hF : ∀ᶠ i in l, InjOn (F i) U)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U) :
    (∃ C, ∀ x ∈ U, f x = C) ∨ InjOn f U := by
  rw [or_iff_not_imp_left]
  intro hfU x hx y hy hxy
  by_contra! hne
  obtain ⟨r, hr₀, hrU, hry⟩ : ∃ r > 0, ball x r ⊆ U ∧ y ∉ ball x r := by
    simp_rw [← subset_compl_singleton_iff, ← subset_inter_iff, ← Metric.mem_nhds_iff]
    simp [hUo.mem_nhds hx, hne]
  have hf_sub : TendstoLocallyUniformlyOn (fun i z ↦ F i z - F i y) (f · - f y) l (ball x r) := by
    refine (hf.mono hrU).fun_sub <|
      (Tendsto.tendstoUniformly_const ?_).tendstoUniformlyOn.tendstoLocallyUniformlyOn
    exact hf.tendsto_at hy
  refine eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn isOpen_ball isPreconnected_ball
    (hF.mono fun i hi z hz ↦ ?_) ?_ hf_sub |>.resolve_left ?_ x (by simpa) (by rwa [sub_eq_zero])
  · rw [sub_ne_zero, hi.ne_iff (hrU hz) hy]
    exact ne_of_mem_of_not_mem hz hry
  · exact hFd.mono fun i hi ↦ hi.mono hrU |>.sub_const _
  · intro heq
    refine hfU ⟨f y, ?_⟩
    refine hf.differentiableOn hFd hUo |>.analyticOnNhd hUo
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hx ?_
    exact heq.eventuallyEq_of_mem (ball_mem_nhds _ hr₀) |>.mono fun z hz ↦ sub_eq_zero.mp hz

end Complex
