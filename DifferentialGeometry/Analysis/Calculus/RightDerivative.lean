import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace DifferentialGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F]

theorem hasDerivAt_of_right
    {f f' : Real -> F} {a b t : Real} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt f (f' x) (Ici x) x)
    (ht : t ∈ Ioo a b) :
    HasDerivAt f (f' t) t := by
  let g : Real -> F := fun x => f a + intervalIntegral f' a x volume
  have hint : IntervalIntegrable f' volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le hf'
  have hgderivIcc : ∀ x ∈ Icc a b,
      HasDerivWithinAt g (f' x) (Icc a b) x := by
    intro x hxIcc
    letI : Fact (x ∈ Icc a b) := ⟨hxIcc⟩
    have hxU : x ∈ uIcc a b := by
      simpa only [uIcc_of_le hab.le] using hxIcc
    have hprim : HasDerivWithinAt
        (fun y => intervalIntegral f' a y volume) (f' x) (Icc a b) x :=
      intervalIntegral.integral_hasDerivWithinAt_right
        (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc hxU))
        (hf'.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
        (hf' x hxIcc)
    simpa only [g] using hprim.const_add (f a)
  have hgderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    exact (hgderivIcc x (mem_Icc_of_Ico hx)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx)
  have hgcont : ContinuousOn g (Icc a b) := by
    have hprim : ContinuousOn
        (fun x => intervalIntegral f' a x volume) (Icc a b) := by
      rw [← uIcc_of_le hab.le]
      exact intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff').mp hint)
    simpa only [g] using continuousOn_const.add hprim
  have hfg : ∀ x ∈ Icc a b, f x = g x := by
    apply eq_of_has_deriv_right_eq hderiv hgderiv hf hgcont
    simp only [g, intervalIntegral.integral_same, add_zero]
  have hfg_ev : f =ᶠ[nhds t] g := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with x hx
    exact hfg x hx
  have hgAt : HasDerivAt g (f' t) t := by
    have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
    exact (hgderivIcc t htIcc).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  exact hgAt.congr_of_eventuallyEq hfg_ev

theorem contDiffOn_of_right
    {v : F → F} {f : Real → F} {a b : Real} (hab : a < b)
    (hv : ContDiff Real ∞ v) (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b,
      HasDerivWithinAt f (v (f t)) (Ici t) t) :
    ContDiffOn Real ∞ f (Ioo a b) := by
  have hvcomp : ContinuousOn (fun t ↦ v (f t)) (Icc a b) :=
    hv.continuous.comp_continuousOn hf
  have hfull : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t :=
    fun t ht ↦ hasDerivAt_of_right hab hf hvcomp hderiv ht
  intro t ht
  let c : Real := (a + t) / 2
  let d : Real := (t + b) / 2
  have hct : c < t := by dsimp only [c]; linarith [ht.1]
  have htd : t < d := by dsimp only [d]; linarith [ht.2]
  have hcd : c < d := hct.trans htd
  have hsub : Icc c d ⊆ Ioo a b := by
    intro r hr
    dsimp only [c, d] at hr
    constructor
    · linarith [hr.1, ht.1]
    · linarith [hr.2, ht.2]
  have hfield : ContDiffOn Real ∞
      (Function.uncurry (fun _ : Real ↦ v))
      ((Icc c d) ×ˢ (Set.univ : Set F)) := by
    have hglobal : ContDiff Real ∞
        (Function.uncurry (fun _ : Real ↦ v)) := by
      simpa only [Function.uncurry_apply_pair] using hv.comp contDiff_snd
    exact hglobal.contDiffOn
  have hlocal : ∀ r ∈ Icc c d, HasDerivWithinAt f
      ((fun _ : Real ↦ v) r (f r)) (Icc c d) r := by
    intro r hr
    exact (hfull r (hsub hr)).hasDerivWithinAt
  have hsmooth : ContDiffOn Real ∞ f (Icc c d) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield hlocal
      (fun _ _ ↦ Set.mem_univ _)
  have htcd : t ∈ Ioo c d := ⟨hct, htd⟩
  exact ((hsmooth t (Ioo_subset_Icc_self htcd)).contDiffAt
    (Icc_mem_nhds hct htd)).contDiffWithinAt

theorem eventually_pos_of_hasDerivAt_pos
    (g : ℝ → ℝ) (ψ : ℝ) (hψ : 0 < ψ) (hg0 : g 0 = 0)
    (hg : HasDerivAt g ψ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < g t := by
  have hlim' : Tendsto (slope g 0) (𝓝[≠] 0) (𝓝 ψ) :=
    hasDerivAt_iff_tendsto_slope.mp hg
  have hmono : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 ψ) :=
    hlim'.mono_left (nhdsWithin_mono 0 (by intro x hx; exact ne_of_gt hx))
  have hsimpa : (fun t : ℝ => slope g 0 t) = fun t : ℝ => g t / t := by
    funext t
    dsimp [slope]
    rw [hg0]
    ring_nf
  have hlim : Tendsto (fun t : ℝ => g t / t) (𝓝[>] 0) (𝓝 ψ) := by
    simpa [hsimpa] using hmono
  have hψ2 : 0 < ψ / 2 := half_pos hψ
  have hψ2' : ψ / 2 < ψ := by linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ψ / 2 < g t / t :=
    hlim.eventually (lt_mem_nhds hψ2')
  filter_upwards [hev, self_mem_nhdsWithin] with t ht ht_mem
  have htpos : 0 < t := ht_mem
  have hgt : (ψ / 2) * t < g t := by
    have hmul := mul_lt_mul_of_pos_right ht htpos
    have hcancel : (g t / t) * t = g t := by
      field_simp [htpos.ne']
    nlinarith
  exact lt_of_lt_of_le (mul_pos hψ2 htpos) (le_of_lt hgt)

theorem eventually_pos_of_continuousAt_pos
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hg0 : 0 < g 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < g t := by
  have hlt : g 0 / 2 < g 0 := by linarith
  have hh : ∀ᶠ t : ℝ in 𝓝 0, g 0 / 2 < g t :=
    hg.eventually (Ioi_mem_nhds hlt)
  have hh' : ∀ᶠ t : ℝ in 𝓝[>] 0, g 0 / 2 < g t := hh.filter_mono nhdsWithin_le_nhds
  filter_upwards [hh', self_mem_nhdsWithin] with t ht _htm
  have hgt : 0 < g t := by
    have hhalf : 0 < g 0 / 2 := half_pos hg0
    exact lt_of_lt_of_le hhalf (le_of_lt ht)
  exact hgt

theorem eventually_neg_of_continuousAt_neg
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hg0 : g 0 < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, g t < 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < -g t :=
    eventually_pos_of_continuousAt_pos (fun t => -g t) hg.neg (by linarith)
  filter_upwards [hev] with t ht
  linarith

theorem eventually_le_of_continuousAt_lt
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (c : ℝ) (hgc : g 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, g t ≤ c := by
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < c - g t :=
    eventually_pos_of_continuousAt_pos (fun t => c - g t) (continuousAt_const.sub hg) (by linarith)
  filter_upwards [hev] with t ht
  linarith

theorem exists_pos_Ioo_of_eventually_nhdsWithin
    (P : ℝ → Prop) (hev : ∀ᶠ t : ℝ in 𝓝[>] 0, P t) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Ioo 0 eps → P t := by
  have hev_nhds : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Ioi 0 → P t :=
    eventually_nhdsWithin_iff.mp hev
  rcases Metric.eventually_nhds_iff.mp hev_nhds with ⟨eps, heps, hball⟩
  let eps' : ℝ := eps / 2
  refine ⟨eps', half_pos heps, ?_⟩
  intro t ht
  have htpos : 0 < t := ht.1
  have htle : t ≤ eps / 2 := by
    dsimp [eps'] at ht
    exact le_of_lt ht.2
  have htlt : t < eps := by
    have hhalf : eps / 2 < eps := half_lt_self heps
    nlinarith [htle]
  have hdist : dist t 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htlt
  exact hball hdist htpos

end DifferentialGeometry
