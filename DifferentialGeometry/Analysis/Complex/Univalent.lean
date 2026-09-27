import DifferentialGeometry.Analysis.Complex.LocalPower
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.Inverse

section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace Complex

theorem deriv_ne_zero_of_analyticAt_of_injOn
    {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ} (hf : AnalyticAt ℂ f p)
    (hU : U ∈ 𝓝 p) (hinj : InjOn f U) : deriv f p ≠ 0 := by
  have hpU : p ∈ U := mem_of_mem_nhds hU
  have hnon : ¬ ∀ᶠ z in 𝓝 p, f z = f p := by
    intro hconst
    have heq : ∀ᶠ z in 𝓝 p, z = p := by
      filter_upwards [hU, hconst] with z hz hzf
      exact hinj hz hpU hzf
    have hne : ∀ᶠ z in 𝓝[≠] p, z ≠ p := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simpa only [mem_compl_iff, mem_singleton_iff] using hz
    obtain ⟨z, hz, he⟩ := (hne.and (heq.filter_mono nhdsWithin_le_nhds)).exists
    exact hz he
  intro hcrit
  obtain ⟨m, e, hm, hep, he0, _, _, heq⟩ :=
    exists_local_homeomorph_pow_of_analytic_deriv_eq_zero hf hnon hcrit
  obtain ⟨O, hOU, hO, hpO⟩ := _root_.mem_nhds_iff.mp hU
  let d := e.restr O
  have hsource : d.source = e.source ∩ O := e.restr_source' O hO
  have hdp : p ∈ d.source := by rw [hsource]; exact ⟨hep, hpO⟩
  have hd0 : d p = 0 := he0
  have h0target : 0 ∈ d.target := hd0 ▸ d.map_source hdp
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (d.open_target.mem_nhds h0target)
  let ζ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hm0 : m ≠ 0 := by omega
  have hζ := Complex.isPrimitiveRoot_exp m hm0
  have hζne : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hm0
  have hζpow : ζ ^ m = 1 := hζ.pow_eq_one
  let y : ℂ := (ε / 2 : ℝ)
  have hynorm : ‖y‖ = ε / 2 := by
    simp only [y, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  have hy0 : y ≠ 0 := by
    intro hy
    have hh := hynorm
    rw [hy, norm_zero] at hh
    linarith
  have hy : y ∈ d.target := hεsub (by
    rw [Metric.mem_ball, dist_zero_right, hynorm]
    linarith)
  have hζy : ζ * y ∈ d.target := hεsub (by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul, hynorm]
    linarith)
  have hxU (t : ℂ) (ht : t ∈ d.target) : d.symm t ∈ U :=
    hOU ((hsource ▸ d.map_target ht).2)
  have hvalue (t : ℂ) (ht : t ∈ d.target) : f (d.symm t) = f p + t ^ m := by
    have hs := d.map_target ht
    have hform := heq (d.symm t) ((hsource ▸ hs).1)
    change f (d.symm t) = f p + d (d.symm t) ^ m at hform
    rwa [d.right_inv ht] at hform
  have hequal : d.symm (ζ * y) = d.symm y := hinj (hxU _ hζy) (hxU _ hy) (by
    rw [hvalue _ hζy, hvalue _ hy, mul_pow, hζpow, one_mul])
  have hzyeq : ζ * y = y := by
    have hh := congrArg d hequal
    simpa only [d.right_inv hζy, d.right_inv hy] using hh
  exact hζne (mul_right_cancel₀ hy0 (hzyeq.trans (one_mul y).symm))

theorem deriv_ne_zero_of_differentiableOn_of_injOn
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {p : ℂ} (hp : p ∈ U) : deriv f p ≠ 0 :=
  deriv_ne_zero_of_analyticAt_of_injOn (hf.analyticOnNhd hU p hp) (hU.mem_nhds hp) hinj

theorem differentiableOn_symm_of_differentiableOn
    (e : OpenPartialHomeomorph ℂ ℂ) (he : DifferentiableOn ℂ e e.source) :
    DifferentiableOn ℂ e.symm e.target := by
  intro z hz
  have hsource := e.map_target hz
  have hd := (he (e.symm z) hsource).differentiableAt (e.open_source.mem_nhds hsource)
  have hne := deriv_ne_zero_of_differentiableOn_of_injOn e.open_source he e.injOn hsource
  exact (e.hasDerivAt_symm hz hne hd.hasDerivAt).differentiableAt.differentiableWithinAt

theorem isOpenMap_domRestrict_of_differentiableOn_of_injOn
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) : IsOpenMap (U.domRestrict f) := by
  apply isOpenMap_iff_nhds_le.mpr
  intro x
  have hA := hf.analyticOnNhd hU x x.property
  have hn := deriv_ne_zero_of_differentiableOn_of_injOn hU hf hinj x.property
  have hmap := (hA.hasStrictDerivAt.hasStrictFDerivAt_equiv hn).map_nhds_eq_of_equiv
  have heq : Filter.map (U.domRestrict f) (𝓝 x) = Filter.map f (𝓝 (x : ℂ)) := by
    rw [show U.domRestrict f = f ∘ (Subtype.val : U → ℂ) from rfl, ← Filter.map_map,
      map_nhds_subtype_val, hU.nhdsWithin_eq x.property]
  exact (heq.trans hmap).ge

theorem exists_openPartialHomeomorph_of_differentiableOn_of_bijOn
    {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hbij : BijOn f U V) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ e.target = V ∧
      (∀ z, e z = f z) ∧ DifferentiableOn ℂ e e.source ∧
      DifferentiableOn ℂ e.symm e.target := by
  let q := hbij.toPartialEquiv f U V
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict q hf.continuousOn
    (isOpenMap_domRestrict_of_differentiableOn_of_injOn hU hf hbij.injOn) hU
  have he : DifferentiableOn ℂ e e.source := hf
  exact ⟨e, rfl, rfl, fun _ => rfl, he, differentiableOn_symm_of_differentiableOn e he⟩

end Complex

end

end
