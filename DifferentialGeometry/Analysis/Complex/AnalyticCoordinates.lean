import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Convex.Topology
import DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism.AngularCompression
import DifferentialGeometry.Analysis.Complex.LocalPower
import Mathlib.Analysis.Complex.Conformal

section

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem eqOn_const_of_locally_analytic_coordinates
    {X : Type*} [TopologicalSpace X] {Ω : Set X} (hΩ : IsPreconnected Ω) {f : X → ℂ}
    (hcharts : ∀ p ∈ Ω, ∃ e : OpenPartialHomeomorph X ℂ,
      p ∈ e.source ∧ AnalyticOnNhd ℂ (fun z => f (e.symm z)) e.target)
    {p : X} (hp : p ∈ Ω) {c : ℂ} (hfp : ∀ᶠ x in 𝓝 p, f x = c) :
    EqOn f (fun _ => c) Ω := by
  let S := {x | ∀ᶠ y in 𝓝 x, f y = c}
  have hS : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hclose : closure S ∩ Ω ⊆ S := by
    rintro x ⟨hxcl, hxΩ⟩
    obtain ⟨e, hxe, heA⟩ := hcharts x hxΩ
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
    let U := e.source ∩ e ⁻¹' Metric.ball (e x) r
    have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
    have hxU : x ∈ U := ⟨hxe, Metric.mem_ball_self hr⟩
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.mp hxcl U hU hxU
    have heyp : e y ∈ Metric.ball (e x) r := hyU.2
    have heyt : e y ∈ e.target := e.map_source hyU.1
    have hnear : ∀ᶠ z in 𝓝 (e y), f (e.symm z) = c := by
      have hs : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
        have hh := e.symm.continuousAt heyt
        change Tendsto e.symm (𝓝 (e y)) (𝓝 (e.symm (e y))) at hh
        rwa [e.left_inv hyU.1] at hh
      exact hs.eventually hyS
    have heq : EqOn (fun z => f (e.symm z)) (fun _ => c) (Metric.ball (e x) r) :=
      (heA.mono hrsub).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (convex_ball (e x) r).isPreconnected heyp hnear
    change ∀ᶠ z in 𝓝 x, f z = c
    filter_upwards [hU.mem_nhds hxU] with z hz
    have hh := heq hz.2
    simpa only [e.left_inv hz.1] using hh
  have hsub := hΩ.subset_of_closure_inter_subset hS (show (Ω ∩ S).Nonempty from ⟨p, hp, hfp⟩)
    hclose
  exact fun x hx => (hsub hx).self_of_nhds

theorem not_eventually_const_of_locally_analytic_coordinates
    {X : Type*} [TopologicalSpace X] {Ω : Set X} (hΩ : IsPreconnected Ω) {f : X → ℂ}
    (hcharts : ∀ p ∈ Ω, ∃ e : OpenPartialHomeomorph X ℂ,
      p ∈ e.source ∧ AnalyticOnNhd ℂ (fun z => f (e.symm z)) e.target)
    (hnon : ¬ ∃ c : ℂ, EqOn f (fun _ => c) Ω) {p : X} (hp : p ∈ Ω) :
    ¬ ∀ᶠ x in 𝓝 p, f x = f p := by
  intro hlocal
  exact hnon ⟨f p, eqOn_const_of_locally_analytic_coordinates hΩ hcharts hp hlocal⟩

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis
open DifferentialGeometry.Topology

theorem exists_alternating_cross_of_analytic_critical_point
    {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hnon : ¬ ∀ᶠ z in 𝓝 p, f z = f p) (hcrit : deriv f p = 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      (0 : ℝ × ℝ) ∈ e.source ∧ e (0, 0) = p ∧
      ∃ η : ℝ, 0 < η ∧
        (∀ t : ℝ, 0 < |t| → |t| < η → (f p).re < (f (e (t, 0))).re) ∧
        ∀ t : ℝ, 0 < |t| → |t| < η → (f (e (0, t))).re < (f p).re := by
  obtain ⟨m, φ, hm, hp, hφp, _, _, hφ⟩ :=
    Complex.exists_local_homeomorph_pow_of_analytic_deriv_eq_zero hf hnon hcrit
  obtain ⟨A, hA0, hAp, hAn⟩ := exists_homeomorph_with_alternating_power_rays hm
  let e := A.toOpenPartialHomeomorph.trans φ.symm
  have h0 : (0 : ℂ) ∈ φ.target := hφp ▸ φ.map_source hp
  have he0 : (0 : ℝ × ℝ) ∈ e.source := by
    refine ⟨mem_univ _, ?_⟩
    change A 0 ∈ φ.target
    rwa [hA0]
  have hep : e (0, 0) = p := by
    change φ.symm (A 0) = p
    rw [hA0, ← hφp, φ.left_inv hp]
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (t, 0) ∈ e.source ∧ (0, t) ∈ e.source := by
    have h₁ : Continuous (fun t : ℝ => (t, (0 : ℝ))) := continuous_id.prodMk continuous_const
    have h₂ : Continuous (fun t : ℝ => ((0 : ℝ), t)) := continuous_const.prodMk continuous_id
    exact ((h₁.tendsto 0).eventually (e.open_source.mem_nhds he0)).and
      ((h₂.tendsto 0).eventually (e.open_source.mem_nhds he0))
  obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨e, he0, hep, η, hη, ?_, ?_⟩
  · intro t ht htr
    have hs := (hηsub (by simpa only [dist_zero_right, Real.norm_eq_abs] using htr)).1
    have hAt : A (t, 0) ∈ φ.target := hs.2
    have hh := hφ (φ.symm (A (t, 0))) (φ.map_target hAt)
    rw [φ.right_inv hAt] at hh
    change (f p).re < (f (φ.symm (A (t, 0)))).re
    rw [hh, Complex.add_re]
    exact lt_add_of_pos_right _ (hAp t (abs_pos.mp ht))
  · intro t ht htr
    have hs := (hηsub (by simpa only [dist_zero_right, Real.norm_eq_abs] using htr)).2
    have hAt : A (0, t) ∈ φ.target := hs.2
    have hh := hφ (φ.symm (A (0, t))) (φ.map_target hAt)
    rw [φ.right_inv hAt] at hh
    change (f (φ.symm (A (0, t)))).re < (f p).re
    rw [hh, Complex.add_re]
    exact add_lt_of_neg_right _ (hAn t (abs_pos.mp ht))

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem exists_alternating_cross_in_analytic_coordinates
    {Ω : Set ℂ} (hΩ : IsPreconnected Ω) {f : ℂ → ℂ}
    (hcharts : ∀ p ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ ℂ,
      p ∈ e.source ∧ AnalyticOnNhd ℂ (fun z => f (e.symm z)) e.target)
    (hnon : ¬ ∃ c : ℂ, EqOn f (fun _ => c) Ω)
    {p : ℂ} (hp : p ∈ Ω) (hf : DifferentiableAt ℝ f p) (hcrit : fderiv ℝ f p = 0)
    (e : OpenPartialHomeomorph ℂ ℂ) (hep : p ∈ e.source)
    (heA : AnalyticAt ℂ (fun z => f (e.symm z)) (e p))
    (hei : DifferentiableAt ℝ e.symm (e p)) :
    ∃ E : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      (0 : ℝ × ℝ) ∈ E.source ∧ E (0, 0) = p ∧
      ∃ η : ℝ, 0 < η ∧
        (∀ t : ℝ, 0 < |t| → |t| < η → (f p).re < (f (E (t, 0))).re) ∧
        ∀ t : ℝ, 0 < |t| → |t| < η → (f (E (0, t))).re < (f p).re := by
  let H := fun z => f (e.symm z)
  have hHp : H (e p) = f p := congrArg f (e.left_inv hep)
  have hnonH : ¬ ∀ᶠ z in 𝓝 (e p), H z = H (e p) := by
    intro heq
    have hne := not_eventually_const_of_locally_analytic_coordinates hΩ hcharts hnon hp
    apply hne
    have hec := e.continuousAt hep
    have hh := hec.tendsto.eventually heq
    filter_upwards [hh, e.open_source.mem_nhds hep] with z hz hze
    simpa only [H, e.left_inv hze, hHp] using hz
  have hf' : DifferentiableAt ℝ f (e.symm (e p)) := by rwa [e.left_inv hep]
  have hHd : fderiv ℝ H (e p) = 0 := by
    have hh := (hf'.hasFDerivAt.comp (e p) hei.hasFDerivAt).fderiv
    change fderiv ℝ H (e p) = _ at hh
    rw [hh, e.left_inv hep, hcrit, ContinuousLinearMap.zero_comp]
  have hHdiff : DifferentiableAt ℝ H (e p) := hf'.comp (e p) hei
  have hHcrit : deriv H (e p) = 0 := by
    rw [complexOfReal_deriv hHdiff (by rw [hHd]; simp), hHd, zero_apply]
  obtain ⟨E, hE0, hEp, η, hη, hpos, hneg⟩ :=
    exists_alternating_cross_of_analytic_critical_point heA hnonH hHcrit
  let T := E.trans e.symm
  have hT0 : (0 : ℝ × ℝ) ∈ T.source := by
    refine ⟨hE0, ?_⟩
    change E (0, 0) ∈ e.target
    rw [hEp]
    exact e.map_source hep
  have hTp : T (0, 0) = p := by
    change e.symm (E (0, 0)) = p
    rw [hEp, e.left_inv hep]
  refine ⟨T, hT0, hTp, η, hη, ?_, ?_⟩
  · intro t ht htr
    change (f p).re < (f (e.symm (E (t, 0)))).re
    simpa only [H, hHp] using hpos t ht htr
  · intro t ht htr
    change (f (e.symm (E (0, t)))).re < (f p).re
    simpa only [H, hHp] using hneg t ht htr

end DifferentialGeometry.Analysis

end

end
