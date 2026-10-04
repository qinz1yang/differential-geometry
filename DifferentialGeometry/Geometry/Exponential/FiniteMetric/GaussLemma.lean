import DifferentialGeometry.Geometry.Exponential.FiniteMetric.DerivativeAtZero
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.GaussKernel

/-!
# The Gauss lemma for a finite-regularity metric

For `g` of class `C^(r+1)` with `2 ≤ r` and `v` in the domain of `exp_x`,
`g (d exp_x(v) v, d exp_x(v) w) = g_x (v, w)` (`inner_mfderiv_expMap_radial`).

Proof: the pairing `P(t) = g(∂ₜF, ∂ₛF)` of the variation `F(s, t) = exp_x(t (v + s w))` has
derivative `g_x(v, w)` (chart kernel `MetricKoszul.hasDerivAt_gauss_chart`, applied in the chart at
the current point, with the speed conservation `inner_geodesicFlow_eq`), and `P(0) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- A curve read in a chart: its derivative is the chart differential of its velocity. -/
theorem hasDerivAt_chart_comp_curve {γ : ℝ → M} {t : ℝ} {x₀ : M}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (hx : γ t ∈ (chartAt H x₀).source) :
    HasDerivAt (fun s => extChartAt I x₀ (γ s))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) t := by
  have h := TauCeti.Manifold.hasDerivAt_comp_curve (mdifferentiableAt_extChartAt hx)
    (TauCeti.Manifold.hasMFDerivAt_curveVelocity hγ)
  rw [TauCeti.Manifold.curveVelocity_apply] at h
  exact h

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The two-parameter variation `(s, t) ↦ φ(⟨x, v + s w⟩, t)` is `C^r` on its open domain. -/
theorem contMDiffAt_geodesicFlow_variation (hr : 1 ≤ r) (x : M) (v w : E) {p : ℝ × ℝ}
    (hp : ((⟨x, v + p.1 • w⟩ : TangentBundle I M), p.2) ∈ g.geodesicFlowDomain) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r
      (fun p : ℝ × ℝ => g.geodesicFlow (⟨x, v + p.1 • w⟩ : TangentBundle I M) p.2) p := by
  have hin : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => ((⟨x, v + p.1 • w⟩ : TangentBundle I M), p.2)) := by
    refine ContMDiff.prodMk ?_ ?_
    · exact (DifferentialGeometry.contMDiff_tangentFiber (I := I) x).comp
        ((contDiff_const.add (contDiff_fst.smul contDiff_const)).contMDiff)
    · exact contDiff_snd.contMDiff
  exact ((g.contMDiffOn_geodesicFlow hr).contMDiffAt
    ((g.isOpen_geodesicFlowDomain hr).mem_nhds hp)).comp p (hin p |>.of_le (by exact_mod_cast le_top))

/-- The velocity of the radial geodesic is the radial derivative of `exp_x`. -/
theorem mfderiv_expMap_smul_apply (hr : 1 ≤ r) (x : M) (v : E) {t : ℝ}
    (ht : ((⟨x, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain) :
    mfderiv 𝓘(ℝ, E) I (fun u : E => g.expMap (⟨x, u⟩ : TangentBundle I M)) (t • v) v =
      (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).snd := by
  set f : E → M := fun u => g.expMap (⟨x, u⟩ : TangentBundle I M) with hf
  have htv : (t • v : E) ∈ {u : E | (⟨x, u⟩ : TangentBundle I M) ∈ g.expDomain} :=
    (mem_expDomain_smul_iff hr).mpr ht
  have hdiff : MDifferentiableAt 𝓘(ℝ, E) I f (t • v) :=
    ((g.contMDiffOn_expMap_fiber hr x).contMDiffAt
      ((g.isOpen_expDomain_fiber hr x).mem_nhds htv)).mdifferentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr).ne')
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ : ℝ => τ • v) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
    have h := ((hasDerivAt_id t).smul_const v).hasFDerivAt
    simp only [one_smul] at h
    exact h.hasMFDerivAt
  have hcomp := mfderiv_comp_of_eq hdiff hlin.mdifferentiableAt rfl
  have hflow := g.hasMFDerivAt_geodesicFlow_proj hr ht
  have hev : (fun τ : ℝ => (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) τ).proj) =ᶠ[𝓝 t]
      f ∘ (fun τ : ℝ => τ • v) := by
    have hopen : IsOpen {τ : ℝ | ((⟨x, v⟩ : TangentBundle I M), τ) ∈ g.geodesicFlowDomain} :=
      (g.isOpen_geodesicFlowDomain hr).preimage (continuous_const.prodMk continuous_id)
    filter_upwards [hopen.mem_nhds ht] with τ hτ
    exact (g.expMap_smul_eq_proj_geodesicFlow hr x v τ hτ).symm
  have huniq := hflow.mfderiv.symm.trans (hev.mfderiv_eq.trans hcomp)
  rw [hlin.mfderiv] at huniq
  have hw := congrArg (fun L => L 1) huniq
  change ((1 : ℝ →L[ℝ] ℝ) 1) • (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).snd =
    mfderiv 𝓘(ℝ, E) I f (t • v) (((1 : ℝ →L[ℝ] ℝ) 1) • v) at hw
  simp only [one_apply_eq_self, one_smul] at hw
  exact hw.symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- The initial data of the variation depend smoothly on the parameters. -/
theorem contMDiff_variation_initial (x : M) (v w : E) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => ((⟨x, v + p.1 • w⟩ : TangentBundle I M), p.2)) := by
  refine ContMDiff.prodMk ?_ ?_
  · exact (DifferentialGeometry.contMDiff_tangentFiber (I := I) x).comp
      ((contDiff_const.add (contDiff_fst.smul contDiff_const)).contMDiff)
  · exact contDiff_snd.contMDiff

/-- **Gauss pairing.** Along the radial geodesic from `v`, the pairing of the velocity with the
variation field in the direction `w` has derivative `g_x(v, w)`. -/
theorem hasDerivAt_gauss_pairing (hr : 2 ≤ r) (x : M) (v w : E) {t₀ : ℝ}
    (ht₀ : ((⟨x, v⟩ : TangentBundle I M), t₀) ∈ g.geodesicFlowDomain) :
    HasDerivAt (fun t => g.inner (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).proj
        (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).snd
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => (g.geodesicFlow (⟨x, v + s • w⟩ : TangentBundle I M) t).proj) 0 1))
      (g.inner x v w) t₀ := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  let : DifferentialGeometry.ContinuousDualEquiv E :=
    IsCoercive.continuousDualEquivOfFiniteDimensional
  set Φ : ℝ × ℝ → TangentBundle I M :=
    fun p => g.geodesicFlow (⟨x, v + p.1 • w⟩ : TangentBundle I M) p.2 with hΦ
  have hΦ0 : ∀ t : ℝ, Φ (0, t) = g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t := by
    intro t
    simp [hΦ]
  set Ω : Set (ℝ × ℝ) :=
    {p | ((⟨x, v + p.1 • w⟩ : TangentBundle I M), p.2) ∈ g.geodesicFlowDomain} with hΩdef
  have hΩ : IsOpen Ω := (g.isOpen_geodesicFlowDomain hr1).preimage
    (contMDiff_variation_initial (I := I) x v w).continuous
  have h0Ω : ((0 : ℝ), t₀) ∈ Ω := by simpa [hΩdef] using ht₀
  have hΦc : ∀ p ∈ Ω, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r Φ p :=
    fun p hp => g.contMDiffAt_geodesicFlow_variation hr1 x v w hp
  set q₀ := Φ (0, t₀) with hq₀
  set Z : ℝ × ℝ → E × E := fun p => extChartAt I.tangent q₀ (Φ p) with hZdef
  have hprojc : ContinuousAt (fun p => (Φ p).proj) ((0 : ℝ), t₀) :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).continuousAt.comp
      (hΦc _ h0Ω).continuousAt
  have hsrc : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), p ∈ Ω ∧ (Φ p).proj ∈ (chartAt H q₀.proj).source :=
    (show ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), p ∈ Ω from hΩ.mem_nhds h0Ω).and (hprojc.preimage_mem_nhds
      ((chartAt H q₀.proj).open_source.mem_nhds (mem_chart_source H q₀.proj)))
  have hZr : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E × E) r Z ((0 : ℝ), t₀) :=
    (contMDiffAt_extChartAt (I := I.tangent) (x := q₀)).comp ((0 : ℝ), t₀) (hΦc _ h0Ω)
  have hZ : ContDiffAt ℝ 2 Z ((0 : ℝ), t₀) :=
    (contMDiffAt_iff_contDiffAt.mp hZr).of_le (WithTop.coe_le_coe.mpr hr)
  have hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), HasDerivAt (fun t => Z (p.1, t))
      (DifferentialGeometry.MetricKoszul.metricSpray (g.chartInner q₀.proj) (Z p)) p.2 := by
    filter_upwards [hsrc] with p hp
    exact g.hasDerivAt_geodesicFlow_chart hr1 hp.1 q₀ hp.2
  have hZ01 : (Z ((0 : ℝ), t₀)).1 = extChartAt I q₀.proj q₀.proj :=
    TangentBundle.extChartAt_tangent_apply_fst q₀
  have htarget : (Z ((0 : ℝ), t₀)).1 ∈ (extChartAt I q₀.proj).target := by
    rw [hZ01]
    exact mem_extChartAt_target q₀.proj
  have hB : DifferentiableAt ℝ (g.chartInner q₀.proj) (Z ((0 : ℝ), t₀)).1 :=
    ((g.contDiffOn_chartInner q₀.proj).contDiffAt
      ((isOpen_extChartAt_target q₀.proj).mem_nhds htarget)).differentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
  -- chart reading of the metric along the variation
  have hread : ∀ p, (Φ p).proj ∈ (chartAt H q₀.proj).source →
      g.inner (Φ p).proj (Φ p).snd (Φ p).snd =
        g.chartInner q₀.proj (Z p).1 (Z p).2 (Z p).2 := by
    intro p hp
    have h1 := TangentBundle.extChartAt_tangent_apply_fst q₀ (p := Φ p)
    have h2 := TangentBundle.extChartAt_tangent_apply_snd q₀ (p := Φ p) hp
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hp] at h2
    simp only [hZdef]
    rw [h1, h2]
    exact g.inner_eq_chartInner hp _ _
  -- the speed
  have hslice_s : Tendsto (fun s : ℝ => (s, t₀)) (𝓝 0) (𝓝 ((0 : ℝ), t₀)) :=
    (continuous_id.prodMk continuous_const).tendsto' _ _ rfl
  have hspeed : (fun s => g.chartInner q₀.proj (Z (s, t₀)).1 (Z (s, t₀)).2 (Z (s, t₀)).2)
      =ᶠ[𝓝 0] fun s => g.inner x (v + s • w) (v + s • w) := by
    filter_upwards [hslice_s.eventually hsrc] with s hs
    rw [← hread _ hs.2]
    exact g.inner_geodesicFlow_eq hr1 _ _ hs.1
  have hq : HasDerivAt (fun s : ℝ => g.inner x (v + s • w) (v + s • w))
      (g.inner x w v + g.inner x v w) 0 := by
    have hu : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
    have hgu : HasDerivAt (fun s : ℝ => g.inner x (v + s • w)) (g.inner x w) 0 :=
      (g.inner x : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hu
    have h := hgu.clm_apply hu
    simpa using h
  have hker := DifferentialGeometry.MetricKoszul.hasDerivAt_gauss_chart hZ hflow hB
    (g.isCoercive_chartInner q₀.proj htarget) (fun a b => g.chartInner_symm q₀.proj _ a b)
    hspeed hq
  have hval : (g.inner x w v + g.inner x v w) / 2 = g.inner x v w := by
    rw [g.symm x w v]
    ring
  rw [hval] at hker
  apply hker.congr_of_eventuallyEq
  -- identification of the chart pairing with the intrinsic one
  have hslice_t : Tendsto (fun t : ℝ => ((0 : ℝ), t)) (𝓝 t₀) (𝓝 ((0 : ℝ), t₀)) :=
    (continuous_const.prodMk continuous_id).tendsto' _ _ rfl
  have hZd : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), DifferentiableAt ℝ Z p :=
    (hZ.eventually (by simp)).mono fun p hp => hp.differentiableAt (by simp)
  filter_upwards [hslice_t.eventually (hsrc.and hZd)] with t ht
  obtain ⟨⟨htΩ, htsrc⟩, htd⟩ := ht
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ (s, t)).proj) 0 := by
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ) I r (fun s : ℝ => (Φ (s, t)).proj) 0 :=
      (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp 0
        ((hΦc _ htΩ).comp 0 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt))
    exact h1.mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
  have hV := hasDerivAt_chart_comp_curve hγ htsrc
  have hV' : HasDerivAt (fun s : ℝ => extChartAt I q₀.proj (Φ (s, t)).proj)
      (fderiv ℝ Z ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ))).1 0 := by
    have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0
      (htd.hasFDerivAt.comp_hasDerivAt 0
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) t)))
    have hfun : (fun s : ℝ => extChartAt I q₀.proj (Φ (s, t)).proj) =
        ⇑(ContinuousLinearMap.fst ℝ E E) ∘ Z ∘ fun s : ℝ => (id s, t) := by
      funext s
      exact (TangentBundle.extChartAt_tangent_apply_fst q₀ (p := Φ (s, t))).symm
    rw [hfun]
    exact h
  have hVeq := hV.unique hV'
  have h1 := TangentBundle.extChartAt_tangent_apply_fst q₀ (p := Φ ((0 : ℝ), t))
  have h2 := TangentBundle.extChartAt_tangent_apply_snd q₀ (p := Φ ((0 : ℝ), t)) htsrc
  rw [TangentBundle.continuousLinearMapAt_trivializationAt htsrc] at h2
  rw [← hΦ0 t]
  change g.inner (Φ (0, t)).proj (Φ (0, t)).snd
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ (s, t)).proj) 0 1) =
    g.chartInner q₀.proj (Z (0, t)).1 (Z (0, t)).2 (fderiv ℝ Z (0, t) (1, 0)).1
  rw [g.inner_eq_chartInner htsrc, ← hVeq]
  simp only [hZdef]
  rw [h1, h2]
  rfl

/-- **The Gauss lemma** for a finite-regularity metric: `d exp_x` at `v` is isometric on the radial
direction, `g (d exp_x(v) v, d exp_x(v) w) = g_x (v, w)`. -/
theorem inner_mfderiv_expMap_radial (hr : 2 ≤ r) (x : M) {v : E}
    (hv : (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain) (w : E) :
    g.inner (g.expMap (⟨x, v⟩ : TangentBundle I M))
        (mfderiv 𝓘(ℝ, E) I (fun u : E => g.expMap (⟨x, u⟩ : TangentBundle I M)) v v)
        (mfderiv 𝓘(ℝ, E) I (fun u : E => g.expMap (⟨x, u⟩ : TangentBundle I M)) v w) =
      g.inner x v w := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  set f : E → M := fun u => g.expMap (⟨x, u⟩ : TangentBundle I M) with hf
  set P : ℝ → ℝ := fun t => g.inner (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).proj
      (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).snd
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (g.geodesicFlow (⟨x, v + s • w⟩ : TangentBundle I M) t).proj) 0 1)
    with hP
  set J := maximalIntegralCurveInterval g.geodesicSpray (⟨x, v⟩ : TangentBundle I M)
  have hJ : ∀ t, t ∈ J ↔ ((⟨x, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain :=
    fun t => Iff.rfl
  have hderiv : ∀ t ∈ J, HasDerivAt (fun t => P t - t * g.inner x v w) 0 t := by
    intro t ht
    have h := (g.hasDerivAt_gauss_pairing hr x v w ((hJ t).mp ht)).sub
      ((hasDerivAt_id t).mul_const (g.inner x v w))
    convert h using 1
    · rfl
    · simp
  have hconst := (isOpen_maximalIntegralCurveInterval (v := g.geodesicSpray)
      (x := (⟨x, v⟩ : TangentBundle I M))).is_const_of_deriv_eq_zero
    (f := fun t => P t - t * g.inner x v w)
    isPreconnected_maximalIntegralCurveInterval
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hderiv t ht).deriv)
    ((hJ 1).mpr hv) ((hJ 0).mpr (g.mem_geodesicFlowDomain_zero hr1 _))
  -- the value at `0`
  have hP0 : P 0 = 0 := by
    have hconstfun : (fun s : ℝ => (g.geodesicFlow (⟨x, v + s • w⟩ : TangentBundle I M) 0).proj) =
        fun _ => x := by
      funext s
      rw [g.geodesicFlow_zero hr1]
    have hm : mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (g.geodesicFlow (⟨x, v + s • w⟩ : TangentBundle I M) 0).proj) 0 = 0 := by
      have h := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) x (0 : ℝ)).congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq hconstfun)
      rw [h.mfderiv]
      ext1
      rfl
    simp only [hP]
    rw [hm]
    exact map_zero _
  -- the value at `1`
  have hvel : (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) 1).snd = mfderiv 𝓘(ℝ, E) I f v v := by
    have h := g.mfderiv_expMap_smul_apply hr1 x v hv
    have key : ∀ y : E, y = v → mfderiv 𝓘(ℝ, E) I f y v =
        (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) 1).snd →
        mfderiv 𝓘(ℝ, E) I f v v = (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) 1).snd := by
      rintro y rfl h
      exact h
    exact (key _ (one_smul ℝ v) h).symm
  have hvar : mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => (g.geodesicFlow (⟨x, v + s • w⟩ : TangentBundle I M) 1).proj) 0 1 =
      mfderiv 𝓘(ℝ, E) I f v w := by
    have hvdom : v ∈ {u : E | (⟨x, u⟩ : TangentBundle I M) ∈ g.expDomain} := hv
    have hdiff : MDifferentiableAt 𝓘(ℝ, E) I f v :=
      ((g.contMDiffOn_expMap_fiber hr1 x).contMDiffAt
        ((g.isOpen_expDomain_fiber hr1 x).mem_nhds hvdom)).mdifferentiableAt
        (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
    have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => v + s • w) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
      have h := (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v).hasFDerivAt
      simp only [one_smul] at h
      exact h.hasMFDerivAt
    have hcomp := mfderiv_comp_of_eq hdiff hlin.mdifferentiableAt (by simp)
    have hfun : (fun s : ℝ => (g.geodesicFlow (⟨x, v + s • w⟩ : TangentBundle I M) 1).proj) =
        f ∘ fun s : ℝ => v + s • w := rfl
    rw [hfun, hcomp, hlin.mfderiv]
    have key : ∀ y : E, y = v →
        ((mfderiv 𝓘(ℝ, E) I f y).comp ((1 : ℝ →L[ℝ] ℝ).smulRight w)) 1 =
          mfderiv 𝓘(ℝ, E) I f v w := by
      rintro y rfl
      change mfderiv 𝓘(ℝ, E) I f y (((1 : ℝ →L[ℝ] ℝ) 1) • w) = _
      rw [one_apply_eq_self, one_smul]
    exact key _ (by simp)
  have hP1 : P 1 = g.inner (g.expMap (⟨x, v⟩ : TangentBundle I M))
      (mfderiv 𝓘(ℝ, E) I f v v) (mfderiv 𝓘(ℝ, E) I f v w) := by
    simp only [hP]
    rw [hvar, hvel]
    rfl
  simp only [hP0, zero_mul, sub_zero, one_mul] at hconst
  rw [← hP1]
  linarith

end Bundle.ContMDiffRiemannianMetric
