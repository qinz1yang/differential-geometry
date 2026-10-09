import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftRegularity

/-!
# The transverse shift of a geodesic and its Gauss lemma (S-SHIFT2)

For a point `p` of the tangent bundle and a vector field `ξ` along the geodesic `γ t = π φ_t(p)`,
the transverse shift is `α(t, h) = π φ_h(γ t, ξ t)` (`transverseShift`; it equals
`exp_{γ t}(h ξ t)` on the flow domain), and `G(t, h) = |∂ₜα|²` is its transverse speed
(`transverseSpeedSq`).

* `hasDerivAt_gauss_pairing_curve`: for a `C^r` curve `c` in the tangent bundle along which
  `|c|_g = 1`, the pairing of `∂ₕ` with `∂ₛ` of `(s, h) ↦ π φ_h(c s)` is constant in `h` (the chart
  kernel `MetricKoszul.hasDerivAt_gauss_chart` with a moving base point).
* `inner_transverseShift_gauss`: if `ξ` is a unit field orthogonal to `γ'` and `t ↦ (γ t, ξ t)` is
  differentiable at `t₀`, then `⟨∂ₕα, ∂ₜα⟩(t₀, h) = 0` for every `h`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The transverse shift `α(t, h) = π φ_h(γ t, ξ t)` of the geodesic `γ t = π φ_t(p)` along `ξ`. -/
def transverseShift {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ξ : ℝ → E) (z : ℝ × ℝ) : M :=
  (g.geodesicFlow (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M) z.2).proj

/-- The transverse speed `G(t, h) = |∂ₜ α(t, h)|²_g` of the transverse shift. -/
def transverseSpeedSq {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ξ : ℝ → E) (z : ℝ × ℝ) : ℝ :=
  g.inner (transverseShift g p ξ z)
    (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, z.2)) z.1 1)
    (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, z.2)) z.1 1)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- Translating the parameter of a curve does not change its velocity. -/
theorem mfderiv_comp_const_add_apply {f : ℝ → M} {s₀ : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f s₀) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s => f (s₀ + s)) 0 1 = mfderiv 𝓘(ℝ, ℝ) I f s₀ 1 := by
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s₀ + s) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℝ)) := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_add s₀).hasFDerivAt
    exact h.hasMFDerivAt
  have hf' : HasMFDerivAt 𝓘(ℝ, ℝ) I f (s₀ + 0) (mfderiv 𝓘(ℝ, ℝ) I f s₀) := by
    rw [add_zero]; exact hf.hasMFDerivAt
  have h := hf'.comp (0 : ℝ) hlin
  change mfderiv 𝓘(ℝ, ℝ) I (f ∘ fun s : ℝ => s₀ + s) 0 1 = _
  rw [h.mfderiv]
  change mfderiv 𝓘(ℝ, ℝ) I f s₀ (((1 : ℝ →L[ℝ] ℝ) 1) • (1 : ℝ)) = _
  rw [one_apply_eq_self, one_smul]
  rfl

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **Gauss pairing along a moving base point.** -/
theorem hasDerivAt_gauss_pairing_curve (hr : 2 ≤ r) {c : ℝ → TangentBundle I M}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r c 0) (hdom : g.geodesicFlowDomain = univ)
    (hspeed : ∀ᶠ s in 𝓝 (0 : ℝ), g.inner (c s).proj (c s).snd (c s).snd = 1) (t₀ : ℝ) :
    HasDerivAt (fun t => g.inner (g.geodesicFlow (c 0) t).proj (g.geodesicFlow (c 0) t).snd
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (g.geodesicFlow (c s) t).proj) 0 1)) 0 t₀ := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  let : DifferentialGeometry.ContinuousDualEquiv E :=
    IsCoercive.continuousDualEquivOfFiniteDimensional
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  set Φ : ℝ × ℝ → TangentBundle I M := fun p => g.geodesicFlow (c p.1) p.2 with hΦ
  have hΦc : ∀ t : ℝ, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r Φ (0, t) := by
    intro t
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r (fun p : ℝ × ℝ => c p.1) (0, t) :=
      ContMDiffAt.comp (x := ((0 : ℝ), t)) (g := c) (f := Prod.fst) hc
        (contDiff_fst.contMDiff.contMDiffAt)
    have hin : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) r
        (fun p : ℝ × ℝ => (c p.1, p.2)) (0, t) :=
      h1.prodMk (contDiff_snd.contMDiff.contMDiffAt)
    exact ((g.contMDiffOn_geodesicFlow hr1).contMDiffAt
      ((g.isOpen_geodesicFlowDomain hr1).mem_nhds (hmem _))).comp ((0 : ℝ), t) hin
  set q₀ := Φ (0, t₀) with hq₀
  set Z : ℝ × ℝ → E × E := fun p => extChartAt I.tangent q₀ (Φ p) with hZdef
  have hprojc : ContinuousAt (fun p => (Φ p).proj) ((0 : ℝ), t₀) :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).continuousAt.comp
      (hΦc t₀).continuousAt
  have hsrc : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), (Φ p).proj ∈ (chartAt H q₀.proj).source :=
    hprojc.preimage_mem_nhds
      ((chartAt H q₀.proj).open_source.mem_nhds (mem_chart_source H q₀.proj))
  have hZr : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E × E) r Z ((0 : ℝ), t₀) :=
    (contMDiffAt_extChartAt (I := I.tangent) (x := q₀)).comp ((0 : ℝ), t₀) (hΦc t₀)
  have hZ : ContDiffAt ℝ 2 Z ((0 : ℝ), t₀) :=
    (contMDiffAt_iff_contDiffAt.mp hZr).of_le (WithTop.coe_le_coe.mpr hr)
  have hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), HasDerivAt (fun t => Z (p.1, t))
      (DifferentialGeometry.MetricKoszul.metricSpray (g.chartInner q₀.proj) (Z p)) p.2 := by
    filter_upwards [hsrc] with p hp
    exact g.hasDerivAt_geodesicFlow_chart hr1 (hmem _) q₀ hp
  have hZ01 : (Z ((0 : ℝ), t₀)).1 = extChartAt I q₀.proj q₀.proj :=
    TangentBundle.extChartAt_tangent_apply_fst q₀
  have htarget : (Z ((0 : ℝ), t₀)).1 ∈ (extChartAt I q₀.proj).target := by
    rw [hZ01]
    exact mem_extChartAt_target q₀.proj
  have hB : DifferentiableAt ℝ (g.chartInner q₀.proj) (Z ((0 : ℝ), t₀)).1 :=
    ((g.contDiffOn_chartInner q₀.proj).contDiffAt
      ((isOpen_extChartAt_target q₀.proj).mem_nhds htarget)).differentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
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
  have hslice_s : Tendsto (fun s : ℝ => (s, t₀)) (𝓝 0) (𝓝 ((0 : ℝ), t₀)) :=
    (continuous_id.prodMk continuous_const).tendsto' _ _ rfl
  have hspeedZ : (fun s => g.chartInner q₀.proj (Z (s, t₀)).1 (Z (s, t₀)).2 (Z (s, t₀)).2)
      =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
    filter_upwards [hslice_s.eventually hsrc, hspeed] with s hs hs1
    rw [← hread _ hs]
    rw [g.inner_geodesicFlow_eq hr1 _ _ (hmem _)]
    exact hs1
  have hker := DifferentialGeometry.MetricKoszul.hasDerivAt_gauss_chart hZ hflow hB
    (g.isCoercive_chartInner q₀.proj htarget) (fun a b => g.chartInner_symm q₀.proj _ a b)
    hspeedZ (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  rw [zero_div] at hker
  apply hker.congr_of_eventuallyEq
  have hslice_t : Tendsto (fun t : ℝ => ((0 : ℝ), t)) (𝓝 t₀) (𝓝 ((0 : ℝ), t₀)) :=
    (continuous_const.prodMk continuous_id).tendsto' _ _ rfl
  have hZd : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), DifferentiableAt ℝ Z p :=
    (hZ.eventually (by simp)).mono fun p hp => hp.differentiableAt (by simp)
  filter_upwards [hslice_t.eventually (hsrc.and hZd)] with t ht
  obtain ⟨htsrc, htd⟩ := ht
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ (s, t)).proj) 0 := by
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ) I r (fun s : ℝ => (Φ (s, t)).proj) 0 :=
      (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp 0
        ((hΦc t).comp 0 ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt))
    exact h1.mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
  have hV := Bundle.ContMDiffRiemannianMetric.hasDerivAt_chart_comp_curve hγ htsrc
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
  change g.inner (Φ (0, t)).proj (Φ (0, t)).snd
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ (s, t)).proj) 0 1) =
    g.chartInner q₀.proj (Z (0, t)).1 (Z (0, t)).2 (fderiv ℝ Z (0, t) (1, 0)).1
  rw [g.inner_eq_chartInner htsrc, ← hVeq]
  simp only [hZdef]
  rw [h1, h2]
  rfl

/-- **Gauss lemma for the transverse shift.** -/
theorem inner_transverseShift_gauss (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {t₀ : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t₀)
    (hunit : ∀ᶠ t in 𝓝 t₀, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : g.inner (g.geodesicFlow p t₀).proj (ξ t₀) (g.geodesicFlow p t₀).snd = 0) (h : ℝ) :
    g.inner (transverseShift g p ξ (t₀, h))
      (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M) h).snd
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h)) t₀ 1) = 0 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  set V : ℝ → TangentBundle I M := fun t => ⟨(g.geodesicFlow p t).proj, ξ t⟩ with hVdef
  set c : ℝ → TangentBundle I M := fun s => V (t₀ + s) with hcdef
  have hc : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r c 0 := by
    have htr : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) r (fun s : ℝ => t₀ + s) 0 :=
      (contDiff_const.add contDiff_id).contMDiff.contMDiffAt
    have hV' : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r V (t₀ + 0) := by rwa [add_zero]
    exact hV'.comp 0 htr
  have hspeed : ∀ᶠ s in 𝓝 (0 : ℝ), g.inner (c s).proj (c s).snd (c s).snd = 1 := by
    have htend : Tendsto (fun s : ℝ => t₀ + s) (𝓝 0) (𝓝 t₀) := by
      have h : Tendsto (fun s : ℝ => t₀ + s) (𝓝 0) (𝓝 (t₀ + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rwa [add_zero] at h
    exact htend.eventually hunit
  -- the pairing is constant in `h`
  set P : ℝ → ℝ := fun h => g.inner (g.geodesicFlow (c 0) h).proj (g.geodesicFlow (c 0) h).snd
    (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (g.geodesicFlow (c s) h).proj) 0 1) with hP
  have hPd : ∀ h, HasDerivAt P 0 h := fun h => hasDerivAt_gauss_pairing_curve g hr hc hdom hspeed h
  have hconst : P h = P 0 := is_const_of_deriv_eq_zero (f := P)
    (fun h => (hPd h).differentiableAt) (fun h => (hPd h).deriv) h 0
  -- the value at `h = 0`
  have hP0 : P 0 = 0 := by
    have hfun : (fun s : ℝ => (g.geodesicFlow (c s) 0).proj) =
        fun s => (g.geodesicFlow p (t₀ + s)).proj := by
      funext s
      rw [g.geodesicFlow_zero hr1]
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun t => (g.geodesicFlow p t).proj) t₀ :=
      (g.hasMFDerivAt_geodesicFlow_proj hr1 (hmem _)).mdifferentiableAt
    have hkey : ∀ (f₁ f₂ : ℝ → M), f₁ = f₂ → ∀ (x : M) (a : E) (s : ℝ),
        g.inner x a (mfderiv 𝓘(ℝ, ℝ) I f₁ s 1) = g.inner x a (mfderiv 𝓘(ℝ, ℝ) I f₂ s 1) := by
      rintro f₁ f₂ rfl x a s
      rfl
    have hkey2 : ∀ (x : M) (a u v : E), u = v → g.inner x a u = g.inner x a v := by
      rintro x a u v rfl
      rfl
    have htr := mfderiv_comp_const_add_apply (f := fun t => (g.geodesicFlow p t).proj) hγd
    have hm := (g.hasMFDerivAt_geodesicFlow_proj hr1 (hmem (p, t₀))).mfderiv
    have hvel : mfderiv 𝓘(ℝ, ℝ) I (fun t => (g.geodesicFlow p t).proj) t₀ 1 =
        (g.geodesicFlow p t₀).snd := by
      rw [hm]
      change ((1 : ℝ →L[ℝ] ℝ) 1) • (g.geodesicFlow p t₀).snd = (g.geodesicFlow p t₀).snd
      rw [one_apply_eq_self, one_smul]
    have hbase : g.geodesicFlow (c 0) 0 = V t₀ := by
      rw [g.geodesicFlow_zero hr1, hcdef]
      change V (t₀ + 0) = V t₀
      rw [add_zero]
    calc P 0 = g.inner (g.geodesicFlow (c 0) 0).proj (g.geodesicFlow (c 0) 0).snd
          (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (g.geodesicFlow p (t₀ + s)).proj) 0 1) :=
          hkey _ _ hfun _ _ 0
      _ = g.inner (g.geodesicFlow (c 0) 0).proj (g.geodesicFlow (c 0) 0).snd
          (g.geodesicFlow p t₀).snd := hkey2 _ _ _ _ (htr.trans hvel)
      _ = 0 := by rw [hbase]; exact hperp
  -- identification with the transverse shift
  have hαd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h)) t₀ := by
    have hin : ContMDiffAt 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) r (fun s : ℝ => (V s, h)) t₀ :=
      hV.prodMk contMDiffAt_const
    have hfl := ((g.contMDiffOn_geodesicFlow hr1).contMDiffAt
      ((g.isOpen_geodesicFlowDomain hr1).mem_nhds (hmem _))).comp t₀ hin
    exact ((Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp t₀ hfl).mdifferentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
  have hid : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (g.geodesicFlow (c s) h).proj) 0 1 =
      mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h)) t₀ 1 :=
    mfderiv_comp_const_add_apply hαd
  have hc0 : c 0 = V t₀ := by simp [hcdef]
  have hfinal : P h = 0 := hconst.trans hP0
  simp only [hP] at hfinal
  rw [hc0] at hfinal
  rw [← hid]
  exact hfinal

end DifferentialGeometry.Geometry.FiniteSoul
