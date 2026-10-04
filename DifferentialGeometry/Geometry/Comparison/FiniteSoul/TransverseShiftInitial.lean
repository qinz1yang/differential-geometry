import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftJacobi
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.TransverseSpeedKernel

/-!
# Initial values of the transverse speed (S-SHIFT2)

Along the geodesic itself (`h = 0`) the transverse speed is `G(t, 0) = |γ'|² = 1`
(`transverseSpeedSq_zero`), and it is stationary: `∂ₕG(t, 0) = 0` (`hasDerivAt_transverseSpeedSq_zero`)
because `ξ ⊥ γ'` and `γ` is a geodesic (chart kernel `MetricKoszul.hasDerivAt_transverse_speed_chart`).
Hence `j = √G(t, ·)` has `j(0) = 1`, `j'(0) = 0` (`deriv_sqrt_transverseSpeedSq_zero`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- Chart reading of the partial velocities of a differentiable two-parameter map. -/
theorem fderiv_chart_comp_slice {F : ℝ × ℝ → M} {z : ℝ × ℝ} {x₀ : M}
    (hF : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I F z) (hz : F z ∈ (chartAt H x₀).source) :
    fderiv ℝ (fun w => extChartAt I x₀ (F w)) z ((1 : ℝ), (0 : ℝ)) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (F z)
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => F (s, z.2)) z.1 1) ∧
    fderiv ℝ (fun w => extChartAt I x₀ (F w)) z ((0 : ℝ), (1 : ℝ)) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (F z)
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => F (z.1, s)) z.2 1) := by
  have hzs : F z ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hY : DifferentiableAt ℝ (fun w => extChartAt I x₀ (F w)) z := by
    have h := (mdifferentiableAt_extChartAt hz).comp z hF
    exact mdifferentiableAt_iff_differentiableAt.mp h
  have hs1 : HasDerivAt (fun s : ℝ => (s, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have hs2 : HasDerivAt (fun s : ℝ => (z.1, s)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hγ1 : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s => F (s, z.2)) z.1 :=
    hF.comp z.1 hs1.differentiableAt.mdifferentiableAt
  have hγ2 : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s => F (z.1, s)) z.2 :=
    hF.comp z.2 hs2.differentiableAt.mdifferentiableAt
  constructor
  · have h1 := hY.hasFDerivAt.comp_hasDerivAt z.1 hs1
    have h2 := Bundle.ContMDiffRiemannianMetric.hasDerivAt_chart_comp_curve hγ1 hz
    exact h1.unique h2
  · have h1 := hY.hasFDerivAt.comp_hasDerivAt z.2 hs2
    have h2 := Bundle.ContMDiffRiemannianMetric.hasDerivAt_chart_comp_curve hγ2 hz
    exact h1.unique h2

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

omit [T2Space M] in
/-- Along `h = 0` the transverse shift is the geodesic. -/
theorem transverseShift_zero (hr : 1 ≤ r) (p : TangentBundle I M) (ξ : ℝ → E) :
    (fun s => transverseShift g p ξ (s, 0)) = fun s => (g.geodesicFlow p s).proj := by
  funext s
  simp only [transverseShift]
  rw [g.geodesicFlow_zero hr]

/-- **`G(t, 0) = 1`.** -/
theorem transverseSpeedSq_zero (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) (hp : g.inner p.proj p.snd p.snd = 1) (ξ : ℝ → E) (t : ℝ) :
    transverseSpeedSq g p ξ (t, 0) = 1 := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have hm := (g.hasMFDerivAt_geodesicFlow_proj hr (hmem (p, t))).mfderiv
  have hvel : @Eq E (mfderiv 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) t 1)
      (g.geodesicFlow p t).snd := by
    rw [hm]
    change ((1 : ℝ →L[ℝ] ℝ) 1) • (g.geodesicFlow p t).snd = (g.geodesicFlow p t).snd
    rw [one_apply_eq_self, one_smul]
  have hkey : ∀ (f₁ f₂ : ℝ → M), f₁ = f₂ → ∀ (x : M) (s : ℝ),
      g.inner x (mfderiv 𝓘(ℝ, ℝ) I f₁ s 1) (mfderiv 𝓘(ℝ, ℝ) I f₁ s 1) =
        g.inner x (mfderiv 𝓘(ℝ, ℝ) I f₂ s 1) (mfderiv 𝓘(ℝ, ℝ) I f₂ s 1) := by
    rintro f₁ f₂ rfl x s
    rfl
  have hkey2 : ∀ (x x' : M) (u v : E), x = x' → u = v → g.inner x u u = g.inner x' v v := by
    rintro x x' u v rfl rfl
    rfl
  have hpt : transverseShift g p ξ (t, 0) = (g.geodesicFlow p t).proj :=
    congrFun (transverseShift_zero g hr p ξ) t
  calc transverseSpeedSq g p ξ (t, 0)
      = g.inner (transverseShift g p ξ (t, 0))
          (mfderiv 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) t 1)
          (mfderiv 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) t 1) :=
        hkey _ _ (transverseShift_zero g hr p ξ) _ t
    _ = g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd (g.geodesicFlow p t).snd :=
        hkey2 _ _ _ _ hpt hvel
    _ = 1 := by rw [g.inner_geodesicFlow_eq hr p t (hmem _), hp]

/-- **`∂ₕG(t₀, 0) = 0`.** -/
theorem hasDerivAt_transverseSpeedSq_zero (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    HasDerivAt (fun h => transverseSpeedSq g p ξ (t₀, h)) 0 0 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  let : DifferentialGeometry.ContinuousDualEquiv E :=
    IsCoercive.continuousDualEquivOfFiniteDimensional
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have hpt : ∀ t, transverseShift g p ξ (t, 0) = (g.geodesicFlow p t).proj := fun t =>
    congrFun (transverseShift_zero g hr1 p ξ) t
  have hαc : ∀ z : ℝ × ℝ, z.1 ∈ J → ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I r (transverseShift g p ξ) z :=
    fun z hz => contMDiffAt_transverseShift g hr1 hdom p (hV z.1 hz)
  have hαd : ∀ z : ℝ × ℝ, z.1 ∈ J → MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (transverseShift g p ξ) z :=
    fun z hz => (hαc z hz).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
  set q := g.geodesicFlow p t₀ with hq
  set x₀ := q.proj with hx₀
  set Y : ℝ × ℝ → E := fun w => extChartAt I x₀ (transverseShift g p ξ w) with hYdef
  set B := g.chartInner x₀ with hBdef
  have hx₀src : transverseShift g p ξ (t₀, 0) ∈ (chartAt H x₀).source := by
    rw [hpt]; exact mem_chart_source H x₀
  have hYc : ContDiffAt ℝ 2 Y (t₀, 0) := by
    have h := (contMDiffAt_extChartAt' (I := I) (n := r) hx₀src).comp ((t₀, 0) : ℝ × ℝ)
      (hαc (t₀, 0) ht₀)
    exact (contMDiffAt_iff_contDiffAt.mp h).of_le (WithTop.coe_le_coe.mpr hr)
  -- the times near `t₀` where everything is read in the chart
  have hγc : ContinuousAt (fun t => (g.geodesicFlow p t).proj) t₀ :=
    (g.hasMFDerivAt_geodesicFlow_proj hr1 (hmem _)).continuousAt
  have hS : ∀ᶠ t in 𝓝 t₀, t ∈ J ∧ (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source :=
    (show ∀ᶠ t in 𝓝 t₀, t ∈ J from hJ.mem_nhds ht₀).and (hγc.preimage_mem_nhds
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)))
  have hDc : ∀ (x x' : M) (u u' : E), x = x' → u = u' →
      mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x u = mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x' u' := by
    rintro x x' u u' rfl rfl
    rfl
  have hvel : ∀ t, @Eq E (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, 0)) t 1)
      (g.geodesicFlow p t).snd := by
    intro t
    rw [transverseShift_zero g hr1 p ξ, (g.hasMFDerivAt_geodesicFlow_proj hr1 (hmem _)).mfderiv]
    change ((1 : ℝ →L[ℝ] ℝ) 1) • (g.geodesicFlow p t).snd = (g.geodesicFlow p t).snd
    rw [one_apply_eq_self, one_smul]
  have heq : ∀ t, t ∈ J ∧ (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source →
      (Y (t, 0), fderiv ℝ Y (t, 0) ((1 : ℝ), (0 : ℝ))) =
        extChartAt I.tangent q (g.geodesicFlow p t) := by
    intro t ht
    have hsrc : transverseShift g p ξ (t, 0) ∈ (chartAt H x₀).source := by rw [hpt]; exact ht.2
    have hsl := (fderiv_chart_comp_slice (hαd (t, 0) ht.1) hsrc).1
    refine Prod.ext ?_ ?_
    · rw [TangentBundle.extChartAt_tangent_apply_fst q]
      simp only [hYdef]
      rw [hpt]
    · rw [TangentBundle.extChartAt_tangent_apply_snd q ht.2,
        TangentBundle.continuousLinearMapAt_trivializationAt ht.2]
      exact hsl.trans (hDc _ _ _ _ (hpt t) (hvel t))
  have hgeo : HasDerivAt (fun t => (Y (t, 0), fderiv ℝ Y (t, 0) ((1 : ℝ), (0 : ℝ))))
      (DifferentialGeometry.MetricKoszul.metricSpray B
        (Y (t₀, 0), fderiv ℝ Y (t₀, 0) ((1 : ℝ), (0 : ℝ)))) t₀ := by
    have h := g.hasDerivAt_geodesicFlow_chart hr1 (hmem (p, t₀)) q (mem_chart_source H x₀)
    rw [← heq t₀ hS.self_of_nhds] at h
    exact h.congr_of_eventuallyEq (hS.mono fun t ht => heq t ht)
  have hperp' : ∀ᶠ t in 𝓝 t₀, B (Y (t, 0)) (fderiv ℝ Y (t, 0) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ Y (t, 0) ((0 : ℝ), (1 : ℝ))) = 0 := by
    filter_upwards [hS] with t ht
    have hsrc : transverseShift g p ξ (t, 0) ∈ (chartAt H x₀).source := by rw [hpt]; exact ht.2
    obtain ⟨h1, h2⟩ := fderiv_chart_comp_slice (hαd (t, 0) ht.1) hsrc
    have hξ : @Eq E (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ ((t, 0).1, s)) (t, 0).2 1)
        (ξ t) := by
      refine (mfderiv_transverseShift_snd g hr1 hdom p ξ (t, 0)).trans ?_
      change (g.geodesicFlow (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M) 0).snd = ξ t
      rw [g.geodesicFlow_zero hr1]
    rw [h1, h2, hDc _ _ _ _ (hpt t) (hvel t), hDc _ _ _ _ (hpt t) hξ]
    have hY0 : Y (t, 0) = extChartAt I x₀ (g.geodesicFlow p t).proj := by
      simp only [hYdef]; rw [hpt]
    rw [hY0]
    exact (g.inner_eq_chartInner ht.2 _ _).symm.trans ((g.symm _ _ _).trans (hperp t ht.1))
  have hy₀ : Y (t₀, 0) ∈ (extChartAt I x₀).target := by
    simp only [hYdef]; rw [hpt]; exact mem_extChartAt_target x₀
  have hB : DifferentiableAt ℝ B (Y (t₀, 0)) :=
    ((g.contDiffOn_chartInner x₀).contDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds hy₀)).differentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
  have hker := DifferentialGeometry.MetricKoszul.hasDerivAt_transverse_speed_chart hYc hgeo
    hperp' hB (g.isCoercive_chartInner x₀ hy₀) (fun v w => g.chartInner_symm x₀ _ v w)
  -- identification with `G(t₀, ·)` near `h = 0`
  apply hker.congr_of_eventuallyEq
  have hαh : ContinuousAt (fun h : ℝ => transverseShift g p ξ (t₀, h)) 0 :=
    (hαc (t₀, 0) ht₀).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [hαh.preimage_mem_nhds ((chartAt H x₀).open_source.mem_nhds hx₀src)] with h hh
  have h1 := (fderiv_chart_comp_slice (hαd (t₀, h) ht₀) hh).1
  change g.inner (transverseShift g p ξ (t₀, h))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h)) t₀ 1)
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h)) t₀ 1) = _
  rw [g.inner_eq_chartInner hh, ← h1]

/-- **`j(0) = 1` and `j'(0) = 0`** for `j = √G(t₀, ·)`. -/
theorem deriv_sqrt_transverseSpeedSq_zero (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) (hp : g.inner p.proj p.snd p.snd = 1) {ξ : ℝ → E} {J : Set ℝ}
    (hJ : IsOpen J)
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    Real.sqrt (transverseSpeedSq g p ξ (t₀, 0)) = 1 ∧
      deriv (fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h))) 0 = 0 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have h0 := transverseSpeedSq_zero g hr1 hdom p hp ξ t₀
  refine ⟨by rw [h0, Real.sqrt_one], ?_⟩
  have hd := (hasDerivAt_transverseSpeedSq_zero g hr hdom p hJ hV hperp ht₀).sqrt
    (by rw [h0]; norm_num)
  rw [hd.deriv]
  simp

end DifferentialGeometry.Geometry.FiniteSoul
