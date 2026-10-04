import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SegmentKernel

/-!
# Short metric segments are radial geodesics (CM1.e)

A unit-speed metric segment `c` from `x` of length `ℓ < ρ` inside a normal chart `e` of radius `ρ`
is `t ↦ exp_x (t • u)` with `|u|_{g_x} = 1` (`eq_expMap_of_short_segment`). Key step
(`hasDerivAt_expChart_symm_segment`): `w = e.symm ∘ c` satisfies `w' = w / τ`, by the direction
kernel `hasDerivAt_of_quadratic_radial` read in a normal chart at `c τ` and the Gauss lemma.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  {r : ℕ∞} (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- Along a short unit-speed segment, `w = e.symm ∘ c` satisfies `w'(τ) = w(τ) / τ`. -/
theorem hasDerivAt_expChart_symm_segment (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {x : M} {ρ : ℝ} (e : OpenPartialHomeomorph E M)
    (he : e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
      (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
      ContMDiffOn 𝓘(ℝ, E) I r e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target ∧
      ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v))
    {c : ℝ → M} {ℓ : ℝ} (hℓρ : ℓ < ρ) (hc0 : c 0 = x)
    (hseg : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) {τ : ℝ}
    (hτ : τ ∈ Ioo 0 ℓ) :
    HasDerivAt (fun s => e.symm (c s)) (τ⁻¹ • e.symm (c τ)) τ := by
  obtain ⟨-, htgt, hexp, -, hsymm, hdist⟩ := he
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr1).ne'
  have hℓ : 0 ≤ ℓ := hτ.1.le.trans hτ.2.le
  have hdx : ∀ s ∈ Icc 0 ℓ, dist x (c s) = s := by
    intro s hs
    rw [← hc0, hseg 0 ⟨le_rfl, hℓ⟩ s hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
  have hct : ∀ s ∈ Icc 0 ℓ, c s ∈ e.target := by
    intro s hs
    rw [htgt, mem_ball, dist_comm, hdx s hs]
    exact lt_of_le_of_lt hs.2 hℓρ
  have hgw : ∀ s ∈ Icc 0 ℓ, g.inner x (e.symm (c s)) (e.symm (c s)) = s ^ 2 := by
    intro s hs
    have h := hdist _ (e.map_target (hct s hs))
    rw [e.right_inv (hct s hs), hdx s hs] at h
    have h2 := Real.sq_sqrt (g.inner_self_nonneg' x (e.symm (c s)))
    rw [← h] at h2
    exact h2.symm
  have hτI : τ ∈ Icc 0 ℓ := Ioo_subset_Icc_self hτ
  set v := e.symm (c τ) with hvdef
  have hvs : v ∈ e.source := e.map_target (hct τ hτI)
  set y := g.expMap (⟨x, v⟩ : TangentBundle I M) with hydef
  have hcy : c τ = y := by rw [hydef, ← (hexp v hvs).2, e.right_inv (hct τ hτI)]
  have hgv : g.inner x v v = τ ^ 2 := hgw τ hτI
  -- the exponential map at `x` and its inverse chart at `v`
  set f : E → M := fun u => g.expMap (⟨x, u⟩ : TangentBundle I M) with hfdef
  have hvdom : v ∈ {u : E | (⟨x, u⟩ : TangentBundle I M) ∈ g.expDomain} := (hexp v hvs).1
  have hyt : y ∈ e.target := hcy ▸ hct τ hτI
  have hsd : MDifferentiableAt I 𝓘(ℝ, E) e.symm y :=
    ((hsymm y hyt).contMDiffAt (e.open_target.mem_nhds hyt)).mdifferentiableAt hr0
  have hfd : MDifferentiableAt 𝓘(ℝ, E) I f v :=
    ((g.contMDiffOn_expMap_fiber hr1 x).contMDiffAt
      ((g.isOpen_expDomain_fiber hr1 x).mem_nhds hvdom)).mdifferentiableAt hr0
  have hfe : e.symm ∘ f =ᶠ[𝓝 v] id := by
    filter_upwards [e.open_source.mem_nhds hvs] with u hu
    simp only [Function.comp_apply, id, hfdef]
    rw [← (hexp u hu).2, e.left_inv hu]
  set P : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) e.symm y with hPdef
  set V : E := mfderiv 𝓘(ℝ, E) I f v v with hVdef
  have hPV : ∀ u : E, P (mfderiv 𝓘(ℝ, E) I f v u) = u := by
    intro u
    have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e.symm ∘ f) v =
        (mfderiv I 𝓘(ℝ, E) e.symm (f v)).comp (mfderiv 𝓘(ℝ, E) I f v) :=
      mfderiv_comp v hsd hfd
    rw [hfe.mfderiv_eq, mfderiv_id] at hc
    exact (congrArg (fun T => T u) hc).symm
  have hfP : ∀ ζ : E, mfderiv 𝓘(ℝ, E) I f v (P ζ) = ζ := by
    intro ζ
    have hfe' : f ∘ e.symm =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hyt] with z hz
      simp only [Function.comp_apply, id, hfdef]
      rw [← (hexp _ (e.map_target hz)).2, e.right_inv hz]
    have hsv : e.symm y = v := by rw [hydef, ← (hexp v hvs).2, e.left_inv hvs]
    have hfd' : MDifferentiableAt 𝓘(ℝ, E) I f (e.symm y) := hsv ▸ hfd
    have hc : mfderiv I I (f ∘ e.symm) y =
        (mfderiv 𝓘(ℝ, E) I f (e.symm y)).comp (mfderiv I 𝓘(ℝ, E) e.symm y) :=
      mfderiv_comp y hfd' hsd
    rw [hfe'.mfderiv_eq, mfderiv_id] at hc
    have key : ∀ u : E, u = v → mfderiv 𝓘(ℝ, E) I f u (P ζ) = ζ → mfderiv 𝓘(ℝ, E) I f v (P ζ) = ζ := by
      rintro u rfl h
      exact h
    exact key _ hsv (congrArg (fun T => T ζ) hc).symm
  -- Gauss
  have hgauss : ∀ ζ : E, g.inner x v (P ζ) = g.inner y V ζ := by
    intro ζ
    have h := g.inner_mfderiv_expMap_radial hr x hvdom (P ζ)
    rw [← hfdef, hfP ζ] at h
    exact h.symm
  have hVV : g.inner y V V = τ ^ 2 := by
    have h := g.inner_mfderiv_expMap_radial hr x hvdom v
    rw [← hfdef] at h
    rw [← hgv]
    exact h
  -- a normal chart at `y`
  obtain ⟨ρy, hρy, hcharty⟩ := g.exists_uniform_normal_charts hr hnorm (isCompact_singleton (x := y))
  obtain ⟨ey, hsrcy, htgty, hexpy, -, -, hdisty⟩ := hcharty y rfl
  have h0y : (0 : E) ∈ ey.source := by
    rw [hsrcy]
    change g.inner y (0 : TangentSpace I y) (0 : TangentSpace I y) < ρy ^ 2
    simp only [map_zero]
    positivity
  have hey0 : ey 0 = y := by
    rw [(hexpy 0 h0y).2]
    exact g.expMap_zero hr1 y
  set ξ : ℝ → E := fun h => ey.symm (c (τ + h)) with hξdef
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), τ + h ∈ Icc 0 ℓ ∧ dist h 0 < ρy := by
    have h1 : ∀ᶠ h in 𝓝 (0 : ℝ), τ + h ∈ Ioo 0 ℓ :=
      ((continuous_const.add continuous_id).tendsto' (0 : ℝ) τ (by simp)).eventually
        (isOpen_Ioo.mem_nhds hτ)
    filter_upwards [h1, Metric.ball_mem_nhds (0 : ℝ) hρy] with h hh1 hh2
    exact ⟨Ioo_subset_Icc_self hh1, hh2⟩
  have hdy : ∀ h, τ + h ∈ Icc 0 ℓ → dist y (c (τ + h)) = |h| := by
    intro h hh
    rw [← hcy, hseg τ hτI (τ + h) hh, show τ - (τ + h) = -h by ring, abs_neg]
  have hξt : ∀ h, τ + h ∈ Icc 0 ℓ → dist h 0 < ρy → c (τ + h) ∈ ey.target := by
    intro h hh hρ
    rw [htgty, mem_ball, dist_comm, hdy h hh]
    rwa [Real.dist_eq, sub_zero] at hρ
  -- the transition map and the squared radial function
  set Θ : E → E := fun ζ => e.symm (ey ζ) with hΘdef
  have hΘ : HasFDerivAt Θ P 0 := by
    have hey : HasMFDerivAt 𝓘(ℝ, E) I ey 0 (ContinuousLinearMap.id ℝ E) := by
      have h := (g.hasMFDerivAt_expMap_zero hr1 y).congr_of_eventuallyEq (f₁ := ey) (by
        filter_upwards [ey.open_source.mem_nhds h0y] with u hu
        exact (hexpy u hu).2)
      exact h.congr_mfderiv (by ext; rfl)
    have hs : HasMFDerivAt I 𝓘(ℝ, E) e.symm (ey 0) P := by
      rw [hey0]
      exact hsd.hasMFDerivAt
    have hc := hs.comp (0 : E) hey
    rw [hasMFDerivAt_iff_hasFDerivAt] at hc
    exact hc.congr_fderiv (by ext; rfl)
  have hΘ0 : Θ 0 = v := by
    simp only [hΘdef]
    rw [hey0, hydef, ← (hexp v hvs).2, e.left_inv hvs]
  set R : E → ℝ := fun ζ => g.inner x (Θ ζ) (Θ ζ) with hRdef
  have hR : HasFDerivAt R ((2 : ℝ) • (g.inner y V : E →L[ℝ] ℝ)) 0 := by
    obtain ⟨B, hBdef⟩ : ∃ B : E →L[ℝ] E →L[ℝ] ℝ, B = g.inner x := ⟨_, rfl⟩
    have hRB : R = fun ζ => B (Θ ζ) (Θ ζ) := by
      subst hBdef
      rfl
    have hB : HasFDerivAt (fun ζ => B (Θ ζ)) (B.comp P) 0 := B.hasFDerivAt.comp 0 hΘ
    have h := hB.clm_apply hΘ
    rw [hRB]
    refine h.congr_fderiv ?_
    ext ζ
    change B (Θ 0) (P ζ) + B (P ζ) (Θ 0) = (2 : ℝ) * g.inner y V ζ
    have hBsym : ∀ a b : E, B a b = B b a := by
      subst hBdef
      exact g.symm x
    have hBg : ∀ ζ' : E, B v (P ζ') = g.inner y V ζ' := by
      subst hBdef
      exact hgauss
    rw [hΘ0, hBsym (P ζ) v, hBg]
    ring
  have hR0 : R 0 = τ ^ 2 := by
    simp only [hRdef]
    rw [hΘ0, hgv]
  have hξprop : ∀ᶠ h in 𝓝 (0 : ℝ),
      (g.inner y : E →L[ℝ] E →L[ℝ] ℝ) (ξ h) (ξ h) = h ^ 2 ∧ R (ξ h) = (τ + h) ^ 2 := by
    filter_upwards [hev] with h hh
    have ht := hξt h hh.1 hh.2
    constructor
    · have hd := hdisty (ξ h) (ey.map_target ht)
      rw [ey.right_inv ht, hdy h hh.1] at hd
      have h2 := Real.sq_sqrt (g.inner_self_nonneg' y (ξ h))
      rw [← hd, sq_abs] at h2
      exact h2.symm
    · simp only [hRdef, hΘdef, hξdef]
      rw [ey.right_inv ht]
      exact hgw _ hh.1
  obtain ⟨cy, hcy0, hcoer⟩ := ContinuousLinearMap.isCoercive_of_posDef (F := E)
    (g.inner y : E →L[ℝ] E →L[ℝ] ℝ) (fun u hu => g.pos y u hu)
  have hξd := hasDerivAt_of_quadratic_radial (E := E) (G := (g.inner y : E →L[ℝ] E →L[ℝ] ℝ))
    (g.symm y) hcy0 hcoer hτ.1 hVV hR hR0 hξprop
  -- the chain rule
  have hξ0 : ξ 0 = 0 := by
    simp only [hξdef, add_zero]
    rw [hcy, ← hey0, ey.left_inv h0y]
  have hΘ' : HasFDerivAt Θ P (ξ 0) := by
    rw [hξ0]
    exact hΘ
  have hcomp := hΘ'.comp_hasDerivAt (0 : ℝ) hξd
  have heq : (fun h => e.symm (c (τ + h))) =ᶠ[𝓝 0] Θ ∘ ξ := by
    filter_upwards [hev] with h hh
    simp only [Function.comp_apply, hΘdef, hξdef]
    rw [ey.right_inv (hξt h hh.1 hh.2)]
  have hW := hcomp.congr_of_eventuallyEq heq
  have hval : P (τ⁻¹ • V) = τ⁻¹ • v := by
    rw [map_smul, hVdef, hPV v]
  replace hW := hW.congr_deriv hval
  have hW' : HasDerivAt (fun h => e.symm (c (τ + h))) (τ⁻¹ • v) (τ + -τ) := by
    rw [add_neg_cancel]
    exact hW
  have h2 := hW'.comp_add_const τ (-τ)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  change e.symm (c s) = e.symm (c (τ + (s + -τ)))
  rw [show τ + (s + -τ) = s by ring]

/-- **CM1.e** A short unit-speed metric segment from `x` is the radial geodesic
`t ↦ exp_x (t • u)`, `|u|_{g_x} = 1`. The chart hypothesis `he` is the six-clause conclusion of
`exists_uniform_normal_charts` (interface change S3 of the CM-N sheet). -/
theorem eq_expMap_of_short_segment [NeZero (Module.finrank ℝ E)] (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {x : M} {ρ : ℝ} (e : OpenPartialHomeomorph E M)
    (he : e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
      (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
      ContMDiffOn 𝓘(ℝ, E) I r e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target ∧
      ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v))
    {c : ℝ → M} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓρ : ℓ < ρ) (hc0 : c 0 = x)
    (hseg : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) :
    ∃ u : E, g.inner x u u = 1 ∧
      ∀ t ∈ Icc 0 ℓ, c t = g.expMap (⟨x, t • u⟩ : TangentBundle I M) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hquad : ∀ (B : E →L[ℝ] E →L[ℝ] ℝ) (a : ℝ) (w : E), B (a • w) (a • w) = a ^ 2 * B w w := by
    intro B a w
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rcases eq_or_lt_of_le hℓ with hℓ0 | hℓ0
  · -- `ℓ = 0`: any unit vector
    subst hℓ0
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (NeZero.pos (Module.finrank ℝ E))
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hgv : 0 < g.inner x v v := g.pos x v hv
    refine ⟨(Real.sqrt (g.inner x v v))⁻¹ • v, ?_, fun t ht => ?_⟩
    · refine (hquad (g.inner x) _ v).trans ?_
      rw [inv_pow, Real.sq_sqrt hgv.le]
      exact inv_mul_cancel₀ hgv.ne'
    · have ht0 : t = 0 := le_antisymm ht.2 ht.1
      rw [ht0, zero_smul, hc0]
      exact (g.expMap_zero hr1 x).symm
  obtain ⟨hsrc, htgt, hexp, hfwd, hsymm, hdist⟩ := he
  have hdx : ∀ s ∈ Icc 0 ℓ, dist x (c s) = s := by
    intro s hs
    rw [← hc0, hseg 0 ⟨le_rfl, hℓ⟩ s hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
  have hct : ∀ s ∈ Icc 0 ℓ, c s ∈ e.target := by
    intro s hs
    rw [htgt, mem_ball, dist_comm, hdx s hs]
    exact lt_of_le_of_lt hs.2 hℓρ
  have hgw : ∀ s ∈ Icc 0 ℓ, g.inner x (e.symm (c s)) (e.symm (c s)) = s ^ 2 := by
    intro s hs
    have h := hdist _ (e.map_target (hct s hs))
    rw [e.right_inv (hct s hs), hdx s hs] at h
    have h2 := Real.sq_sqrt (g.inner_self_nonneg' x (e.symm (c s)))
    rw [← h] at h2
    exact h2.symm
  -- `s ↦ s⁻¹ • e.symm (c s)` has derivative zero on `(0, ℓ)`
  have hU' : ∀ τ ∈ Ioo 0 ℓ, HasDerivAt (fun s : ℝ => s⁻¹ • e.symm (c s)) 0 τ := by
    intro τ hτ
    have hw := g.hasDerivAt_expChart_symm_segment hr hnorm e
      ⟨hsrc, htgt, hexp, hfwd, hsymm, hdist⟩ hℓρ hc0 hseg hτ
    refine ((hasDerivAt_inv hτ.1.ne').smul hw).congr_deriv ?_
    rw [smul_smul, ← add_smul]
    have hτ0 : τ ≠ 0 := hτ.1.ne'
    have hcoef : τ⁻¹ * τ⁻¹ + -(τ ^ 2)⁻¹ = 0 := by rw [sq, mul_inv]; ring
    rw [hcoef, zero_smul]
  -- continuity up to `ℓ`
  have hcc : ContinuousOn c (Icc 0 ℓ) := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    refine ⟨ε, hε, fun a ha hab => ?_⟩
    rwa [hseg a ha b hb, ← Real.dist_eq]
  have hwc : ContinuousOn (fun s => e.symm (c s)) (Icc 0 ℓ) :=
    e.continuousOn_symm.comp hcc (fun s hs => hct s hs)
  have hUeq : ∀ t ∈ Ioc 0 ℓ, t⁻¹ • e.symm (c t) = ℓ⁻¹ • e.symm (c ℓ) := by
    intro t ht
    have hcont : ContinuousOn (fun s : ℝ => s⁻¹ • e.symm (c s)) (Icc t ℓ) :=
      (continuousOn_id.inv₀ (fun s hs => (ht.1.trans_le hs.1).ne')).smul
        (hwc.mono (Icc_subset_Icc ht.1.le le_rfl))
    have h := constant_of_has_deriv_right_zero hcont (fun s hs =>
      (hU' s ⟨ht.1.trans_le hs.1, hs.2⟩).hasDerivWithinAt) ℓ ⟨ht.2, le_rfl⟩
    exact h.symm
  refine ⟨ℓ⁻¹ • e.symm (c ℓ), ?_, fun t ht => ?_⟩
  · have h2 := hgw ℓ ⟨hℓ, le_rfl⟩
    refine (hquad (g.inner x) _ _).trans ?_
    refine (congrArg (fun a => ℓ⁻¹ ^ 2 * a) h2).trans ?_
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_pos hℓ0 2).ne'
  · rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← ht0, zero_smul, hc0]
      exact (g.expMap_zero hr1 x).symm
    · have hwt : e.symm (c t) = t • (ℓ⁻¹ • e.symm (c ℓ)) := by
        rw [← hUeq t ⟨ht0, ht.2⟩, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
      have hmem : t • (ℓ⁻¹ • e.symm (c ℓ)) ∈ e.source := hwt ▸ e.map_target (hct t ht)
      rw [← (hexp _ hmem).2, ← hwt, e.right_inv (hct t ht)]

end Bundle.ContMDiffRiemannianMetric
