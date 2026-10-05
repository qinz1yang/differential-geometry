import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowGradient
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.ShortSegment

/-!
# Transport of finite minimizing directions and of the LFR46.2 margin (lane CMS3-FLOW2, G4)

LFR49 consumer item (b) (`build-logs/resume/state-LFR49.md`): LFR46.2's point margin
`g(X, u) ≤ −1/4` must hold in the transported carrier of LFR47 against the carrier metric's FINITE
minimizing directions. `finiteMinimizingDirectionsTo` reads the endpoint through `expMap`, so the
transport needs "geodesics go to geodesics" under the `C^k` isometric identity transition. It is
proved here METRICALLY, without a spray naturality computation:

* `eq_expMap_of_segment`: a `C¹` unit-speed metric segment `c : [0, d] → M` (`d(c s, c t) = |s − t|`) of
  a complete finite metric (order `≥ 3`) is the radial geodesic `t ↦ exp(t c'(0))`, `|c'(0)| = 1`.
  Short pieces are radial geodesics by the short-segment lemma (`eq_expMap_of_short_segment`, uniform
  radius on the compact image); their velocities are those of `c`; so the lift `(c, c')` is an
  integral curve of the geodesic spray on `(0, d)` and ODE uniqueness glues the pieces.
* `mfderiv_mem_finiteMinimizingDirectionsTo_of_isometry`: for a `C¹` distance-preserving map
  `F : N → M` with `G = F^* g` (inner products through `dF`), `dF` maps `G`'s minimizing directions to
  a set `T` into `g`'s minimizing directions to `F '' T` (the `G`-geodesic is a segment, its image is a
  `C¹` unit-speed `g`-segment).
* `inner_le_of_finiteMinimizingDirectionsTo_of_isometry`: the transported margin — a field `W` on
  `N` with `dF W = X ∘ F` has margin `≤ −κ` against `G`'s minimizing directions to `{n}` wherever `X`
  has it against `g`'s minimizing directions to `{F n}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

section Curves

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- A shift of the parameter keeps the velocity. -/
theorem hasMFDerivAt_comp_add_transport {γ : ℝ → N} {a s : ℝ} {v : TangentSpace IN (γ (a + s))}
    (h : HasMFDerivAt 𝓘(ℝ, ℝ) IN γ (a + s) ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) IN (fun τ => γ (a + τ)) s ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ : ℝ => a + τ) s (ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr ((hasFDerivAt_id s).const_add a)
  exact (h.comp s hshift).congr_mfderiv (ContinuousLinearMap.ext fun x => rfl)

/-- Two velocities of the same curve coincide. -/
theorem eq_of_hasMFDerivAt_curve_transport {γ : ℝ → N} {s : ℝ} {v w : TangentSpace IN (γ s)}
    (hv : HasMFDerivAt 𝓘(ℝ, ℝ) IN γ s ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hw : HasMFDerivAt 𝓘(ℝ, ℝ) IN γ s ((1 : ℝ →L[ℝ] ℝ).smulRight w)) : v = w := by
  have h := hv.mfderiv.symm.trans hw.mfderiv
  have h1 := congrArg (fun L : ℝ →L[ℝ] TangentSpace IN (γ s) => L 1) h
  change (1 : ℝ →L[ℝ] ℝ) 1 • v = (1 : ℝ →L[ℝ] ℝ) 1 • w at h1
  rwa [one_apply_eq_self, one_smul, one_smul] at h1

/-- A point of `TN` is the pair of any base point equal to its projection and its vector. -/
theorem mk_snd_eq_of_proj_eq_transport (p : TangentBundle IN N) {y : N} (h : p.proj = y) :
    (⟨y, p.snd⟩ : TangentBundle IN N) = p := by
  obtain ⟨a, b⟩ := p
  subst h
  rfl

end Curves

/-- **A `C¹` unit-speed metric segment is the radial geodesic.** -/
theorem eq_expMap_of_segment [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {c : ℝ → M} {c' : (t : ℝ) → TangentSpace I (c t)} {d : ℝ} (hd : 0 < d)
    (hseg : ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d, dist (c s) (c t) = |s - t|)
    (hc : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I c t ((1 : ℝ →L[ℝ] ℝ).smulRight (c' t))) :
    g.inner (c 0) (c' 0) (c' 0) = 1 ∧
      ∀ t ∈ Icc 0 d, c t = g.expMap (⟨c 0, t • c' 0⟩ : TangentBundle I M) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom : ∀ q, q ∈ g.geodesicFlowDomain := fun q => by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]; exact mem_univ q
  have hcc : Continuous c := continuous_iff_continuousAt.mpr fun t =>
    (hc t).mdifferentiableAt.continuousAt
  have hK : IsCompact (c '' Icc 0 d) := isCompact_Icc.image hcc
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm hK
  have hexpflow : ∀ (x : M) (w : E) (τ : ℝ),
      g.expMap (⟨x, τ • w⟩ : TangentBundle I M) =
        (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) τ).proj := fun x w τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 x w τ (hdom _)
  -- short pieces are radial geodesics
  have hloc : ∀ a ∈ Icc 0 d, a < d → ∃ ℓ > 0, a + ℓ ≤ d ∧ min (ρ / 2) (d - a) ≤ ℓ ∧ ∃ w : E,
      g.inner (c a) w w = 1 ∧ ∀ s ∈ Icc 0 ℓ, c (a + s) = g.expMap (⟨c a, s • w⟩ : TangentBundle I M) := by
    intro a ha had
    set ℓ := min (ρ / 2) (d - a) with hℓ
    have hℓ0 : 0 < ℓ := lt_min (half_pos hρ) (sub_pos.mpr had)
    obtain ⟨e, he⟩ := hch (c a) (mem_image_of_mem c ha)
    obtain ⟨w, hw1, hw⟩ := g.eq_expMap_of_short_segment hr hnorm e he (c := fun s => c (a + s))
      (ℓ := ℓ) hℓ0.le (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ)) (by simp)
      (fun s hs t ht => by
        rw [hseg (a + s) ⟨by linarith [hs.1, ha.1], by linarith [hs.2, min_le_right (ρ / 2) (d - a)]⟩
          (a + t) ⟨by linarith [ht.1, ha.1], by linarith [ht.2, min_le_right (ρ / 2) (d - a)]⟩]
        congr 1
        ring)
    exact ⟨ℓ, hℓ0, by linarith [min_le_right (ρ / 2) (d - a)], le_rfl, w, hw1, hw⟩
  -- on a piece, the lift `(c, c')` is the geodesic flow
  have hvel : ∀ a ℓ, ∀ w : E, (∀ s ∈ Icc 0 ℓ, c (a + s) = g.expMap (⟨c a, s • w⟩ : TangentBundle I M)) →
      ∀ s ∈ Ioo 0 ℓ, (⟨c (a + s), c' (a + s)⟩ : TangentBundle I M) =
        g.geodesicFlow (⟨c a, w⟩ : TangentBundle I M) s := by
    intro a ℓ w hw s hs
    have hproj : c (a + s) = (g.geodesicFlow (⟨c a, w⟩ : TangentBundle I M) s).proj := by
      rw [hw s ⟨hs.1.le, hs.2.le⟩, hexpflow]
    have h1 := hasMFDerivAt_comp_add_transport (hc (a + s))
    have hev : (fun τ => c (a + τ)) =ᶠ[𝓝 s]
        fun τ => (g.geodesicFlow (⟨c a, w⟩ : TangentBundle I M) τ).proj := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with τ hτ
      rw [hw τ ⟨hτ.1.le, hτ.2.le⟩, hexpflow]
    have h2 := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := (⟨c a, w⟩ : TangentBundle I M)) (t := s)
      (hdom _)
    have h2' := h2.congr_of_eventuallyEq_abuse hev
    have hsnd : @Eq E (c' (a + s)) (g.geodesicFlow (⟨c a, w⟩ : TangentBundle I M) s).snd :=
      eq_of_hasMFDerivAt_curve_transport (γ := fun τ => c (a + τ)) h1 h2'
    rw [← mk_snd_eq_of_proj_eq_transport (g.geodesicFlow (⟨c a, w⟩ : TangentBundle I M) s) hproj.symm]
    congr 1
  -- the lift is an integral curve of the spray on `(0, d)`
  set Γ : ℝ → TangentBundle I M := fun t => ⟨c t, c' t⟩ with hΓ
  have hcurve : IsMIntegralCurveOn Γ g.geodesicSpray (Ioo 0 d) := by
    intro t ht
    set a := max 0 (t - ρ / 4) with ha
    have ha0 : 0 ≤ a := le_max_left _ _
    have hat : a < t := max_lt ht.1 (by linarith)
    obtain ⟨ℓ, hℓ0, haℓ, hℓρ, w, -, hw⟩ := hloc a ⟨ha0, by linarith [ht.2]⟩ (by linarith [ht.2])
    have hta : t - a < ℓ := by
      have h1 : t - ρ / 4 ≤ a := le_max_right _ _
      exact lt_of_lt_of_le (lt_min (by linarith) (by linarith [ht.2])) hℓρ
    have hev : Γ =ᶠ[𝓝 t] fun τ => g.geodesicFlow (⟨c a, w⟩ : TangentBundle I M) (-a + τ) := by
      filter_upwards [Ioo_mem_nhds hat (by linarith : t < a + ℓ)] with τ hτ
      have h := hvel a ℓ w hw (τ - a) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      rw [show a + (τ - a) = τ by ring] at h
      rw [show -a + τ = τ - a by ring]
      exact h
    have hmem : -a + t ∈ maximalIntegralCurveInterval g.geodesicSpray
        (⟨c a, w⟩ : TangentBundle I M) := hdom (_, _)
    have hflow := (g.isMIntegralCurveOn_geodesicFlow hr1 (⟨c a, w⟩ : TangentBundle I M) (-a + t)
      hmem).hasMFDerivAt (isOpen_maximalIntegralCurveInterval.mem_nhds hmem)
    have h := (hasMFDerivAt_comp_add_transport (a := -a) (s := t) hflow).congr_of_eventuallyEq_abuse
      hev
    have hpt : Γ t = g.geodesicFlow (⟨c a, w⟩ : TangentBundle I M) (-a + t) := hev.self_of_nhds
    rw [← hpt] at h
    exact h.hasMFDerivWithinAt
  obtain ⟨ℓ₀, hℓ₀, hℓ₀d, -, w₀, hw₀1, hw₀⟩ := hloc 0 ⟨le_rfl, hd.le⟩ hd
  set p₀ : TangentBundle I M := ⟨c 0, w₀⟩ with hp₀
  have hflow0 : IsMIntegralCurveOn (g.geodesicFlow p₀) g.geodesicSpray (Ioo 0 d) := fun t _ => by
    have hmem : t ∈ maximalIntegralCurveInterval g.geodesicSpray p₀ := hdom (_, _)
    exact ((g.isMIntegralCurveOn_geodesicFlow hr1 p₀ t hmem).hasMFDerivAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds hmem)).hasMFDerivWithinAt
  have ht₀ : ℓ₀ / 2 ∈ Ioo 0 d := ⟨half_pos hℓ₀, by linarith⟩
  have hagree : Γ (ℓ₀ / 2) = g.geodesicFlow p₀ (ℓ₀ / 2) := by
    have h := hvel 0 ℓ₀ w₀ hw₀ (ℓ₀ / 2) ⟨half_pos hℓ₀, half_lt_self hℓ₀⟩
    rw [zero_add] at h
    exact h
  have hspray : ContMDiff I.tangent I.tangent.tangent 1 (fun v : TangentBundle I M =>
      (⟨v, g.geodesicSpray v⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr1)
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hspray hcurve hflow0 hagree
  have hc2 : Continuous (fun τ => (g.geodesicFlow p₀ τ).proj) :=
    continuous_iff_continuousAt.mpr fun τ =>
      (g.hasMFDerivAt_geodesicFlow_proj hr1 (hdom (p₀, τ))).mdifferentiableAt.continuousAt
  have hEq : EqOn c (fun τ => (g.geodesicFlow p₀ τ).proj) (Icc 0 d) := by
    have h1 : EqOn c (fun τ => (g.geodesicFlow p₀ τ).proj) (Ioo 0 d) := fun t ht =>
      congrArg TotalSpace.proj (heq ht)
    have h2 := h1.closure hcc hc2
    rwa [closure_Ioo hd.ne] at h2
  -- the initial velocity, by one-sided uniqueness at `0`
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Ici (0 : ℝ)) 0 :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffWithinAt_Ici 0)
  have hA := (hc 0).hasMFDerivWithinAt (s := Ici 0)
  have hB := (g.hasMFDerivAt_geodesicFlow_proj hr1 (p := p₀) (t := 0) (hdom _)).hasMFDerivWithinAt
    (s := Ici 0)
  have hB' := hB.congr_of_eventuallyEq (f₁ := c)
    (by filter_upwards [Icc_mem_nhdsGE hd] with τ hτ using hEq hτ) (hEq ⟨le_rfl, hd.le⟩)
  have hEqd := hU.eq hA hB'
  have h1 := congrArg (fun L : ℝ →L[ℝ] TangentSpace I (c 0) => L 1) hEqd
  have hc'0 : @Eq E (c' 0) (g.geodesicFlow p₀ 0).snd := by
    change @Eq E ((1 : ℝ →L[ℝ] ℝ) 1 • c' 0) ((1 : ℝ →L[ℝ] ℝ) 1 • (g.geodesicFlow p₀ 0).snd) at h1
    rwa [one_apply_eq_self, one_smul, one_smul] at h1
  rw [g.geodesicFlow_zero hr1] at hc'0
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hc'0]
    exact hw₀1
  · refine (hEq ht).trans ?_
    rw [hc'0]
    exact (hexpflow (c 0) w₀ t).symm

section Transport

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I' x)] [IsRiemannianManifold I' N] [CompleteSpace N]

/-- **A `C¹` isometry with pulled-back inner products maps finite minimizing directions to finite
minimizing directions.** -/
theorem mfderiv_mem_finiteMinimizingDirectionsTo_of_isometry
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {r' : ℕ∞} (G : ContMDiffRiemannianMetric I' ((r' : ℕ∞ω) + 1) E' (TangentSpace I' : N → Type _))
    (hr' : 2 ≤ r')
    (hGnorm : ∀ (x : N) (w : TangentSpace I' x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    {F : N → M} (hF : ∀ y, MDifferentiableAt I' I F y) (hFi : Isometry F)
    (hinner : ∀ (y : N) (v w : TangentSpace I' y),
      G.inner y v w = g.inner (F y) (mfderiv I' I F y v) (mfderiv I' I F y w))
    {T : Set N} {y : N} {v : TangentSpace I' y} (hv : v ∈ G.finiteMinimizingDirectionsTo T y) :
    mfderiv I' I F y v ∈ g.finiteMinimizingDirectionsTo (F '' T) (F y) := by
  have hr1' : 1 ≤ r' := one_le_two.trans hr'
  have hdomG : ∀ q, q ∈ G.geodesicFlowDomain := fun q => by
    rw [G.geodesicFlowDomain_eq_univ hr' hGnorm]; exact mem_univ q
  obtain ⟨hv1, hvT⟩ := hv
  have hu1 : g.inner (F y) (mfderiv I' I F y v) (mfderiv I' I F y v) = 1 := by
    rw [← hinner]; exact hv1
  have hNZ : NeZero (Module.finrank ℝ E) := by
    have hne : (mfderiv I' I F y v : E) ≠ 0 := by
      intro h0
      have h := hu1
      rw [h0] at h
      simp at h
    have : Nontrivial E := ⟨⟨_, 0, hne⟩⟩
    exact ⟨Module.finrank_pos.ne'⟩
  refine ⟨hu1, ?_⟩
  rw [Metric.infDist_image hFi]
  set d := infDist y T with hd
  set p : TangentBundle I' N := ⟨y, v⟩ with hp
  have hγ : ∀ τ : ℝ, G.expMap (⟨y, τ • v⟩ : TangentBundle I' N) = (G.geodesicFlow p τ).proj :=
    fun τ => G.expMap_smul_eq_proj_geodesicFlow hr1' y v τ (hdomG _)
  rcases eq_or_lt_of_le (infDist_nonneg : 0 ≤ d) with hd0 | hdpos
  · -- `d = 0`: `y ∈ T`
    have hd0' : d = 0 := hd0.symm
    have hyT : y ∈ T := by
      have h := hvT
      change G.expMap (⟨y, d • v⟩ : TangentBundle I' N) ∈ T at h
      rw [hd0', zero_smul, G.expMap_zero hr1'] at h
      exact h
    rw [hd0', zero_smul, g.expMap_zero (one_le_two.trans hr)]
    exact mem_image_of_mem F hyT
  · -- the `G`-geodesic is a segment
    set γ : ℝ → N := fun τ => (G.geodesicFlow p τ).proj with hγdef
    have hγ0 : γ 0 = y := by
      simp only [hγdef, G.geodesicFlow_zero hr1', hp]
    have hγd : γ d ∈ T := by
      have h := hvT
      rw [hγ] at h
      exact h
    have hlip : ∀ s t, dist (γ s) (γ t) ≤ |t - s| := fun s t => by
      have h := G.dist_proj_geodesicFlow_le hr1' hGnorm (p := p) (s := s) (t := t)
        (fun τ _ => hdomG _)
      change dist _ _ ≤ Real.sqrt (G.inner y v v) * |t - s| at h
      rwa [hv1, Real.sqrt_one, one_mul] at h
    have hseg : ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d, dist (γ s) (γ t) = |s - t| := by
      have hle : ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d, s ≤ t → dist (γ s) (γ t) = t - s := by
        intro s hs t ht hst
        refine le_antisymm ?_ ?_
        · have := hlip s t
          rwa [abs_of_nonneg (sub_nonneg.mpr hst)] at this
        · have h1 : d ≤ dist (γ 0) (γ d) := by
            rw [hγ0]; exact infDist_le_dist_of_mem hγd
          have h2 := dist_triangle4 (γ 0) (γ s) (γ t) (γ d)
          have h3 := hlip 0 s
          have h4 := hlip t d
          rw [sub_zero, abs_of_nonneg hs.1] at h3
          rw [abs_of_nonneg (sub_nonneg.mpr ht.2)] at h4
          linarith
      intro s hs t ht
      rcases le_total s t with hst | hts
      · rw [hle s hs t ht hst, abs_of_nonpos (sub_nonpos.mpr hst)]
        ring
      · rw [dist_comm, hle t ht s hs hts, abs_of_nonneg (sub_nonneg.mpr hts)]
    -- its image is a `C¹` unit-speed `g`-segment
    set c : ℝ → M := fun τ => F (γ τ) with hcdef
    set c' : (τ : ℝ) → TangentSpace I (c τ) := fun τ =>
      mfderiv I' I F (γ τ) (G.geodesicFlow p τ).snd with hc'def
    have hcseg : ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d, dist (c s) (c t) = |s - t| := fun s hs t ht => by
      rw [hcdef]
      dsimp only
      rw [hFi.dist_eq]
      exact hseg s hs t ht
    have hc : ∀ τ, HasMFDerivAt 𝓘(ℝ, ℝ) I c τ ((1 : ℝ →L[ℝ] ℝ).smulRight (c' τ)) := by
      intro τ
      have h1 := G.hasMFDerivAt_geodesicFlow_proj hr1' (p := p) (t := τ) (hdomG _)
      have h2 := (hF (γ τ)).hasMFDerivAt.comp τ h1
      refine h2.congr_mfderiv (ContinuousLinearMap.ext fun (x : ℝ) => ?_)
      change mfderiv I' I F (γ τ) (x • (G.geodesicFlow p τ).snd) =
        x • mfderiv I' I F (γ τ) (G.geodesicFlow p τ).snd
      rw [map_smul]
    obtain ⟨-, hcd⟩ := eq_expMap_of_segment g hr hnorm hdpos hcseg hc
    have hend := hcd d ⟨hdpos.le, le_rfl⟩
    have hkey : ∀ q : TangentBundle I' N, q = p →
        (⟨F q.proj, d • mfderiv I' I F q.proj q.snd⟩ : TangentBundle I M) =
          ⟨F y, d • mfderiv I' I F y v⟩ := by
      rintro q rfl
      rfl
    have h0 := hkey (G.geodesicFlow p 0) (G.geodesicFlow_zero hr1' p)
    change F (γ d) = g.expMap (⟨F (G.geodesicFlow p 0).proj,
      d • mfderiv I' I F (G.geodesicFlow p 0).proj (G.geodesicFlow p 0).snd⟩ : TangentBundle I M)
      at hend
    rw [h0] at hend
    rw [← hend]
    exact mem_image_of_mem F hγd

/-- **The transported margin (LFR49 item (b), kernel).** If `dF W = X ∘ F` and `X` has margin `≤ −κ`
against `g`'s minimizing directions to `{F n}` beyond distance `A`, then `W` has the same margin
against `G`'s FINITE minimizing directions to `{n}`. -/
theorem inner_le_of_finiteMinimizingDirectionsTo_of_isometry
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {r' : ℕ∞} (G : ContMDiffRiemannianMetric I' ((r' : ℕ∞ω) + 1) E' (TangentSpace I' : N → Type _))
    (hr' : 2 ≤ r')
    (hGnorm : ∀ (x : N) (w : TangentSpace I' x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    {F : N → M} (hF : ∀ y, MDifferentiableAt I' I F y) (hFi : Isometry F)
    (hinner : ∀ (y : N) (v w : TangentSpace I' y),
      G.inner y v w = g.inner (F y) (mfderiv I' I F y v) (mfderiv I' I F y w))
    (X : (x : M) → TangentSpace I x) (W : (y : N) → TangentSpace I' y)
    (hWX : ∀ y, mfderiv I' I F y (W y) = X (F y)) (n : N) {A κ : ℝ}
    (hX : ∀ q, A ≤ dist (F n) q → ∀ u ∈ g.finiteMinimizingDirectionsTo {F n} q,
      g.inner q (X q) u ≤ -κ) :
    ∀ y, A ≤ dist n y → ∀ v ∈ G.finiteMinimizingDirectionsTo {n} y, G.inner y (W y) v ≤ -κ := by
  intro y hy v hv
  have hmem := mfderiv_mem_finiteMinimizingDirectionsTo_of_isometry g hr hnorm G hr' hGnorm hF hFi
    hinner hv
  rw [image_singleton] at hmem
  rw [hinner, hWX]
  exact hX (F y) (by rw [hFi.dist_eq]; exact hy) _ hmem

end Transport

end DifferentialGeometry.Geometry.FiniteSoul
