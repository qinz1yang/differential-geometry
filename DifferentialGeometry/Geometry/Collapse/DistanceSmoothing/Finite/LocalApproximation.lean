import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FirstVariation

/-!
# Local smoothing of the distance to a closed set for a metric of finite order (LFR02, tier T2)

Finite-order re-run of LC28's chart tier (`DistanceSmoothing/{ChartMetric, ChartDistanceDini,
LocalApproximation}.lean`, whose statements take a `SmoothRiemannianMetric`):

* `hasMFDerivAt_extChartAt_symm_line`: the chart line `t ↦ φ.symm (φ z + t w)` has velocity
  `e.symmL z w`.
* `eventually_finiteMinimizingDirectionsTo_chart_close` (upper semicontinuity of `V(Y)` in a chart,
  proved through the closed graph CM3.b).
* `exists_ball_finiteSeminormAt_chart_sub_le` (chart Lipschitz bound, along a minimizing geodesic).
* `exists_local_distance_approximation_finite` (local smoothing with a Lipschitz difference).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Analysis.Calculus

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- The chart line through `z` in direction `w` has velocity `e.symmL z w` at `0`. -/
theorem hasMFDerivAt_extChartAt_symm_line (b : M) {z : M} (hz : z ∈ (chartAt H b).source)
    (w : E) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => (extChartAt I b).symm (extChartAt I b z + t • w)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)) := by
  set φ := extChartAt I b with hφ
  have hzs : z ∈ φ.source := by rw [hφ, extChartAt_source]; exact hz
  have hy₀ : φ z ∈ φ.target := φ.map_source hzs
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ z) := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := b) hy₀
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hmd : mfderiv 𝓘(ℝ, E) I φ.symm (φ z) =
      (trivializationAt E (TangentSpace I) b).symmL ℝ z := by
    rw [TangentBundle.symmL_trivializationAt hz, ModelWithCorners.Boundaryless.range_eq_univ,
      mfderivWithin_univ]
  have hline : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => φ z + t • w) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    refine hasMFDerivAt_iff_hasFDerivAt.mpr ?_
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (φ z)
    rw [one_smul] at this
    exact this.hasFDerivAt
  have hsymm' : HasMFDerivAt 𝓘(ℝ, E) I φ.symm (φ z + (0 : ℝ) • w)
      (mfderiv 𝓘(ℝ, E) I φ.symm (φ z)) := by
    rw [zero_smul, add_zero]; exact hsymm.hasMFDerivAt
  refine (hsymm'.comp 0 hline).congr_mfderiv ?_
  rw [hmd]
  ext
  change (trivializationAt E (TangentSpace I) b).symmL ℝ z
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) 1) =
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)) 1
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
    one_smul, one_smul]

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

variable {r : ℕ∞}

/-- Directional Dini bound for the distance to a closed set read in the chart at `b`
(finite-order form of LC28's `eventually_infDist_chart_increment_le`). -/
theorem eventually_infDist_chart_increment_le_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {Y : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty) (b : M) {z : M}
    (hz : z ∈ (chartAt H b).source) (hzY : z ∉ Y) (w : E) {c : ℝ}
    (hc : ∀ u ∈ finiteMinimizingDirectionsTo g Y z,
      -g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Metric.infDist ((extChartAt I b).symm (extChartAt I b z + t • w)) Y -
        Metric.infDist z Y ≤ t * c := by
  obtain ⟨u, hu⟩ := (finiteMinimizingDirectionsTo_nonempty_isCompact g hr hnorm hY hYne z).1
  have hzs : z ∈ (extChartAt I b).source := by rw [extChartAt_source]; exact hz
  exact eventually_infDist_sub_le_finite_of_eq g hr hnorm hY hYne
    (γ := fun t : ℝ => (extChartAt I b).symm (extChartAt I b z + t • w))
    (by simp only [zero_smul, add_zero]; exact (extChartAt I b).left_inv hzs)
    (hasMFDerivAt_extChartAt_symm_line b hz w) hzY hu (hc u hu)

omit [NeZero (Module.finrank ℝ E)] in
/-- Upper semicontinuity of the minimizing directions read through the chart at `b` (finite-order
form of LC28's `eventually_minimizingDirectionsTo_chart_close`, proved through the closed graph). -/
theorem eventually_finiteMinimizingDirectionsTo_chart_close [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {Y : Set M} (hY : IsClosed Y) (b : M) {u₀ : TangentSpace I b} {a : ℝ}
    (hclose : ∀ u ∈ finiteMinimizingDirectionsTo g Y b,
      Real.sqrt (g.inner b (u - u₀) (u - u₀)) < a) :
    ∀ᶠ z in 𝓝 b, ∀ u ∈ finiteMinimizingDirectionsTo g Y z, ∀ w : E,
      |g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) - g.inner b u₀ w| ≤
        a * finiteMetricSeminormAt g b w := by
  set T := trivializationAt E (TangentSpace I) b with hT
  set N := finiteMetricSeminormAt g b with hN
  have hbase : ∀ z : M, z ∈ T.baseSet ↔ z ∈ (chartAt H b).source := by
    intro z; rw [hT, TangentBundle.trivializationAt_baseSet]
  obtain ⟨c₀, hc₀, hc₀N⟩ := exists_mul_norm_le_finiteMetricSeminormAt g b
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨z, hzlim, hbad⟩ := exists_seq_forall_of_frequently hcon
  push Not at hbad
  choose u hu w hlt using hbad
  have hwpos : ∀ n, 0 < N (w n) := by
    intro n
    rcases (apply_nonneg N (w n)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hw0 : w n = 0 := by
        by_contra hne
        have := Real.sqrt_pos.mpr (g.pos b (w n) hne)
        exact this.ne' (h.symm.trans rfl)
      have e1 : T.symmL ℝ (z n) (w n) = 0 := by rw [hw0, map_zero]
      have e2 : g.inner (z n) (u n) (T.symmL ℝ (z n) (w n)) = 0 := by rw [e1, map_zero]
      have e3 : g.inner b u₀ (w n) = 0 := by rw [hw0]; exact (finiteMetricFormAt g b u₀).map_zero
      have := hlt n
      rw [e2, e3, sub_zero, abs_zero, ← h, mul_zero] at this
      exact lt_irrefl 0 this
  set w' : ℕ → E := fun n => (N (w n))⁻¹ • w n with hw'
  have hNw' : ∀ n, N (w' n) = 1 := fun n => by
    rw [hw', map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos (hwpos n),
      inv_mul_cancel₀ (hwpos n).ne']
  have hlt' : ∀ n, a < |g.inner (z n) (u n) (T.symmL ℝ (z n) (w' n)) - g.inner b u₀ (w' n)| := by
    intro n
    have e : g.inner (z n) (u n) (T.symmL ℝ (z n) (w' n)) - g.inner b u₀ (w' n) =
        (N (w n))⁻¹ * (g.inner (z n) (u n) (T.symmL ℝ (z n) (w n)) - g.inner b u₀ (w n)) := by
      rw [hw']
      change g.inner (z n) (u n) (T.symmL ℝ (z n) ((N (w n))⁻¹ • w n)) -
        finiteMetricFormAt g b u₀ ((N (w n))⁻¹ • w n) = _
      rw [map_smul, map_smul, map_smul]
      simp only [smul_eq_mul]
      change (N (w n))⁻¹ * g.inner (z n) (u n) (T.symmL ℝ (z n) (w n)) -
        (N (w n))⁻¹ * finiteMetricFormAt g b u₀ (w n) = (N (w n))⁻¹ *
          (g.inner (z n) (u n) (T.symmL ℝ (z n) (w n)) - finiteMetricFormAt g b u₀ (w n))
      ring
    rw [e, abs_mul, abs_inv, abs_of_pos (hwpos n), lt_inv_mul_iff₀ (hwpos n)]
    have := hlt n
    linarith [mul_comm a (N (w n))]
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hzlim.eventually (eventually_finite_chart_metric_comparison g b one_lt_two))
  set ũ : ℕ → E := fun n => T.continuousLinearMapAt ℝ (z (n + K)) (u (n + K)) with hũ
  have hsymm : ∀ n, T.symmL ℝ (z (n + K)) (ũ n) = u (n + K) := fun n =>
    T.symmL_continuousLinearMapAt ((hbase _).mpr (hK (n + K) (Nat.le_add_left K n)).1)
      (u (n + K))
  set R : ℝ := Real.sqrt 2 / c₀ + 1 / c₀ with hR
  have hbd : ∀ n, (ũ n, w' (n + K)) ∈ Metric.closedBall ((0 : E), (0 : E)) R := by
    intro n
    have hgood := hK (n + K) (Nat.le_add_left K n)
    have h1 := (hgood.2 (ũ n)).1
    rw [hsymm n, (hu (n + K)).1, mul_one] at h1
    have h2 : ‖ũ n‖ ≤ Real.sqrt 2 / c₀ := by
      rw [le_div_iff₀ hc₀]
      calc ‖ũ n‖ * c₀ = c₀ * ‖ũ n‖ := mul_comm _ _
        _ ≤ N (ũ n) := hc₀N _
        _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
    have h3 : ‖w' (n + K)‖ ≤ 1 / c₀ := by
      rw [le_div_iff₀ hc₀]
      calc ‖w' (n + K)‖ * c₀ = c₀ * ‖w' (n + K)‖ := mul_comm _ _
        _ ≤ N (w' (n + K)) := hc₀N _
        _ = 1 := hNw' _
    rw [Metric.mem_closedBall, Prod.dist_eq, dist_zero_right, dist_zero_right]
    have h4 : 0 ≤ Real.sqrt 2 / c₀ := by positivity
    have h5 : 0 ≤ 1 / c₀ := by positivity
    exact max_le (by linarith) (by linarith)
  obtain ⟨⟨uInf, wInf⟩, -, ψ, hψ, hψlim⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  have hψ1 : Tendsto (fun n => ũ (ψ n)) atTop (𝓝 uInf) := (continuous_fst.tendsto _).comp hψlim
  have hψ2 : Tendsto (fun n => w' (ψ n + K)) atTop (𝓝 wInf) :=
    (continuous_snd.tendsto _).comp hψlim
  have hzψ : Tendsto (fun n => z (ψ n + K)) atTop (𝓝 b) :=
    hzlim.comp ((tendsto_add_atTop_nat K).comp hψ.tendsto_atTop)
  have hplim : Tendsto (fun n => (⟨z (ψ n + K), u (ψ n + K)⟩ : TangentBundle I M)) atTop
      (𝓝 (⟨b, uInf⟩ : TangentBundle I M)) := by
    have hcont : ContinuousAt (fun p : M × E => (⟨p.1, T.symmL ℝ p.1 p.2⟩ : TangentBundle I M))
        (b, uInf) :=
      (continuousOn_trivializationAt_symm (I := I) b).continuousAt
        (prod_mem_nhds ((chartAt H b).open_source.mem_nhds (mem_chart_source H b)) univ_mem)
    have h2 := hcont.tendsto.comp (hzψ.prodMk_nhds hψ1)
    have hsx : T.symmL ℝ b uInf = uInf := trivializationAt_symmL_self b uInf
    rw [hsx] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hsymm (ψ n)]
  have huInf : uInf ∈ finiteMinimizingDirectionsTo g Y b :=
    mem_finiteMinimizingDirectionsTo_of_tendsto g hr hnorm hY
      (p := fun n => (⟨z (ψ n + K), u (ψ n + K)⟩ : TangentBundle I M)) (fun n => hu _) hplim
  have hNwInf : N wInf = 1 := by
    have h := ((continuous_finiteMetricSeminormAt g b).tendsto wInf).comp hψ2
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun n => (hNw' (ψ n + K)).symm)
  -- continuity of the pulled back metric
  have hG : ContinuousAt (fun p : M × E × E => g.inner p.1 (T.symmL ℝ p.1 p.2.1)
      (T.symmL ℝ p.1 p.2.2)) (b, uInf, wInf) := by
    have hsrc : (chartAt H b).source ×ˢ (univ : Set (E × E)) ∈ 𝓝 (b, uInf, wInf) :=
      prod_mem_nhds ((chartAt H b).open_source.mem_nhds (mem_chart_source H b)) univ_mem
    have hS := continuousOn_trivializationAt_symm (I := I) b
    have hv : ContinuousOn (fun p : M × E × E => (⟨p.1, T.symmL ℝ p.1 p.2.1⟩ : TangentBundle I M))
        ((chartAt H b).source ×ˢ univ) :=
      hS.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
        (fun p hp => ⟨hp.1, mem_univ _⟩)
    have hw : ContinuousOn (fun p : M × E × E => (⟨p.1, T.symmL ℝ p.1 p.2.2⟩ : TangentBundle I M))
        ((chartAt H b).source ×ˢ univ) :=
      hS.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
        (fun p hp => ⟨hp.1, mem_univ _⟩)
    exact (continuousOn_finiteInner_of_bundle (g := g) (b := fun p : M × E × E => p.1)
      (v := fun p => T.symmL ℝ p.1 p.2.1) (w := fun p => T.symmL ℝ p.1 p.2.2) hv hw).continuousAt
        hsrc
  have hGlim := hG.tendsto.comp (hzψ.prodMk_nhds (hψ1.prodMk_nhds hψ2))
  have hu₀lim : Tendsto (fun n => g.inner b u₀ (w' (ψ n + K))) atTop (𝓝 (g.inner b u₀ wInf)) :=
    ((finiteMetricFormAt g b u₀).continuous.tendsto wInf).comp hψ2
  have hval : g.inner b (T.symmL ℝ b uInf) (T.symmL ℝ b wInf) = g.inner b uInf wInf := by
    rw [trivializationAt_symmL_self, trivializationAt_symmL_self]
  have hlim := (hGlim.sub hu₀lim).abs
  simp only [Function.comp_def, hval] at hlim
  have hge : a ≤ |g.inner b uInf wInf - g.inner b u₀ wInf| := by
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have := hlt' (ψ n + K)
    rw [← hsymm (ψ n)] at this
    exact this.le
  obtain ⟨uT, huT⟩ : ∃ uT : TangentSpace I b, uT = uInf := ⟨uInf, rfl⟩
  have hcs : |g.inner b uT wInf - g.inner b u₀ wInf| ≤
      Real.sqrt (g.inner b (uT - u₀) (uT - u₀)) * N wInf := by
    have e : g.inner b uT wInf - g.inner b u₀ wInf = g.inner b (uT - u₀) wInf := by
      rw [map_sub]; rfl
    rw [e]
    exact abs_finite_inner_le g b _ _
  rw [hNwInf, mul_one] at hcs
  have := hclose uT (huT ▸ huInf)
  rw [← huT] at hge
  linarith

/-- Chart Lipschitz bound for a complete finite-order metric: near the chart centre `b`,
`N_b(φ x' - φ x) ≤ κ dist x x'` for `φ = extChartAt I b` and every `κ > 1` (finite-order form of
LC28's `exists_ball_metricSeminormAt_chart_sub_le`, along a minimizing geodesic). -/
theorem exists_ball_finiteSeminormAt_chart_sub_le [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (b : M) {κ : ℝ} (hκ : 1 < κ) :
    ∃ r₀ > 0, Metric.ball b r₀ ⊆ (chartAt H b).source ∧
      ∀ x ∈ Metric.ball b r₀, ∀ x' ∈ Metric.ball b r₀,
        finiteMetricSeminormAt g b (extChartAt I b x' - extChartAt I b x) ≤ κ * dist x x' := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set T := trivializationAt E (TangentSpace I) b with hT
  have hbase : ∀ z : M, z ∈ T.baseSet ↔ z ∈ (chartAt H b).source := by
    intro z; rw [hT, TangentBundle.trivializationAt_baseSet]
  have hκ2 : 1 < κ ^ 2 := by nlinarith
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (eventually_finite_chart_metric_comparison g b hκ2)
  refine ⟨ε / 3, by positivity, fun z hz => (hball (Metric.ball_subset_ball (by linarith) hz)).1,
    fun x hx x' hx' => ?_⟩
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  set D := dist x x' with hD
  have hD0 : 0 ≤ D := dist_nonneg
  have hDlt : D < 2 * (ε / 3) := by
    have h1 := dist_triangle x b x'
    rw [Metric.mem_ball] at hx hx'
    rw [dist_comm b x'] at h1
    linarith
  obtain ⟨u, hu1, -, hend⟩ := exists_unit_segment_expMap g hr hnorm x x'
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x, v = D • u := ⟨_, rfl⟩
  set p : TangentBundle I M := ⟨x, v⟩ with hp
  have hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain := by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]; exact fun _ => mem_univ _
  set γ : ℝ → M := fun t => (g.geodesicFlow p t).proj with hγ
  have hγexp : ∀ t, γ t = g.expMap (⟨x, t • v⟩ : TangentBundle I M) := fun t =>
    (g.expMap_smul_eq_proj_geodesicFlow hr1 x v t (hdom t)).symm
  have hγ0 : γ 0 = x := by rw [hγexp, zero_smul]; exact g.expMap_zero hr1 x
  have hγ1 : γ 1 = x' := by rw [hγexp, one_smul, hv]; exact hend
  have hvv : g.inner x v v = D ^ 2 := by
    rw [hv]; erw [finite_inner_smul_self g x D u]; rw [hu1, mul_one]
  have hγV : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Metric.ball b ε := by
    intro t ht
    have h := g.dist_expMap_smul_le_of_completeSpace hr1 hnorm v 0 t
    rw [zero_smul, g.expMap_zero hr1 x, ← hγexp, hvv, Real.sqrt_sq hD0, sub_zero,
      abs_of_nonneg ht.1] at h
    have hxt : dist x (γ t) ≤ D := h.trans (by nlinarith [ht.2])
    rw [Metric.mem_ball] at hx ⊢
    have := dist_triangle (γ t) x b
    rw [dist_comm (γ t) x] at this
    linarith
  set φ := extChartAt I b with hφ
  set V₀ : E := φ x' - φ x with hV₀
  set N := finiteMetricSeminormAt g b with hN
  let L₀ : E →L[ℝ] ℝ := finiteMetricFormAt g b V₀
  let ψ : ℝ → ℝ := fun t => L₀ (φ (γ t))
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (L₀ (T (g.geodesicFlow p t)).2) t := by
    intro t ht
    have hz : γ t ∈ (chartAt H b).source := (hball (hγV t ht)).1
    have h1 := g.hasMFDerivAt_geodesicFlow_proj hr1 (hdom t)
    have h2 : HasMFDerivAt I 𝓘(ℝ, E) φ (γ t) (mfderiv I 𝓘(ℝ, E) φ (γ t)) :=
      (mdifferentiableAt_extChartAt hz).hasMFDerivAt
    have h3 : HasFDerivAt (fun σ => φ (γ σ))
        (show ℝ →L[ℝ] E from (mfderiv I 𝓘(ℝ, E) φ (γ t)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p t).snd)) t :=
      hasMFDerivAt_iff_hasFDerivAt.mp (h2.comp t h1)
    have h4 := (L₀.hasFDerivAt.comp t h3).hasDerivAt
    refine HasDerivAt.congr_deriv h4 ?_
    change L₀ ((mfderiv I 𝓘(ℝ, E) φ (γ t))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p t).snd) 1)) = _
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, hφ,
      ← TangentBundle.continuousLinearMapAt_trivializationAt hz]
    congr 1
    exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace I) b) ((hbase _).mpr hz) (g.geodesicFlow p t).snd
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖L₀ (T (g.geodesicFlow p t)).2‖ ≤ N V₀ * (κ * D) := by
    intro t ht
    have hz := hball (hγV t (Ico_subset_Icc_self ht))
    set w' : E := (T (g.geodesicFlow p t)).2 with hw'
    have hT' : T.symmL ℝ (γ t) w' = (g.geodesicFlow p t).snd := by
      rw [hw', ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) T
        ((hbase _).mpr hz.1)]
      exact T.symmL_continuousLinearMapAt ((hbase _).mpr hz.1) _
    have hspeed : g.inner (γ t) (T.symmL ℝ (γ t) w') (T.symmL ℝ (γ t) w') = D ^ 2 := by
      rw [hT', g.inner_geodesicFlow_eq hr1 p t (hdom t)]; exact hvv
    have hcmp := (hz.2 w').1
    rw [hspeed] at hcmp
    have hNw : N w' ≤ κ * D := by
      rw [hN, finiteMetricSeminormAt_apply, Real.sqrt_le_left (mul_nonneg hκpos.le hD0)]
      calc g.inner b w' w' ≤ κ ^ 2 * D ^ 2 := hcmp
        _ = (κ * D) ^ 2 := by ring
    rw [Real.norm_eq_abs]
    calc |L₀ w'| = |g.inner b V₀ w'| := rfl
      _ ≤ N V₀ * N w' := abs_inner_le_finiteMetricSeminormAt g b V₀ w'
      _ ≤ N V₀ * (κ * D) := mul_le_mul_of_nonneg_left hNw (apply_nonneg _ _)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ)
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound
  have hψ : ψ 1 - ψ 0 = N V₀ ^ 2 := by
    have e1 : ψ 1 - ψ 0 = L₀ V₀ := by
      change L₀ (φ (γ 1)) - L₀ (φ (γ 0)) = L₀ V₀
      rw [hγ0, hγ1, ← map_sub]
    rw [e1, hN, finiteMetricSeminormAt_sq]
    rfl
  rw [hψ, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hmv
  have hN0 := apply_nonneg N V₀
  have hKD : 0 ≤ κ * D := mul_nonneg hκpos.le hD0
  refine le_of_not_gt fun hcon => ?_
  nlinarith

/-- Local smoothing of the distance to a closed set with a Lipschitz difference, for a complete
metric of finite order (finite-order form of LC28's `exists_local_distance_approximation`). -/
theorem exists_local_distance_approximation_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {Y U : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty)
    (hU : IsOpen U) (hUY : Disjoint U Y) {θ L : ℝ} (hθL : 2 * θ < L)
    (hdiam : ∀ q ∈ U, ∀ u ∈ finiteMinimizingDirectionsTo g Y q,
      ∀ u' ∈ finiteMinimizingDirectionsTo g Y q, Real.sqrt (g.inner q (u - u') (u - u')) < θ)
    {b : M} (hb : b ∈ U) :
    ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ η > 0, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' W ∧
        (∀ x ∈ W, |f' x - Metric.infDist x Y| ≤ η) ∧
        ∀ x ∈ W, ∀ x' ∈ W, |(f' x - Metric.infDist x Y) - (f' x' - Metric.infDist x' Y)| ≤
          L * dist x x' := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hnot : ∀ q ∈ U, q ∉ Y := fun q hq => Set.disjoint_left.mp hUY hq
  obtain ⟨u₀, hu₀⟩ := (finiteMinimizingDirectionsTo_nonempty_isCompact g hr hnorm hY hYne b).1
  have hθpos : 0 < θ := by
    have := hdiam b hb u₀ hu₀ u₀ hu₀
    simpa using this
  set a : ℝ := (2 * θ + L) / 4 with ha
  have hθa : θ < a := by rw [ha]; linarith
  have hapos : 0 < a := hθpos.trans hθa
  set κ : ℝ := L / (2 * a) with hκ
  have hκ1 : 1 < κ := by
    rw [hκ, one_lt_div (by positivity)]
    rw [ha]; linarith
  have h2aκ : 2 * a * κ = L := by rw [hκ]; field_simp
  set N := finiteMetricSeminormAt g b with hN
  set φ := extChartAt I b with hφ
  set ℓ : E →L[ℝ] ℝ := -finiteMetricFormAt g b u₀ with hℓ
  have husc := eventually_finiteMinimizingDirectionsTo_chart_close g hr hnorm hY b (u₀ := u₀)
    (a := a) (fun u hu => (hdiam b hb u hu u₀ hu₀).trans hθa)
  obtain ⟨r₁, hr₁, hr₁src, hchart⟩ := exists_ball_finiteSeminormAt_chart_sub_le g hr hnorm b hκ1
  set A : Set M := {z | z ∈ U ∧ z ∈ (chartAt H b).source ∧
    ∀ u ∈ finiteMinimizingDirectionsTo g Y z, ∀ w : E,
      |g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) -
          g.inner b u₀ w| ≤ a * N w} with hA
  have hAnhds : A ∈ 𝓝 b := by
    filter_upwards [hU.mem_nhds hb, (chartAt H b).open_source.mem_nhds (mem_chart_source H b),
      husc] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hpre : φ.target ∩ φ.symm ⁻¹' A ∈ 𝓝 (φ b) :=
    inter_mem (extChartAt_target_mem_nhds b)
      ((continuousAt_extChartAt_symm b).preimage_mem_nhds (by rwa [extChartAt_to_inv]))
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set B : Set E := Metric.ball (φ b) ρ₀ with hB
  let h : E → ℝ := fun y => Metric.infDist (φ.symm y) Y - ℓ y
  have hcont : ContinuousOn h B := by
    refine ContinuousOn.sub ?_ ℓ.continuous.continuousOn
    exact ((Metric.continuous_infDist_pt Y).comp_continuousOn
      (continuousOn_extChartAt_symm b)).mono (fun y hy => (hball hy).1)
  have hdini : ∀ y ∈ B, ∀ w : E, ∀ c, a * N w < c →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), h (y + t • w) - h y ≤ t * c := by
    intro y hy w c hc
    obtain ⟨hyt, hyA⟩ := hball hy
    set z := φ.symm y with hz
    have hφz : φ z = y := φ.right_inv hyt
    have hzsrc : z ∈ (chartAt H b).source := hyA.2.1
    have hev := eventually_infDist_chart_increment_le_finite g hr hnorm hY hYne b hzsrc
      (hnot z hyA.1) w (c := c + ℓ w) (by
        intro u hu
        have h1 := hyA.2.2 u hu w
        have h2 : ℓ w = -g.inner b u₀ w := rfl
        rw [h2]
        have h3 := (abs_le.mp h1).1
        linarith)
    filter_upwards [hev] with t ht
    rw [hφz] at ht
    simp only [h, map_add, map_smul, smul_eq_mul]
    linarith
  have hlip := abs_sub_le_seminorm_of_eventually_increment_le N (convex_ball _ _) hcont hdini
  refine ⟨(chartAt H b).source ∩ φ ⁻¹' Metric.ball (φ b) (ρ₀ / 2) ∩ Metric.ball b r₁,
    ((isOpen_extChartAt_preimage b Metric.isOpen_ball).inter Metric.isOpen_ball),
    ⟨⟨mem_chart_source H b, Metric.mem_ball_self (by positivity)⟩, Metric.mem_ball_self hr₁⟩,
    ?_, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx.1.1
    have hmem : φ x ∈ B := Metric.ball_subset_ball (by linarith) hx.1.2
    have := (hball hmem).2
    rw [Set.mem_preimage, φ.left_inv hxs] at this
    exact this.1
  · exact (isCompact_closedBall b r₁).of_isClosed_subset isClosed_closure
      ((closure_mono inter_subset_right).trans Metric.closure_ball_subset_closedBall)
  · intro η hη
    set C : ℝ := Real.sqrt ‖finiteMetricFormAt g b‖ with hC
    have hC0 : 0 ≤ C := Real.sqrt_nonneg _
    set r : ℝ := min (ρ₀ / 2) (η / (a * C + 1)) with hr
    have hrpos : 0 < r := lt_min (by positivity) (by positivity)
    have hδ : ∀ z : E, ‖z‖ ≤ r → N z ≤ C * r := fun z hz =>
      (finiteMetricSeminormAt_le_mul_norm g b z).trans (mul_le_mul_of_nonneg_left hz hC0)
    obtain ⟨h', hsmooth, hl, hv⟩ := exists_contDiff_seminorm_lipschitz_approx N
      (finiteMetricSeminormAt_le_mul_norm g b) hapos.le hlip hrpos hδ
    have haδ : a * (C * r) ≤ η := by
      have hr2 : r ≤ η / (a * C + 1) := min_le_right _ _
      have h1 : a * C * r ≤ a * C * (η / (a * C + 1)) :=
        mul_le_mul_of_nonneg_left hr2 (by positivity)
      have h2 : a * C * (η / (a * C + 1)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have hsub : ∀ x ∈ (chartAt H b).source ∩ φ ⁻¹' Metric.ball (φ b) (ρ₀ / 2) ∩
        Metric.ball b r₁, Metric.closedBall (φ x) r ⊆ B := by
      intro x hx y hy
      rw [Metric.mem_closedBall] at hy
      have h1 : dist (φ x) (φ b) < ρ₀ / 2 := hx.1.2
      have h2 : r ≤ ρ₀ / 2 := min_le_left _ _
      rw [hB, Metric.mem_ball]
      linarith [dist_triangle y (φ x) (φ b)]
    have hhx : ∀ x ∈ (chartAt H b).source, h (φ x) = Metric.infDist x Y - ℓ (φ x) := by
      intro x hx
      have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx
      simp only [h, φ.left_inv hxs]
    refine ⟨fun x => h' (φ x) + ℓ (φ x), ?_, ?_, ?_⟩
    · have hs : ContDiff ℝ ∞ (fun y => h' y + ℓ y) := hsmooth.add ℓ.contDiff
      exact hs.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt.mono
        (fun x hx => hx.1.1))
    · intro x hx
      have := hv (φ x) (hsub x hx)
      rw [hhx x hx.1.1] at this
      calc |h' (φ x) + ℓ (φ x) - Metric.infDist x Y|
          = |h' (φ x) - (Metric.infDist x Y - ℓ (φ x))| := by ring_nf
        _ ≤ a * (C * r) := this
        _ ≤ η := haδ
    · intro x hx x' hx'
      have h1 := hl (φ x) (φ x') (hsub x hx) (hsub x' hx')
      have h2 := hlip (φ x) ((hsub x hx) (Metric.mem_closedBall_self hrpos.le))
        (φ x') ((hsub x' hx') (Metric.mem_closedBall_self hrpos.le))
      rw [hhx x hx.1.1, hhx x' hx'.1.1] at h2
      have h3 := hchart x' hx'.2 x hx.2
      rw [dist_comm x' x] at h3
      calc |(h' (φ x) + ℓ (φ x) - Metric.infDist x Y) -
            (h' (φ x') + ℓ (φ x') - Metric.infDist x' Y)|
          = |(h' (φ x) - h' (φ x')) -
              ((Metric.infDist x Y - ℓ (φ x)) - (Metric.infDist x' Y - ℓ (φ x')))| := by
            ring_nf
        _ ≤ |h' (φ x) - h' (φ x')| +
              |(Metric.infDist x Y - ℓ (φ x)) - (Metric.infDist x' Y - ℓ (φ x'))| := abs_sub _ _
        _ ≤ a * N (φ x - φ x') + a * N (φ x - φ x') := add_le_add h1 h2
        _ = 2 * a * N (φ x - φ x') := by ring
        _ ≤ 2 * a * (κ * dist x x') := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = L * dist x x' := by rw [← h2aκ]; ring

end Bundle.ContMDiffRiemannianMetric
