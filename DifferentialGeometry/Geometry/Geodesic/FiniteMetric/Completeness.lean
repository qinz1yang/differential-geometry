import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.FlowLemmas
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow

/-!
# Completeness of the geodesic flow of a complete finite-regularity metric (CM2.b, flow part)

For `g : ContMDiffRiemannianMetric I (r + 1)` with `1 ≤ r` on a manifold whose distance is the
Riemannian distance of a bundle metric with the norm of `g` (`hnorm`), completeness of the distance
implies that the ported geodesic flow is defined for all times
(`geodesicFlowDomain_eq_univ_of_one_le`; frozen-regularity form `geodesicFlowDomain_eq_univ`).

Escape argument: if the maximal interval of an orbit had a finite supremum `b`, the orbit would stay
on `[0, b)` in a compact ball (`Manifold.properSpace_of_isRiemannianManifold`, speed bound
`dist_proj_geodesicFlow_le`) with constant speed (CM1.b); in the tangent chart at a limit point the
velocity coordinates are bounded (uniform coercivity of the chart coefficients,
`exists_pos_eventually_le_of_isCoercive`), so the orbit has a cluster point in `TM` at `b⁻`, which
TauCeti's escape lemma `not_mapClusterPt_nhdsLT_maximalIntegralCurve` forbids. No normal charts are
needed. Corollary: the Lipschitz bound `dist_expMap_smul_le_of_completeSpace`.
Lane CM-H, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Bundle.ContMDiffRiemannianMetric

section Kernel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance completeFlowBilinNormedGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Coercivity is uniform near a point of continuity. -/
theorem exists_pos_eventually_le_of_isCoercive {X : Type*} [TopologicalSpace X] {b : X → F →L[ℝ] F →L[ℝ] ℝ} {y : X}
    (hb : ContinuousAt b y) (hco : IsCoercive (b y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y' in 𝓝 y, ∀ v : F, C * ‖v‖ ^ 2 ≤ b y' v v := by
  obtain ⟨C, hC, hCv⟩ := hco
  refine ⟨C / 2, half_pos hC, ?_⟩
  filter_upwards [hb.eventually (Metric.ball_mem_nhds (b y) (half_pos hC))] with y' hy' v
  rw [dist_eq_norm] at hy'
  have hle : |(b y' - b y) v v| ≤ ‖b y' - b y‖ * ‖v‖ * ‖v‖ :=
    (Real.norm_eq_abs _).symm.le.trans ((b y' - b y).le_opNorm₂ v v)
  have hsplit : b y' v v = b y v v + (b y' - b y) v v := by
    simp only [sub_apply]; ring
  have h1 := hCv v
  have h2 : ‖b y' - b y‖ * ‖v‖ * ‖v‖ ≤ C / 2 * ‖v‖ * ‖v‖ := by
    have := mul_nonneg (norm_nonneg v) (norm_nonneg v)
    nlinarith
  nlinarith [abs_le.mp hle, norm_nonneg v]

end Kernel

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Reading of the tangent-bundle chart. -/
theorem extChartAt_tangent_apply_eq (a p : TangentBundle I M)
    (hp : p.proj ∈ (chartAt H a.proj).source) :
    extChartAt I.tangent a p =
      (extChartAt I a.proj p.proj, mfderiv I 𝓘(ℝ, E) (extChartAt I a.proj) p.proj p.snd) := by
  apply Prod.ext
  · exact TangentBundle.extChartAt_tangent_apply_fst a
  · rw [TangentBundle.extChartAt_tangent_apply_snd a hp,
      TangentBundle.continuousLinearMapAt_trivializationAt hp]
    rfl

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- **The flow of a complete finite metric is complete forward in time.** The maximal interval
of every orbit is unbounded above: on a bounded interval the orbit stays in a compact ball with
constant speed, so it has a cluster point in `TM` (uniform coercivity of the chart coefficients),
which the escape lemma forbids. Only `C²` regularity is used. -/
theorem not_bddAbove_maximalIntegralCurveInterval [CompleteSpace M] (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) :
    ¬ BddAbove (maximalIntegralCurveInterval g.geodesicSpray p) := by
  intro hbdd
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hv : ContMDiff I.tangent I.tangent.tangent 1
      (fun q : TangentBundle I M =>
        (⟨q, g.geodesicSpray q⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr)
  set J := maximalIntegralCurveInterval g.geodesicSpray p with hJ
  have hmem : ∀ σ, σ ∈ J ↔ (p, σ) ∈ g.geodesicFlowDomain := fun σ => Iff.rfl
  have h0 : (0 : ℝ) ∈ J := (hmem 0).mpr (g.mem_geodesicFlowDomain_zero hr p)
  have hconn : J.OrdConnected := ordConnected_maximalIntegralCurveInterval
  have hopen : IsOpen J := isOpen_maximalIntegralCurveInterval
  set b := sSup J with hb_def
  have hlub : IsLUB J b := isLUB_csSup ⟨0, h0⟩ hbdd
  have hbJ : b ∉ J := by
    intro hb
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen b hb
    have : b + ε / 2 ∈ J := hball (by rw [mem_ball, Real.dist_eq]; rw [abs_of_pos] <;> linarith)
    linarith [hlub.1 this]
  have hb0 : 0 < b := lt_of_le_of_ne (hlub.1 h0) (fun h => hbJ (h ▸ h0))
  obtain ⟨u, -, hub, hut, huJ⟩ := hlub.exists_seq_strictMono_tendsto_of_notMem hbJ ⟨0, h0⟩
  set σ : ℕ → ℝ := fun n => max (u n) 0 with hσ
  have hσJ : ∀ n, σ n ∈ J := fun n => by
    rcases le_total (u n) 0 with h | h
    · simp only [hσ, max_eq_right h]; exact h0
    · simp only [hσ, max_eq_left h]; exact huJ n
  have hσnn : ∀ n, 0 ≤ σ n := fun n => le_max_right _ _
  have hσb : ∀ n, σ n < b := fun n => max_lt (hub n) hb0
  have hσt : Tendsto σ atTop (𝓝[<] b) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hσb⟩
    have := hut.max (tendsto_const_nhds (x := (0 : ℝ)))
    rwa [max_eq_left hb0.le] at this
  set c := Real.sqrt (g.inner p.proj p.snd p.snd) with hc
  have hpos : ∀ n, (g.geodesicFlow p (σ n)).proj ∈ closedBall p.proj (c * b) := by
    intro n
    have hsub : ∀ τ ∈ uIcc 0 (σ n), (p, τ) ∈ g.geodesicFlowDomain := by
      intro τ hτ
      rw [uIcc_of_le (hσnn n)] at hτ
      exact (hmem τ).mp (hconn.out h0 (hσJ n) hτ)
    have hd := g.dist_proj_geodesicFlow_le hr hnorm hsub
    rw [g.geodesicFlow_zero hr p, sub_zero, abs_of_nonneg (hσnn n)] at hd
    rw [mem_closedBall, dist_comm]
    exact hd.trans (mul_le_mul_of_nonneg_left (hσb n).le (Real.sqrt_nonneg _))
  obtain ⟨y, -, ψ, hψ, hy⟩ := (isCompact_closedBall p.proj (c * b)).tendsto_subseq hpos
  set q : ℕ → TangentBundle I M := fun k => g.geodesicFlow p (σ (ψ k)) with hq
  have hy' : Tendsto (fun k => (q k).proj) atTop (𝓝 y) := hy
  have hsrc : ∀ᶠ k in atTop, (q k).proj ∈ (chartAt H y).source :=
    hy' ((chartAt H y).open_source.mem_nhds (mem_chart_source H y))
  have hκ : Tendsto (fun k => extChartAt I y (q k).proj) atTop (𝓝 (extChartAt I y y)) :=
    ((continuousAt_extChartAt y).tendsto).comp hy'
  have hBc : ContinuousAt (g.chartInner y) (extChartAt I y y) :=
    ((g.contDiffOn_chartInner y).continuousOn).continuousAt
      ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
  obtain ⟨C, hC, hCev⟩ := exists_pos_eventually_le_of_isCoercive hBc
    (g.isCoercive_chartInner y (mem_extChartAt_target y))
  set V : ℕ → E := fun k => mfderiv I 𝓘(ℝ, E) (extChartAt I y) (q k).proj (q k).snd with hV
  have hVb : ∀ᶠ k in atTop, V k ∈ closedBall (0 : E) (c / Real.sqrt C) := by
    filter_upwards [hsrc, hκ hCev] with k hk hck
    have hspeed := g.inner_geodesicFlow_eq hr p (σ (ψ k)) ((hmem _).mp (hσJ (ψ k)))
    rw [g.inner_eq_chartInner hk] at hspeed
    have h1 := hck (V k)
    change C * ‖V k‖ ^ 2 ≤ g.chartInner y (extChartAt I y (q k).proj) (V k) (V k) at h1
    have hgnn : 0 ≤ g.inner p.proj p.snd p.snd := by
      by_cases hz : p.snd = 0
      · rw [hz]; simp
      · exact (g.pos p.proj p.snd hz).le
    rw [mem_closedBall_zero_iff, le_div_iff₀ (Real.sqrt_pos.mpr hC), hc,
      Real.le_sqrt (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hgnn, mul_pow,
      Real.sq_sqrt hC.le, ← hspeed]
    linarith
  obtain ⟨Vlim, -, ψ₂, hψ₂, hVlim⟩ := (isCompact_closedBall (0 : E) _).tendsto_subseq' hVb.frequently
  set T := extChartAt I.tangent (⟨y, 0⟩ : TangentBundle I M) with hT
  set z : TangentBundle I M := ⟨y, Vlim⟩ with hz
  have hzsrc : z ∈ T.source := by
    simpa only [hT, extChartAt_source, TangentBundle.mem_chart_source_iff] using
      mem_chart_source H y
  have hTz : T z = (extChartAt I y y, Vlim) := by
    rw [hT, extChartAt_tangent_apply_eq _ _ (mem_chart_source H y)]
    change (extChartAt I y y, mfderiv I 𝓘(ℝ, E) (extChartAt I y) y Vlim) = _
    rw [mfderiv_extChartAt_self]
    rfl
  have hTq : ∀ᶠ k in atTop, T (q k) = (extChartAt I y (q k).proj, V k) :=
    hsrc.mono fun k hk => extChartAt_tangent_apply_eq _ _ hk
  have hTlim : Tendsto (fun j => T (q (ψ₂ j))) atTop (𝓝 (T z)) := by
    rw [hTz]
    refine Tendsto.congr' ((hψ₂.tendsto_atTop.eventually hTq).mono fun j hj => hj.symm) ?_
    exact (hκ.comp hψ₂.tendsto_atTop).prodMk_nhds hVlim
  have hqsrc : ∀ᶠ j in atTop, q (ψ₂ j) ∈ T.source :=
    hψ₂.tendsto_atTop.eventually (hsrc.mono fun k hk => (show q k ∈ T.source by
      simpa only [hT, extChartAt_source, TangentBundle.mem_chart_source_iff] using hk))
  have hqz : Tendsto (fun j => q (ψ₂ j)) atTop (𝓝 z) := by
    have hcont : ContinuousAt T.symm (T z) :=
      continuousAt_extChartAt_symm'' (T.map_source hzsrc)
    have h := hcont.tendsto.comp hTlim
    rw [T.left_inv hzsrc] at h
    refine h.congr' ?_
    filter_upwards [hqsrc] with j hj
    exact T.left_inv hj
  have hcl : MapClusterPt z (𝓝[<] b) (maximalIntegralCurve g.geodesicSpray p) :=
    MapClusterPt.of_comp (hσt.comp (hψ.tendsto_atTop.comp hψ₂.tendsto_atTop))
      (Tendsto.mapClusterPt hqz)
  exact not_mapClusterPt_nhdsLT_maximalIntegralCurve hv h0 hlub z hcl

/-- **CM2.b, completeness of the flow** (`C²` metrics suffice): the ported geodesic flow of a
complete finite metric is defined for all times. -/
theorem geodesicFlowDomain_eq_univ_of_one_le [CompleteSpace M] (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    g.geodesicFlowDomain = univ := by
  refine eq_univ_of_forall fun q => ?_
  obtain ⟨p, t⟩ := q
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval g.geodesicSpray p :=
    g.mem_geodesicFlowDomain_zero hr p
  have hup := not_bddAbove_maximalIntegralCurveInterval g hr hnorm p
  have hlow : ¬ BddBelow (maximalIntegralCurveInterval g.geodesicSpray p) := by
    rintro ⟨m, hm⟩
    apply not_bddAbove_maximalIntegralCurveInterval g hr hnorm ⟨p.proj, (-1 : ℝ) • p.snd⟩
    refine ⟨-m, fun σ hσ => ?_⟩
    have h := (geodesicFlow_smul (g := g) hr (p := p) (s := -1) (t := σ)).mp hσ
    have := hm h
    linarith
  have huniv := maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow h0 hup hlow
  change t ∈ maximalIntegralCurveInterval g.geodesicSpray p
  rw [huniv]
  exact mem_univ t

/-- **CM2.b, completeness of the flow**, frozen regularity (`hr : 2 ≤ r`). -/
theorem geodesicFlowDomain_eq_univ [CompleteSpace M] (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    g.geodesicFlowDomain = univ :=
  g.geodesicFlowDomain_eq_univ_of_one_le (one_le_two.trans hr) hnorm

/-- Lipschitz bound for radial geodesics of a complete finite metric:
`d(exp_x (s v), exp_x (t v)) ≤ |v|_g |t - s|` (finite-order form of the smooth
`maximalGeodesic_edist_le_speed_mul_time`). -/
theorem dist_expMap_smul_le_of_completeSpace [CompleteSpace M] (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {x : M} (v : TangentSpace I x) (s t : ℝ) :
    dist (g.expMap (⟨x, s • v⟩ : TangentBundle I M)) (g.expMap (⟨x, t • v⟩ : TangentBundle I M)) ≤
      Real.sqrt (g.inner x v v) * |t - s| :=
  g.dist_expMap_smul_le hr hnorm v fun τ _ => by
    rw [g.geodesicFlowDomain_eq_univ_of_one_le hr hnorm]
    exact mem_univ _

end Bundle.ContMDiffRiemannianMetric
