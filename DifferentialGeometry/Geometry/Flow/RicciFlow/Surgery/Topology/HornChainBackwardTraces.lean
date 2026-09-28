import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.InverseSqrtScalarDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartTailHornBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Topology.Connected.Frontier

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_lt_of_mem_ball_chain (g : SmoothRiemannianMetric I M)
    {p : ℕ → M} {δ : ℕ → ℝ} {N : ℕ} (hδ : ∀ k ≤ N, 0 < δ k)
    (hch : ∀ k < N, p (k + 1) ∈ riemannianBallOf g (p k) (δ k)) :
    ∀ k ≤ N, ∀ w ∈ riemannianBallOf g (p k) (δ k),
      riemannianEDistOf g (p 0) w < ENNReal.ofReal (∑ i ∈ Finset.range (N + 1), δ i) := by
  have hS0 : ∀ j, j ≤ N → 0 ≤ ∑ i ∈ Finset.range (j + 1), δ i := fun j hj =>
    Finset.sum_nonneg fun i hi => (hδ i (by have := Finset.mem_range.mp hi; omega)).le
  have hchain : ∀ j ≤ N, ∀ w ∈ riemannianBallOf g (p j) (δ j),
      riemannianEDistOf g (p 0) w < ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), δ i) := by
    intro j
    induction j with
    | zero =>
      intro _ w hw
      rw [Finset.sum_range_one]
      exact hw
    | succ j ih =>
      intro hj w hw
      have hpj := ih (by omega) (p (j + 1)) (hch j (by omega))
      have hδj := hδ (j + 1) hj
      calc riemannianEDistOf g (p 0) w
          ≤ riemannianEDistOf g (p 0) (p (j + 1)) + riemannianEDistOf g (p (j + 1)) w :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), δ i) + ENNReal.ofReal (δ (j + 1)) :=
            ENNReal.add_lt_add hpj hw
        _ = ENNReal.ofReal (∑ i ∈ Finset.range (j + 1 + 1), δ i) := by
            rw [← ENNReal.ofReal_add (hS0 j (by omega)) hδj.le,
              Finset.sum_range_succ _ (j + 1)]
  intro k hk w hw
  refine (hchain k hk w hw).trans_le (ENNReal.ofReal_le_ofReal
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun i hi _ =>
      (hδ i (by have := Finset.mem_range.mp hi; omega)).le))

theorem isPreconnected_biUnion_riemannianBallOf_chain (g : SmoothRiemannianMetric I M)
    {p : ℕ → M} {δ : ℕ → ℝ} {N : ℕ} (hδ : ∀ k ≤ N, 0 < δ k)
    (hch : ∀ k < N, p (k + 1) ∈ riemannianBallOf g (p k) (δ k)) :
    IsPreconnected (⋃ j ∈ Iic N, riemannianBallOf g (p j) (δ j)) := by
  refine IsPreconnected.biUnion_of_chain ordConnected_Iic (fun j hj =>
    (DifferentialGeometry.isPathConnected_riemannianBallOf g (p j)
      (hδ j hj)).isConnected.isPreconnected) fun j _ hj1 => ?_
  rw [Order.succ_eq_add_one] at hj1 ⊢
  have hj1' : j + 1 ≤ N := hj1
  refine ⟨p (j + 1), hch j (by omega), ?_⟩
  change riemannianEDistOf g (p (j + 1)) (p (j + 1)) < ENNReal.ofReal (δ (j + 1))
  rw [riemannianEDistOf_self]
  exact ENNReal.ofReal_pos.mpr (hδ (j + 1) hj1')

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_forall_scalar_bounds_of_scalar_mem_Ioc
    (L : G.TerminalLimitMetric) {Ctime : ℝ≥0} {q m Mx : ℝ} (hq : 0 < q)
    (hder : G.DerivativeBoundBefore Ctime q s) (hqm : 2 * q < m) (hmM : m ≤ Mx) :
    ∀ᶠ τ in 𝓝[<] s, ∀ w : P.Carrier, m < G.flow.scalar τ w → G.flow.scalar τ w ≤ Mx →
      ∃ hw : w ∈ G.terminalRegularOpen, m / 2 ≤ metricScalarAt L.metric ⟨w, hw⟩ ∧
        metricScalarAt L.metric ⟨w, hw⟩ ≤ 2 * Mx := by
  have hm : 0 < m := by linarith
  have hMx : 0 < Mx := hm.trans_le hmM
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  have hwdt0 : 0 < 1 / (4 * Mx * ((Ctime : ℝ) + 1)) := by positivity
  filter_upwards [Ioo_mem_nhdsLT G.lt, Ioo_mem_nhdsLT (sub_lt_self s hwdt0)] with τ hτ hτw
  intro w hw1 hw2
  have hqw : q < G.flow.scalar τ w := by linarith
  have hRw : 0 < G.flow.scalar τ w := hq.trans hqw
  have hmaxτ : max q (G.flow.scalar τ w) = G.flow.scalar τ w := max_eq_right hqw.le
  have e1 : 1 / (4 * Mx) = 1 / Mx / 4 := by field_simp
  have e2 : 1 / (2 * Mx) = 1 / Mx / 2 := by field_simp
  have hgap : (Ctime : ℝ) * (s - τ) < 1 / Mx / 4 := by
    have h1 : s - τ < 1 / (4 * Mx * ((Ctime : ℝ) + 1)) := by linarith [hτw.1]
    have h2 : (Ctime : ℝ) * (s - τ) ≤ ((Ctime : ℝ) + 1) * (s - τ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [hτ.2])
    have h3 : ((Ctime : ℝ) + 1) * (s - τ) < ((Ctime : ℝ) + 1) *
        (1 / (4 * Mx * ((Ctime : ℝ) + 1))) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    have h4 : ((Ctime : ℝ) + 1) * (1 / (4 * Mx * ((Ctime : ℝ) + 1))) = 1 / Mx / 4 := by
      field_simp
    linarith
  have hinvM : 1 / Mx ≤ (G.flow.scalar τ w)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hRw hw2
  have hinvm : (G.flow.scalar τ w)⁻¹ < 1 / m := by
    rw [one_div]
    exact inv_strictAnti₀ hm hw1
  have hmM' : 1 / Mx ≤ 1 / m := one_div_le_one_div_of_le hm hmM
  have hMx0 : 0 < 1 / Mx := by positivity
  have hreg : w ∈ G.terminalRegularRegion := by
    refine G.mem_terminalRegularRegion_of_inv_max_scalar_gt hq hder hPhi hpinch hτ ?_
    rw [hmaxτ]
    have e3 : 4 * (Ctime : ℝ) * (s - τ) = 4 * ((Ctime : ℝ) * (s - τ)) := by ring
    linarith
  have hreg' : w ∈ G.terminalRegularOpen := hreg
  have hlip := G.lipschitzOnWith_inv_max_scalar hq hder w
  have hlim : Tendsto (fun t => metricScalarAt (G.flow.base.metric t) w) (𝓝[<] s)
      (𝓝 (metricScalarAt L.metric ⟨w, hreg'⟩)) := L.tendsto_metricScalarAt ⟨w, hreg'⟩
  have hnear : ∀ t ∈ Ioo τ s, |(max q (G.flow.scalar t w))⁻¹ - (G.flow.scalar τ w)⁻¹| <
      1 / Mx / 4 := by
    intro t ht
    have hd := hlip.dist_le_mul t ⟨hτ.1.trans ht.1, ht.2⟩ τ hτ
    rw [Real.dist_eq, Real.dist_eq, hmaxτ, abs_of_pos (sub_pos.mpr ht.1)] at hd
    have h2 : (Ctime : ℝ) * (t - τ) ≤ (Ctime : ℝ) * (s - τ) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.2]) Ctime.coe_nonneg
    linarith
  refine ⟨hreg', ge_of_tendsto hlim ?_, le_of_tendsto hlim ?_⟩
  · filter_upwards [Ioo_mem_nhdsLT hτ.2] with t ht
    have h := (abs_lt.mp (hnear t ht)).2
    have hpos : 0 < max q (G.flow.scalar t w) := hq.trans_le (le_max_left _ _)
    have hinv : (max q (G.flow.scalar t w))⁻¹ < 2 / m := by
      have : 2 / m = 1 / m + 1 / m := by ring
      linarith
    have hge : m / 2 < max q (G.flow.scalar t w) := by
      have h' := inv_strictAnti₀ (inv_pos.mpr hpos) hinv
      rwa [inv_inv, inv_div] at h'
    have hmx : max q (G.flow.scalar t w) = G.flow.scalar t w := by
      rcases le_total q (G.flow.scalar t w) with h1 | h1
      · exact max_eq_right h1
      · rw [max_eq_left h1] at hge
        linarith
    change m / 2 ≤ metricScalarAt (G.flow.base.metric t) w
    exact (hmx ▸ hge).le
  · filter_upwards [Ioo_mem_nhdsLT hτ.2] with t ht
    have h := (abs_lt.mp (hnear t ht)).1
    have hpos : 0 < max q (G.flow.scalar t w) := hq.trans_le (le_max_left _ _)
    have hinv : 1 / (2 * Mx) < (max q (G.flow.scalar t w))⁻¹ := by
      rw [e2]
      linarith
    have hle : max q (G.flow.scalar t w) < 2 * Mx := by
      have h' := inv_strictAnti₀ (by positivity) hinv
      rwa [inv_inv, one_div, inv_inv] at h'
    change metricScalarAt (G.flow.base.metric t) w ≤ 2 * Mx
    exact (le_max_right _ _).trans hle.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ}

theorem subset_hornHalfRange_of_isPreconnected_of_scalar_gt (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents D.slab.terminalRegularOpen} (hc : c ∈ P.component)
    {e : P.hornIndex c} {x : D.slab.terminalRegularOpen} (hx : x ∈ P.hornHalfRange c e)
    {S : Set D.slab.terminalRegularOpen} (hS : IsPreconnected S) (hxS : x ∈ S)
    (hscal : ∀ y ∈ S, Λ * (P.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric y) :
    S ⊆ P.hornHalfRange c e := by
  have hxc : ConnectedComponents.mk x = c := hornHalfRange_mk_eq P c e hx
  have hcomp : ∀ y ∈ S, ConnectedComponents.mk y = c := by
    intro y hy
    rw [← hxc]
    exact ConnectedComponents.coe_eq_coe'.mpr (hS.subset_connectedComponent hxS hy)
  have hxcore : x ∉ P.core c := by
    obtain ⟨⟨⟨y, t⟩, ht⟩, hxeq⟩ := hx
    rcases (show (0 : ℝ) ≤ t from ht).lt_or_eq with htpos | ht0
    · rw [← hxeq]
      exact P.horn_pos_notMem_core c e y htpos
    · subst ht0
      have hbase := P.horn_base_scalar c e y
      have h := hscal x hxS
      rw [← hxeq] at h
      exact absurd hbase (not_le.mpr h)
  have hcore : ∀ y ∈ S, y ∉ P.core c := by
    have hclosed : IsClosed (P.core c) := (P.core_isCompact c hc).isClosed
    have hsub :=
      DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
        (B := (P.core c)ᶜ) hS ?_ ⟨x, hxS, ?_⟩
    · intro y hy hyc
      exact (interior_subset (hsub hy)) hyc
    · rw [frontier_compl]
      refine Set.disjoint_left.mpr fun y hy hyf => ?_
      exact absurd (P.frontier_scalar_le c hc hyf) (not_le.mpr (hscal y hy))
    · rw [interior_compl, hclosed.closure_eq]
      exact hxcore
  obtain ⟨e', he'⟩ := P.exists_hornHalfRange_superset_of_isPreconnected hc hS ⟨x, hxS⟩ hcomp hcore
  have hee : e' = e := hornHalfRange_unique P (he' hxS) hx
  subst hee
  exact he'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

private theorem lt_scalar_of_mem_closedBall_of_gradientBoundBefore {P : OrientedThreeStage.{u}}
    {a s : ℝ} {G : P.IncomingSlab a s} {Cgrad : ℝ≥0} {qcan Dr τ : ℝ}
    (hgrad : G.GradientBoundBefore Cgrad qcan s) (hτ : τ ∈ Ioo a s) (hDr : 0 ≤ Dr)
    {x w : P.Carrier} (hx : 0 < G.flow.scalar τ x)
    (hqm : qcan < G.flow.scalar τ x / (2 * (1 + (Cgrad : ℝ) * Dr) ^ 2))
    (hw : w ∈ riemannianClosedBallOf (G.flow.base.metric τ) x
      (Dr / Real.sqrt (G.flow.scalar τ x))) :
    G.flow.scalar τ x / (2 * (1 + (Cgrad : ℝ) * Dr) ^ 2) < G.flow.scalar τ w := by
  set κ := 1 + (Cgrad : ℝ) * Dr with hκdef
  have hCD : 0 ≤ (Cgrad : ℝ) * Dr := mul_nonneg Cgrad.coe_nonneg hDr
  have hκ1 : 1 ≤ κ := by linarith
  have hsx : 0 < Real.sqrt (G.flow.scalar τ x) := Real.sqrt_pos.mpr hx
  by_contra hle
  push Not at hle
  have hmx : G.flow.scalar τ x / (2 * κ ^ 2) ≤ G.flow.scalar τ x :=
    div_le_self hx.le (by nlinarith)
  have key :=
    Perelman.CanonicalNeighborhood.inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound
      G.flow Cgrad.coe_nonneg hqm (fun z hz v => hgrad z τ hτ hz v) hmx hle
      (div_nonneg hDr hsx.le) hw
  have hsq : Real.sqrt (G.flow.scalar τ x / (2 * κ ^ 2)) =
      Real.sqrt (G.flow.scalar τ x) / (Real.sqrt 2 * κ) := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by linarith)]
  rw [hsq, inv_div] at key
  have key' : (Real.sqrt 2 * κ - 1) * (Real.sqrt (G.flow.scalar τ x))⁻¹ ≤
      ((Cgrad : ℝ) / 2 * Dr) * (Real.sqrt (G.flow.scalar τ x))⁻¹ := by
    calc (Real.sqrt 2 * κ - 1) * (Real.sqrt (G.flow.scalar τ x))⁻¹ =
          Real.sqrt 2 * κ / Real.sqrt (G.flow.scalar τ x) -
            (Real.sqrt (G.flow.scalar τ x))⁻¹ := by ring
      _ ≤ (Cgrad : ℝ) / 2 * (Dr / Real.sqrt (G.flow.scalar τ x)) := key
      _ = ((Cgrad : ℝ) / 2 * Dr) * (Real.sqrt (G.flow.scalar τ x))⁻¹ := by ring
  have h2 := le_of_mul_le_mul_right key' (inv_pos.mpr hsx)
  have hs2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [hκdef, mul_add, mul_one] at h2
  have h4 : 0 ≤ Real.sqrt 2 * ((Cgrad : ℝ) * Dr) - (Cgrad : ℝ) / 2 * Dr := by
    have : Real.sqrt 2 * ((Cgrad : ℝ) * Dr) - (Cgrad : ℝ) / 2 * Dr =
        (Real.sqrt 2 - 1 / 2) * ((Cgrad : ℝ) * Dr) := by ring
    rw [this]
    exact mul_nonneg (by linarith) hCD
  linarith

theorem eventually_chain_backward_traces_of_mem_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ (H : RetainedCoreHistory.{u}) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
      {εP Λ : ℝ}
      (P : TerminalCorePresentation
        { stage := H.stage (Fin.last H.eventCount)
          startTime := H.time (Fin.last H.eventCount)
          endTime := s
          startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
          startTime_lt_endTime := G.lt
          slab := G
          terminal := L
          singular := hsing
          parameters := parameters } εP Λ), εP ≤ eta →
    ∀ (c : ConnectedComponents G.terminalRegularOpen), c ∈ P.component →
    ∀ (e : P.hornIndex c) (x : G.terminalRegularOpen), x ∈ P.hornHalfRange c e →
    ∀ {ε ε₁ C1 C2 qcan : ℝ} {Ctime Cgrad : ℝ≥0}, 0 < ε → ε ≤ eta → 0 < qcan →
      H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1 C2 qcan s →
      G.DerivativeBoundBefore Ctime qcan s → G.GradientBoundBefore Cgrad qcan s →
    ∀ {Dr : ℝ}, 0 ≤ Dr →
      8 * max (4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹)) (max (Λ * (P.coreRadius ^ 2)⁻¹) qcan) *
          (1 + Cgrad * Dr) ^ 2 < metricScalarAt L.metric x →
    ∀ᶠ τ in 𝓝[<] s,
      ∀ (N : ℕ) (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ) (M : ℝ),
        p 0 = x.val → (∀ k ≤ N, 0 < δ k) →
        (∀ k < N, p (k + 1) ∈ riemannianBallOf (G.flow.base.metric τ) (p k) (δ k)) →
        (∀ k ≤ N, ∀ z ∈ riemannianBallOf (G.flow.base.metric τ) (p k) (δ k),
          G.flow.scalar τ z ≤ M) →
        G.flow.scalar τ x.val ≤ M → M ≤ Dr ^ 2 * G.flow.scalar τ x.val →
        ∑ k ∈ Finset.range (N + 1), δ k ≤ Dr / Real.sqrt (G.flow.scalar τ x.val) →
        ∀ k ≤ N, ∀ z ∈ riemannianBallOf (G.flow.base.metric τ) (p k) (δ k),
          ∃ first : Fin (H.eventCount + 1), H.time first ≤ τ - 1 / 5 / M ∧
            Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
              (Fin.le_last first) z) := by
  obtain ⟨eta, heta, hsn⟩ := eventually_forall_historyStrongNeck_of_subset_hornHalfRange.{u}
  refine ⟨eta, heta, ?_⟩
  intro H s G L hsing parameters εP Λ P hεP c hc e x hx ε ε₁ C1 C2 qcan Ctime Cgrad hε hεη hq
    hcan hder hgrad Dr hDr hbig
  set lam := Λ * (P.coreRadius ^ 2)⁻¹ with hlamdef
  set μ := max (4 * C2 * lam) (max lam qcan) with hμdef
  set κ := 1 + (Cgrad : ℝ) * Dr with hκdef
  set Rx := metricScalarAt L.metric x with hRxdef
  have hCD : 0 ≤ (Cgrad : ℝ) * Dr := mul_nonneg Cgrad.coe_nonneg hDr
  have hκ1 : 1 ≤ κ := by linarith
  have hμq : qcan ≤ μ := (le_max_right _ _).trans (le_max_right _ _)
  have hμl : lam ≤ μ := (le_max_left _ _).trans (le_max_right _ _)
  have hμC : 4 * C2 * lam ≤ μ := le_max_left _ _
  have hμ : 0 < μ := hq.trans_le hμq
  have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ1
  have hRx : 8 * μ * κ ^ 2 < Rx := hbig
  have hRxpos : 0 < Rx := lt_of_le_of_lt (by positivity) hRx
  set mlow := Rx / (4 * κ ^ 2) with hmlowdef
  have hmlow : 2 * μ < mlow := by
    rw [hmlowdef, lt_div_iff₀ (by positivity)]
    linarith
  set Mmax := 2 * (Dr ^ 2 + 1) * Rx with hMmaxdef
  have hmM : mlow ≤ Mmax := by
    have h1 : mlow ≤ Rx := div_le_self hRxpos.le (by linarith)
    have h2 : Rx ≤ 2 * (Dr ^ 2 + 1) * Rx := by nlinarith [sq_nonneg Dr]
    linarith
  have hcont : Continuous (metricScalarAt L.metric) := (metricScalar_smooth L.metric).continuous
  set B : Set G.terminalRegularOpen := P.hornHalfRange c e ∩
    {w | mlow / 2 ≤ metricScalarAt L.metric w ∧ metricScalarAt L.metric w ≤ 2 * Mmax} with hBdef
  have hBc : IsCompact B := by
    refine (L.isCompact_scalar_sublevel (2 * Mmax)).of_isClosed_subset ?_ fun w hw => hw.2.2
    have hhorn : IsClosed (P.hornHalfRange c e) := by
      simpa only [TerminalCorePresentation.hornHalfRange] using (P.horn_proper c e).isClosed_range
    exact hhorn.inter
      ((isClosed_le continuous_const hcont).inter (isClosed_le hcont continuous_const))
  have hsnB := hsn H (Fin.last H.eventCount) G L hsing parameters P hεP c e hBc
    (fun w hw => hw.1) hε hεη (fun w hw => by linarith [hw.2.1]) (fun w hw => by linarith [hw.2.1])
    hcan
  have hfwd := L.eventually_forall_scalar_bounds_of_scalar_mem_Ioc hq hder
    (by linarith : 2 * qcan < mlow) hmM
  filter_upwards [Ioo_mem_nhdsLT G.lt,
    (L.tendsto_metricScalarAt x).eventually
      (Ioo_mem_nhds (half_lt_self hRxpos) (by linarith : Rx < 2 * Rx)), hsnB, hfwd]
    with τ hτ hRτ hsnτ hfwdτ
  intro N p δ M hp0 hδ hch hb hxM hMle hsum k hk z hz
  have hRτx1 : Rx / 2 < G.flow.scalar τ x.val := hRτ.1
  have hRτx2 : G.flow.scalar τ x.val < 2 * Rx := hRτ.2
  have hRτxpos : 0 < G.flow.scalar τ x.val := by linarith
  have hMMmax : M ≤ Mmax := by
    have h1 : Dr ^ 2 * G.flow.scalar τ x.val ≤ Dr ^ 2 * (2 * Rx) :=
      mul_le_mul_of_nonneg_left hRτx2.le (sq_nonneg Dr)
    have h2 : Mmax = Dr ^ 2 * (2 * Rx) + 2 * Rx := by rw [hMmaxdef]; ring
    linarith
  have hqm : qcan < G.flow.scalar τ x.val / (2 * κ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    have h1 : qcan * (2 * κ ^ 2) ≤ μ * (2 * κ ^ 2) :=
      mul_le_mul_of_nonneg_right hμq (by positivity)
    linarith
  have hmlowτ : mlow ≤ G.flow.scalar τ x.val / (2 * κ ^ 2) := by
    rw [hmlowdef, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set S : Set (H.stage (Fin.last H.eventCount)).Carrier :=
    ⋃ j ∈ Iic N, riemannianBallOf (G.flow.base.metric τ) (p j) (δ j) with hSdef
  have hSbounds : ∀ w ∈ S, mlow < G.flow.scalar τ w ∧ G.flow.scalar τ w ≤ Mmax := by
    intro w hw
    obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp hw
    have hd := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_lt_of_mem_ball_chain
      (G.flow.base.metric τ) hδ hch j hj w hwj
    rw [hp0] at hd
    have hmem : w ∈ riemannianClosedBallOf (G.flow.base.metric τ) x.val
        (Dr / Real.sqrt (G.flow.scalar τ x.val)) :=
      hd.le.trans (ENNReal.ofReal_le_ofReal hsum)
    exact ⟨hmlowτ.trans_lt (lt_scalar_of_mem_closedBall_of_gradientBoundBefore hgrad hτ hDr
      hRτxpos hqm hmem), (hb j hj w hwj).trans hMMmax⟩
  have hSΩ : ∀ w ∈ S, w ∈ G.terminalRegularOpen := fun w hw =>
    (hfwdτ w (hSbounds w hw).1 (hSbounds w hw).2).1
  set S' : Set G.terminalRegularOpen := Subtype.val ⁻¹' S with hS'def
  have hS'pre : IsPreconnected S' := by
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
    convert DifferentialGeometry.Geometry.Metric.isPreconnected_biUnion_riemannianBallOf_chain
      (G.flow.base.metric τ) hδ hch using 1
    ext w
    constructor
    · rintro ⟨w', hw', rfl⟩
      exact hw'
    · intro hw
      exact ⟨⟨w, hSΩ w hw⟩, hw, rfl⟩
  have hS'bounds : ∀ w ∈ S', mlow / 2 ≤ metricScalarAt L.metric w ∧
      metricScalarAt L.metric w ≤ 2 * Mmax := by
    intro w hw
    obtain ⟨_, h1, h2⟩ := hfwdτ w.val (hSbounds w.val hw).1 (hSbounds w.val hw).2
    exact ⟨h1, h2⟩
  have hxS' : x ∈ S' := by
    change x.val ∈ S
    rw [← hp0]
    refine mem_iUnion₂.mpr ⟨0, Nat.zero_le N, ?_⟩
    change riemannianEDistOf (G.flow.base.metric τ) (p 0) (p 0) < ENNReal.ofReal (δ 0)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (hδ 0 (Nat.zero_le N))
  have hS'horn : S' ⊆ P.hornHalfRange c e :=
    P.subset_hornHalfRange_of_isPreconnected_of_scalar_gt hc hx hS'pre hxS' fun y hy => by
      linarith [(hS'bounds y hy).1]
  have hzS : z ∈ S := mem_iUnion₂.mpr ⟨k, hk, hz⟩
  have hz'S' : (⟨z, hSΩ z hzS⟩ : G.terminalRegularOpen) ∈ S' := hzS
  have hz'B : (⟨z, hSΩ z hzS⟩ : G.terminalRegularOpen) ∈ B :=
    ⟨hS'horn hz'S', hS'bounds _ hz'S'⟩
  obtain ⟨first, hle, -, -, hdepth, -, -, -, zz, hzz, -⟩ := hsnτ _ hz'B
  have hRz : 0 < G.flow.scalar τ z := by linarith [(hSbounds z hzS).1]
  have hRzM : G.flow.scalar τ z ≤ M := hb k hk z hz
  refine ⟨first, hdepth.trans ?_, ?_⟩
  · have hinv : 1 / 5 / M ≤ 1 / 5 * (G.flow.scalar τ z)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hRz hRzM) (by norm_num)
    linarith
  · have hmem := zz.property
    rw [hzz] at hmem
    exact hmem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
