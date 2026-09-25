import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapTraceExclusion
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallChart
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance terminal_regular_sigmaCompact (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem exists_stage_covering_time_before
    (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ first : Fin (H.eventCount + 1), first ≤ last ∧ H.time first ≤ t ∧
      ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → t < H.time j.succ := by
  by_cases hlast : H.time last ≤ t
  · refine ⟨last,le_rfl,hlast,?_⟩
    intro j hj hnext
    exact False.elim ((not_le_of_gt j.castSucc_lt_succ) (hnext.trans hj))
  · let tH : Icc (0 : ℝ) H.horizon := ⟨t,ht,(not_le.mp hlast).le.trans (H.time_le_horizon_at last)⟩
    have hle : H.activeStage tH ≤ last := by
      apply H.time_strictMono.le_iff_le.mp
      exact (H.activeStage_time_le tH).trans (not_le.mp hlast).le
    refine ⟨H.activeStage tH,hle,H.activeStage_time_le tH,?_⟩
    intro j hj hnext
    have hn : (H.activeStage tH).val < H.eventCount := lt_of_le_of_lt hj j.isLt
    exact (H.activeStage_before_next tH hn).trans_le
      (H.time_strictMono.monotone (show (⟨(H.activeStage tH).val + 1,by omega⟩ : Fin (H.eventCount+1)) ≤ j.succ from
        Nat.succ_le_succ hj))

theorem exists_eventually_backward_traces_on_compact_of_pointed_product_limit
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hQlim : Tendsto Q atTop atTop) {a : ℝ} (ha : 0 < a) (hsa : ∀ i, a ≤ s i) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i => {
          M := (G i).terminalRegularOpen
          basepoint := x i
          metric := scaleMetric (Q i) (hQ i) (L i).metric } };
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (subseq : ℕ → ℕ), StrictMono subseq →
    ∀ (Phi : PointedRiemannianConvergenceMaps X P subseq) (Cm : MetricConvergenceData Phi),
    (∀ i, Cm.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) →
    MetricComplete P →
    ∀ {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
      [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
      [T2Space N] [ConnectedSpace N]
      (hprod : SmoothRiemannianMetric J N), Module.finrank ℝ F = 2 →
    ∀ e : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), ThreeModel⟯ P.M,
    Diffeomorph.pullbackMetricCross P.metric e = hprod.prod (euclideanMetric (E := ℝ)) →
    ∀ (K : Set P.M), IsCompact K →
    (∀ y ∈ K, 0 < metricScalarAt P.metric y) →
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (subseq i)).eventCount + 1),
      ∃ hle : first ≤ last (subseq i),
        (H (subseq i)).time first ≤ s (subseq i) - θ / Q (subseq i) ∧
        0 ≤ s (subseq i) - θ / Q (subseq i) ∧
        ∀ y ∈ K, Nonempty (BackwardPointTrace (H (subseq i)) first (last (subseq i)) hle
          (Phi.map i y).val) := by
  intro X P subseq hsubseq Phi Cm hcanonical hcomplete
    F H' M hnorm hspace hfinite htop J hboundary hMtop hMchart hMsmooth hMt2 hMconn
    hprod hdim e he K hK hpositive
  let projection := fun z : P.M => (e.symm z).1
  have hprojection : Function.Surjective projection := fun z => ⟨e (z, 0),by simp [projection]⟩
  let _ : SigmaCompactSpace M := isSigmaCompact_univ_iff.mp (by
    rw [← hprojection.range_eq]
    exact isSigmaCompact_range (continuous_fst.comp e.symm.continuous))
  have hPconn : ConnectedSpace P.M := by
    exact e.toHomeomorph.connectedSpace_iff.mp inferInstance
  let _ : ConnectedSpace P.M := hPconn
  have hdistCont : Continuous (fun y : P.M => (riemannianEDistOf P.metric P.basepoint y).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top P.metric P.basepoint y)).comp
      (Geometry.Riemannian.continuous_riemannianEDist P.metric P.basepoint).continuousAt
  obtain ⟨A₀,hA₀⟩ := hK.bddAbove_image hdistCont.continuousOn
  let A : ℝ := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hKA : K ⊆ riemannianClosedBallOf P.metric P.basepoint A := by
    intro y hy
    apply (ENNReal.toReal_le_toReal (riemannianEDistOf_ne_top P.metric P.basepoint y) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hA]
    exact (hA₀ ⟨y,hy,rfl⟩).trans (le_max_left _ _)
  obtain ⟨c,B,hc,hB,hcB,hscalar⟩ :=
    Perelman.KappaSolutions.exists_positive_pointed_scalar_bounds_on_compact Phi Cm hcanonical K hK hpositive
  obtain ⟨θ,Qmin,R,εprod,ε₀,δ₀,hθ,hQmin,hR,hεprod,hεquarter,hε₀,hεhalf,hδ₀,htrace⟩ :=
    ObservedHistory.exists_uniform_backward_trace_of_prepared_caps_and_product_chart_of_scalar_bounds
      D r eps a₀ c B Ctime ha₀ hc hB heps hepssmall hr hfit
  have hclosed : RiemannianMetricComplete P.metric := ⟨hcomplete⟩
  obtain ⟨O,hO,hcharts⟩ := exists_eventually_fixed_domain_diffeomorph_capturing_balls
    Phi Cm hcanonical e P.basepoint hA hR.le
    (by linarith : 2 * (2 * A + R) < 2 * (2 * A + R) + 1)
    (hclosed.closedEBall_isCompact P.basepoint (2 * (2 * A + R) + 1))
  refine ⟨θ,ε₀,δ₀,hθ,hε₀,hδ₀,?_⟩
  intro parameters records hfixed hlower hdelta haccuracy hmargin hm q₀ hq₀ hderiv hfinal
    hcap center precision order d w Jbig hJbig hzero hmark
  have hlarge : ∀ᶠ i in atTop,
      Qmin ≤ Q (subseq i) ∧ 2 * q₀ < c * Q (subseq i) ∧ θ / Q (subseq i) ≤ a := by
    have hQsub : Tendsto (fun i => Q (subseq i)) atTop atTop := hQlim.comp hsubseq.tendsto_atTop
    filter_upwards [hQsub.eventually (eventually_ge_atTop Qmin),
      hQsub.eventually (eventually_gt_atTop (2 * q₀ / c)),
      hQsub.eventually (eventually_ge_atTop (θ / a))] with i h₁ h₂ h₃
    refine ⟨h₁,?_,?_⟩
    · have hh := (div_lt_iff₀ hc).mp h₂
      nlinarith
    · apply (div_le_iff₀ (hQ (subseq i))).mpr
      have hh := (div_le_iff₀ ha).mp h₃
      nlinarith
  filter_upwards [hscalar,hcharts 2 εprod hεprod,hlarge,
    hsubseq.tendsto_atTop.eventually hdelta,hsubseq.tendsto_atTop.eventually haccuracy]
      with i hsc hchart hlargei hdi hacc
  obtain ⟨V,Ψ,hΨ,hcapture,hjets⟩ := hchart
  have hnonneg : 0 ≤ s (subseq i) - θ / Q (subseq i) :=
    sub_nonneg.mpr (hlargei.2.2.trans (hsa (subseq i)))
  obtain ⟨first,hle,hfirst,hcross⟩ := exists_stage_covering_time_before
    (H (subseq i)) (last (subseq i)) hnonneg
  refine ⟨first,hle,hfirst,hnonneg,?_⟩
  intro y hy
  have hlo : c * Q (subseq i) ≤ metricScalarAt (L (subseq i)).metric (Phi.map i y) := by
    have hh := (hsc.2 y hy).1
    change c ≤ metricScalarAt (scaleMetric (Q (subseq i)) (hQ (subseq i)) (L (subseq i)).metric) (Phi.map i y) at hh
    rw [metricScalarAt_scaleMetric,← div_eq_inv_mul] at hh
    exact (le_div_iff₀ (hQ (subseq i))).mp hh
  have hhi : metricScalarAt (L (subseq i)).metric (Phi.map i y) ≤ B * Q (subseq i) := by
    have hh := (hsc.2 y hy).2
    change metricScalarAt (scaleMetric (Q (subseq i)) (hQ (subseq i)) (L (subseq i)).metric) (Phi.map i y) ≤ B at hh
    rw [metricScalarAt_scaleMetric,← div_eq_inv_mul] at hh
    exact (div_le_iff₀ (hQ (subseq i))).mp hh
  apply htrace (H (subseq i)) first (last (subseq i)) hle (s (subseq i))
    (G (subseq i)) (L (subseq i)) (hinit (subseq i))
    (parameters (subseq i)) (records (subseq i)) (hfixed (subseq i)) (hlower (subseq i))
    (fun j _ hj b => hdi j hj b) q₀ (Q (subseq i)) hq₀ (hQ (subseq i)) hlargei.1
    (fun j _ hj => hderiv (subseq i) j hj) (hfinal (subseq i)) hcross (hmargin (subseq i))
    (hm (subseq i)) hacc (fun j _ _ b => (records (subseq i) j).static b)
    (fun j _ hj => hcap (subseq i) j hj)
    (fun j _ hj => center (subseq i) j hj) (fun j _ hj => precision (subseq i) j hj)
    (fun j _ hj => order (subseq i) j hj) (fun j _ hj => d (subseq i) j hj)
    (fun j _ hj => w (subseq i) j hj) (fun j _ hj => Jbig (subseq i) j hj)
    (fun j _ hj => hJbig (subseq i) j hj) (fun j _ hj => hzero (subseq i) j hj) ?_
    (Phi.map i y) hlo hhi (hlargei.2.1.trans_le hlo) hprod hdim O V Ψ ?_ ?_
  · intro j hf hj b z
    obtain ⟨v,hv,hvmark⟩ := hmark (subseq i) j hj b z
    have hD : StandardCap.transitionEnd < D + 1 := by
      have hri : 0 < r := by linarith [StandardCap.transitionEnd_pos,inv_pos.mpr heps]
      have hi : 0 < eps⁻¹ := inv_pos.mpr heps
      nlinarith [StandardCap.transitionEnd_pos]
    let u : standardCapWindow D := ⟨v.val,hv.trans_lt hD⟩
    exact ⟨u,hv,hvmark⟩
  · intro z hz
    have hz' : z ∈ riemannianClosedBallOf (X.obj (subseq i)).metric (Phi.map i y) R := by
      change riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i y) z ≤ ENNReal.ofReal R
      exact le_of_lt (show riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i y) z < ENNReal.ofReal R from hz)
    exact hcapture y (hKA hy) hz'
  · intro z n hn
    have hh := (hjets z n hn).le
    rw [he] at hh
    exact hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] terminal_regular_sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_common_backward_trace_window_of_pointed_product_limit
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hQlim : Tendsto Q atTop atTop) {a : ℝ} (ha : 0 < a) (hsa : ∀ i, a ≤ s i) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i => {
          M := (G i).terminalRegularOpen
          basepoint := x i
          metric := scaleMetric (Q i) (hQ i) (L i).metric } };
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (subseq : ℕ → ℕ), StrictMono subseq →
    ∀ (Phi : PointedRiemannianConvergenceMaps X P subseq) (Cm : MetricConvergenceData Phi),
    (∀ i, Cm.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) →
    MetricComplete P →
    ∀ {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
      [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
      [T2Space N] [ConnectedSpace N]
      (hprod : SmoothRiemannianMetric J N), Module.finrank ℝ F = 2 →
    ∀ e : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), ThreeModel⟯ P.M,
    Diffeomorph.pullbackMetricCross P.metric e = hprod.prod (euclideanMetric (E := ℝ)) →
    ∀ B₀ : ℝ, 0 < B₀ → (∀ y, metricScalarAt P.metric y ≤ B₀) →
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (K : Set P.M), IsCompact K → (∀ y ∈ K, 0 < metricScalarAt P.metric y) →
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (subseq i)).eventCount + 1),
      ∃ hle : first ≤ last (subseq i),
        (H (subseq i)).time first ≤ s (subseq i) - θ / Q (subseq i) ∧
        0 ≤ s (subseq i) - θ / Q (subseq i) ∧
        ∀ y ∈ K, Nonempty (BackwardPointTrace (H (subseq i)) first (last (subseq i)) hle
          (Phi.map i y).val) := by
  intro X P subseq hsubseq Phi Cm hcanonical hcomplete
    F H' M hnorm hspace hfinite htop J hboundary hMtop hMchart hMsmooth hMt2 hMconn
    hprod hdim e he B₀ hB₀ hupper
  obtain ⟨θ,ε₀,δ₀,hθ,hε₀,hεhalf,hδ₀,hall⟩ :=
    ObservedHistory.exists_uniform_backward_trace_of_prepared_caps_and_product_chart_of_scalar_upper_bound
      D r eps a₀ (B₀ + 1) Ctime ha₀ (by positivity) heps hepssmall hr hfit
  refine ⟨θ,ε₀,δ₀,hθ,hε₀,hδ₀,?_⟩
  intro K hK hpositive
  let projection := fun z : P.M => (e.symm z).1
  have hprojection : Function.Surjective projection := fun z => ⟨e (z, 0),by simp [projection]⟩
  let _ : SigmaCompactSpace M := isSigmaCompact_univ_iff.mp (by
    rw [← hprojection.range_eq]
    exact isSigmaCompact_range (continuous_fst.comp e.symm.continuous))
  have hPconn : ConnectedSpace P.M := by
    exact e.toHomeomorph.connectedSpace_iff.mp inferInstance
  let _ : ConnectedSpace P.M := hPconn
  have hdistCont : Continuous (fun y : P.M => (riemannianEDistOf P.metric P.basepoint y).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top P.metric P.basepoint y)).comp
      (Geometry.Riemannian.continuous_riemannianEDist P.metric P.basepoint).continuousAt
  obtain ⟨A₀,hA₀⟩ := hK.bddAbove_image hdistCont.continuousOn
  let A : ℝ := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hKA : K ⊆ riemannianClosedBallOf P.metric P.basepoint A := by
    intro y hy
    apply (ENNReal.toReal_le_toReal (riemannianEDistOf_ne_top P.metric P.basepoint y) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hA]
    exact (hA₀ ⟨y,hy,rfl⟩).trans (le_max_left _ _)
  obtain ⟨c,B,hc,hB,hcB,hscalar⟩ :=
    Perelman.KappaSolutions.exists_positive_pointed_scalar_bounds_on_compact Phi Cm hcanonical K hK hpositive
  obtain ⟨Nupper,hNupper⟩ := Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    Cm hcanonical K hK 1 zero_lt_one
  obtain ⟨Qmin,R,εprod,hQmin,hR,hεprod,hεquarter,htrace⟩ := hall c hc
  have hclosed : RiemannianMetricComplete P.metric := ⟨hcomplete⟩
  obtain ⟨O,hO,hcharts⟩ := exists_eventually_fixed_domain_diffeomorph_capturing_balls
    Phi Cm hcanonical e P.basepoint hA hR.le
    (by linarith : 2 * (2 * A + R) < 2 * (2 * A + R) + 1)
    (hclosed.closedEBall_isCompact P.basepoint (2 * (2 * A + R) + 1))
  intro parameters records hfixed hlower hdelta haccuracy hmargin hm q₀ hq₀ hderiv hfinal
    hcap center precision order d w Jbig hJbig hzero hmark
  have hlarge : ∀ᶠ i in atTop,
      Qmin ≤ Q (subseq i) ∧ 2 * q₀ < c * Q (subseq i) ∧ θ / Q (subseq i) ≤ a := by
    have hQsub : Tendsto (fun i => Q (subseq i)) atTop atTop := hQlim.comp hsubseq.tendsto_atTop
    filter_upwards [hQsub.eventually (eventually_ge_atTop Qmin),
      hQsub.eventually (eventually_gt_atTop (2 * q₀ / c)),
      hQsub.eventually (eventually_ge_atTop (θ / a))] with i h₁ h₂ h₃
    refine ⟨h₁,?_,?_⟩
    · have hh := (div_lt_iff₀ hc).mp h₂
      nlinarith
    · apply (div_le_iff₀ (hQ (subseq i))).mpr
      have hh := (div_le_iff₀ ha).mp h₃
      nlinarith
  filter_upwards [hscalar,eventually_ge_atTop Nupper,hcharts 2 εprod hεprod,hlarge,
    hsubseq.tendsto_atTop.eventually hdelta,hsubseq.tendsto_atTop.eventually haccuracy]
      with i hsc hiUpper hchart hlargei hdi hacc
  obtain ⟨V,Ψ,hΨ,hcapture,hjets⟩ := hchart
  have hnonneg : 0 ≤ s (subseq i) - θ / Q (subseq i) :=
    sub_nonneg.mpr (hlargei.2.2.trans (hsa (subseq i)))
  obtain ⟨first,hle,hfirst,hcross⟩ := exists_stage_covering_time_before
    (H (subseq i)) (last (subseq i)) hnonneg
  refine ⟨first,hle,hfirst,hnonneg,?_⟩
  intro y hy
  have hlo : c * Q (subseq i) ≤ metricScalarAt (L (subseq i)).metric (Phi.map i y) := by
    have hh := (hsc.2 y hy).1
    change c ≤ metricScalarAt (scaleMetric (Q (subseq i)) (hQ (subseq i)) (L (subseq i)).metric) (Phi.map i y) at hh
    rw [metricScalarAt_scaleMetric,← div_eq_inv_mul] at hh
    exact (le_div_iff₀ (hQ (subseq i))).mp hh
  have hhi : metricScalarAt (L (subseq i)).metric (Phi.map i y) ≤ (B₀ + 1) * Q (subseq i) := by
    have herr := (abs_lt.mp ((hNupper i hiUpper).2 y hy)).2
    have hh : metricScalarAt (X.obj (subseq i)).metric (Phi.map i y) ≤ B₀ + 1 := by
      linarith [hupper y]
    change metricScalarAt (scaleMetric (Q (subseq i)) (hQ (subseq i)) (L (subseq i)).metric) (Phi.map i y) ≤ B₀ + 1 at hh
    rw [metricScalarAt_scaleMetric,← div_eq_inv_mul] at hh
    exact (div_le_iff₀ (hQ (subseq i))).mp hh
  apply htrace (H (subseq i)) first (last (subseq i)) hle (s (subseq i))
    (G (subseq i)) (L (subseq i)) (hinit (subseq i))
    (parameters (subseq i)) (records (subseq i)) (hfixed (subseq i)) (hlower (subseq i))
    (fun j _ hj b => hdi j hj b) q₀ (Q (subseq i)) hq₀ (hQ (subseq i)) hlargei.1
    (fun j _ hj => hderiv (subseq i) j hj) (hfinal (subseq i)) hcross (hmargin (subseq i))
    (hm (subseq i)) hacc (fun j _ _ b => (records (subseq i) j).static b)
    (fun j _ hj => hcap (subseq i) j hj)
    (fun j _ hj => center (subseq i) j hj) (fun j _ hj => precision (subseq i) j hj)
    (fun j _ hj => order (subseq i) j hj) (fun j _ hj => d (subseq i) j hj)
    (fun j _ hj => w (subseq i) j hj) (fun j _ hj => Jbig (subseq i) j hj)
    (fun j _ hj => hJbig (subseq i) j hj) (fun j _ hj => hzero (subseq i) j hj) ?_
    (Phi.map i y) hlo hhi (hlargei.2.1.trans_le hlo) hprod hdim O V Ψ ?_ ?_
  · intro j hf hj b z
    obtain ⟨v,hv,hvmark⟩ := hmark (subseq i) j hj b z
    have hD : StandardCap.transitionEnd < D + 1 := by
      have hri : 0 < r := by linarith [StandardCap.transitionEnd_pos,inv_pos.mpr heps]
      have hi : 0 < eps⁻¹ := inv_pos.mpr heps
      nlinarith [StandardCap.transitionEnd_pos]
    let u : standardCapWindow D := ⟨v.val,hv.trans_lt hD⟩
    exact ⟨u,hv,hvmark⟩
  · intro z hz
    have hz' : z ∈ riemannianClosedBallOf (X.obj (subseq i)).metric (Phi.map i y) R := by
      change riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i y) z ≤ ENNReal.ofReal R
      exact le_of_lt (show riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i y) z < ENNReal.ofReal R from hz)
    exact hcapture y (hKA hy) hz'
  · intro z n hn
    have hh := (hjets z n hn).le
    rw [he] at hh
    exact hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
