import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckSurvival

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private exists_stage_covering_time_before from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CompactProductTraceSurvival
open private exists_subsequence_prospective_historical_neck_recognition from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckConvergence
open private exists_pointed_cylinder_convergence_of_selected_necks
  exists_actual_reset_pointed_convergence actual_reset_point_trace_on_compact_of_selected_chart
  exists_neck_restrictions_in_growing_source_slabs exists_growing_selected_neck_trace_subsequence
  selected_neck_slab_traces_mono_depth exists_threeModel_cylinder selectedChartExtension
  selected_chart_image_trace_of_extended_points reset_time_bounds_of_scale_lower_bound
  ObservedHistory.scalar_deriv_bound_at_actual_source_reset BackwardPointTrace.concat from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckSurvival

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {Q : OrientedThreeStage.{u}} {a s : ℝ} (G : Q.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private theorem common_backward_trace_window_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) (B₀ : ℝ) (hB₀ : 0 < B₀) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i),
    Tendsto Q atTop atTop → ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
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
    (∀ y, metricScalarAt P.metric y ≤ B₀) →
    ∀ (K : Set P.M), IsCompact K → (∀ y ∈ K, 0 < metricScalarAt P.metric y) →
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / Q i) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ i < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime *
          (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (subseq i)).eventCount + 1),
      ∃ hle : first ≤ last (subseq i),
        (H (subseq i)).time first ≤ s (subseq i) - θ / Q (subseq i) ∧
        0 ≤ s (subseq i) - θ / Q (subseq i) ∧
        ∀ y ∈ K, Nonempty (BackwardPointTrace (H (subseq i)) first (last (subseq i)) hle
          (Phi.map i y).val) := by
  open ObservedHistory in
  obtain ⟨θ,ε₀,δ₀,hθ,hε₀,hεhalf,hδ₀,hall⟩ :=
    exists_uniform_backward_trace_of_prepared_caps_and_product_chart_of_scalar_upper_bound
      D r eps a₀ (B₀ + 1) Ctime ha₀ (by positivity) heps hepssmall hr hfit
  refine ⟨θ,ε₀,δ₀,hθ,hε₀,hδ₀,?_⟩
  intro H last s G L hinit x Q hQ hQlim a ha hsa X P subseq hsubseq Phi Cm hcanonical
    hcomplete F H' M hnorm hspace hfinite htop J hboundary hMtop hMchart hMsmooth hMt2
    hMconn hprod hdim e he hupper K hK hpositive
  let projection := fun z : P.M => (e.symm z).1
  have hprojection : Function.Surjective projection := fun z => ⟨e (z, 0),by simp [projection]⟩
  let _ : SigmaCompactSpace M := isSigmaCompact_univ_iff.mp (by
    rw [← hprojection.range_eq]
    exact isSigmaCompact_range (continuous_fst.comp e.symm.continuous))
  have hPconn : ConnectedSpace P.M := by
    exact e.toHomeomorph.connectedSpace_iff.mp inferInstance
  let _ : ConnectedSpace P.M := hPconn
  have hdistCont : Continuous (fun y : P.M =>
      (riemannianEDistOf P.metric P.basepoint y).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top P.metric P.basepoint y)).comp
      (Geometry.Riemannian.continuous_riemannianEDist P.metric P.basepoint).continuousAt
  obtain ⟨A₀,hA₀⟩ := hK.bddAbove_image hdistCont.continuousOn
  let A : ℝ := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hKA : K ⊆ riemannianClosedBallOf P.metric P.basepoint A := by
    intro y hy
    apply (ENNReal.toReal_le_toReal (riemannianEDistOf_ne_top P.metric P.basepoint y)
        ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hA]
    exact (hA₀ ⟨y,hy,rfl⟩).trans (le_max_left _ _)
  obtain ⟨c,B,hc,hB,hcB,hscalar⟩ :=
    Perelman.KappaSolutions.exists_positive_pointed_scalar_bounds_on_compact Phi Cm hcanonical K
        hK hpositive
  obtain ⟨Nupper,hNupper⟩ :=
    Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    Cm hcanonical K hK 1 zero_lt_one
  obtain ⟨Qmin,R,εprod,hQmin,hR,hεprod,hεquarter,htrace⟩ := hall c hc
  have hclosed : RiemannianMetricComplete P.metric := ⟨hcomplete⟩
  obtain ⟨O,hO,hcharts⟩ := exists_eventually_fixed_domain_diffeomorph_capturing_balls
    Phi Cm hcanonical e P.basepoint hA hR.le
    (by linarith : 2 * (2 * A + R) < 2 * (2 * A + R) + 1)
    (hclosed.closedEBall_isCompact P.basepoint (2 * (2 * A + R) + 1))
  intro parameters records hfixed hlower hdelta haccuracy hmargin hm q₀ hq₀ hqlim hderiv hfinal
    hcap center precision order d w Jbig hJbig hzero hmark
  have hlarge : ∀ᶠ i in atTop,
      Qmin ≤ Q (subseq i) ∧ 2 * q₀ (subseq i) < c * Q (subseq i) ∧ θ / Q (subseq i) ≤ a := by
    have hQsub : Tendsto (fun i => Q (subseq i)) atTop atTop := hQlim.comp hsubseq.tendsto_atTop
    have hratio : Tendsto (fun i => q₀ (subseq i) / Q (subseq i)) atTop (𝓝 0) :=
      hqlim.comp hsubseq.tendsto_atTop
    filter_upwards [hQsub.eventually (eventually_ge_atTop Qmin),
      hratio.eventually (gt_mem_nhds (half_pos hc)),
      hQsub.eventually (eventually_ge_atTop (θ / a))] with i h₁ h₂ h₃
    refine ⟨h₁,?_,?_⟩
    · have hh := (div_lt_iff₀ (hQ (subseq i))).mp h₂
      linarith
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
    change c ≤ metricScalarAt (scaleMetric (Q (subseq i)) (hQ (subseq i)) (L (subseq i)).metric)
        (Phi.map i y) at hh
    rw [metricScalarAt_scaleMetric,← div_eq_inv_mul] at hh
    exact (le_div_iff₀ (hQ (subseq i))).mp hh
  have hhi : metricScalarAt (L (subseq i)).metric (Phi.map i y) ≤ (B₀ + 1) * Q (subseq i) := by
    have herr := (abs_lt.mp ((hNupper i hiUpper).2 y hy)).2
    have hh : metricScalarAt (X.obj (subseq i)).metric (Phi.map i y) ≤ B₀ + 1 := by
      linarith [hupper y]
    change metricScalarAt (scaleMetric (Q (subseq i)) (hQ (subseq i)) (L (subseq i)).metric)
        (Phi.map i y) ≤ B₀ + 1 at hh
    rw [metricScalarAt_scaleMetric,← div_eq_inv_mul] at hh
    exact (div_le_iff₀ (hQ (subseq i))).mp hh
  apply htrace (H (subseq i)) first (last (subseq i)) hle (s (subseq i))
    (G (subseq i)) (L (subseq i)) (hinit (subseq i))
    (parameters (subseq i)) (records (subseq i)) (hfixed (subseq i)) (hlower (subseq i))
    (fun j _ hj b => hdi j hj b) (q₀ (subseq i)) (Q (subseq i)) (hq₀ (subseq i))
    (hQ (subseq i)) hlargei.1
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
      exact le_of_lt (show riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i y) z <
          ENNReal.ofReal R from hz)
    exact hcapture y (hKA hy) hz'
  · intro z n hn
    have hh := (hjets z n hn).le
    rw [he] at hh
    exact hh

private theorem uniform_backward_trace_window_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i),
    Tendsto Q atTop atTop → ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i => {
          M := (G i).terminalRegularOpen
          basepoint := x i
          metric := scaleMetric (Q i) (hQ i) (L i).metric } };
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (subseq : ℕ → ℕ), StrictMono subseq →
    ∀ (Phi : PointedRiemannianConvergenceMaps X P subseq) (Cm : MetricConvergenceData Phi),
    (∀ i, Cm.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) →
    ∀ (e : NeckCylinder ≃ₘ⟮NeckCylinderModel,ThreeModel⟯ P.M) (v : ℝ), v ≤ 0 →
    Diffeomorph.pullbackMetricCross P.metric e = PDE.RicciFlow.shrinkingCylinderMetric
        (E := ThreeSpace) v →
    ∀ (K : Set P.M), IsCompact K →
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / Q i) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ i < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime *
          (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (subseq i)).eventCount + 1),
      ∃ hle : first ≤ last (subseq i),
        (H (subseq i)).time first ≤ s (subseq i) - θ / Q (subseq i) ∧
        0 ≤ s (subseq i) - θ / Q (subseq i) ∧
        ∀ y ∈ K, Nonempty (BackwardPointTrace (H (subseq i)) first (last (subseq i)) hle
          (Phi.map i y).val) := by
  obtain ⟨theta,eps0,delta0,htheta,heps0,hdelta0,hwindow⟩ :=
    common_backward_trace_window_of_threshold_ratio D r eps a₀ Ctime ha₀ heps
      hepssmall hr hfit 1 zero_lt_one
  refine ⟨theta,eps0,delta0,htheta,heps0,hdelta0,?_⟩
  intro H last s G L hinit x Q hQ hQlim a ha hsa X P subseq hsubseq maps Cm hcanonical e
      v hv he K hK
  have hv1 : v < 1 := hv.trans_lt zero_lt_one
  have hmetric : P.metric = Diffeomorph.pullbackMetricCross
      (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm := by
    exact (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp he).symm
  have hcomplete : MetricComplete P := by
    have hc : RiemannianMetricComplete P.metric := by
      rw [hmetric]
      exact RiemannianMetricComplete.pullbackCross _ e.symm
        (PDE.RicciFlow.shrinkingCylinderMetric_complete v)
    exact hc.complete
  have hscalar (y : P.M) : metricScalarAt P.metric y = (1-v)⁻¹ := by
    rw [hmetric,metricScalar_cross,
      PDE.RicciFlow.shrinkingCylinderMetric_scalar hv1]
  let hprod := scaleMetric (2 * (1-v)) (mul_pos (by norm_num) (by linarith))
    (Geometry.roundMetric (E := ThreeSpace) (n := 2))
  have hp : Diffeomorph.pullbackMetricCross P.metric e = hprod.prod (euclideanMetric (E := ℝ)) := by
    rw [he]
    exact PDE.RicciFlow.shrinkingCylinderMetric_eq_prod hv1
  let _ : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  exact hwindow H last s G L hinit x Q hQ hQlim ha hsa P subseq hsubseq maps Cm hcanonical
    hcomplete hprod (by simp) e hp
    (fun y => by rw [hscalar]; exact inv_le_one_of_one_le₀ (by linarith))
    K hK (fun y _ => by rw [hscalar]; exact inv_pos.mpr (by linarith))

private theorem uniform_initial_trace_window_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel),
      (NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) → Sphere 2 →
    ∃ f : ℕ → ℕ, StrictMono f ∧
    ∀ (K : Set NeckCylinder), IsCompact K →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / (O i).scale) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ i < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime *
          (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (f i)).eventCount + 1),
      ∃ hle : first ≤ last (f i),
        (H (f i)).time first ≤ s (f i) - θ / (O (f i)).scale ∧
        0 ≤ s (f i) - θ / (O (f i)).scale ∧
        ∀ x ∈ (O (f i)).chart '' {z | z.val ∈ K},
          Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val) := by
  obtain ⟨θ,ε₀,δ₀,hθ,hε₀,hδ₀,hwindow⟩ :=
    uniform_backward_trace_window_of_threshold_ratio D r eps a₀ Ctime
      ha₀ heps hepssmall hr hfit
  refine ⟨θ,ε₀,δ₀,hθ,hε₀,hδ₀,?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa P e mark
  let x := fun i => (O i).chart
    ⟨(mark,0),by constructor <;> dsimp <;> linarith [inv_pos.mpr (O i).delta_pos]⟩
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := { obj := fun i => {
    M := (G i).terminalRegularOpen
    basepoint := x i
    metric := scaleMetric (O i).scale (O i).scale_pos (L i).metric } }
  let P₀ : PointedRiemannianManifold.{u, 0, 0} ThreeModel := {
    P with
    basepoint := e (mark,0)
    metric := Diffeomorph.pullbackMetricCross
      (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0) e.symm }
  obtain ⟨_,_,hproduct,f,hf,maps,hmap,_,_,_,C,hcanonical⟩ :=
    exists_pointed_cylinder_convergence_of_selected_necks H last s G L eta m O heta hm P e mark
  refine ⟨f,hf,?_⟩
  intro K hK parameters records hfixed hlower hdelta haccuracy hmargin horder
    q₀ hq₀ hqlim hderiv hfinal hcap center precision order d w Jbig hJbig hzero hmark
  have he : Diffeomorph.pullbackMetricCross P₀.metric e =
      PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0 := by
    rw [PDE.RicciFlow.shrinkingCylinderMetric_zero,← roundCylinderMetric_eq_geometry]
    exact hproduct
  have htraces := hwindow H last s G L hinit x (fun i => (O i).scale)
    (fun i => (O i).scale_pos) hscale ha hsa P₀ f hf maps C hcanonical e 0 le_rfl he
    (e '' K) (hK.image e.continuous) parameters records hfixed hlower hdelta haccuracy
    hmargin horder q₀ hq₀ hqlim hderiv hfinal hcap center precision order d w Jbig hJbig hzero
    hmark
  filter_upwards [htraces] with i hi
  obtain ⟨first,hle,hfirst,hnonneg,hpoints⟩ := hi
  refine ⟨first,hle,hfirst,hnonneg,?_⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩ := hy
  have hh := hpoints (e z) (mem_image_of_mem e hz)
  simpa only [hmap i z] using hh

private theorem uniform_trace_extension_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i),
    Tendsto Q atTop atTop → ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i => {
          M := (G i).terminalRegularOpen
          basepoint := x i
          metric := scaleMetric (Q i) (hQ i) (L i).metric } };
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (subseq : ℕ → ℕ), StrictMono subseq →
    ∀ (Phi : PointedRiemannianConvergenceMaps X P subseq) (Cm : MetricConvergenceData Phi),
    (∀ i, Cm.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) →
    ∀ (e : NeckCylinder ≃ₘ⟮NeckCylinderModel,ThreeModel⟯ P.M) (v : ℝ), v ≤ 0 →
    Diffeomorph.pullbackMetricCross P.metric e = PDE.RicciFlow.shrinkingCylinderMetric
        (E := ThreeSpace) v →
    ∀ (K : Set P.M), IsCompact K →
    ∀ (later : ∀ i, Fin ((H i).eventCount + 1)) (hlater : ∀ i, last i ≤ later i)
      (endpoint : ∀ i, P.M → ((H i).stage (later i)).Carrier),
    (∀ᶠ i in atTop, ∀ y ∈ K,
      ∃ A : BackwardPointTrace (H (subseq i)) (last (subseq i)) (later (subseq i))
          (hlater (subseq i)) (endpoint (subseq i) y),
        (Phi.map i y).val = A.point (last (subseq i)) le_rfl (hlater (subseq i))) →
    ∀ (originalTime : ℕ → ℝ) (T : ℝ),
    (∀ i, s i = originalTime i + v / Q i) →
    v < -T + θ / 2 →
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / Q i) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ i < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime *
          (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (subseq i)).eventCount + 1),
      ∃ hle : first ≤ later (subseq i),
        (H (subseq i)).time first < originalTime (subseq i) - (T + θ/2) / Q (subseq i) ∧
        ∀ y ∈ K, Nonempty (BackwardPointTrace (H (subseq i)) first (later (subseq i)) hle
          (endpoint (subseq i) y)) := by
  obtain ⟨theta,eps0,delta0,htheta,heps0,hdelta0,hwindow⟩ :=
    uniform_backward_trace_window_of_threshold_ratio D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨theta,eps0,delta0,htheta,heps0,hdelta0,?_⟩
  intro H last s G L hinit x Q hQ hQlim a ha hsa X P subseq hsubseq Phi Cm hcanonical e v hv he K hK
    later hlater endpoint hpoint originalTime T htime hvT parameters records hfixed hlower
    hdelta haccuracy hmargin hm q0 hq0 hqlim hderiv hfinal hcap center precision order d
        w Jbig hJbig
    hzero hmark
  have htraces := hwindow H last s G L hinit x Q hQ hQlim ha hsa P subseq hsubseq Phi Cm hcanonical
    e v hv he K hK parameters records hfixed hlower hdelta haccuracy hmargin hm q0 hq0 hqlim hderiv
    hfinal hcap
    center precision order d w Jbig hJbig hzero hmark
  filter_upwards [hpoint,htraces] with i hpointi htracesi
  obtain ⟨first,hle,hfirst,_,hbefore⟩ := htracesi
  have hgain : s (subseq i) - theta / Q (subseq i) <
      originalTime (subseq i) - (T + theta/2) / Q (subseq i) := by
    rw [htime]
    have hdiv := div_lt_div_of_pos_right hvT (hQ (subseq i))
    have heq : (-T + theta/2) / Q (subseq i) - theta / Q (subseq i) =
        -(T + theta/2) / Q (subseq i) := by ring
    rw [neg_div] at heq
    linarith
  refine ⟨first,hle.trans (hlater (subseq i)),hfirst.trans_lt hgain,?_⟩
  intro y hy
  obtain ⟨A,hA⟩ := hpointi y hy
  obtain ⟨B⟩ := hbefore y hy
  have B' : BackwardPointTrace (H (subseq i)) first (last (subseq i)) hle
      (A.point (last (subseq i)) le_rfl (hlater (subseq i))) := by
    rw [← hA]
    exact B
  exact ⟨BackwardPointTrace.concat A hle B'⟩

private theorem selected_neck_trace_extension_of_threshold_ratio
    (D r tol a₀ : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (_ : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (δ : ℕ → ℝ) (_ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
  (_ : Tendsto δ atTop (𝓝 0))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (_ : Tendsto eps atTop (𝓝 0)) (_ : Tendsto order atTop atTop)
  (offset : ℕ → ℕ) (_ : offset 0 = 0)
  (hprecision : ∀ n j, eps (j + offset n) ≤ δ n)
  (Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen)
  (_ : ∀ n j x, x ∈ Footprint n j → Nonempty (BackwardPointTrace
    (H (j + offset n)) (first (j + offset n)) (last (j + offset n))
    (hle (j + offset n)) x.val))
  (_ : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
    interior (Footprint n j))
  (T : ℝ) (_ : 0 < T)
  (_ : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (q0 : ℕ → ℝ) (_ : ∀ i, 0 < q0 i)
  (_ : Tendsto (fun i => q0 i / (O i).scale) atTop (𝓝 0))
  (_ : Tendsto (fun i => (O i).scale) atTop atTop)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q0 i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (_ : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    q0 i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (_ : Perelman.AdmissiblePinchingFunction phi)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (_ : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)
    (_ : Antitone δ)
    {a : ℝ} (_ : 0 < a) (_ : ∀ i, a ≤ s i)
    (_ : ∀ i, 2 * T / a ≤ (O i).scale)
    (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (mark : Sphere 2)
    (_ : e (mark, 0) = P.basepoint),
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈tol⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∃ ind : ℕ → ℕ, StrictMono ind ∧
      ∀ K : Set NeckCylinder, IsCompact K → ∀ᶠ i in atTop,
        ∃ earlier : Fin ((H (ind i)).eventCount + 1), ∃ he : earlier ≤ last (ind i),
          (H (ind i)).time earlier < s (ind i) - (T + θ / 2) / (O (ind i)).scale ∧
          ∀ z ∈ K, Nonempty (BackwardPointTrace (H (ind i)) earlier (last (ind i)) he
            (selectedChartExtension (O (ind i)) z).val) := by
  obtain ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, hwindow⟩ :=
    uniform_trace_extension_of_threshold_ratio D r tol a₀ C ha₀ htol htolsmall hr hfit
  refine ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, ?_⟩
  intro H last first hle s J L hinit δ hδ hδ1 hδlim eps order O heps horder offset hoffset
    hprecision Footprint htrace hinside T hT hstart q0 hq0 hqlim hscale hderivative hfinal
    phi hphi hpinching hpinchFinal hmono a ha hsa hQLower P e mark hmark
    parameters records hfixed hlower hdelta haccuracy hmargin hm hcap
    center precision capOrder d w Jbig hJbig hzero hcapmark
  have hq : ∀ᶠ i in atTop, q0 i / (O i).scale ≤ 1 :=
    hqlim.eventually (ge_mem_nhds zero_lt_one)
  let η := min T θ
  have hη : 0 < η := lt_min hT hθ
  have hηT : η ≤ T := min_le_left _ _
  have hηθ : η ≤ θ := min_le_right _ _
  have hleft : -T < -T + η / 4 := by linarith
  have hmid : -T + η / 4 < -T + η / 2 := by linarith
  have hright : -T + η / 2 < 0 := by linarith
  obtain ⟨v, hv, reset, hf, hl, Jτ, Lτ, hinitτ, hregτ, htermτ, hsourceτ,
    rho, hrho, k, hk, x, hc, hscalar, hproduct, ell, hell, maps, hmap, Cm, hcanonical⟩ :=
    exists_actual_reset_pointed_convergence H last first hle s J L hinit δ hδ hδ1 hδlim
      eps order O heps horder offset hoffset hprecision Footprint htrace hinside T hT hstart
      C q0 hq hscale
      (fun i j _ hj => hderivative i j hj) hfinal hphi
      (fun i j _ hj => hpinching i j hj) hpinchFinal hmono P e mark hmark hleft hmid hright
  let p := rho ∘ k
  have hp : StrictMono p := hrho.comp hk
  let τ := fun i => s i + v / (O i).scale
  have hv0 : v < 0 := hv.2.trans hright
  have hvT : -T < v := hleft.trans hv.1
  have hvGain : v < -T + θ / 2 := hv.2.trans_le (by linarith)
  have hτa (i) : a / 2 ≤ τ i :=
    (reset_time_bounds_of_scale_lower_bound ha (hsa i) (O i).scale_pos (hQLower i) ⟨hvT,hv0⟩).1.le
  let Pτ : PointedRiemannianManifold.{u, 0, 0} ThreeModel := { P with
    metric := Diffeomorph.pullbackMetricCross
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm }
  have he : Diffeomorph.pullbackMetricCross Pτ.metric e =
      PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl
  have hfinalτ (i) : ∀ y, ∀ t ∈ Ioo ((H i).time (reset i)) (τ i),
      q0 i < (Jτ i).flow.scalar t y →
      |derivWithin (fun v => (Jτ i).flow.scalar v y) (Iic t) t| ≤ C * (Jτ i).flow.scalar t y ^ 2 :=
    ObservedHistory.scalar_deriv_bound_at_actual_source_reset (H i) (reset i) (last i)
      (J i) (Jτ i) (hsourceτ i) (hderivative i) (hfinal i)
  refine ⟨p ∘ ell, hp.comp hell, ?_⟩
  intro K hK
  have hpointK := actual_reset_point_trace_on_compact_of_selected_chart
    (fun i => H (p (ell i))) (fun i => first (p (ell i))) (fun i => reset (p (ell i)))
    (fun i => last (p (ell i))) (fun i => hf (p (ell i))) (fun i => hl (p (ell i)))
    (fun i => s (p (ell i))) (fun i => J (p (ell i))) (fun i => L (p (ell i)))
    (fun i => eps (p (ell i))) (fun i => δ (ell i)) (fun i => order (p (ell i)))
    (fun i => O (p (ell i))) (fun i => hδ (ell i)) (fun i => hδ1 (ell i))
    (hδlim.comp hell.tendsto_atTop) (fun i z => (maps.map i (e z)).val) hmap K hK
  have hpointP : ∀ᶠ i in atTop, ∀ y ∈ e '' K,
      ∃ A : BackwardPointTrace (H (p (ell i))) (reset (p (ell i))) (last (p (ell i)))
          (hl (p (ell i))) (selectedChartExtension (O (p (ell i))) (e.symm y)).val,
        (maps.map i y).val = A.point (reset (p (ell i))) le_rfl (hl (p (ell i))) := by
    filter_upwards [hpointK] with i hi y hy
    obtain ⟨z,hz,rfl⟩ := hy
    obtain ⟨A,hA⟩ := hi z hz
    have hA' : ∃ A' : BackwardPointTrace (H (p (ell i))) (reset (p (ell i))) (last (p (ell i)))
        (hl (p (ell i))) (selectedChartExtension (O (p (ell i))) z).val,
        (maps.map i (e z)).val = A'.point (reset (p (ell i))) le_rfl (hl (p (ell i))) :=
      ⟨A.restrictFirst (hf _) (hl _), hA⟩
    have hzEq : e.symm (e z) = z := e.symm_apply_apply z
    exact hzEq.symm ▸ hA'
  have hdeltaτ : ∀ᶠ i in atTop, ∀ j : Fin (H (p i)).eventCount, j.succ ≤ reset (p i) →
      ∀ b, (records (p i) j).delta b ≤ δ₀ :=
    (hp.tendsto_atTop.eventually hdelta).mono fun i hi j hj => hi j (hj.trans (hl (p i)))
  have hresult := hwindow (fun i => H (p i)) (fun i => reset (p i)) (fun i => τ (p i))
    (fun i => Jτ (p i)) (fun i => Lτ (p i)) (fun i => hinitτ (p i)) x
    (fun i => (O (p i)).scale) (fun i => (O (p i)).scale_pos)
    (hscale.comp hp.tendsto_atTop) (half_pos ha) (fun i => hτa (p i))
    Pτ ell hell maps Cm hcanonical e v hv0.le he (e '' K) (hK.image e.continuous)
    (fun i => last (p i)) (fun i => hl (p i))
    (fun i y => (selectedChartExtension (O (p i)) (e.symm y)).val) hpointP
    (fun i => s (p i)) T (fun _ => rfl) hvGain
    (fun i => parameters (p i)) (fun i => records (p i))
    (fun i => hfixed (p i)) (fun i => hlower (p i)) hdeltaτ
    (hp.tendsto_atTop.eventually haccuracy) (fun i => hmargin (p i)) (fun i => hm (p i))
    (fun i => q0 (p i)) (fun i => hq0 (p i)) (hqlim.comp hp.tendsto_atTop)
    (fun i j hj => hderivative (p i) j (hj.trans (hl (p i))))
    (fun i => hfinalτ (p i)) (fun i j hj => hcap (p i) j (hj.trans (hl (p i))))
    (fun i j hj => center (p i) j (hj.trans (hl (p i))))
    (fun i j hj => precision (p i) j (hj.trans (hl (p i))))
    (fun i j hj => capOrder (p i) j (hj.trans (hl (p i))))
    (fun i j hj => d (p i) j (hj.trans (hl (p i))))
    (fun i j hj => w (p i) j (hj.trans (hl (p i))))
    (fun i j hj => Jbig (p i) j (hj.trans (hl (p i))))
    (fun i j hj => hJbig (p i) j (hj.trans (hl (p i))))
    (fun i j hj => hzero (p i) j (hj.trans (hl (p i))))
    (fun i j hj => hcapmark (p i) j (hj.trans (hl (p i))))
  filter_upwards [hresult] with i hi
  obtain ⟨earlier, hle', htime, htraces⟩ := hi
  refine ⟨earlier, hle', htime, ?_⟩
  intro z hz
  have hh := htraces (e z) ⟨z,hz,rfl⟩
  simpa only [e.symm_apply_apply, Function.comp_apply] using! hh


private theorem selected_neck_trace_extension_growing_of_threshold_ratio
    (D r tol a₀ : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (_ : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (_ : Tendsto eps atTop (𝓝 0)) (_ : Tendsto order atTop atTop)
  (_ : ∀ i, eps i ≤ (1 / 2 : ℝ))
  (radius : ℕ → ℝ) (_ : Tendsto radius atTop atTop) (_ : ∀ i, (3 : ℝ) ≤ radius i)
  (_ : ∀ i x, x ∈ (O i).chart '' {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
    Nonempty (BackwardPointTrace (H i) (first i) (last i) (hle i) x.val))
  (T : ℝ) (_ : 0 < T)
  (_ : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (q0 : ℕ → ℝ) (_ : ∀ i, 0 < q0 i)
  (_ : Tendsto (fun i => q0 i / (O i).scale) atTop (𝓝 0))
  (_ : Tendsto (fun i => (O i).scale) atTop atTop)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q0 i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (_ : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    q0 i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (_ : Perelman.AdmissiblePinchingFunction phi)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (_ : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)
    {a : ℝ} (_ : 0 < a) (_ : ∀ i, a ≤ s i)
    (_ : ∀ i, 2 * T / a ≤ (O i).scale)
    (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (mark : Sphere 2)
    (_ : e (mark, 0) = P.basepoint),
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈tol⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∃ ind : ℕ → ℕ, StrictMono ind ∧
      ∀ K : Set NeckCylinder, IsCompact K → ∀ᶠ i in atTop,
        ∃ earlier : Fin ((H (ind i)).eventCount + 1), ∃ he : earlier ≤ last (ind i),
          (H (ind i)).time earlier < s (ind i) - (T + θ / 2) / (O (ind i)).scale ∧
          ∀ z ∈ K, Nonempty (BackwardPointTrace (H (ind i)) earlier (last (ind i)) he
            (selectedChartExtension (O (ind i)) z).val) := by
  obtain ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, hstep⟩ :=
    selected_neck_trace_extension_of_threshold_ratio D r tol a₀ C ha₀ htol htolsmall hr hfit
  refine ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, ?_⟩
  intro H last first hle s J L hinit eps order O heps horder hprecision0 radius hradius hfit0
    htrace T hT hstart q0 hq0 hqlim hscale hderivative hfinal phi hphi hpinching hpinchFinal
    a ha hsa hQLower P e mark hmark parameters records hfixed hlower hdelta haccuracy
        hmargin hm hcap
    center precision capOrder d w Jbig hJbig hzero hcapmark
  obtain ⟨δ, hδ1, _, hδ, hmono, hδlim, offset, hprecision, hoffset, _, hinside⟩ :=
    exists_neck_restrictions_in_growing_source_slabs H last s J L eps order O heps
      hprecision0 radius hradius hfit0
  let Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen :=
    fun n j => (O (j + offset n)).chart ''
      {z | -(radius (j + offset n)) ≤ z.val.2 ∧ z.val.2 ≤ radius (j + offset n)}
  exact hstep H last first hle s J L hinit δ hδ hδ1 hδlim eps order O heps horder offset hoffset
    hprecision Footprint (fun n j => htrace (j + offset n)) hinside T hT hstart
    q0 hq0 hqlim hscale hderivative hfinal hphi hpinching hpinchFinal hmono ha hsa hQLower
    P e mark hmark parameters records hfixed hlower hdelta haccuracy hmargin hm hcap
    center precision capOrder d w Jbig hJbig hzero hcapmark

private theorem prospective_neck_convergence_growing_of_threshold_ratio
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (hinit : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (hprecision0 : ∀ i, eps i ≤ δ)
  {k : ℕ} (hk : ∀ i, k ≤ order i)
  (N : ∀ i, NormalizedNeck (L i).metric δ k)
  (hN : ∀ i, N i = ((O i).monoDelta
    (hprecision0 i) hδ1).lowerOrder (hk i))
  (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
  (hfit0 : ∀ i, δ⁻¹ + 1 ≤ radius i)
  (htrace : ∀ i x, x ∈ (O i).chart '' {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
    Nonempty (BackwardPointTrace (H i) (first i) (last i) (hle i) x.val))
  (hstart2 : ∀ i, (H i).time (first i) ≤ s i - 2 / (O i).scale)
  (C : ℝ≥0) (q : ℕ → ℝ)
  (hq : Tendsto (fun i => q i / (O i).scale) atTop (𝓝 0))
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (hfinal : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    q i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi) :
    ∃ (K : ∀ i, Set (J i).terminalRegularOpen)
      (Phi : ∀ i, neckBuffer δ → (H i).backwardSurvivorIncomingFootprint
        (first i) (last i) (hle i) (J i) (K i))
      (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
      (G : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i)))
      (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
        (RealTimeInterval.closed (-2) 0 (by norm_num)))
      (rho : ℕ → ℕ),
      StrictMono rho ∧
      (∀ i, (H i).backwardSurvivorIncomingFootprintMap
        (first i) (last i) (hle i) (J i) (K i) ∘ Phi i = (N i).chart) ∧
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, (S i).base.metric 0 = (N i).normalizedMetric) ∧
      (∀ i t, (S i).base.metric t = localPullMetric
        (scaleMetric (N i).scale (N i).scale_pos (G i (s i + t / (N i).scale)))
        (Phi i) (hPhi i)) ∧
      (∀ i (j : Fin (H i).eventCount) (hf : first i ≤ j.castSucc) (hl : j.succ ≤ last i),
        ∀ t ∈ Icc ((H i).time j.castSucc) ((H i).time j.succ),
          G i t = (((H i).backwardSurvivorSlabMetric (first i) (last i)
            (hle i) j hf hl t).restrictOpen
            ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (J i))).restrictOpen
              ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ i t, t ∈ Icc ((H i).time (last i)) (s i) →
        G i t = ((H i).backwardSurvivorIncomingMetric
          (first i) (last i) (hle i) (J i) (L i) t).restrictOpen
          ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ A : Set (neckBuffer δ), IsCompact A → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn A p ((S (rho i)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < η) ∧
      ∀ᶠ i in atTop,
        ∃ Z : (b : ℕ) → Icc (-1 : ℝ) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Z b v x = iteratedDerivWithin b (fun t =>
            metricTensorField ((S (rho i)).base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-1 : ℝ) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η := by
  let d : ℕ → ℝ := fun n => Nat.casesOn n δ (fun m => δ / ((m : ℝ) + 2))
  have hd : ∀ n, 0 < d n := by
    intro n
    cases n with
    | zero => exact hδ
    | succ n => dsimp [d]; positivity
  have hd1 : ∀ n, d n < 1 := by
    intro n
    cases n with
    | zero => exact hδ1
    | succ n =>
      dsimp [d]
      apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    apply (hh.const_div_atTop δ).congr'
    apply Eventually.of_forall
    intro n
    cases n with
    | zero => simp [d]
    | succ n => dsimp [d]; congr 1; push_cast; ring
  have htail (n : ℕ) : ∃ m : ℕ, ∀ j, m ≤ j → eps j ≤ d n ∧ (d n)⁻¹ + 1 ≤ radius j := by
    have hp : ∀ᶠ j in atTop, eps j ≤ d n :=
      (heps.eventually (Iio_mem_nhds (hd n))).mono fun j hj => hj.le
    have hr : ∀ᶠ j in atTop, (d n)⁻¹ + 1 ≤ radius j :=
      hradius.eventually (eventually_ge_atTop _)
    exact eventually_atTop.1 (hp.and hr)
  choose tail htail using htail
  let offset : ℕ → ℕ := fun n => Nat.casesOn n 0 (fun m => tail (m+1))
  have hoffset : offset 0 = 0 := rfl
  have hprecision : ∀ n j, eps (j + offset n) ≤ d n := by
    intro n j
    cases n with
    | zero => simpa [offset, d] using hprecision0 j
    | succ n => exact (htail (n+1) (j + offset (n+1)) (by dsimp [offset]; omega)).1
  have hfit : ∀ n j, (d n)⁻¹ + 1 ≤ radius (j + offset n) := by
    intro n j
    cases n with
    | zero => simpa [offset, d] using hfit0 j
    | succ n => exact (htail (n+1) (j + offset (n+1)) (by dsimp [offset]; omega)).2
  let K : ∀ n j, Set (J (j + offset n)).terminalRegularOpen :=
    fun n j => (O (j + offset n)).chart ''
      {z | -(radius (j + offset n)) ≤ z.val.2 ∧ z.val.2 ≤ radius (j + offset n)}
  have hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hd1 n)).chart ⊆
      interior (K n j) := by
    intro n j x hx
    obtain ⟨z, rfl⟩ := hx
    dsimp [K]
    rw [(O (j + offset n)).interior_image_closedSlab]
    refine ⟨TopologicalSpace.Opens.inclusion
      (neckBuffer_le_of_le (O (j + offset n)).delta_pos (hprecision n j)) z, ?_, rfl⟩
    constructor <;> dsimp <;> linarith [z.property.1, z.property.2, hfit n j]
  have hqevent : ∀ᶠ i in atTop, q i / (O i).scale ≤ 1 :=
    hq.eventually (ge_mem_nhds zero_lt_one)
  exact exists_subsequence_prospective_historical_neck_recognition H last first hle s J L hinit
    d hd hd1 hdlim eps order O heps horder offset hoffset hprecision hk N hN K
    (fun n j => htrace (j + offset n)) hinside hstart2 C q hqevent hscale
    hderivative hfinal hphi hpinching hpinchFinal

private theorem selected_neck_traces_cylindrical_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
      (_ : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (_ : Sphere 2),
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / (O i).scale) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ i < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime *
          (G i).flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (last i)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ target : ℝ, ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ n : ℕ, ∀ᶠ i in atTop,
        ∃ (first : Fin ((H (f i)).eventCount + 1)) (hle : first ≤ last (f i)),
          (H (f i)).time first ≤ s (f i) - target / (O (f i)).scale ∧
          ∀ x ∈ (O (f i)).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
            Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val) := by
  classical
  obtain ⟨theta0,eps0,delta0,htheta0,heps0,hdelta0,hbase⟩ :=
    uniform_initial_trace_window_of_threshold_ratio D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  obtain ⟨theta1,eps1,delta1,htheta1,heps1,hdelta1,hstep⟩ :=
    selected_neck_trace_extension_growing_of_threshold_ratio D r eps a₀ Ctime ha₀ heps
        hepssmall hr hfit
  refine ⟨min eps0 eps1,min delta0 delta1,lt_min heps0 heps1,lt_min hdelta0 hdelta1,?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa P e mark
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hqlim hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark target
  let Pmark := P.repoint (e (mark,0))
  have hmarkP : e (mark,0) = Pmark.basepoint := rfl
  let depth := fun n : ℕ => theta0 + (n : ℝ) * (theta1 / 2)
  have hdepth : ∀ n, 0 < depth n := by intro n; dsimp [depth]; positivity
  let Traces := fun (T : ℝ) (f : ℕ → ℕ) => ∀ n : ℕ, ∀ᶠ i in atTop,
    ∃ (first : Fin ((H (f i)).eventCount + 1)) (hle : first ≤ last (f i)),
      (H (f i)).time first ≤ s (f i) - T / (O (f i)).scale ∧
      ∀ x ∈ (O (f i)).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
        Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val)
  have hdelta0' := hdelta.mono fun i hi j hj b => (hi j hj b).trans (min_le_left _ _)
  have haccuracy0 := haccuracy.mono fun i hi => hi.trans (min_le_left _ _)
  obtain ⟨f0,hf0,hfirst⟩ := hbase H last s G L hinit eta m O heta hm hscale ha hsa Pmark e mark
  have hbaseP : Traces (depth 0) f0 := by
    intro n
    have hh := hfirst (univ ×ˢ Icc (-(n : ℝ)) n) (isCompact_univ.prod isCompact_Icc)
      parameters records hfixed hlower hdelta0' haccuracy0 hmargin horder q0 hq0 hqlim
          hderiv hfinal hcap
      center precision order d w Jbig hJbig hzero hmark
    filter_upwards [hh] with i hi
    obtain ⟨first,hle,htime,_,hpoints⟩ := hi
    refine ⟨first,hle,?_,?_⟩
    · simpa [depth] using htime
    · simpa only [mem_prod,mem_univ,true_and,mem_Icc] using hpoints
  have hind : ∀ n : ℕ, ∃ f : ℕ → ℕ, StrictMono f ∧ Traces (depth n) f := by
    intro n
    induction n with
    | zero => exact ⟨f0,hf0,hbaseP⟩
    | succ n ih =>
      obtain ⟨f,hf,htraces⟩ := ih
      have hscaleF := hscale.comp hf.tendsto_atTop
      obtain ⟨N,hN⟩ := eventually_atTop.mp (hscaleF.eventually_ge_atTop (2 * depth n / a))
      let f' := fun i => f (i+N)
      have hf' : StrictMono f' := hf.comp (strictMono_nat_of_lt_succ fun _ => by omega)
      have htraces' : Traces (depth n) f' := by
        intro j
        exact (tendsto_add_atTop_nat N).eventually (htraces j)
      obtain ⟨g,hg,first,hle,radius,hradius,_,hfit0,_,_,_,hprec,hord,hstart,htrace⟩ :=
        exists_growing_selected_neck_trace_subsequence
          (fun i => H (f' i)) (fun i => last (f' i)) (fun i => s (f' i))
          (fun i => G (f' i)) (fun i => L (f' i)) (fun i => eta (f' i)) (fun i => m (f' i))
          (fun i => O (f' i)) (heta.comp hf'.tendsto_atTop) (hm.comp hf'.tendsto_atTop)
          (by norm_num : 0 < (1/2 : ℝ)) 0 (depth n) htraces'
      let p := f' ∘ g
      have hp : StrictMono p := hf'.comp hg
      have hfit0' : ∀ i, 3 ≤ radius i := by norm_num at hfit0 ⊢; exact hfit0
      have hQLower : ∀ i, 2 * depth n / a ≤ (O (p i)).scale := by
        intro i
        exact hN (g i + N) (by omega)
      have hdelta1' := (hp.tendsto_atTop.eventually hdelta).mono
        fun i hi j hj b => (hi j hj b).trans (min_le_right _ _)
      have haccuracy1 := (hp.tendsto_atTop.eventually haccuracy).mono
        fun i hi => hi.trans (min_le_right _ _)
      obtain ⟨ell,hell,hext⟩ := hstep
        (fun i => H (p i)) (fun i => last (p i)) first hle (fun i => s (p i))
        (fun i => G (p i)) (fun i => L (p i)) (fun i => hinit (p i))
        (fun i => eta (p i)) (fun i => m (p i)) (fun i => O (p i))
        (heta.comp hp.tendsto_atTop) (hm.comp hp.tendsto_atTop) hprec radius hradius hfit0'
        htrace (depth n) (hdepth n) hstart (fun i => q0 (p i)) (fun i => hq0 (p i))
        (hqlim.comp hp.tendsto_atTop) (hscale.comp hp.tendsto_atTop)
        (fun i => hderiv (p i)) (fun i => hfinal (p i)) hphi
        (fun i => hpinch (p i)) (fun i => hpinchFinal (p i)) ha (fun i => hsa (p i)) hQLower
        Pmark e mark hmarkP (fun i => parameters (p i)) (fun i => records (p i))
        (fun i => hfixed (p i)) (fun i => hlower (p i)) hdelta1' haccuracy1
        (fun i => hmargin (p i)) (fun i => horder (p i))
        (fun i => hcap (p i)) (fun i => center (p i)) (fun i => precision (p i))
        (fun i => order (p i)) (fun i => d (p i)) (fun i => w (p i))
        (fun i => Jbig (p i)) (fun i => hJbig (p i)) (fun i => hzero (p i)) (fun i => hmark (p i))
      refine ⟨p ∘ ell,hp.comp hell,?_⟩
      intro j
      have hh := hext (univ ×ˢ Icc (-(j : ℝ)) j) (isCompact_univ.prod isCompact_Icc)
      filter_upwards [hh] with i hi
      obtain ⟨earlier,hle',htime,hpoints⟩ := hi
      refine ⟨earlier,hle',?_,?_⟩
      · have hdepthsucc : depth (n+1) = depth n + theta1/2 := by dsimp [depth]; push_cast; ring
        simpa only [hdepthsucc,Function.comp_apply] using htime.le
      · exact selected_chart_image_trace_of_extended_points (H (p (ell i))) earlier
          (last (p (ell i))) hle' (G (p (ell i))) (L (p (ell i))) (O (p (ell i))) j hpoints
  obtain ⟨n,hn⟩ := exists_nat_gt ((target - theta0) / (theta1/2))
  have htarget : target ≤ depth n := by
    have hh := (div_lt_iff₀ (by positivity : 0 < theta1/2)).mp hn
    dsimp [depth]
    linarith
  obtain ⟨f,hf,htraces⟩ := hind n
  refine ⟨f,hf,?_⟩
  exact selected_neck_slab_traces_mono_depth (fun i => H (f i)) (fun i => last (f i))
    (fun i => s (f i)) (fun i => G (f i)) (fun i => L (f i))
    (fun i => eta (f i)) (fun i => m (f i)) (fun i => O (f i)) htarget htraces

private theorem selected_neck_traces_at_depth_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / (O i).scale) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ i < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime *
          (G i).flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (last i)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ target : ℝ, ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ n : ℕ, ∀ᶠ i in atTop,
        ∃ (first : Fin ((H (f i)).eventCount + 1)) (hle : first ≤ last (f i)),
          (H (f i)).time first ≤ s (f i) - target / (O (f i)).scale ∧
          ∀ x ∈ (O (f i)).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
            Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, h⟩ :=
    selected_neck_traces_cylindrical_of_threshold_ratio
      D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa
  obtain ⟨P, ⟨e⟩⟩ := exists_threeModel_cylinder.{u}
  exact h H last s G L hinit eta m O heta hm hscale ha hsa P e spherePoint

private theorem prospective_neck_convergence_improving_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / (O i).scale) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ i < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime *
          (G i).flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (last i)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∃ (ind : ℕ → ℕ), StrictMono ind ∧
    ∃ (first : ∀ i, Fin ((H (ind i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (ind i))
      (hprecision : ∀ i, eta (ind i) ≤ δ) (horder : ∀ i, k ≤ m (ind i)),
    let N := fun i => ((O (ind i)).monoDelta (hprecision i) hδ1).lowerOrder (horder i)
    (∀ i, (H (ind i)).time (first i) ≤ s (ind i) - 2 / (O (ind i)).scale) ∧
    ∃ (K : ∀ i, Set (G (ind i)).terminalRegularOpen)
      (Phi : ∀ i, neckBuffer δ → (H (ind i)).backwardSurvivorIncomingFootprint
        (first i) (last (ind i)) (hle i) (G (ind i)) (K i))
      (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
      (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H (ind i)).backwardSurvivorIncomingFootprint (first i) (last (ind i)) (hle i)
            (G (ind i)) (K i)))
      (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
        (RealTimeInterval.closed (-2) 0 (by norm_num)))
      (rho : ℕ → ℕ),
      StrictMono rho ∧
      (∀ i, (H (ind i)).backwardSurvivorIncomingFootprintMap
        (first i) (last (ind i)) (hle i) (G (ind i)) (K i) ∘ Phi i = (N i).chart) ∧
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, (S i).base.metric 0 = (N i).normalizedMetric) ∧
      (∀ i t, (S i).base.metric t = localPullMetric
        (scaleMetric (N i).scale (N i).scale_pos (gflow i (s (ind i) + t / (N i).scale)))
        (Phi i) (hPhi i)) ∧
      (∀ i (j : Fin (H (ind i)).eventCount) (hf : first i ≤ j.castSucc)
          (hl : j.succ ≤ last (ind i)),
        ∀ t ∈ Icc ((H (ind i)).time j.castSucc) ((H (ind i)).time j.succ),
          gflow i t = (((H (ind i)).backwardSurvivorSlabMetric (first i) (last (ind i))
            (hle i) j hf hl t).restrictOpen
            ((H (ind i)).backwardSurvivorIncomingDomain (first i) (last (ind i)) (hle i)
                (G (ind i)))).restrictOpen
              ((H (ind i)).backwardSurvivorIncomingFootprint (first i) (last (ind i)) (hle i)
                  (G (ind i)) (K i))) ∧
      (∀ i t, t ∈ Icc ((H (ind i)).time (last (ind i))) (s (ind i)) →
        gflow i t = ((H (ind i)).backwardSurvivorIncomingMetric
          (first i) (last (ind i)) (hle i) (G (ind i)) (L (ind i)) t).restrictOpen
          ((H (ind i)).backwardSurvivorIncomingFootprint (first i) (last (ind i)) (hle i)
              (G (ind i)) (K i))) ∧
      (∀ A : Set (neckBuffer δ), IsCompact A → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn A p ((S (rho i)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < η) ∧
      ∀ᶠ i in atTop,
        ∃ Z : (b : ℕ) → Icc (-1 : ℝ) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Z b v x = iteratedDerivWithin b (fun t =>
            metricTensorField ((S (rho i)).base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-1 : ℝ) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hiter⟩ :=
    selected_neck_traces_at_depth_of_threshold_ratio D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hqlim hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark δ hδ hδ1 k
  obtain ⟨f, hf, htraces⟩ := hiter H last s G L hinit eta m O heta hm hscale ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hqlim hderiv hfinal
    hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark 2
  obtain ⟨g, hg, first, hle, radius, hradius, _, hfit0, _, _, _, hprec, hord, hstart, htrace⟩ :=
    exists_growing_selected_neck_trace_subsequence
      (fun i => H (f i)) (fun i => last (f i)) (fun i => s (f i))
      (fun i => G (f i)) (fun i => L (f i))
      (fun i => eta (f i)) (fun i => m (f i)) (fun i => O (f i))
      (heta.comp hf.tendsto_atTop) (hm.comp hf.tendsto_atTop) hδ k 2 htraces
  let ind := f ∘ g
  have hind : StrictMono ind := hf.comp hg
  let N := fun i => ((O (ind i)).monoDelta (hprec i) hδ1).lowerOrder (hord i)
  refine ⟨ind, hind, first, hle, hprec, hord, hstart, ?_⟩
  exact prospective_neck_convergence_growing_of_threshold_ratio
    (fun i => H (ind i)) (fun i => last (ind i)) first hle
    (fun i => s (ind i)) (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i))
    hδ hδ1 (fun i => eta (ind i)) (fun i => m (ind i)) (fun i => O (ind i))
    (heta.comp hind.tendsto_atTop) (hm.comp hind.tendsto_atTop) hprec hord N (fun _ => rfl)
    radius hradius hfit0 htrace hstart Ctime (fun i => q0 (ind i))
    (hqlim.comp hind.tendsto_atTop) (hscale.comp hind.tendsto_atTop)
    (fun i j _ hj => hderiv (ind i) j hj) (fun i => hfinal (ind i)) hphi
    (fun i j _ hj => hpinch (ind i) j hj) (fun i => hpinchFinal (ind i))

private theorem exists_subsequence_selected_neck_append_backward_of_threshold_ratio
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (s : ℕ → ℝ) (Qstage : ℕ → OrientedThreeStage.{u})
      (E : ∀ i, MetricCutCapEvent ((H i).stage (Fin.last (H i).eventCount)) (Qstage i)
        ((H i).time (Fin.last (H i).eventCount)) (s i)),
    ∀ hinit : ∀ i, (E i).incoming.flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount),
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (E i).terminal.metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ Fin.last (H i).eventCount → ∀ b,
        (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
    Tendsto (fun i => q₀ i / (O i).scale) atTop (𝓝 0) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ i < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (s i), q₀ i <
        (E i).incoming.flow.scalar t y →
      |derivWithin (fun v => (E i).incoming.flow.scalar v y) (Iic t) t| ≤ Ctime *
          (E i).incoming.flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (E i).incoming.flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt
            ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b)
            (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
              (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius →
            ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion
          (((records i j).static b).witness.cap z)) →
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ (hprecision : ∀ i, eta (ind i) ≤ δ) (horder : ∀ i, k ≤ m (ind i)),
      let N := fun i => ((O (ind i)).monoDelta (hprecision i) hδ1).lowerOrder (horder i)
      ∀ᶠ i in atTop,
        ∃ N' : NormalizedNeck (((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i))
          (hinit (ind i))).event (Fin.last (H (ind i)).eventCount)).terminal.metric δ k,
          HEq N' (N i) ∧ Nonempty (IncomingBackwardNeck
            ((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i)) (hinit (ind i)))
            (Fin.last (H (ind i)).eventCount) N' (Real.sqrt (N i).scale⁻¹)) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hrec⟩ :=
    prospective_neck_convergence_improving_of_threshold_ratio D r eps a₀ Ctime ha₀ heps
        hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H s Qstage E hinit eta m O heta hm hscale a ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hqlim hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark δ hδ hδ1 k
  obtain ⟨ind, hind, first, hle, hprec, hord, hstart, K, Phi, hPhi, gflow, S, rho, hrho,
    hmap, hS, hterminal, hmetric, hslabs, hlast, _, hjets⟩ :=
    hrec H (fun i => Fin.last (H i).eventCount) s (fun i => (E i).incoming)
      (fun i => (E i).terminal) hinit eta m O heta hm hscale ha hsa
      parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hqlim hderiv hfinal
      hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark hδ hδ1 k
  let N := fun i => ((O (ind i)).monoDelta (hprec i) hδ1).lowerOrder (hord i)
  refine ⟨ind ∘ rho, hind.comp hrho, (fun i => hprec (rho i)), (fun i => hord (rho i)), ?_⟩
  filter_upwards [hjets] with i hi
  obtain ⟨Z, hZ, eta', heta', hclose⟩ := hi
  have hclock : (H (ind (rho i))).time (first (rho i)) ≤ s (ind (rho i)) - (N (rho i)).scale⁻¹ := by
    apply (hstart (rho i)).trans
    have hscale : (N (rho i)).scale = (O (ind (rho i))).scale := rfl
    rw [hscale, inv_eq_one_div]
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (O (ind (rho i))).scale_pos.le
  obtain ⟨N', hN', B, _, _⟩ := NormalizedNeck.exists_incomingBackwardNeck_appendEvent
    (H (ind (rho i))) (first (rho i)) (hle (rho i)) (E (ind (rho i))) (hinit (ind (rho i)))
    (N (rho i)) (K (rho i)) (Phi (rho i)) (hPhi (rho i)) (hmap (rho i)) (gflow (rho i))
    (by norm_num : (1 : ℝ) < 2) (S (rho i)) (hS (rho i)) (hterminal (rho i))
    (fun t _ => hmetric (rho i) t) (hslabs (rho i)) (hlast (rho i)) hclock Z hZ
        ⟨eta', heta', hclose⟩
  exact ⟨N', hN', ⟨B⟩⟩

private theorem selected_neck_append_backward_uniform_of_threshold_ratio
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ a : ℝ, 0 < a →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ ηstar : ℝ, ∃ mstar : ℕ, ∃ Λ : ℝ,
      0 < ηstar ∧ ηstar ≤ δ ∧ k ≤ mstar ∧ 0 < Λ ∧
    ∀ q₀ : ℝ, 0 < q₀ →
    ∀ (H : ObservedHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime *
          E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        (H.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        normalizedDatum (H.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    η ≤ ηstar → mstar ≤ m → Λ * max q₀ 1 ≤ O.scale →
    ∀ (hprec : η ≤ δ) (hord : k ≤ m),
    let N := (O.monoDelta hprec hδ1).lowerOrder hord
    ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹)) := by
  classical
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hseq⟩ :=
    exists_subsequence_selected_neck_append_backward_of_threshold_ratio D r tol a₀ Ctime ha₀ htol
        htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a ha phi hphi
  by_contra hnot
  push Not at hnot
  have hfail (n : ℕ) := hnot (min (δ / 2) (1 / ((n : ℝ) + 1))) (k + n) ((n : ℝ) + 1)
    (lt_min (half_pos hδ) (by positivity))
    ((min_le_left _ _).trans (half_le_self hδ.le)) (Nat.le_add_right k n) (by positivity)
  choose q0 hq0 H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy
      hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale hprec hord hbad using hfail
  have hηlim : Tendsto η atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (O n).delta_pos.le)
      (fun n => (hη n).trans (min_le_right _ _))
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hmlim : Tendsto m atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_add_atTop_nat k)
    intro n
    have hn := hm n
    omega
  have hscaleLower (n : ℕ) : (n : ℝ) + 1 ≤ (O n).scale :=
    (le_mul_of_one_le_right (by positivity) (le_max_right _ _)).trans (hscale n)
  have hscaleLim : Tendsto (fun n => (O n).scale) atTop atTop :=
    tendsto_atTop_mono hscaleLower
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hratio (n : ℕ) : q0 n / (O n).scale ≤ 1 / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (O n).scale_pos (by positivity)]
    calc q0 n * ((n : ℝ) + 1) ≤ max (q0 n) 1 * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = ((n : ℝ) + 1) * max (q0 n) 1 := mul_comm _ _
      _ ≤ (O n).scale := hscale n
      _ = 1 * (O n).scale := (one_mul _).symm
  have hqlim : Tendsto (fun n => q0 n / (O n).scale) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (div_pos (hq0 n) (O n).scale_pos).le) hratio
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  obtain ⟨ind, hind, hprecision, horder', hsuccess⟩ :=
    hseq H s Qstage E hinit η m O hηlim hmlim hscaleLim ha hsa parameters records
      hfixed hlower (Eventually.of_forall fun i j _ => hdelta i j)
      (Eventually.of_forall haccuracy) hmargin horder q0 hq0 hqlim
      (fun i j _ => hderiv i j) hfinal hphi (fun i j _ => hpinch i j) hpinchFinal
      (fun i j _ => hcap i j)
      (fun i j _ => center i j) (fun i j _ => precision i j) (fun i j _ => order i j)
      (fun i j _ => d i j) (fun i j _ => w i j) (fun i j _ => Jbig i j)
      (fun i j _ => hJbig i j) (fun i j _ => hzero i j) (fun i j _ => hmark i j)
      hδ hδ1 k
  obtain ⟨n, hn⟩ := hsuccess.exists
  obtain ⟨N', hN', hB⟩ := hn
  exact hbad (ind n) ⟨N', hN', hB⟩

theorem exists_threshold_uniform_selected_neck_append_backward
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ a : ℝ, 0 < a →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Λ : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Λ ∧
    ∀ q₀ : ℝ, 0 < q₀ →
    ∀ (H : ObservedHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime *
          E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        (H.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        normalizedDatum (H.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Λ * max q₀ 1 ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹)) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hthreshold⟩ :=
    selected_neck_append_backward_uniform_of_threshold_ratio D r tol a₀ Ctime ha₀ htol
        htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a ha phi hphi
  obtain ⟨ηstar, mstar, Λ, hηstar, hηδ, hkm, hΛ, hmain⟩ :=
    hthreshold hδ hδ1 k a ha phi hphi
  refine ⟨ηstar, mstar, Λ, hηδ, hkm, hηstar, hΛ, ?_⟩
  intro q₀ hq₀ H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy
      hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale
  exact hmain q₀ hq₀ H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy
      hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale (hη.trans hηδ) (hkm.trans hm)

private theorem exists_uniform_selected_neck_append_backward_of_threshold_uniform
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ (a q₀ : ℝ), 0 < a → 0 < q₀ →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Qmin : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Qmin ∧
    ∀ (H : ObservedHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime *
          E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        (H.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        normalizedDatum (H.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v)
            (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Qmin ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹)) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, h⟩ :=
    exists_threshold_uniform_selected_neck_append_backward D r tol a₀ Ctime ha₀ htol
      htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a q₀ ha hq₀ phi hphi
  obtain ⟨ηstar, mstar, Λ, hηδ, hkm, hηstar, hΛ, hmain⟩ := h hδ hδ1 k a ha phi hphi
  exact ⟨ηstar, mstar, Λ * max q₀ 1, hηδ, hkm, hηstar,
    mul_pos hΛ (lt_max_of_lt_right one_pos), hmain q₀ hq₀⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
