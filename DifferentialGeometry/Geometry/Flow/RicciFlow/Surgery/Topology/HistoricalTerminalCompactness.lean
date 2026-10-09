import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalConeExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryTerminalVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalMetricExtraction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalMetricExtension
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section
open Set Bundle Manifold Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem exists_local_metric_limit_on_original_balls
    (X : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel))
    (g₀ : ∀ k, SmoothRiemannianMetric ThreeModel (X.obj k).M)
    (hcomplete : SeqMetricComplete (I := ThreeModel) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := ThreeModel)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := ThreeModel) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := ThreeModel) (X.obj k) x η)
    (hmetric : ∀ᶠ k in atTop, ∀ y ∈ riemannianBallOf
      (X.obj k).metric (X.obj k).basepoint R,
      (g₀ k).inner y = (X.obj k).metric.inner y)
    (hballs : ∀ n, riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r =
      riemannianClosedBallOf (g₀ n) (X.obj n).basepoint r)
    (houter : ∀ n, riemannianBallOf (X.obj n).metric (X.obj n).basepoint R ⊆
      riemannianClosedBallOf (g₀ n) (X.obj n).basepoint R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Q : Type, ∃ top : TopologicalSpace Q, letI := top
      ∃ charts : ChartedSpace ThreeSpace Q, letI := charts
      ∃ hman : IsManifold ThreeModel ∞ Q, letI := hman
      ∃ hT2 : T2Space Q, letI := hT2
      ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
      ∃ (gQ : SmoothRiemannianMetric ThreeModel Q)
        (V : TopologicalSpace.Opens Q) (q : Q)
        (Φ : ∀ k, PartialDiffeomorph ThreeModel ThreeModel Q
          (X.obj (phi k)).M ∞)
        (G : ℕ → SmoothRiemannianMetric ThreeModel V),
        IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
        (∀ k, closure (V : Set Q) ⊆ (Φ k).source) ∧
        (∀ k, Φ k q = (X.obj (phi k)).basepoint) ∧
        (∀ k, riemannianClosedBallOf (g₀ (phi k))
          (X.obj (phi k)).basepoint r ⊆ (Φ k) '' (V : Set Q)) ∧
        (∀ k, (Φ k) '' closure (V : Set Q) ⊆
          riemannianClosedBallOf (g₀ (phi k)) (X.obj (phi k)).basepoint R) ∧
        (∀ k (x : V) (v w : TangentSpace ThreeModel x),
          (G k).inner x v w = (g₀ (phi k)).inner (Φ k x)
            (mfderiv ThreeModel ThreeModel (Φ k) (x : Q) v)
            (mfderiv ThreeModel ThreeModel (Φ k) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨phi,hphi,Q,top,charts,hman,hT2,hsecond,gQ,V,q,Φ,G,hV,hq,hsource,hbase,hcapture,himage,hG,hconv⟩ :=
    exists_finite_pointed_metric_convergence_of_local_metric_agreement X g₀ hcomplete hconn
      hr hrR hη hjets hinj hmetric
  refine ⟨phi,hphi,Q,top,charts,hman,hT2,hsecond,gQ,V,q,Φ,G,hV,hq,hsource,hbase,?_,?_,hG,hconv⟩
  · intro n
    rw [← hballs]
    exact hcapture n
  · exact fun n => (himage n).trans (houter (phi n))

theorem exists_historical_footprint_terminal_metric_limit
    (A : ℕ → ObservedHistory.{u}) (i : ∀ n, Fin (A n).eventCount)
    (first : ∀ n, Fin ((A n).eventCount + 1)) (hle : ∀ n, first n ≤ (i n).castSucc)
    (δ₀ : ℕ → ℝ) (eps : ℝ) (k : ℕ → ℕ)
    (N : ∀ n, NormalizedNeck ((A n).event (i n)).terminal.metric (δ₀ n) (k n))
    (hprecision : ∀ n, δ₀ n ≤ eps) (hk : ∀ n, ⌈eps⁻¹⌉₊ ≤ k n)
    (a : ℝ) (ha : 24 < a) (hfit : 4 * a < eps⁻¹)
    (htrace : ∀ n, ∀ x ∈ (N n).chart ''
      {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
        Nonempty (BackwardPointTrace (A n) (first n) (i n).castSucc (hle n) x.val)) :
    ∀ (p : ∀ n, (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})),
      (∀ n, (A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}) (p n) =
        (N n).center) →
    ∀ g₀ : ∀ n, SmoothRiemannianMetric ThreeModel
        ((A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})),
      (∀ n, g₀ n = scaleMetric (N n).scale (N n).scale_pos
        (localPullMetric ((A n).event (i n)).terminal.metric
          ((A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))
          ((A n).backwardSurvivorFootprintMap_isLocalDiffeomorph (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})))) →
      (∀ n, IsCompact (riemannianClosedBallOf (g₀ n) (p n) (2*a))) →
      (∀ n, ∀ x ∈ riemannianClosedBallOf (g₀ n) (p n) (2*a),
        curvDerivNormSq 0 (g₀ n) x ≤ (8 * Real.sqrt 3)^2) →
      (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        ∀ x ∈ riemannianClosedBallOf (g₀ n) (p n) (a/2), curvDerivNorm m (g₀ n) x ≤ C) →
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        ∃ Q : Type, ∃ top : TopologicalSpace Q, letI := top
        ∃ charts : ChartedSpace ThreeSpace Q, letI := charts
        ∃ hman : IsManifold ThreeModel ∞ Q, letI := hman
        ∃ hT2 : T2Space Q, letI := hT2
        ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
        ∃ (gQ : SmoothRiemannianMetric ThreeModel Q)
          (V : TopologicalSpace.Opens Q) (q : Q)
          (Φ : ∀ n, PartialDiffeomorph ThreeModel ThreeModel Q
            ((A (phi n)).backwardSurvivorFootprintInterior
              (first (phi n)) (i (phi n)) (hle (phi n)) ((N (phi n)).chart '' {z : neckBuffer (δ₀ (phi n)) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})) ∞)
          (G : ℕ → SmoothRiemannianMetric ThreeModel V),
          IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
          (∀ n, closure (V : Set Q) ⊆ (Φ n).source) ∧
          (∀ n, Φ n q = p (phi n)) ∧
          (∀ n, riemannianClosedBallOf (g₀ (phi n)) (p (phi n)) (a/16) ⊆
            (Φ n) '' (V : Set Q)) ∧
          (∀ n, (Φ n) '' closure (V : Set Q) ⊆
            riemannianClosedBallOf (g₀ (phi n)) (p (phi n)) (a/8)) ∧
          (∀ n (x : V) (v w : TangentSpace ThreeModel x),
            (G n).inner x v w = (g₀ (phi n)).inner (Φ n x)
              (mfderiv ThreeModel ThreeModel (Φ n) (x : Q) v)
              (mfderiv ThreeModel ThreeModel (Φ n) (x : Q) w)) ∧
          MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  intro p hp g₀ hg₀ hcpt hcurv hderiv
  classical
  let K := fun n => (N n).chart ''
    {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
  let W := fun n => (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) (K n)
  obtain ⟨η,hη,hinjectivity⟩ := exists_complete_historical_footprint_metric_with_injectivity.{u}
  choose g' U hcomplete hU hKU heq hlemetric hjets hclosed hinj using fun n =>
    hinjectivity (N n) (hprecision n) (hk n) a ha hfit (htrace n) (p n) (hp n)
      (g₀ n) (hg₀ n) (hcpt n) (hcurv n)
  let X : PointedRiemannianSeq.{u,0,0} ThreeModel := {
    obj := fun n => { M := W n, basepoint := p n, metric := g' n } }
  have hcompleteX : SeqMetricComplete X := ⟨fun n => (hcomplete n).complete⟩
  have hconn : ∀ n, ConnectedSpace (X.obj n).M := by
    intro n
    exact (N n).connectedSpace_historical_footprint (hprecision n) a (by linarith) hfit (htrace n)
  have hjetsX : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in Filter.atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint (a/8) m C := by
    intro m
    obtain ⟨C,hC,hbound⟩ := hderiv m
    refine ⟨C,hC,Filter.Eventually.of_forall fun n x hx => ?_⟩
    have hx' : x ∈ riemannianClosedBallOf (g₀ n) (p n) (a/8) := by
      rw [← hclosed n (a/8) (by linarith) (by linarith)]
      exact hx
    have hx2 : x ∈ riemannianClosedBallOf (g₀ n) (p n) (2*a) :=
      hx'.trans (ENNReal.ofReal_le_ofReal (by linarith))
    change curvDerivNorm m (g' n) x ≤ C
    rw [hjets n m x (hKU n hx2)]
    exact hbound n x (hx'.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hinjX : ∀ᶠ n in Filter.atTop, ∀ x : (X.obj n).M,
      riemannianEDistOf (X.obj n).metric (X.obj n).basepoint x ≤ ENNReal.ofReal (a/16) →
        HasInjRadiusAt (X.obj n) x η := by
    refine Filter.Eventually.of_forall fun n x hx => ?_
    exact hasInjRadiusAt_of_expMap_injOn (X.obj n) x hη
      (hinj n x (hx.trans (ENNReal.ofReal_le_ofReal (by linarith))))
  have hagree : ∀ᶠ n in Filter.atTop, ∀ x ∈ riemannianBallOf
      (X.obj n).metric (X.obj n).basepoint (a/8), (g₀ n).inner x = (X.obj n).metric.inner x := by
    refine Filter.Eventually.of_forall fun n x hx => ?_
    have hx' : x ∈ riemannianClosedBallOf (g₀ n) (p n) (a/8) := by
      rw [← hclosed n (a/8) (by linarith) (by linarith)]
      exact le_of_lt (show riemannianEDistOf (g' n) (p n) x < ENNReal.ofReal (a/8) from hx)
    exact (heq n x (hKU n (hx'.trans (ENNReal.ofReal_le_ofReal (by linarith))))).symm
  apply exists_local_metric_limit_on_original_balls X
    (fun n => (g₀ n : SmoothRiemannianMetric ThreeModel (X.obj n).M)) hcompleteX hconn
    (by linarith : 0 ≤ a/16) (by linarith : a/16 < a/8) hη hjetsX hinjX hagree
  · intro n
    exact hclosed n (a/16) (by linarith) (by linarith)
  · intro n x hx
    rw [← hclosed n (a/8) (by linarith) (by linarith)]
    exact le_of_lt (show riemannianEDistOf (g' n) (p n) x < ENNReal.ofReal (a/8) from hx)

private local instance (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) := by
  let _ : SigmaCompactSpace (H.toHistory.backwardSurvivorDomain first (Fin.last H.eventCount)
      (Fin.le_last first)) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.toHistory.backwardSurvivorDomain first (Fin.last H.eventCount) (Fin.le_last first)).isOpen)
  let _ : SigmaCompactSpace (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
      (Fin.le_last first) G) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) (Fin.le_last first) G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel
    (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K).isOpen)

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem RetainedCoreHistory.exists_uniform_normalized_incomingFootprint_volume_radius_of_scaled_bound
    {R θ C σ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hC : 0 ≤ C) (hσ : 0 < σ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
    ∀ (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    , H.horizon < s → ∀ (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    , (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    → (∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    → ∀ (p : H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) {Q κ : ℝ} (hQ : 1 ≤ Q),
    IsCompact (riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s)) p R) →
    H.time first ≤ s - θ / Q →
    (∀ v ∈ Ico (-θ) 0, ∀ z : H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K,
      normSq0S (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow (s + v / Q))) z 4
        (metricRm04At (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow (s + v / Q))) z) ≤ C) →
     (∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) →
    ∀ x ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s)) p (R / 4),
      ENNReal.ofReal (κ * a ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s))
          (riemannianBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s)) x a) := by
  obtain ⟨a₀, ha₀, hvol⟩ :=
    RetainedCoreHistory.exists_uniform_normalized_incomingFootprint_volume_radius hR hθ hC hσ
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha haa₀ H s G L hinit hs first K gflow hslabs hlast p Q κ hQ hcpt hroom hbound htested x hx
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hphysical : ∀ v ∈ Ico (s - θ / Q) s, ∀ z : H.toHistory.backwardSurvivorIncomingFootprint
      first (Fin.last H.eventCount) (Fin.le_last first) G K,
      normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ C * Q ^ 2 := by
    intro v hv z
    have hu : Q * (v - s) ∈ Ico (-θ) 0 := by
      constructor
      · have hh := mul_le_mul_of_nonneg_left hv.1 hQpos.le
        field_simp at hh
        nlinarith
      · exact mul_neg_of_pos_of_neg hQpos (sub_neg.mpr hv.2)
    have hclock : s + (Q * (v - s)) / Q = v := by field_simp; ring
    have hb := hbound (Q * (v - s)) hu z
    rw [hclock] at hb
    have hscale : normSq0S (scaleMetric Q hQpos (gflow v)) z 4
        (metricRm04At (scaleMetric Q hQpos (gflow v)) z) =
        Q⁻¹ ^ 2 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) := by
      change CheegerGromovCompactness.curvDerivNormSq 0 (scaleMetric Q hQpos (gflow v)) z =
        Q⁻¹ ^ 2 * CheegerGromovCompactness.curvDerivNormSq 0 (gflow v) z
      rw [CheegerGromovCompactness.curvDerivNormSq_scaleMetric]
    rw [hscale] at hb
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg Q)
    have heq : Q ^ 2 * (Q⁻¹ ^ 2 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z)) =
        normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) := by field_simp
    rw [heq] at hh
    simpa only [mul_comm C] using hh
  exact hvol a ha haa₀ H G L hinit hs first K gflow hslabs hlast p hQ
    hcpt hroom hphysical htested x hx


theorem exists_pointed_convergence_of_tested_incomingFootprint_flows
    {R θ C σ κ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hC : 0 < C) (hσ : 0 < σ) (hκ : 0 < κ)
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (first : ∀ n, Fin ((H n).eventCount + 1)) (K : ∀ n, Set (G n).terminalRegularOpen) :
    let W := fun n => (H n).toHistory.backwardSurvivorIncomingFootprint (first n)
      (Fin.last (H n).eventCount) (Fin.le_last (first n)) (G n) (K n)
    ∀ (gflow : ∀ n, ℝ → SmoothRiemannianMetric ThreeModel (W n)) (p : ∀ n, W n)
      (Q : ℕ → ℝ) (hQ : ∀ n, (1 : ℝ) ≤ Q n),
    (∀ n (j : Fin (H n).eventCount) (hf : first n ≤ j.castSucc),
      ∀ v ∈ Icc ((H n).time j.castSucc) ((H n).time j.succ),
        gflow n v = (((H n).toHistory.backwardSurvivorSlabMetric (first n)
          (Fin.last (H n).eventCount) (Fin.le_last (first n)) j hf (Fin.le_last _) v).restrictOpen
            ((H n).toHistory.backwardSurvivorIncomingDomain (first n) (Fin.last (H n).eventCount)
              (Fin.le_last (first n)) (G n))).restrictOpen (W n)) →
    (∀ n, ∀ v ∈ Icc ((H n).time (Fin.last (H n).eventCount)) (s n),
      gflow n v = ((H n).toHistory.backwardSurvivorIncomingMetric (first n)
        (Fin.last (H n).eventCount) (Fin.le_last (first n)) (G n) (L n) v).restrictOpen (W n)) →
    (∀ n, (H n).time (first n) ≤ s n - θ / Q n) →
    let S := fun n => ({ base.metric := fun v => scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (gflow n (s n + v / Q n)) } : SolutionOn (I := ThreeModel) (M := W n)
        (RealTimeInterval.closed (-θ) 0 (by linarith)))
    (∀ n, IsSolutionOn (S n)) →
    (∀ n, IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (p n) R)) →
    (∀ n, ∀ v ∈ Icc (-θ) 0, ∀ z : W n,
      normSq0S ((S n).base.metric v) z 4 (metricRm04At ((S n).base.metric v) z) ≤ C ^ 2) →
    (∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      {obj := fun n => { M := W n, basepoint := p n, metric := (S n).base.metric 0 }}
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < (R / 4)) ∧ Tendsto r atTop (𝓝 (R / 4)) ∧
      ∃ (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent L f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ C : MetricConvergenceData F',
        (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal (R / 4)) ∧
        (∀ q : ℝ, 0 ≤ q → q < (R / 4) → IsCompact (riemannianClosedBallOf L.metric L.basepoint q)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ x ∈ F'.source n, ∀ v : TangentSpace ThreeModel x,
          (1 - eps) * L.metric.inner x v v ≤
            (X.obj (f n)).metric.inner (F'.map n x) (mfderiv ThreeModel ThreeModel (F'.map n) x v) (mfderiv ThreeModel ThreeModel (F'.map n) x v) ∧
          (X.obj (f n)).metric.inner (F'.map n x) (mfderiv ThreeModel ThreeModel (F'.map n) x v) (mfderiv ThreeModel ThreeModel (F'.map n) x v) ≤
            (1 + eps) * L.metric.inner x v v := by
  intro W gflow p Q hQ hslabs hlast hroom S hS hcompact hcurv htested X
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨a₀, ha₀, hvol⟩ :=
    RetainedCoreHistory.exists_uniform_normalized_incomingFootprint_volume_radius_of_scaled_bound
      hR hθ (sq_nonneg C) hσ
  have hz (n) : (S n).base.metric 0 = scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (gflow n (s n)) := by
    simp only [S, zero_div, add_zero]
  apply exists_pointed_terminal_metric_convergence_of_local_curvature_and_volume_lower_bound
    X S hS hR hC (by linarith : -θ < 0) Subset.rfl Subset.rfl (fun _ => rfl)
    (Eventually.of_forall hcompact)
    (Eventually.of_forall fun n v hv z _ => hcurv n v hv z) ha₀ hκ
  intro a ha haa₀
  refine Eventually.of_forall fun n x hx => ?_
  have hh := hvol a ha haa₀ (H n) (G n) (L n) (hinit n) (hs n) (first n) (K n)
    (gflow n) (hslabs n) (hlast n) (p n) (hQ n)
    (by rw [← hz]; exact hcompact n) (hroom n)
    (fun v hv z => hcurv n v ⟨hv.1, hv.2.le⟩ z) (htested n) x (by simpa only [X, hz] using hx)
  simpa only [hdim, X, hz] using hh

theorem tested_incomingFootprint_flow_rescaled_cone_exclusion
    {R θ C σ κ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hC : 0 < C) (hσ : 0 < σ) (hκ : 0 < κ)
    {End : Type u} [MetricSpace End] [ChartedSpace ThreeSpace End] [IsManifold ThreeModel ∞ End]
    (gW : SmoothRiemannianMetric ThreeModel End)
    (hWmetric : ∀ a b : End, edist a b = riemannianEDistOf gW a b)
    {q : UniformSpace.Completion End} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    (x : ℕ → End) (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    {Rcmp lower upper : ℝ} (hRcmp : 0 < Rcmp) (hlower : 0 < lower)
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (first : ∀ n, Fin ((H n).eventCount + 1)) (K : ∀ n, Set (G n).terminalRegularOpen) :
    let W := fun n => (H n).toHistory.backwardSurvivorIncomingFootprint (first n)
      (Fin.last (H n).eventCount) (Fin.le_last (first n)) (G n) (K n)
    ∀ (gflow : ∀ n, ℝ → SmoothRiemannianMetric ThreeModel (W n)) (p : ∀ n, W n)
      (Q : ℕ → ℝ) (hQ : ∀ n, (1 : ℝ) ≤ Q n),
    (∀ n (j : Fin (H n).eventCount) (hf : first n ≤ j.castSucc),
      ∀ v ∈ Icc ((H n).time j.castSucc) ((H n).time j.succ),
        gflow n v = (((H n).toHistory.backwardSurvivorSlabMetric (first n)
          (Fin.last (H n).eventCount) (Fin.le_last (first n)) j hf (Fin.le_last _) v).restrictOpen
            ((H n).toHistory.backwardSurvivorIncomingDomain (first n) (Fin.last (H n).eventCount)
              (Fin.le_last (first n)) (G n))).restrictOpen (W n)) →
    (∀ n, ∀ v ∈ Icc ((H n).time (Fin.last (H n).eventCount)) (s n),
      gflow n v = ((H n).toHistory.backwardSurvivorIncomingMetric (first n)
        (Fin.last (H n).eventCount) (Fin.le_last (first n)) (G n) (L n) v).restrictOpen (W n)) →
    (∀ n, (H n).time (first n) ≤ s n - θ / Q n) →
    let S := fun n => ({ base.metric := fun v => scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (gflow n (s n + v / Q n)) } : SolutionOn (I := ThreeModel) (M := W n)
        (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)))
    (∀ n, IsSolutionOn (S n)) →
    (∀ n, IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (p n) R)) →
    (∀ n, ∀ v ∈ Icc (-θ) 0, ∀ z : W n,
      normSq0S ((S n).base.metric v) z 4 (metricRm04At ((S n).base.metric v) z) ≤ C ^ 2) →
    (∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) →
    (∀ n, metricScalarAt ((S n).base.metric 0) (p n) = 1) →
    ∀ {Phi : ℝ → ℝ}, (Perelman.AdmissiblePinchingFunction Phi) →
    (Tendsto Q atTop atTop) →
    (∀ t ∈ Icc (-θ) 0, ∀ᶠ n in atTop,
      ∀ z ∈ riemannianClosedBallOf ((S n).base.metric 0) (p n) R,
        curvatureOperatorLowerBoundAt ((S n).base.metric t) z
          (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) z)
          (Perelman.rescalePinchingFunction (Q n) Phi (metricScalarAt ((S n).base.metric t) z))) →
    ∀ (Bmap : ∀ n, PartialDiffeomorph ThreeModel ThreeModel End (W n) ∞),
    (∀ n, riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) Rcmp ⊆ (Bmap n).source) →
    (∀ n, Bmap n (x n) = (p n)) →
    (∀ n, riemannianClosedBallOf ((S n).base.metric 0) (p n) (Rcmp/4) ⊆
      (Bmap n) '' riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) Rcmp) →
    (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) Rcmp,
      ∀ v : TangentSpace ThreeModel y,
        (1-eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          ((S n).base.metric 0).inner (Bmap n y) (mfderiv ThreeModel ThreeModel (Bmap n) y v) (mfderiv ThreeModel ThreeModel (Bmap n) y v) ∧
        ((S n).base.metric 0).inner (Bmap n y) (mfderiv ThreeModel ThreeModel (Bmap n) y v) (mfderiv ThreeModel ThreeModel (Bmap n) y v) ≤
          (1+eta)*(scaleMetric (scale n) (hscale n) gW).inner y v v) →
    (∀ᶠ n in atTop, dist (x n : UniformSpace.Completion End) q /
      (1 / Real.sqrt (scale n)) ∈ Icc lower upper) → False := by
  intro W gflow p Q hQ hslabs hlast hroom S hS hcompact hcurv htested hbaseOne
    Phi hPhi hQtop hpinching Bmap hBsource hBbase hcapture hBconv hcenter
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    {obj := fun n => { M := W n, basepoint := p n, metric := (S n).base.metric 0 }}
  obtain ⟨a₀, ha₀, hvol⟩ :=
    RetainedCoreHistory.exists_uniform_normalized_incomingFootprint_volume_radius_of_scaled_bound
      hR hθ (sq_nonneg C) hσ
  have hz (n) : (S n).base.metric 0 = scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (gflow n (s n)) := by
    simp only [S, zero_div, add_zero]
  apply source_flow_rescaled_cone_exclusion_of_curvature_and_volume_lower_bounds
    X S hS hθ Subset.rfl Subset.rfl (fun _ => rfl) hbaseOne C R hC hR hcompact
    (fun n t ht z _ => hcurv n t ht z) ha₀ hκ _ hPhi Q
    (fun n => zero_lt_one.trans_le (hQ n)) hQtop hpinching
    gW hWmetric cone x scale hscale hscaleTop Bmap hRcmp hlower hBsource hBbase hcapture hBconv hcenter
  intro a ha haa₀
  refine Eventually.of_forall fun n x hx => ?_
  have hh := hvol a ha haa₀ (H n) (G n) (L n) (hinit n) (hs n) (first n) (K n)
    (gflow n) (hslabs n) (hlast n) (p n) (hQ n)
    (by rw [← hz]; exact hcompact n) (hroom n)
    (fun v hv z => hcurv n v ⟨hv.1, hv.2.le⟩ z) (htested n) x (by simpa only [X, hz] using hx)
  simpa only [X, hz] using hh
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
