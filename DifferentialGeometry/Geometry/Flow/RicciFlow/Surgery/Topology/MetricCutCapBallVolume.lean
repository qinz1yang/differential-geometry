import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedMetricCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventProtectedBalls

noncomputable section
open Set Function TopologicalSpace Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
attribute [local instance] threeBallChartedSpace threeBall_isManifold
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_isManifold transitionEnd_pos hB

private local instance {P Q : OrientedThreeStage.{u}} {a s : ℝ} (event : MetricCutCapEvent P Q a s) :
    MeasurableSpace event.incoming.terminalRegularOpen := borel event.incoming.terminalRegularOpen
private local instance {P Q : OrientedThreeStage.{u}} {a s : ℝ} (event : MetricCutCapEvent P Q a s) :
    BorelSpace event.incoming.terminalRegularOpen := ⟨rfl⟩
private local instance {P Q : OrientedThreeStage.{u}} {a s : ℝ} (event : MetricCutCapEvent P Q a s) :
    SigmaCompactSpace event.incoming.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel event.incoming.terminalRegularOpen.isOpen)

theorem exists_uniform_metricCutCapEvent_ball_volume_lower_or_terminal_volume :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]
        [IsManifold ThreeModel ∞ M] [CompactSpace M],
      ∀ {ι : Type} [Fintype ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ε ≤ 1 / 2 → transitionEnd + 2 < D →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
      let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
      let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
      let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
      let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
      let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
      let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
      ∀ (o : SmoothOrientation ThreeModel M)
        (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))
        (oQ : SmoothOrientation ThreeModel Qcap) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y))
        {t₀ t₁ : ℝ}
        (event : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
          (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁),
      event.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      event.capped = OrientedThreeStage.ofSmoothOrientation Qcap oQ →
      HEq event.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ (fun i => (d₀ i).precision_lt_one)
          f hf hdisj R hnontrivial).reparametrizeCaps
            (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary) →
      event.old = event.transition.trace.retainedCore →
      event.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs U g R hRet c hc
        x₀ order d₀ hOriginal hrec d hmap hside w →
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ q : Ret,
        (∀ r : ℝ, 0 < r → r ≤ r₀ →
          ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
              event.outputMetric (riemannianBallOf event.outputMetric q r)) ∨
        ∃ p : event.incoming.terminalRegularOpen, event.RegularCrossing p.val q ∧
          IsCompact (riemannianClosedBallOf event.terminal.metric p r₀) ∧
          ∀ r : ℝ, 0 < r → r ≤ r₀ →
            riemannianVolumeMeasure ThreeModel (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
              event.outputMetric (riemannianBallOf event.outputMetric q r) =
              riemannianVolumeMeasure ThreeModel event.incoming.terminalRegularOpen event.terminal.metric
                (riemannianBallOf event.terminal.metric p r) := by
  obtain ⟨ν, hν, hbound⟩ :=
    exists_uniform_finiteFullPreparedMetric_small_ball_volume_lower_or_retained_neighborhood.{0, 0, u, 0}
  refine ⟨ν, hν, ?_⟩
  intro M _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
    k' hrec d hmap hside A D ε hA m w heps hD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
  let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
  dsimp only
  intro o hnontrivial oQ oRet oDisc B a hboundary t₀ t₁ event hDisc hCap htrace hOld hmetric
  obtain ⟨r₀, hr₀, hballs⟩ := hbound ThreeModel hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
    hrec d hmap hside w heps hD
  have hrange := MetricCutCapEvent.range_oldOutput_eq_of_buffered_trace transitionEnd_pos hδ
    (fun i => (d₀ i).precision_lt_one) f hf hdisj hs R o hnontrivial oQ oRet oDisc B a hboundary
    event hDisc hCap htrace hOld
  refine ⟨r₀, hr₀, ?_⟩
  intro q
  rcases hballs q with hvolume | hbuffer
  · left
    intro r hr hrr
    rw [hmetric]
    exact hvolume r hr hrr
  right
  have hprotected : riemannianClosedBallOf event.outputMetric q (3 * r₀ / 2) ⊆
      interior (range event.oldOutput) := by
    rw [hrange, hmetric]
    intro y hy
    apply hbuffer
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 2 * r₀)).mpr (by linarith))
  obtain ⟨p, hp, hcpt, hvol⟩ := event.exists_terminal_ball_compact_volume_eq_of_output_buffer q hprotected
  refine ⟨p, hp, hcpt r₀ hr₀.le (by linarith), ?_⟩
  intro r hr hrr
  exact hvol r hr (by linarith)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
