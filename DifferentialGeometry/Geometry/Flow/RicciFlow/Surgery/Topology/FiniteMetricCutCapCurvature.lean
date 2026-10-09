import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedMetricCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricRetainedCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PreparedCollarCorrespondence

noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private theorem output_curvature_of_metric_eq
    {P Q : OrientedThreeStage.{u}} {t₀ t₁ : ℝ}
    (E : MetricCutCapEvent P Q t₀ t₁) (G : P.IncomingSlab t₀ t₁)
    (L : G.TerminalLimitMetric) (hG : E.incoming = G) (hL : HEq E.terminal L)
    (gRet : Q.Metric) (hout : E.outputMetric = gRet)
    (hpin : ∀ a : ℝ, 0 < a →
      (∀ x : G.terminalRegularOpen, InFixedHamiltonIveyRegion L.metric a x) →
      ∀ x : Q.Carrier, InFixedHamiltonIveyRegion gRet a x)
    (hscalar : ∀ L₀ : ℝ, L₀ ≤ 0 →
      (∀ x : G.terminalRegularOpen, L₀ ≤ metricScalarAt L.metric x) →
      ∀ x : Q.Carrier, L₀ ≤ metricScalarAt gRet x) :
    (∀ a : ℝ, 0 < a →
      (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
      ∀ x : Q.Carrier, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
    (∀ L₀ : ℝ, L₀ ≤ 0 →
      (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
      ∀ x : Q.Carrier, L₀ ≤ metricScalarAt E.outputMetric x) := by
  cases hG
  cases eq_of_heq hL
  simpa only [hout] using And.intro hpin hscalar

theorem exists_uniform_metricCutCapEvent_curvature_preserving :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [CompactSpace M],
      ∀ (o : SmoothOrientation ThreeModel M) {t₀ t₁ : ℝ}
        (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
        (L : G.TerminalLimitMetric)
        {ι : Type} [Fintype ι] (precision : ι → ℝ) (hδ : ∀ i, 0 < precision i),
      (∀ i, precision i ≤ δ₀) → ∀ (x₀ : ι → G.terminalRegularOpen)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (m + 6))
        (f : ∀ i : ι, bufferedCylinder (precision i) → M)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)),
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : LocallyPathConnectedSpace M :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
      let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
      letI : ChartedSpace ThreeSpace Q :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
      letI : IsManifold ThreeModel ∞ Q :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
      letI : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      letI : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
      ∃ hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
      ∃ d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (m + 4),
      ∃ hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (d b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b) A hA D m ε,
        (∀ b : Bidx, |metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
          metricScalarAt L.metric (x₀ b.val.1) - 1| ≤ c * precision b.val.1) ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
      ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (F : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
        (∀ b, F b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ F b = LinearIsometryEquiv.neg ℝ) ∧
        (∀ b x, (B b x : ThreeSpace) = F b x) ∧
      ∃ E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ
            (fun i => (d₀ i).precision_lt_one) f hf hdisj R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary) ∧
        E.incoming = G ∧ HEq E.terminal L ∧
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀
          hOriginal hrec d hmap hside w ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) := by
  classical
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hmod⟩ :=
    exists_uniform_prepared_collar_correspondence.{0, 0, u}
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hquarter, hprep⟩ := hmod D hD m ε hε
  refine ⟨δ₀, hδ₀, hquarter, ?_⟩
  intro M _ _ _ _ _ o t₀ t₁ G L ι _ precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet hnontrivial
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : LocallyPathConnectedSpace M :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
  let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
  let : ChartedSpace ThreeSpace Q :=
    finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q :=
    finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  let : CompactSpace Disc :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
  let : Nonempty M := hnontrivial.elim
    (fun ⟨i⟩ => ⟨(x₀ i).val⟩) (fun ⟨p⟩ => ⟨p.val.val⟩)
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  have hp (b : Bidx) := hprep (precision b.val.1) (hδ b.val.1) (hle b.val.1)
    L.metric (x₀ b.val.1) (d₀ b.val.1) b.val.2
  choose hrec d hmap hside hratio w hw hcorr using hp
  let gRet : SmoothRiemannianMetric ThreeModel Ret := finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
    G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀ hOriginal hrec d hmap hside w
  have hTensor := finiteFullPreparedMetric_retainedCore_inner ThreeModel hδ f hf hdisj hs
    G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀ hOriginal hrec d hmap hside w
  obtain ⟨oQ, oRet, oDisc, F, B, a, hboundary, hchoice, hB, E, hDisc, hCap,
    htrace, hG, hL, hOutput, hOld, hBoundary⟩ :=
    exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps transitionEnd_pos hδ
      (fun i => (d₀ i).precision_lt_one) f hf hdisj hs R o hnontrivial G L hRet gRet
      (fun p v z => (hTensor p v z).symm)
  refine ⟨hrec, d, hmap, hside, w, hratio, hw, oQ, oRet, oDisc, F, B, a,
    hboundary, hchoice, hB, E, hDisc, hCap, htrace, hG, hL, hOutput, hOld, hBoundary, ?_⟩
  apply output_curvature_of_metric_eq E G L hG hL gRet hOutput
  · intro a ha hin x
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a x).mpr
    exact finiteFullPreparedMetric_hamiltonIvey ThreeModel hδ f hf hdisj hs
      G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6)
      d₀ hOriginal hrec d hmap hside w hw a ha
      (fun p => (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion L.metric a p).mp (hin p)) x
  · intro L₀ hL₀ hin x
    exact finiteFullPreparedMetric_scalar_floor ThreeModel hδ f hf hdisj hs
      G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6)
      d₀ hOriginal hrec d hmap hside w hw L₀ hL₀ hin x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
