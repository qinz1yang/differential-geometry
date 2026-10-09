import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricCutCapCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricEventVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteVolumeDebit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRetainedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NontrivialCutSelection

open private output_curvature_of_metric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricCutCapCurvature

noncomputable section
open Set Function TopologicalSpace Manifold MeasureTheory Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u v
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
attribute [local instance] threeBallChartedSpace threeBall_isManifold
private theorem tube_system_eq_of_trace_heq
    {P Q D D' N N' : OrientedThreeStage.{u}}
    (hD : D = D') (hN : N = N')
    {T : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier}
    {T' : CutCapTopology P.Carrier Q.Carrier D'.Carrier N'.Carrier}
    (h : HEq T T') : T.tubes = T'.tubes := by
  cases hD
  cases hN
  cases eq_of_heq h
  rfl


private local instance terminalRegularOpen_sigmaCompactSpace
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem volume_add_real_card_debit_le
    {X ι : Type v} (hIndex : X = ι)
    (volume : ℝ≥0∞) (S : ℝ) (V : ℝ≥0∞)
    (h : volume + (Nat.card ι : ℝ≥0∞) * ENNReal.ofReal (S ^ (-3 / 2 : ℝ)) ≤ V) :
    volume + ENNReal.ofReal ((Nat.card X : ℝ) * S ^ (-3 / 2 : ℝ)) ≤ V := by
  rw [hIndex]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h

private theorem exists_uniform_oriented_metricCutCapEvent_volume_debit_with_cap_precision :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), (2 * A < 1 / 2 ∧ StaticCollarAdmits.{0, 0, u} A hA) ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∀ δcap : ℝ, 0 < δcap → ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
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
        (hSingular : G.SingularEndpoint)
        (_ : ∀ i, cuttingSphereComponent hδ f hf hdisj (i, true) ∈ R ∧
          cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R)
        (S : ℝ) (_ : 0 < S) (_ : ∀ i, metricScalarAt L.metric (x₀ i) = S),
      let hnontrivial := G.nonempty_cut_or_discardedCore_of_singularEndpoint hSingular f R hRet
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace M
      letI : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
          G.terminalRegularOpen.isOpen)
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
      ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (F : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
        (∀ b, F b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ F b = LinearIsometryEquiv.neg ℝ) ∧
        (∀ b x, (B b x : ThreeSpace) = F b x) ∧
      ∃ E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ
            (fun i => (d₀ i).precision_lt_one) f hf hdisj R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts hδ
          (fun i => (d₀ i).precision_lt_one) f hf hdisj ∧
        E.incoming = G ∧ HEq E.terminal L ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ K : Set G.terminalRegularOpen, IsCompact K ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * S ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric K) ∧
      ∃ hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
      ∃ d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (m + 4),
      ∃ hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (d b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b) A hA D m ε,
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀
          hOriginal hrec d hmap hside w ∧
        (∀ b : Bidx, |metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
          metricScalarAt L.metric (x₀ b.val.1) - 1| ≤ c * precision b.val.1) ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
        (∀ b : Bidx, c * precision b.val.1 ≤ δcap) ∧
        ∀ b : Bidx, S / 2 ≤
          metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) := by
  classical
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hfactory⟩ :=
    exists_uniform_metricCutCapEvent_volume_bound.{u}
  choose δV hδV hhalf hdebit using exists_finiteFullPreparedMetric_volume_debit A hA
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε δcap hδcap
  choose δ₀ hδ₀ hquarter hmake using hfactory D hD m ε hε (min δV δcap) (lt_min hδV hδcap)
  let margin := Real.pi / (8 * (riemannianVolumeMeasure (𝓡 3) ThreeSpace metric
    {x | ‖x‖ ≤ transitionEnd}).toReal + 1)
  have hmargin : 0 < margin := div_pos Real.pi_pos (by positivity)
  refine ⟨min δ₀ margin, lt_min hδ₀ hmargin, (min_le_left _ _).trans_lt hquarter, ?_⟩
  intro M _ _ _ _ _ o t₀ t₁ G L ι _ precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet
    hSingular hone S hS hscale
  let hnontrivial := G.nonempty_cut_or_discardedCore_of_singularEndpoint hSingular f R hRet
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace M
  let : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
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
  obtain
    ⟨hrec,d,hmap,hside,w,hratio,hw,hcapPrecision,hlow,oQ,oRet,oDisc,F,B,a,hboundary,hchoice,hB,E,
    hDisc,hCap,htrace,hG,hL,hOutput,hOld,hBoundary,_⟩ :=
    hmake o G L precision hδ (fun i => (hle i).trans (min_le_left _ _)) x₀ d₀ f hf hdisj hs
      hOriginal R hRet hnontrivial
  have htubes : E.transition.trace.tubes = TubeSystem.ofBufferedCharts hδ
      (fun i => (d₀ i).precision_lt_one) f hf hdisj :=
    tube_system_eq_of_trace_heq hDisc hCap htrace
  have hlocal (b : Bidx) : S / 2 ≤
      metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) := by
    simpa only [hscale] using hlow b
  have hquarterAll : ∀ i, precision i ≤ 1 / 4 :=
    fun i => ((hle i).trans (min_le_left _ _)).trans hquarter.le
  have hprecision : ∀ i, precision i ≤ margin := fun i => (hle i).trans (min_le_right _ _)
  let K : Set G.terminalRegularOpen :=
    range (retainedCoreDomainMap f R G.terminalRegularOpen hRet) ∪
      ⋃ i : ι, (d₀ i).map '' {q | q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)}
  have hK : IsCompact K :=
    isCompact_retained_core_union_negative_bands G.terminalRegularOpen L.metric
      x₀ (fun _ => m + 6) d₀ f hf hdisj R hRet
  have hfactoryDebit := hdebit ThreeModel hδ f hf hdisj hs G.terminalRegularOpen
    L.metric R hRet c hc x₀ (fun _ => m + 6) d₀ hOriginal (fun _ => m + 4)
    hrec d hmap hside D m ε w
      (fun b => (hcapPrecision b).trans (min_le_left _ _)) hquarterAll hone S hS hscale hlocal
        hprecision
  let gPrepared : SmoothRiemannianMetric ThreeModel Ret :=
    finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs G.terminalRegularOpen L.metric
      R hRet c hc x₀ (fun _ => m + 6) d₀ hOriginal hrec d hmap hside w
  have hpreserve := output_curvature_of_metric_eq E G L hG hL gPrepared hOutput
    (fun a ha hin x =>
      (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a x).mpr
        (finiteFullPreparedMetric_hamiltonIvey ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6)
          d₀ hOriginal hrec d hmap hside w hw a ha
          (fun p => (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
            L.metric a p).mp (hin p)) x))
    (fun L₀ hL₀ hin x => finiteFullPreparedMetric_scalar_floor ThreeModel hδ f hf hdisj hs
      G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6)
      d₀ hOriginal hrec d hmap hside w hw L₀ hL₀ hin x)
  have hbound : riemannianVolumeMeasure ThreeModel
      (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier E.outputMetric univ +
        (Nat.card ι : ℝ≥0∞) * ENNReal.ofReal (S ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric K := by
    rw [hOutput]
    convert hfactoryDebit using 1 <;> congr 1
  have hIndex : E.transition.trace.tubes.Index = ι :=
    congrArg TubeSystem.Index htubes
  have hfinal := volume_add_real_card_debit_le hIndex
    (riemannianVolumeMeasure ThreeModel
      (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier E.outputMetric univ) S
      (riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric K) hbound
  exact ⟨oQ, oRet, oDisc, F, B, a, hboundary, hchoice, hB, E, hDisc, hCap, htrace, htubes, hG, hL, hOld,
    hBoundary, hpreserve.1, hpreserve.2, ⟨K, hK, hfinal⟩,
    hrec, d, hmap, hside, w, hOutput, hratio, hw,
    (fun b => (hcapPrecision b).trans (min_le_right _ _)), hlocal⟩

theorem exists_uniform_metricCutCapEvent_volume_debit_with_recenter_data :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), (2 * A < 1 / 2 ∧ StaticCollarAdmits.{0, 0, u} A hA) ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∀ δcap : ℝ, 0 < δcap → ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {P : OrientedThreeStage.{u}} {t₀ t₁ : ℝ}
        (G : P.IncomingSlab t₀ t₁)
        (L : G.TerminalLimitMetric)
        {ι : Type} [Fintype ι] (precision : ι → ℝ) (hδ : ∀ i, 0 < precision i),
      (∀ i, precision i ≤ δ₀) → ∀ (x₀ : ι → G.terminalRegularOpen)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (m + 6))
        (f : ∀ i : ι, bufferedCylinder (precision i) → P.Carrier)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R)
          (fun x : P.Carrier => G.terminalRegularRegion x))
        (hSingular : G.SingularEndpoint)
        (_ : ∀ i, cuttingSphereComponent hδ f hf hdisj (i, true) ∈ R ∧
          cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R)
        (S : ℝ) (_ : 0 < S) (_ : ∀ i, metricScalarAt L.metric (x₀ i) = S),
      let hnontrivial := G.nonempty_cut_or_discardedCore_of_singularEndpoint hSingular f R hRet
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : SecondCountableTopology P.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
      letI : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
          G.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace P.Carrier :=
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
      ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (F : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
        (∀ b, F b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ F b = LinearIsometryEquiv.neg ℝ) ∧
        (∀ b x, (B b x : ThreeSpace) = F b x) ∧
      ∃ E : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ
            (fun i => (d₀ i).precision_lt_one) f hf hdisj R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts hδ
          (fun i => (d₀ i).precision_lt_one) f hf hdisj ∧
        E.incoming = G ∧ HEq E.terminal L ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ K : Set G.terminalRegularOpen, IsCompact K ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * S ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric K) ∧
      ∃ hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
      ∃ d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (m + 4),
      ∃ hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (d b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b) A hA D m ε,
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀
          hOriginal hrec d hmap hside w ∧
        (∀ b : Bidx, |metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
          metricScalarAt L.metric (x₀ b.val.1) - 1| ≤ c * precision b.val.1) ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
        (∀ b : Bidx, c * precision b.val.1 ≤ δcap) ∧
        ∀ b : Bidx, S / 2 ≤
          metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) := by
  obtain ⟨c,hc,C,hC,A,hA,hsmall,hfactory⟩ :=
    exists_uniform_oriented_metricCutCapEvent_volume_debit_with_cap_precision.{u}
  refine ⟨c,hc,C,hC,A,hA,hsmall,?_⟩
  intro D hD m ε hε δcap hδcap
  obtain ⟨δ₀,hδ₀,hquarter,hmake⟩ := hfactory D hD m ε hε δcap hδcap
  refine ⟨δ₀,hδ₀,hquarter,?_⟩
  intro P
  rw [← P.ofSmoothOrientation_smoothOrientation]
  exact hmake P.smoothOrientation


theorem exists_uniform_metricCutCapEvent_volume_debit_with_cap_precision :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∀ δcap : ℝ, 0 < δcap → ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {P : OrientedThreeStage.{u}} {t₀ t₁ : ℝ}
        (G : P.IncomingSlab t₀ t₁)
        (L : G.TerminalLimitMetric)
        {ι : Type} [Fintype ι] (precision : ι → ℝ) (hδ : ∀ i, 0 < precision i),
      (∀ i, precision i ≤ δ₀) → ∀ (x₀ : ι → G.terminalRegularOpen)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (m + 6))
        (f : ∀ i : ι, bufferedCylinder (precision i) → P.Carrier)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R)
          (fun x : P.Carrier => G.terminalRegularRegion x))
        (hSingular : G.SingularEndpoint)
        (_ : ∀ i, cuttingSphereComponent hδ f hf hdisj (i, true) ∈ R ∧
          cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R)
        (S : ℝ) (_ : 0 < S) (_ : ∀ i, metricScalarAt L.metric (x₀ i) = S),
      let hnontrivial := G.nonempty_cut_or_discardedCore_of_singularEndpoint hSingular f R hRet
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : SecondCountableTopology P.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
      letI : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
          G.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace P.Carrier :=
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
      ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
      ∃ E : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ
            (fun i => (d₀ i).precision_lt_one) f hf hdisj R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts hδ
          (fun i => (d₀ i).precision_lt_one) f hf hdisj ∧
        E.incoming = G ∧ HEq E.terminal L ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ K : Set G.terminalRegularOpen, IsCompact K ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * S ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric K) ∧
      ∃ hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
      ∃ d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (m + 4),
      ∃ hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (d b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b) A hA D m ε,
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀
          hOriginal hrec d hmap hside w ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
        (∀ b : Bidx, c * precision b.val.1 ≤ δcap) ∧
        ∀ b : Bidx, S / 2 ≤
          metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) := by
  classical
  choose c hc C hC A hA hsmall hfactory using
    exists_uniform_metricCutCapEvent_volume_debit_with_recenter_data.{u}
  refine ⟨c, hc, C, hC, A, hA, hsmall.1, ?_⟩
  intro D hD m ε hε δcap hδcap
  choose δ₀ hδ₀ hquarter hmake using hfactory D hD m ε hε δcap hδcap
  refine ⟨δ₀, hδ₀, hquarter, ?_⟩
  intro P t₀ t₁ G L ι inst precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet
    hSingular hone S hS hscale
  choose oQ oRet oDisc F B aCap hboundary hchoice hB E
    hDisc hCap htrace htubes hG hL hOld hBoundary hpin hscalar
    hvolume hrec d hmap hside w hOutput hratio hw hcapPrecision hlow using
    hmake G L precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet hSingular hone S hS hscale
  exact ⟨oQ, oRet, oDisc, B, aCap, hboundary, E, hDisc, hCap, htrace, htubes,
    hG, hL, hOld, hBoundary, hpin, hscalar, hvolume, hrec, d, hmap, hside, w,
    hOutput, hw, hcapPrecision, hlow⟩

theorem exists_uniform_metricCutCapEvent_volume_debit :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {P : OrientedThreeStage.{u}} {t₀ t₁ : ℝ}
        (G : P.IncomingSlab t₀ t₁)
        (L : G.TerminalLimitMetric)
        {ι : Type} [Fintype ι] (precision : ι → ℝ) (hδ : ∀ i, 0 < precision i),
      (∀ i, precision i ≤ δ₀) → ∀ (x₀ : ι → G.terminalRegularOpen)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (m + 6))
        (f : ∀ i : ι, bufferedCylinder (precision i) → P.Carrier)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R)
          (fun x : P.Carrier => G.terminalRegularRegion x))
        (hSingular : G.SingularEndpoint)
        (_ : ∀ i, cuttingSphereComponent hδ f hf hdisj (i, true) ∈ R ∧
          cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R)
        (S : ℝ) (_ : 0 < S) (_ : ∀ i, metricScalarAt L.metric (x₀ i) = S),
      let hnontrivial := G.nonempty_cut_or_discardedCore_of_singularEndpoint hSingular f R hRet
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : SecondCountableTopology P.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
      letI : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
          G.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace P.Carrier :=
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
      ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
      ∃ E : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ
            (fun i => (d₀ i).precision_lt_one) f hf hdisj R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts hδ
          (fun i => (d₀ i).precision_lt_one) f hf hdisj ∧
        E.incoming = G ∧ HEq E.terminal L ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ K : Set G.terminalRegularOpen, IsCompact K ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * S ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric K) ∧
      ∃ hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
      ∃ d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (m + 4),
      ∃ hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (d b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b) A hA D m ε,
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀
          hOriginal hrec d hmap hside w ∧
        ∀ b : Bidx, StaticInsertionAdditionalProperties C (w b) := by
  classical
  choose c hc C hC A hA hsmall hfactory using
    exists_uniform_metricCutCapEvent_volume_debit_with_cap_precision.{u}
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  choose δ₀ hδ₀ hquarter hmake using hfactory D hD m ε hε 1 zero_lt_one
  refine ⟨δ₀, hδ₀, hquarter, ?_⟩
  intro P t₀ t₁ G L ι _ precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet
    hSingular hone S hS hscale
  let hnontrivial := G.nonempty_cut_or_discardedCore_of_singularEndpoint hSingular f R hRet
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
  let : LocallyPathConnectedSpace P.Carrier :=
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
  dsimp only
  choose oQ oRet oDisc B aCap hboundary E hDisc hCap htrace htubes hG hL
    hOld hBoundary hpin hfloor hvolume hrec d hmap hside w hOutput hw hcap hlocal using
    hmake G L precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet
      hSingular hone S hS hscale
  exact ⟨oQ, oRet, oDisc, B, aCap, hboundary, E, hDisc, hCap, htrace, htubes, hG, hL,
    hOld, hBoundary, hpin, hfloor, hvolume, hrec, d, hmap, hside, w, hOutput, hw⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
