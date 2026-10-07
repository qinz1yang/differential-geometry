import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticFamilyVolumePreparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedMetricCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricRetainedCore

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
theorem exists_uniform_metricCutCapEvent_volume_bound :
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
        (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)),
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace M
      letI : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
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
        (∀ b : Bidx, c * precision b.val.1 ≤ δcap) ∧
        (∀ b : Bidx, metricScalarAt L.metric (x₀ b.val.1) / 2 ≤
          metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) ∧
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
        riemannianVolumeMeasure ThreeModel (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier E.outputMetric univ ≤
          riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
            (range (retainedCoreDomainMap f R G.terminalRegularOpen hRet)) +
          ∑' b : Bidx, ENNReal.ofReal (8 * (metricScalarAt L.metric (x₀ b.val.1)) ^ (-3 / 2 : ℝ)) *
            riemannianVolumeMeasure (𝓡 3) ThreeSpace metric {x | ‖x‖ ≤ transitionEnd} := by
  classical
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hmod⟩ := exists_uniform_recentered_static_family_volume_bound.{0, 0, u, 0}
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε δcap hδcap
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  obtain ⟨δ₀, hδ₀, hquarter, hprep⟩ := hmod D hD m ε hε
  refine ⟨min δ₀ (δcap / c), lt_min hδ₀ (div_pos hδcap hcpos),
    (min_le_left _ _).trans_lt hquarter, ?_⟩
  intro M _ _ _ _ _ o t₀ t₁ G L ι _ precision hδ hle x₀ d₀ f hf hdisj hs hOriginal R hRet hnontrivial
  let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace M
  let : SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
  let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).2
  let : Nonempty M := hnontrivial.elim (fun ⟨i⟩ => ⟨(x₀ i).val⟩) (fun ⟨p⟩ => ⟨p.val.val⟩)
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  obtain ⟨hrec, d, w, hmap, hside, hratio, hlow, hupp, hw, hcapvol⟩ := hprep L.metric
    (fun b : Bidx => x₀ b.val.1) (fun b : Bidx => precision b.val.1) (fun b : Bidx => d₀ b.val.1)
    (fun b => (hle b.val.1).trans (min_le_left _ _)) (fun b => cuttingSign b.val.2) (fun b => cuttingSign_sq b.val.2)
  let gRet : SmoothRiemannianMetric ThreeModel Ret := finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
    G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀ hOriginal hrec d hmap hside w
  have hTensor := finiteFullPreparedMetric_retainedCore_inner ThreeModel hδ f hf hdisj hs
    G.terminalRegularOpen L.metric R hRet c hc x₀ (fun _ => m + 6) d₀ hOriginal hrec d hmap hside w
  obtain ⟨oQ, oRet, oDisc, F, B, a, hboundary, hchoice, hB, E, hDisc, hCap,
    htrace, hG, hL, hOutput, hOld, hBoundary⟩ :=
    exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps transitionEnd_pos hδ
      (fun i => (d₀ i).precision_lt_one) f hf hdisj hs R o hnontrivial G L hRet gRet
      (fun p v z => (hTensor p v z).symm)
  have hcapPrecision (b : Bidx) : c * precision b.val.1 ≤ δcap := by
    have hb := (hle b.val.1).trans (min_le_right _ _)
    exact (mul_comm c (precision b.val.1)) ▸ (le_div_iff₀ hcpos).mp hb
  refine ⟨hrec,d,hmap,hside,w,hratio,hw,hcapPrecision,hlow,oQ,oRet,oDisc,F,B,a,hboundary,hchoice,hB,E,
    hDisc,hCap,htrace,hG,hL,hOutput,hOld,hBoundary,?_⟩
  rw [hOutput]
  exact (finiteFullPreparedMetric_volume_le ThreeModel hδ f hf hdisj hs G.terminalRegularOpen L.metric
    R hRet c hc x₀ (fun _ => m + 6) d₀ hOriginal hrec d hmap hside w).trans
    (add_le_add_right (ENNReal.tsum_le_tsum hcapvol) _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
