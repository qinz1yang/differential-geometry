import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteVolumeDebit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    BorelSpace G.terminalRegularOpen := ⟨rfl⟩
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem MetricCutCapEvent.exists_compact_volume_debit_of_finiteFullPreparedMetric
    (A : ℝ) (hA : 0 < A) :
    ∃ δV : ℝ, 0 < δV ∧ δV < 1 / 2 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [CompactSpace M]
        (o : SmoothOrientation ThreeModel M) {ι : Type} [Finite ι] {precision : ι → ℝ}
        (hδ : ∀ i, 0 < precision i) (f : ∀ i, bufferedCylinder (precision i) → M)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (R : Set (ConnectedComponents (cutCore f))),
      letI : LocallyPathConnectedSpace M :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
      letI : ChartedSpace ThreeSpace Q :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
      letI : IsManifold ThreeModel ∞ Q :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
      letI : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      letI : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
      ∀ (oRet : SmoothOrientation ThreeModel Ret) {a s : ℝ}
        (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
          (OrientedThreeStage.ofSmoothOrientation Ret oRet) a s)
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => E.incoming.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → E.incoming.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum E.terminal.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap E.incoming.terminalRegularOpen (d₀ i))
        (k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ)
        (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          normalizedDatum E.terminal.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
            (c * precision b.val.1) (k' b))
        (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          (d b).retainedSide = true)
        (D : ℝ) (m : ℕ) (ε : ℝ)
        (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          CanonicalStaticInsertionWitness (d b) A hA D m ε),
      E.transition.trace.tubes.Index ≃ ι →
      E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
        E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
        hOriginal hrec d hmap hside w →
      (∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
        c * precision b.val.1 ≤ δV) →
      (∀ i, precision i ≤ 1 / 4) →
      (∀ i, cuttingSphereComponent hδ f hf hdisj (i, true) ∈ R ∧
        cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R) →
      ∀ S : ℝ, 0 < S → (∀ i, metricScalarAt E.terminal.metric (x₀ i) = S) →
      (∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
        S / 2 ≤ metricScalarAt E.terminal.metric ((d₀ b.val.1).offsetPoint
          (cuttingSign_sq b.val.2))) →
      (∀ i, precision i ≤ Real.pi /
        (8 * (riemannianVolumeMeasure (𝓡 3) ThreeSpace metric
          {x | ‖x‖ ≤ transitionEnd}).toReal + 1)) →
      ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel
          (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier E.outputMetric univ +
          ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * S ^ (-3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F := by
  obtain ⟨δV, hδV, hhalf, hfactory⟩ := exists_finiteFullPreparedMetric_volume_debit A hA
  refine ⟨δV, hδV, hhalf, ?_⟩
  intro M _ _ _ _ _ o ι _ precision hδ f hf hdisj hs R
  let : LocallyPathConnectedSpace M :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
  let : ChartedSpace ThreeSpace Q :=
    finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q :=
    finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  intro oRet a s E hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside D m ε w
    e hout hsmall hquarter hone S hS hscale hlocal hprecision
  let F := range (retainedCoreDomainMap f R E.incoming.terminalRegularOpen hRet) ∪
    ⋃ i : ι, (d₀ i).map '' {q | q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)}
  refine ⟨F, isCompact_retained_core_union_negative_bands
    E.incoming.terminalRegularOpen E.terminal.metric x₀ order d₀ f hf hdisj R hRet, ?_⟩
  have h := hfactory ThreeModel hδ f hf hdisj hs E.incoming.terminalRegularOpen
    E.terminal.metric R hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside D m ε w
    hsmall hquarter hone S hS hscale hlocal hprecision
  rw [hout, Nat.card_congr e]
  simp only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  convert h using 1 <;> congr 1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
