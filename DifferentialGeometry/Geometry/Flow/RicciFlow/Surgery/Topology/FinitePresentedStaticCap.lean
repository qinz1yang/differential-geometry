import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteStaticCapInclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedMetricCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricRetainedCore

section

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {precision : ι → ℝ}
  (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
private local instance : LocallyPathConnectedSpace M :=
  originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
local notation "Bidx" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}

theorem exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => E.incoming.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → E.incoming.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum E.terminal.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap E.incoming.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum E.terminal.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∃ e : E.RetainedBoundaryIndex ≃ Bidx,
          (∀ b, HEq b.val (e b).val) ∧
          ∀ b : E.RetainedBoundaryIndex,
            ∃ S : E.PresentedStaticCap fixed D m ε b,
              S.delta = c * precision (e b).val.1 ∧ S.order = k' (e b) ∧
              HEq S.neck (d (e b)).oriented.toNormalizedNeck ∧
              ∀ u : standardCapWindow D,
                S.inclusion (S.witness.window u) =
                  finiteFullWitnessMap ThreeModel (by simp) transitionEnd_pos
                    hδ f hf hdisj hs R c hc (e b) ((w (e b)).window u) := by
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
  intro oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace
  rcases E with @⟨discarded, capped, X, G, gLimit, gRet, old, holdc, holdr, oldcharts,
    oldsmooth, oldinduced, oldTerminal, oldTerminaleq, oldOutput, oldOutputeq,
    oldMetric, oldContains, oldMeet⟩
  dsimp only at hDisc hCap htrace
  subst discarded
  subst capped
  rcases X with @⟨trace, sourceNonempty, tubesSmooth, coreCharts, coreSmooth, coreInduced,
    coreBoundary, coreInclusion, ballCharts, ballSmooth, ballInduced, ballBoundary,
    capSmooth, attaching, attachingEq, corePositive, capPositive, presentation,
    presentationEq, presentationPositive⟩
  dsimp only at htrace
  have ht := eq_of_heq htrace
  clear htrace
  cases ht
  intro hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  have hretainedBoundary (b : ι × Bool) :
      (∀ y, (T).coreBoundarySphere b y ∈
        (CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).retainedCore) ↔ cuttingSphereComponent hδ f hf hdisj b ∈ R :=
    CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff transitionEnd_pos hδ hδ1
      f hf hdisj R hnontrivial b
  let e := Equiv.subtypeEquivRight hretainedBoundary
  refine ⟨e, (fun _ => HEq.rfl), ?_⟩
  intro b
  let b' : Bidx := e b
  let S := (w b').toStaticCapWitness hD
  let inclusion := finiteStaticCapInclusion hδ f hf hdisj hs G.terminalRegularOpen
    gLimit.metric R c hc x₀ order d₀ d w b' hD
  refine ⟨MetricCutCapEvent.PresentedStaticCap.ofReparametrizedCapping _ b S
    (Capping.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj)
    B a hboundary rfl (A b.val) (hB b.val) inclusion ?_ ?_ ?_ ?_
    (finiteStaticRetainedTubePoint hδ f hf hdisj R c hc hδ1 b') ?_ ?_, rfl, rfl, HEq.rfl, fun _ => rfl⟩
  · exact finiteStaticCapInclusion_smooth hδ f hf hdisj hs G.terminalRegularOpen
      gLimit.metric R c hc x₀ order d₀ d w b' hD
  · intro q v z
    have hmetric := finiteFullPreparedMetric_staticCap_inclusion_inner hδ f hf hdisj hs
      G.terminalRegularOpen gLimit.metric R hRet c hc x₀ order d₀ hOriginal
      hrec d hmap hside w b' hD q v z
    apply hmetric.trans
    congr 3
    exact hOutput.symm
  · rfl
  · exact finiteStaticCapInclusion_cap_presentation hδ f hf hdisj hs
      G.terminalRegularOpen gLimit.metric R c hc x₀ order d₀ d w hδ1 hnontrivial b' hD
  · exact @finiteStaticRetainedTubePoint_eq_neck M _ _ _ hSmooth ι _ precision
      hδ f hf hdisj G.terminalRegularOpen gLimit.metric R c hc x₀ order d₀
      hOriginal k' hrec d hmap hside _ hδ1 b'
  · exact finiteStaticCapInclusion_retained_presentation hδ f hf hdisj hs
      G.terminalRegularOpen gLimit.metric R c hc x₀ order d₀ d w hδ1 hnontrivial b' hD

theorem exists_presentedStaticCap_neck_heq_of_finiteMetricEvent (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => E.incoming.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → E.incoming.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum E.terminal.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap E.incoming.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum E.terminal.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∃ e : E.RetainedBoundaryIndex ≃ Bidx,
          (∀ b, HEq b.val (e b).val) ∧
          ∀ b : E.RetainedBoundaryIndex,
            ∃ S : E.PresentedStaticCap fixed D m ε b,
              S.delta = c * precision (e b).val.1 ∧ S.order = k' (e b) ∧
              HEq S.neck (d (e b)).oriented.toNormalizedNeck := by
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
  intro oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  apply Exists.imp _ (exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent hδ hδ1 f hf hdisj hs R o
    hnontrivial hD oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput)
  intro e he
  exact ⟨he.1, fun b => (he.2 b).imp fun S h => ⟨h.1, h.2.1, h.2.2.1⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem terminal_data_transport
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric)
    (hG : E.incoming = G) (hL : HEq E.terminal L)
    {F : (G : P.IncomingSlab a s) → G.TerminalLimitMetric → Prop}
    (h : F E.incoming E.terminal) : F G L := by
  cases hG
  have ht := eq_of_heq hL
  cases ht
  exact h

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {precision : ι → ℝ}
  (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
private local instance : LocallyPathConnectedSpace M :=
  originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
local notation "Bidx" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}

theorem exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent_terminal (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∃ e : E.RetainedBoundaryIndex ≃ Bidx,
          (∀ b, HEq b.val (e b).val) ∧
          ∀ b : E.RetainedBoundaryIndex,
            ∃ S : E.PresentedStaticCap fixed D m ε b,
              S.delta = c * precision (e b).val.1 ∧ S.order = k' (e b) ∧
              HEq S.neck (d (e b)).oriented.toNormalizedNeck ∧
              ∀ u : standardCapWindow D,
                S.inclusion (S.witness.window u) =
                  finiteFullWitnessMap ThreeModel (by simp) transitionEnd_pos
                    hδ f hf hdisj hs R c hc (e b) ((w (e b)).window u) := by
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
  intro oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
  apply terminal_data_transport E G L hG hL
  exact exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent hδ hδ1 f hf hdisj hs R o
    hnontrivial hD oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace

theorem exists_presentedStaticCap_neck_heq_of_finiteMetricEvent_terminal (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∃ e : E.RetainedBoundaryIndex ≃ Bidx,
          (∀ b, HEq b.val (e b).val) ∧
          ∀ b : E.RetainedBoundaryIndex,
            ∃ S : E.PresentedStaticCap fixed D m ε b,
              S.delta = c * precision (e b).val.1 ∧ S.order = k' (e b) ∧
              HEq S.neck (d (e b)).oriented.toNormalizedNeck := by
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
  intro oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  obtain ⟨e, he, hS⟩ := exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent_terminal hδ hδ1 f hf hdisj hs R o
    hnontrivial hD oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  refine ⟨e, he, ?_⟩
  intro b
  obtain ⟨S, hδS, hkS, hNS, _⟩ := hS b
  exact ⟨S, hδS, hkS, hNS⟩

def finitePresentedStaticCaps (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => E.incoming.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → E.incoming.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum E.terminal.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap E.incoming.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum E.terminal.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        Σ e : E.RetainedBoundaryIndex ≃ Bidx,
          {S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b //
            (∀ b, HEq b.val (e b).val) ∧
            ∀ b, (S b).delta = c * precision (e b).val.1 ∧
              (S b).order = k' (e b) ∧
              HEq (S b).neck (d (e b)).oriented.toNormalizedNeck ∧
              ∀ u : standardCapWindow D,
                (S b).inclusion ((S b).witness.window u) =
                  finiteFullWitnessMap ThreeModel (by simp) transitionEnd_pos
                    hδ f hf hdisj hs R c hc (e b) ((w (e b)).window u)} := by
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
  intro oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  classical
  let hex := exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc E A B a hboundary hB
    hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  exact ⟨hex.choose, ⟨fun b => (hex.choose_spec.2 b).choose,
    hex.choose_spec.1, fun b => (hex.choose_spec.2 b).choose_spec⟩⟩

def finitePresentedStaticCapsOfTerminal (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        Σ e : E.RetainedBoundaryIndex ≃ Bidx,
          {S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b //
            (∀ b, HEq b.val (e b).val) ∧
            ∀ b, (S b).delta = c * precision (e b).val.1 ∧
              (S b).order = k' (e b) ∧
              HEq (S b).neck (d (e b)).oriented.toNormalizedNeck ∧
              ∀ u : standardCapWindow D,
                (S b).inclusion ((S b).witness.window u) =
                  finiteFullWitnessMap ThreeModel (by simp) transitionEnd_pos
                    hδ f hf hdisj hs R c hc (e b) ((w (e b)).window u)} := by
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
  intro oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  classical
  let hex := exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent_terminal
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc G L E A B a hboundary hB
    hDisc hCap htrace hG hL hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  exact ⟨hex.choose, ⟨fun b => (hex.choose_spec.2 b).choose,
    hex.choose_spec.1, fun b => (hex.choose_spec.2 b).choose_spec⟩⟩


private theorem cap_output_of_trace_heq
    {P₁ P₂ P₃ P₄ P₃' P₄' : OrientedThreeStage.{u}}
    {tr : CutCapTopology P₁.Carrier P₂.Carrier P₃.Carrier P₄.Carrier}
    {tr' : CutCapTopology P₁.Carrier P₂.Carrier P₃'.Carrier P₄'.Carrier}
    (hZ : P₃' = P₃) (hW : P₄' = P₄) (h : HEq tr' tr)
    {b' : tr'.tubes.Boundary} {b : tr.tubes.Boundary} (hb : HEq b' b)
    (z : ThreeBall) (q : P₂.Carrier) :
    tr'.presentation (tr'.capping.cap b' z) = Sum.inl q ↔
      tr.presentation (tr.capping.cap b z) = Sum.inl q := by
  cases hZ
  cases hW
  cases eq_of_heq h
  cases eq_of_heq hb
  rfl

theorem finite_presented_static_cap_inclusion_cap (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      ∀ (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → E.incoming.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum E.terminal.metric (x₀ i) (precision i) (order i))
        (k' : Bidx → ℕ)
        (d : ∀ b : Bidx, normalizedDatum E.terminal.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        ∀ (e : E.RetainedBoundaryIndex ≃ Bidx),
          (∀ b, HEq b.val (e b).val) →
          ∀ (b : E.RetainedBoundaryIndex) (S : E.PresentedStaticCap fixed D m ε b)
            (z : ThreeBall),
            S.inclusion (S.witness.cap z) =
              finiteFullWitnessMap ThreeModel (by simp) transitionEnd_pos hδ f hf hdisj hs
                R c hc (e b) ((w (e b)).cap (B (e b).val z)) := by
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
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace c hc x₀ order d₀ k' d w e he b S z
  have hp := (cap_output_of_trace_heq
    hDisc hCap htrace (he b) z
    (S.inclusion (S.witness.cap z))).mp (S.cap_eq z)
  apply Sum.inl_injective
  apply hp.symm.trans
  change (CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
    hnontrivial).presentation
      ((Capping.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj).cap (e b).val
        (B (e b).val z)) = _
  exact finiteStaticCapInclusion_cap_presentation (fixed := fixed) (D := D) (ε := ε) (m := m) hδ f hf hdisj hs
    E.incoming.terminalRegularOpen E.terminal.metric R c hc x₀ order d₀ d w hδ1 hnontrivial (e b) hD (B (e b).val z)

theorem finite_presented_static_cap_inclusion_cap_terminal (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      ∀ (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (k' : Bidx → ℕ)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        ∀ (e : E.RetainedBoundaryIndex ≃ Bidx),
          (∀ b, HEq b.val (e b).val) →
          ∀ (b : E.RetainedBoundaryIndex) (S : E.PresentedStaticCap fixed D m ε b)
            (z : ThreeBall),
            S.inclusion (S.witness.cap z) =
              finiteFullWitnessMap ThreeModel (by simp) transitionEnd_pos hδ f hf hdisj hs
                R c hc (e b) ((w (e b)).cap (B (e b).val z)) := by
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
  intro oQ oRet oDisc G L E B a hboundary hDisc hCap htrace hG hL
  apply terminal_data_transport E G L hG hL
  exact finite_presented_static_cap_inclusion_cap (fixed := fixed) (D := D) (m := m) (ε := ε)
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc E B a hboundary hDisc hCap htrace


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {precision : ι → ℝ}
  (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : LocallyPathConnectedSpace M :=
  originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
local notation "Bidx" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}

theorem exists_metricCutCapEvent_presentedStaticCap_neck_heq (hD : 0 < D) :
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
    ∀ (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
        (fun x : M => G.terminalRegularRegion x))
      (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
      (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
      (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
      (k' : Bidx → ℕ)
      (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
      (d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
      (hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
      (hside : ∀ b : Bidx, (d b).retainedSide = true)
      (w : ∀ b : Bidx,
        CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
    let gRet : SmoothRiemannianMetric ThreeModel Ret := finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
      G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b, A b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ A b = LinearIsometryEquiv.neg ℝ) ∧
      (∀ b x, (B b x : ThreeSpace) = A b x) ∧
      ∃ E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
            hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary) ∧
        E.incoming = G ∧ HEq E.terminal L ∧ E.outputMetric = gRet ∧
        E.old = E.transition.trace.retainedCore ∧
        E.transition.boundaryFrameReversing ∧
        ∃ e : E.RetainedBoundaryIndex ≃ Bidx,
          (∀ b, HEq b.val (e b).val) ∧
          ∀ b : E.RetainedBoundaryIndex,
            ∃ S : E.PresentedStaticCap fixed D m ε b,
              S.delta = c * precision (e b).val.1 ∧ S.order = k' (e b) ∧
              HEq S.neck (d (e b)).oriented.toNormalizedNeck := by
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
  intro G L hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w
  let : Nonempty M := hnontrivial.elim
    (fun ⟨i⟩ => ⟨(x₀ i).val⟩) (fun ⟨p⟩ => ⟨p.val.val⟩)
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  let gRet : SmoothRiemannianMetric ThreeModel Ret := finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
    G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  have hTensor := finiteFullPreparedMetric_retainedCore_inner ThreeModel hδ f hf hdisj hs
    G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  obtain ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, E, hDisc, hCap,
    htrace, hG, hL, hOutput, hOld, hBoundary⟩ :=
    exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps transitionEnd_pos hδ hδ1 f hf hdisj
      hs R o hnontrivial G L hRet gRet (fun p v z => (hTensor p v z).symm)
  refine ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, E, hDisc, hCap,
    htrace, hG, hL, hOutput, hOld, hBoundary, ?_⟩
  exact exists_presentedStaticCap_neck_heq_of_finiteMetricEvent_terminal hδ hδ1 f hf hdisj hs R o
    hnontrivial hD oQ oRet oDisc G L E A (fun b => (B b).toHomeomorph) a hboundary hB
    hDisc hCap htrace hG hL hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

section

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {precision : ι → ℝ}
  (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
private local instance : LocallyPathConnectedSpace M :=
  originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
local notation "Bidx" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}

theorem exists_presentedStaticCap_of_finiteMetricEvent (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => E.incoming.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → E.incoming.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum E.terminal.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap E.incoming.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum E.terminal.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ b : E.RetainedBoundaryIndex,
          Nonempty (E.PresentedStaticCap fixed D m ε b) := by
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
  intro oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput b
  obtain ⟨e, he, hcap⟩ := exists_presentedStaticCap_neck_heq_of_finiteMetricEvent
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc E A B a hboundary
    hB hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  obtain ⟨S, _, _, _⟩ := hcap b
  exact ⟨S⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {precision : ι → ℝ}
  (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
private local instance : LocallyPathConnectedSpace M :=
  originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
local notation "Bidx" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}

theorem exists_presentedStaticCap_of_finiteMetricEvent_terminal (hD : 0 < D) :
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ b : E.RetainedBoundaryIndex,
          Nonempty (E.PresentedStaticCap fixed D m ε b) := by
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
  intro oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput b
  obtain ⟨e, he, hcap⟩ := exists_presentedStaticCap_neck_heq_of_finiteMetricEvent_terminal
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc G L E A B a hboundary
    hB hDisc hCap htrace hG hL hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  obtain ⟨S, _, _, _⟩ := hcap b
  exact ⟨S⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {precision : ι → ℝ}
  (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : LocallyPathConnectedSpace M :=
  originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
local notation "Bidx" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}

theorem exists_metricCutCapEvent_presentedStaticCap (hD : 0 < D) :
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
    ∀ (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
        (fun x : M => G.terminalRegularRegion x))
      (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
      (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
      (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
      (k' : Bidx → ℕ)
      (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
      (d : ∀ b : Bidx, normalizedDatum L.metric
        ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
      (hmap : ∀ b : Bidx, (d b).map =
        (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
      (hside : ∀ b : Bidx, (d b).retainedSide = true)
      (w : ∀ b : Bidx,
        CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε),
    let gRet : SmoothRiemannianMetric ThreeModel Ret := finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
      G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b, A b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ A b = LinearIsometryEquiv.neg ℝ) ∧
      (∀ b x, (B b x : ThreeSpace) = A b x) ∧
      ∃ E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
            hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary) ∧
        E.incoming = G ∧ HEq E.terminal L ∧ E.outputMetric = gRet ∧
        E.old = E.transition.trace.retainedCore ∧
        E.transition.boundaryFrameReversing ∧
        ∀ b : E.RetainedBoundaryIndex, Nonempty (E.PresentedStaticCap fixed D m ε b) := by
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
  intro G L hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w
  obtain ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, E, hDisc, hCap,
    htrace, hG, hL, hOutput, hOld, hBoundary, e, he, hcap⟩ :=
    exists_metricCutCapEvent_presentedStaticCap_neck_heq hδ hδ1 f hf hdisj hs R o
      hnontrivial hD G L hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w
  refine ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, E, hDisc, hCap,
    htrace, hG, hL, hOutput, hOld, hBoundary, ?_⟩
  intro b
  obtain ⟨S, _, _, _⟩ := hcap b
  exact ⟨S⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end


end
