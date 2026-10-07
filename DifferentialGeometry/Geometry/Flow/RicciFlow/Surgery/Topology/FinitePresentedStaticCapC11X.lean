import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticCoordinates

/-!
# FinitePresentedStaticCapC11X（S-CH11-EXT1，extension of 已跟踪 `FinitePresentedStaticCap`）

astra（`chapter11-astra` @ a73e4bdbfd）在 `Topology/FinitePresentedStaticCap.lean` 里对
`exists_presentedStaticCap_neck_heq_window_eq_of_finiteMetricEvent{,_terminal}` 与
`finitePresentedStaticCaps{,OfTerminal}` 做了加强：结论多一个
`S.witness.HasRadialCoordinates` 合取，并新增 `…_hasRadialCoordinates` 两个定理。
W8 的宿主文件保持不变（不替换已跟踪文件）；本文件逐字抄写 donor 的新增声明 / 加强声明，
证明体不改。规则：

* 新名字（W8 没有）原样保留：`…_coordinates_of_finiteMetricEvent{,_terminal}`、
  `finitePresentedStaticCaps_hasRadialCoordinates`、
  `finitePresentedStaticCapsOfTerminal_hasRadialCoordinates`；
* donor 里 **body 被改写**的两个 `def`（它们选出的 cap family 现在来自带 radial 的 `hex`）
  改名 `finitePresentedStaticCaps_C11X` / `finitePresentedStaticCapsOfTerminal_C11X`，W8 的
  同名旧 `def` 保留（两版并存；`…_hasRadialCoordinates` 说的是 `_C11X` 版选出的 family）。
* 宿主私有的 `terminal_data_transport` 用 `open private` 取得，不重复声明。
* **唯一一处非逐字改动**：两个 `_C11X` def 的末尾 `fun b => by obtain ⟨hδS, hkS, hNS, _, hwindow⟩ :=
  (hex.choose_spec.2 b).choose_spec; exact ⟨hδS, hkS, hNS, hwindow⟩` 改成同义的 term 模式投影
  `⟨….choose_spec.1, ….choose_spec.2.1, ….choose_spec.2.2.1, ….choose_spec.2.2.2.2⟩`
  （同一个 statement、同一个选择；donor 的 tactic 写法在树内 elaboration > 1000 s，term 写法两个 def 共 ≈ 3.5 min）。
-/

open private terminal_data_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap


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

theorem exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent (hD : 0 < D) :
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
              S.witness.HasRadialCoordinates ∧
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
    (finiteStaticRetainedTubePoint hδ f hf hdisj R c hc hδ1 b') ?_ ?_, rfl, rfl, HEq.rfl, ?_, fun _ => rfl⟩
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
  · exact (w b').toStaticCapWitness_hasRadialCoordinates hD


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

theorem exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent_terminal (hD : 0 < D) :
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
              S.witness.HasRadialCoordinates ∧
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
  exact exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent hδ hδ1 f hf hdisj hs R o
    hnontrivial hD oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace


def finitePresentedStaticCaps_C11X (hD : 0 < D) :
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
  let hex := exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc E A B a hboundary hB
    hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  exact ⟨hex.choose, ⟨fun b => (hex.choose_spec.2 b).choose,
    hex.choose_spec.1, fun b =>
      ⟨(hex.choose_spec.2 b).choose_spec.1, (hex.choose_spec.2 b).choose_spec.2.1,
        (hex.choose_spec.2 b).choose_spec.2.2.1, (hex.choose_spec.2 b).choose_spec.2.2.2.2⟩⟩⟩


/-- The radial companion belongs to the exact family selected above. No second
cap family is selected after projecting the constructor conclusion. -/
theorem finitePresentedStaticCaps_hasRadialCoordinates (hD : 0 < D) :
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
      ∀ (hB : ∀ b x, (B b x : ThreeSpace) = A b x),
      ∀ (hDisc : E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc),
      ∀ (hCap : E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ),
      ∀ (htrace : HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary)),
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
        ∀ (hOutput : E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w),
        ∀ b, ((finitePresentedStaticCaps_C11X hδ hδ1 f hf hdisj hs R o hnontrivial hD
          oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace hRet
          c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput).2.1 b).witness.HasRadialCoordinates := by
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
  let hex := exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc E A B a hboundary hB
    hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  change ∀ b, ((hex.choose_spec.2 b).choose).witness.HasRadialCoordinates
  exact fun b => (hex.choose_spec.2 b).choose_spec.2.2.2.1


def finitePresentedStaticCapsOfTerminal_C11X (hD : 0 < D) :
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
  let hex := exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent_terminal
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc G L E A B a hboundary hB
    hDisc hCap htrace hG hL hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  exact ⟨hex.choose, ⟨fun b => (hex.choose_spec.2 b).choose,
    hex.choose_spec.1, fun b =>
      ⟨(hex.choose_spec.2 b).choose_spec.1, (hex.choose_spec.2 b).choose_spec.2.1,
        (hex.choose_spec.2 b).choose_spec.2.2.1, (hex.choose_spec.2 b).choose_spec.2.2.2.2⟩⟩⟩


/-- The radial companion belongs to the exact family selected above. No second
cap family is selected after projecting the constructor conclusion. -/
theorem finitePresentedStaticCapsOfTerminal_hasRadialCoordinates (hD : 0 < D) :
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
      ∀ (hB : ∀ b x, (B b x : ThreeSpace) = A b x),
      ∀ (hDisc : E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc),
      ∀ (hCap : E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ),
      ∀ (htrace : HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary)),
      ∀ (hG : E.incoming = G) (hL : HEq E.terminal L),
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
        ∀ (hOutput : E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w),
        ∀ b, ((finitePresentedStaticCapsOfTerminal_C11X hδ hδ1 f hf hdisj hs R o hnontrivial hD
          oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL hRet
          c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput).2.1 b).witness.HasRadialCoordinates := by
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
  let hex := exists_presentedStaticCap_neck_heq_window_eq_coordinates_of_finiteMetricEvent_terminal
    hδ hδ1 f hf hdisj hs R o hnontrivial hD oQ oRet oDisc G L E A B a hboundary hB
    hDisc hCap htrace hG hL hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  change ∀ b, ((hex.choose_spec.2 b).choose).witness.HasRadialCoordinates
  exact fun b => (hex.choose_spec.2 b).choose_spec.2.2.2.1


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end
