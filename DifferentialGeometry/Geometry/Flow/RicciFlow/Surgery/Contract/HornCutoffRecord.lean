import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCorePresentationExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteProtectedCoreEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRecentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricCutCapCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffGeometryReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreMetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckIsometries
import DifferentialGeometry.Geometry.Neck.OrderReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCutRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornMetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryMetricEventMetricAlignment

noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section
universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private theorem exists_buffered_chart_geometry
    {M : Type*} [TopologicalSpace M] {ι : Type} [Fintype ι] {δ : ι → ℝ}
    (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j < 1)
    (f : ∀ j, bufferedCylinder (δ j) → M)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
    (hd : Pairwise fun j k => Disjoint (range (f j)) (range (f k)))
    (T : TubeSystem M) (htubes : T = TubeSystem.ofBufferedCharts hδ hδ1 f hf hd)
    {U : Set M} (g : ∀ j, bufferedCylinder (δ j) → U)
    (hgf : ∀ j x, (g j x).val = f j x) :
    ∃ e : ι ≃ T.Index,
      e = Equiv.cast (congrArg TubeSystem.Index htubes).symm ∧
      (Pairwise fun α β => Disjoint (range (g (e.symm α))) (range (g (e.symm β)))) ∧
      ∀ α (x : TubeDomain) (hx : (x.1, x.2.1) ∈ bufferedCylinder (δ (e.symm α))),
        T.tube α x = (g (e.symm α) ⟨(x.1, x.2.1), hx⟩).val := by
  subst T
  refine ⟨Equiv.refl ι, rfl, ?_, ?_⟩
  · intro j k hjk
    refine Set.disjoint_left.mpr ?_
    rintro p ⟨x, rfl⟩ ⟨y, hy⟩
    apply Set.disjoint_left.mp (hd hjk)
    · exact ⟨x, (hgf j x).symm⟩
    · refine ⟨y, ?_⟩
      exact (hgf k y).symm.trans (congrArg Subtype.val hy)
  · intro j x hx
    exact (hgf j ⟨(x.1, x.2.1), hx⟩).symm

private theorem boundary_label_from_heq
    {X Y : Type u} (hYX : Y = X)
    {P : X × Bool → Prop} {Q : Y × Bool → Prop}
    (eTube : X ≃ Y) (heTube : eTube = Equiv.cast hYX.symm)
    (eB : {b : Y × Bool // Q b} ≃ {b : X × Bool // P b})
    (he : ∀ b, HEq b.val (eB b).val) (b : {b : Y × Bool // Q b}) :
    (eB b).val.1 = eTube.symm b.val.1 ∧ (eB b).val.2 = b.val.2 := by
  cases hYX
  cases heTube
  have hh : b.val = (eB b).val := eq_of_heq (he b)
  exact ⟨congrArg Prod.fst hh.symm, congrArg Prod.snd hh.symm⟩

open private tube_system_eq_of_trace_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricEventDebit

open private retained_image_eq_of_trace_heq retained_image_of_buffered_finite_caps
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteProtectedCoreEvent

private structure PreparedCutoffEventGeometry
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (parameters : CutoffParameters) (δ r : ℝ) (k : ℕ) where
  singular : E.incoming.SingularEndpoint
  neck : E.transition.trace.tubes.Index → NormalizedNeck E.terminal.metric δ k
  scale_eq : ∀ α, (neck α).scale = (r ^ 2)⁻¹
  buffer_disjoint : Pairwise fun α β =>
    Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer δ,
    E.transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
  protected_interior : ∀ x : E.incoming.terminalRegularOpen,
    metricScalarAt E.terminal.metric x ≤
      ((parameters.protectedRadius s) ^ 2)⁻¹ →
    x.1 ∈ interior (Subtype.val '' E.transition.trace.retainedCore)
  retained_meets_protected : ∀ c : ConnectedComponents E.transition.trace.tubes.core,
    (∃ x : E.transition.trace.tubes.core,
      ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
    ∃ x : E.incoming.terminalRegularOpen,
      ∃ hx : x.1 ∈ E.transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
          metricScalarAt E.terminal.metric x ≤
            ((parameters.protectedRadius s) ^ 2)⁻¹
  one_retained_side : ∀ α,
    E.RetainedBoundary (α, true) ↔ ¬ E.RetainedBoundary (α, false)
  static : ∀ b : E.RetainedBoundaryIndex,
    E.PresentedStaticCap parameters.fixed parameters.modelRadius parameters.modelOrder
      parameters.modelAccuracy b
  recenter_mark : ∀ b : E.RetainedBoundaryIndex,
    (static b).neck.sphereMark = (neck b.1.1).sphereMark
  recenter_delta : ∀ b : E.RetainedBoundaryIndex,
    (static b).delta = parameters.recenterConstant * δ
  recenter_scale_comparison : ∀ b : E.RetainedBoundaryIndex,
    |(static b).neck.scale / (neck b.1.1).scale - 1| ≤
      parameters.recenterConstant * δ
  recenter_chart : ∀ b : E.RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
    ∀ hx : (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer δ,
      (static b).neck.chart x = (neck b.1.1).chart
        ⟨(x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩
  recenter_in_buffer : ∀ b : E.RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
      (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer δ
  old_eq_retained : E.old = E.transition.trace.retainedCore
  curvature_preserving : ∀ a : ℝ, 0 < a →
    (∀ x : E.incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion E.terminal.metric a x) →
    ∀ x : Q.Carrier, InFixedHamiltonIveyRegion E.outputMetric a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 →
    (∀ x : E.incoming.terminalRegularOpen,
      L ≤ metricScalarAt E.terminal.metric x) →
    ∀ x : Q.Carrier, L ≤ metricScalarAt E.outputMetric x

private def PreparedCutoffEventGeometry.toRetained
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {p : CutoffParameters} {δ r : ℝ} {k : ℕ}
    (F : PreparedCutoffEventGeometry E p δ r k) :
    PreparedCutoffEventGeometry
      (E.toRetainedCoreEvent F.old_eq_retained).toMetricCutCapEvent p δ r k where
  singular := F.singular
  neck := F.neck
  scale_eq := F.scale_eq
  buffer_disjoint := F.buffer_disjoint
  tube_eq := F.tube_eq
  protected_interior := F.protected_interior
  retained_meets_protected := F.retained_meets_protected
  one_retained_side := F.one_retained_side
  static := fun b => {
    delta := (F.static b).delta
    order := (F.static b).order
    neck := (F.static b).neck
    witness := (F.static b).witness
    inclusion := (F.static b).inclusion
    inclusion_smooth := (F.static b).inclusion_smooth
    inclusion_metric := (F.static b).inclusion_metric
    cap_eq := (F.static b).cap_eq
    attaching_eq := (F.static b).attaching_eq
    retainedPoint := (F.static b).retainedPoint
    retained_point_eq := (F.static b).retained_point_eq
    retained_eq := (F.static b).retained_eq }
  recenter_mark := F.recenter_mark
  recenter_delta := F.recenter_delta
  recenter_scale_comparison := F.recenter_scale_comparison
  recenter_chart := F.recenter_chart
  recenter_in_buffer := F.recenter_in_buffer
  old_eq_retained := rfl
  curvature_preserving := F.curvature_preserving
  scalar_preserving := F.scalar_preserving

private theorem PreparedCutoffEventGeometry.exists_of_retainedEvent_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {p : CutoffParameters} {δ r : ℝ} {k : ℕ}
    (F : PreparedCutoffEventGeometry E p δ r k)
    (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s)
    (hE : HEq E' (E.toRetainedCoreEvent F.old_eq_retained)) :
    ∃ F' : PreparedCutoffEventGeometry E'.toMetricCutCapEvent p δ r k,
      ∃ e : E'.transition.trace.tubes.Index ≃ E.transition.trace.tubes.Index,
        ∀ j, HEq (F'.neck j) (F.neck (e j)) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨F.toRetained, Equiv.refl _, fun _ => HEq.rfl⟩

private theorem geometricCutoffRecord_of_preparedEventGeometry
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    {δ r : ℝ} {k : ℕ}
    (F : PreparedCutoffEventGeometry (H.event i) p δ r k)
    (hδ : δ ≤ p.delta (H.time i.succ))
    (hk : max (p.modelOrder + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ k)
    (hr : r < (p.delta (H.time i.succ)) ^ 2 * p.neckRadius (H.time i.succ))
    (hback : ∀ j, IncomingBackwardNeck H i (F.neck j) r) :
    Nonempty (GeometricCutoffRecord H i p) := by
  refine ⟨GeometricCutoffRecord.ofFrontier {
    singular := F.singular
    nominalRadius := fun _ => r
    nominal_small := fun _ => hr
    nominal_time := ?_
    delta := fun _ => δ
    delta_le := fun _ => hδ
    order := fun _ => k
    order_lower := fun _ => hk
    neck := F.neck
    scale_eq := F.scale_eq
    buffer_disjoint := F.buffer_disjoint
    tube_eq := F.tube_eq
    backward := hback
    protected_interior := F.protected_interior
    retained_meets_protected := F.retained_meets_protected
    one_retained_side := F.one_retained_side
    no_cuts_discard := fun h => @geometricCutoff_no_cuts_discard H i h
    static := F.static
    recenter_mark := F.recenter_mark
    recenter_delta := F.recenter_delta
    recenter_scale_comparison := F.recenter_scale_comparison
    recenter_chart := F.recenter_chart
    recenter_in_buffer := F.recenter_in_buffer
    old_eq_retained := F.old_eq_retained
    curvature_preserving := F.curvature_preserving
    scalar_preserving := F.scalar_preserving }⟩
  rintro ⟨j⟩
  have hnonneg := (hback j).left_nonneg
  linarith


variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {δ : ℝ}
  (hδ : ∀ _ : ι, 0 < δ) (hδ1 : ∀ _ : ι, δ < 1)
  (f : ι → bufferedCylinder δ → M)
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

variable {t₀ t₁ : ℝ}

private theorem exists_preparedCutoffEventGeometry_of_finiteMetricEvent
    (p : CutoffParameters) {r : ℝ} {k : ℕ} :
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
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming.SingularEndpoint → E.old = E.transition.trace.retainedCore →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => E.incoming.terminalRegularRegion x))
        (x₀ : ι → E.incoming.terminalRegularOpen)
        (d₀ : ∀ j, normalizedDatum E.terminal.metric (x₀ j) δ (p.modelOrder + 6))
        (hOriginal : ∀ j, f j = neckAmbientMap E.incoming.terminalRegularOpen (d₀ j))
        (N : ι → NormalizedNeck E.terminal.metric δ k)
        (_ : ∀ j q, (N j).chart q = (d₀ j).map q)
        (_ : ∀ j, (N j).sphereMark = spherePoint)
        (_ : ∀ j, (N j).scale = metricScalarAt E.terminal.metric (x₀ j))
        (_ : ∀ j, metricScalarAt E.terminal.metric (x₀ j) = (r ^ 2)⁻¹)
        (_ : ∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((p.protectedRadius t₁)^2)⁻¹ →
          x.val ∈ interior ((Subtype.val : cutCore f → M) '' retainedCore f R))
        (_ : R ⊆ scalarSublevelComponents E.incoming.terminalRegularOpen
          E.terminal.metric f ((p.protectedRadius t₁)^2)⁻¹)
        (_ : ∀ j, cuttingSphereComponent hδ f hf hdisj (j, true) ∈ R ∧
          cuttingSphereComponent hδ f hf hdisj (j, false) ∉ R)
        (hrec : ∀ _ : Bidx, (p.recenterConstant * δ)⁻¹ + 1 ≤ δ⁻¹)
        (d : ∀ b : Bidx, normalizedDatum E.terminal.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
          (p.recenterConstant * δ) (p.modelOrder + 4))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b)
          p.fixed.collarLength p.fixed.collar_pos p.modelRadius p.modelOrder p.modelAccuracy)
        (_ : ∀ b : Bidx,
          |metricScalarAt E.terminal.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
            metricScalarAt E.terminal.metric (x₀ b.val.1) - 1| ≤ p.recenterConstant * δ)
        (_ : ∀ c : ℝ, 0 < c →
          (∀ z, InFixedHamiltonIveyRegion E.terminal.metric c z) →
          ∀ z, InFixedHamiltonIveyRegion E.outputMetric c z)
        (_ : ∀ B₀ : ℝ, B₀ ≤ 0 →
          (∀ z, B₀ ≤ metricScalarAt E.terminal.metric z) →
          ∀ z, B₀ ≤ metricScalarAt E.outputMetric z),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet p.recenterConstant p.recenterConstant_ge_four x₀
          (fun _ => p.modelOrder + 6) d₀ hOriginal hrec d hmap hside w →
        ∃ (e : ι ≃ E.transition.trace.tubes.Index)
          (F : PreparedCutoffEventGeometry E p δ r k),
          F.neck = fun j => N (e.symm j) := by
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
  intro oQ oRet oDisc E A B a hboundary hB hDisc hCap htrace hsing hOld hRet x₀ d₀
    hOriginal N hNchart hNmark hNscale hscale hprotected hR hone hrec d hmap hside w hratio hcurvature hscalar hOutput
  classical
  have htubes : E.transition.trace.tubes = T := tube_system_eq_of_trace_heq hDisc hCap htrace
  obtain ⟨e, he, hd, htube⟩ := exists_buffered_chart_geometry hδ hδ1 f hf hdisj
    E.transition.trace.tubes htubes (fun j => (d₀ j).map)
    (fun j q => by rw [hOriginal j]; rfl)
  obtain ⟨eB, heB, hS⟩ := exists_presentedStaticCap_neck_heq_of_finiteMetricEvent
    hδ hδ1 f hf hdisj hs R o hnontrivial p.modelRadius_pos oQ oRet oDisc E A B a hboundary
    hB hDisc hCap htrace hRet p.recenterConstant p.recenterConstant_ge_four x₀ (fun _ => p.modelOrder + 6) d₀
    hOriginal (fun _ => p.modelOrder + 4) hrec d hmap hside w hOutput
  choose S hSδ hSk hSN using hS
  have hlabel (b : E.RetainedBoundaryIndex) :=
    boundary_label_from_heq (congrArg TubeSystem.Index htubes) e he eB heB b
  have hfields (b : E.RetainedBoundaryIndex) :=
    (S b).recenter_fields_of_neck_heq (d₀ (eB b).val.1) (d₀ (eB b).val.1) rfl
      (eB b).val.2 (hrec (eB b)) (d (eB b)) (hmap (eB b)) (hside (eB b))
      (hSδ b) (hSk b) (hSN b) (hratio (eB b))
  have himage : (Subtype.val : E.transition.trace.tubes.core → M) '' E.transition.trace.retainedCore =
      (Subtype.val : cutCore f → M) '' retainedCore f R :=
    (retained_image_eq_of_trace_heq hDisc hCap htrace).trans
      (retained_image_of_buffered_finite_caps transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial)
  refine ⟨e, {
    singular := hsing
    neck := fun j => N (e.symm j)
    scale_eq := fun j => (hNscale (e.symm j)).trans (hscale (e.symm j))
    buffer_disjoint := ?_
    tube_eq := ?_
    protected_interior := ?_
    retained_meets_protected := ?_
    one_retained_side := ?_
    static := S
    recenter_mark := ?_
    recenter_delta := hSδ
    recenter_scale_comparison := ?_
    recenter_chart := ?_
    recenter_in_buffer := ?_
    old_eq_retained := hOld
    curvature_preserving := hcurvature
    scalar_preserving := hscalar }, rfl⟩
  · intro j l hjl
    refine Set.disjoint_left.mpr ?_
    rintro q ⟨y, rfl⟩ ⟨z, hz⟩
    apply Set.disjoint_left.mp (hd hjl)
    · exact ⟨y, (hNchart _ y).symm⟩
    · exact ⟨z, (hNchart _ z).symm.trans hz⟩
  · intro j z hz
    exact (htube j z hz).trans (congrArg Subtype.val (hNchart _ _).symm)
  · intro x hx
    rw [himage]
    exact hprotected x hx
  · exact finiteMetricCutCapEvent_retained_meets_scalar_sublevel
      transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial hs o oQ oRet oDisc E B a
      hboundary hDisc hCap htrace _ hR
  · exact finiteMetricCutCapEvent_one_retained_side
      transitionEnd_pos hδ hδ1 f hf hdisj R hnontrivial hs o oQ oRet oDisc E B a
      hboundary hDisc hCap htrace (fun j => iff_of_true (hone j).1 (hone j).2)
  · intro b
    rw [hNmark]
    exact (hfields b).2.2.1
  · intro b
    have h := (hfields b).2.2.2.1
    change |(S b).neck.scale / metricScalarAt E.terminal.metric (x₀ (eB b).val.1) - 1| ≤
      p.recenterConstant * δ at h
    have hscaleB : (N (e.symm b.val.1)).scale = metricScalarAt E.terminal.metric (x₀ (eB b).val.1) :=
      (hNscale _).trans (congrArg (fun j => metricScalarAt E.terminal.metric (x₀ j))
        (hlabel b).1.symm)
    exact hscaleB.symm ▸ h
  · intro b z hz
    have hz' : (z.val.1, (if (eB b).val.2 then (1 : ℝ) else -1) * (1 + z.val.2)) ∈ neckBuffer δ :=
      (hlabel b).2.symm ▸ hz
    have h := (hfields b).2.2.2.2.2 z hz'
    apply h.trans
    change (d₀ (eB b).val.1).map _ = _
    have hpt : (⟨(z.val.1, (if (eB b).val.2 then (1 : ℝ) else -1) * (1 + z.val.2)), hz'⟩ : neckBuffer δ) =
        ⟨(z.val.1, (if b.val.2 then (1 : ℝ) else -1) * (1 + z.val.2)), hz⟩ := by
      apply Subtype.ext
      exact congrArg (fun v : Bool => (z.val.1, (if v then (1 : ℝ) else -1) * (1 + z.val.2))) (hlabel b).2
    exact (congrArg₂ (fun j q => (d₀ j).map q) (hlabel b).1 hpt).trans (hNchart _ _).symm
  · intro b z
    exact (hlabel b).2 ▸ (hfields b).2.2.2.2.1 z

open private terminal_data_transport
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap

private theorem exists_preparedCutoffEventGeometry_of_finiteMetricEvent_terminal
    (p : CutoffParameters) {r : ℝ} {k : ℕ} :
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
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      G.SingularEndpoint → E.old = E.transition.trace.retainedCore →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (x₀ : ι → G.terminalRegularOpen)
        (d₀ : ∀ j, normalizedDatum L.metric (x₀ j) δ (p.modelOrder + 6))
        (hOriginal : ∀ j, f j = neckAmbientMap G.terminalRegularOpen (d₀ j))
        (N : ι → NormalizedNeck L.metric δ k)
        (_ : ∀ j q, (N j).chart q = (d₀ j).map q)
        (_ : ∀ j, (N j).sphereMark = spherePoint)
        (_ : ∀ j, (N j).scale = metricScalarAt L.metric (x₀ j))
        (_ : ∀ j, metricScalarAt L.metric (x₀ j) = (r ^ 2)⁻¹)
        (_ : ∀ x : G.terminalRegularOpen,
          metricScalarAt L.metric x ≤ ((p.protectedRadius t₁)^2)⁻¹ →
          x.val ∈ interior ((Subtype.val : cutCore f → M) '' retainedCore f R))
        (_ : R ⊆ scalarSublevelComponents G.terminalRegularOpen
          L.metric f ((p.protectedRadius t₁)^2)⁻¹)
        (_ : ∀ j, cuttingSphereComponent hδ f hf hdisj (j, true) ∈ R ∧
          cuttingSphereComponent hδ f hf hdisj (j, false) ∉ R)
        (hrec : ∀ _ : Bidx, (p.recenterConstant * δ)⁻¹ + 1 ≤ δ⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
          (p.recenterConstant * δ) (p.modelOrder + 4))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b)
          p.fixed.collarLength p.fixed.collar_pos p.modelRadius p.modelOrder p.modelAccuracy)
        (_ : ∀ b : Bidx,
          |metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
            metricScalarAt L.metric (x₀ b.val.1) - 1| ≤ p.recenterConstant * δ)
        (_ : ∀ c : ℝ, 0 < c →
          (∀ z, InFixedHamiltonIveyRegion L.metric c z) →
          ∀ z, InFixedHamiltonIveyRegion E.outputMetric c z)
        (_ : ∀ B₀ : ℝ, B₀ ≤ 0 →
          (∀ z, B₀ ≤ metricScalarAt L.metric z) →
          ∀ z, B₀ ≤ metricScalarAt E.outputMetric z),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet p.recenterConstant p.recenterConstant_ge_four x₀
          (fun _ => p.modelOrder + 6) d₀ hOriginal hrec d hmap hside w →
        ∃ (e : ι ≃ E.transition.trace.tubes.Index)
          (F : PreparedCutoffEventGeometry E p δ r k),
          ∀ j, HEq (F.neck (e j)) (N j) := by
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
  intro hsing hOld hRet x₀ d₀ hOriginal N hNchart hNmark hNscale hscale hprotected hR
    hone hrec d hmap hside w hratio hcurvature hscalar hOutput
  obtain ⟨e, F, hF⟩ := exists_preparedCutoffEventGeometry_of_finiteMetricEvent
    hδ hδ1 f hf hdisj hs R o hnontrivial p oQ oRet oDisc E A B a hboundary
    hB hDisc hCap htrace hsing hOld hRet x₀ d₀ hOriginal N hNchart hNmark hNscale
    hscale hprotected hR hone hrec d hmap hside w hratio hcurvature hscalar hOutput
  refine ⟨e, F, fun j => heq_of_eq ?_⟩
  exact (congrFun hF (e j)).trans (congrArg N (e.symm_apply_apply j))

end

section

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

section Static

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ₀ δ : ℝ} {k l m : ℕ}

private def orientedRotatedNeck (N : NormalizedNeck g δ₀ k)
    (hδ : δ₀ ≤ δ) (hδ1 : δ < 1)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : DifferentialGeometry.Geometry.sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (hl : l ≤ k) : NormalizedNeck g δ l :=
  (((N.monoDelta hδ hδ1).rotatedDatum e he side).oriented).toNormalizedNeck.lowerOrder hl

private theorem orientedRotatedNeck_eq_datum_chart
    (N : NormalizedNeck g δ₀ k) (hδ : δ₀ ≤ δ) (hδ1 : δ < 1)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : DifferentialGeometry.Geometry.sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (hl : l ≤ k) (hm : m ≤ k) {x : M} (hcenter : N.center = x)
    (d : normalizedDatum g x δ m)
    (hd : HEq d (((N.monoDelta hδ hδ1).rotatedDatum e he side).oriented.lowerOrder hm)) :
    let N' := orientedRotatedNeck N hδ hδ1 e he side hl
    N'.chart = ⟨d.map, d.smooth.continuous⟩ ∧
      N'.center = x ∧ N'.sphereMark = spherePoint ∧ N'.scale = N.scale := by
  cases hcenter
  cases eq_of_heq hd
  exact ⟨rfl, rfl, rfl, N.scale_scalar.symm⟩

end Static

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private def IncomingBackwardNeck.orientedRotatedNeck
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ₀ δ r : ℝ} {k l : ℕ}
    {N : NormalizedNeck (H.event i).terminal.metric δ₀ k}
    (B : IncomingBackwardNeck H i N r) (hδ : δ₀ ≤ δ) (hδ1 : δ < 1)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : DifferentialGeometry.Geometry.sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (hl : l ≤ k) :
    IncomingBackwardNeck H i (orientedRotatedNeck N hδ hδ1 e he side hl) r :=
  (IncomingBackwardNeck.oriented _ ((B.monoDelta hδ hδ1).rotatedDatum e he side)).lowerOrder hl

end

section

private def cutoffParametersOfFiniteCap
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ρ : ℝ) (hρ : 0 < ρ)
    (r : ℝ) (hr : 0 < r) (fixed : StaticCapScaffold)
    (D : ℝ) (hD : 0 < D) (m : ℕ) (accuracy : ℝ) (ha : 0 < accuracy)
    (c : ℝ) (hc : 4 ≤ c) : CutoffParameters where
  delta := fun _ => δ
  neckRadius := fun _ => ρ
  protectedRadius := fun _ => r
  delta_pos := fun _ _ => hδ
  delta_lt_one := fun _ _ => hδ1
  neckRadius_pos := fun _ _ => hρ
  protectedRadius_pos := fun _ _ => hr
  fixed := fixed
  modelRadius := D
  modelRadius_pos := hD
  modelOrder := m
  modelAccuracy := accuracy
  modelAccuracy_pos := ha
  recenterConstant := c
  recenterConstant_ge_four := hc

private theorem sqrt_inv_lt_of_inv_sq_lt {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R)
    (h : (R ^ 2)⁻¹ < Q) : Real.sqrt Q⁻¹ < R := by
  apply (Real.sqrt_lt (inv_nonneg.mpr hQ.le) hR.le).2
  have hQR : Q⁻¹ < R ^ 2 := by
    simpa only [inv_inv] using (inv_lt_inv₀ hQ (inv_pos.mpr (pow_pos hR 2))).mpr h
  exact hQR

end

set_option autoImplicit false

section

universe u

private theorem exists_preparedCutoffEventGeometry_of_finiteMetricEvent_stage
    (P : OrientedThreeStage.{u})
    {ι : Type} [Fintype ι] {δ : ℝ}
    (hδ : ∀ _ : ι, 0 < δ) (hδ1 : ∀ _ : ι, δ < 1)
    (f : ι → bufferedCylinder δ → P.Carrier)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
    (R : Set (ConnectedComponents (cutCore f)))
    (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))
    (p : CutoffParameters) {r : ℝ} {k : ℕ} {t₀ t₁ : ℝ} :
    letI : LocallyPathConnectedSpace P.Carrier :=
      originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
    let Q := FiniteCapQuotient transitionEnd_pos hδ f
      (fun i => (hf i).injective) hdisj
    let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
    let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
    let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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
      (G : P.IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      (∀ b x, (B b x : ThreeSpace) = A b x) →
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B (fun b => (a b).toHomeomorph) hboundary) →
      E.incoming = G → HEq E.terminal L →
      G.SingularEndpoint → E.old = E.transition.trace.retainedCore →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R)
          (fun x : P.Carrier => G.terminalRegularRegion x))
        (x₀ : ι → G.terminalRegularOpen)
        (d₀ : ∀ j, normalizedDatum L.metric (x₀ j) δ (p.modelOrder + 6))
        (hOriginal : ∀ j, f j = neckAmbientMap G.terminalRegularOpen (d₀ j))
        (N : ι → NormalizedNeck L.metric δ k)
        (_ : ∀ j q, (N j).chart q = (d₀ j).map q)
        (_ : ∀ j, (N j).sphereMark = spherePoint)
        (_ : ∀ j, (N j).scale = metricScalarAt L.metric (x₀ j))
        (_ : ∀ j, metricScalarAt L.metric (x₀ j) = (r ^ 2)⁻¹)
        (_ : ∀ x : G.terminalRegularOpen,
          metricScalarAt L.metric x ≤ ((p.protectedRadius t₁)^2)⁻¹ →
          x.val ∈ interior ((Subtype.val : cutCore f → P.Carrier) '' retainedCore f R))
        (_ : R ⊆ scalarSublevelComponents G.terminalRegularOpen
          L.metric f ((p.protectedRadius t₁)^2)⁻¹)
        (_ : ∀ j, cuttingSphereComponent hδ f hf hdisj (j, true) ∈ R ∧
          cuttingSphereComponent hδ f hf hdisj (j, false) ∉ R)
        (hrec : ∀ _ : Bidx, (p.recenterConstant * δ)⁻¹ + 1 ≤ δ⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
          (p.recenterConstant * δ) (p.modelOrder + 4))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx, CanonicalStaticInsertionWitness (d b)
          p.fixed.collarLength p.fixed.collar_pos p.modelRadius p.modelOrder p.modelAccuracy)
        (_ : ∀ b : Bidx,
          |metricScalarAt L.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
            metricScalarAt L.metric (x₀ b.val.1) - 1| ≤ p.recenterConstant * δ)
        (_ : ∀ c : ℝ, 0 < c →
          (∀ z, InFixedHamiltonIveyRegion L.metric c z) →
          ∀ z, InFixedHamiltonIveyRegion E.outputMetric c z)
        (_ : ∀ B₀ : ℝ, B₀ ≤ 0 →
          (∀ z, B₀ ≤ metricScalarAt L.metric z) →
          ∀ z, B₀ ≤ metricScalarAt E.outputMetric z),
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet p.recenterConstant p.recenterConstant_ge_four x₀
          (fun _ => p.modelOrder + 6) d₀ hOriginal hrec d hmap hside w →
        ∃ (e : ι ≃ E.transition.trace.tubes.Index)
          (F : PreparedCutoffEventGeometry E p δ r k),
          ∀ j, HEq (F.neck (e j)) (N j) := by
  revert f
  rw [← P.ofSmoothOrientation_smoothOrientation]
  intro f hf hdisj hs R hnontrivial
  exact exists_preparedCutoffEventGeometry_of_finiteMetricEvent_terminal
    hδ hδ1 f hf hdisj hs R P.smoothOrientation hnontrivial p

end

section

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

open private terminal_data_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap

universe v

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem original_neck_data_of_terminal_heq
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric)
    (hG : E.incoming = G) (hL : HEq E.terminal L)
    {ι : Type v} {δ : ℝ} {l : ℕ} (hδ1 : δ < 1)
    (δOrig : ι → ℝ) (kOrig : ι → ℕ)
    (NOrig : ∀ j, NormalizedNeck L.metric (δOrig j) (kOrig j))
    (hδOrig : ∀ j, δOrig j ≤ δ)
    (rotation : ι → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
      (NOrig j).sphereMark)
    (side : ι → Bool) (horder : ∀ j, l ≤ kOrig j) :
    ∃ (NE : ∀ j, NormalizedNeck E.terminal.metric (δOrig j) (kOrig j))
      (hmarkE : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
        (NE j).sphereMark),
      HEq NE NOrig ∧ (∀ j, HEq (NE j) (NOrig j)) ∧
      (∀ j, (NE j).scale = (NOrig j).scale) ∧
      ∀ j, HEq (orientedRotatedNeck (NE j) (hδOrig j) hδ1
          (rotation j) (hmarkE j) (side j) (horder j))
        (orientedRotatedNeck (NOrig j) (hδOrig j) hδ1
          (rotation j) (hmark j) (side j) (horder j)) := by
  subst G
  cases eq_of_heq hL
  exact ⟨NOrig, hmark, HEq.rfl, fun _ => HEq.rfl, fun _ => rfl, fun _ => HEq.rfl⟩

private theorem exists_prepared_horn_cutoff_event :
    ∃ (c : ℝ) (_ : 4 ≤ c) (A : ℝ) (hA : 0 < A),
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ ε₀ → ∃ (Qout : OrientedThreeStage.{u})
        (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (p : CutoffParameters) (Q : ℝ)
        (N : E.transition.trace.tubes.Index → NormalizedNeck E.terminal.metric δ
          (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4))),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        p.delta = (fun _ => δ) ∧ p.protectedRadius = (fun _ => P.coreRadius) ∧
        p.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        p.fixed = StaticCapScaffold.ofCollarLength A hA ∧ p.modelOrder = m ∧
        p.modelRadius = Dcap ∧ p.modelAccuracy = accuracy ∧ p.recenterConstant = c ∧
        Real.sqrt Q⁻¹ < (p.delta D.endTime)^2 * p.neckRadius D.endTime ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        ∃ F : PreparedCutoffEventGeometry E p δ (Real.sqrt Q⁻¹)
          (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)), F.neck = N ∧
          ∃ (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
            (NOriginal : ∀ j, NormalizedNeck E.terminal.metric (δOriginal j) (kOriginal j))
            (hδOriginal : ∀ j, δOriginal j ≤ δ)
            (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
            (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
              spherePoint = (NOriginal j).sphereMark)
            (side : Fin n → Bool)
            (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
            (hδ1 : δ < 1) (e : Fin n ≃ E.transition.trace.tubes.Index),
            (∀ j, (NOriginal j).scale = Q) ∧
            ∀ j, F.neck (e j) = orientedRotatedNeck (NOriginal j) (hδOriginal j)
              hδ1 (rotation j) (hmark j) (side j) (horder j) := by
  classical
  choose c hc C hC A hA hsmall hfamily using
    exists_uniform_horn_cut_metricCutCapEvent_volume_debit_with_recenter_data.{u}
  refine ⟨c, hc, A, hA, ?_⟩
  intro Dcap hDcap m accuracy haccuracy
  choose δ hδ hquarter ε₀ hε₀ hεorder hmake using hfamily Dcap hDcap m accuracy haccuracy
  have hδ1 : δ < 1 := hquarter.trans (by norm_num)
  refine ⟨δ, hδ, hδ1, ε₀, hε₀, ?_⟩
  intro D ε Λ P hε
  let _ : SigmaCompactSpace D.slab.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)
  choose Q₀ hQ₀ hmakeQ using hmake P hε
  let ρ := D.parameters.neckRadius D.endTime
  have ht : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hρ : 0 < ρ := D.parameters.neckRadius_pos _ ht
  let Q := max Q₀ (((δ^2 * ρ)^2)⁻¹) + 1
  have hQQ : Q₀ < Q := by dsimp [Q]; linarith [le_max_left Q₀ (((δ^2 * ρ)^2)⁻¹)]
  have hQ : 0 < Q := hQ₀.trans hQQ
  have hr : Real.sqrt Q⁻¹ < δ^2 * ρ :=
    sqrt_inv_lt_of_inv_sq_lt hQ (mul_pos (pow_pos hδ 2) hρ) (by
      dsimp [Q]; linarith [le_max_right Q₀ (((δ^2 * ρ)^2)⁻¹)])
  choose Fhorn Khorn hK hfix hF hcore e t a ν x₀ d hcenter ha hside hmap hf hd hlocal hRet
    hfaces horiginal oQ oRet oDisc rotationCap B aCap hboundary hchoice hB E
    hDisc hCap htrace htubes hG hL hOld hBoundary hpin hfloor hvol hrec dCap
    hcapMap hcapSide w hOutput hratio hw hbound using hmakeQ Q hQQ spherePoint
  let P' := P.reparametrizeHornsOfCompactSupport Fhorn hfix Khorn hK hF
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P'.coreRadius^2)⁻¹
  obtain ⟨δOrig, kOrig, NOrig, hδOrig, rotation, hmark, side, horder, hdata, hdet, hdatum⟩ := horiginal
  let k := max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)
  have hk (j) : k ≤ kOrig j := by
    apply max_le (horder j)
    exact (hεorder.trans (Nat.add_le_add_right
      (Nat.floor_mono (inv_anti₀ P.epsilon_pos hε)) 1)).trans (hdata j).2.2.2
  let Nhigh := fun j => orientedRotatedNeck (NOrig j) (hδOrig j) hδ1
    (rotation j) (hmark j) (side j) (hk j)
  have hNdata (j) := orientedRotatedNeck_eq_datum_chart (NOrig j) (hδOrig j) hδ1
    (rotation j) (hmark j) (side j) (hk j) (horder j) (hdata j).1 (d j) (hdatum j)
  let p := cutoffParametersOfFiniteCap δ hδ hδ1 ρ hρ P'.coreRadius P'.coreRadius_pos
    (StaticCapScaffold.ofCollarLength A hA) Dcap hDcap m accuracy haccuracy c hc
  let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
  let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
    f (fun j => (hf j).injective) hd
  let _ : LocallyPathConnectedSpace D.stage.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let _ : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd
  let _ : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd hlocal
  let _ : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let _ : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let _ : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).1
  let _ : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).2
  have hprotected : ∀ x : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤ ((p.protectedRadius D.endTime)^2)⁻¹ →
      x.val ∈ interior ((Subtype.val : cutCore f → D.stage.Carrier) '' retainedCore f R) := by
    intro x hx
    exact P'.retainedCore_protected_of_central_horn_matching (fun _ => δ) e a
      (fun j => by linarith [ha j, inv_pos.mpr hδ]) f (fun j => ν j)
      (fun j q _ => congrArg Subtype.val (hmap j q)) x hx
  have hscale (j) : metricScalarAt D.terminal.metric (x₀ j) = ((Real.sqrt Q⁻¹)^2)⁻¹ := by
    rw [(hcenter j).2.2, Real.sq_sqrt (inv_nonneg.mpr hQ.le), inv_inv]
  have hone (j) : cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,true) ∈ R ∧
      cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,false) ∉ R := by
    exact ⟨(hfaces j true).mpr rfl, fun h => Bool.false_ne_true ((hfaces j false).mp h)⟩
  have hNchart (j q) : (Nhigh j).chart q = (d j).map q :=
    congrArg (fun C => C q) (hNdata j).1
  have hNmark (j) : (Nhigh j).sphereMark = spherePoint := (hNdata j).2.2.1
  have hNscale (j) : (Nhigh j).scale = metricScalarAt D.terminal.metric (x₀ j) :=
    (hNdata j).2.2.2.trans ((hdata j).2.1.trans (hcenter j).2.2.symm)
  have hpreserve := terminal_data_transport E D.slab D.terminal hG hL
    (F := fun G L =>
      (∀ z : ℝ, 0 < z → (∀ x, InFixedHamiltonIveyRegion L.metric z x) →
        ∀ x, InFixedHamiltonIveyRegion E.outputMetric z x) ∧
      (∀ z : ℝ, z ≤ 0 → (∀ x, z ≤ metricScalarAt L.metric x) →
        ∀ x, z ≤ metricScalarAt E.outputMetric x)) ⟨hpin, hfloor⟩
  obtain ⟨eEvent, geometry, hgeometry⟩ :=
    exists_preparedCutoffEventGeometry_of_finiteMetricEvent_stage D.stage
      (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
      f hf hd hlocal R hnontrivial p oQ oRet oDisc D.slab D.terminal E rotationCap
      (fun b => (B b).toHomeomorph) aCap hboundary hB hDisc hCap htrace hG hL D.singular hOld
      hRet x₀ d (fun _ => rfl) Nhigh hNchart hNmark hNscale hscale hprotected
      Subset.rfl hone hrec dCap hcapMap hcapSide w hratio hpreserve.1 hpreserve.2 hOutput
  obtain ⟨NOrigE, hmarkE, hNE, hNEpoint, hNEscale, hNEhigh⟩ := original_neck_data_of_terminal_heq
    E D.slab D.terminal hG hL hδ1 δOrig kOrig NOrig hδOrig rotation hmark side hk
  have hEscale (j) : (NOrigE j).scale = Q := by
    exact (hNEscale j).trans (hdata j).2.1
  refine ⟨_, E, p, Q, geometry.neck, hQ, hG, hL, hOld, hBoundary,
    rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hr, hvol, hbound, geometry, rfl,
    _, δOrig, kOrig, NOrigE, hδOrig, rotation, hmarkE, side, hk, hδ1, eEvent, hEscale, ?_⟩
  · exact funext fun _ => rfl
  · intro j
    exact eq_of_heq ((hgeometry j).trans (hNEhigh j).symm)

end

section

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem exists_original_backward_transfer
    {P₀ P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory P₀} {i : Fin H.eventCount}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hP : H.stage i.castSucc = P) (hQ : H.stage i.succ = Q)
    (ha : H.time i.castSucc = a) (hs : H.time i.succ = s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hE : HEq (H.coreEvent i) (E.toRetainedCoreEvent hOld))
    {ι : Type*} {δ : ℝ} {δOriginal : ι → ℝ} {kOriginal : ι → ℕ} {k : ℕ}
    (N : ∀ j, NormalizedNeck E.terminal.metric (δOriginal j) (kOriginal j))
    (hδ : ∀ j, δOriginal j ≤ δ) (hδ1 : δ < 1)
    (rotation : ι → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
      spherePoint = (N j).sphereMark) (side : ι → Bool)
    (horder : ∀ j, k ≤ kOriginal j) :
    ∃ (NH : ∀ j, NormalizedNeck (H.toHistory.event i).terminal.metric (δOriginal j) (kOriginal j))
      (NHhigh : ι → NormalizedNeck (H.toHistory.event i).terminal.metric δ k),
      HEq NH N ∧ (∀ j, HEq (NH j) (N j)) ∧
      (∀ j, (NH j).scale = (N j).scale) ∧
      ∃ hmarkH : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NH j).sphereMark,
      (∀ j, NHhigh j = orientedRotatedNeck (NH j) (hδ j) hδ1
        (rotation j) (hmarkH j) (side j) (horder j)) ∧
      HEq NHhigh (fun j => orientedRotatedNeck (N j) (hδ j) hδ1
        (rotation j) (hmark j) (side j) (horder j)) ∧
      (∀ j, HEq (NHhigh j) (orientedRotatedNeck (N j) (hδ j) hδ1
        (rotation j) (hmark j) (side j) (horder j))) ∧
      ∀ r, (∀ j, Nonempty (IncomingBackwardNeck H.toHistory i (NH j) r)) →
        ∀ j, Nonempty (IncomingBackwardNeck H.toHistory i (NHhigh j) r) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  have heq := eq_of_heq hE
  have hdata :
      ∃ (NH : ∀ j, NormalizedNeck (H.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j)),
        HEq NH N ∧ (∀ j, HEq (NH j) (N j)) ∧
        (∀ j, (NH j).scale = (N j).scale) ∧
        ∃ hmarkH : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
            spherePoint = (NH j).sphereMark,
          HEq (fun j => orientedRotatedNeck (NH j) (hδ j) hδ1
              (rotation j) (hmarkH j) (side j) (horder j))
            (fun j => orientedRotatedNeck (N j) (hδ j) hδ1
              (rotation j) (hmark j) (side j) (horder j)) ∧
          ∀ j, HEq (orientedRotatedNeck (NH j) (hδ j) hδ1
              (rotation j) (hmarkH j) (side j) (horder j))
            (orientedRotatedNeck (N j) (hδ j) hδ1
              (rotation j) (hmark j) (side j) (horder j)) := by
    change ∃ (NH : ∀ j, NormalizedNeck (H.coreEvent i).toMetricCutCapEvent.terminal.metric
          (δOriginal j) (kOriginal j)),
        HEq NH N ∧ (∀ j, HEq (NH j) (N j)) ∧
        (∀ j, (NH j).scale = (N j).scale) ∧
        ∃ hmarkH : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
            spherePoint = (NH j).sphereMark,
          HEq (fun j => orientedRotatedNeck (NH j) (hδ j) hδ1
              (rotation j) (hmarkH j) (side j) (horder j))
            (fun j => orientedRotatedNeck (N j) (hδ j) hδ1
              (rotation j) (hmark j) (side j) (horder j)) ∧
          ∀ j, HEq (orientedRotatedNeck (NH j) (hδ j) hδ1
              (rotation j) (hmarkH j) (side j) (horder j))
            (orientedRotatedNeck (N j) (hδ j) hδ1
              (rotation j) (hmark j) (side j) (horder j))
    rw [heq]
    exact ⟨N, HEq.rfl, fun _ => HEq.rfl, fun _ => rfl,
      hmark, HEq.rfl, fun _ => HEq.rfl⟩
  obtain ⟨NH, hNH, hNHpoint, hNHscale, hmarkH, hhigh, hhighpoint⟩ := hdata
  refine ⟨NH, fun j => orientedRotatedNeck (NH j) (hδ j) hδ1
    (rotation j) (hmarkH j) (side j) (horder j), hNH, hNHpoint, hNHscale,
    hmarkH, fun _ => rfl, hhigh, hhighpoint, ?_⟩
  intro r hB j
  obtain ⟨B⟩ := hB j
  exact ⟨B.orientedRotatedNeck (hδ j) hδ1 (rotation j) (hmarkH j) (side j) (horder j)⟩

private theorem exists_record_from_original_backward
    {P₀ P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory P₀} {i : Fin H.eventCount}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hP : H.stage i.castSucc = P) (hQ : H.stage i.succ = Q)
    (ha : H.time i.castSucc = a) (hs : H.time i.succ = s)
    {p : CutoffParameters} {δ r : ℝ} {k : ℕ}
    (F : PreparedCutoffEventGeometry E p δ r k)
    (hE : HEq (H.coreEvent i) (E.toRetainedCoreEvent F.old_eq_retained))
    (hδ : δ ≤ p.delta s)
    (hk : max (p.modelOrder + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ k)
    (hr : r < (p.delta s) ^ 2 * p.neckRadius s)
    {n : ℕ} (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
    (N : ∀ j, NormalizedNeck E.terminal.metric (δOriginal j) (kOriginal j))
    (hδOrig : ∀ j, δOriginal j ≤ δ) (hδ1 : δ < 1)
    (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
      spherePoint = (N j).sphereMark) (side : Fin n → Bool)
    (horder : ∀ j, k ≤ kOriginal j)
    (e : Fin n ≃ E.transition.trace.tubes.Index)
    (hneck : ∀ j, F.neck (e j) = orientedRotatedNeck (N j) (hδOrig j) hδ1
      (rotation j) (hmark j) (side j) (horder j)) :
    ∃ (NH : ∀ j, NormalizedNeck (H.toHistory.event i).terminal.metric (δOriginal j) (kOriginal j))
      (hmarkH : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
        spherePoint = (NH j).sphereMark)
      (Nrecord : (H.toHistory.event i).transition.trace.tubes.Index →
        NormalizedNeck (H.toHistory.event i).terminal.metric δ k)
      (eOriginal : Fin n ≃ (H.toHistory.event i).transition.trace.tubes.Index),
      HEq NH N ∧ (∀ j, (NH j).scale = (N j).scale) ∧
      (∀ j, Nrecord (eOriginal j) = orientedRotatedNeck (NH j) (hδOrig j) hδ1
        (rotation j) (hmarkH j) (side j) (horder j)) ∧
      (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
        (H.toHistory.event i).transition.trace.tubes.tube j z =
          ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
      ((∀ j, Nonempty (IncomingBackwardNeck H.toHistory i (NH j) r)) →
        Nonempty (GeometricCutoffRecord H.toHistory i p)) := by
  obtain ⟨NH, NHhigh, hNH, hNHpoint, hNHscale, hmarkH, hhighDef,
    hNHhigh, hNHhighpoint, hback⟩ := exists_original_backward_transfer
    E hP hQ ha hs F.old_eq_retained hE N hδOrig hδ1 rotation hmark side horder
  obtain ⟨FH, er, hNr⟩ := F.exists_of_retainedEvent_heq (H.coreEvent i) hP hQ ha hs hE
  let eOriginal := e.trans er.symm
  have hrecord (j) : FH.neck j = NHhigh (e.symm (er j)) := by
    let z := e.symm (er j)
    have hh : HEq (FH.neck j) (F.neck (e z)) := by
      simpa only [z, e.apply_symm_apply] using hNr j
    exact eq_of_heq (hh.trans ((heq_of_eq (hneck z)).trans (hNHhighpoint z).symm))
  refine ⟨NH, hmarkH, FH.neck, eOriginal, hNH, hNHscale, ?_, FH.tube_eq, ?_⟩
  · intro j
    rw [hrecord]
    have hind : e.symm (er (eOriginal j)) = j := by simp [eOriginal]
    exact (congrArg NHhigh hind).trans (hhighDef j)
  · intro hB
    apply geometricCutoffRecord_of_preparedEventGeometry FH
      (by simpa only [hs] using hδ) hk (by simpa only [hs] using hr)
    intro j
    rw [hrecord]
    exact Classical.choice (hback r hB (e.symm (er j)))

end

section

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem exists_append_metricCutCapEvent
    {P : OrientedThreeStage.{u}} {g : P.Metric} (H : RetainedCoreHistory P)
    (A : InitialIdentification P g H.toHistory)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    ∃ (K : RetainedCoreHistory P) (B : InitialIdentification P g K.toHistory),
      A.IsPrefixOf B ∧ K.horizon = s ∧ K.eventCount = H.eventCount + 1 ∧
      K.time (Fin.last K.eventCount) = s ∧ K.stage (Fin.last K.eventCount) = Q ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      ∃ i : Fin K.eventCount, i.val = H.eventCount ∧
        K.stage i.castSucc = H.stage (Fin.last H.eventCount) ∧
        K.time i.castSucc = H.time (Fin.last H.eventCount) ∧
        K.stage i.succ = Q ∧ K.time i.succ = s ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        K = H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit := by
  let F := E.toRetainedCoreEvent hOld
  let K := H.appendEvent E.incoming.lt F hinit
  have hprefix : H.toHistory.IsPrefixOf K.toHistory :=
    H.appendEvent_isPrefixOf E.incoming.lt F hinit (htime ▸ E.incoming.lt)
      (H.appendEventCompatible_of_time_eq_horizon F htime)
  have hstage : K.toHistory.stage 0 = H.toHistory.stage 0 :=
    H.appendEvent_stage_castSucc E.incoming.lt F hinit 0
  have hmetric : HEq (K.toHistory.initialMetric 0) (H.toHistory.initialMetric 0) :=
    H.appendEvent_initialMetric_castSucc_heq E.incoming.lt F hinit 0
  let B := A.of_stageZero hstage hmetric
  refine ⟨K, B, ⟨hprefix, (A.map_of_stageZero_heq hstage hmetric).symm⟩,
    rfl, rfl, H.appendEvent_time_last E.incoming.lt F hinit,
    H.appendEvent_stage_last E.incoming.lt F hinit,
    H.appendEvent_initialMetric_last_heq E.incoming.lt F hinit,
    Fin.last H.eventCount, rfl,
    H.appendEvent_stage_castSucc E.incoming.lt F hinit (Fin.last H.eventCount),
    H.appendEvent_time_castSucc E.incoming.lt F hinit (Fin.last H.eventCount),
    H.appendEvent_stage_last E.incoming.lt F hinit,
    H.appendEvent_time_last E.incoming.lt F hinit, ?_, rfl⟩
  change HEq ((H.appendEvent E.incoming.lt F hinit).coreEvent (Fin.last H.eventCount)) F
  refine (heq_of_eq (H.appendEvent_coreEvent_last E.incoming.lt F hinit)).trans ?_
  change HEq (H.extendCoreEventLast F) F
  unfold RetainedCoreHistory.extendCoreEventLast
  have transport_heq {P₁ Q₁ P₂ Q₂ : OrientedThreeStage.{u}} {a₁ s₁ a₂ s₂ : ℝ}
      (hP : P₁ = P₂) (hQ : Q₁ = Q₂) (ha : a₁ = a₂) (hs : s₁ = s₂)
      (D : RetainedCoreEvent P₁ Q₁ a₁ s₁) :
      HEq (RetainedCoreEvent.transport hP hQ ha hs D) D := by
    cases hP
    cases hQ
    cases ha
    cases hs
    exact HEq.rfl
  exact transport_heq _ _ _ _ F


theorem exists_uniform_horn_cutoff_history_extension :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ε₀ ∧
    ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
      (H : RetainedCoreHistory P₀) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
      ∀ (D : OneStepIncoming.{u}), H.stage (Fin.last H.eventCount) = D.stage →
      H.time (Fin.last H.eventCount) = D.startTime →
      HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)) →
      ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ ε₀ →
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory P₀) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters) (Q : ℝ)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dcap ∧ parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        ((∀ j, Nonempty (IncomingBackwardNeck K.toHistory i (NOriginal j) (Real.sqrt Q⁻¹))) →
          Nonempty (GeometricCutoffRecord K.toHistory i parameters)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
  classical
  obtain ⟨c, hc, A, hA, hfamily⟩ := exists_prepared_horn_cutoff_event.{u}
  refine ⟨StaticCapScaffold.ofCollarLength A hA, c, hc, ?_⟩
  intro Dcap hDcap m accuracy haccuracy
  obtain ⟨δ, hδ, hδ1, ε₀, hε₀, hmake⟩ := hfamily Dcap hDcap m accuracy haccuracy
  refine ⟨δ, ε₀, hδ, hδ1, hε₀, ?_⟩
  intro P₀ g₀ H initial htime D hstage hstart hinit ε Λ P hε
  obtain ⟨Qout, E, p, Q, N, hQ, hG, hL, hOld, hBoundary,
    hpδ, hpR, hpρ, hpFixed, hpM, hpD, hpAcc, hpC, hr, hvol, hcap,
    geometry, hgeometry, n, δOrig, kOrig, NOrig, hδOrig, rotation, hmark,
    side, horder, hδ1', e, hscale, hneck⟩ := hmake P hε
  have hext : ∃ (K : RetainedCoreHistory P₀) (B : InitialIdentification P₀ g₀ K.toHistory),
      initial.IsPrefixOf B ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
      K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      ∃ i : Fin K.eventCount, i.val = H.eventCount ∧
        K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        ∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial := by
    cases D with
    | mk stage startTime endTime hnonneg hlt slab terminal singular params =>
      cases hstage
      cases hstart
      have hinitE : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) := by
        rw [hG]
        exact eq_of_heq hinit
      obtain ⟨K, B, hpref, hhor, hcount, htimeLast, hstageLast, hmetricLast,
        i, hi, hsource, hsourceTime, htarget, htargetTime, hEvent, hK⟩ :=
        exists_append_metricCutCapEvent H initial htime E hOld hinitE
      exact ⟨K, B, hpref, hhor, hcount, htimeLast, hstageLast, hmetricLast,
        i, hi, hsource, hsourceTime, htarget, htargetTime, hEvent,
        E, hOld, hinitE, HEq.rfl, hK⟩
  obtain ⟨K, B, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    i, hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend⟩ := hext
  have hdelta : δ ≤ p.delta D.endTime := by rw [hpδ]
  have hk : max (p.modelOrder + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤
      max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) := by rw [hpM]
  obtain ⟨NOrigH, hmarkH, Nrecord, eOriginal, hNOrigH, hscaleH, hNrecord, hTube, hrecord⟩ :=
    exists_record_from_original_backward
    E hsrc hout hsrcTime houtTime geometry hEvent hdelta hk hr
    δOrig kOrig NOrig hδOrig hδ1' rotation hmark side horder e hneck
  exact ⟨Qout, E, hOld, K, B, i, p, Q, n, δOrig, kOrig, NOrigH,
    hδOrig, rotation, hmarkH, side, horder, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC, hpM, hpD, hpAcc,
    (by simpa only [hOld] using geometry.protected_interior), geometry.retained_meets_protected,
    fun j => (hscaleH j).trans (hscale j), hNrecord, hTube, hrecord, hvol, hcap⟩

theorem exists_neckRadius_horn_cutoff_history_extension :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
      (H : RetainedCoreHistory P₀) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
      ∀ (D : OneStepIncoming.{u}), H.stage (Fin.last H.eventCount) = D.stage →
      H.time (Fin.last H.eventCount) = D.startTime →
      HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)) →
      ∃ (ρ : ℝ → ℝ) (_ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory P₀) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters) (Q : ℝ)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => D.parameters.delta D.endTime * ρ D.endTime) ∧
        parameters.neckRadius = (fun _ => ρ D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dcap ∧ parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        ((∀ j, Nonempty (IncomingBackwardNeck K.toHistory i (NOriginal j) (Real.sqrt Q⁻¹))) →
          Nonempty (GeometricCutoffRecord K.toHistory i parameters)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
  obtain ⟨fixed, recenterConstant, hconstant, hfamily⟩ :=
    exists_uniform_horn_cutoff_history_extension.{u}
  refine ⟨fixed, recenterConstant, hconstant, ?_⟩
  intro Dcap hDcap m accuracy haccuracy
  obtain ⟨δ, ε₀, hδ, hδ1, hε₀, hfactory⟩ := hfamily Dcap hDcap m accuracy haccuracy
  obtain ⟨Λ, hΛ, hpresentation⟩ := OneStepIncoming.exists_neckRadius_terminalCorePresentation hε₀
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro P₀ g₀ H initial htime D hstage hstart hinit
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, _, hprotect, P, hradius, _⟩ := hpresentation D
  obtain ⟨Qout, E, hOld, K, B, i, p, Q, n, δOrig, kOrig, NOrig,
    hδOrig, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hbfr, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpConstant, hpM, hpD, hpAcc,
    hprotected, hretained, hscale, hNrecord, hTube, hrecord, hvol, hcap⟩ :=
    hfactory H initial htime (D.withNeckRadius ρ hρ) hstage hstart hinit P le_rfl
  have hpRadius : p.protectedRadius = (fun _ => D.parameters.delta D.endTime * ρ D.endTime) :=
    hpR.trans (congrArg (fun r : ℝ => fun _ : ℝ => r) hradius)
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, hprotect, Qout, E, hOld, K, B, i, p,
    Q, n, δOrig, kOrig, NOrig, hδOrig, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hbfr, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric, hi, hsrc,
    hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpRadius, hpρ, hpFixed, hpConstant, hpM, hpD, hpAcc,
    hprotected, ?_, hretained, hscale, hNrecord, hTube, hrecord, hvol, hcap⟩
  intro x hx
  apply hprotected
  apply hx.trans
  rw [hpRadius]
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hr : 0 < D.parameters.delta D.endTime * ρ D.endTime :=
    mul_pos (D.parameters.delta_pos _ hs) (hρ _ hs)
  apply inv_anti₀ (sq_pos_of_pos hr)
  have hp := D.parameters.protectedRadius_pos D.endTime hs
  nlinarith

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
