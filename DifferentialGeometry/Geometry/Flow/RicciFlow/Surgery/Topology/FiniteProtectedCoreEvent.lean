import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedMetricCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingReparametrization
import DifferentialGeometry.Geometry.Neck.ScalarRetainedCore

noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private theorem core_eq_and_retained_image_eq_of_trace_heq
    {P Q D D' N N' : OrientedThreeStage.{u}}
    (hD : D = D') (hN : N = N')
    {T : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier}
    {T' : CutCapTopology P.Carrier Q.Carrier D'.Carrier N'.Carrier}
    (h : HEq T T') :
    T.tubes.core = T'.tubes.core ∧
    (Subtype.val : T.tubes.core → P.Carrier) '' T.retainedCore =
      (Subtype.val : T'.tubes.core → P.Carrier) '' T'.retainedCore := by
  cases hD
  cases hN
  cases eq_of_heq h
  exact ⟨rfl, rfl⟩

private theorem retained_image_eq_of_trace_heq
    {P Q D D' N N' : OrientedThreeStage.{u}}
    (hD : D = D') (hN : N = N')
    {T : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier}
    {T' : CutCapTopology P.Carrier Q.Carrier D'.Carrier N'.Carrier}
    (h : HEq T T') :
    (Subtype.val : T.tubes.core → P.Carrier) '' T.retainedCore =
      (Subtype.val : T'.tubes.core → P.Carrier) '' T'.retainedCore :=
  (core_eq_and_retained_image_eq_of_trace_heq hD hN h).2

private theorem one_retained_side_of_trace_heq
    {P Q D D' N N' : OrientedThreeStage.{u}}
    (hD : D = D') (hN : N = N')
    {T : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier}
    {T' : CutCapTopology P.Carrier Q.Carrier D'.Carrier N'.Carrier}
    (h : HEq T T')
    (hone : ∀ j : T'.tubes.Index,
      (∀ y, T'.tubes.coreBoundarySphere (j, true) y ∈ T'.retainedCore) ↔
        ¬ (∀ y, T'.tubes.coreBoundarySphere (j, false) y ∈ T'.retainedCore)) :
    ∀ j : T.tubes.Index,
      (∀ y, T.tubes.coreBoundarySphere (j, true) y ∈ T.retainedCore) ↔
        ¬ (∀ y, T.tubes.coreBoundarySphere (j, false) y ∈ T.retainedCore) := by
  cases hD
  cases hN
  cases eq_of_heq h
  exact hone

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (R : Set (ConnectedComponents (cutCore f)))
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

private local instance : LocallyPathConnectedSpace M :=
  originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three

private theorem retained_image_of_buffered_finite_caps :
    (Subtype.val : (TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).core → M) ''
      (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).retainedCore =
      (Subtype.val : cutCore f → M) '' retainedCore f R := by
  rw [CutCapTopology.ofBufferedFiniteCaps_retainedCore]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).symm p, ?_, rfl⟩
    simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hp


attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable [IsManifold ThreeModel ∞ M] [CompactSpace M]
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (o : SmoothOrientation ThreeModel M) {t₀ t₁ : ℝ}

local notation "Q" => FiniteCapQuotient hL hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "Ret" => finiteCapRetained hL hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded hL hδ f hf hdisj R

theorem finiteMetricCutCapEvent_protected_interior :
    letI : ChartedSpace ThreeSpace Q :=
      finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q :=
      finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    letI : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
    letI : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
    letI : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
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
        ((CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
          B (fun b => (a b).toHomeomorph) hboundary) →
      ∀ (x₀ : ι → E.incoming.terminalRegularOpen) (order : ι → ℕ)
        (d : ∀ i, normalizedDatum E.terminal.metric (x₀ i) (δ i) (order i)),
        (∀ i, f i = neckAmbientMap E.incoming.terminalRegularOpen (d i)) →
        (∀ i, 2 ≤ order i) → (∀ i, δ i ≤ 1 / 2) →
        ∀ K : ℝ,
        (∀ i, K < (1 - 4323 * δ i) * metricScalarAt E.terminal.metric (x₀ i)) →
        R = scalarSublevelComponents E.incoming.terminalRegularOpen E.terminal.metric f K →
        ∀ x : E.incoming.terminalRegularOpen, metricScalarAt E.terminal.metric x ≤ K →
          x.val ∈ interior ((Subtype.val : E.transition.trace.tubes.core → M) ''
            E.transition.trace.retainedCore) := by
  let : ChartedSpace ThreeSpace Q :=
    finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q :=
    finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace x₀ order d hOriginal horder hδhalf K hhigh hR x hx
  have htraceImage := retained_image_eq_of_trace_heq hDisc hCap htrace
  have himage : (Subtype.val : E.transition.trace.tubes.core → M) '' E.transition.trace.retainedCore =
      (Subtype.val : cutCore f → M) '' retainedCore f R := by
    exact htraceImage.trans (retained_image_of_buffered_finite_caps hL hδ hδ1 f hf hdisj R hnontrivial)
  rw [himage]
  have hfEq : (fun i => neckAmbientMap E.incoming.terminalRegularOpen (d i)) = f :=
    funext fun i => (hOriginal i).symm
  have hdisj' : Pairwise fun i j =>
      Disjoint (range (neckAmbientMap E.incoming.terminalRegularOpen (d i)))
        (range (neckAmbientMap E.incoming.terminalRegularOpen (d j))) := by
    intro i j hij
    rw [← hOriginal i, ← hOriginal j]
    exact hdisj hij
  have hp := scalarSublevelComponents_protected E.incoming.terminalRegularOpen E.terminal.metric
    x₀ order d horder hδhalf hdisj' K hhigh
  dsimp only at hp
  rw [hfEq, ← hR] at hp
  exact hp.1 x hx


theorem finiteMetricCutCapEvent_retained_meets_scalar_sublevel :
    letI : ChartedSpace ThreeSpace Q :=
      finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q :=
      finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    letI : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
    letI : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
    letI : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
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
        ((CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
          B (fun b => (a b).toHomeomorph) hboundary) →
      ∀ K : ℝ,
        R ⊆ scalarSublevelComponents E.incoming.terminalRegularOpen E.terminal.metric f K →
        ∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ p : E.transition.trace.tubes.core,
            ConnectedComponents.mk p = c ∧ p ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤ K := by
  let : ChartedSpace ThreeSpace Q :=
    finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q :=
    finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace K hR
  have htraceImage := retained_image_eq_of_trace_heq hDisc hCap htrace
  have himage : (Subtype.val : E.transition.trace.tubes.core → M) '' E.transition.trace.retainedCore =
      (Subtype.val : cutCore f → M) '' retainedCore f R :=
    htraceImage.trans (retained_image_of_buffered_finite_caps hL hδ hδ1 f hf hdisj R hnontrivial)
  have hcores : E.transition.trace.tubes.core = cutCore f :=
    (core_eq_and_retained_image_eq_of_trace_heq hDisc hCap htrace).1.trans
      (TubeSystem.ofBufferedCharts_core hδ hδ1 f hf hdisj)
  have himageSubset : (Subtype.val : E.transition.trace.tubes.core → M) ''
      E.transition.trace.retainedCore ⊆ (Subtype.val : cutCore f → M) ''
        retainedCore f (scalarSublevelComponents E.incoming.terminalRegularOpen
          E.terminal.metric f K) :=
    himage.subset.trans (image_mono (preimage_mono hR))
  exact retainedCore_component_meets_scalar_sublevel_of_image_subset
    E.incoming.terminalRegularOpen E.terminal.metric f K E.transition.trace.retainedCore
    hcores.symm.subset himageSubset


theorem finiteMetricCutCapEvent_one_retained_side :
    letI : ChartedSpace ThreeSpace Q :=
      finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q :=
      finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    letI : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
    letI : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
    letI : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
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
        ((CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
          B (fun b => (a b).toHomeomorph) hboundary) →
      (∀ j, cuttingSphereComponent hδ f hf hdisj (j, true) ∈ R ↔
        cuttingSphereComponent hδ f hf hdisj (j, false) ∉ R) →
      ∀ j, E.RetainedBoundary (j, true) ↔ ¬ E.RetainedBoundary (j, false) := by
  let : ChartedSpace ThreeSpace Q :=
    finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q :=
    finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace hone
  apply one_retained_side_of_trace_heq hDisc hCap htrace
  intro j
  change (∀ y, (TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere (j, true) y ∈
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).retainedCore) ↔
    ¬ (∀ y, (TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere (j, false) y ∈
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).retainedCore)
  have htrue := CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff
    hL hδ hδ1 f hf hdisj R hnontrivial (j, true)
  have hfalse := CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff
    hL hδ hδ1 f hf hdisj R hnontrivial (j, false)
  exact htrue.trans ((hone j).trans hfalse.not.symm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
