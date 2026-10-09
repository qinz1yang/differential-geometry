import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OpenCoreSubmanifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffGeometryReduction
import DifferentialGeometry.Geometry.Curvature.EmbeddingIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteStaticCapInclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedMetricCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricRetainedCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricScalarLower

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_regularCrossing_of_not_mem_cap
    (hOld : E.old = E.transition.trace.retainedCore) (q : Q.Carrier)
    (hq : ∀ b : E.transition.trace.tubes.Boundary,
      E.transition.trace.presentation.symm (Sum.inl q) ∉ range (E.transition.trace.capping.cap b)) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core :=
    E.transition.coreCharts
  let _ : IsManifold (𝓡∂ 3) ∞ E.transition.trace.tubes.core := E.transition.coreSmooth
  let _ : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  have hcover := Set.ext_iff.mp E.transition.trace.capping.exhaustive
    (E.transition.trace.presentation.symm (Sum.inl q)) |>.mpr (mem_univ _)
  have hcore : E.transition.trace.presentation.symm (Sum.inl q) ∈ range
    E.transition.trace.capping.coreInclusion := by
    rcases hcover with h | h
    · exact h
    · obtain ⟨b, hb⟩ := mem_iUnion.mp h
      exact (hq b hb).elim
  obtain ⟨x, hx⟩ := hcore
  have hpres : E.transition.trace.presentation (E.transition.trace.capping.coreInclusion x) =
    Sum.inl q := by
    rw [hx, Homeomorph.apply_symm_apply]
  have hxret : x ∈ E.transition.trace.retainedCore := ⟨q, hpres⟩
  have hxint : (𝓡∂ 3).IsInteriorPoint x := by
    apply ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
    intro hb
    change x ∈ (𝓡∂ 3).boundary E.transition.trace.tubes.core at hb
    rw [E.transition.core_boundary] at hb
    obtain ⟨b, z, hzx⟩ := mem_iUnion.mp hb
    apply hq b
    refine ⟨sphereToThreeBall ((E.transition.attaching b).symm z), ?_⟩
    rw [E.transition.trace.capping.boundary_eq]
    have ha : E.transition.trace.capping.attaching b ((E.transition.attaching b).symm z) = z := by
      rw [← E.transition.attaching_eq]
      exact (E.transition.attaching b).apply_symm_apply z
    rw [ha, hzx]
    exact hx
  have hnhds : E.transition.trace.retainedCore ∈ 𝓝 x :=
    E.transition.trace.retainedCore_isOpen.mem_nhds hxret
  have himage : (Subtype.val : E.transition.trace.tubes.core → P.Carrier) ''
      E.transition.trace.retainedCore ∈ 𝓝 x.val :=
    DifferentialGeometry.Topology.immersion_image_mem_nhds
      (E.transition.core_induced.isImmersion.isImmersionAt x) (by simp [ThreeSpace]) hxint hnhds
  let xo : E.old := ⟨x, hOld.symm ▸ hxret⟩
  let p := E.oldTerminal xo
  have hp : p.val ∈ interior (Subtype.val '' E.old) := by
    apply mem_interior_iff_mem_nhds.mpr
    rw [hOld, E.oldTerminal_eq]
    exact himage
  obtain ⟨y, hyp, hyint, hcross⟩ := E.exists_oldTerminal_eq_of_mem_interior_old p hp
  have hyx : y.val = x := by
    apply Subtype.ext
    have hy := congrArg Subtype.val hyp
    rw [E.oldTerminal_eq, E.oldTerminal_eq] at hy
    exact hy
  have hqeq : E.oldOutput y = q := by
    apply Sum.inl_injective
    exact (E.oldOutput_eq y).symm.trans (hyx ▸ hpres)
  exact ⟨p, hqeq ▸ hcross⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_regularCrossing_of_scalar_lt
    (hOld : E.old = E.transition.trace.retainedCore) (Qmin : ℝ)
    (hcap : ∀ (b : E.RetainedBoundaryIndex) (z : ThreeBall) (q : Q.Carrier),
      E.transition.trace.presentation (E.transition.trace.capping.cap b.val z) = Sum.inl q →
        Qmin ≤ metricScalarAt E.outputMetric q)
    (q : Q.Carrier) (hq : metricScalarAt E.outputMetric q < Qmin) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q := by
  apply E.exists_regularCrossing_of_not_mem_cap hOld q
  intro b hb
  obtain ⟨z, hz⟩ := hb
  have hpres : E.transition.trace.presentation (E.transition.trace.capping.cap b z) = Sum.inl q
    := by
    rw [hz, Homeomorph.apply_symm_apply]
  have hret : E.RetainedBoundary b := by
    rw [retainedBoundary_iff_capRetained E b]
    rcases E.transition.trace.cap_retained_or_discarded b with h | h
    · exact h
    · obtain ⟨y, hy⟩ := h z
      exact (Sum.inr_ne_inl (hy.trans hpres)).elim
  exact (not_le_of_gt hq) (hcap ⟨b, hret⟩ z q hpres)

theorem PresentedStaticCap.scalar_eq {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η : ℝ}
    {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m η b) (x : S.witness.Output) :
    metricScalarAt S.witness.metric x = metricScalarAt E.outputMetric (S.inclusion x) := by
  let _ : SigmaCompactSpace S.witness.Output := by
    let _ : SecondCountableTopology Q.Carrier := ChartedSpace.secondCountable_of_sigmaCompact
      ThreeSpace Q.Carrier
    let _ : SecondCountableTopology S.witness.Output :=
      S.inclusion_smooth.isEmbedding.secondCountableTopology
    let _ : LocallyCompactSpace S.witness.Output := ChartedSpace.locallyCompactSpace ThreeSpace
      S.witness.Output
    infer_instance
  have hloc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ S.inclusion :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv S.inclusion
      S.inclusion_smooth.contMDiff
      (fun p => (S.inclusion_smooth.isImmersion.isImmersionAt p).mfderiv_injective (by simp)) rfl
  exact (DifferentialGeometry.Geometry.Curvature.curvature_of_injective_local_isometry
    S.witness.metric E.outputMetric S.inclusion hloc S.inclusion_smooth.isEmbedding.injective
    S.inclusion_metric x).1

theorem exists_regularCrossing_of_presented_cap_scalar_lt
    (hOld : E.old = E.transition.trace.retainedCore) {fixed : StaticCapScaffold} {D : ℝ} {m :
      ℕ} {η : ℝ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m η b)
    (Qmin : ℝ)
    (hcap : ∀ (b : E.RetainedBoundaryIndex) (z : ThreeBall),
      Qmin ≤ metricScalarAt (S b).witness.metric ((S b).witness.cap z))
    (q : Q.Carrier) (hq : metricScalarAt E.outputMetric q < Qmin) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q := by
  apply E.exists_regularCrossing_of_scalar_lt hOld Qmin _ q hq
  intro b z y hy
  have hval : (S b).inclusion ((S b).witness.cap z) = y :=
    Sum.inl_injective (((S b).cap_eq z).symm.trans hy)
  have hscalar := (S b).scalar_eq E ((S b).witness.cap z)
  rw [hval] at hscalar
  exact hscalar ▸ hcap b z

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

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

theorem finiteMetricEvent_cap_output_mem_range :
    letI : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel
      finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold
      finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
    letI : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f
      hf hdisj R).1
    letI : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ
      f hf hdisj R).2
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₜ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B a hboundary) →
      ∀ (b : E.transition.trace.tubes.Boundary) (z : ThreeBall) (q : Ret),
        E.transition.trace.presentation (E.transition.trace.capping.cap b z) = Sum.inl q →
          q.val ∈ range (finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective)
            hdisj) := by
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three
    transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf
    hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f
    hf hdisj R).2
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace
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
  intro b z q hq
  have hp := congrArg (finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three
    transitionEnd_pos hδ f hf hdisj R) hq
  change (finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three
    transitionEnd_pos hδ f hf hdisj R)
    ((finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ
      f hf hdisj R).symm
      ((Capping.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj).cap b (B b z))) = _ at hp
  rw [Diffeomorph.apply_symm_apply] at hp
  change (Capping.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj).cap b (B b z) =
    q.val at hp
  have hcap := Capping.ofBufferedFiniteCaps_cap transitionEnd_pos hδ hδ1 f hf hdisj b (B b z)
  exact ⟨_, hcap.symm.trans hp⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold.Attachment
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

private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

theorem finiteMetricCutCapEvent_cap_scalar_lower_of_prepared_metric :
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
      (a : (ι × Bool) → Sphere 2 ≃ₜ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B a hboundary) →
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
        ∀ Qmin : ℝ,
        (∀ b : Bidx, ∀ x ∈ range (w b).data.capMap,
          metricScalarAt E.terminal.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) / 2 ≤
            metricScalarAt (w b).data.outMetric x) →
        (∀ b : Bidx, Qmin ≤ metricScalarAt E.terminal.metric ((d₀ b.val.1).offsetPoint
          (cuttingSign_sq b.val.2))) →
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ (b : E.transition.trace.tubes.Boundary) (z : ThreeBall) (q : Ret),
          E.transition.trace.presentation (E.transition.trace.capping.cap b z) = Sum.inl q →
            Qmin / 2 ≤ metricScalarAt E.outputMetric q := by
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three
    transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf
    hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f
    hf hdisj R).2
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec
    d hmap hside w Qmin hlower hscale hOutput b z q hq
  have hcap := finiteMetricEvent_cap_output_mem_range hδ hδ1 f hf hdisj hs R o hnontrivial
    oQ oRet oDisc E B a hboundary hDisc hCap htrace b z q hq
  rw [hOutput]
  exact finiteFullPreparedMetric_cap_scalar_lower_bound_of_local ThreeModel hδ f hf hdisj hs
    E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
    hOriginal hrec d hmap hside w Qmin hlower hscale q hcap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] threeBallChartedSpace threeBall_isManifold
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

theorem exists_finiteMetricCutCapEvent_cap_scalar_lower (fixed : StaticCapScaffold) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [CompactSpace M],
      ∀ {ι : Type} [Fintype ι] {precision : ι → ℝ}
        (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
        (f : ∀ i : ι, bufferedCylinder (precision i) → M)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (R : Set (ConnectedComponents (cutCore f))) (o : SmoothOrientation ThreeModel M)
        (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))
        {t₀ t₁ D ε : ℝ} {m : ℕ},
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      letI : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel
        finrank_threeSpace_eq_three
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₜ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B a hboundary) →
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
        (∀ b : Bidx, c * precision b.val.1 ≤ δ₀) →
        (∀ b : Bidx, 2 ≤ k' b) →
        ∀ Qmin : ℝ,
        (∀ b : Bidx, Qmin ≤ metricScalarAt E.terminal.metric ((d₀ b.val.1).offsetPoint
          (cuttingSign_sq b.val.2))) →
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          E.incoming.terminalRegularOpen E.terminal.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        (∀ (b : E.transition.trace.tubes.Boundary) (z : ThreeBall) (q : Ret),
          E.transition.trace.presentation (E.transition.trace.capping.cap b z) = Sum.inl q →
            Qmin / 2 ≤ metricScalarAt E.outputMetric q) ∧
        (E.old = E.transition.trace.retainedCore → ∀ q : Ret,
          metricScalarAt E.outputMetric q < Qmin / 2 →
            ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q) := by
  obtain ⟨δ₀, hδ₀, hhalf, hlower⟩ :=
    exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound fixed.collarLength
      fixed.collar_pos
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro M _ _ _ _ _ ι _ precision hδ hδ1 f hf hdisj hs R o hnontrivial t₀ t₁ D ε m
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel
    finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
  let Disc := finiteCapDiscarded transitionEnd_pos hδ f hf hdisj R
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three
    transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf
    hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f
    hf hdisj R).2
  dsimp only
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec
    d hmap hside w hsmall horder Qmin hscale hOutput
  have hcap := finiteMetricCutCapEvent_cap_scalar_lower_of_prepared_metric hδ hδ1 f hf hdisj hs
    R o hnontrivial
    oQ oRet oDisc E B a hboundary hDisc hCap htrace hRet c hc x₀ order d₀ hOriginal k' hrec d
      hmap hside w Qmin
    (fun b => hlower (c * precision b.val.1) (d b).precision_pos (hsmall b) (k' b) (horder b)
      E.terminal.metric ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (d b) D m ε (w b))
        hscale hOutput
  refine ⟨hcap, ?_⟩
  intro hOld q hq
  exact E.exists_regularCrossing_of_scalar_lt hOld (Qmin / 2) (fun b => hcap b.val) q hq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

def capRegion : Set Q.Carrier :=
  {q | ∃ (b : E.transition.trace.tubes.Boundary) (z : ThreeBall),
    E.transition.trace.presentation (E.transition.trace.capping.cap b z) = Sum.inl q}

@[simp] theorem mem_capRegion_iff (q : Q.Carrier) :
    q ∈ E.capRegion ↔ ∃ (b : E.transition.trace.tubes.Boundary) (z : ThreeBall),
      E.transition.trace.presentation (E.transition.trace.capping.cap b z) = Sum.inl q := Iff.rfl

theorem exists_regularCrossing_of_not_mem_capRegion
    (hOld : E.old = E.transition.trace.retainedCore) {q : Q.Carrier} (hq : q ∉ E.capRegion) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q := by
  apply E.exists_regularCrossing_of_not_mem_cap hOld q
  rintro b ⟨z, hz⟩
  exact hq ⟨b, z, by rw [hz, Homeomorph.apply_symm_apply]⟩

theorem exists_regularCrossing_of_scalar_lt_on_capRegion
    (hOld : E.old = E.transition.trace.retainedCore) {Qmin : ℝ}
    (hcap : ∀ x ∈ E.capRegion, Qmin ≤ metricScalarAt E.outputMetric x)
    {q : Q.Carrier} (hq : metricScalarAt E.outputMetric q < Qmin) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q := by
  apply E.exists_regularCrossing_of_not_mem_capRegion hOld
  exact fun hx => (not_le_of_gt hq) (hcap q hx)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section

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

variable {t₀ t₁ : ℝ} {A : ℝ} {hA : 0 < A} {D ε : ℝ} {m : ℕ}

private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

theorem finiteMetricCutCapEvent_capRegion_scalar_lower_of_prepared_metric :
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
      (a : (ι × Bool) → Sphere 2 ≃ₜ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B a hboundary) →
      ∀ (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U)
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          U)
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → U) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum g
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) A hA D m ε),
        ∀ Qmin : ℝ,
        (∀ b : Bidx, ∀ x ∈ range (w b).data.capMap,
          metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) / 2 ≤
            metricScalarAt (w b).data.outMetric x) →
        (∀ b : Bidx, Qmin ≤ metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) →
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          U g R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ q ∈ E.capRegion, Qmin / 2 ≤ metricScalarAt E.outputMetric q := by
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
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace U g hRet c hc x₀ order d₀ hOriginal k'
    hrec d hmap hside w Qmin hlower hscale hOutput q hq
  obtain ⟨b, z, hq⟩ := hq
  have hcap := finiteMetricEvent_cap_output_mem_range hδ hδ1 f hf hdisj hs R o hnontrivial
    oQ oRet oDisc E B a hboundary hDisc hCap htrace b z q hq
  rw [hOutput]
  exact finiteFullPreparedMetric_cap_scalar_lower_bound_of_local ThreeModel hδ f hf hdisj hs
    U g R hRet c hc x₀ order d₀
    hOriginal hrec d hmap hside w Qmin hlower hscale q hcap


end

section

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_finiteMetricCutCapEvent_capRegion_scalar_lower (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [CompactSpace M],
      ∀ {ι : Type} [Fintype ι] {precision : ι → ℝ}
        (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
        (f : ∀ i : ι, bufferedCylinder (precision i) → M)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (R : Set (ConnectedComponents (cutCore f))) (o : SmoothOrientation ThreeModel M)
        (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))
        {t₀ t₁ D ε : ℝ} {m : ℕ},
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₜ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B a hboundary) →
      ∀ (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U)
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          U)
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → U) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum g
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) A hA D m ε),
        (∀ b : Bidx, c * precision b.val.1 ≤ δ₀) →
        (∀ b : Bidx, 2 ≤ k' b) →
        ∀ Qmin : ℝ,
        (∀ b : Bidx, Qmin ≤ metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) →
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          U g R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ q ∈ E.capRegion, Qmin / 2 ≤ metricScalarAt E.outputMetric q := by
  obtain ⟨δ₀, hδ₀, hhalf, hlower⟩ :=
    exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound A hA
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro M _ _ _ _ _ ι _ precision hδ hδ1 f hf hdisj hs R o hnontrivial t₀ t₁ D ε m
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
  dsimp only
  intro oQ oRet oDisc E B a hboundary hDisc hCap htrace U g hRet c hc x₀ order d₀
    hOriginal k' hrec d hmap hside w hsmall horder Qmin hscale hOutput
  exact finiteMetricCutCapEvent_capRegion_scalar_lower_of_prepared_metric
    hδ hδ1 f hf hdisj hs R o hnontrivial oQ oRet oDisc E B a hboundary hDisc hCap htrace
    U g hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w Qmin
    (fun b => hlower (c * precision b.val.1) (d b).precision_pos (hsmall b) (k' b) (horder b)
      g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (d b) D m ε (w b)) hscale hOutput

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section

theorem exists_metricCutCapEvent_capRegion_scalar_lower (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧
      ∀ {P : OrientedThreeStage.{u}},
      ∀ {ι : Type} [Fintype ι] {precision : ι → ℝ}
        (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
        (f : ∀ i : ι, bufferedCylinder (precision i) → P.Carrier)
        (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
        (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
        (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
        (R : Set (ConnectedComponents (cutCore f)))
        (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))
        {t₀ t₁ D ε : ℝ} {m : ℕ},
      let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
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
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (E : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁)
      (B : (ι × Bool) → ThreeBall ≃ₜ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₜ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
          hnontrivial).reparametrizeCaps B a hboundary) →
      ∀ (U : Opens P.Carrier) (g : SmoothRiemannianMetric ThreeModel U)
        (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R)
          U)
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → U) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum g
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) A hA D m ε),
        (∀ b : Bidx, c * precision b.val.1 ≤ δ₀) →
        (∀ b : Bidx, 2 ≤ k' b) →
        ∀ Qmin : ℝ,
        (∀ b : Bidx, Qmin ≤ metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) →
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          U g R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ q ∈ E.capRegion, Qmin / 2 ≤ metricScalarAt E.outputMetric q := by
  choose δ₀ hδ₀ hhalf hmake using exists_finiteMetricCutCapEvent_capRegion_scalar_lower A hA
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro P
  rw [← P.ofSmoothOrientation_smoothOrientation]
  intro ι _ precision hδ hδ1 f hf hdisj hs R hnontrivial t₀ t₁ D ε m
  exact hmake hδ hδ1 f hf hdisj hs R P.smoothOrientation hnontrivial

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem isInteriorPoint_of_oldOutput_not_mem_capRegion
    (hOld : E.old = E.transition.trace.retainedCore) (z : E.old)
    (hz : E.oldOutput z ∉ E.capRegion) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    (𝓡∂ 3).IsInteriorPoint z := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  obtain ⟨p, w, hw, _, hweq⟩ := E.exists_regularCrossing_of_not_mem_capRegion hOld hz
  have heq : w = z := E.oldOutput_injective hweq
  exact heq ▸ hw

theorem oldOutput_mem_capRegion_of_not_isInteriorPoint
    (hOld : E.old = E.transition.trace.retainedCore) (z : E.old) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    ¬ (𝓡∂ 3).IsInteriorPoint z → E.oldOutput z ∈ E.capRegion := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  intro hz
  by_contra hnot
  exact hz (E.isInteriorPoint_of_oldOutput_not_mem_capRegion hOld z hnot)


theorem exists_retained_cap_of_not_isInteriorPoint
    (hOld : E.old = E.transition.trace.retainedCore) (z : E.old) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    ¬ (𝓡∂ 3).IsInteriorPoint z →
      ∃ (b : E.RetainedBoundaryIndex) (x : ThreeBall),
        E.transition.trace.presentation (E.transition.trace.capping.cap b.val x) = Sum.inl (E.oldOutput z) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  intro hz
  obtain ⟨b, x, hx⟩ := E.oldOutput_mem_capRegion_of_not_isInteriorPoint hOld z hz
  have hret : E.RetainedBoundary b := by
    rw [retainedBoundary_iff_capRetained]
    rcases E.transition.trace.cap_retained_or_discarded b with h | h
    · exact h
    · obtain ⟨d, hd⟩ := h x
      exact (Sum.inr_ne_inl (hd.trans hx)).elim
  exact ⟨⟨b, hret⟩, x, hx⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_regularCrossing_or_cap
    (hOld : E.old = E.transition.trace.retainedCore) (q : Q.Carrier) :
    (∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q) ∨
      ∃ (b : E.RetainedBoundaryIndex) (z : ThreeBall),
        E.transition.trace.presentation (E.transition.trace.capping.cap b.val z) = Sum.inl q := by
  by_cases hcap : q ∈ E.capRegion
  · obtain ⟨b, z, hb⟩ := hcap
    have hret : E.RetainedBoundary b := by
      rw [E.retainedBoundary_iff_capRetained b]
      rcases E.transition.trace.cap_retained_or_discarded b with h | h
      · exact h
      · obtain ⟨d, hd⟩ := h z
        exact (Sum.inr_ne_inl (hd.trans hb)).elim
    exact Or.inr ⟨⟨b, hret⟩, z, hb⟩
  · exact Or.inl (E.exists_regularCrossing_of_not_mem_capRegion hOld hcap)

theorem regularCrossing_or_cap_of_admissible_node
    (hOld : E.old = E.transition.trace.retainedCore) {p : P.Carrier} {q : Q.Carrier}
    (hnode : ∃ z : E.old, z.val.val = p ∧ E.oldOutput z = q) :
    E.RegularCrossing p q ∨
      ∃ (b : E.RetainedBoundaryIndex) (z : ThreeBall),
        E.transition.trace.presentation (E.transition.trace.capping.cap b.val z) = Sum.inl q := by
  rcases E.exists_regularCrossing_or_cap hOld q with ⟨x, hx⟩ | hcap
  · obtain ⟨z, hp, hq⟩ := hnode
    have hpx : p = x.val := hp.symm.trans ((E.oldOutput_eq_iff_of_regularCrossing z hx).mp hq)
    exact Or.inl (hpx.symm ▸ hx)
  · exact Or.inr hcap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
