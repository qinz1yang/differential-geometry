import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffCollapseBands
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapDistance
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.LipschitzImage
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Completeness
import Mathlib.MeasureTheory.Measure.Continuity

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Measure DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

private local instance incomingTerminalSigmaCompact
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

private theorem compact_collapseBandOutput_volume_le
    (b : (H.event i).RetainedBoundaryIndex) (n : ℕ) :
    riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric
        (G.collapseBandOutput b '' (G.static b).witness.compactBandParameters n) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric
        ((G.static b).witness.collapseBandSource ''
          (G.static b).witness.compactBandParameters n) := by
  let S := G.static b
  let w := S.witness
  let c : neckCentralDomain S.delta → (H.event i).incoming.terminalRegularOpen :=
    fun x => S.neck.chart x.val
  have hchart : _root_.Topology.IsOpenEmbedding S.neck.chart :=
    DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
      S.neck.chart S.neck.chart_smooth.contMDiff S.neck.chart_smooth.isEmbedding.injective
      (fun z => DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
        NeckCylinderModel ThreeModel S.neck.chart z
        (S.neck.chart_smooth.isImmersion.isImmersionAt z))
      (by simp [Module.finrank_prod, ThreeSpace])
  have hc : _root_.Topology.IsOpenEmbedding c :=
    hchart.comp (isOpen_neckCentralDomain S.delta).isOpenEmbedding_subtypeVal
  let U : Opens (H.event i).incoming.terminalRegularOpen := ⟨range c, hc.isOpen_range⟩
  let e : neckCentralDomain S.delta ≃ₜ U := hc.isEmbedding.toHomeomorph
  let κ : C(w.CollapseBandDomain, U) :=
    (⟨e, e.continuous⟩ : C(neckCentralDomain S.delta, U)).comp w.collapseBandParameter
  let F : C(U, (H.stage i.succ).Carrier) :=
    S.inclusion.comp (w.collapse.comp
      (⟨e.symm, e.symm.continuous⟩ : C(U, neckCentralDomain S.delta)))
  let : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.event i).incoming.terminalRegularOpen.isOpen)
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  let : MeasurableSpace (H.event i).incoming.terminalRegularOpen :=
    borel (H.event i).incoming.terminalRegularOpen
  let : BorelSpace (H.event i).incoming.terminalRegularOpen := ⟨rfl⟩
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have he (x : neckCentralDomain S.delta) : (e x).val = c x := rfl
  have hesymm (x : U) : c (e.symm x) = x.val :=
    (he (e.symm x)).symm.trans (congrArg Subtype.val (e.apply_symm_apply x))
  have hκ (x : w.CollapseBandDomain) : (κ x).val = w.collapseBandSource x :=
    he (w.collapseBandParameter x)
  have hFκ (x : w.CollapseBandDomain) : F (κ x) = G.collapseBandOutput b x := by
    change S.inclusion (w.collapse (e.symm (e (w.collapseBandParameter x)))) = _
    rw [e.symm_apply_apply]
    rfl
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ S.inclusion :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      S.inclusion S.inclusion_smooth.contMDiff
      (fun x => (S.inclusion_smooth.isImmersion.isImmersionAt x).mfderiv_injective
        (by simp)) rfl
  have hinc (x y : w.Output) :
      riemannianEDistOf (H.event i).outputMetric (S.inclusion x) (S.inclusion y) ≤
        riemannianEDistOf w.metric x y := by
    have h := edistOf_le_of_quad_of_localDiffeomorph w.metric (H.event i).outputMetric
      S.inclusion hlocal (c := 1) zero_lt_one
      (fun z v => by rw [← S.inclusion_metric, one_mul]) x y
    simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h
  have hshort (p : U) : ∃ V ∈ 𝓝 p, ∀ y ∈ V, ∀ z ∈ V,
      riemannianEDistOf (H.event i).outputMetric (F y) (F z) ≤
        riemannianEDistOf ((H.event i).terminal.metric.restrictOpen U) y z := by
    obtain ⟨V, hV, hbound⟩ := w.exists_mem_nhds_collapse_riemannianEDistOf_le (e.symm p)
    refine ⟨e.symm ⁻¹' V, e.symm.continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
    intro y hy z hz
    calc
      _ ≤ riemannianEDistOf w.metric (w.collapse (e.symm y))
          (w.collapse (e.symm z)) := hinc _ _
      _ ≤ riemannianEDistOf (H.event i).terminal.metric
          (c (e.symm y)) (c (e.symm z)) := hbound _ hy _ hz
      _ = riemannianEDistOf (H.event i).terminal.metric y.val z.val := by
        rw [hesymm, hesymm]
      _ ≤ _ := riemannianEDistOf_le_restrictOpen (H.event i).terminal.metric U y z
  let K : Set U := κ '' w.compactBandParameters n
  let A : Set (H.event i).incoming.terminalRegularOpen :=
    w.collapseBandSource '' w.compactBandParameters n
  have hK : IsCompact K := (w.isCompact_compactBandParameters n).image κ.continuous
  have hA : IsCompact A := w.isCompact_collapseBandSource_piece n
  have hAU : A ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact (κ x).property
  have hpre : K = (Subtype.val : U → (H.event i).incoming.terminalRegularOpen) ⁻¹' A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hκ x).symm⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext ((hκ x).trans hxy)⟩
  have himage : F '' K = G.collapseBandOutput b '' w.compactBandParameters n := by
    change F '' (κ '' w.compactBandParameters n) = _
    rw [← image_comp]
    congr 1
    exact funext hFκ
  have hvolume := riemannianVolumeMeasure_image_le_of_locally_nonexpanding
    ((H.event i).terminal.metric.restrictOpen U) (H.event i).outputMetric F hK
    (fun p _ => hshort p)
  rw [himage] at hvolume
  calc
    _ ≤ riemannianVolumeMeasure ThreeModel U
        ((H.event i).terminal.metric.restrictOpen U) K := hvolume
    _ = riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric A := by
      rw [hpre]
      exact riemannianVolumeMeasure_restrictOpen_preimage_of_subset
        (H.event i).terminal.metric U hA.measurableSet hAU

private theorem negativeCollapseImage_volume_le
    (b : (H.event i).RetainedBoundaryIndex) :
    riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric
        (G.negativeCollapseImage b) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric (G.static b).witness.negativeCollapseBand := by
  have hout : Monotone (fun n : ℕ =>
      G.collapseBandOutput b '' (G.static b).witness.compactBandParameters n) :=
    fun _ _ h => image_mono ((G.static b).witness.compactBandParameters_mono h)
  have hin : Monotone (fun n : ℕ =>
      (G.static b).witness.collapseBandSource ''
        (G.static b).witness.compactBandParameters n) :=
    fun _ _ h => image_mono ((G.static b).witness.compactBandParameters_mono h)
  rw [G.negativeCollapseImage_eq_iUnion b, hout.measure_iUnion,
    (G.static b).witness.negativeCollapseBand_eq_iUnion, hin.measure_iUnion]
  exact iSup_mono fun n => G.compact_collapseBandOutput_volume_le b n

private theorem output_eq_old_union_negativeCollapseImage :
    (univ : Set (H.stage i.succ).Carrier) =
      range (H.event i).oldOutput ∪ ⋃ b, G.negativeCollapseImage b := by
  classical
  let E := H.event i
  let : CompactSpace E.transition.trace.tubes.core := E.transition.core_compact
  let : LocallyConnectedSpace E.transition.trace.tubes.core :=
    E.transition.core_locallyConnected
  apply Subset.antisymm
  · intro q _
    let c := ConnectedComponents.mk q
    let q' : E.transition.ChildCarrier c := ⟨q, rfl⟩
    have hq : q' ∈ range (E.transition.childCoreInclusion c) ∪
        ⋃ b, range (E.transition.childCap c b) := by
      rw [E.transition.range_childCoreInclusion_union_range_childCap c]
      trivial
    rcases hq with hq | hq
    · obtain ⟨x, hx⟩ := hq
      have hxold : x.val ∈ E.old := by
        rw [show E.old = E.transition.trace.retainedCore from G.old_eq_retained]
        exact CutCapTopology.childCore_subset_retainedCore
          E.transition.trace c x.property
      have heq : E.oldOutput ⟨x.val, hxold⟩ =
          (E.transition.childCoreInclusion c x).val :=
        Sum.inl.inj ((E.oldOutput_eq ⟨x.val, hxold⟩).symm.trans
          (E.transition.childCoreInclusionFun_eq c x))
      exact Or.inl ⟨⟨x.val, hxold⟩, heq.trans (congrArg Subtype.val hx)⟩
    · obtain ⟨b, z, hz⟩ := mem_iUnion.mp hq
      let b' : E.RetainedBoundaryIndex :=
        ⟨b.val, E.transition.retainedBoundary_of_mem_childCapBoundary c b⟩
      have heq : (G.static b').inclusion ((G.static b').witness.cap z) = q :=
        (Sum.inl.inj (((G.static b').cap_eq z).symm.trans
          (E.transition.childCapFun_eq c b z))).trans (congrArg Subtype.val hz)
      rcases G.cap_range_subset_oldOutput_union_negativeCollapseImage b' ⟨z, heq⟩ with
        hold | hnegative
      · exact Or.inl hold
      · exact Or.inr (mem_iUnion.mpr ⟨b', hnegative⟩)
  · exact subset_univ _

private theorem source_volume_budget :
    riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric (range (H.event i).oldTerminal) +
      ∑' b : (H.event i).RetainedBoundaryIndex,
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric (G.static b).witness.negativeCollapseBand ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric G.collapseBandHull := by
  let : MeasurableSpace (H.event i).incoming.terminalRegularOpen :=
    borel (H.event i).incoming.terminalRegularOpen
  let : BorelSpace (H.event i).incoming.terminalRegularOpen := ⟨rfl⟩
  let μ := riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
    (H.event i).terminal.metric
  let S := fun b : (H.event i).RetainedBoundaryIndex =>
    (G.static b).witness.negativeCollapseBand
  have hS (b : (H.event i).RetainedBoundaryIndex) : MeasurableSet (S b) := by
    change MeasurableSet (G.static b).witness.negativeCollapseBand
    rw [(G.static b).witness.negativeCollapseBand_eq_iUnion]
    exact MeasurableSet.iUnion fun n =>
      ((G.static b).witness.isCompact_collapseBandSource_piece n).measurableSet
  have hd : Disjoint (range (H.event i).oldTerminal) (⋃ b, S b) :=
    disjoint_iUnion_right.mpr fun b =>
      (G.disjoint_negativeCollapseBand_oldTerminal b).symm
  change μ (range (H.event i).oldTerminal) + ∑' b, μ (S b) ≤ _
  calc
    _ = μ (range (H.event i).oldTerminal ∪ ⋃ b, S b) := by
      rw [measure_union hd (MeasurableSet.iUnion hS),
        measure_iUnion G.pairwise_disjoint_negativeCollapseBand hS]
    _ ≤ μ G.collapseBandHull := measure_mono (union_subset
      G.oldTerminal_subset_collapseBandHull
      (iUnion_subset fun b => G.negativeCollapseBand_subset_collapseBandHull b))

/-- The original output volume is bounded by the volume of the original compact
terminal hull of the retained region and collapse bands. -/
theorem volume_le_collapseBandHull :
    riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
        (H.event i).outputMetric univ ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric G.collapseBandHull := by
  let μ := riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric
  change μ univ ≤ _
  calc
    μ univ = μ (range (H.event i).oldOutput ∪ ⋃ b, G.negativeCollapseImage b) :=
      congrArg μ G.output_eq_old_union_negativeCollapseImage
    _ ≤ μ (range (H.event i).oldOutput) + μ (⋃ b, G.negativeCollapseImage b) :=
      measure_union_le _ _
    _ ≤ μ (range (H.event i).oldOutput) + ∑' b, μ (G.negativeCollapseImage b) :=
      add_le_add (le_refl _) (measure_iUnion_le _)
    _ = riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric (range (H.event i).oldTerminal) +
          ∑' b, μ (G.negativeCollapseImage b) := by
      rw [(H.event i).oldOutput_volume_eq_oldTerminal_volume]
    _ ≤ riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric (range (H.event i).oldTerminal) +
          ∑' b : (H.event i).RetainedBoundaryIndex,
            riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
              (H.event i).terminal.metric (G.static b).witness.negativeCollapseBand :=
      add_le_add (le_refl _) (ENNReal.tsum_le_tsum fun b => G.negativeCollapseImage_volume_le b)
    _ ≤ _ := G.source_volume_budget

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
