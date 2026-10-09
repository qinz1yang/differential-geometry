import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventVolumeRecord_S14
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

private local instance sigmaCompactTRO4_S14 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- VB-B: every actual event carrying a `GeometricCutoffRecord` does not increase volume: the output
stage volume is at most the terminal-limit volume of a compact set of the terminal regular open
set.  No smallness hypothesis on `δ` is needed: the static cap is `1`-Lipschitz-collapsed from the
removed band (`StaticCapWitness.collapse_length`). -/
theorem event_volume_le_compact_S14 {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (R : GeometricCutoffRecord H i parameters) :
    ∃ K : Set (H.event i).incoming.terminalRegularOpen, IsCompact K ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ ≤
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric K := by
  classical
  have : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
  have hLC : LocallyPathConnectedSpace (H.stage i.castSucc).Carrier :=
    DifferentialGeometry.Topology.ThreeManifold.Surgery.originalModel_locallyPathConnected ThreeModel (by simp [ThreeSpace])
  obtain ⟨T, hTvol, hT⟩ := offTube_image_S14 (H.event i)
  let X := (H.event i).incoming.terminalRegularOpen
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have : Finite (H.event i).RetainedBoundaryIndex := by
    have : Finite (H.event i).transition.trace.tubes.Index := inferInstance
    infer_instance
  let W₁ : Set X := {y | y.1 ∈ offTubeRetained_S14 (H.event i)}
  let B : Set X := ⋃ b, band_S14 R b
  let K : Set X := range (H.event i).oldTerminal ∪ B
  have hold : CompactSpace (H.event i).old := isCompact_iff_compactSpace.mp (H.event i).old_compact
  have hKc : IsCompact K :=
    (isCompact_range (H.event i).oldTerminal.continuous).union
      (isCompact_iUnion fun b => isCompact_band_S14 R b)
  refine ⟨K, hKc, ?_⟩
  -- covering
  have hcov : (univ : Set (H.stage i.succ).Carrier) ⊆ T ∪ ⋃ b, (R.static b).inclusion ''
      ((R.static b).witness.collapse '' capBandDom_S14 (R.static b)) := by
    intro q _
    rcases cover_S14 R q with ⟨z, hz, rfl⟩ | ⟨b, hb⟩
    · exact Or.inl (hT z hz)
    · exact Or.inr (mem_iUnion.mpr ⟨b, hb⟩)
  have h1 : riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ ≤
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric T +
        ∑' b : (H.event i).RetainedBoundaryIndex,
          riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric
            ((R.static b).inclusion '' ((R.static b).witness.collapse '' capBandDom_S14 (R.static b))) :=
    (measure_mono hcov).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (measure_iUnion_le _)))
  have h2 : ∑' b : (H.event i).RetainedBoundaryIndex,
        riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric
          ((R.static b).inclusion '' ((R.static b).witness.collapse '' capBandDom_S14 (R.static b))) ≤
      ∑' b : (H.event i).RetainedBoundaryIndex,
        riemannianVolumeMeasure ThreeModel X (H.event i).terminal.metric (band_S14 R b) :=
    ENNReal.tsum_le_tsum fun b => collapse_volume_le_band_S14 (R.static b)
  have hBmeas : ∀ b, MeasurableSet (band_S14 R b) := fun b =>
    (isCompact_band_S14 R b).isClosed.measurableSet
  have hW₁ : MeasurableSet W₁ :=
    ((isOpen_offTubeRetained_S14 (H.event i)).preimage continuous_subtype_val).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint fun b => band_S14 R b) := fun b b' hne =>
    band_disjoint_S14 R hne
  have hBm : MeasurableSet B := MeasurableSet.iUnion hBmeas
  have hWB : Disjoint W₁ B := by
    rw [Set.disjoint_left]
    intro y hy hyB
    obtain ⟨b, q, hq, rfl⟩ := mem_iUnion.mp hyB
    exact band_not_offTube_S14 R b q hq hy
  have h3 : riemannianVolumeMeasure ThreeModel X (H.event i).terminal.metric W₁ +
        ∑' b, riemannianVolumeMeasure ThreeModel X (H.event i).terminal.metric (band_S14 R b) =
      riemannianVolumeMeasure ThreeModel X (H.event i).terminal.metric (W₁ ∪ B) := by
    rw [measure_union hWB hBm, measure_iUnion hdisj hBmeas]
  have hsub : W₁ ∪ B ⊆ K := by
    refine union_subset_union_left _ ?_
    intro y hy
    obtain ⟨z, hz, hze⟩ := offTubeRetained_subset_old_S14 (H.event i) hy
    exact ⟨⟨z, hz⟩, Subtype.ext (by rw [(H.event i).oldTerminal_eq]; exact hze)⟩
  calc _ ≤ _ := h1
    _ ≤ riemannianVolumeMeasure ThreeModel X (H.event i).terminal.metric W₁ +
        ∑' b, riemannianVolumeMeasure ThreeModel X (H.event i).terminal.metric (band_S14 R b) :=
      add_le_add hTvol h2
    _ = _ := h3
    _ ≤ _ := measure_mono hsub

end GC.LongTime.Ch12
