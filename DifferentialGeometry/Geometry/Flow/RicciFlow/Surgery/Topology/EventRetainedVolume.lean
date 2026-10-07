import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Analysis.Integration.Measure.NullImage
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Geometry.Measure.LocalIsometry

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Measure
open Set Manifold MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

private local instance incomingTerminalSigmaCompact
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

/-- The entire retained image has the same volume in the actual terminal and
output metrics. Boundary images have zero volume; the retained interior uses
the original event's isometric survivor map. -/
theorem oldOutput_volume_eq_oldTerminal_volume
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric (range E.oldOutput) =
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
        E.terminal.metric (range E.oldTerminal) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  let : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
  let : SigmaCompactSpace E.incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        E.incoming.terminalRegularOpen.isOpen)
  let : MeasurableSpace E.incoming.terminalRegularOpen :=
    borel E.incoming.terminalRegularOpen
  let : BorelSpace E.incoming.terminalRegularOpen := ⟨rfl⟩
  let : MeasurableSpace Q.Carrier := borel Q.Carrier
  let : BorelSpace Q.Carrier := ⟨rfl⟩
  let A : Set P.Carrier :=
    (Subtype.val : E.transition.trace.tubes.core → P.Carrier) '' E.old
  let W : Opens E.incoming.terminalRegularOpen :=
    ⟨{x | x.val ∈ interior A}, isOpen_interior.preimage continuous_subtype_val⟩
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  have hA : range (fun x : E.old => (x.val.val : P.Carrier)) = A := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmem (x : E.old) (hx : (𝓡∂ 3).IsInteriorPoint x) : E.oldTerminal x ∈ W := by
    change (E.oldTerminal x).val ∈ interior A
    rw [E.oldTerminal_eq]
    apply mem_interior_iff_mem_nhds.mpr
    have h := immersion_image_mem_nhds
      (E.old_induced.isImmersion.isImmersionAt x) rfl hx
      (s := univ) Filter.univ_mem
    simpa only [image_univ, hA] using h
  have hW : (W : Set E.incoming.terminalRegularOpen) =
      E.oldTerminal '' (𝓡∂ 3).interior E.old := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxy, hx, _⟩ := E.exists_oldTerminal_eq_of_mem_interior_old y hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact hmem x hx
  obtain ⟨F, _, hinj, hlocal, hcross, hold, hmetric⟩ :=
    E.exists_isometric_survivor_map W (fun _ hx => hx)
  have hF : range F = E.oldOutput '' (𝓡∂ 3).interior E.old := by
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨_, _, _, hregular⟩ := hcross y
      obtain ⟨x, hx, _, hxF⟩ := hregular
      exact ⟨x, hx, hxF⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨E.oldTerminal x, hmem x hx⟩, hold x (hmem x hx)⟩
  have hnullTerminal :
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
        (E.oldTerminal '' (𝓡∂ 3).boundary E.old) = 0 :=
    riemannianVolumeMeasure_image_boundary_eq_zero E.terminal.metric
      (E.oldTerminal_isSmoothEmbedding.contMDiff.mdifferentiable (by simp))
  have hnullOutput : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
      (E.oldOutput '' (𝓡∂ 3).boundary E.old) = 0 :=
    riemannianVolumeMeasure_image_boundary_eq_zero E.outputMetric
      (E.contMDiff_oldOutput.mdifferentiable (by simp))
  have hcover (X : Type u) (f : E.old → X) :
      range f = f '' (𝓡∂ 3).interior E.old ∪ f '' (𝓡∂ 3).boundary E.old := by
    rw [← image_union, ModelWithCorners.interior_union_boundary_eq_univ, image_univ]
  have hterminal :
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
          (range E.oldTerminal) =
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
          E.terminal.metric (W : Set E.incoming.terminalRegularOpen) := by
    apply le_antisymm
    · calc
        _ = riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
            E.terminal.metric ((W : Set E.incoming.terminalRegularOpen) ∪
              E.oldTerminal '' (𝓡∂ 3).boundary E.old) := by
          rw [hW, ← hcover _ E.oldTerminal]
        _ ≤ riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
              E.terminal.metric (W : Set E.incoming.terminalRegularOpen) +
            riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
              E.terminal.metric (E.oldTerminal '' (𝓡∂ 3).boundary E.old) :=
          measure_union_le _ _
        _ = _ := by rw [hnullTerminal, add_zero]
    · apply measure_mono
      rw [hW]
      exact image_subset_range _ _
  have houtput : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
      (range E.oldOutput) = riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
        (range F) := by
    apply le_antisymm
    · calc
        _ = riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
            (range F ∪ E.oldOutput '' (𝓡∂ 3).boundary E.old) := by
          rw [hF, ← hcover _ E.oldOutput]
        _ ≤ riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric (range F) +
            riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
              (E.oldOutput '' (𝓡∂ 3).boundary E.old) := measure_union_le _ _
        _ = _ := by rw [hnullOutput, add_zero]
    · apply measure_mono
      rw [hF]
      exact image_subset_range _ _
  have hvolume := riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (E.terminal.metric.restrictOpen W) E.outputMetric F hlocal hinj
    (fun x v w => (hmetric x v w).symm) MeasurableSet.univ
  rw [image_univ] at hvolume
  have hpre : (Subtype.val : W → E.incoming.terminalRegularOpen) ⁻¹'
      (W : Set E.incoming.terminalRegularOpen) = univ := by
    ext x
    exact iff_of_true x.property (mem_univ x)
  have hrestriction := riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    E.terminal.metric W W.isOpen.measurableSet (Subset.refl _)
  rw [hpre] at hrestriction
  exact houtput.trans (hvolume.symm.trans (hrestriction.trans hterminal.symm))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
