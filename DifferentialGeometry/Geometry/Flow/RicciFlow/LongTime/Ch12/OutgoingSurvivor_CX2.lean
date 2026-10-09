import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutoffThreshold_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- Scalar matching extends to the boundary of the retained compact manifold.
This is a continuity argument from its dense manifold interior. -/
theorem old_scalar_eq_CX2 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (z : E.old) :
    metricScalarAt E.terminal.metric (E.oldTerminal z) =
      metricScalarAt E.outputMetric (E.oldOutput z) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  have heq : EqOn (fun w : E.old => metricScalarAt E.terminal.metric (E.oldTerminal w))
      (fun w : E.old => metricScalarAt E.outputMetric (E.oldOutput w))
      ((𝓡∂ 3).interior E.old) := by
    intro w hw
    exact MetricCutCapEvent.RegularCrossing.scalar_eq E
      (p := E.oldTerminal w) ⟨w, hw, (E.oldTerminal_eq w).symm, rfl⟩
  exact heq.closure
    ((metricScalar_smooth E.terminal.metric).continuous.comp E.oldTerminal_isSmoothEmbedding.contMDiff.continuous)
    ((metricScalar_smooth E.outputMetric).continuous.comp E.oldOutput.continuous)
    (ModelWithCorners.dense_interior (𝓡∂ 3) z)

/-- A regular crossing lands in the ambient interior of the retained image. -/
theorem crossing_mem_interior_oldOutput_CX2 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) {x : E.incoming.terminalRegularOpen} {y : Q.Carrier}
    (hcross : E.RegularCrossing x.val y) : y ∈ interior (range E.oldOutput) := by
  obtain ⟨F, _, _, _, hy, hFcross, _⟩ := hcross.exists_survivor_partialDiffeomorph E
  apply interior_maximal (t := F.target) ?_ F.open_target hy
  intro q hq
  obtain ⟨z, _, _, hz⟩ := hFcross (F.symm q) (F.map_target hq)
  exact ⟨z, hz.trans (F.right_inv hq)⟩

/-- The cut-neck scalar barrier excludes the frontier of the retained image
on the outgoing side too. No scalar lower bound inside an inserted cap is used. -/
theorem low_scalar_oldOutput_mem_interior_CX2
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {L : ℝ}
    (hδ : ∀ j, R.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * R.delta j) * (R.neck j).scale)
    (z : (H.event i).old)
    (hz : metricScalarAt (H.event i).outputMetric ((H.event i).oldOutput z) ≤ L) :
    (H.event i).oldOutput z ∈ interior (range (H.event i).oldOutput) := by
  let E := H.event i
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  have hscalar : metricScalarAt E.terminal.metric (E.oldTerminal z) ≤ L :=
    (old_scalar_eq_CX2 E z).trans_le hz
  have hcore := R.scalar_sublevel_mem_interior_core hδ hscale (E.oldTerminal z) hscalar
  rw [E.oldTerminal_eq] at hcore
  have hret : z.val ∈ E.transition.trace.retainedCore := by
    rw [← R.old_eq_retained]
    exact z.property
  have hint : (E.oldTerminal z).val ∈ interior (Subtype.val '' E.old) := by
    have himage : Subtype.val '' E.old = Subtype.val '' E.transition.trace.retainedCore :=
      congrArg (fun A => Subtype.val '' A) R.old_eq_retained
    rw [E.oldTerminal_eq, himage]
    exact DifferentialGeometry.Topology.mem_interior_image_val_of_isOpen
      E.transition.trace.isClopen_retainedCore.isOpen hret hcore
  obtain ⟨w, hw, _, hcross⟩ := E.exists_oldTerminal_eq_of_mem_interior_old (E.oldTerminal z) hint
  have hwz : w = z := E.oldTerminal_isSmoothEmbedding.isEmbedding.injective hw
  subst w
  exact crossing_mem_interior_oldOutput_CX2 E hcross

/-- First exit across a surgery frontier is impossible for a connected
outgoing low-scalar set anchored at one surviving point. -/
theorem outgoing_low_scalar_subset_oldInterior_CX2
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {L : ℝ}
    (hδ : ∀ j, R.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * R.delta j) * (R.neck j).scale)
    {U : Set (H.stage i.succ).Carrier} (hU : IsPreconnected U)
    (hscalar : ∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ L)
    {x : (H.event i).incoming.terminalRegularOpen} {y : (H.stage i.succ).Carrier}
    (hy : y ∈ U) (hcross : (H.event i).RegularCrossing x.val y) :
    U ⊆ interior (range (H.event i).oldOutput) := by
  apply hU.subset_of_closure_inter_subset isOpen_interior
    ⟨y, hy, crossing_mem_interior_oldOutput_CX2 (H.event i) hcross⟩
  intro q hq
  have hclosed := (H.event i).oldOutput_isClosedEmbedding.isClosed_range
  obtain ⟨z, rfl⟩ := (closure_minimal interior_subset hclosed) hq.1
  exact low_scalar_oldOutput_mem_interior_CX2 R hδ hscale z (hscalar _ hq.2)

/-- A single genuine survivor chart covers the entire outgoing low-scalar
set; its inverse supplies the compatible incoming points. -/
theorem outgoing_survivor_chart_of_nominal_threshold_CX2
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {r Λ K : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * K < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    {U : Set (H.stage i.succ).Carrier} (hU : IsPreconnected U)
    (hscalar : ∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ K / r ^ 2)
    {x : (H.event i).incoming.terminalRegularOpen} {y : (H.stage i.succ).Carrier}
    (hy : y ∈ U) (hcross : (H.event i).RegularCrossing x.val y) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      U ⊆ E.target ∧ E x = y ∧
      (∀ q ∈ U, (H.event i).RegularCrossing (E.symm q).val q) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (H.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (H.event i).terminal.metric.inner z v w := by
  have hsub := outgoing_low_scalar_subset_oldInterior_CX2 R
    (fun j => (hδ j).trans (by norm_num))
    (cutoff_threshold_of_nominal_CX2 R hr hΛ hKΛ hδ hnom) hU hscalar hy hcross
  obtain ⟨E, hsource, _, hxy, _, hEcross, hmetric⟩ :=
    hcross.exists_survivor_partialDiffeomorph (H.event i)
  have htarget : U ⊆ E.target := by
    intro q hq
    obtain ⟨z, hz⟩ := (H.event i).exists_terminal_regularCrossing_of_mem_interior_oldOutput q (hsub hq)
    obtain ⟨E', hsource', hz', _, _, _, _⟩ :=
      hz.exists_survivor_partialDiffeomorph (H.event i)
    have hzE : z ∈ E.source := by rwa [hsource, ← hsource']
    have heq : E z = q := (H.event i).regularCrossing_right_unique (hEcross z hzE) hz
    exact heq ▸ E.map_source hzE
  refine ⟨E, htarget, hxy, ?_, hmetric⟩
  intro q hq
  have hqE := htarget hq
  have hc := hEcross (E.symm q) (E.map_target hqE)
  have heq : E (E.symm q) = q := E.right_inv hqE
  exact (congrArg (fun z => (H.event i).RegularCrossing (E.symm q).val z) heq).mp hc

end GC.LongTime.Ch12
