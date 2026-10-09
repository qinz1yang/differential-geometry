import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open DifferentialGeometry.Topology (ClosedOrientedManifold)

def HasControlledExtinctionWithin (M : ClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) (B : ℝ) : Prop :=
  ∃ W : PoincareControlledExtinction M g, W.time ≤ B

theorem nonempty_poincareControlledExtinction_of_hasControlledExtinctionWithin
    {M : ClosedOrientedManifold.{u} 3}
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier} {B : ℝ}
    (h : HasControlledExtinctionWithin M g B) :
    Nonempty (PoincareControlledExtinction M g) :=
  h.elim fun W _ => ⟨W⟩

theorem not_hasControlledExtinctionWithin_of_nonpos
    {M : ClosedOrientedManifold.{u} 3}
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier} {B : ℝ} (hB : B ≤ 0) :
    ¬ HasControlledExtinctionWithin M g B := by
  rintro ⟨W, hW⟩
  linarith [W.time_pos, hW, hB]

theorem hasControlledExtinctionWithin_of_observedHistory
    (P : OrientedThreeStage.{u}) (g : P.Metric) (H : ObservedHistory.{u})
    (A : InitialIdentification P g H) [Nonempty P.Carrier]
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ i : Fin H.eventCount, ∀ c : ConnectedComponents (H.event i).discarded.Carrier,
      DifferentialGeometry.Topology.isPoincareStandard
        ((H.event i).discarded.toClosedOrientedManifold.component c).Carrier)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier)
    {B : ℝ} (hB : H.time (Fin.last H.eventCount) ≤ B) :
    HasControlledExtinctionWithin P.toClosedOrientedManifold g B := by
  have hn : 0 < H.eventCount :=
    @ObservedHistory.eventCount_pos_of_final_empty H A.initial_nonempty hempty
  refine ⟨{ history := H.toSurgeryFiniteSurgeryHistoryOfCutCapCompletion hn hc hout
            time := H.time (Fin.last H.eventCount)
            time_pos := H.last_time_pos hn
            initial := A.toFiniteSurgeryHistory hn (H.toSurgeryEvents hc hout)
              (H.toSurgeryEvents_initial hc hout) (H.toSurgeryEvents_output hc hout)
            controlled := ?_
            extinct := ?_ }, hB⟩
  · intro i
    exact SphericalCutCapTransition.ofSmoothCutCapTransition_poincareControlled
      (H.event i).transition (hc i) (hctrl i)
  · exact ⟨rfl, hempty⟩

theorem hasControlledExtinctionWithin_of_tower_extinctBy
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    [Nonempty P.Carrier]
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      SmoothCutCapCompletion ((T.observe b hb).event i).transition)
    (hout : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    {B : ℝ} (h : T.ExtinctBy B) :
    HasControlledExtinctionWithin P.toClosedOrientedManifold g B := by
  obtain ⟨b, hb, hbB, hempty⟩ := h
  refine hasControlledExtinctionWithin_of_observedHistory P g (T.observe b hb.le)
    (T.observeInitial b hb.le) (hc b hb.le) (hout b hb.le) (hctrl b hb.le) hempty ?_
  calc (T.observe b hb.le).time (Fin.last (T.observe b hb.le).eventCount)
      ≤ (T.observe b hb.le).horizon := ObservedHistory.time_le_horizon_at _ _
    _ = b := T.observe_horizon b hb.le
    _ ≤ B := hbB

theorem hasControlledExtinctionWithin_of_tower_extinctAbove
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    [Nonempty P.Carrier]
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      SmoothCutCapCompletion ((T.observe b hb).event i).transition)
    (hout : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    {B : ℝ} (h : T.ExtinctAbove B) :
    HasControlledExtinctionWithin P.toClosedOrientedManifold g (max 1 (B + 1)) :=
  hasControlledExtinctionWithin_of_tower_extinctBy T hc hout hctrl
    (T.extinctBy_of_extinctAbove h)

theorem hasControlledExtinctionWithin_of_tower_uniformRecordsAbove
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    [Nonempty P.Carrier]
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      SmoothCutCapCompletion ((T.observe b hb).event i).transition)
    (hout : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    {c A : ℝ} (h : T.UniformRecordsAbove c A) :
    HasControlledExtinctionWithin P.toClosedOrientedManifold g
      (max 1 (extinctionThreshold c A + 1)) :=
  hasControlledExtinctionWithin_of_tower_extinctBy T hc hout hctrl
    (T.extinctBy_extinctionThreshold_of_uniformRecordsAbove h)

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_timeLe
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {B : ℝ} (hB : T.toObservationTower.ExtinctBy B) :
    HasControlledExtinctionWithin M.toClosedOrientedManifold g B :=
  letI : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  hasControlledExtinctionWithin_of_tower_extinctBy T.toObservationTower
    (fun b hb i => (T.hasCutCapCompletion_toObservationTower hbfr b hb i).some)
    (fun b hb i => T.coreInclusionIsSmoothEmbedding_toObservationTower b hb i)
    (fun b hb i q => T.poincareStandardDiscarded_toObservationTower hctrl b hb i q)
    hB

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_uniformRecordsAbove_timeLe
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (h : T.toObservationTower.UniformRecordsAbove c A) :
    HasControlledExtinctionWithin M.toClosedOrientedManifold g
      (max 1 (extinctionThreshold c A + 1)) :=
  letI : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  hasControlledExtinctionWithin_of_tower_uniformRecordsAbove T.toObservationTower
    (fun b hb i => (T.hasCutCapCompletion_toObservationTower hbfr b hb i).some)
    (fun b hb i => T.coreInclusionIsSmoothEmbedding_toObservationTower b hb i)
    (fun b hb i q => T.poincareStandardDiscarded_toObservationTower hctrl b hb i q)
    h

end DifferentialGeometry.PDE.RicciFlow.Surgery

end
