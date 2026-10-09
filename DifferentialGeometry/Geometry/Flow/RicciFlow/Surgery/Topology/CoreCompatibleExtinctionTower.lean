import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OpenCoreSubmanifold

set_option autoImplicit false
noncomputable section
open Bundle Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

def hasCoreCompatibleEventsOfHistory (H : ObservedHistory.{u}) : Prop :=
  ∀ i : Fin H.eventCount, (H.event i).coreCompatibility

def hasCoreCompatibleEvents {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) : Prop :=
  ∀ (b : ℝ) (hb : 0 ≤ b), hasCoreCompatibleEventsOfHistory (T.observe b hb)

theorem hasCoreCompatibleEventsOfHistory_observe_zero {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : ObservationTower P g) :
    hasCoreCompatibleEventsOfHistory (T.observe 0 le_rfl) := by
  intro i
  have h : (T.observe 0 le_rfl).eventCount = 0 :=
    ObservedHistory.eventCount_eq_zero_of_horizon_zero (T.observe 0 le_rfl) rfl
  exact (h ▸ i).elim0

theorem isOpen_old_of_coreCompatibleEvents {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (h : hasCoreCompatibleEvents T) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      IsOpen (((T.observe b hb).event i).old :
        Set ((T.observe b hb).event i).transition.trace.tubes.core) :=
  fun b hb i => ((T.observe b hb).event i).isOpen_old_of_coreCompatibility (h b hb i)

theorem coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    (h : hasCoreCompatibleEvents T) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1) :=
  fun b hb i =>
    ((T.observe b hb).event i).coreInclusion_isSmoothEmbedding_of_coreCompatibility (h b hb i)

theorem hasExtinctObservationTower_of_coreCompatibleEvents
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.observe b hb).event i).transition))
    (hcore : hasCoreCompatibleEvents T)
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    (hextinct : towerExtinct T) :
    hasExtinctObservationTower M g :=
  ⟨T, hc, coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents T hcore, hctrl, hextinct⟩

def hasCoreCompatibleObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.observe b hb).event i).transition)) ∧
    hasCoreCompatibleEvents T ∧
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier) ∧
    towerExtinct T

theorem hasExtinctObservationTower_of_coreCompatible
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasCoreCompatibleObservationTower M g) : hasExtinctObservationTower M g := by
  obtain ⟨T, hc, hcore, hctrl, hextinct⟩ := h
  exact hasExtinctObservationTower_of_coreCompatibleEvents M g T hc hcore hctrl hextinct

theorem exists_poincare_controlled_extinction_of_coreCompatible
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasCoreCompatibleObservationTower M g) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_extinctObservationTower M g
    (hasExtinctObservationTower_of_coreCompatible M g h)

theorem exists_isOpenCoreSubmanifold {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    ∃ (old : Type u) (oldTop : TopologicalSpace old)
      (oldCharts : ChartedSpace (EuclideanHalfSpace 3) old) (ι : old → X.trace.tubes.core),
      @IsOpenCoreSubmanifold P Q D N X old oldTop oldCharts ι :=
  ⟨↥(⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩ :
      TopologicalSpace.Opens X.trace.tubes.core),
    inferInstance, X.coreOpensCharts _, Subtype.val,
    X.isOpenCoreSubmanifold_retainedCore⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery
