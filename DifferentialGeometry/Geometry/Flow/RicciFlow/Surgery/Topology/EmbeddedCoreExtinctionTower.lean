import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CoreCompatibleExtinctionTower
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def IsEmbeddedCoreSubmanifold {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (old : Type u) [oldTop : TopologicalSpace old]
    [oldCharts : ChartedSpace (EuclideanHalfSpace 3) old]
    (ι : old → X.trace.tubes.core) : Prop :=
  letI : TopologicalSpace old := oldTop
  letI : ChartedSpace (EuclideanHalfSpace 3) old := oldCharts
  letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  IsSmoothEmbedding (𝓡∂ 3) (𝓡∂ 3) ∞ ι

theorem IsEmbeddedCoreSubmanifold.of_isOpenCoreSubmanifold {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) {old : Type u} [oldTop : TopologicalSpace old]
    [oldCharts : ChartedSpace (EuclideanHalfSpace 3) old]
    [oldSmooth : IsManifold (𝓡∂ 3) ∞ old]
    (ι : old → X.trace.tubes.core) (h : IsOpenCoreSubmanifold X old ι) :
    IsEmbeddedCoreSubmanifold X old ι := by
  classical
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  let coreSmooth : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
  obtain ⟨U, Ψ, hΨ⟩ := h
  have hbase : IsSmoothEmbedding (𝓡∂ 3) (𝓡∂ 3) ∞
      (Subtype.val : U → X.trace.tubes.core) := IsSmoothEmbedding.of_opens U
  have hcomp := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := 𝓡∂ 3)
    (f := (Subtype.val : U → X.trace.tubes.core)) hbase Ψ
  have hfun : ((Subtype.val : U → X.trace.tubes.core) ∘ ⇑Ψ) = ι := funext fun x => hΨ x
  change IsSmoothEmbedding (𝓡∂ 3) (𝓡∂ 3) ∞ ι
  exact hfun ▸ hcomp

theorem SmoothCutCapTransition.coreInclusion_isSmoothEmbedding_of_isEmbeddedCoreSubmanifold
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) {old : Type u}
    [oldTop : TopologicalSpace old] [oldCharts : ChartedSpace (EuclideanHalfSpace 3) old]
    (ι : old → X.trace.tubes.core) (h : IsEmbeddedCoreSubmanifold X old ι) :
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : old => X.trace.capping.coreInclusion (ι x)) := by
  classical
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  have hι : IsSmoothEmbedding (𝓡∂ 3) (𝓡∂ 3) ∞ ι := h
  exact IsSmoothEmbedding.comp_of_smoothBoundary
    (I := 𝓡∂ 3) (J := 𝓡∂ 3) (J' := ThreeModel)
    (f := ι) (g := X.trace.capping.coreInclusion) X.core_inclusion_smooth hι

theorem SmoothCutCapTransition.isEmbeddedCoreSubmanifold_retainedCore
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) :
    IsEmbeddedCoreSubmanifold (X := X)
      (old := ↥(⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩ :
        TopologicalSpace.Opens X.trace.tubes.core))
      (oldTop := inferInstance)
      (oldCharts := X.coreOpensCharts
        ⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩) (Subtype.val) := by
  classical
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  let coreSmooth : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
  exact IsEmbeddedCoreSubmanifold.of_isOpenCoreSubmanifold (X := X) (old := ↥(⟨X.trace.retainedCore,
      X.trace.retainedCore_isOpen⟩ : TopologicalSpace.Opens X.trace.tubes.core))
    (oldCharts := X.coreOpensCharts ⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩)
    (oldSmooth := inferInstance) (Subtype.val) X.isOpenCoreSubmanifold_retainedCore

theorem exists_isEmbeddedCoreSubmanifold {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    ∃ (old : Type u) (oldTop : TopologicalSpace old)
      (oldCharts : ChartedSpace (EuclideanHalfSpace 3) old) (ι : old → X.trace.tubes.core),
      @IsEmbeddedCoreSubmanifold P Q D N X old oldTop oldCharts ι :=
  ⟨↥(⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩ :
      TopologicalSpace.Opens X.trace.tubes.core),
    inferInstance, X.coreOpensCharts _, Subtype.val,
    X.isEmbeddedCoreSubmanifold_retainedCore⟩

theorem contMDiffAt_oldInclusion {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (x : E.old) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    letI : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core :=
      E.transition.coreCharts
    ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (fun y : E.old => y.1) x := by
  classical
  let oldCharts : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core :=
    E.transition.coreCharts
  have hcore := E.transition.core_induced.isImmersion.isImmersionAt (x.1)
  rw [ContMDiffAt.iff_comp_isImmersionAt hcore]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact E.old_induced.contMDiff.contMDiffAt

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem isEmbeddedCoreSubmanifold_of_coreCompatibility (E : MetricCutCapEvent P Q a s)
    (h : E.coreCompatibility) :
    IsEmbeddedCoreSubmanifold (X := E.transition) (old := E.old) (oldTop := inferInstance)
      (oldCharts := E.oldCharts) (fun x : E.old => x.1) := by
  classical
  let oldCharts : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let oldSmooth : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  exact IsEmbeddedCoreSubmanifold.of_isOpenCoreSubmanifold (X := E.transition) (old := E.old)
    (oldCharts := E.oldCharts) (oldSmooth := E.oldSmooth) (fun x : E.old => x.1) h

theorem coreInclusion_isSmoothEmbedding_of_isEmbeddedCoreSubmanifold
    (E : MetricCutCapEvent P Q a s)
    (h : IsEmbeddedCoreSubmanifold (X := E.transition) (old := E.old) (oldTop := inferInstance)
      (oldCharts := E.oldCharts) (fun x : E.old => x.1)) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : E.old => E.transition.trace.capping.coreInclusion x.1) :=
  E.transition.coreInclusion_isSmoothEmbedding_of_isEmbeddedCoreSubmanifold
    (old := E.old) (oldCharts := E.oldCharts) (fun x : E.old => x.1) h

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def hasEmbeddedCoreEventsOfHistory (H : ObservedHistory.{u}) : Prop :=
  ∀ i : Fin H.eventCount,
    @IsEmbeddedCoreSubmanifold _ _ _ _ (H.event i).transition (H.event i).old
      inferInstance (H.event i).oldCharts (fun x => x.1)

def hasEmbeddedCoreEvents {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) : Prop :=
  ∀ (b : ℝ) (hb : 0 ≤ b), hasEmbeddedCoreEventsOfHistory (T.observe b hb)

theorem hasEmbeddedCoreEventsOfHistory_observe_zero {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : ObservationTower P g) :
    hasEmbeddedCoreEventsOfHistory (T.observe 0 le_rfl) := by
  intro i
  have h : (T.observe 0 le_rfl).eventCount = 0 :=
    ObservedHistory.eventCount_eq_zero_of_horizon_zero (T.observe 0 le_rfl) rfl
  exact (h ▸ i).elim0

theorem hasEmbeddedCoreEvents_of_coreCompatibleEvents {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : ObservationTower P g) (h : hasCoreCompatibleEvents T) :
    hasEmbeddedCoreEvents T :=
  fun b hb i => ((T.observe b hb).event i).isEmbeddedCoreSubmanifold_of_coreCompatibility
    (h b hb i)

theorem coreInclusion_isSmoothEmbedding_of_embeddedCoreEvents
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    (h : hasEmbeddedCoreEvents T) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1) :=
  fun b hb i =>
    ((T.observe b hb).event i).coreInclusion_isSmoothEmbedding_of_isEmbeddedCoreSubmanifold
      (h b hb i)

theorem hasExtinctObservationTower_of_embeddedCoreEvents
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.observe b hb).event i).transition))
    (hcore : hasEmbeddedCoreEvents T)
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    (hextinct : towerExtinct T) :
    hasExtinctObservationTower M g :=
  ⟨T, hc, coreInclusion_isSmoothEmbedding_of_embeddedCoreEvents T hcore, hctrl, hextinct⟩

def hasEmbeddedCoreObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.observe b hb).event i).transition)) ∧
    hasEmbeddedCoreEvents T ∧
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier) ∧
    towerExtinct T

theorem hasEmbeddedCoreObservationTower_of_coreCompatible
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasCoreCompatibleObservationTower M g) : hasEmbeddedCoreObservationTower M g := by
  obtain ⟨T, hc, hcore, hctrl, hextinct⟩ := h
  exact ⟨T, hc, hasEmbeddedCoreEvents_of_coreCompatibleEvents T hcore, hctrl, hextinct⟩

theorem hasExtinctObservationTower_of_embeddedCore
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasEmbeddedCoreObservationTower M g) : hasExtinctObservationTower M g := by
  obtain ⟨T, hc, hcore, hctrl, hextinct⟩ := h
  exact hasExtinctObservationTower_of_embeddedCoreEvents M g T hc hcore hctrl hextinct

theorem exists_poincare_controlled_extinction_of_embeddedCore
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasEmbeddedCoreObservationTower M g) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_extinctObservationTower M g
    (hasExtinctObservationTower_of_embeddedCore M g h)

end DifferentialGeometry.PDE.RicciFlow.Surgery
