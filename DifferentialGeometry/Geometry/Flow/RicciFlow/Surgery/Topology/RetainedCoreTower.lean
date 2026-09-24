import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CoreCompatibleExtinctionTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EmptyHistory
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingRestriction

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

def retainedCoreOpens (X : SmoothCutCapTransition P Q D N) :
    TopologicalSpace.Opens X.trace.tubes.core :=
  ⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩

end SmoothCutCapTransition

private theorem isManifold_opens {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (U : TopologicalSpace.Opens M) : IsManifold (𝓡∂ 3) ∞ (↥U) :=
  inferInstance

structure RetainedCoreEvent (P Q : OrientedThreeStage.{u}) (a s : ℝ) where
  discarded : OrientedThreeStage.{u}
  capped : OrientedThreeStage.{u}
  transition : SmoothCutCapTransition P Q discarded capped
  incoming : P.IncomingSlab a s
  terminal : incoming.TerminalLimitMetric
  outputMetric : Q.Metric
  oldTerminal : C((transition.retainedCoreOpens : Type u), incoming.terminalRegularOpen)
  oldTerminal_eq : ∀ x : transition.retainedCoreOpens, (oldTerminal x).1 = x.1.1
  oldOutput : C((transition.retainedCoreOpens : Type u), Q.Carrier)
  oldOutput_eq : ∀ x : transition.retainedCoreOpens,
    transition.trace.presentation (transition.trace.capping.coreInclusion x.1) =
      Sum.inl (oldOutput x)
  old_metric_eq : letI := transition.coreOpensCharts transition.retainedCoreOpens
    ∀ (x : transition.retainedCoreOpens) (v w : TangentSpace (𝓡∂ 3) x),
      terminal.metric.inner (oldTerminal x)
          (mfderiv (𝓡∂ 3) ThreeModel oldTerminal x v)
          (mfderiv (𝓡∂ 3) ThreeModel oldTerminal x w) =
        outputMetric.inner (oldOutput x)
          (mfderiv (𝓡∂ 3) ThreeModel oldOutput x v)
          (mfderiv (𝓡∂ 3) ThreeModel oldOutput x w)
  old_contains_outside : ∀ x : transition.trace.tubes.core,
    x ∈ transition.trace.retainedCore →
    (∀ b : transition.trace.tubes.Index,
      x.1 ∉ transition.trace.tubes.tube b ''
        {z : TubeDomain | (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2}) →
      x ∈ transition.trace.retainedCore
  every_child_meets_old : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : transition.retainedCoreOpens, ConnectedComponents.mk (oldOutput x) = c

namespace RetainedCoreEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

def toMetricCutCapEvent (E : RetainedCoreEvent P Q a s) : MetricCutCapEvent P Q a s :=
  letI : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core :=
    E.transition.coreCharts
  letI : IsManifold (𝓡∂ 3) ∞ E.transition.trace.tubes.core := E.transition.coreSmooth
  letI : CompactSpace E.transition.trace.tubes.core := E.transition.core_compact
  { discarded := E.discarded
    capped := E.capped
    transition := E.transition
    incoming := E.incoming
    terminal := E.terminal
    outputMetric := E.outputMetric
    old := E.transition.trace.retainedCore
    old_compact := (CutCapTopology.isClopen_retainedCore E.transition.trace).isClosed.isCompact
    old_retained := subset_rfl
    oldCharts := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    oldSmooth := isManifold_opens E.transition.retainedCoreOpens
    old_induced := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
      (𝓡∂ 3) ThreeModel _ E.transition.core_induced E.transition.retainedCoreOpens
    oldTerminal := E.oldTerminal
    oldTerminal_eq := E.oldTerminal_eq
    oldOutput := E.oldOutput
    oldOutput_eq := E.oldOutput_eq
    old_metric_eq := E.old_metric_eq
    old_contains_outside := fun _ hx _ => hx
    every_child_meets_old := E.every_child_meets_old }

theorem coreCompatibility (E : RetainedCoreEvent P Q a s) :
    E.toMetricCutCapEvent.coreCompatibility :=
  E.transition.isOpenCoreSubmanifold_retainedCore

theorem coreInclusion_isSmoothEmbedding (E : RetainedCoreEvent P Q a s) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.toMetricCutCapEvent.old :=
      E.toMetricCutCapEvent.oldCharts
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : E.toMetricCutCapEvent.old =>
        E.transition.trace.capping.coreInclusion x.1) :=
  E.toMetricCutCapEvent.coreInclusion_isSmoothEmbedding_of_coreCompatibility
    E.coreCompatibility

end RetainedCoreEvent

structure RetainedCoreHistory (P : OrientedThreeStage.{u}) where
  horizon : ℝ
  horizon_nonneg : 0 ≤ horizon
  eventCount : ℕ
  time : Fin (eventCount + 1) → ℝ
  time_strictMono : StrictMono time
  time_zero : time 0 = 0
  time_le_horizon : time (Fin.last eventCount) ≤ horizon
  stage : Fin (eventCount + 1) → OrientedThreeStage.{u}
  initialMetric : (i : Fin (eventCount + 1)) → (stage i).Metric
  coreEvent : (i : Fin eventCount) →
    RetainedCoreEvent (stage i.castSucc) (stage i.succ) (time i.castSucc) (time i.succ)
  event_initial : ∀ i : Fin eventCount,
    (coreEvent i).toMetricCutCapEvent.incoming.flow.base.metric (time i.castSucc) =
      initialMetric i.castSucc
  event_output : ∀ i : Fin eventCount,
    (coreEvent i).toMetricCutCapEvent.outputMetric = initialMetric i.succ
  finalSlab : time (Fin.last eventCount) < horizon →
    (stage (Fin.last eventCount)).ClosedSlab (time (Fin.last eventCount)) horizon
  final_initial : ∀ h : time (Fin.last eventCount) < horizon,
    (finalSlab h).flow.base.metric (time (Fin.last eventCount)) =
      initialMetric (Fin.last eventCount)

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}}

abbrev toHistory (H : RetainedCoreHistory P) : ObservedHistory.{u} where
  horizon := H.horizon
  horizon_nonneg := H.horizon_nonneg
  eventCount := H.eventCount
  time := H.time
  time_strictMono := H.time_strictMono
  time_zero := H.time_zero
  time_le_horizon := H.time_le_horizon
  stage := H.stage
  initialMetric := H.initialMetric
  event := fun i => (H.coreEvent i).toMetricCutCapEvent
  event_initial := H.event_initial
  event_output := H.event_output
  finalSlab := H.finalSlab
  final_initial := H.final_initial

@[simp] theorem toHistory_eventCount (H : RetainedCoreHistory P) :
    H.toHistory.eventCount = H.eventCount := rfl

@[simp] theorem toHistory_event (H : RetainedCoreHistory P) (i : Fin H.eventCount) :
    H.toHistory.event i = (H.coreEvent i).toMetricCutCapEvent := rfl

end RetainedCoreHistory

structure RetainedCoreObservationTower (P : OrientedThreeStage.{u}) (g : P.Metric) where
  history : ℕ → RetainedCoreHistory P
  horizon_eq : ∀ n : ℕ, (history n).horizon = (n : ℝ)
  initial : ∀ n : ℕ, InitialIdentification P g (history n).toHistory
  successor : ∀ n : ℕ, ObservedHistory.SamePresentation
    (((history (n + 1)).toHistory).restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        simp only [horizon_eq]
        exact_mod_cast Nat.le_succ n⟩)
      ((history n).toHistory)
  initial_successor : ∀ n : ℕ,
    HEq (((initial (n + 1)).restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        simp only [horizon_eq]
        exact_mod_cast Nat.le_succ n⟩)).map
      (initial n).map

namespace RetainedCoreObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)

def toObservationTower : ObservationTower P g where
  history := fun n => (T.history n).toHistory
  horizon_eq := T.horizon_eq
  initial := T.initial
  successor := T.successor
  initial_successor := T.initial_successor

end RetainedCoreObservationTower

namespace ObservedHistory

theorem coreCompatibility_restrict {K : ObservedHistory.{u}} {t : Icc (0 : ℝ) K.horizon}
    (i : Fin (K.restrict t).eventCount)
    (h : ∀ j : Fin K.eventCount, (K.event j).coreCompatibility) :
    ((K.restrict t).event i).coreCompatibility := by
  rw [eq_of_heq (ObservedHistory.restrict_event K t i)]
  exact h _

end ObservedHistory

namespace RetainedCoreObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)

theorem hasCoreCompatibleEvents_toObservationTower :
    hasCoreCompatibleEvents T.toObservationTower := by
  intro b hb i
  simp only [ObservationTower.observe, ObservationTower.atIndex,
    RetainedCoreObservationTower.toObservationTower]
  refine ObservedHistory.coreCompatibility_restrict i ?_
  intro j
  exact RetainedCoreEvent.coreCompatibility ((T.history (Nat.ceil b)).coreEvent j)

end RetainedCoreObservationTower

namespace ObservedHistory

private theorem IsPrefixOf.restrict_prefix {H K : ObservedHistory.{u}}
    (h : H.IsPrefixOf K) {t : Icc (0 : ℝ) K.horizon} (ht : H.horizon ≤ t.1) :
    H.IsPrefixOf (K.restrict t) := by
  refine ⟨ht, ?_⟩
  have h1 := ObservedHistory.restrict_restrict K t ⟨H.horizon, H.horizon_nonneg, ht⟩
  have h2 := h.presentation
  have hs : (⟨H.horizon, H.horizon_nonneg, ht.trans t.2.2⟩ : Icc (0 : ℝ) K.horizon) =
      ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩ := Subtype.ext rfl
  rw [← hs] at h2
  exact h1.trans h2

end ObservedHistory

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}}

abbrev atZero (P : OrientedThreeStage.{u}) (g : P.Metric) : RetainedCoreHistory P where
  horizon := 0
  horizon_nonneg := le_rfl
  eventCount := 0
  time := fun _ => 0
  time_strictMono := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  time_zero := rfl
  time_le_horizon := le_rfl
  stage := fun _ => P
  initialMetric := fun _ => g
  coreEvent i := Fin.elim0 i
  event_initial i := Fin.elim0 i
  event_output i := Fin.elim0 i
  finalSlab := fun h => False.elim ((lt_irrefl (0 : ℝ)) h)
  final_initial := fun h => False.elim ((lt_irrefl (0 : ℝ)) h)

def emptyExtension (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) : RetainedCoreHistory P where
  horizon := B
  horizon_nonneg := H.horizon_nonneg.trans hB
  eventCount := H.eventCount
  time := H.time
  time_strictMono := H.time_strictMono
  time_zero := H.time_zero
  time_le_horizon := H.time_le_horizon.trans hB
  stage := H.stage
  initialMetric := H.initialMetric
  coreEvent := H.coreEvent
  event_initial := H.event_initial
  event_output := H.event_output
  finalSlab := fun h => (H.stage (Fin.last H.eventCount)).emptyClosedSlab
    (H.initialMetric (Fin.last H.eventCount)) h
  final_initial := fun _ => rfl

@[simp] theorem emptyExtension_horizon (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) : (H.emptyExtension B hB).horizon = B := rfl

theorem toHistory_emptyExtension (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B) :
    (H.emptyExtension B hB).toHistory = (H.toHistory).emptyExtension B hB := rfl

end RetainedCoreHistory

private def initialIdentificationAtZero (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g : P.Metric) : InitialIdentification P g (RetainedCoreHistory.atZero P g).toHistory where
  map := Diffeomorph.refl ThreeModel
    ((RetainedCoreHistory.atZero P g).toHistory.stage 0).Carrier ∞
  positive := ⟨(Diffeomorph.refl ThreeModel
      ((RetainedCoreHistory.atZero P g).toHistory.stage 0).Carrier ∞).contMDiff_toFun,
    fun x => isEmptyElim x⟩
  metric_eq := fun x => isEmptyElim x

namespace RetainedCoreObservationTower

def empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier] (g : P.Metric) :
    RetainedCoreObservationTower P g :=
  letI : IsEmpty ((RetainedCoreHistory.atZero P g).stage
      (Fin.last (RetainedCoreHistory.atZero P g).eventCount)).Carrier := hP
  letI : IsEmpty ((RetainedCoreHistory.atZero P g).toHistory.stage
      (Fin.last (RetainedCoreHistory.atZero P g).toHistory.eventCount)).Carrier := hP
  { history := fun n => (RetainedCoreHistory.atZero P g).emptyExtension n (Nat.cast_nonneg n)
    horizon_eq := fun n => rfl
    initial := fun n => (initialIdentificationAtZero P g).emptyExtension n (Nat.cast_nonneg n)
    successor := fun n => by
      refine (ObservedHistory.emptyExtension_unique ((RetainedCoreHistory.atZero P g).toHistory) n
        (Nat.cast_nonneg n) _ ?_ ?_).symm
      · refine ObservedHistory.IsPrefixOf.restrict_prefix ?_ ?_
        · rw [RetainedCoreHistory.toHistory_emptyExtension]
          exact ObservedHistory.isPrefixOf_emptyExtension _ _ (Nat.cast_nonneg (n + 1))
        · exact Nat.cast_nonneg n
      · simp only [ObservedHistory.restrict_horizon]
    initial_successor := fun n => HEq.rfl }

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

@[simp] theorem empty_eventCount (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g : P.Metric) (n : ℕ) : ((empty P g).history n).eventCount = 0 := rfl

private theorem restrict_eventCount_eq_zero {H : ObservedHistory.{u}}
    (t : Icc (0 : ℝ) H.horizon) (hc : H.eventCount = 0) : (H.restrict t).eventCount = 0 := by
  rw [ObservedHistory.restrict_eventCount]
  have hlt := (H.activeStage t).isLt
  omega

theorem empty_observe_eventCount (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g : P.Metric) (b : ℝ) (hb : 0 ≤ b) :
    ((empty P g).toObservationTower.observe b hb).eventCount = 0 :=
  restrict_eventCount_eq_zero (H := (empty P g).toObservationTower.history (Nat.ceil b)) _
    (by
      rw [RetainedCoreObservationTower.toObservationTower, RetainedCoreHistory.toHistory_eventCount]
      exact RetainedCoreObservationTower.empty_eventCount P g (Nat.ceil b))

theorem towerExtinct_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) :
    towerExtinct (empty P g).toObservationTower :=
  ⟨0, le_rfl, ⟨fun x => hP.false x⟩⟩

theorem exists_coreCompatible_extinct_tower_of_isEmpty (P : OrientedThreeStage.{u})
    [IsEmpty P.Carrier] (g : P.Metric) :
    ∃ T : RetainedCoreObservationTower P g,
      (∀ (b : ℝ) (hb : 0 ≤ b)
        (i : Fin (T.toObservationTower.observe b hb).eventCount),
        Nonempty
          (SmoothCutCapCompletion ((T.toObservationTower.observe b hb).event i).transition)) ∧
      hasCoreCompatibleEvents T.toObservationTower ∧
      (∀ (b : ℝ) (hb : 0 ≤ b)
        (i : Fin (T.toObservationTower.observe b hb).eventCount),
        ∀ q : ConnectedComponents ((T.toObservationTower.observe b hb).event i).discarded.Carrier,
          DifferentialGeometry.Topology.isPoincareStandard
            (((T.toObservationTower.observe b hb).event i).discarded.toClosedOrientedManifold
              |>.component q).Carrier) ∧
      towerExtinct T.toObservationTower := by
  refine ⟨empty P g, ?_, (empty P g).hasCoreCompatibleEvents_toObservationTower, ?_,
    towerExtinct_empty P g⟩
  · intro b hb i
    exact Fin.elim0 (Fin.cast (empty_observe_eventCount P g b hb) i)
  · intro b hb i
    exact Fin.elim0 (Fin.cast (empty_observe_eventCount P g b hb) i)

end RetainedCoreObservationTower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem hasCoreCompatibleObservationTower_of_retainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b)
      (i : Fin (T.toObservationTower.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.toObservationTower.observe b hb).event i).transition))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b)
      (i : Fin (T.toObservationTower.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.toObservationTower.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.toObservationTower.observe b hb).event i).discarded.toClosedOrientedManifold
            |>.component q).Carrier)
    (hextinct : towerExtinct T.toObservationTower) :
    hasCoreCompatibleObservationTower M g :=
  ⟨T.toObservationTower, hc, T.hasCoreCompatibleEvents_toObservationTower, hctrl, hextinct⟩

theorem hasExtinctObservationTower_of_retainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b)
      (i : Fin (T.toObservationTower.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.toObservationTower.observe b hb).event i).transition))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b)
      (i : Fin (T.toObservationTower.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.toObservationTower.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.toObservationTower.observe b hb).event i).discarded.toClosedOrientedManifold
            |>.component q).Carrier)
    (hextinct : towerExtinct T.toObservationTower) :
    hasExtinctObservationTower M g :=
  hasExtinctObservationTower_of_coreCompatible M g
    (hasCoreCompatibleObservationTower_of_retainedCoreTower M g T hc hctrl hextinct)

theorem exists_poincare_controlled_extinction_of_retainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b)
      (i : Fin (T.toObservationTower.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.toObservationTower.observe b hb).event i).transition))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b)
      (i : Fin (T.toObservationTower.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.toObservationTower.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.toObservationTower.observe b hb).event i).discarded.toClosedOrientedManifold
            |>.component q).Carrier)
    (hextinct : towerExtinct T.toObservationTower) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_coreCompatible M g
    (hasCoreCompatibleObservationTower_of_retainedCoreTower M g T hc hctrl hextinct)

end DifferentialGeometry.PDE.RicciFlow.Surgery
