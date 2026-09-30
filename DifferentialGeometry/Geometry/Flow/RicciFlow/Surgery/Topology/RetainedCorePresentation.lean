import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingCompletion

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N]

def retainedOutput (E : CutCapTopology M Q D N) (x : E.retainedCore) : Q :=
  Classical.choose x.2

theorem retainedOutput_eq (E : CutCapTopology M Q D N) (x : E.retainedCore) :
    E.presentation (E.capping.coreInclusion x.1) = Sum.inl (E.retainedOutput x) :=
  Classical.choose_spec x.2

theorem continuous_retainedOutput (E : CutCapTopology M Q D N) :
    Continuous E.retainedOutput := by
  refine (Topology.IsEmbedding.inl (X := Q) (Y := D)).continuous_iff.mpr ?_
  have h : (Sum.inl ∘ E.retainedOutput) =
      fun x : E.retainedCore => E.presentation (E.capping.coreInclusion x.1) := by
    funext x
    exact (E.retainedOutput_eq x).symm
  rw [h]
  exact E.presentation.continuous.comp
    (E.capping.coreInclusion.continuous.comp continuous_subtype_val)

end CutCapTopology

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

def retainedOutputMap (X : SmoothCutCapTransition P Q D N) :
    C((X.retainedCoreOpens : Type u), Q.Carrier) :=
  ⟨X.trace.retainedOutput, X.trace.continuous_retainedOutput⟩

theorem retainedOutputMap_apply (X : SmoothCutCapTransition P Q D N)
    (x : X.retainedCoreOpens) :
    X.retainedOutputMap x = X.trace.retainedOutput x := rfl

theorem retainedOutputMap_eq (X : SmoothCutCapTransition P Q D N)
    (x : X.retainedCoreOpens) :
    X.trace.presentation (X.trace.capping.coreInclusion x.1) =
      Sum.inl (X.retainedOutputMap x) :=
  X.trace.retainedOutput_eq x

end SmoothCutCapTransition

namespace SmoothCutCapCompletion

variable {P Q D N : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D N}

theorem exists_retainedOutputMap_eq (h : SmoothCutCapCompletion X)
    (c : ConnectedComponents Q.Carrier) :
    ∃ x : X.retainedCoreOpens, ConnectedComponents.mk (X.retainedOutputMap x) = c := by
  obtain ⟨x, q, hpres, hmk⟩ := h.every_component_meets_core c
  have hpres' : X.trace.presentation (X.trace.capping.coreInclusion x) = Sum.inl q := by
    rw [← h.coreInclusion_eq x, ← X.presentation_eq]
    exact hpres
  have hx : x ∈ X.trace.retainedCore := ⟨q, hpres'⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  have h1 : X.trace.presentation (X.trace.capping.coreInclusion x) =
      Sum.inl (X.retainedOutputMap ⟨x, hx⟩) := X.retainedOutputMap_eq ⟨x, hx⟩
  rw [hpres'] at h1
  rw [← Sum.inl_injective h1, hmk]

end SmoothCutCapCompletion

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} {a s : ℝ}

def retainedTerminalMap (X : SmoothCutCapTransition P Q D N) (G : P.IncomingSlab a s)
    (h : ∀ x : X.trace.tubes.core, x ∈ X.trace.retainedCore →
      x.1 ∈ G.terminalRegularRegion) :
    C((X.retainedCoreOpens : Type u), G.terminalRegularOpen) where
  toFun x := ⟨x.1.1, h x.1 x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem retainedTerminalMap_apply (X : SmoothCutCapTransition P Q D N) (G : P.IncomingSlab a s)
    (h : ∀ x : X.trace.tubes.core, x ∈ X.trace.retainedCore →
      x.1 ∈ G.terminalRegularRegion) (x : X.retainedCoreOpens) :
    (X.retainedTerminalMap G h x).1 = x.1.1 := rfl

end SmoothCutCapTransition

structure RetainedCoreEventData (P Q : OrientedThreeStage.{u}) (a s : ℝ) where
  discarded : OrientedThreeStage.{u}
  capped : OrientedThreeStage.{u}
  transition : SmoothCutCapTransition P Q discarded capped
  completion : SmoothCutCapCompletion transition
  incoming : P.IncomingSlab a s
  terminal : incoming.TerminalLimitMetric
  outputMetric : Q.Metric
  retained_terminal : ∀ x : transition.trace.tubes.core,
    x ∈ transition.trace.retainedCore → x.1 ∈ incoming.terminalRegularRegion
  retained_metric_eq : letI := transition.coreOpensCharts transition.retainedCoreOpens
    ∀ (x : transition.retainedCoreOpens) (v w : TangentSpace (𝓡∂ 3) x),
      terminal.metric.inner (transition.retainedTerminalMap incoming retained_terminal x)
          (mfderiv (𝓡∂ 3) ThreeModel
            (transition.retainedTerminalMap incoming retained_terminal) x v)
          (mfderiv (𝓡∂ 3) ThreeModel
            (transition.retainedTerminalMap incoming retained_terminal) x w) =
        outputMetric.inner (transition.retainedOutputMap x)
          (mfderiv (𝓡∂ 3) ThreeModel transition.retainedOutputMap x v)
          (mfderiv (𝓡∂ 3) ThreeModel transition.retainedOutputMap x w)

namespace RetainedCoreEventData

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

def toRetainedCoreEvent (D : RetainedCoreEventData P Q a s) : RetainedCoreEvent P Q a s where
  discarded := D.discarded
  capped := D.capped
  transition := D.transition
  incoming := D.incoming
  terminal := D.terminal
  outputMetric := D.outputMetric
  oldTerminal := D.transition.retainedTerminalMap D.incoming D.retained_terminal
  oldTerminal_eq := fun _ => rfl
  oldOutput := D.transition.retainedOutputMap
  oldOutput_eq := fun x => D.transition.retainedOutputMap_eq x
  old_metric_eq := D.retained_metric_eq
  every_child_meets_old := D.completion.exists_retainedOutputMap_eq

theorem coreCompatibility (D : RetainedCoreEventData P Q a s) :
    D.toRetainedCoreEvent.toMetricCutCapEvent.coreCompatibility :=
  D.toRetainedCoreEvent.coreCompatibility

end RetainedCoreEventData

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

def coreInclusionIsSmoothEmbedding (E : MetricCutCapEvent P Q a s) : Prop :=
  letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
    (fun x : E.old => E.transition.trace.capping.coreInclusion x.1)

theorem coreInclusionIsSmoothEmbedding_of_coreCompatibility (E : MetricCutCapEvent P Q a s)
    (h : E.coreCompatibility) : E.coreInclusionIsSmoothEmbedding :=
  E.coreInclusion_isSmoothEmbedding_of_coreCompatibility h

def hasCutCapCompletion (E : MetricCutCapEvent P Q a s) : Prop :=
  Nonempty (SmoothCutCapCompletion E.transition)

def poincareStandardDiscarded (E : MetricCutCapEvent P Q a s) : Prop :=
  ∀ q : ConnectedComponents E.discarded.Carrier,
    DifferentialGeometry.Topology.isPoincareStandard
      (E.discarded.toClosedOrientedManifold.component q).Carrier

end MetricCutCapEvent

namespace RetainedCoreEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem toMetricCutCapEvent_coreInclusionIsSmoothEmbedding (E : RetainedCoreEvent P Q a s) :
    E.toMetricCutCapEvent.coreInclusionIsSmoothEmbedding :=
  E.transition.coreInclusion_isSmoothEmbedding_retainedCore

theorem toMetricCutCapEvent_hasCutCapCompletion (E : RetainedCoreEvent P Q a s)
    (h : E.transition.boundaryFrameReversing) :
    E.toMetricCutCapEvent.hasCutCapCompletion :=
  ⟨E.transition.toSmoothCutCapCompletion h⟩

end RetainedCoreEvent

namespace ObservedHistory

variable {K : ObservedHistory.{u}}

theorem coreInclusionIsSmoothEmbedding_restrict {t : Icc (0 : ℝ) K.horizon}
    (i : Fin (K.restrict t).eventCount)
    (h : ∀ j : Fin K.eventCount, (K.event j).coreInclusionIsSmoothEmbedding) :
    ((K.restrict t).event i).coreInclusionIsSmoothEmbedding := by
  rw [eq_of_heq (ObservedHistory.restrict_event K t i)]
  exact h _

theorem hasCutCapCompletion_restrict {t : Icc (0 : ℝ) K.horizon}
    (i : Fin (K.restrict t).eventCount)
    (h : ∀ j : Fin K.eventCount, (K.event j).hasCutCapCompletion) :
    ((K.restrict t).event i).hasCutCapCompletion := by
  rw [eq_of_heq (ObservedHistory.restrict_event K t i)]
  exact h _

theorem poincareStandardDiscarded_restrict {t : Icc (0 : ℝ) K.horizon}
    (i : Fin (K.restrict t).eventCount)
    (h : ∀ j : Fin K.eventCount, (K.event j).poincareStandardDiscarded) :
    ((K.restrict t).event i).poincareStandardDiscarded := by
  rw [eq_of_heq (ObservedHistory.restrict_event K t i)]
  exact h _

end ObservedHistory

namespace RetainedCoreObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def hasBoundaryFrameReversing (T : RetainedCoreObservationTower P g) : Prop :=
  ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
    ((T.history n).coreEvent j).transition.boundaryFrameReversing

def hasPoincareStandardDiscarded (T : RetainedCoreObservationTower P g) : Prop :=
  ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
    ((T.history n).coreEvent j).toMetricCutCapEvent.poincareStandardDiscarded

theorem hasCutCapCompletion_toObservationTower (T : RetainedCoreObservationTower P g)
    (h : T.hasBoundaryFrameReversing) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.toObservationTower.observe b hb).eventCount),
      ((T.toObservationTower.observe b hb).event i).hasCutCapCompletion := by
  intro b hb i
  simp only [ObservationTower.observe, ObservationTower.atIndex,
    RetainedCoreObservationTower.toObservationTower]
  refine ObservedHistory.hasCutCapCompletion_restrict i ?_
  intro j
  exact ((T.history (Nat.ceil b)).coreEvent j).toMetricCutCapEvent_hasCutCapCompletion
    (h (Nat.ceil b) j)

theorem coreInclusionIsSmoothEmbedding_toObservationTower (T : RetainedCoreObservationTower P g) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.toObservationTower.observe b hb).eventCount),
      ((T.toObservationTower.observe b hb).event i).coreInclusionIsSmoothEmbedding := by
  intro b hb i
  simp only [ObservationTower.observe, ObservationTower.atIndex,
    RetainedCoreObservationTower.toObservationTower]
  refine ObservedHistory.coreInclusionIsSmoothEmbedding_restrict i ?_
  intro j
  exact ((T.history (Nat.ceil b)).coreEvent j).toMetricCutCapEvent_coreInclusionIsSmoothEmbedding

theorem poincareStandardDiscarded_toObservationTower (T : RetainedCoreObservationTower P g)
    (h : T.hasPoincareStandardDiscarded) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.toObservationTower.observe b hb).eventCount),
      ((T.toObservationTower.observe b hb).event i).poincareStandardDiscarded := by
  intro b hb i
  simp only [ObservationTower.observe, ObservationTower.atIndex,
    RetainedCoreObservationTower.toObservationTower]
  refine ObservedHistory.poincareStandardDiscarded_restrict i ?_
  intro j
  exact h (Nat.ceil b) j

end RetainedCoreObservationTower

private def twoPointTubeSystem : TubeSystem (PUnit.{1} ⊕ PUnit.{1}) where
  Index := PEmpty
  finiteIndex := inferInstance
  tube := fun a => PEmpty.elim a
  embedding := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

private theorem twoPointTubeSystem_core : twoPointTubeSystem.core = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  simp only [TubeSystem.core, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  intro a
  exact PEmpty.elim a

private def twoPointCapping : Capping twoPointTubeSystem (PUnit.{1} ⊕ PUnit.{1}) where
  coreInclusion := ⟨Subtype.val, continuous_subtype_val⟩
  coreEmbedding := Topology.IsEmbedding.subtypeVal
  cap := fun b => PEmpty.elim b.1
  capEmbedding := fun b => PEmpty.elim b.1
  attaching := fun b => PEmpty.elim b.1
  boundary_eq := fun b => PEmpty.elim b.1
  exhaustive := by
    have hunion : (⋃ b : twoPointTubeSystem.Boundary,
        Set.range (PEmpty.elim b.1 : C(ThreeBall, PUnit.{1} ⊕ PUnit.{1}))) = ∅ := by
      apply Set.iUnion_eq_empty.mpr
      intro b
      exact PEmpty.elim b.1
    rw [hunion, Set.union_empty]
    apply Set.range_eq_univ.mpr
    intro x
    exact ⟨⟨x, by rw [twoPointTubeSystem_core]; exact Set.mem_univ x⟩, rfl⟩
  core_cap_intersection := fun b => PEmpty.elim b.1
  cap_disjoint := fun b => PEmpty.elim b.1

private def twoPointCutCap :
    CutCapTopology (PUnit.{1} ⊕ PUnit.{1}) PUnit.{1} PUnit.{1} (PUnit.{1} ⊕ PUnit.{1}) where
  tubes := twoPointTubeSystem
  capping := twoPointCapping
  presentation := Homeomorph.refl _
  nontrivial := Or.inr ⟨PUnit.unit⟩

theorem exists_cutCapTopology_retainedOutput :
    ∃ (E : CutCapTopology (PUnit.{1} ⊕ PUnit.{1}) PUnit.{1} PUnit.{1}
        (PUnit.{1} ⊕ PUnit.{1})) (x : E.retainedCore),
      E.retainedOutput x = PUnit.unit :=
  ⟨twoPointCutCap,
    ⟨⟨Sum.inl PUnit.unit,
        show Sum.inl PUnit.unit ∈ twoPointTubeSystem.core from by
          rw [twoPointTubeSystem_core]
          exact Set.mem_univ _⟩,
      ⟨PUnit.unit, rfl⟩⟩,
    Subsingleton.elim _ _⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem toSurgeryFiniteSurgeryHistory_poincareControlled_iff {H : ObservedHistory.{u}}
    (hn : 0 < H.eventCount)
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old =>
          (H.event i).transition.trace.capping.coreInclusion x.1)) :
    (H.toSurgeryFiniteSurgeryHistoryOfCutCapCompletion hn hc hout).poincareControlled ↔
      ∀ i : Fin H.eventCount, (H.event i).poincareStandardDiscarded :=
  Iff.rfl

theorem hasCoreCompatibleObservationTower_of_retainedCoreTower_cutCap
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (hctrl : T.hasPoincareStandardDiscarded)
    (hextinct : towerExtinct T.toObservationTower) :
    hasCoreCompatibleObservationTower M g :=
  ⟨T.toObservationTower, T.hasCutCapCompletion_toObservationTower hbfr,
    T.hasCoreCompatibleEvents_toObservationTower,
    T.poincareStandardDiscarded_toObservationTower hctrl, hextinct⟩

theorem hasExtinctObservationTower_of_retainedCoreTower_cutCap
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (hctrl : T.hasPoincareStandardDiscarded)
    (hextinct : towerExtinct T.toObservationTower) :
    hasExtinctObservationTower M g :=
  ⟨T.toObservationTower, T.hasCutCapCompletion_toObservationTower hbfr,
    T.coreInclusionIsSmoothEmbedding_toObservationTower,
    T.poincareStandardDiscarded_toObservationTower hctrl, hextinct⟩

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_cutCap
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (hctrl : T.hasPoincareStandardDiscarded)
    (hextinct : towerExtinct T.toObservationTower) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_extinctObservationTower M g
    (hasExtinctObservationTower_of_retainedCoreTower_cutCap M g T hbfr hctrl hextinct)

end DifferentialGeometry.PDE.RicciFlow.Surgery
