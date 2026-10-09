import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PoincareStandardDiscarded
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationLocality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OpenCoreSubmanifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem ObservedHistory.exists_isEmpty_stage_iff_final (H : ObservedHistory.{u}) :
    (∃ j : Fin (H.eventCount + 1), IsEmpty (H.stage j).Carrier) ↔
      IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
  refine ⟨?_, fun h => ⟨Fin.last H.eventCount, h⟩⟩
  rintro ⟨j, hj⟩
  have hlast : j = Fin.last H.eventCount := ObservedHistory.empty_stage_is_last H j
  rw [hlast] at hj
  exact hj

theorem MetricCutCapEvent.hasCutCapCompletion_of_boundaryFrameReversing
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : E.transition.boundaryFrameReversing) : E.hasCutCapCompletion :=
  ⟨E.transition.toSmoothCutCapCompletion h⟩

def InitialIdentification.reflAtZero (P : OrientedThreeStage.{u}) (g : P.Metric) :
    InitialIdentification P g (ObservedHistory.atZero P g) where
  map := Diffeomorph.refl ThreeModel ((ObservedHistory.atZero P g).stage 0).Carrier ∞
  positive := preservesTangentOrientation_refl P.orientation
  metric_eq := by
    intro x v w
    change g.inner x (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x v)
      (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x w) = g.inner x v w
    rw [mfderiv_id]
    rfl

def HasExtinctObservationNucleus (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
    (∀ i : Fin H.eventCount, (H.event i).transition.boundaryFrameReversing) ∧
    (∀ i : Fin H.eventCount, (H.event i).coreInclusionIsSmoothEmbedding) ∧
    (∀ i : Fin H.eventCount, (H.event i).poincareStandardDiscarded) ∧
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

def HasExtinctObservationNucleusWithCompletion
    (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
    (∀ i : Fin H.eventCount, (H.event i).transition.boundaryFrameReversing) ∧
    (∀ i : Fin H.eventCount, (H.event i).hasCutCapCompletion) ∧
    (∀ i : Fin H.eventCount, (H.event i).coreInclusionIsSmoothEmbedding) ∧
    (∀ i : Fin H.eventCount, (H.event i).poincareStandardDiscarded) ∧
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

def HasExtinctStandardSideNucleus (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
    (∀ i : Fin H.eventCount, (H.event i).transition.boundaryFrameReversing) ∧
    (∀ i : Fin H.eventCount, (H.event i).coreInclusionIsSmoothEmbedding) ∧
    (∀ i : Fin H.eventCount,
      (H.event i).discarded.toClosedOrientedManifold.componentwiseStandardFactor) ∧
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

def HasExtinctObservationNucleusOfCutCapCompletion
    (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
    (∀ i : Fin H.eventCount, (H.event i).hasCutCapCompletion) ∧
    (∀ i : Fin H.eventCount, (H.event i).coreInclusionIsSmoothEmbedding) ∧
    (∀ i : Fin H.eventCount, (H.event i).poincareStandardDiscarded) ∧
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_nucleus (P : OrientedThreeStage.{u})
    (g : P.Metric) (h : HasExtinctObservationNucleus P g) :
    HasExtinctObservationNucleusOfCutCapCompletion P g := by
  obtain ⟨H, A, hbfr, hcore, hctrl, hempty⟩ := h
  exact ⟨H, A, fun i => (H.event i).hasCutCapCompletion_of_boundaryFrameReversing (hbfr i),
    hcore, hctrl, hempty⟩

theorem exists_poincare_controlled_extinction_of_hasExtinctObservationNucleusOfCutCapCompletion
    (P : OrientedThreeStage.{u}) (g : P.Metric) [Nonempty P.Carrier]
    (h : HasExtinctObservationNucleusOfCutCapCompletion P g) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  obtain ⟨H, A, hc, hcore, hctrl, hempty⟩ := h
  exact exists_poincare_controlled_extinction_of_observedHistory P g H A
    (fun i => (hc i).some) (fun i => hcore i) hctrl hempty

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_tower_extinctBy
    (P : OrientedThreeStage.{u}) (g : P.Metric) (T : RetainedCoreObservationTower P g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {B : ℝ} (hB : T.toObservationTower.ExtinctBy B) :
    HasExtinctObservationNucleusOfCutCapCompletion P g := by
  obtain ⟨b, hb, _, hempty⟩ := hB
  exact ⟨T.toObservationTower.observe b hb.le,
    T.toObservationTower.observeInitial b hb.le,
    fun i => T.hasCutCapCompletion_toObservationTower hbfr b hb.le i,
    fun i => T.coreInclusionIsSmoothEmbedding_toObservationTower b hb.le i,
    fun i => T.poincareStandardDiscarded_toObservationTower hctrl b hb.le i,
    hempty⟩

theorem hasExtinctObservationNucleus_of_hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) :
    HasExtinctObservationNucleus
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g := by
  obtain ⟨H, A, hbfr, hctrl, hempty⟩ := h
  exact ⟨H.toHistory, A, hbfr,
    fun i => (H.coreEvent i).toMetricCutCapEvent_coreInclusionIsSmoothEmbedding, hctrl, hempty⟩

theorem hasExtinctObservationNucleusWithCompletion_iff (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    HasExtinctObservationNucleusWithCompletion P g ↔ HasExtinctObservationNucleus P g := by
  constructor
  · rintro ⟨H, A, hbfr, _, hcore, hctrl, hempty⟩
    exact ⟨H, A, hbfr, hcore, hctrl, hempty⟩
  · rintro ⟨H, A, hbfr, hcore, hctrl, hempty⟩
    exact ⟨H, A, hbfr, fun i => (H.event i).hasCutCapCompletion_of_boundaryFrameReversing
      (hbfr i), hcore, hctrl, hempty⟩

theorem hasExtinctStandardSideNucleus_implies (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : HasExtinctStandardSideNucleus P g) : HasExtinctObservationNucleus P g := by
  obtain ⟨H, A, hbfr, hcore, hside, hempty⟩ := h
  exact ⟨H, A, hbfr, hcore,
    fun i => MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseStandardFactor
      (H.event i) (hside i), hempty⟩

theorem exists_poincare_controlled_extinction_of_hasExtinctObservationNucleus
    (P : OrientedThreeStage.{u}) (g : P.Metric) [Nonempty P.Carrier]
    (h : HasExtinctObservationNucleus P g) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  obtain ⟨H, A, hbfr, hcore, hctrl, hempty⟩ := h
  exact exists_poincare_controlled_extinction_of_observedHistory P g H A
    (fun i => ((H.event i).hasCutCapCompletion_of_boundaryFrameReversing (hbfr i)).some)
    (fun i => hcore i) hctrl hempty

theorem hasExtinctObservationNucleus_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasExtinctObservationNucleus P g := by
  refine ⟨ObservedHistory.atZero P g, InitialIdentification.reflAtZero P g, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · exact hP

theorem not_isEmpty_atZero_stage_last (P : OrientedThreeStage.{u}) (g : P.Metric)
    [Nonempty P.Carrier] :
    ¬ IsEmpty ((ObservedHistory.atZero P g).stage
      (Fin.last (ObservedHistory.atZero P g).eventCount)).Carrier :=
  not_isEmpty_iff.mpr (inferInstanceAs (Nonempty P.Carrier))

theorem HasExtinctObservationNucleus.exists_eventCount_pos {P : OrientedThreeStage.{u}}
    {g : P.Metric} [Nonempty P.Carrier] (h : HasExtinctObservationNucleus P g) :
    ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H), 0 < H.eventCount := by
  obtain ⟨H, A, _, _, _, hempty⟩ := h
  exact ⟨H, A, @ObservedHistory.eventCount_pos_of_final_empty H A.initial_nonempty hempty⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
