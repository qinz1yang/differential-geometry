import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.GraphSumGluingReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricEvent

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

namespace MetricCutCapEvent

variable {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3} {a s : ℝ}

def sphericalGraphSumRealization (E : MetricCutCapEvent M Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  E.transition.sphericalGraphSumRealization S

theorem sphericalGraphSumRealization_iff (E : MetricCutCapEvent M Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) :
    E.sphericalGraphSumRealization S ↔ E.transition.sphericalGraphSumRealization S :=
  Iff.rfl

theorem sphericalGraphSumRealization_of_isEmpty_index (E : MetricCutCapEvent M Q a s)
    [IsEmpty E.transition.tubes.Index] (hr : E.transition.NoTubeRealization)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S) :
    E.sphericalGraphSumRealization S :=
  E.transition.sphericalGraphSumRealization_of_isEmpty_index hr S hS

theorem isEmpty_of_isEmpty (h : IsEmpty M.Carrier) : IsEmpty (MetricCutCapEvent M Q a s) :=
  ⟨fun E => E.transition.source_nonempty.elim h.false⟩

theorem isEmpty_of_not_lt (h : ¬ a < s) : IsEmpty (MetricCutCapEvent M Q a s) :=
  ⟨fun E => h E.incoming.lt⟩

end MetricCutCapEvent

def EventSphericalGraphSumRealization
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3) (a s : ℝ)
    (E : MetricCutCapEvent M Q a s), E.sphericalGraphSumRealization S

theorem eventSphericalGraphSumRealization_iff
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) :
    EventSphericalGraphSumRealization S ↔
      ∀ (M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3) (a s : ℝ)
        (E : MetricCutCapEvent M Q a s), E.transition.sphericalGraphSumRealization S :=
  Iff.rfl

theorem eventSphericalGraphSumRealization_of_transition
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ (M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
      (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q),
      E.sphericalGraphSumRealization S) :
    EventSphericalGraphSumRealization S :=
  fun M Q _ _ E => h M Q E.transition

theorem eventSphericalGraphSumRealization_iff_forall_transition_of_realization
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hreal : ∀ (M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
      (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q),
      ∃ a s : ℝ, ∃ E' : MetricCutCapEvent M Q a s, E'.transition = E) :
    EventSphericalGraphSumRealization S ↔
      ∀ (M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
        (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q),
        E.sphericalGraphSumRealization S := by
  constructor
  · intro h M Q E
    obtain ⟨a, s, E', hE'⟩ := hreal M Q E
    rw [← hE']
    exact h M Q a s E'
  · intro h M Q a s E
    exact h M Q E.transition

namespace MetricCutCapEvent

variable {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3} {s : ℝ}

noncomputable def toFiniteSurgeryHistory (E : MetricCutCapEvent M Q 0 s) :
    FiniteSurgeryHistory.{u} where
  eventCount := 1
  eventCount_pos := Nat.one_pos
  time := fun i => if (i : ℕ) = 0 then 0 else s
  time_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp_all
    · simpa using E.incoming.lt
    · simp_all
    · simp_all
  time_zero := rfl
  stage := Fin.cases M (fun _ => Q)
  initialMetric := Fin.cases (E.incoming.flow.base.metric 0) (fun _ => E.outputMetric)
  event := fun i => Fin.cases E (fun j => Fin.elim0 j) i
  event_initial := by
    intro i
    fin_cases i
    rfl
  event_output := by
    intro i
    fin_cases i
    rfl

theorem toFiniteSurgeryHistory_event (E : MetricCutCapEvent M Q 0 s) :
    E.toFiniteSurgeryHistory.event ⟨0, Nat.one_pos⟩ = E := rfl

theorem toFiniteSurgeryHistory_cutCapTrace_transition (E : MetricCutCapEvent M Q 0 s) :
    E.toFiniteSurgeryHistory.cutCapTrace.transition ⟨0, Nat.one_pos⟩ = E.transition :=
  congrArg MetricCutCapEvent.transition E.toFiniteSurgeryHistory_event

theorem sphericalGraphSumRealization_of_forall_cutCapTrace
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).sphericalGraphSumRealization S)
    (E : MetricCutCapEvent M Q 0 s) : E.transition.sphericalGraphSumRealization S := by
  rw [← E.toFiniteSurgeryHistory_cutCapTrace_transition]
  exact h _ _

end MetricCutCapEvent

namespace FiniteSurgeryHistory

variable (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)

theorem sphericalGraphSumRealization_of_eventSphericalGraphSumRealization
    (h : EventSphericalGraphSumRealization S) (H : FiniteSurgeryHistory.{u}) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).sphericalGraphSumRealization S :=
  fun i => h _ _ _ _ (H.event i)

theorem componentConnectedSumDecomposition_of_eventSphericalGraphSumRealization
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (h : EventSphericalGraphSumRealization S) (H : FiniteSurgeryHistory.{u}) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).componentConnectedSumDecomposition :=
  fun i =>
    (H.cutCapTrace.transition i).componentConnectedSumDecomposition_of_sphericalGraphSumRealization
      S hS (h _ _ _ _ (H.event i))

end FiniteSurgeryHistory

theorem smoothPoincareConjecture_of_eventSphericalGraphSumRealization
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (h : EventSphericalGraphSumRealization S)
    (hext : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} :=
  Topology.smoothPoincareConjecture_of_sphericalGraphSumRealization S hS
    (fun H i => h _ _ _ _ (H.event i)) hext

end DifferentialGeometry.PDE.RicciFlow.Surgery
