import DifferentialGeometry.Geometry.Thurston.NonemptyGeometricPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
namespace GC.Surgery
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Geometry
set_option autoImplicit false
noncomputable section
universe u

theorem metric_event_discarded_geometry
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (h : E.poincareStandardDiscarded)
    (C : ConnectedComponents E.discarded.Carrier) :
    Nonempty (StandardGeometricPresentation
      (E.discarded.toClosedOrientedManifold.component C).toClosedOrientedManifold) := by
  obtain ⟨P⟩ := h C
  obtain ⟨G,-⟩ := standard_geometric_presentation
    (E.discarded.toClosedOrientedManifold.component C) P
  exact ⟨G⟩

theorem spherical_event_discarded_geometry
    {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) (h : E.poincareControlled)
    (C : ConnectedComponents E.discarded.Carrier) :
    Nonempty (StandardGeometricPresentation
      (E.discarded.component C).toClosedOrientedManifold) := by
  obtain ⟨P⟩ := h C
  obtain ⟨G,-⟩ := standard_geometric_presentation (E.discarded.component C) P
  exact ⟨G⟩

theorem observed_history_discarded_geometry
    (H : ObservedHistory.{u})
    (h : ∀ i : Fin H.eventCount, (H.event i).poincareStandardDiscarded) :
    ∀ (i : Fin H.eventCount)
      (C : ConnectedComponents (H.event i).discarded.Carrier),
      Nonempty (StandardGeometricPresentation
        ((H.event i).discarded.toClosedOrientedManifold.component C).toClosedOrientedManifold) :=
  fun i C => metric_event_discarded_geometry (H.event i) (h i) C

theorem tower_observation_discarded_geometry
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (h : T.hasPoincareStandardDiscarded)
    (b : ℝ) (hb : 0 ≤ b) :
    ∀ (i : Fin (T.toObservationTower.observe b hb).eventCount)
      (C : ConnectedComponents ((T.toObservationTower.observe b hb).event i).discarded.Carrier),
      Nonempty (StandardGeometricPresentation
        (((T.toObservationTower.observe b hb).event i).discarded.toClosedOrientedManifold.component C).toClosedOrientedManifold) :=
  observed_history_discarded_geometry (T.toObservationTower.observe b hb)
    (T.poincareStandardDiscarded_toObservationTower h b hb)

end
end GC.Surgery
