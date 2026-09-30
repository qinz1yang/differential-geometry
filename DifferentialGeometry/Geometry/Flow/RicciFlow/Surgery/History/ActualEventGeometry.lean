import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MarkedDiscardedGeometry
namespace GC.Surgery
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Geometry
set_option autoImplicit false
noncomputable section
universe u

def HasMarkedDiscardedReconstruction
    {M Q : ClosedOrientedManifold.{u} 3}
    (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q) : Prop :=
    ∃ R : CutCapSumData E,
      Function.Bijective (presentationComponentEquiv E ∘ componentSlot R) ∧
      ∀ s : (Σ w : R.Group, Fin (R.factors w).length),
        (∃ q : Q.Carrier,
          presentationComponentEquiv E (componentSlot R s) = ConnectedComponents.mk (Sum.inl q) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (E.capped.component (componentSlot R s)).toClosedOrientedManifold
            (Q.component (ConnectedComponents.mk q)).toClosedOrientedManifold)) ∨
        ∃ D : DiscardedSlotGeometry E (componentSlot R s),
          D.atCap.presentation.diffeomorph =
            D.comparison.trans D.geometric.presentation.diffeomorph ∧
          Nonempty (Fin D.atCap.presentation.factors.length)

def ActualMetricEventGeometry
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) : Prop :=
  ∃ hc : SmoothCutCapCompletion E.transition,
    let X := DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc
    HasMarkedDiscardedReconstruction X ∧
    (X.presentation : E.capped.Carrier → Q.Carrier ⊕ E.discarded.Carrier) = E.transition.presentation ∧
    (∀ x : E.transition.trace.tubes.core,
      X.capping.coreInclusion x = E.transition.trace.capping.coreInclusion x) ∧
    ∀ C : ConnectedComponents E.discarded.Carrier,
      Nonempty (StandardGeometricPresentation
        (E.discarded.toClosedOrientedManifold.component C).toClosedOrientedManifold)

theorem actual_metric_event_geometry
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    (hbfr : E.transition.boundaryFrameReversing)
    (hctrl : E.poincareStandardDiscarded) : ActualMetricEventGeometry E := by
  let hc := E.transition.toSmoothCutCapCompletion hbfr
  let X := DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc
  have hx : X.poincareControlled :=
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition_poincareControlled E.transition hc hctrl
  refine ⟨hc,marked_reconstruction_with_discarded_geometry X hx,rfl,?_,?_⟩
  · exact hc.coreInclusion_eq
  · exact metric_event_discarded_geometry E hctrl

end
end GC.Surgery
