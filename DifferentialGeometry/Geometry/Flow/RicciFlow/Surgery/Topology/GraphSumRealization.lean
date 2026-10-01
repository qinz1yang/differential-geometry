import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Topology.ThreeManifold.SmoothCutCapGraphSumRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology (SphericalCutCapTransition)

variable {P Q D N : OrientedThreeStage.{u}} {a s : ℝ}

namespace RetainedCoreEventData

theorem componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (R : RetainedCoreEventData P Q a s)
    (hglue : (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).cutComponentGluing)
    (hcount : (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).cutCapSummandCountDeterminedOnCutComponents) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).componentConnectedSumDecomposition :=
  R.transition.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    R.completion hglue hcount

theorem graphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (R : RetainedCoreEventData P Q a s)
    (hglue : (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).cutComponentGluing)
    (hcount : (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).cutCapSummandCountDeterminedOnCutComponents) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).graphSumRealization :=
  R.transition.graphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    R.completion hglue hcount

theorem sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (R : RetainedCoreEventData P Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hglue : (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).cutComponentGluing)
    (hcount : (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).cutCapSummandCountDeterminedOnCutComponents) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition R.transition R.completion).sphericalGraphSumRealization S :=
  R.transition.sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    R.completion S hS hglue hcount

end RetainedCoreEventData

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.Topology (SphericalCutCapTransition)

theorem metricCutCapEvent_hsum_of_event_data
    {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3} {a s : ℝ}
    (E : MetricCutCapEvent M Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hnoTube : E.transition.NoTubeRealization)
    (hglue : E.transition.cutComponentGluing)
    (hcount : E.transition.cutCapSummandCountDetermined) :
    E.transition.sphericalGraphSumRealization S :=
  SphericalCutCapTransition.hsum_of_event_data E.transition S hS hnoTube hglue hcount

theorem metricCutCapEvent_hsum_of_frontier
    {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3} {a s : ℝ}
    (E : MetricCutCapEvent M Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (h : SphericalCutCapTransition.cutCapSummandFrontier E.transition) :
    E.transition.sphericalGraphSumRealization S :=
  SphericalCutCapTransition.sphericalGraphSumRealization_of_cutCapSummandFrontier
    E.transition S hS h

theorem metricCutCapEvent_hsum_of_capping_and_presentation
    {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3} {a s : ℝ}
    (E : MetricCutCapEvent M Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hcap : E.transition.UncutCappingRealization)
    (hpres : E.transition.CappedPresentationRealization)
    (hglue : E.transition.cutComponentGluing)
    (hcount : E.transition.cutCapSummandCountDetermined) :
    E.transition.sphericalGraphSumRealization S :=
  SphericalCutCapTransition.hsum_of_event_data_of_uncutCappingRealization
    E.transition S hS hcap hpres hglue hcount

theorem finiteSurgeryHistory_cutCapTrace_transition_eq_event
    (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount) :
    H.cutCapTrace.transition i = (H.event i).transition := rfl

theorem finiteSurgeryHistory_event_hsum_of_event_data
    (H : FiniteSurgeryHistory.{u})
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hnoTube : ∀ i : Fin H.eventCount, (H.event i).transition.NoTubeRealization)
    (hglue : ∀ i : Fin H.eventCount, (H.event i).transition.cutComponentGluing)
    (hcount : ∀ i : Fin H.eventCount, (H.event i).transition.cutCapSummandCountDetermined) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).sphericalGraphSumRealization S :=
  fun i => metricCutCapEvent_hsum_of_event_data (H.event i) S hS (hnoTube i) (hglue i)
    (hcount i)

theorem finiteSurgeryHistory_event_hsum_of_capping_and_presentation
    (H : FiniteSurgeryHistory.{u})
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hcap : ∀ i : Fin H.eventCount, (H.event i).transition.UncutCappingRealization)
    (hpres : ∀ i : Fin H.eventCount, (H.event i).transition.CappedPresentationRealization)
    (hglue : ∀ i : Fin H.eventCount, (H.event i).transition.cutComponentGluing)
    (hcount : ∀ i : Fin H.eventCount, (H.event i).transition.cutCapSummandCountDetermined) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).sphericalGraphSumRealization S :=
  fun i => metricCutCapEvent_hsum_of_capping_and_presentation (H.event i) S hS
    (hcap i) (hpres i) (hglue i) (hcount i)

theorem finiteSurgeryHistory_componentConnectedSumDecomposition_of_event_data
    (H : FiniteSurgeryHistory.{u})
    (hnoTube : ∀ i : Fin H.eventCount, (H.event i).transition.NoTubeRealization)
    (hglue : ∀ i : Fin H.eventCount, (H.event i).transition.cutComponentGluing)
    (hcount : ∀ i : Fin H.eventCount, (H.event i).transition.cutCapSummandCountDetermined) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).componentConnectedSumDecomposition :=
  fun i =>
    SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutCapSummandFrontier
      (H.cutCapTrace.transition i)
      (SphericalCutCapTransition.cutCapSummandFrontier_of_noTube_of_gluing_of_count
        _ (hnoTube i) (hglue i) (hcount i))

end DifferentialGeometry.PDE.RicciFlow.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology (SphericalCutCapTransition)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem retainedCoreEventData_hsum_of_frontier
    (D : RetainedCoreEventData P Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (h : SphericalCutCapTransition.cutCapSummandFrontier
      (ofSmoothCutCapTransition D.transition D.completion)) :
    (ofSmoothCutCapTransition D.transition D.completion).sphericalGraphSumRealization S :=
  SphericalCutCapTransition.sphericalGraphSumRealization_of_cutCapSummandFrontier _ S hS h

theorem retainedCoreEventData_every_component_meets_core_of_completion
    (D : RetainedCoreEventData P Q a s) :
    ∀ c : ConnectedComponents Q.Carrier,
      ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition D.transition).core,
        ∃ q : Q.Carrier,
          (ofSmoothCutCapTransition D.transition D.completion).presentation
              ((ofSmoothCutCapTransition D.transition D.completion).capping.coreInclusion x) =
            Sum.inl q ∧ ConnectedComponents.mk q = c :=
  D.completion.every_component_meets_core

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

section

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.Topology (SphericalCutCapTransition)

theorem metricCutCapEvent_hsum_of_cutComponentGluing_of_cutCapSummandCountDetermined
    {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3} {a s : ℝ}
    (E : MetricCutCapEvent M Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hglue : E.transition.cutComponentGluing)
    (hcount : E.transition.cutCapSummandCountDetermined) :
    E.transition.sphericalGraphSumRealization S :=
  SphericalCutCapTransition.sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    E.transition S hS hglue hcount

theorem finiteSurgeryHistory_event_hsum_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (H : FiniteSurgeryHistory.{u})
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hglue : ∀ i : Fin H.eventCount, (H.event i).transition.cutComponentGluing)
    (hcount : ∀ i : Fin H.eventCount, (H.event i).transition.cutCapSummandCountDetermined) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).sphericalGraphSumRealization S :=
  fun i => metricCutCapEvent_hsum_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (H.event i) S hS (hglue i) (hcount i)

end DifferentialGeometry.PDE.RicciFlow.Surgery

end
