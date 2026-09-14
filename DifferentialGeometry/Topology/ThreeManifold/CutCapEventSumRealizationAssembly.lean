import DifferentialGeometry.Topology.ThreeManifold.CutCapFrontierCanonicalReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapGluingPresentation
import DifferentialGeometry.Topology.ThreeManifold.CutCapLocalReconstructionReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountInvariance
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift
import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutComponentRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def finiteConnectedSumSummandCountUniqueRaw
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  ∀ (K K' : List (ConnectedClosedOrientedManifold.{u} 3)),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K')).toClosedOrientedManifold) →
    K.length = K'.length

theorem not_finiteConnectedSumSummandCountUniqueRaw_nil :
    ¬ finiteConnectedSumSummandCountUniqueRaw
      ([] : List (ConnectedClosedOrientedManifold.{u} 3)) := by
  intro h
  have hlen := h [] [standardThreeSphereLift.{u}]
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  simp at hlen

theorem not_forall_finiteConnectedSumSummandCountUniqueRaw :
    ¬ (∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
        finiteConnectedSumSummandCountUniqueRaw L) :=
  fun h => not_finiteConnectedSumSummandCountUniqueRaw_nil (h _)

theorem exists_isSphereTwoTimesCircleFactor_zero :
    ∃ S : ConnectedClosedOrientedManifold.{0} 3, isSphereTwoTimesCircleFactor S :=
  ⟨sphereTwoTimesCircleLift, isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift⟩

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3}

def cutCapSummandFrontier (E : SphericalCutCapTransition M Q) : Prop :=
  E.NoTubeRealization ∧ E.cutComponentGluing ∧ E.cutCapSummandCountDetermined

theorem cutCapSummandFrontier_of_noTube_of_gluing_of_count
    (E : SphericalCutCapTransition M Q) (hnoTube : E.NoTubeRealization)
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.cutCapSummandFrontier :=
  ⟨hnoTube, hglue, hcount⟩

theorem noTubeRealization_of_cutCapSummandFrontier (E : SphericalCutCapTransition M Q)
    (h : E.cutCapSummandFrontier) : E.NoTubeRealization :=
  h.1

theorem cutComponentGluing_of_cutCapSummandFrontier (E : SphericalCutCapTransition M Q)
    (h : E.cutCapSummandFrontier) : E.cutComponentGluing :=
  h.2.1

theorem cutCapSummandCountDetermined_of_cutCapSummandFrontier
    (E : SphericalCutCapTransition M Q) (h : E.cutCapSummandFrontier) :
    E.cutCapSummandCountDetermined :=
  h.2.2

theorem componentConnectedSumDecomposition_of_cutCapSummandFrontier
    (E : SphericalCutCapTransition M Q) (h : E.cutCapSummandFrontier) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
    ⟨h.1, E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      h.2.1 h.2.2⟩

theorem hsum_of_event_data (E : SphericalCutCapTransition M Q)
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hnoTube : E.NoTubeRealization) (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDetermined) : E.sphericalGraphSumRealization S :=
  E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS
    (E.componentConnectedSumDecomposition_of_cutCapSummandFrontier
      (E.cutCapSummandFrontier_of_noTube_of_gluing_of_count hnoTube hglue hcount))

theorem sphericalGraphSumRealization_of_cutCapSummandFrontier
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) (h : E.cutCapSummandFrontier) :
    E.sphericalGraphSumRealization S :=
  E.hsum_of_event_data S hS h.1 h.2.1 h.2.2

theorem hsum_of_event_data_of_uncutCappingRealization
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) (hcap : E.UncutCappingRealization)
    (hpres : E.CappedPresentationRealization) (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDetermined) : E.sphericalGraphSumRealization S :=
  E.hsum_of_event_data S hS
    (E.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization hcap hpres)
    hglue hcount

theorem hsum_of_event_data_of_uncutCappingRealization_of_retained_of_discarded
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) (hcap : E.UncutCappingRealization)
    (hret : E.CappedRetainedPresentationRealization)
    (hdisc : E.CappedDiscardedPresentationRealization)
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.sphericalGraphSumRealization S :=
  E.hsum_of_event_data_of_uncutCappingRealization S hS hcap
    (E.cappedPresentationRealization_of_retained_of_discarded hret hdisc) hglue hcount

theorem sphericalGraphSumRealization_iff_cutCapSummandFrontier_of_summandCountUnique
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S)
    (huniq : ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
      finiteConnectedSumSummandCountUnique L) :
    E.sphericalGraphSumRealization S ↔ E.cutCapSummandFrontier := by
  constructor
  · intro hex
    exact ⟨E.noTubeRealization_of_componentConnectedSumDecomposition
        (E.componentConnectedSumDecomposition_of_sphericalGraphSumRealization S hS hex),
      E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr
        (E.cutComponentCanonicalGluing_of_sphericalGraphSumRealization hS hex),
      E.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_summandCountUnique
        hS hex huniq⟩
  · exact E.sphericalGraphSumRealization_of_cutCapSummandFrontier S hS

theorem cutComponentRealization_of_cutCapSummandFrontier
    (E : SphericalCutCapTransition M Q) (h : E.cutCapSummandFrontier) :
    E.cutComponentRealization :=
  E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined h.2.1 h.2.2

theorem localReconstruction_of_cutCapSummandFrontier
    (E : SphericalCutCapTransition M Q) (h : E.cutCapSummandFrontier) :
    E.localReconstruction :=
  E.localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    h.1 h.2.1 h.2.2

end SphericalCutCapTransition

end DifferentialGeometry.Topology

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
