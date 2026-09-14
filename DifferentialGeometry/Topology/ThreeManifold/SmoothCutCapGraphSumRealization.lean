import DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentPieceGluing
import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumLocalization
import DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalGraphSumRealizationReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountAbelianizationRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutCapSummandCountDeterminedOnCutComponents : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∀ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      E.CompleteEnumeration C L →
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) →
      K.length = (E.cutIndices C).card + 1 - L.length

theorem cutCapSummandCountDeterminedOnCutComponents_of_cutCapSummandCountDetermined
    (h : E.cutCapSummandCountDetermined) : E.cutCapSummandCountDeterminedOnCutComponents :=
  fun C _ => h C

theorem cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDeterminedOnCutComponents) :
    E.cutComponentRealization := by
  intro C hC L hL
  obtain ⟨K, hKfac, hdiff⟩ := hglue C hC L hL
  exact ⟨K, hcount C hC L K hL hKfac hdiff, hKfac, hdiff⟩

theorem componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDeterminedOnCutComponents) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_cutComponentRealization.mpr
    (E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
      hglue hcount)

theorem graphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDeterminedOnCutComponents) :
    E.graphSumRealization :=
  E.graphSumRealization_iff_cutComponentRealization.mpr
    (E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
      hglue hcount)

theorem sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDeterminedOnCutComponents) :
    E.sphericalGraphSumRealization S :=
  E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS
    (E.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
      hglue hcount)

theorem cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_componentConnectedSumDecomposition_of_cutCapFactorAbelianizationRationalFinite
    (h : E.componentConnectedSumDecomposition)
    (hfin : E.cutCapFactorAbelianizationRationalFinite) :
    E.cutComponentGluing ∧ E.cutCapSummandCountDeterminedOnCutComponents :=
  ⟨E.cutComponentGluing_of_cutComponentRealization
      (E.cutComponentRealization_of_componentConnectedSumDecomposition h),
    E.cutCapSummandCountDeterminedOnCutComponents_of_cutCapSummandCountDetermined
      (E.cutCapSummandCountDetermined_of_graphSumRealization_of_cutCapFactorAbelianizationRationalFinite
        (E.graphSumRealization_of_componentConnectedSumDecomposition h) hfin)⟩

theorem componentConnectedSumDecomposition_iff_cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_cutCapFactorAbelianizationRationalFinite
    (hfin : E.cutCapFactorAbelianizationRationalFinite) :
    E.componentConnectedSumDecomposition ↔
      E.cutComponentGluing ∧ E.cutCapSummandCountDeterminedOnCutComponents :=
  ⟨fun h =>
      E.cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_componentConnectedSumDecomposition_of_cutCapFactorAbelianizationRationalFinite
        h hfin,
    fun h =>
      E.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
        h.1 h.2⟩

theorem graphSumRealization_iff_cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_cutCapFactorAbelianizationRationalFinite
    (hfin : E.cutCapFactorAbelianizationRationalFinite) :
    E.graphSumRealization ↔
      E.cutComponentGluing ∧ E.cutCapSummandCountDeterminedOnCutComponents :=
  (E.graphSumRealization_iff_componentConnectedSumDecomposition).trans
    (E.componentConnectedSumDecomposition_iff_cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_cutCapFactorAbelianizationRationalFinite
      hfin)

theorem sphericalGraphSumRealization_iff_cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_cutCapFactorAbelianizationRationalFinite
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hfin : E.cutCapFactorAbelianizationRationalFinite) :
    E.sphericalGraphSumRealization S ↔
      E.cutComponentGluing ∧ E.cutCapSummandCountDeterminedOnCutComponents :=
  (E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S hS).trans
    (E.componentConnectedSumDecomposition_iff_cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_cutCapFactorAbelianizationRationalFinite
      hfin)

theorem cutComponentGluing_of_cutComponentPieceGluing
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (h : E.cutComponentPieceGluing S) : E.cutComponentGluing :=
  E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr
    ((E.cutComponentCanonicalGluing_iff_sphericalSummandCompletion S hS).mpr
      ((E.sphericalSummandCompletion_iff_cutComponentPieceGluing S hinj).mpr h))

theorem componentConnectedSumDecomposition_of_cutComponentPieceGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (hpiece : E.cutComponentPieceGluing S)
    (hcount : E.cutCapSummandCountDeterminedOnCutComponents) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (E.cutComponentGluing_of_cutComponentPieceGluing S hS hinj hpiece) hcount

theorem cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_isEmpty_index
    [IsEmpty E.tubes.Index] :
    E.cutComponentGluing ∧ E.cutCapSummandCountDeterminedOnCutComponents :=
  ⟨E.cutComponentGluing_of_forall_cutIndices_eq_empty
      fun C => E.cutIndices_eq_empty_of_isEmpty_index C,
    fun C hC => absurd (E.cutIndices_eq_empty_of_isEmpty_index C) hC⟩

theorem componentConnectedSumDecomposition_of_isEmpty_tubeIndex [IsEmpty E.tubes.Index] :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (E.cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_isEmpty_index).1
    (E.cutComponentGluing_and_cutCapSummandCountDeterminedOnCutComponents_of_isEmpty_index).2

end SphericalCutCapTransition

theorem not_finiteConnectedSumSummandCountUniqueRaw
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    ¬ finiteConnectedSumSummandCountUniqueRaw L := by
  intro h
  have hlen := h [] [standardThreeSphereLift.{u}] (by
    simpa using (finiteConnectedSum_append_standardThreeSphereLift L).map fun ρ => ρ.symm)
  simp at hlen

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology (SphericalCutCapTransition)

variable {P Q D N : OrientedThreeStage.{u}} {a s : ℝ}

theorem SmoothCutCapTransition.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (hglue : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutComponentGluing)
    (hcount : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutCapSummandCountDeterminedOnCutComponents) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition X h).componentConnectedSumDecomposition :=
  SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    _ hglue hcount

theorem SmoothCutCapTransition.graphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (hglue : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutComponentGluing)
    (hcount : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutCapSummandCountDeterminedOnCutComponents) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition X h).graphSumRealization :=
  SphericalCutCapTransition.graphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    _ hglue hcount

theorem SmoothCutCapTransition.sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hglue : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutComponentGluing)
    (hcount : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutCapSummandCountDeterminedOnCutComponents) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition X h).sphericalGraphSumRealization S :=
  SphericalCutCapTransition.sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDeterminedOnCutComponents
    _ S hS hglue hcount

theorem SmoothCutCapTransition.componentConnectedSumDecomposition_of_cutComponentPieceGluing_of_cutCapSummandCountDeterminedOnCutComponents
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hinj : ∀ C : ConnectedComponents P.toClosedOrientedManifold.Carrier,
      Function.Injective ((SphericalCutCapTransition.ofSmoothCutCapTransition X h).cappedFactor C))
    (hpiece : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutComponentPieceGluing S)
    (hcount : (SphericalCutCapTransition.ofSmoothCutCapTransition X h).cutCapSummandCountDeterminedOnCutComponents) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition X h).componentConnectedSumDecomposition :=
  SphericalCutCapTransition.componentConnectedSumDecomposition_of_cutComponentPieceGluing_of_cutCapSummandCountDeterminedOnCutComponents
    _ S hS hinj hpiece hcount

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
