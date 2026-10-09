import DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentGluingReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutCappingRealization
import DifferentialGeometry.Topology.ThreeManifold.PartialRealizationStepQuotient
import DifferentialGeometry.Topology.ThreeManifold.CutCapFrontierCanonicalReduction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

structure CutComponentCollaredQuotientRealization : Prop where
  quotient : ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∃ N : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold)

theorem cutComponentCollaredQuotientRealization_of_self :
    E.CutComponentCollaredQuotientRealization :=
  ⟨fun C _ => ⟨M.component C, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩⟩

theorem cutComponentCollaredQuotientRealization_of_cutComponentGluing :
    E.cutComponentGluing → E.CutComponentCollaredQuotientRealization :=
  fun _ => E.cutComponentCollaredQuotientRealization_of_self

theorem not_collaredQuotientRealization_determines_blockLength :
    ¬ (∀ (N : ConnectedClosedOrientedManifold.{u} 3)
      (K K' : List (ConnectedClosedOrientedManifold.{u} 3)),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        N.toClosedOrientedManifold (finiteConnectedSum K).toClosedOrientedManifold) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        N.toClosedOrientedManifold (finiteConnectedSum K').toClosedOrientedManifold) →
      K.length = K'.length) := by
  intro h
  have hlen := h standardThreeSphereLift.{u} [standardThreeSphereLift.{u}] []
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  simp only [List.length_singleton, List.length_nil] at hlen
  exact absurd hlen (by decide)

structure CutComponentSingleTubeCollaredQuotientGluing : Prop where
  quotient : ∀ (C : ConnectedComponents M.Carrier), (E.cutIndices C).card = 1 →
    ∃ (N : ConnectedClosedOrientedManifold.{u} 3)
      (K : List (ConnectedClosedOrientedManifold.{u} 3)),
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        N.toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

theorem cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing
    (h : E.CutComponentSingleTubeCollaredQuotientGluing) :
    E.cutComponentSingleTubeGluing := by
  intro C hcard
  obtain ⟨N, K, hKfac, ⟨ρ₁⟩, ⟨ρ₂⟩⟩ := h.quotient C hcard
  exact ⟨K, hKfac, ⟨ρ₁.trans ρ₂⟩⟩

structure CutComponentCollaredQuotientGluing : Prop where
  quotient : ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3)), E.CompleteEnumeration C L →
      ∃ (N : ConnectedClosedOrientedManifold.{u} 3)
        (K : List (ConnectedClosedOrientedManifold.{u} 3)),
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          N.toClosedOrientedManifold (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

theorem cutComponentGluing_of_cutComponentCollaredQuotientGluing
    (h : E.CutComponentCollaredQuotientGluing) : E.cutComponentGluing := by
  intro C hC L hL
  obtain ⟨N, K, hKfac, ⟨ρ₁⟩, ⟨ρ₂⟩⟩ := h.quotient C hC L hL
  exact ⟨K, hKfac, ⟨ρ₁.trans ρ₂⟩⟩

theorem cutComponentCollaredQuotientGluing_of_cutComponentGluing
    (h : E.cutComponentGluing) : E.CutComponentCollaredQuotientGluing := by
  refine ⟨fun C hC L hL => ?_⟩
  obtain ⟨K, hKfac, ⟨ρ⟩⟩ := h C hC L hL
  exact ⟨M.component C, K, hKfac,
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩, ⟨ρ⟩⟩

theorem cutComponentGluing_iff_cutComponentCollaredQuotientGluing :
    E.cutComponentGluing ↔ E.CutComponentCollaredQuotientGluing :=
  ⟨E.cutComponentCollaredQuotientGluing_of_cutComponentGluing,
    E.cutComponentGluing_of_cutComponentCollaredQuotientGluing⟩

theorem cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing
    (h : E.CutComponentCollaredQuotientGluing) :
    E.CutComponentSingleTubeCollaredQuotientGluing := by
  refine ⟨fun C hcard => ?_⟩
  have hC : E.cutIndices C ≠ ∅ := by
    rintro h0
    rw [h0] at hcard
    simp at hcard
  exact h.quotient C hC (E.canonicalEnumeration C)
    (E.completeEnumeration_canonicalEnumeration C)

theorem cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentGluing
    (h : E.cutComponentGluing) : E.CutComponentSingleTubeCollaredQuotientGluing :=
  E.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing
    (E.cutComponentCollaredQuotientGluing_of_cutComponentGluing h)

theorem cutComponentGluing_of_cutComponentSingleTubeCollaredQuotientGluing_of_subsingleton_index
    [Subsingleton E.tubes.Index] (h : E.CutComponentSingleTubeCollaredQuotientGluing) :
    E.cutComponentGluing :=
  E.cutComponentGluing_of_cutComponentSingleTubeGluing_of_subsingleton_index
    (E.cutComponentSingleTubeGluing_of_cutComponentSingleTubeCollaredQuotientGluing h)

theorem cutComponentCollaredQuotientGluing_of_isEmpty_index [IsEmpty E.tubes.Index] :
    E.CutComponentCollaredQuotientGluing :=
  E.cutComponentCollaredQuotientGluing_of_cutComponentGluing
    (E.cutComponentGluing_of_forall_cutIndices_eq_empty fun C =>
      E.cutIndices_eq_empty_of_isEmpty_index C)

theorem cutComponentSingleTubeCollaredQuotientGluing_of_isEmpty_index
    [IsEmpty E.tubes.Index] : E.CutComponentSingleTubeCollaredQuotientGluing :=
  E.cutComponentSingleTubeCollaredQuotientGluing_of_cutComponentCollaredQuotientGluing
    E.cutComponentCollaredQuotientGluing_of_isEmpty_index

structure CutComponentCollaredQuotientGluingBridge where
  graph : MarkedManifoldGraph.{u}
  zFactor : ConnectedClosedOrientedManifold.{u} 3
  zFactor_sphere : isSphereTwoTimesCircleFactor zFactor
  realized : PartialRealization graph Finset.univ
  realized_blockInvariant : realized.IsBlockInvariant zFactor
  vertexOf : ConnectedComponents M.Carrier → graph.Vertex
  blockEnumeration : ∀ C : ConnectedComponents M.Carrier,
    E.CompleteEnumeration C (graph.vertexBlockList Finset.univ (vertexOf C))
  componentDiffeo : ∀ (C : ConnectedComponents M.Carrier)
    (y : graph.puncturedCarrier Finset.univ (vertexOf C)),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (realized.realization.component
          (ConnectedComponents.mk (realized.vertexPiece (vertexOf C) y))).toClosedOrientedManifold)

theorem cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge
    (h : E.CutComponentCollaredQuotientGluingBridge) :
    E.CutComponentCollaredQuotientGluing := by
  obtain ⟨b, -, hb⟩ := h.realized_blockInvariant.2.1
  refine ⟨fun C _ L hL => ?_⟩
  obtain ⟨y⟩ := MarkedManifoldGraph.nonempty_puncturedCarrier h.graph Finset.univ (h.vertexOf C)
  refine ⟨h.realized.realization.component
      (ConnectedComponents.mk (h.realized.vertexPiece (h.vertexOf C) y)),
    List.replicate (b (h.vertexOf C)) h.zFactor, ?_, h.componentDiffeo C y, ?_⟩
  · intro F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact h.zFactor_sphere
  · obtain ⟨ρ₂⟩ := hb (h.vertexOf C) y
    obtain ⟨ρ₃⟩ := finiteConnectedSum_perm
      ((E.completeEnumeration_perm (h.blockEnumeration C) hL).append_right
        (List.replicate (b (h.vertexOf C)) h.zFactor))
    exact ⟨ρ₂.trans ρ₃⟩

theorem cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge
    (h : E.CutComponentCollaredQuotientGluingBridge) : E.cutComponentGluing :=
  E.cutComponentGluing_of_cutComponentCollaredQuotientGluing
    (E.cutComponentCollaredQuotientGluing_of_cutComponentCollaredQuotientGluingBridge h)

def cutComponentCollaredQuotientGluingBridgeOfSeamEquation
    (graph : MarkedManifoldGraph.{u}) (zFactor : ConnectedClosedOrientedManifold.{u} 3)
    (zFactor_sphere : isSphereTwoTimesCircleFactor zFactor)
    (realized : PartialRealization graph Finset.univ)
    {e : graph.Edge} (he : e ∈ (Finset.univ : Finset graph.Edge))
    (hcover : realized.FlagCovered e) (hseam : realized.SeamEquation e he)
    (hcorr : realized.componentCorrespondence) (hpres : realized.HasBlockPresentation zFactor)
    (vertexOf : ConnectedComponents M.Carrier → graph.Vertex)
    (blockEnumeration : ∀ C : ConnectedComponents M.Carrier,
      E.CompleteEnumeration C (graph.vertexBlockList Finset.univ (vertexOf C)))
    (componentDiffeo : ∀ (C : ConnectedComponents M.Carrier)
      (y : graph.puncturedCarrier Finset.univ (vertexOf C)),
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (realized.realization.component
            (ConnectedComponents.mk (realized.vertexPiece (vertexOf C) y))).toClosedOrientedManifold)) :
    E.CutComponentCollaredQuotientGluingBridge :=
  ⟨graph, zFactor, zFactor_sphere, realized,
    PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation he hcover hseam hcorr hpres,
    vertexOf, blockEnumeration, componentDiffeo⟩

theorem cutComponentGluing_of_seamData
    (graph : MarkedManifoldGraph.{u}) (zFactor : ConnectedClosedOrientedManifold.{u} 3)
    (zFactor_sphere : isSphereTwoTimesCircleFactor zFactor)
    (realized : PartialRealization graph Finset.univ)
    {e : graph.Edge} (he : e ∈ (Finset.univ : Finset graph.Edge))
    (hcover : realized.FlagCovered e) (hseam : realized.SeamEquation e he)
    (hcorr : realized.componentCorrespondence) (hpres : realized.HasBlockPresentation zFactor)
    (vertexOf : ConnectedComponents M.Carrier → graph.Vertex)
    (blockEnumeration : ∀ C : ConnectedComponents M.Carrier,
      E.CompleteEnumeration C (graph.vertexBlockList Finset.univ (vertexOf C)))
    (componentDiffeo : ∀ (C : ConnectedComponents M.Carrier)
      (y : graph.puncturedCarrier Finset.univ (vertexOf C)),
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (realized.realization.component
            (ConnectedComponents.mk (realized.vertexPiece (vertexOf C) y))).toClosedOrientedManifold)) :
    E.cutComponentGluing :=
  E.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge
    (E.cutComponentCollaredQuotientGluingBridgeOfSeamEquation graph zFactor zFactor_sphere
      realized he hcover hseam hcorr hpres vertexOf blockEnumeration componentDiffeo)

theorem componentConnectedSumDecomposition_of_cutComponentCollaredQuotientGluingBridge
    (h : E.CutComponentCollaredQuotientGluingBridge) (hcount : E.cutCapSummandCountDetermined) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    E.noTubeRealization (E.cutComponentGluing_of_cutComponentCollaredQuotientGluingBridge h) hcount

end SphericalCutCapTransition

end DifferentialGeometry.Topology
