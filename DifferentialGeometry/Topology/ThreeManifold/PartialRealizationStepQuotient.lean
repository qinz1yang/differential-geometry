import DifferentialGeometry.Topology.ThreeManifold.MarkedBallTubeProducer
import DifferentialGeometry.Topology.ThreeManifold.PartialRealizationBlockCount
import DifferentialGeometry.Topology.ThreeManifold.PartialRealizationSeam

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × Set.Icc (-2 : ℝ) 2

private theorem connectedComponents_mk_map_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Continuous f) {a b : α}
    (h : (a : ConnectedComponents α) = (b : ConnectedComponents α)) :
    (f a : ConnectedComponents β) = (f b : ConnectedComponents β) := by
  rw [ConnectedComponents.coe_eq_coe'] at h ⊢
  exact IsPreconnected.subset_connectedComponent
    (isPreconnected_connectedComponent.image f hf.continuousOn)
    ⟨b, mem_connectedComponent, rfl⟩ ⟨a, h, rfl⟩

private instance instPreconnectedSpaceSetIcc (a b : ℝ) : PreconnectedSpace (Set.Icc a b) :=
  isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc

private instance instSubsingletonConnectedComponentsTube :
    Subsingleton (ConnectedComponents Tube) := inferInstance

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}}

theorem connectedComponents_mk_cylinderEnd {S : Finset G.Edge} {e : G.Edge}
    (P : PartialRealization G S) (he : e ∈ S) (h : P.SeamEquation e he) (b : Bool) (z : S²) :
    ConnectedComponents.mk (P.cylinderPiece e he (z, tubeEndLevel b)) =
      ConnectedComponents.mk
        (P.vertexPiece (G.endpoint e b) (G.flagBoundaryPoint S e b z)) := by
  cases b with
  | false => exact congrArg ConnectedComponents.mk (h.1 z)
  | true => exact congrArg ConnectedComponents.mk (h.2 z)

theorem exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece {S : Finset G.Edge}
    {e : G.Edge} (P : PartialRealization G S) (he : e ∈ S) (h : P.SeamEquation e he)
    (q : G.cylinderCarrier e) :
    ∃ (v : G.Vertex) (y : G.puncturedCarrier S v),
      ConnectedComponents.mk (P.cylinderPiece e he q) =
        ConnectedComponents.mk (P.vertexPiece v y) := by
  refine ⟨G.endpoint e false, G.flagBoundaryPoint S e false q.1, ?_⟩
  have hq : (q : ConnectedComponents (G.cylinderCarrier e)) =
      ((q.1, tubeEndLevel false) : ConnectedComponents (G.cylinderCarrier e)) :=
    Subsingleton.elim _ _
  rw [connectedComponents_mk_map_eq (P.cylinderPiece e he).continuous hq]
  exact connectedComponents_mk_cylinderEnd P he h false q.1

def FlagCovered {S : Finset G.Edge} (P : PartialRealization G S) (e : G.Edge) : Prop :=
  ∀ x : P.realization.Carrier,
    (∃ (v : G.Vertex) (y : G.puncturedCarrier S v), P.vertexPiece v y = x) ∨
      (∃ (he : e ∈ S) (q : G.cylinderCarrier e), P.cylinderPiece e he q = x)

theorem cylinderComponentCovering_of_flagCovered_of_seamEquation {S : Finset G.Edge}
    {e : G.Edge} {P : PartialRealization G S} (he : e ∈ S) (hcover : P.FlagCovered e)
    (h : P.SeamEquation e he) : P.CylinderComponentCovering := by
  intro x
  rcases hcover x with ⟨v, y, hy⟩ | ⟨he', q, hq⟩
  · exact ⟨v, y, by rw [hy]⟩
  · obtain ⟨v, y, hC⟩ := exists_connectedComponents_mk_cylinderPiece_eq_vertexPiece P he' h q
    exact ⟨v, y, by rw [← hq, hC]⟩

theorem isBlockInvariant_of_flagCovered_of_seamEquation {S : Finset G.Edge} {e : G.Edge}
    {Z : ConnectedClosedOrientedManifold.{u} 3} {P : PartialRealization G S} (he : e ∈ S)
    (hcover : P.FlagCovered e) (h : P.SeamEquation e he) (hcorr : P.componentCorrespondence)
    (hpres : P.HasBlockPresentation Z) : P.IsBlockInvariant Z :=
  ⟨hcorr, hpres, cylinderComponentCovering_of_flagCovered_of_seamEquation he hcover h⟩

end PartialRealization

structure CollaredQuotientStep (G : MarkedManifoldGraph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) : Prop where
  step : ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
    P.IsBlockInvariant Z →
      ∃ P' : PartialRealization G (insert e S),
        P'.FlagCovered e ∧ P'.SeamEquation e (Finset.mem_insert_self e S) ∧
          P'.componentCorrespondence ∧ P'.HasBlockPresentation Z

theorem hasRealizationStep_of_collaredQuotientStep {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : CollaredQuotientStep G Z) :
    HasRealizationStep G Z :=
  fun S P e he hP => by
    obtain ⟨P', hcover, hseam, hcorr, hpres⟩ := h.step S P e he hP
    exact ⟨P', PartialRealization.isBlockInvariant_of_flagCovered_of_seamEquation
      (Finset.mem_insert_self e S) hcover hseam hcorr hpres⟩

theorem blockStepLaw_of_collaredQuotientStep_of_initial {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    (h₀ : ∃ P : PartialRealization G ∅, P.IsBlockInvariant Z)
    (h : CollaredQuotientStep G Z) : BlockStepLaw G Z :=
  blockStepLaw_of_hasRealizationStep_of_initial h₀ (hasRealizationStep_of_collaredQuotientStep h)

theorem collaredQuotientStep_of_isEmpty {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} [IsEmpty G.Edge] :
    CollaredQuotientStep G Z :=
  ⟨fun _ _ e _ _ => isEmptyElim e⟩

theorem hasRealizationStep_of_isEmpty {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} [IsEmpty G.Edge] :
    HasRealizationStep G Z :=
  fun _ _ e _ _ => isEmptyElim e

theorem collaredQuotientStep_oneVertex (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    CollaredQuotientStep (MarkedManifoldGraph.oneVertex N) Z :=
  collaredQuotientStep_of_isEmpty

theorem collaredQuotientStep_twoVertexEmpty
    (N N' Z : ConnectedClosedOrientedManifold.{0} 3) :
    CollaredQuotientStep (MarkedManifoldGraph.twoVertexEmpty N N') Z :=
  collaredQuotientStep_of_isEmpty

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {e : G.Edge}

theorem StepAssemblyData.partialRealization_flagCovered (D : StepAssemblyData G ∅ e) :
    (D.partialRealization).FlagCovered e := by
  intro x
  rcases D.partialRealization.covers x with ⟨v, y, hy⟩ | ⟨f, hf, q, hq⟩
  · exact Or.inl ⟨v, y, hy⟩
  · have hfe : f = e := by simpa using hf
    subst hfe
    exact Or.inr ⟨_, q, hq⟩

theorem StepAssemblyData.partialRealization_isBlockInvariant
    {Z : ConnectedClosedOrientedManifold.{u} 3} (D : StepAssemblyData G ∅ e)
    (hcorr : (D.partialRealization).componentCorrespondence)
    (hpres : (D.partialRealization).HasBlockPresentation Z) :
    (D.partialRealization).IsBlockInvariant Z :=
  isBlockInvariant_of_flagCovered_of_seamEquation (Finset.mem_insert_self e ∅)
    D.partialRealization_flagCovered D.partialRealization_seamEquation hcorr hpres

end PartialRealization

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem not_stepAssemblyRel_cylinder_of_mem {S : Finset G.Edge} {e f : G.Edge}
    (he : e ∉ S) (hf : f ∈ S) (q : G.cylinderCarrier f) (y : G.assemblyCarrier (insert e S)) :
    ¬ G.stepAssemblyRel S e (Sum.inr ⟨⟨f, Finset.mem_insert_of_mem hf⟩, q⟩) y := by
  intro h
  have hne : f ≠ e := fun hfe => he (hfe ▸ hf)
  rcases h with ⟨z, hx, -⟩ | ⟨z, -, hx⟩ | ⟨z, hx, -⟩ | ⟨z, -, hx⟩
  · exact Sum.inr_ne_inl hx
  · exact hne (Subtype.ext_iff.mp (Sigma.mk.inj_iff.mp (Sum.inr.inj hx)).1)
  · exact hne (Subtype.ext_iff.mp (Sigma.mk.inj_iff.mp (Sum.inr.inj hx)).1)
  · exact Sum.inr_ne_inl hx

theorem vertexBlockList_length (S : Finset G.Edge) (v : G.Vertex) :
    (G.vertexBlockList S v).length = (G.vertexBlock S v).card := by
  rw [vertexBlockList, List.length_map, Finset.length_toList]

def blockSummandCount (S : Finset G.Edge) (b : G.Vertex → ℕ) : Prop :=
  ∀ v : G.Vertex, b v + (G.vertexBlock S v).card = (G.blockEdgeFinset S v).card + 1

theorem blockSummandCount_empty {b : G.Vertex → ℕ} :
    G.blockSummandCount (∅ : Finset G.Edge) b ↔ ∀ v : G.Vertex, b v = 0 := by
  constructor
  · intro h v
    have hv := h v
    rw [vertexBlock_empty, blockEdgeFinset, Finset.filter_empty, Finset.card_singleton,
      Finset.card_empty] at hv
    omega
  · intro h v
    rw [vertexBlock_empty, blockEdgeFinset, Finset.filter_empty, Finset.card_singleton,
      Finset.card_empty, h v]

theorem eq_card_sub_of_blockSummandCount {S : Finset G.Edge} {b : G.Vertex → ℕ}
    (h : G.blockSummandCount S b) (v : G.Vertex) :
    b v = (G.blockEdgeFinset S v).card + 1 - (G.vertexBlock S v).card := by
  have hv := h v
  omega

end MarkedManifoldGraph

end DifferentialGeometry.Topology
