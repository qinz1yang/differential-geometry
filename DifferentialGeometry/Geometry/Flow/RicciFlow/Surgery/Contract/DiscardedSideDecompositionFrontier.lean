import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

theorem isStandardFactor_vertex_of_relativeDiscardPresentation
    {C : Type u} [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C]
    (P : RelativeDiscardPresentation C) (i : Fin P.vertexCount) :
    isStandardFactor (P.vertex i) := by
  rcases P.vertex_elementary i with h | h
  · exact h
  · exact h.elim fun g hg => Or.inl (sphericalSpaceFormCovering_holds (P.vertex i) g hg)

theorem isPoincareStandard_vertex_of_relativeDiscardPresentation
    {C : Type u} [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C]
    (P : RelativeDiscardPresentation C) (i : Fin P.vertexCount) :
    isPoincareStandard (P.vertex i).Carrier :=
  isPoincareStandard_of_standard_factor (P.vertex i)
    (isStandardFactor_vertex_of_relativeDiscardPresentation P i)

def relativeDiscardPresentationOfVertex
    (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (M₀ : ConnectedClosedOrientedManifold.{u} 3) (hM₀ : isStandardFactor M₀) :
    RelativeDiscardPresentation C where
  vertexCount := 1
  vertex := fun _ => M₀
  vertex_elementary := fun _ => Or.inl hM₀
  edgeCount := 0
  edgeSource := fun e => e.elim0
  edgeTarget := fun e => e.elim0
  graph_connected := by
    intro i i'
    have h : i = i' := Subsingleton.elim i i'
    subst h
    exact Relation.ReflTransGen.refl
  externalCount := 0
  externalSphere := fun b => b.elim0
  externalSphere_smooth := by intro b; exact b.elim0
  externalSphere_pairwise := by intro b; exact b.elim0
  edgeCollar := fun e => e.elim0
  edgeCollar_smooth := by intro e; exact e.elim0
  edgeCollar_pairwise := by intro e; exact e.elim0
  edgeCollar_disjoint_sphere := by intro e; exact e.elim0
  region := fun _ => Set.univ
  region_compact := fun _ => isCompact_univ
  region_connected := fun _ => isConnected_univ
  region_frontier := fun _ => by simp
  cover := fun x => Or.inl ⟨0, Set.mem_univ x⟩

def uliftStandardFactor (G : SphericalSpaceFormGroup) :
    ConnectedClosedOrientedManifold.{u} 3 :=
  ConnectedClosedOrientedManifold.ulift.{0, u} G.manifold

theorem isStandardFactor_uliftStandardFactor (G : SphericalSpaceFormGroup) :
    isStandardFactor (uliftStandardFactor.{u} G) :=
  Or.inl ⟨G, ⟨(ClosedOrientedManifold.uliftOrientedDiffeomorph
    G.manifold.toClosedOrientedManifold).symm⟩⟩

theorem hasElementaryDiscardDecomposition_of_connectedSpace
    (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    HasElementaryDiscardDecomposition C :=
  ⟨relativeDiscardPresentationOfVertex C (uliftStandardFactor.{u} SphericalSpaceFormGroup.antipodal)
    (isStandardFactor_uliftStandardFactor SphericalSpaceFormGroup.antipodal)⟩

theorem hasElementaryDiscardDecomposition_of_nonempty_isStandardFactor
    (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (M₀ : ConnectedClosedOrientedManifold.{u} 3) (hM₀ : isStandardFactor M₀) :
    HasElementaryDiscardDecomposition C :=
  ⟨relativeDiscardPresentationOfVertex C M₀ hM₀⟩

theorem exists_relativeDiscardPresentation_vertex_const
    (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (M₀ : ConnectedClosedOrientedManifold.{u} 3) (hM₀ : isStandardFactor M₀) :
    ∃ P : RelativeDiscardPresentation C, P.vertexCount = 1 ∧
      (∀ i : Fin P.vertexCount, P.vertex i = M₀) ∧ P.edgeCount = 0 ∧ P.externalCount = 0 :=
  ⟨relativeDiscardPresentationOfVertex C M₀ hM₀, rfl, fun _ => rfl, rfl, rfl⟩

def HasElementaryDiscardedModel (C : Type u) [TopologicalSpace C]
    [ChartedSpace ThreeSpace C] [IsManifold ThreeModel ∞ C] [T2Space C]
    [CompactSpace C] : Prop :=
  ∃ M : ConnectedClosedOrientedManifold.{u} 3, isStandardFactor M ∧
    Nonempty (Diffeomorph ThreeModel ThreeModel C M.Carrier ∞)

theorem hasElementaryDiscardDecomposition_of_hasElementaryDiscardedModel
    {C : Type u} [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : HasElementaryDiscardedModel C) : HasElementaryDiscardDecomposition C :=
  h.elim fun M hM => hasElementaryDiscardDecomposition_of_nonempty_isStandardFactor C M hM.1

theorem hasElementaryDiscardedModel_uliftStandardFactorCarrier
    (G : SphericalSpaceFormGroup) :
    HasElementaryDiscardedModel (uliftStandardFactor.{u} G).Carrier :=
  ⟨uliftStandardFactor.{u} G, isStandardFactor_uliftStandardFactor G,
    ⟨Diffeomorph.refl ThreeModel (uliftStandardFactor.{u} G).Carrier ∞⟩⟩

theorem pieceInput_of_connectedSpace (DiscardedCutOpen : Type u → Prop)
    (hconn : ∀ (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
      [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C],
      DiscardedCutOpen C → ConnectedSpace C) :
    ∀ (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
      [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C],
      DiscardedCutOpen C → HasElementaryDiscardDecomposition C := by
  intro C _ _ _ _ _ hC
  exact @hasElementaryDiscardDecomposition_of_connectedSpace C _ _ _ _ _ (hconn C hC)

theorem isStandardFactor_component_of_discardPresentation
    {D : ClosedOrientedManifold.{u} 3} (P : RelativeDiscardPresentation D.Carrier)
    (c : ConnectedComponents D.Carrier) (i : Fin P.vertexCount)
    (e : ClosedOrientedManifold.OrientedDiffeomorph
      (D.component c).toClosedOrientedManifold (P.vertex i).toClosedOrientedManifold) :
    isStandardFactor (D.component c) :=
  isStandardFactor_of_orientedDiffeomorph e.symm
    (isStandardFactor_vertex_of_relativeDiscardPresentation P i)

theorem componentwiseStandardFactorOrProjectiveThreeSpaceSum_of_discardPresentation
    {D : ClosedOrientedManifold.{u} 3} (P : RelativeDiscardPresentation D.Carrier)
    (h : ∀ c : ConnectedComponents D.Carrier, ∃ i : Fin P.vertexCount,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.component c).toClosedOrientedManifold (P.vertex i).toClosedOrientedManifold)) :
    D.componentwiseStandardFactorOrProjectiveThreeSpaceSum :=
  fun c => by
    obtain ⟨i, he⟩ := h c
    exact Or.inl (isStandardFactor_component_of_discardPresentation P c i (Classical.choice he))

theorem GlobalStepInputs.component_isPoincareStandard
    {p : CutoffParameters} {τ ε d : ℝ} {k : ℕ} {DiscardedCutOpen : Type u → Prop}
    (G : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)
    (H : ObservedHistory.{u}) (i : Fin H.eventCount) (R : GeometricCutoffRecord H i p)
    (hD : DiscardedCutOpen (H.event i).discarded.Carrier)
    (C : ConnectedComponents (H.event i).discarded.Carrier) :
    componentIsPoincareStandard (H.event i).discarded.toClosedOrientedManifold C :=
  componentwise_isPoincareStandard_of_componentwiseConnectedSumStandardFactor
    (H.event i).discarded.toClosedOrientedManifold (G.pieceInput H i R hD) C

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
