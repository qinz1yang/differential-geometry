import DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentPieceGluing

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S2 × Set.Icc (-2 : ℝ) 2

local instance partialGraphClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance partialGraphClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

structure MarkedBall (N : ClosedOrientedManifold.{u} 3) where
  ball : ClosedCell 3 → N.Carrier
  ball_embedding : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball
  collar : Set N.Carrier
  collar_isOpen : IsOpen collar
  ball_subset_collar : range ball ⊆ collar
  collarBudget : ℝ
  collarBudget_pos : 0 < collarBudget

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

def boundary (B : MarkedBall N) : S2 → N.Carrier := B.ball ∘ sphereToClosedCell

theorem boundary_mem_collar (B : MarkedBall N) (z : S2) : B.boundary z ∈ B.collar :=
  B.ball_subset_collar (mem_range_self (sphereToClosedCell z))

theorem collarBudget_ne_zero (B : MarkedBall N) : B.collarBudget ≠ 0 :=
  ne_of_gt B.collarBudget_pos

end MarkedBall

structure MarkedManifoldGraph where
  Vertex : Type u
  Edge : Type u
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  edgeDecidableEq : DecidableEq Edge
  endpoint : Edge → Bool → Vertex
  vertexManifold : Vertex → ConnectedClosedOrientedManifold.{u} 3
  flag : (e : Edge) → (b : Bool) →
    MarkedBall (vertexManifold (endpoint e b)).toClosedOrientedManifold
  flag_collar_disjoint : ∀ (v : Vertex)
      (f f' : {p : Edge × Bool // endpoint p.1 p.2 = v}), f ≠ f' →
      Disjoint (f.2 ▸ (flag f.1.1 f.1.2).collar) (f'.2 ▸ (flag f'.1.1 f'.1.2).collar)
  attach : (e : Edge) → (b : Bool) → S2 → (vertexManifold (endpoint e b)).Carrier
  attach_eq : ∀ (e : Edge) (b : Bool) (z : S2),
    attach e b z = (flag e b).ball (sphereToClosedCell z)

attribute [instance] MarkedManifoldGraph.vertexFintype MarkedManifoldGraph.edgeFintype
  MarkedManifoldGraph.edgeDecidableEq

private theorem reachable_sup_edge_of_walk {V : Type u} {H : SimpleGraph V} {a b : V} :
    ∀ {u v : V}, (H ⊔ SimpleGraph.edge a b).Walk u v →
      H.Reachable u v ∨ (H.Reachable u a ∧ H.Reachable v b) ∨
        (H.Reachable u b ∧ H.Reachable v a)
  | _, _, .nil => Or.inl (SimpleGraph.Reachable.refl _)
  | _, _, .cons hadj p => by
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hadj
    have ih := reachable_sup_edge_of_walk p
    rcases hadj with hadj | ⟨hmem, _⟩
    · have huw : H.Reachable _ _ := hadj.reachable
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (huw.trans h)
      · exact Or.inr (Or.inl ⟨huw.trans h1, h2⟩)
      · exact Or.inr (Or.inr ⟨huw.trans h1, h2⟩)
    · rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h.symm⟩)
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h2⟩)
        · exact Or.inl h2.symm
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h.symm⟩)
        · exact Or.inl h2.symm
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h2⟩)

private theorem connectedComponents_mk_eq_of_preconnectedSpace {α : Type u} [TopologicalSpace α]
    (h : PreconnectedSpace α) (x y : α) : ConnectedComponents.mk x = ConnectedComponents.mk y :=
  @Subsingleton.elim _ (@ConnectedComponents.subsingleton α inferInstance h) x y

theorem reachable_sup_edge_iff {V : Type u} (H : SimpleGraph V) (a b u v : V) :
    (H ⊔ SimpleGraph.edge a b).Reachable u v ↔
      H.Reachable u v ∨ (H.Reachable u a ∧ H.Reachable v b) ∨
        (H.Reachable u b ∧ H.Reachable v a) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨p⟩ := h
    exact reachable_sup_edge_of_walk p
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono le_sup_left
    · by_cases hab : a = b
      · subst hab
        exact (h1.mono le_sup_left).trans (h2.mono le_sup_left).symm
      · refine (h1.mono le_sup_left).trans ((SimpleGraph.Adj.reachable ?_).trans
          (h2.mono le_sup_left).symm)
        rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
    · by_cases hab : a = b
      · subst hab
        exact (h1.mono le_sup_left).trans (h2.mono le_sup_left).symm
      · refine (h1.mono le_sup_left).trans ((SimpleGraph.Adj.reachable ?_).trans
          (h2.mono le_sup_left).symm)
        rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
        exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm hab⟩

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

def source (e : G.Edge) : G.Vertex := G.endpoint e false

def target (e : G.Edge) : G.Vertex := G.endpoint e true

def removedBallSet (S : Finset G.Edge) (v : G.Vertex) : Set (G.vertexManifold v).Carrier :=
  {x | ∃ (e : G.Edge) (_ : e ∈ S) (b : Bool) (h : G.endpoint e b = v),
    x ∈ h ▸ (range (G.flag e b).ball \
      range ((G.flag e b).ball ∘ sphereToClosedCell))}

abbrev puncturedCarrier (S : Finset G.Edge) (v : G.Vertex) : Type u :=
  {x : (G.vertexManifold v).Carrier // x ∉ G.removedBallSet S v}

abbrev cylinderCarrier (_ : G.Edge) : Type := Tube

def gluedEdges (S : Finset G.Edge) : Finset G.Edge := S

def remainingEdges (S : Finset G.Edge) : Finset G.Edge := Sᶜ

theorem mem_gluedEdges (S : Finset G.Edge) (e : G.Edge) : e ∈ G.gluedEdges S ↔ e ∈ S :=
  Iff.rfl

theorem mem_remainingEdges (S : Finset G.Edge) (e : G.Edge) :
    e ∈ G.remainingEdges S ↔ e ∉ S := Finset.mem_compl

theorem remainingEdges_insert (S : Finset G.Edge) (e : G.Edge) :
    G.remainingEdges (insert e S) = (G.remainingEdges S).erase e := by
  ext f
  simp only [remainingEdges, Finset.mem_compl, Finset.mem_insert, Finset.mem_erase]
  tauto

theorem mem_remainingEdges_insert (S : Finset G.Edge) (e f : G.Edge) :
    f ∈ G.remainingEdges (insert e S) ↔ f ≠ e ∧ f ∈ G.remainingEdges S := by
  rw [remainingEdges_insert, Finset.mem_erase]

def processedGraph (S : Finset G.Edge) : SimpleGraph G.Vertex :=
  S.sup fun e => SimpleGraph.edge (G.source e) (G.target e)

theorem processedGraph_insert (S : Finset G.Edge) (e : G.Edge) :
    G.processedGraph (insert e S) =
      SimpleGraph.edge (G.source e) (G.target e) ⊔ G.processedGraph S :=
  Finset.sup_insert

theorem processedGraph_mono {S T : Finset G.Edge} (h : S ⊆ T) :
    G.processedGraph S ≤ G.processedGraph T := by
  rw [processedGraph, processedGraph]
  refine Finset.sup_le fun e he => ?_
  exact Finset.le_sup (f := fun e => SimpleGraph.edge (G.source e) (G.target e)) (h he)

theorem processedGraph_reachable_insert (S : Finset G.Edge) (e : G.Edge) (u v : G.Vertex) :
    (G.processedGraph (insert e S)).Reachable u v ↔
      (G.processedGraph S).Reachable u v ∨
        ((G.processedGraph S).Reachable u (G.source e) ∧
          (G.processedGraph S).Reachable v (G.target e)) ∨
        ((G.processedGraph S).Reachable u (G.target e) ∧
          (G.processedGraph S).Reachable v (G.source e)) := by
  rw [G.processedGraph_insert S e, sup_comm]
  exact reachable_sup_edge_iff (G.processedGraph S) (G.source e) (G.target e) u v

theorem reachable_source_target_insert (S : Finset G.Edge) (e : G.Edge) :
    (G.processedGraph (insert e S)).Reachable (G.source e) (G.target e) :=
  (G.processedGraph_reachable_insert S e _ _).mpr
    (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩))

theorem not_reachable_insert_of_not_reachable (S : Finset G.Edge) (e : G.Edge) {u v : G.Vertex}
    (huv : ¬ (G.processedGraph S).Reachable u v)
    (h1 : ¬ (G.processedGraph S).Reachable u (G.source e))
    (h2 : ¬ (G.processedGraph S).Reachable u (G.target e)) :
    ¬ (G.processedGraph (insert e S)).Reachable u v := by
  rw [G.processedGraph_reachable_insert S e]
  rintro (h | ⟨h1', -⟩ | ⟨h1', -⟩)
  exacts [huv h, h1 h1', h2 h1']

abbrev twoVertex (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) : MarkedManifoldGraph.{0} where
  Vertex := Bool
  Edge := PUnit
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun _ b => b
  vertexManifold := fun _ => N
  flag := fun _ b => if b then B' else B
  flag_collar_disjoint := fun v f f' hne => by
    refine absurd (Subtype.ext ?_) hne
    refine Prod.ext (Subsingleton.elim _ _) ?_
    exact f.2.trans f'.2.symm
  attach := fun _ b => (if b then B' else B).ball ∘ sphereToClosedCell
  attach_eq := fun _ _ _ => rfl

theorem processedGraph_empty_twoVertex (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) :
    (twoVertex N B B').processedGraph (∅ : Finset PUnit) = ⊥ :=
  Finset.sup_empty

theorem not_reachable_twoVertex_empty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) :
    ¬ ((twoVertex N B B').processedGraph ∅).Reachable false true := by
  rw [processedGraph_empty_twoVertex, SimpleGraph.reachable_bot]
  exact Bool.false_ne_true

theorem reachable_twoVertex_insert (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) :
    ((twoVertex N B B').processedGraph
      (insert PUnit.unit (∅ : Finset PUnit))).Reachable false true :=
  (twoVertex N B B').reachable_source_target_insert ∅ PUnit.unit

end MarkedManifoldGraph

structure PartialRealization (G : MarkedManifoldGraph.{u}) (S : Finset G.Edge) where
  realization : ClosedOrientedManifold.{u} 3
  vertexPiece : (v : G.Vertex) → C(G.puncturedCarrier S v, realization.Carrier)
  cylinderPiece : (e : G.Edge) → e ∈ S → C(G.cylinderCarrier e, realization.Carrier)
  survivingFlag : (e : G.Edge) → e ∉ S → MarkedBall realization
  covers : ∀ x : realization.Carrier,
    (∃ (v : G.Vertex) (y : G.puncturedCarrier S v), vertexPiece v y = x) ∨
    (∃ (e : G.Edge) (he : e ∈ S) (y : G.cylinderCarrier e), cylinderPiece e he y = x)
  survivingFlag_collar_disjoint : ∀ (e e' : G.Edge) (he : e ∉ S) (he' : e' ∉ S), e ≠ e' →
    Disjoint (survivingFlag e he).collar (survivingFlag e' he').collar

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge} (P : PartialRealization G S)

def collarBudget (e : G.Edge) (he : e ∉ S) : ℝ := (P.survivingFlag e he).collarBudget

theorem collarBudget_pos (e : G.Edge) (he : e ∉ S) : 0 < P.collarBudget e he :=
  (P.survivingFlag e he).collarBudget_pos

def survivingFlags (e : {e : G.Edge // e ∉ S}) : MarkedBall P.realization :=
  P.survivingFlag e.1 e.2

def assignedToProcessedComponents : Prop :=
  ∀ (v v' : G.Vertex) (y : G.puncturedCarrier S v) (y' : G.puncturedCarrier S v'),
    P.vertexPiece v y = P.vertexPiece v' y' → (G.processedGraph S).Reachable v v'

def componentCorrespondence : Prop :=
  ∀ (v v' : G.Vertex) (y : G.puncturedCarrier S v) (y' : G.puncturedCarrier S v'),
    ConnectedComponents.mk (P.vertexPiece v y) = ConnectedComponents.mk (P.vertexPiece v' y') ↔
      (G.processedGraph S).Reachable v v'

theorem assignedToProcessedComponents_of_componentCorrespondence (h : P.componentCorrespondence) :
    P.assignedToProcessedComponents :=
  fun v v' y y' hv => (h v v' y y').mp (by simpa using congrArg ConnectedComponents.mk hv)

theorem component_eq_of_reachable (h : P.componentCorrespondence) {v v' : G.Vertex}
    (hv : (G.processedGraph S).Reachable v v')
    (y : G.puncturedCarrier S v) (y' : G.puncturedCarrier S v') :
    ConnectedComponents.mk (P.vertexPiece v y) = ConnectedComponents.mk (P.vertexPiece v' y') :=
  (h v v' y y').mpr hv

theorem component_eq_source_target_insert (e : G.Edge)
    (P : PartialRealization G (insert e S)) (h : P.componentCorrespondence)
    (y : G.puncturedCarrier (insert e S) (G.source e))
    (y' : G.puncturedCarrier (insert e S) (G.target e)) :
    ConnectedComponents.mk (P.vertexPiece (G.source e) y) =
      ConnectedComponents.mk (P.vertexPiece (G.target e) y') :=
  P.component_eq_of_reachable h (G.reachable_source_target_insert S e) y y'

def IsConnectedSumPresentable (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  ∃ b : ℕ, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
    (finiteConnectedSum (Vlist ++ List.replicate b Z)).toClosedOrientedManifold)

def IsPartialInvariant (P : PartialRealization G S)
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  P.IsConnectedSumPresentable Z Vlist ∧ P.componentCorrespondence

end PartialRealization

namespace MarkedManifoldGraph

abbrev oneVertex (N : ConnectedClosedOrientedManifold.{u} 3) : MarkedManifoldGraph.{u} where
  Vertex := PUnit
  Edge := PEmpty.{u + 1}
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun e => PEmpty.elim e
  vertexManifold := fun _ => N
  flag := fun e => PEmpty.elim e
  flag_collar_disjoint := fun _ f => PEmpty.elim f.1.1
  attach := fun e => PEmpty.elim e
  attach_eq := fun e => PEmpty.elim e

end MarkedManifoldGraph

namespace PartialRealization

def oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    PartialRealization (MarkedManifoldGraph.oneVertex N) ∅ where
  realization := N.toClosedOrientedManifold
  vertexPiece := fun _ => ⟨Subtype.val, continuous_subtype_val⟩
  cylinderPiece := fun e => PEmpty.elim e
  survivingFlag := fun e => PEmpty.elim e
  covers := fun x =>
    Or.inl ⟨PUnit.unit, ⟨x, by rintro ⟨e, -, -⟩; exact PEmpty.elim e⟩, rfl⟩
  survivingFlag_collar_disjoint := fun e => PEmpty.elim e

theorem componentCorrespondence_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    (oneVertexEmpty N).componentCorrespondence := by
  have hpre : PreconnectedSpace (oneVertexEmpty N).realization.Carrier :=
    inferInstanceAs (PreconnectedSpace N.Carrier)
  intro v v' y y'
  constructor
  · intro _
    exact SimpleGraph.Reachable.refl v
  · intro _
    exact connectedComponents_mk_eq_of_preconnectedSpace hpre _ _

theorem nonempty_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (PartialRealization (MarkedManifoldGraph.oneVertex N) ∅) :=
  ⟨oneVertexEmpty N⟩

theorem remainingEdges_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    (MarkedManifoldGraph.oneVertex N).remainingEdges (∅ : Finset PEmpty.{u + 1}) = ∅ :=
  rfl

theorem orientedDiffeomorph_oneVertexEmpty (N : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (oneVertexEmpty N).realization
      (finiteConnectedSum [N]).toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

end PartialRealization

structure PartialStepLaw (G : MarkedManifoldGraph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3)
    (Vlist : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop where
  initial : ∃ P : PartialRealization G ∅, P.IsPartialInvariant Z Vlist
  step : ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
    P.IsPartialInvariant Z Vlist →
      ∃ P' : PartialRealization G (insert e S), P'.IsPartialInvariant Z Vlist

theorem exists_invariant_of_stepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    {Vlist : List (ConnectedClosedOrientedManifold.{u} 3)}
    (h : PartialStepLaw G Z Vlist) (S : Finset G.Edge) :
    ∃ P : PartialRealization G S, P.IsPartialInvariant Z Vlist := by
  induction S using Finset.induction_on with
  | empty => exact h.initial
  | insert e S he ih =>
    obtain ⟨P, hP⟩ := ih
    exact h.step S P e he hP

theorem exists_connectedSumPresentation_full_of_stepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    {Vlist : List (ConnectedClosedOrientedManifold.{u} 3)}
    (h : PartialStepLaw G Z Vlist) :
    ∃ (P : PartialRealization G Finset.univ) (b : ℕ),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
        (finiteConnectedSum (Vlist ++ List.replicate b Z)).toClosedOrientedManifold) := by
  obtain ⟨P, hpres, -⟩ := exists_invariant_of_stepLaw h Finset.univ
  exact ⟨P, hpres⟩

theorem oneVertexStepLaw (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    PartialStepLaw (MarkedManifoldGraph.oneVertex N) Z [N] where
  initial := ⟨PartialRealization.oneVertexEmpty N,
    ⟨0, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩,
    PartialRealization.componentCorrespondence_oneVertexEmpty N⟩
  step := fun _ _ e _ _ => PEmpty.elim e

theorem exists_connectedSumPresentation_oneVertex_of_stepLaw
    (N Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ (P : PartialRealization (MarkedManifoldGraph.oneVertex N) Finset.univ) (b : ℕ),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph P.realization
        (finiteConnectedSum ([N] ++ List.replicate b Z)).toClosedOrientedManifold) :=
  exists_connectedSumPresentation_full_of_stepLaw (oneVertexStepLaw N Z)

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3}

def ComponentPresentationData (E : SphericalCutCapTransition M Q)
    (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ →
    ∃ (L : List (ConnectedClosedOrientedManifold.{u} 3)) (b : ℕ),
      List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
          B.toClosedOrientedManifold)) L (E.cappedCutPieceFactorList C) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ List.replicate b S)).toClosedOrientedManifold)

theorem componentPresentationData_of_cutComponentPieceDistinctGluing
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.cutComponentPieceDistinctGluing S) : E.ComponentPresentationData S := by
  intro C hC
  obtain ⟨b, hb⟩ := h C hC
  exact ⟨E.cappedCutPieceFactorList C, b, List.forall₂_same.mpr fun A _ =>
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl A.toClosedOrientedManifold⟩, hb⟩

theorem cutComponentPieceDistinctGluing_of_componentPresentationData
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.ComponentPresentationData S) : E.cutComponentPieceDistinctGluing S := by
  intro C hC
  obtain ⟨L, b, hL, ⟨ρ⟩⟩ := h C hC
  obtain ⟨σ⟩ := finiteConnectedSum_congr
    (List.rel_append hL (List.forall₂_same.mpr fun A _ =>
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl A.toClosedOrientedManifold⟩))
  exact ⟨b, ⟨ρ.trans σ⟩⟩

theorem sphericalSummandCompletion_of_componentPresentationData
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.ComponentPresentationData S) : E.sphericalSummandCompletion S :=
  (E.cutComponentPieceDistinctGluing_iff_sphericalSummandCompletion S).mp
    (E.cutComponentPieceDistinctGluing_of_componentPresentationData S h)

theorem componentPresentationData_iff_cutComponentPieceDistinctGluing
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.ComponentPresentationData S ↔ E.cutComponentPieceDistinctGluing S :=
  ⟨E.cutComponentPieceDistinctGluing_of_componentPresentationData S,
    E.componentPresentationData_of_cutComponentPieceDistinctGluing S⟩

theorem componentPresentationData_of_forall_cutIndices_eq_empty
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.ComponentPresentationData S :=
  E.componentPresentationData_of_cutComponentPieceDistinctGluing S
    ((E.cutComponentPieceGluing_iff_cutComponentPieceDistinctGluing S
        fun C => E.injective_cappedFactor_of_cutIndices_eq_empty C (h C)).mp
      (E.cutComponentPieceGluing_of_forall_cutIndices_eq_empty S h))

theorem componentPresentationData_iff_sphericalSummandCompletion
    (E : SphericalCutCapTransition M Q) (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.ComponentPresentationData S ↔ E.sphericalSummandCompletion S :=
  (E.componentPresentationData_iff_cutComponentPieceDistinctGluing S).trans
    (E.cutComponentPieceDistinctGluing_iff_sphericalSummandCompletion S)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
