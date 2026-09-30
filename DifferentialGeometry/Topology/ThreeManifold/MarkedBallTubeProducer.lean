import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.ThreeManifold.PartialRealizationStepAssembly

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

local instance markedBallClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance markedBallClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

def ofBallEmbedding (ball : ClosedCell 3 → N.Carrier)
    (ball_embedding : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball) : MarkedBall N where
  ball := ball
  ball_embedding := ball_embedding
  neighborhood := univ
  isOpen_neighborhood := isOpen_univ
  range_ball_subset_neighborhood := Set.subset_univ (range ball)

theorem ofBallEmbedding_ball (ball : ClosedCell 3 → N.Carrier)
    (ball_embedding : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball) :
    (ofBallEmbedding ball ball_embedding).ball = ball := rfl

theorem ofBallEmbedding_neighborhood (ball : ClosedCell 3 → N.Carrier)
    (ball_embedding : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball) :
    (ofBallEmbedding ball ball_embedding).neighborhood = univ := rfl

theorem nonempty_iff_exists_isSmoothEmbedding :
    Nonempty (MarkedBall N) ↔
      ∃ ball : ClosedCell 3 → N.Carrier,
        IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ball :=
  ⟨fun ⟨B⟩ => ⟨B.ball, B.ball_embedding⟩,
    fun ⟨ball, hball⟩ => ⟨ofBallEmbedding ball hball⟩⟩

theorem neighborhood_nonempty (B : MarkedBall N) : B.neighborhood.Nonempty :=
  ⟨B.ball (closedCellCenter 3),
    B.range_ball_subset_neighborhood (mem_range_self (closedCellCenter 3))⟩

theorem neighborhood_ne_univ_of_disjoint (B : MarkedBall N) {C : Set N.Carrier}
    (h : Disjoint B.neighborhood C) (hC : C.Nonempty) : B.neighborhood ≠ univ := by
  intro hc
  obtain ⟨x, hx⟩ := hC
  exact Set.disjoint_left.mp h (by simp [hc]) hx

theorem not_disjoint_of_neighborhood_eq_univ (B B' : MarkedBall N) (h : B.neighborhood = univ) :
    ¬ Disjoint B.neighborhood B'.neighborhood :=
  fun hd => neighborhood_ne_univ_of_disjoint B hd B'.neighborhood_nonempty h

end MarkedBall

namespace SphericalCapping

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}

def markedBall (E : SphericalCapping M N T) (b : T.Boundary) : MarkedBall N :=
  MarkedBall.ofBallEmbedding (E.cap b) (E.cap_embedding b)

theorem markedBall_ball (E : SphericalCapping M N T) (b : T.Boundary) :
    (markedBall E b).ball = E.cap b := rfl

theorem markedBall_neighborhood (E : SphericalCapping M N T) (b : T.Boundary) :
    (markedBall E b).neighborhood = univ := rfl

theorem nonempty_markedBall_of_boundary (E : SphericalCapping M N T)
    (h : Nonempty T.Boundary) : Nonempty (MarkedBall N) :=
  h.elim fun b => ⟨markedBall E b⟩

end SphericalCapping

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem nonempty_markedBall_of_tube (h : Nonempty E.tubes.Index) : Nonempty (MarkedBall E.capped) :=
  h.elim fun a => ⟨SphericalCapping.markedBall E.capping (a, false)⟩

end SphericalCutCapTransition

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

private theorem set_nonempty_cast {V : Type u} (X : V → Type u) {a b : V} (h : a = b)
    {S : Set (X a)} (hS : S.Nonempty) : (h ▸ S : Set (X b)).Nonempty := by
  cases h
  exact hS

theorem flag_neighborhood_ne_univ_of_ne (e e' : G.Edge) (b b' : Bool)
    (hv : G.endpoint e' b' = G.endpoint e b) (h : (e, b) ≠ (e', b')) :
    (G.flag e b).neighborhood ≠ univ := by
  classical
  have hne : (⟨(e, b), rfl⟩ : {p : G.Edge × Bool // G.endpoint p.1 p.2 = G.endpoint e b}) ≠
      ⟨(e', b'), hv⟩ := fun hh => h (congrArg Subtype.val hh)
  have hdisj : Disjoint (G.flag e b).neighborhood (hv ▸ (G.flag e' b').neighborhood) := by
    simpa using G.flag_neighborhood_disjoint (G.endpoint e b) ⟨(e, b), rfl⟩ ⟨(e', b'), hv⟩ hne
  exact MarkedBall.neighborhood_ne_univ_of_disjoint (G.flag e b) hdisj
    (set_nonempty_cast (fun v => (G.vertexManifold v).Carrier) hv (G.flag e' b').neighborhood_nonempty)

end MarkedManifoldGraph

def HasRealizationStep (G : MarkedManifoldGraph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
    P.IsBlockInvariant Z → ∃ P' : PartialRealization G (insert e S), P'.IsBlockInvariant Z

theorem hasRealizationStep_of_blockStepLaw {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : BlockStepLaw G Z) :
    HasRealizationStep G Z := h.step

theorem blockStepLaw_of_hasRealizationStep_of_initial {G : MarkedManifoldGraph.{u}}
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    (h₀ : ∃ P : PartialRealization G ∅, P.IsBlockInvariant Z)
    (h : HasRealizationStep G Z) : BlockStepLaw G Z := ⟨h₀, h⟩

theorem hasRealizationStep_oneVertex (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    HasRealizationStep (MarkedManifoldGraph.oneVertex N) Z :=
  hasRealizationStep_of_blockStepLaw (MarkedManifoldGraph.oneVertexBlockStepLaw N Z)

theorem hasRealizationStep_twoVertexEmpty
    (N N' Z : ConnectedClosedOrientedManifold.{0} 3) :
    HasRealizationStep (MarkedManifoldGraph.twoVertexEmpty N N') Z :=
  fun _ _ e _ _ => PEmpty.elim e

end DifferentialGeometry.Topology
