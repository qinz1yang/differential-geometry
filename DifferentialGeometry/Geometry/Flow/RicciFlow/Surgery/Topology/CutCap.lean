import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev ThreeBall := Metric.closedBall (0 : ThreeSpace) 1


def sphereToThreeBall : C(Sphere 2, ThreeBall) :=
  ⟨fun x => ⟨x.1, le_of_eq x.2⟩, continuous_subtype_val.subtype_mk _⟩


abbrev TubeDomain := Sphere 2 × Icc (-2 : ℝ) 2


structure TubeSystem (M : Type*) [TopologicalSpace M] where

  Index : Type
  finiteIndex : Fintype Index

  tube : Index → C(TubeDomain, M)
  embedding : ∀ a, Topology.IsEmbedding (tube a)
  disjoint : Pairwise fun a b => Disjoint (Set.range (tube a)) (Set.range (tube b))

attribute [instance] TubeSystem.finiteIndex

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)


def removedBand (a : T.Index) : Set M :=
  T.tube a '' {z : TubeDomain | (-1 : ℝ) < z.2.1 ∧ z.2.1 < 1}


def core : Set M := (⋃ a, T.removedBand a)ᶜ


abbrev Boundary := T.Index × Bool


def boundaryLevel (b : Bool) : Icc (-2 : ℝ) 2 :=
  if b then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩


def boundarySphere (b : T.Boundary) : C(Sphere 2, M) :=
  (T.tube b.1).comp ⟨fun y => (y, boundaryLevel b.2), continuous_id.prodMk continuous_const⟩

theorem boundarySphere_mem_core (b : T.Boundary) (y : Sphere 2) :
    T.boundarySphere b y ∈ T.core := by
  intro hm
  obtain ⟨a, z, hz, heq⟩ := by
    simpa only [mem_iUnion, removedBand, mem_image] using hm
  have ha : a = b.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne)
      (Set.mem_range_self z) ⟨(y, boundaryLevel b.2), heq.symm⟩
  subst a
  have hcoord := congrArg (fun z : TubeDomain => (z.2 : ℝ))
    ((T.embedding b.1).injective heq)
  rcases b with ⟨b, side⟩
  cases side <;> simp [boundaryLevel] at hcoord <;> rcases hz with ⟨hlo, hhi⟩ <;> linarith


def coreBoundarySphere (b : T.Boundary) : C(Sphere 2, T.core) :=
  ⟨fun y => ⟨T.boundarySphere b y, T.boundarySphere_mem_core b y⟩,
    (T.boundarySphere b).continuous.subtype_mk _⟩

theorem core_eq_univ_of_isEmpty [IsEmpty T.Index] : T.core = univ := by
  simp [core]

end TubeSystem


abbrev ComponentCarrier {X : Type*} [TopologicalSpace X] (c : ConnectedComponents X) :=
  {x : X // ConnectedComponents.mk x = c}


structure Capping {M : Type*} [TopologicalSpace M] (T : TubeSystem M)
    (N : Type*) [TopologicalSpace N] where
  coreInclusion : C(T.core, N)
  coreEmbedding : Topology.IsEmbedding coreInclusion
  cap : T.Boundary → C(ThreeBall, N)
  capEmbedding : ∀ b, Topology.IsEmbedding (cap b)

  attaching : T.Boundary → Sphere 2 ≃ₜ Sphere 2
  boundary_eq : ∀ b y,
    cap b (sphereToThreeBall y) = coreInclusion (T.coreBoundarySphere b (attaching b y))
  exhaustive : Set.range coreInclusion ∪ (⋃ b, Set.range (cap b)) = univ
  core_cap_intersection : ∀ b,
    Set.range coreInclusion ∩ Set.range (cap b) =
      Set.range (coreInclusion.comp (T.coreBoundarySphere b))
  cap_disjoint : Pairwise fun b b' => Disjoint (Set.range (cap b)) (Set.range (cap b'))

namespace Capping

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {T : TubeSystem M} (K : Capping T N)


def componentMap : ConnectedComponents T.core → ConnectedComponents N :=
  K.coreInclusion.continuous.connectedComponentsMap

@[simp] theorem componentMap_mk (x : T.core) :
    K.componentMap (ConnectedComponents.mk x) = ConnectedComponents.mk (K.coreInclusion x) := rfl

theorem rfs_cap_component_bijection [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [T2Space N] : Function.Bijective K.componentMap := by
  sorry


def componentEquiv [CompactSpace T.core] [LocallyConnectedSpace T.core] [T2Space N] :
    ConnectedComponents T.core ≃ ConnectedComponents N :=
  Equiv.ofBijective K.componentMap K.rfs_cap_component_bijection


theorem component_meets_core [CompactSpace T.core] [LocallyConnectedSpace T.core] [T2Space N]
    (c : ConnectedComponents N) :
    ∃ x : T.core, ConnectedComponents.mk (K.coreInclusion x) = c := by
  obtain ⟨d, hd⟩ := K.rfs_cap_component_bijection.surjective c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe d
  exact ⟨x, hd⟩

end Capping

theorem rfs_capped_simply_connected {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] [T2Space N]
    (T : TubeSystem M) (K : Capping T N) (c : ConnectedComponents N) :
    SimplyConnectedSpace (ComponentCarrier c) := by
  sorry

theorem rfs_retained_capped_simply_connected {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] [T2Space N]
    (T : TubeSystem M) (K : Capping T N) (retained : Set (ConnectedComponents N))
    (c : retained) : SimplyConnectedSpace (ComponentCarrier c.1) :=
  rfs_capped_simply_connected T K c.1

structure CutCapTopology (M Q D N : Type*) [TopologicalSpace M] [TopologicalSpace Q]
    [TopologicalSpace D] [TopologicalSpace N] where
  tubes : TubeSystem M
  capping : Capping tubes N
  presentation : N ≃ₜ Q ⊕ D
  nontrivial : Nonempty tubes.Index ∨ Nonempty D

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [TopologicalSpace D] [TopologicalSpace N] (E : CutCapTopology M Q D N)


def retainedCore : Set E.tubes.core :=
  {x | ∃ q : Q, E.presentation (E.capping.coreInclusion x) = Sum.inl q}


def cappedChild (c : ConnectedComponents Q) : ConnectedComponents N :=
  (E.presentation.symm.continuous.comp continuous_inl).connectedComponentsMap c


def childCore [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core] [T2Space N]
    (c : ConnectedComponents Q) : ConnectedComponents E.tubes.core :=
  E.capping.componentEquiv.symm (E.cappedChild c)


def rfs_child_parent [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core] [T2Space N]
    (c : ConnectedComponents Q) : ConnectedComponents M :=
  continuous_subtype_val.connectedComponentsMap (E.childCore c)


theorem childCore_unique [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core]
    [T2Space N] (c : ConnectedComponents Q) :
    ∃! d : ConnectedComponents E.tubes.core,
      E.capping.componentMap d = E.cappedChild c := by
  exact E.capping.rfs_cap_component_bijection.existsUnique _

end CutCapTopology

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
