import DifferentialGeometry.Topology.ThreeManifold.Model
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section

open Set Function Relation
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


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
