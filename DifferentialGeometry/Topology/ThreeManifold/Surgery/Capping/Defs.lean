import DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeSystem.Defs

noncomputable section

open Set Function Relation
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
