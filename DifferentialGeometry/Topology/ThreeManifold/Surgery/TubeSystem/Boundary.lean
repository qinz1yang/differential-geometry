import DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeSystem.Defs
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem TubeSystem.coreBoundarySphere_disjoint {M : Type u} [TopologicalSpace M]
    (T : TubeSystem M) {b b' : T.Boundary} (h : b ≠ b') :
    Disjoint (Set.range (T.coreBoundarySphere b)) (Set.range (T.coreBoundarySphere b')) := by
  rcases b with ⟨a, s⟩
  rcases b' with ⟨a', s'⟩
  rw [Set.disjoint_left]
  rintro p ⟨y, rfl⟩ ⟨y', hy'⟩
  have h' : T.boundarySphere (a', s') y' = T.boundarySphere (a, s) y :=
    congrArg (fun q : T.core => (q : M)) hy'
  by_cases ha : a = a'
  · subst ha
    have hcoord : TubeSystem.boundaryLevel s' = TubeSystem.boundaryLevel s := by
      have hinj := (T.embedding a).injective h'
      exact congrArg (fun z : TubeDomain => z.2) hinj
    cases s <;> cases s'
    · exact absurd rfl h
    · norm_num [TubeSystem.boundaryLevel] at hcoord
    · norm_num [TubeSystem.boundaryLevel] at hcoord
    · exact absurd rfl h
  · refine Set.disjoint_left.mp (T.disjoint ha)
      (Set.mem_range_self (f := T.tube a) ⟨y, TubeSystem.boundaryLevel s⟩) ?_
    exact ⟨⟨y', TubeSystem.boundaryLevel s'⟩, h'⟩

theorem TubeSystem.coreBoundarySphere_mem_boundary {M : Type u} [TopologicalSpace M]
    (T : TubeSystem M) [ChartedSpace (EuclideanHalfSpace 3) T.core]
    (hcore : (𝓡∂ 3).boundary T.core = ⋃ b, Set.range (T.coreBoundarySphere b))
    (b : T.Boundary) (y : Sphere 2) :
    T.coreBoundarySphere b y ∈ (𝓡∂ 3).boundary T.core := by
  rw [hcore]
  exact Set.mem_iUnion.mpr ⟨b, Set.mem_range_self y⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
