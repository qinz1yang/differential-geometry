import DifferentialGeometry.Topology.ThreeManifold.CoreComponentGeometry
import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutComponentRealization

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

include C in
theorem exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent
    (x : T.core) :
    (∃ (b : T.Boundary) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      T.coreBoundarySphere b q ∈ connectedComponent x) ∨
      Subtype.val '' connectedComponent x = connectedComponent x.val := by
  classical
  by_cases h : ∃ (b : T.Boundary) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      T.coreBoundarySphere b q ∈ connectedComponent x
  · exact Or.inl h
  right
  obtain ⟨_, hconn, _, _, hfront⟩ := C.coreComponent_geometry x
  have hfrontempty : frontier (Subtype.val '' connectedComponent x) = ∅ := by
    rw [hfront]
    apply iUnion_eq_empty.mpr
    intro b
    exact (h ⟨b.val, b.property⟩).elim
  have hcl := isClopen_iff_frontier_eq_empty.mpr hfrontempty
  have hx : x.val ∈ Subtype.val '' connectedComponent x :=
    ⟨x, mem_connectedComponent, rfl⟩
  exact Subset.antisymm (hconn.isPreconnected.subset_connectedComponent hx)
    (hcl.connectedComponent_subset hx)

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty
    (x : E.tubes.core) :
    (∃ (b : E.tubes.Boundary) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      E.tubes.coreBoundarySphere b q ∈ connectedComponent x) ∨
      E.cutIndices (ConnectedComponents.mk x.val) = ∅ := by
  rcases E.capping.exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent x with h | h
  · exact Or.inl h
  right
  have hcore : connectedComponent x.val ⊆ E.tubes.core := by
    rw [← h]
    rintro z ⟨y, _, rfl⟩
    exact y.property
  apply (E.cutIndices_eq_empty_iff _).mpr
  rintro j ⟨q, hq⟩
  let q₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (-2 : ℝ) 2 :=
    (q₀, ⟨0, by norm_num⟩)
  have hzcomp : E.tubes.tube j z ∈ connectedComponent x.val := by
    have htube := (E.tubes.isPreconnected_range_tube j).subset_connectedComponent
      (mem_range_self q) (mem_range_self z)
    rw [ClosedOrientedManifold.componentSet_mk] at hq
    rwa [← connectedComponent_eq hq] at htube
  exact hcore hzcomp (mem_iUnion.mpr ⟨j, z, by norm_num [z], rfl⟩)

end DifferentialGeometry.Topology.SphericalCutCapTransition
