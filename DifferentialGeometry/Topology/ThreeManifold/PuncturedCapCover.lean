import DifferentialGeometry.Topology.ThreeManifold.PuncturedCapIncidence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingBridge

noncomputable section
open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement
    {Ω : Set M.Carrier} (hΩ : IsClosed Ω) (outer : T.Boundary)
    (hfront : frontier Ω = range (T.boundarySphere outer))
    (s : Finset T.Boundary)
    (B : T.Boundary → PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hB : ∀ b ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
    (hinside : ∀ b ∈ s, B b '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdis : (s : Set T.Boundary).Pairwise (fun b c =>
      Disjoint (B b '' closedBall (0 : ThreeSpace) 1) (B c '' closedBall (0 : ThreeSpace) 1)))
    (hsphere : ∀ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere b))
    (x : T.core)
    (hcomponent : Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1 =
      (Subtype.val : T.core → M.Carrier) '' connectedComponent x) :
    (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, range (C.cap b)) ∪
      range (C.cap outer) = N.componentSet (ConnectedComponents.mk (C.coreInclusion x)) := by
  classical
  obtain ⟨hcontains, hexact⟩ := T.toTopological.boundary_incidence_of_finite_ball_complement_component
    hΩ outer hfront s B hB hinside hdis hsphere x hcomponent
  have h := C.image_coreComponent_union_caps_eq_connectedComponent x
    (insert outer (s : Set T.Boundary))
    (fun b hb q => hcontains b (by simpa only [mem_insert_iff,Finset.mem_coe] using hb) q)
    (fun b hb => by simpa only [mem_insert_iff,Finset.mem_coe] using hexact b hb)
  rw [ClosedOrientedManifold.componentSet_mk]
  rw [← h]
  ext y
  simp only [mem_union,mem_iUnion,mem_insert_iff,Finset.mem_coe]
  aesop

end DifferentialGeometry.Topology.SphericalCapping
