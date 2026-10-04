import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapImmersions

/-!
Actual relative spherical capping, keeping standard cap orientation and all old torus collars.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

local instance sphereCapCappingBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance sphereCapCappingBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

private theorem sphereCapCoreOpen_of_interior {x : C.Carrier}
    (hx : C.model.IsInteriorPoint x) : x ∈ B.sphereCapCoreOpen := by
  intro hs
  obtain ⟨i, z, hz⟩ := mem_iUnion.mp hs
  have hb : C.model.IsBoundaryPoint x := hz ▸ B.sphere_zero_boundary i z
  exact (C.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hb

private theorem sphereCapReparameterizedCap_range (i : Fin B.sphereCount) :
    range (B.sphereCapReparameterizedCap i) = range (B.sphereCapBall i) :=
  (B.sphereCapOrientationData.reparameterization i).surjective.range_comp (B.sphereCapBall i)

set_option backward.isDefEq.respectTransparency false in
def sphereCapRelativeCapping : RelativeSphereCapping C B.sphereCapCarrier B := by
  letI := B.sphereCapQuotientChartedSpace
  letI := B.sphereCapQuotientIsManifold
  let hA := B.exists_sphereCapQuotientAtlas.choose_spec.2
  refine {
    core := B.sphereCapCore
    core_embedding := B.sphereCapCore_isSmoothEmbedding hA
    cap := B.sphereCapReparameterizedCap
    cap_embedding := ?_
    attaching := B.sphereCapOrientationData.attaching
    boundary_eq := B.sphereCapReparameterizedCap_boundary
    covers := ?_
    core_cap_intersection := ?_
    cap_disjoint := ?_
    retained := B.sphereCapRetained
    retained_collar := fun i p hp => B.sphereCapRetained_collar i hp
    boundary_exhausted := B.sphereCapRetained_exhausted
    core_positive := ?_
    cap_positive := B.sphereCapReparameterizedCap_positive }
  · intro i
    let D := B.sphereCapOrientationData.reparameterization i
    exact (B.sphereCapBall_isSmoothEmbedding hA i).comp_diffeomorph D
  · change range B.sphereCapCore ∪ ⋃ i, range (B.sphereCapReparameterizedCap i) = univ
    simp only [B.sphereCapReparameterizedCap_range]
    exact B.sphereCap_covers
  · intro i
    change range B.sphereCapCore ∩ range (B.sphereCapReparameterizedCap i) =
      range (fun z => B.sphereCapCore (B.sphere i (z, halfZero)))
    rw [B.sphereCapReparameterizedCap_range]
    exact B.sphereCapCore_ball_intersection i
  · intro i j hij
    change Disjoint (range (B.sphereCapReparameterizedCap i))
      (range (B.sphereCapReparameterizedCap j))
    rw [B.sphereCapReparameterizedCap_range, B.sphereCapReparameterizedCap_range]
    exact B.sphereCapBall_disjoint hij
  · intro x hx
    exact B.sphereCapCore_positive ⟨x, B.sphereCapCoreOpen_of_interior hx⟩

end GC.GraphManifold.MixedBoundaryCertificate

namespace GC.GraphManifold

theorem exists_relativeSphereCapping (C : CompactCarrier.{u})
    (B : MixedBoundaryCertificate C) :
    ∃ Q : CompactCarrier.{u}, Nonempty (RelativeSphereCapping C Q B) :=
  ⟨B.sphereCapCarrier, ⟨B.sphereCapRelativeCapping⟩⟩

end GC.GraphManifold
