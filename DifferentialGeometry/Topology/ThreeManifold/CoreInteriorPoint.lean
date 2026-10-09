import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.Manifold.InteriorBoundary
import Mathlib.Analysis.Convex.PathConnected

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem exists_coreInclusion_mem_component (K : ConnectedComponents N.Carrier) :
    ∃ x : T.core, C.coreInclusion x ∈ N.componentSet K := by
  obtain ⟨y,hy⟩ := N.componentSet_nonempty K
  have hc : y ∈ range C.coreInclusion ∪ ⋃ b,range (C.cap b) := C.exhaustive ▸ mem_univ y
  rcases hc with ⟨x,hx⟩ | hc
  · exact ⟨x,hx ▸ hy⟩
  · obtain ⟨b,x,hx⟩ := mem_iUnion.mp hc
    have hpre : IsPreconnected (range (C.cap b)) := by
      let _ : PreconnectedSpace (ClosedCell 3) := isPreconnected_iff_preconnectedSpace.mp
        (show IsPreconnected {x : E3 | ‖x‖ ≤ 1} from by
          simpa only [closedBall,dist_zero_right] using (convex_closedBall (0:E3) 1).isPreconnected)
      exact isPreconnected_range (C.cap b).continuous
    let z : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
    let xcore := T.coreBoundarySphere b (C.attaching b z)
    refine ⟨xcore, ?_⟩
    have hcomp : ConnectedComponents.mk (C.cap b (sphereToClosedCell z)) = ConnectedComponents.mk y := by
      apply ConnectedComponents.coe_eq_coe'.mpr
      exact hpre.subset_connectedComponent ⟨x,hx⟩ ⟨sphereToClosedCell z,rfl⟩
    rw [N.mem_componentSet] at hy ⊢
    have heq : C.coreInclusion xcore = C.cap b (sphereToClosedCell z) := (C.boundary_eq b z).symm
    rw [heq,hcomp]
    exact hy

theorem exists_coreInterior_mem_component (K : ConnectedComponents N.Carrier) :
    letI := C.coreCharts
    ∃ x : T.core, (𝓡∂ 3).IsInteriorPoint x ∧ C.coreInclusion x ∈ N.componentSet K := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  obtain ⟨x,hx⟩ := C.exists_coreInclusion_mem_component K
  let U : Set T.core := C.coreInclusion ⁻¹' N.componentSet K
  have hU : IsOpen U := (N.isOpen_componentSet K).preimage C.coreInclusion.continuous
  have hUne : U.Nonempty := ⟨x,hx⟩
  obtain ⟨y,hyU,hyint⟩ := (dense_iff_inter_open.mp (ModelWithCorners.dense_interior (𝓡∂ 3))) U hU hUne
  exact ⟨y,hyint,hyU⟩

end DifferentialGeometry.Topology.SphericalCapping
