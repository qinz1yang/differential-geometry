import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopVertexFaces
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCircleData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopVerticalBase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Layers

/-!
The SAME actual two vertices, one original nonempty handle and full circle region give native
layers.
The genuine closed fixture has no external ports or whole seams; its true cover and fibres persist.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly
open FC39P0

private def loopBaseLayerIndex : Fin standardLoopBallHandleCycle.len :=
  ⟨0,standardLoopBallHandleCycle.len_pos⟩

def loopVertexLayer : VertexLayer (NoCuts.carrier standardThreeSphereLift.{0}) where
  vertexCount := 2
  vertex := loopCertificateVertex

def loopEdgeLayer : EdgeLayer (NoCuts.carrier standardThreeSphereLift.{0}) where
  handleCount := 1
  handle := fun _ => standardLoopBallHandleCycle.handle loopBaseLayerIndex
  edgeCircleCount := 0
  edgeCircle := fun e => e.elim0

def loopPortLayer : PortLayer (NoCuts.carrier standardThreeSphereLift.{0})
    (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{0})) loopVertexLayer where
  external_exhausted := by
    rw [BoundaryTori.empty_image]
    exact closedCarrier_boundary_eq_empty _
  externalOwner := fun i => i.elim0
  external_owned := fun i => i.elim0

def loopSeamLayer : SeamLayer (NoCuts.carrier standardThreeSphereLift.{0})
    loopVertexLayer loopCircleRegionData where
  torusSeamCount := 0
  torusSeam := fun c => c.elim0
  torusSide := fun c => c.elim0
  torusSide_neg := fun c => c.elim0
  torusSide_pos := fun c => c.elim0
  torusSeam_disjoint := fun c => c.elim0
  sphereSeamCount := 0
  sphereSeam := fun c => c.elim0
  sphereSide := fun c => c.elim0
  sphereSide_neg := fun c => c.elim0
  sphereSide_pos := fun c => c.elim0
  sphereSeam_disjoint := fun c => c.elim0
  sphere_torus_seam_disjoint := fun c => c.elim0

theorem loopCoverLayer : CoverLayer (NoCuts.carrier standardThreeSphereLift.{0})
    loopVertexLayer loopEdgeLayer loopCircleRegionData where
  cover := by
    change (⋃ k : Fin 2, (loopCertificateVertex k).image) ∪
      (⋃ _h : Fin 1, Set.range (standardLoopBallHandleCycle.handle loopBaseLayerIndex).map) ∪
      (⋃ e : Fin 0, Set.range ((e.elim0 : EdgeCirclePiece
        (NoCuts.carrier standardThreeSphereLift.{0})).piece.map)) ∪ loopCircleRegion = Set.univ
    simp only [iUnion_of_empty,union_empty,iUnion_const]
    exact loopCertificateVertex_cover
  vertex_disjoint := loopCertificateVertex_disjoint
  handle_disjoint := by
    intro h h' hne
    have he : h = h' := by
      apply Fin.ext
      have hh : h.val < 1 := h.isLt
      have hh' : h'.val < 1 := h'.isLt
      omega
    exact False.elim (hne he)
  edgeCircle_disjoint := fun e => e.elim0
  vertex_handle_disjoint := fun k _h => loopCertificateVertex_handle_disjoint k
  edgeCircle_vertex_disjoint := fun e => e.elim0
  edgeCircle_handle_disjoint := fun e => e.elim0
  circ_vertex_disjoint := loopCertificateVertex_region_disjoint
  circ_handle_disjoint := fun _h => loopCircleRegion_handle_disjoint loopBaseLayerIndex
  circ_edgeCircle_disjoint := fun e => e.elim0

theorem loopVerticalLayer : VerticalLayer (NoCuts.carrier standardThreeSphereLift.{0})
    loopEdgeLayer loopCircleRegionData where
  vertical_fibre := fun _h t => ⟨loopHandleBase t,loopHandle_vertical_fibre t⟩
  edgeCircle_vertical := fun e => e.elim0

end GC.GraphManifold.Assembly
