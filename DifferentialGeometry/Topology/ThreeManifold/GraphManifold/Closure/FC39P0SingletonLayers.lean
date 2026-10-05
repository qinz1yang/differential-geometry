import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0ClosedZero
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SlimCircle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Layers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Strong

/-!
Two separate X136 closed singleton configurations, selected by their carrier. Each has one
whole closed vertex and empty ports, seams, faces and handles; every layer uses that same carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

def configurationQ : Bool → ConnectedClosedOrientedManifold.{0} 3
  | false => standardThreeSphere
  | true => sphereTwoTimesCircleLift

def configurationW (b : Bool) : CompactCarrier.{0} := NoCuts.carrier (configurationQ b)

def configurationVertex : (b : Bool) → Vertex (configurationW b)
  | false => .closedZero zeroClosedPiece
  | true => .slim slimPiece slimModel

theorem configurationVertex_image (b : Bool) : (configurationVertex b).image = univ := by
  cases b
  · exact zeroClosedPiece_cover
  · exact wholePiece_range sphereTwoTimesCircleLift

theorem configurationVertex_boundary (b : Bool) :
    (configurationVertex b).boundaryImage = ∅ := by
  have hpiece : (configurationVertex b).piece = wholePiece (configurationQ b) := by
    cases b <;> rfl
  rw [Vertex.boundaryImage, hpiece, wholePiece_boundary, image_empty]

def configurationVertices (b : Bool) : VertexLayer (configurationW b) where
  vertexCount := 1
  vertex := Function.const (Fin 1) (configurationVertex b)

def configurationEdges (b : Bool) : EdgeLayer (configurationW b) where
  handleCount := 0
  handle h := h.elim0
  edgeCircleCount := 0
  edgeCircle e := e.elim0

def configurationPorts (b : Bool) : PortLayer (configurationW b)
    (BoundaryTori.empty (configurationW b)) (configurationVertices b) where
  external_exhausted := by
    change (NoCuts.carrier (configurationQ b)).model.boundary
      (NoCuts.carrier (configurationQ b)).Carrier = _
    rw [closedCarrier_boundary_eq_empty, BoundaryTori.empty_image]
    rfl
  externalOwner i := i.elim0
  external_owned i := i.elim0

def configurationSeams (b : Bool) : SeamLayer (configurationW b)
    (configurationVertices b) (CircleRegion.empty (configurationW b)) where
  torusSeamCount := 0
  torusSeam c := c.elim0
  torusSide c := c.elim0
  torusSide_neg c := c.elim0
  torusSide_pos c := c.elim0
  torusSeam_disjoint c := c.elim0
  sphereSeamCount := 0
  sphereSeam c := c.elim0
  sphereSide c := c.elim0
  sphereSide_neg c := c.elim0
  sphereSide_pos c := c.elim0
  sphereSeam_disjoint c := c.elim0
  sphere_torus_seam_disjoint c := c.elim0

def configurationFaces (b : Bool) : FaceLayer (configurationW b)
    (BoundaryTori.empty (configurationW b)) (configurationVertices b)
    (configurationSeams b) (configurationPorts b) where
  faceCount := 0
  face f := f.elim0
  faceOwner f := f.elim0
  faceModel f := f.elim0
  face_exhausted k := by
    rw [show (configurationVertices b).vertex k = configurationVertex b from rfl,
      configurationVertex_boundary b]
    simp only [iUnion_of_empty]
  faceKind f := f.elim0
  face_disjoint f := f.elim0
  face_external f := f.elim0
  external_face i := i.elim0
  face_torusSeam f := f.elim0
  torusSeam_face c := c.elim0
  face_sphereSeam f := f.elim0
  sphereSeam_face c := c.elim0

def configurationHandleEnds (b : Bool) : HandleEndLayer (configurationW b)
    (configurationVertices b) (configurationEdges b) (configurationFaces b) where
  handleEnd h := h.elim0
  handleFace h := h.elim0
  handleFace_owner h := h.elim0
  handleFace_kind h := h.elim0
  handleEnd_face h := h.elim0
  endDisk_disjoint h := h.elim0

def configurationRims (b : Bool) : RimChartLayer (configurationW b) (configurationEdges b)
    (CircleRegion.empty (configurationW b)) where
  handleCorner h := h.elim0
  handleCorner_bijective := by
    constructor
    · intro hb
      exact hb.1.elim0
    · intro c
      exact c.elim0
  rimChart h := h.elim0
  rim_source h := h.elim0
  rim_proj h := h.elim0
  rim_label h := h.elim0
  rim_disjoint h := h.elim0

def configurationArcs (b : Bool) : ArcLayer (configurationW b) (configurationEdges b)
    (CircleRegion.empty (configurationW b)) (configurationFaces b) (configurationHandleEnds b)
    (configurationRims b) where
  arcFaceCount := 0
  arcFace j := j.elim0
  arcOwner j := j.elim0
  arcOwner_kind j := j.elim0
  arcBase j := j.elim0
  arcBase_embedding j := j.elim0
  arcFace_eq j := j.elim0
  arcDefining j := j.elim0
  arcBase_defining j := j.elim0
  arcAnnulus j := j.elim0
  arcAnnulus_continuous j := j.elim0
  arcAnnulus_injective j := j.elim0
  arcAnnulus_range j := j.elim0
  arcAnnulus_proj j := j.elim0
  loopFaceCount := 0
  loopFace j := j.elim0
  loopOwner j := j.elim0
  loopOwner_kind j := j.elim0
  loopBase j := j.elim0
  loopBase_embedding j := j.elim0
  loopFace_eq j := j.elim0
  loopDefining j := j.elim0
  loopBase_defining j := j.elim0
  loopFace_closed j := j.elim0
  loopFace_nonempty j := j.elim0
  arcFace_disjoint j := j.elim0
  loopFace_disjoint j := j.elim0
  arc_loop_disjoint j := j.elim0
  face_partition f := f.elim0
  face_region_inter f := f.elim0
  handleArc h := h.elim0
  handleArc_owner h := h.elim0
  handleArc_meets h := h.elim0
  endDisk_loop_disjoint h := h.elim0
  endDisk_rim h := h.elim0
  arcEnd j := j.elim0
  arcEnd_arc j := j.elim0
  arcEnd_injective j := j.elim0
  arcEnd_surjective h := h.elim0
  arcAnnulus_end j := j.elim0
  arcBase_end j := j.elim0

theorem configurationCover (b : Bool) : CoverLayer (configurationW b) (configurationVertices b)
    (configurationEdges b) (CircleRegion.empty (configurationW b)) where
  cover := by
    refine eq_univ_of_univ_subset fun x hx => ?_
    refine Or.inl (Or.inl (Or.inl (mem_iUnion.2 ⟨(0 : Fin 1), ?_⟩)))
    change x ∈ (configurationVertex b).image
    rw [configurationVertex_image]
    exact mem_univ x
  vertex_disjoint k k' h := (h (Subsingleton.elim (α := Fin 1) k k')).elim
  handle_disjoint h := h.elim0
  edgeCircle_disjoint e := e.elim0
  vertex_handle_disjoint k h := h.elim0
  edgeCircle_vertex_disjoint e := e.elim0
  edgeCircle_handle_disjoint e := e.elim0
  circ_vertex_disjoint k := by rw [CircleRegion.empty_region]; simp
  circ_handle_disjoint h := h.elim0
  circ_edgeCircle_disjoint e := e.elim0

theorem configurationVertical (b : Bool) : VerticalLayer (configurationW b) (configurationEdges b)
    (CircleRegion.empty (configurationW b)) where
  vertical_fibre h := h.elim0
  edgeCircle_vertical e := e.elim0

theorem configurationRimRegion (b : Bool) : RimRegionLayer (configurationW b)
    (configurationVertices b) (configurationEdges b) (CircleRegion.empty (configurationW b))
    (configurationHandleEnds b) (configurationRims b) where
  rim_vertex h := h.elim0
  rim_handle h := h.elim0
  rim_region h := h.elim0

theorem configurationProtection (b : Bool) : ProtectionLayer (configurationW b)
    (BoundaryTori.empty (configurationW b)) (configurationEdges b)
    (CircleRegion.empty (configurationW b)) (configurationSeams b) (configurationRims b) where
  external_region_disjoint i := i.elim0
  external_handle_disjoint i := i.elim0
  external_edgeCircle_disjoint i := i.elim0
  external_torusSeam_disjoint i := i.elim0
  external_sphereSeam_disjoint i := i.elim0
  rim_external_disjoint h := h.elim0
  rim_torusSeam_disjoint h := h.elim0
  rim_sphereSeam_disjoint h := h.elim0
  sphereSeam_region_disjoint c := c.elim0
  sphereSeam_handle_disjoint c := c.elim0

def configurationCertificate (b : Bool) : DecompositionCertificate (configurationW b)
    (BoundaryTori.empty (configurationW b)) :=
  ofLayers (configurationVertices b) (configurationEdges b)
    (CircleRegion.empty (configurationW b)) (configurationPorts b) (configurationSeams b)
    (configurationFaces b) (configurationHandleEnds b) (configurationRims b)
    (configurationArcs b) (configurationCover b) (configurationVertical b)
    (configurationRimRegion b) (configurationProtection b)

theorem configurationRimProduct (b : Bool) : ∀ h c,
    RimProductAt ((configurationRims b).rimChart h c) ((configurationEdges b).handle h) c :=
  fun h => h.elim0

theorem configurationCertificate_rimProduct (b : Bool) : (configurationCertificate b).RimProduct :=
  ofLayers_rimProduct_iff.2 (configurationRimProduct b)

def configurationStrong (b : Bool) : StrongCertificate (configurationW b)
    (BoundaryTori.empty (configurationW b)) :=
  ⟨configurationCertificate b, configurationCertificate_rimProduct b⟩

def zeroStrong : StrongCertificate zeroW (BoundaryTori.empty zeroW) := configurationStrong false

def slimStrong : StrongCertificate slimW (BoundaryTori.empty slimW) := configurationStrong true

end GC.GraphManifold.Assembly.FC39P0.X136
