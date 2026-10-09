import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

/-!
# Consumer of the FC39 certificate: one closed zero piece

The trivial example of the closed certificate (`ClosedDecompositionCertificate`, `AssemblyCertificate.lean`):
a closed zero piece `C : ClosedZeroPiece W` whose image is all of `W`. The carrier then has empty
boundary (`ClosedZeroPiece.boundary_eq_empty_of_range_eq_univ`: every point is the image of an
interior point under a map of bijective differential), and `closedCertificateOfClosedZeroPiece` is the
certificate with one vertex `.closedZero C`, no handles, no circle-base edges, the empty circle region
`CircleRegion.empty`, no seams, no faces, the empty port family `BoundaryTori.empty`. This is the
right-disjunct shape of the FC42 consumer (assembly design §0, review §8 / D12).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- A closed zero piece whose image is all of `W` forces `∂W = ∅`: each point of `W` is the image
of an interior point of the piece under a map with bijective differential. -/
theorem ClosedZeroPiece.boundary_eq_empty_of_range_eq_univ {W : CompactCarrier.{u}}
    (C : ClosedZeroPiece W) (hcover : range C.piece.map = univ) :
    W.model.boundary W.Carrier = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨q, rfl⟩ : x ∈ range C.piece.map := hcover ▸ mem_univ x
  have hq : (𝓡∂ 3).IsInteriorPoint q := by
    rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with h | h
    · exact h
    · have hb : q ∈ (𝓡∂ 3).boundary C.piece.Piece := h
      rw [C.boundary_empty] at hb
      exact hb.elim
  have hint : W.model.IsInteriorPoint (C.piece.map q) :=
    (C.piece.smooth.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv
      (C.piece.mfderiv_bijective q).2 hq
  exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).1 hint hx

/-- **The trivial closed certificate.** One closed zero piece covering `W`. -/
def closedCertificateOfClosedZeroPiece {W : CompactCarrier.{u}} (C : ClosedZeroPiece W)
    (hcover : range C.piece.map = univ) : ClosedDecompositionCertificate W :=
  DecompositionCertificate.toClosed (E := BoundaryTori.empty W)
    { external_exhausted := by
        rw [C.boundary_eq_empty_of_range_eq_univ hcover, BoundaryTori.empty_image]
      vertexCount := 1
      vertex := fun _ => .closedZero C
      handleCount := 0
      handle := fun h => h.elim0
      edgeCircleCount := 0
      edgeCircle := fun e => e.elim0
      circ := CircleRegion.empty W
      cover := by
        refine eq_univ_of_univ_subset fun x _ => Or.inl (Or.inl (Or.inl (mem_iUnion.2 ⟨0, ?_⟩)))
        change x ∈ range C.piece.map
        rw [hcover]
        exact mem_univ x
      vertex_disjoint := fun k k' h => (h (Subsingleton.elim k k')).elim
      handle_disjoint := fun h => h.elim0
      edgeCircle_disjoint := fun e => e.elim0
      vertex_handle_disjoint := fun _ h => h.elim0
      edgeCircle_vertex_disjoint := fun e => e.elim0
      edgeCircle_handle_disjoint := fun e => e.elim0
      circ_vertex_disjoint := fun _ => by simp
      circ_handle_disjoint := fun h => h.elim0
      circ_edgeCircle_disjoint := fun e => e.elim0
      vertical_fibre := fun h => h.elim0
      edgeCircle_vertical := fun e => e.elim0
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
      externalOwner := fun i => i.elim0
      external_owned := fun i => i.elim0
      faceCount := 0
      face := fun f => f.elim0
      faceOwner := fun f => f.elim0
      faceModel := fun f => f.elim0
      face_exhausted := fun _ => by
        change _ = C.piece.map '' (𝓡∂ 3).boundary C.piece.Piece
        rw [C.boundary_empty, image_empty]
        simp
      face_disjoint := fun f => f.elim0
      faceKind := fun f => f.elim0
      face_external := fun f => f.elim0
      external_face := fun i => i.elim0
      face_torusSeam := fun f => f.elim0
      torusSeam_face := fun c => c.elim0
      face_sphereSeam := fun f => f.elim0
      sphereSeam_face := fun c => c.elim0
      handleEnd := fun h => h.elim0
      handleFace := fun h => h.elim0
      handleFace_owner := fun h => h.elim0
      handleFace_kind := fun h => h.elim0
      handleEnd_face := fun h => h.elim0
      endDisk_disjoint := fun h => h.elim0
      arcFaceCount := 0
      arcFace := fun j => j.elim0
      arcOwner := fun j => j.elim0
      arcOwner_kind := fun j => j.elim0
      arcBase := fun j => j.elim0
      arcBase_embedding := fun j => j.elim0
      arcFace_eq := fun j => j.elim0
      arcDefining := fun j => j.elim0
      arcBase_defining := fun j => j.elim0
      arcAnnulus := fun j => j.elim0
      arcAnnulus_continuous := fun j => j.elim0
      arcAnnulus_injective := fun j => j.elim0
      arcAnnulus_range := fun j => j.elim0
      arcAnnulus_proj := fun j => j.elim0
      loopFaceCount := 0
      loopFace := fun j => j.elim0
      loopOwner := fun j => j.elim0
      loopOwner_kind := fun j => j.elim0
      loopBase := fun j => j.elim0
      loopBase_embedding := fun j => j.elim0
      loopFace_eq := fun j => j.elim0
      loopDefining := fun j => j.elim0
      loopBase_defining := fun j => j.elim0
      loopFace_closed := fun j => j.elim0
      loopFace_nonempty := fun j => j.elim0
      arcFace_disjoint := fun j => j.elim0
      loopFace_disjoint := fun j => j.elim0
      arc_loop_disjoint := fun j => j.elim0
      face_partition := fun f => f.elim0
      face_region_inter := fun f => f.elim0
      handleArc := fun h => h.elim0
      handleArc_owner := fun h => h.elim0
      handleArc_meets := fun h => h.elim0
      endDisk_loop_disjoint := fun h => h.elim0
      endDisk_rim := fun h => h.elim0
      arcEnd := fun j => j.elim0
      arcEnd_arc := fun j => j.elim0
      arcEnd_injective := fun j => j.elim0
      arcEnd_surjective := fun h => h.elim0
      arcAnnulus_end := fun j => j.elim0
      handleCorner := fun h => h.elim0
      handleCorner_bijective := ⟨fun a => a.1.elim0, fun b => b.elim0⟩
      arcBase_end := fun j => j.elim0
      rimChart := fun h => h.elim0
      rim_source := fun h => h.elim0
      rim_proj := fun h => h.elim0
      rim_vertex := fun h => h.elim0
      rim_handle := fun h => h.elim0
      rim_region := fun h => h.elim0
      rim_label := fun h => h.elim0
      rim_disjoint := fun h => h.elim0
      external_region_disjoint := fun i => i.elim0
      external_handle_disjoint := fun i => i.elim0
      external_edgeCircle_disjoint := fun i => i.elim0
      external_torusSeam_disjoint := fun i => i.elim0
      external_sphereSeam_disjoint := fun i => i.elim0
      rim_external_disjoint := fun h => h.elim0
      rim_torusSeam_disjoint := fun h => h.elim0
      rim_sphereSeam_disjoint := fun h => h.elim0
      sphereSeam_region_disjoint := fun c => c.elim0
      sphereSeam_handle_disjoint := fun c => c.elim0 }

section ClosedZero

variable {W : CompactCarrier.{u}} (C : ClosedZeroPiece W) (hcover : range C.piece.map = univ)

@[simp]
theorem closedCertificateOfClosedZeroPiece_vertexCount :
    (closedCertificateOfClosedZeroPiece C hcover).cert.vertexCount = 1 :=
  rfl

theorem closedCertificateOfClosedZeroPiece_vertex (k : Fin 1) :
    (closedCertificateOfClosedZeroPiece C hcover).cert.vertex k = .closedZero C :=
  rfl

theorem closedCertificateOfClosedZeroPiece_vertex_image (k : Fin 1) :
    ((closedCertificateOfClosedZeroPiece C hcover).cert.vertex k).image = univ :=
  hcover

@[simp]
theorem closedCertificateOfClosedZeroPiece_region :
    (closedCertificateOfClosedZeroPiece C hcover).cert.circ.region = ∅ :=
  CircleRegion.empty_region W

@[simp]
theorem closedCertificateOfClosedZeroPiece_faceCount :
    (closedCertificateOfClosedZeroPiece C hcover).cert.faceCount = 0 :=
  rfl

end ClosedZero

/-- The binding shape: a closed zero piece covering `W` gives a closed certificate. -/
theorem nonempty_closedDecompositionCertificate_of_closedZeroPiece {W : CompactCarrier.{u}}
    (C : ClosedZeroPiece W) (hcover : range C.piece.map = univ) :
    Nonempty (ClosedDecompositionCertificate W) :=
  ⟨closedCertificateOfClosedZeroPiece C hcover⟩

end GC.GraphManifold.Assembly
