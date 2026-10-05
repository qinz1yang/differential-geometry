import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SphereBalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

/-!
A nondegenerate V4 decomposition of the standard three-sphere into two actual hemisphere balls.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.Assembly

private def sphereCertificateVertex (k : Fin 2) :
    Vertex (NoCuts.carrier standardThreeSphereLift.{u}) :=
  .zero (standardS3HemispherePiece (k == 1)) (.ball (standardS3HemisphereBall (k == 1)))

private def sphereCertificateSide (b : Bool) : Fin 2 :=
  if b then 0 else 1

private def sphereCertificateFaceKind (f : Fin 2) : FaceKind 0 0 1 :=
  .sphereSeam 0 (f == 0)

def standardSphereCertificate :
    DecompositionCertificate (NoCuts.carrier standardThreeSphereLift.{u})
      (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{u})) where
  external_exhausted := by
    rw [BoundaryTori.empty_image]
    exact closedCarrier_boundary_eq_empty _
  vertexCount := 2
  vertex := sphereCertificateVertex
  handleCount := 0
  handle h := h.elim0
  edgeCircleCount := 0
  edgeCircle e := e.elim0
  circ := CircleRegion.empty _
  cover := by
    apply eq_univ_of_univ_subset
    intro x hx
    have hc := standardS3HemispherePiece_cover.{u}
    have hm : x ∈ range (standardS3HemispherePiece false).map ∪
        range (standardS3HemispherePiece true).map := hc.symm ▸ mem_univ x
    rcases hm with hn | hp
    · exact Or.inl (Or.inl (Or.inl (mem_iUnion.mpr ⟨0, hn⟩)))
    · exact Or.inl (Or.inl (Or.inl (mem_iUnion.mpr ⟨1, hp⟩)))
  vertex_disjoint := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact (hkl rfl).elim
    · exact standardS3HemispherePiece_interiors_disjoint
    · exact standardS3HemispherePiece_interiors_disjoint.symm
    · exact (hkl rfl).elim
  handle_disjoint h := h.elim0
  edgeCircle_disjoint e := e.elim0
  vertex_handle_disjoint k h := h.elim0
  edgeCircle_vertex_disjoint e := e.elim0
  edgeCircle_handle_disjoint e := e.elim0
  circ_vertex_disjoint k := by
    rw [CircleRegion.empty_region, interior_empty]
    exact empty_disjoint _
  circ_handle_disjoint h := h.elim0
  circ_edgeCircle_disjoint e := e.elim0
  vertical_fibre h := h.elim0
  edgeCircle_vertical e := e.elim0
  torusSeamCount := 0
  torusSeam c := c.elim0
  torusSide c := c.elim0
  torusSide_neg c := c.elim0
  torusSide_pos c := c.elim0
  torusSeam_disjoint c := c.elim0
  sphereSeamCount := 1
  sphereSeam c := standardS3EquatorSeam
  sphereSide c := sphereCertificateSide
  sphereSide_neg c z s hs hlo := standardS3EquatorSeam_neg z s hs
  sphereSide_pos c z s hs hhi := standardS3EquatorSeam_pos z s hs
  sphereSeam_disjoint := by
    intro c d hcd
    exact (hcd (Subsingleton.elim c d)).elim
  sphere_torus_seam_disjoint c d := d.elim0
  externalOwner i := i.elim0
  external_owned i := i.elim0
  faceCount := 2
  face f := standardS3Equator
  faceOwner f := f
  faceModel f := Sum.inl standardS3EquatorHomeomorph
  face_exhausted := by
    intro k
    change (⋃ (f : Fin 2) (h : f = k), standardS3Equator) =
      (standardS3HemispherePiece (k == 1)).map ''
        (𝓡∂ 3).boundary (standardS3HemispherePiece (k == 1)).Piece
    rw [standardS3HemispherePiece_boundary]
    ext x
    simp only [mem_iUnion, exists_prop, exists_eq_left]
  faceKind := sphereCertificateFaceKind
  face_disjoint := by
    intro f g hfg hs ht
    fin_cases f <;> fin_cases g
    · exact (hfg rfl).elim
    · exact (hs 0 true ⟨rfl, rfl⟩).elim
    · exact (hs 0 false ⟨rfl, rfl⟩).elim
    · exact (hfg rfl).elim
  face_external := by
    intro f i
    exact i.elim0
  external_face i := i.elim0
  face_torusSeam := by
    intro f c
    exact c.elim0
  torusSeam_face c := c.elim0
  face_sphereSeam := by
    intro f c b hf
    have he : range (fun z : ClosureSphere.{u} => standardS3EquatorSeam.collar (z, 0)) =
        standardS3Equator := by
      apply congrArg range
      funext z
      exact standardS3EquatorSeam_zero z
    refine ⟨he.symm, ?_⟩
    fin_cases f <;> fin_cases c <;> cases b <;>
      simp_all [sphereCertificateFaceKind, sphereCertificateSide]
  sphereSeam_face := by
    intro c b
    fin_cases c
    cases b
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩
  handleEnd h := h.elim0
  handleFace h := h.elim0
  handleFace_owner h := h.elim0
  handleFace_kind h := h.elim0
  handleEnd_face h := h.elim0
  endDisk_disjoint h := h.elim0
  arcFaceCount := 0
  arcFace a := a.elim0
  arcOwner a := a.elim0
  arcOwner_kind a := a.elim0
  arcBase a := a.elim0
  arcBase_embedding a := a.elim0
  arcFace_eq a := a.elim0
  arcDefining a := a.elim0
  arcBase_defining a := a.elim0
  arcAnnulus a := a.elim0
  arcAnnulus_continuous a := a.elim0
  arcAnnulus_injective a := a.elim0
  arcAnnulus_range a := a.elim0
  arcAnnulus_proj a := a.elim0
  loopFaceCount := 0
  loopFace l := l.elim0
  loopOwner l := l.elim0
  loopOwner_kind l := l.elim0
  loopBase l := l.elim0
  loopBase_embedding l := l.elim0
  loopFace_eq l := l.elim0
  loopDefining l := l.elim0
  loopBase_defining l := l.elim0
  loopFace_closed l := l.elim0
  loopFace_nonempty l := l.elim0
  arcFace_disjoint a := a.elim0
  loopFace_disjoint l := l.elim0
  arc_loop_disjoint a := a.elim0
  face_partition := by
    intro f hf
    cases hf
  face_region_inter := by
    intro f hf
    cases hf
  handleArc h := h.elim0
  handleArc_owner h := h.elim0
  handleArc_meets h := h.elim0
  endDisk_loop_disjoint h := h.elim0
  endDisk_rim h := h.elim0
  arcEnd a := a.elim0
  arcEnd_arc a := a.elim0
  arcEnd_injective a := a.elim0
  arcEnd_surjective h := h.elim0
  arcAnnulus_end a := a.elim0
  handleCorner h := h.elim0
  handleCorner_bijective := by
    constructor
    · intro a b
      exact a.1.elim0
    · intro c
      exact c.elim0
  arcBase_end a := a.elim0
  rimChart h := h.elim0
  rim_source h := h.elim0
  rim_proj h := h.elim0
  rim_vertex h := h.elim0
  rim_handle h := h.elim0
  rim_region h := h.elim0
  rim_label h := h.elim0
  rim_disjoint h := h.elim0
  external_region_disjoint i := i.elim0
  external_handle_disjoint i := i.elim0
  external_edgeCircle_disjoint i := i.elim0
  external_torusSeam_disjoint i := i.elim0
  external_sphereSeam_disjoint i := i.elim0
  rim_external_disjoint h := h.elim0
  rim_torusSeam_disjoint h := h.elim0
  rim_sphereSeam_disjoint h := h.elim0
  sphereSeam_region_disjoint c := by
    rw [CircleRegion.empty_region]
    exact disjoint_empty _
  sphereSeam_handle_disjoint c h := h.elim0

theorem exists_standardSphereCertificate :
    ∃ D : DecompositionCertificate (NoCuts.carrier standardThreeSphereLift.{u})
        (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{u})),
      D.vertexCount = 2 ∧ D.sphereSeamCount = 1 ∧ D.faceCount = 2 ∧
        D.handleCount = 0 ∧ D.edgeCircleCount = 0 ∧ D.torusSeamCount = 0 ∧
        D.arcFaceCount = 0 ∧ D.loopFaceCount = 0 :=
  ⟨standardSphereCertificate, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GC.GraphManifold.Assembly
