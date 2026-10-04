import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
A raw presentation of a single circle-fibred compact carrier, with its actual boundary collars.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private def singlePieceTorusPresentation (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier]
    {n : ℕ} (E : BoundaryTori C n) (hb : C.model.boundary C.Carrier = E.image) :
    TorusPresentation C where
  cutCarrier := C
  components := singleComponents C (connectedSpace_pieceInterior_top C)
  pairing := emptyTorusPairing C
  externalCount := n
  external := E
  cutExternal := E
  external_exhausted := hb
  cut_boundary_exhausted := by
    rw [iUnion_block_emptyTorusPairing, empty_union]
    exact hb
  external_disjoint := by
    rw [iUnion_block_emptyTorusPairing]
    exact empty_disjoint E.image
  reconstruction := emptyTorusPairingHomeomorph C
  quotient_smooth := contMDiff_id
  quotient_oriented x := by
    refine ⟨LinearEquiv.refl ℝ _, fun v => ?_, ?_⟩
    · change v = mfderiv C.model C.model (id : C.Carrier → C.Carrier) x v
      rw [mfderiv_id]
      rfl
    · change Orientation.map (Fin 3) (LinearEquiv.refl ℝ (TangentSpace C.model x))
        (C.orientation.orientation x) = C.orientation.orientation x
      rw [Orientation.map_refl]
      rfl
  interiorImage := C.interior
  interiorDiffeomorph := Diffeomorph.refl C.model C.interior ∞
  interior_map x := rfl
  seam j := j.elim0
  seam_source j := j.elim0
  seam_zero j := j.elim0
  seam_positive j := j.elim0
  seam_negative j := j.elim0
  seam_interior j := j.elim0
  seam_disjoint j := j.elim0
  marked_collar i p hp := rfl
  external_seam_disjoint i j := j.elim0
  leftPiece j := j.elim0
  rightPiece j := j.elim0
  left_owned j := j.elim0
  right_owned j := j.elim0
  externalPiece i := ⟨0, Nat.one_pos⟩
  external_owned i := subset_univ _

def singlePieceRawPresentation (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier]
    (F : CircleFibration C ⊤) {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = E.image) : RawGraphPresentation C :=
  (singlePieceTorusPresentation C E hb).withFibration fun i => Fin.cases F (fun j => j.elim0) i

theorem singlePieceRawPresentation_components_count
    (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier]
    (F : CircleFibration C ⊤) {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = E.image) :
    (singlePieceRawPresentation C F E hb).components.count = 1 := rfl

theorem singlePieceRawPresentation_pairing_count
    (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier]
    (F : CircleFibration C ⊤) {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = E.image) :
    (singlePieceRawPresentation C F E hb).pairing.count = 0 := rfl

theorem singlePieceRawPresentation_external_count
    (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier]
    (F : CircleFibration C ⊤) {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = E.image) :
    (singlePieceRawPresentation C F E hb).externalCount = n := rfl

theorem singlePieceRawPresentation_external_collar
    (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier]
    (F : CircleFibration C ⊤) {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = E.image) (i : Fin n)
    (p : Torus × EuclideanHalfSpace 1) :
    (singlePieceRawPresentation C F E hb).external.collar i p = E.collar i p := rfl

end GC.GraphManifold
