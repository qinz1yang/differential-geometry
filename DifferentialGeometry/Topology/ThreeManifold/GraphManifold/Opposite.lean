import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Transport
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.OrientationTransport

set_option autoImplicit false

/-!
# Raw graph presentations of the opposite orientation

A raw graph presentation of a compact carrier `W` gives one of `W.opposite`: the cut carrier is
replaced by its opposite and every other datum is kept. The two orientation conditions survive
because `Orientation.map` commutes with negation: the quotient map still carries the (negated)
orientation of the cut carrier to the (negated) orientation of `W`, and the two collars of each
torus pair still induce opposite boundary orientations.

Combined with the orientation dichotomy and `RawGraphPresentation.transport`, a raw graph
presentation of a connected closed oriented manifold gives one of every manifold diffeomorphic
to it, whatever the diffeomorphism does to orientations.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold
universe u

def CircleFibration.opposite {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
    (F : CircleFibration C U) : CircleFibration C.opposite U where
  base := F.base
  projection := F.projection
  surjective := F.surjective
  smooth := F.smooth
  neighborhood := F.neighborhood
  mem_neighborhood := F.mem_neighborhood
  trivialization := F.trivialization
  projection_trivialization := F.projection_trivialization

def BoundaryTori.opposite {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n) :
    BoundaryTori C.opposite n where
  collar := T.collar
  source_eq := T.source_eq
  boundary_zero := T.boundary_zero
  disjoint := T.disjoint

@[simp] theorem BoundaryTori.opposite_collar {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) : T.opposite.collar = T.collar := rfl

@[simp] theorem BoundaryTori.opposite_torusMap {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) : T.opposite.torusMap = T.torusMap := rfl

@[simp] theorem BoundaryTori.opposite_image {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) : T.opposite.image = T.image := rfl

theorem BoundaryTori.opposite_incompressible_iff {C : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori C n) : T.opposite.incompressible ↔ T.incompressible := Iff.rfl

theorem reversesBoundaryOrientation_opposite {C : CompactCarrier.{u}}
    {l r : Torus × EuclideanHalfSpace 1 → C.Carrier}
    (h : ReversesBoundaryOrientation C l r) : ReversesBoundaryOrientation C.opposite l r := by
  intro t
  obtain ⟨L, R, hL, hR, ho⟩ := h t
  refine ⟨L, R, hL, hR, ?_⟩
  change Orientation.map (Fin 3) L.symm (-C.orientation.orientation (l (t, halfZero))) =
    -Orientation.map (Fin 3) R.symm (-C.orientation.orientation (r (t, halfZero)))
  rw [Orientation.map_neg, Orientation.map_neg, ho]

def TorusPairing.opposite {C : CompactCarrier.{u}} (P : TorusPairing C) :
    TorusPairing C.opposite where
  count := P.count
  gluing := P.gluing
  leftParam := P.leftParam
  rightParam := P.rightParam
  matching := P.matching
  matching_eq := P.matching_eq
  leftCollar := P.leftCollar
  rightCollar := P.rightCollar
  left_source := P.left_source
  right_source := P.right_source
  left_zero := P.left_zero
  right_zero := P.right_zero
  reversing i := reversesBoundaryOrientation_opposite (P.reversing i)

@[simp] theorem TorusPairing.opposite_count {C : CompactCarrier.{u}} (P : TorusPairing C) :
    P.opposite.count = P.count := rfl

@[simp] theorem TorusPairing.opposite_gluing {C : CompactCarrier.{u}} (P : TorusPairing C) :
    P.opposite.gluing = P.gluing := rfl

def RawGraphPresentation.opposite {W : CompactCarrier.{u}} (G : RawGraphPresentation W) :
    RawGraphPresentation W.opposite where
  cutCarrier := G.cutCarrier.opposite
  components := G.components.opposite
  fibration i := (G.fibration i).opposite
  pairing := G.pairing.opposite
  externalCount := G.externalCount
  external := G.external.opposite
  cutExternal := G.cutExternal.opposite
  external_exhausted := G.external_exhausted
  cut_boundary_exhausted := G.cut_boundary_exhausted
  external_disjoint := G.external_disjoint
  reconstruction := G.reconstruction
  quotient_smooth := G.quotient_smooth
  quotient_oriented := by
    intro x
    obtain ⟨L, hL, ho⟩ := G.quotient_oriented x
    exact ⟨L, hL, (Orientation.map_neg _ _).trans (congrArg Neg.neg ho)⟩
  interiorImage := G.interiorImage
  interiorDiffeomorph := G.interiorDiffeomorph
  interior_map := G.interior_map
  seam := G.seam
  seam_source := G.seam_source
  seam_zero := G.seam_zero
  seam_positive := G.seam_positive
  seam_negative := G.seam_negative
  seam_interior := G.seam_interior
  seam_disjoint := G.seam_disjoint
  marked_collar := G.marked_collar
  external_seam_disjoint := G.external_seam_disjoint
  leftPiece := G.leftPiece
  rightPiece := G.rightPiece
  left_owned := G.left_owned
  right_owned := G.right_owned
  externalPiece := G.externalPiece
  external_owned := G.external_owned

namespace RawGraphPresentation
variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)

@[simp] theorem opposite_cutCarrier : G.opposite.cutCarrier = G.cutCarrier.opposite := rfl

@[simp] theorem opposite_components : G.opposite.components = G.components.opposite := rfl

@[simp] theorem opposite_pairing : G.opposite.pairing = G.pairing.opposite := rfl

@[simp] theorem opposite_externalCount : G.opposite.externalCount = G.externalCount := rfl

@[simp] theorem opposite_external : G.opposite.external = G.external.opposite := rfl

@[simp] theorem opposite_cutExternal : G.opposite.cutExternal = G.cutExternal.opposite := rfl

@[simp] theorem opposite_interiorImage : G.opposite.interiorImage = G.interiorImage := rfl

@[simp] theorem opposite_leftPiece : G.opposite.leftPiece = G.leftPiece := rfl

@[simp] theorem opposite_rightPiece : G.opposite.rightPiece = G.rightPiece := rfl

@[simp] theorem opposite_externalPiece : G.opposite.externalPiece = G.externalPiece := rfl

theorem opposite_reconstruction_apply (q : G.pairing.QuotientSpace) :
    G.opposite.reconstruction q = G.reconstruction q := rfl

theorem opposite_seam_apply (i : Fin G.pairing.count) (p : Torus × ℝ) :
    G.opposite.seam i p = G.seam i p := rfl

theorem opposite_transport {W' : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (G.transport e he).opposite =
      G.opposite.transport (W' := W'.opposite) e
        (Diffeomorph.preservesOrientation_opposite he) := rfl

end RawGraphPresentation

theorem rawGraphPresentation_of_diffeomorph {M N : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M))
    (f : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier) :
    Nonempty (RawGraphPresentation (NoCuts.carrier N)) := by
  rcases f.preservesOrientation_or_preservesOrientation_opposite
    M.orientation N.orientation with hf | hf
  · exact ⟨G.transport f hf⟩
  · have hp : f.preservesOrientation M.orientation.opposite N.orientation := by
      simpa only [ManifoldOrientation.opposite_opposite] using
        Diffeomorph.preservesOrientation_opposite hf
    exact ⟨G.opposite.transport (W' := NoCuts.carrier N) f hp⟩

end GC.GraphManifold
