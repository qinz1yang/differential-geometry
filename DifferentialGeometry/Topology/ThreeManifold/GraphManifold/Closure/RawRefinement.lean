import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeProof

/-!
Raw assembly from compatible actual local cut systems and their local circle fibrations.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def fibredRefinementPieceDiffeomorph {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k) (J : Fin R.count) :
    R.splice.components.piece J ≃ₘ⟮k.model, k.model⟯
      (R.system (R.pieceIndex J).1).components.piece (R.pieceIndex J).2 := by
  let e : (R.system (R.pieceIndex J).1).Piece (R.pieceIndex J).2
      ≃ₘ⟮k.model, k.model⟯ R.splice.components.piece J :=
    R.splice.pieceDiffeomorph J
  exact e.symm.trans ((R.system (R.pieceIndex J).1).pieceDiffeomorph (R.pieceIndex J).2)

def fibredRefinementFibration {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) :
    R.splice.toTorusPresentation.Fibration := fun J =>
  (F (R.pieceIndex J).1 (R.pieceIndex J).2).ofDiffeomorph
    (fibredRefinementPieceDiffeomorph T R J)

theorem fibredRefinementFibration_projection {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration)
    (J : Fin R.count) (x : R.splice.components.piece J) :
    (fibredRefinementFibration T R F J).projection x =
      (F (R.pieceIndex J).1 (R.pieceIndex J).2).projection
        (fibredRefinementPieceDiffeomorph T R J x) := rfl

def rawGraphPresentation_of_fibredRefinement {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) : RawGraphPresentation W :=
  R.splice.toTorusPresentation.withFibration (fibredRefinementFibration T R F)

theorem rawGraphPresentation_of_fibredRefinement_toTorusPresentation
    {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) :
    (rawGraphPresentation_of_fibredRefinement T R F).toTorusPresentation =
      R.splice.toTorusPresentation := rfl

theorem rawGraphPresentation_of_fibredRefinement_externalCount
    {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) :
    (rawGraphPresentation_of_fibredRefinement T R F).externalCount = T.externalCount := rfl

theorem rawGraphPresentation_of_fibredRefinement_external_collar
    {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) (i : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (rawGraphPresentation_of_fibredRefinement T R F).external.collar i p =
      T.external.collar i p :=
  R.splice_external_collar i hp

theorem rawGraphPresentation_of_fibredRefinement_seam_old
    {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) (j : Fin T.pairing.count) :
    (rawGraphPresentation_of_fibredRefinement T R F).seam (finSumFinEquiv (.inr j)) =
      T.seam j :=
  R.splice_seam_old j

theorem rawGraphPresentation_of_fibredRefinement_matching_old
    {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) (j : Fin T.pairing.count) :
    (rawGraphPresentation_of_fibredRefinement T R F).pairing.matching
      (finSumFinEquiv (.inr j)) = T.pairing.matching j :=
  R.splice_matching_old j

theorem rawGraphPresentation_of_fibredRefinement_counts
    {W : CompactCarrier.{u}} {k : CarrierModel}
    (T : TorusPresentation W) (R : T.Refinement k)
    (F : ∀ i, (R.system i).toTorusPresentation.Fibration) :
    (rawGraphPresentation_of_fibredRefinement T R F).components.count = R.count ∧
    (rawGraphPresentation_of_fibredRefinement T R F).pairing.count =
      R.newSeamCount + T.pairing.count ∧
    (rawGraphPresentation_of_fibredRefinement T R F).externalCount = T.externalCount :=
  ⟨rfl, rfl, rfl⟩

end GC.GraphManifold
