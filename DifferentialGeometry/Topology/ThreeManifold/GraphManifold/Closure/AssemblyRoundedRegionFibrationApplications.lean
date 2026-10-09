import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionFibration

/-!
# Consumers of FC42 packet T2: the rounded circle region as finitely many circle-fibred pieces

* `CircleRegion.exists_roundedRegion_pieces` (consumer of T2a and T2b): the rounded circle region is a
  finite disjoint union of `PieceEmbedding`s, in the output shape of B1-interior
  (`exists_pieces_of_interior_sublevel`, here for `f = rounding ∘ proj` on `domain`), each carrying a
  circle fibration over a compact surface, with boundary the preimage of the base boundary;
* `CircleRegion.rawPiece_of_roundedRegionPiece_of_boundaryTori` (consumer of the Raw constructor): with
  any boundary-torus family of the piece exhausting its boundary, the piece is a Raw piece in the
  `hpiece` format of B3 (`exists_rawGraphPresentation_of_regularCutData`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- **The rounded circle region in pieces.** -/
theorem exists_roundedRegion_pieces :
    ∃ (m : ℕ) (P : Fin m → PieceEmbedding W),
      (⋃ k, range (P k).map) = {x | x ∈ R.domain ∧ R.roundedFunction x ≤ 0} ∧
      Pairwise (fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      (∀ k q, (𝓡∂ 3).IsBoundaryPoint q ↔ R.roundedFunction ((P k).map q) = 0) ∧
      ∀ k, ∃ F : CircleFibration (P k).toCarrier ⊤,
        (𝓡∂ 3).boundary (P k).Piece = (fun q => F.projection ⟨q, trivial⟩) ⁻¹'
          (SurfaceModel.model F.base.kind).boundary F.base.Carrier := by
  let e := Finite.equivFin (ConnectedComponents R.roundedBase)
  refine ⟨Nat.card (ConnectedComponents R.roundedBase), fun k => R.roundedRegionPiece (e.symm k),
    ?_, ?_, fun k q => roundedRegionPiece_isBoundaryPoint_iff, fun k =>
    ⟨R.roundedRegionFibration (e.symm k), R.roundedRegionPiece_boundary_eq (e.symm k)⟩⟩
  · rw [← R.rounded_eq_sublevel, ← R.iUnion_range_roundedRegionPiece]
    exact e.symm.surjective.iUnion_comp fun j => range (R.roundedRegionPiece j).map
  · intro k k' hkk'
    exact R.pairwise_disjoint_range_roundedRegionPiece (e.symm.injective.ne hkk')

/-- **Raw piece from boundary tori.** -/
theorem rawPiece_of_roundedRegionPiece_of_boundaryTori (j : ConnectedComponents R.roundedBase)
    {n : ℕ} (E : BoundaryTori (R.roundedRegionPiece j).toCarrier n)
    (hb : (R.roundedRegionPiece j).toCarrier.model.boundary
      (R.roundedRegionPiece j).toCarrier.Carrier = E.image) :
    ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (R.roundedRegionPiece j).Piece) :=
  ⟨(R.roundedRegionPiece j).toCarrier, ⟨R.roundedRegionRawPresentation j E hb⟩,
    ⟨show (R.roundedRegionPiece j).toCarrier.Carrier ≃ₘ⟮(R.roundedRegionPiece j).toCarrier.model,
      𝓡∂ 3⟯ (R.roundedRegionPiece j).Piece from
      Diffeomorph.refl (𝓡∂ 3) (R.roundedRegionPiece j).Piece ∞⟩⟩

end CircleRegion

end GC.GraphManifold.Assembly
