import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Blocks

/-!
# Flattening Seifert blocks

Chapter 6, packet K21 (review item 5.2). A torus presentation does not determine a circle
fibration of its pieces, so the raw certificate of a Seifert block is rebuilt from the block
itself. `SeifertBlock.pieceFibration` fibres every piece: the product piece by the fibration of
its `ProductFibredPiece`, and each solid torus by the disc bundle `P₁ × S¹` of its own product
identification, the fibration that `GM/SolidTorus.lean` and `GM/Sphere.lean` use for the Clifford
solid tori (`CircleFibration.ofProductDiffeomorph`). `SeifertBlock.toRaw` is
`presentation.withFibration pieceFibration`; its torus presentation is `presentation` by `rfl`, so
orientations, ownership, sides and external collars are those of the block, stated field by field.
On the product piece and on each solid torus the fibration is that of the block
(`toRaw_fibration_product`, `toRaw_fibration_solid`), whose projection sends every port collar
to the base collar (`ProductFibredPiece.fibration_projection_pieceCollar`).

The ports of K03 lift to blocks. A diffeomorphism or the opposite orientation keeps the cut
carrier, the pieces and the sides, so `SeifertBlock.transport` and `SeifertBlock.opposite` keep
all block data; only the owned sides are re-indexed (`ownedSideTransport`, `ownedSideOpposite`),
since the side maps are definitions by `match`. Then `toRaw` commutes with both
(`toRaw_transport` by `rfl`, `toRaw_opposite` piece by piece). A block is of the shape produced
by `ofPiece` (one piece, no seams) exactly when it has no fillings, `d.ports = d.k`
(`components_count_eq_one_iff`); for every block, `toRaw_ofPiece` identifies the raw restriction
to a piece with the restricted torus presentation fibred by that piece's fibration.

A torus presentation all of whose pieces are product fibred, as is a flattened union of Seifert
blocks, is raw by `toRawOfProductPieces`. Flattening a presentation whose pieces are themselves
filled blocks needs a substitution of presentations into pieces, which is not built here.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace TorusPresentation

variable {W W' : CompactCarrier.{u}}

theorem sidePiece_transport (T : TorusPresentation.{u} W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (T.transport e he).sidePiece = T.sidePiece := by
  funext s
  rcases s with k | k | k <;> rfl

theorem sideCollar_transport (T : TorusPresentation.{u} W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (T.transport e he).sideCollar = T.sideCollar := by
  funext s
  rcases s with k | k | k <;> rfl

theorem sidePiece_opposite (T : TorusPresentation.{u} W) :
    T.opposite.sidePiece = T.sidePiece := by
  funext s
  rcases s with k | k | k <;> rfl

theorem sideCollar_opposite (T : TorusPresentation.{u} W) :
    T.opposite.sideCollar = T.sideCollar := by
  funext s
  rcases s with k | k | k <;> rfl

def ownedSideTransport (T : TorusPresentation.{u} W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) (i : Fin T.components.count) :
    T.OwnedSide i ≃ (T.transport e he).OwnedSide i :=
  Equiv.subtypeEquivRight fun s => by rw [sidePiece_transport]; exact Iff.rfl

def ownedSideOpposite (T : TorusPresentation.{u} W) (i : Fin T.components.count) :
    T.OwnedSide i ≃ T.opposite.OwnedSide i :=
  Equiv.subtypeEquivRight fun s => by rw [sidePiece_opposite]; exact Iff.rfl

@[simp]
theorem ownedSideTransport_val (T : TorusPresentation.{u} W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) (i : Fin T.components.count)
    (s : T.OwnedSide i) : (T.ownedSideTransport e he i s).val = s.val := rfl

@[simp]
theorem ownedSideOpposite_val (T : TorusPresentation.{u} W) (i : Fin T.components.count)
    (s : T.OwnedSide i) : (T.ownedSideOpposite i s).val = s.val := rfl

theorem pieceCollar_transport (T : TorusPresentation.{u} W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) (i : Fin T.components.count)
    (s : T.OwnedSide i) :
    (T.transport e he).pieceCollar i (T.ownedSideTransport e he i s) = T.pieceCollar i s := by
  simp only [pieceCollar, sideCollar_transport]
  rfl

theorem pieceCollar_opposite (T : TorusPresentation.{u} W) (i : Fin T.components.count)
    (s : T.OwnedSide i) :
    T.opposite.pieceCollar i (T.ownedSideOpposite i s) = T.pieceCollar i s := by
  simp only [pieceCollar, sideCollar_opposite]
  rfl

def toRawOfProductPieces (T : TorusPresentation.{u} W) (k : Fin T.components.count → ℕ)
    (P : (i : Fin T.components.count) → ProductFibredPiece T i (k i)) : RawGraphPresentation W :=
  T.withFibration fun i => (P i).fibration

@[simp]
theorem toTorusPresentation_toRawOfProductPieces (T : TorusPresentation.{u} W)
    (k : Fin T.components.count → ℕ)
    (P : (i : Fin T.components.count) → ProductFibredPiece T i (k i)) :
    (T.toRawOfProductPieces k P).toTorusPresentation = T := rfl

theorem toRawOfProductPieces_fibration (T : TorusPresentation.{u} W)
    (k : Fin T.components.count → ℕ)
    (P : (i : Fin T.components.count) → ProductFibredPiece T i (k i))
    (i : Fin T.components.count) :
    (T.toRawOfProductPieces k P).fibration i = (P i).fibration := rfl

end TorusPresentation

namespace ProductFibredPiece

variable {W W' : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {i : Fin T.components.count} {k : ℕ}

def transport (P : ProductFibredPiece T i k) (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    ProductFibredPiece (T.transport e he) i k where
  base := P.base
  port := P.port.trans (T.ownedSideTransport e he i)
  trivialization := P.trivialization
  collar_eq j p hp := by
    rw [Equiv.trans_apply, T.pieceCollar_transport]
    exact P.collar_eq j p hp

def opposite (P : ProductFibredPiece T i k) : ProductFibredPiece T.opposite i k where
  base := P.base
  port := P.port.trans (T.ownedSideOpposite i)
  trivialization := P.trivialization
  collar_eq j p hp := by
    rw [Equiv.trans_apply, T.pieceCollar_opposite]
    exact P.collar_eq j p hp

theorem fibration_transport (P : ProductFibredPiece T i k)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (P.transport e he).fibration = P.fibration := rfl

theorem fibration_opposite (P : ProductFibredPiece T i k) :
    P.opposite.fibration = P.fibration.opposite := rfl

end ProductFibredPiece

namespace SeifertBlock

variable {W W' : CompactCarrier.{u}} {d : SeifertData}

def blockFibration (B : SeifertBlock W d) : (o : Option (Fin d.fillingCount)) →
    CircleFibration B.presentation.cutCarrier (B.presentation.components.piece (B.piece o))
  | none => B.product.fibration
  | some m => (B.solid m).fibration

def pieceFibration (B : SeifertBlock W d) : B.presentation.Fibration :=
  Equiv.piCongrLeft (fun i => CircleFibration B.presentation.cutCarrier
    (B.presentation.components.piece i)) B.piece B.blockFibration

theorem pieceFibration_piece (B : SeifertBlock W d) (o : Option (Fin d.fillingCount)) :
    B.pieceFibration (B.piece o) = B.blockFibration o :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

@[simp]
theorem pieceFibration_product (B : SeifertBlock W d) :
    B.pieceFibration (B.piece none) = B.product.fibration :=
  B.pieceFibration_piece none

@[simp]
theorem pieceFibration_solid (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.pieceFibration (B.piece (some m)) = (B.solid m).fibration :=
  B.pieceFibration_piece (some m)

def toRaw (B : SeifertBlock W d) : RawGraphPresentation W :=
  B.presentation.withFibration B.pieceFibration

@[simp]
theorem toRaw_toTorusPresentation (B : SeifertBlock W d) :
    B.toRaw.toTorusPresentation = B.presentation := rfl

theorem toRaw_fibration (B : SeifertBlock W d) : B.toRaw.fibration = B.pieceFibration := rfl

@[simp]
theorem toRaw_cutCarrier (B : SeifertBlock W d) :
    B.toRaw.cutCarrier = B.presentation.cutCarrier := rfl

theorem toRaw_cutCarrier_orientation (B : SeifertBlock W d) :
    B.toRaw.cutCarrier.orientation = B.presentation.cutCarrier.orientation := rfl

@[simp]
theorem toRaw_reconstruction (B : SeifertBlock W d) :
    B.toRaw.reconstruction = B.presentation.reconstruction := rfl

@[simp]
theorem toRaw_pairing (B : SeifertBlock W d) : B.toRaw.pairing = B.presentation.pairing := rfl

@[simp]
theorem toRaw_components (B : SeifertBlock W d) :
    B.toRaw.components = B.presentation.components := rfl

@[simp]
theorem toRaw_leftPiece (B : SeifertBlock W d) :
    B.toRaw.leftPiece = B.presentation.leftPiece := rfl

@[simp]
theorem toRaw_rightPiece (B : SeifertBlock W d) :
    B.toRaw.rightPiece = B.presentation.rightPiece := rfl

@[simp]
theorem toRaw_externalPiece (B : SeifertBlock W d) :
    B.toRaw.externalPiece = B.presentation.externalPiece := rfl

theorem toRaw_sidePiece (B : SeifertBlock W d) : B.toRaw.sidePiece = B.presentation.sidePiece :=
  (RawGraphPresentation.toTorusPresentation_sidePiece B.toRaw).symm

theorem toRaw_ownedSide (B : SeifertBlock W d) (i : Fin B.presentation.components.count) :
    B.toRaw.OwnedSide i = B.presentation.OwnedSide i :=
  (RawGraphPresentation.toTorusPresentation_ownedSide B.toRaw i).symm

@[simp]
theorem toRaw_externalCount (B : SeifertBlock W d) :
    B.toRaw.externalCount = B.presentation.externalCount := rfl

@[simp]
theorem toRaw_external (B : SeifertBlock W d) : B.toRaw.external = B.presentation.external := rfl

@[simp]
theorem toRaw_cutExternal (B : SeifertBlock W d) :
    B.toRaw.cutExternal = B.presentation.cutExternal := rfl

@[simp]
theorem toRaw_seam (B : SeifertBlock W d) : B.toRaw.seam = B.presentation.seam := rfl

theorem toRaw_sideCollar (B : SeifertBlock W d) :
    B.toRaw.sideCollar = B.presentation.sideCollar :=
  (RawGraphPresentation.toTorusPresentation_sideCollar B.toRaw).symm

@[simp]
theorem toRaw_fibration_product (B : SeifertBlock W d) :
    B.toRaw.fibration (B.piece none) = B.product.fibration :=
  B.pieceFibration_product

@[simp]
theorem toRaw_fibration_solid (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.toRaw.fibration (B.piece (some m)) = (B.solid m).fibration :=
  B.pieceFibration_solid m

def transport (B : SeifertBlock W d) (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) : SeifertBlock W' d where
  presentation := B.presentation.transport e he
  piece := B.piece
  product := B.product.transport e he
  solid m := (B.solid m).transport e he
  port := B.port
  seam := B.seam
  free := B.free
  free_port := B.free_port
  filled_port := B.filled_port
  solid_port := B.solid_port
  slope := B.slope

def opposite (B : SeifertBlock W d) : SeifertBlock W.opposite d where
  presentation := B.presentation.opposite
  piece := B.piece
  product := B.product.opposite
  solid m := (B.solid m).opposite
  port := B.port
  seam := B.seam
  free := B.free
  free_port := B.free_port
  filled_port := B.filled_port
  solid_port := B.solid_port
  slope := B.slope

@[simp]
theorem transport_presentation (B : SeifertBlock W d)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (B.transport e he).presentation = B.presentation.transport e he := rfl

@[simp]
theorem opposite_presentation (B : SeifertBlock W d) :
    B.opposite.presentation = B.presentation.opposite := rfl

theorem pieceFibration_transport (B : SeifertBlock W d)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (B.transport e he).pieceFibration = B.pieceFibration := rfl

theorem toRaw_transport (B : SeifertBlock W d)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (B.transport e he).toRaw = B.toRaw.transport e he := rfl

theorem pieceFibration_opposite (B : SeifertBlock W d) (i : Fin B.presentation.components.count) :
    B.opposite.pieceFibration i = (B.pieceFibration i).opposite := by
  obtain ⟨o, rfl⟩ := B.piece.surjective i
  refine (B.opposite.pieceFibration_piece o).trans ?_
  rw [B.pieceFibration_piece o]
  cases o <;> rfl

theorem toRaw_opposite (B : SeifertBlock W d) : B.opposite.toRaw = B.toRaw.opposite :=
  congrArg B.opposite.presentation.withFibration (funext B.pieceFibration_opposite)

theorem opposite_transport (B : SeifertBlock W d)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (B.transport e he).opposite =
      B.opposite.transport (W' := W'.opposite) e
        (Diffeomorph.preservesOrientation_opposite he) := rfl

theorem isGoodBlock_opposite_iff (B : SeifertBlock W d) : B.opposite.IsGoodBlock ↔ B.IsGoodBlock :=
  Iff.rfl

theorem components_count_eq_one_iff (B : SeifertBlock W d) :
    B.presentation.components.count = 1 ↔ d.ports = d.k := by
  have h := d.ports_add_fillingCount
  rw [B.components_count]
  omega

theorem pairing_count_eq_zero_iff (B : SeifertBlock W d) :
    B.presentation.pairing.count = 0 ↔ d.ports = d.k := by
  have h := d.ports_add_fillingCount
  rw [B.pairing_count]
  omega

theorem toRaw_ofPiece (B : SeifertBlock W d) (i : Fin B.presentation.components.count) :
    B.toRaw.ofPiece i = (B.presentation.ofPiece i).withFibration
      (fun _ => CircleFibration.toComponent B.presentation.components i (B.pieceFibration i)) :=
  RawGraphPresentation.toTorusPresentation_injective_on_fibration
    (Sigma.ext (RawGraphPresentation.toTorusPresentation_ofPiece B.toRaw i) HEq.rfl)

end SeifertBlock

end GC.Seifert
