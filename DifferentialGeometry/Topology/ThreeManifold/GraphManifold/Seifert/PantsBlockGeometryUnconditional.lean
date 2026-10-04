import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBlockGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldFinal

/-!
# Pants blocks are `H² × ℝ`, unconditionally

Chapter 6, packet K16c with K16f. Lane K16f proved the named input `PantsQuotientDiffeo` as
`pantsQuotientDiffeo` (`Seifert/PantsFoldFinal.lean`). Feeding it to the consumers of
`Seifert/PantsBlockGeometry.lean` gives the pants geometries without hypothesis: the interior
identification `pantsCircleInteriorDiffeo'` of the product pants carrier with `PantsQuotient`, the
geometry `productPantsInteriorGeometry'`, its transport `ProductFibredPiece.pantsInteriorGeometry'`
to any product-fibred piece over a `PlanarBase 3`, and `pantsBlockInteriorGeometry'` on the
unfilled pants piece of a Seifert block with `d.k = 3`, all of model `.hyperbolicProduct`.
-/

set_option autoImplicit false

universe u

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

namespace GC.Seifert

def pantsCircleInteriorDiffeo' :
    pantsCircleCarrier.{u}.pieceInterior ⊤ ≃ₘ⟮pantsCircleCarrier.{u}.model, 𝓡 3⟯
      PantsQuotient :=
  pantsCircleInteriorDiffeo pantsQuotientDiffeo

def productPantsInteriorGeometry' : pantsCircleCarrier.{u}.InteriorGeometry ⊤ :=
  productPantsInteriorGeometry pantsQuotientDiffeo

theorem productPantsInteriorGeometry'_model :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace pantsCircleCarrier.{u}.model ∞
      (M := pantsCircleCarrier.{u}.pieceInterior ⊤)
    letI := DifferentialGeometry.Manifold.interiorIsManifold pantsCircleCarrier.{u}.model ∞
      (M := pantsCircleCarrier.{u}.pieceInterior ⊤)
    productPantsInteriorGeometry'.{u}.model = ThurstonModel.hyperbolicProduct :=
  productPantsInteriorGeometry_model pantsQuotientDiffeo

section Piece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def ProductFibredPiece.pantsInteriorDiffeo' (P : ProductFibredPiece T i k) (hk : k = 3) :
    T.cutCarrier.pieceInterior (T.components.piece i) ≃ₘ⟮T.cutCarrier.model, 𝓡 3⟯
      PantsQuotient :=
  P.pantsInteriorDiffeo hk pantsQuotientDiffeo

def ProductFibredPiece.pantsInteriorGeometry' (P : ProductFibredPiece T i k) (hk : k = 3) :
    T.cutCarrier.InteriorGeometry (T.components.piece i) :=
  P.pantsInteriorGeometry hk pantsQuotientDiffeo

theorem ProductFibredPiece.pantsInteriorGeometry'_model (P : ProductFibredPiece T i k)
    (hk : k = 3) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := DifferentialGeometry.Manifold.interiorIsManifold T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    (P.pantsInteriorGeometry' hk).model = ThurstonModel.hyperbolicProduct :=
  P.pantsInteriorGeometry_model hk pantsQuotientDiffeo

end Piece

def pantsBlockInteriorGeometry' {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (hk : d.k = 3) :
    B.presentation.cutCarrier.InteriorGeometry (B.presentation.components.piece (B.piece none)) :=
  pantsBlockInteriorGeometry B hk pantsQuotientDiffeo

theorem pantsBlockInteriorGeometry'_model {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (hk : d.k = 3) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    letI := DifferentialGeometry.Manifold.interiorIsManifold B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    (pantsBlockInteriorGeometry' B hk).model = ThurstonModel.hyperbolicProduct :=
  pantsBlockInteriorGeometry_model B hk pantsQuotientDiffeo

end GC.Seifert
