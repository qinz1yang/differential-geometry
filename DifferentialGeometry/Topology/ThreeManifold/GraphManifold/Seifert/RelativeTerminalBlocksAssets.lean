import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksKept
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksTransfer

/-!
# Composition and interior restriction of actual piece transfers

Full compact transfers compose with their exact half collars. Their interior restrictions
transport geometries without changing the model or replacing the compact carrier.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.PieceTransfer

variable {W V Z : CompactCarrier.{u}} {T : TorusPresentation W} {U : TorusPresentation V}
  {R : TorusPresentation Z} {i : Fin T.components.count} {j : Fin U.components.count}
  {k : Fin R.components.count}

def relativeTrans (τ : PieceTransfer T i U j) (υ : PieceTransfer U j R k) :
    PieceTransfer T i R k where
  map := τ.map.trans υ.map
  side := τ.side.trans υ.side
  collar_eq s p hp := by
    rw [Equiv.trans_apply, υ.collar_eq _ p hp, τ.collar_eq _ p hp]
    rfl

def relativeInteriorDiffeomorph (τ : PieceTransfer T i U j) :
    T.cutCarrier.pieceInterior (T.components.piece i) ≃ₘ⟮T.cutCarrier.model,
      U.cutCarrier.model⟯ U.cutCarrier.pieceInterior (U.components.piece j) := by
  let C := componentCarrier T.cutCarrier T.components i
  let D := componentCarrier U.cutCarrier U.components j
  let et : (⊤ : TopologicalSpace.Opens C.Carrier) ≃ₘ⟮C.model, D.model⟯
      (⊤ : TopologicalSpace.Opens D.Carrier) :=
    (topOpensDiffeomorph (I := C.model) C.Carrier).trans
      (τ.map.trans (topOpensDiffeomorph (I := D.model) D.Carrier).symm)
  exact (componentInteriorDiffeomorph T.cutCarrier T.components i).symm.trans
    ((pieceInteriorCongr et).trans (componentInteriorDiffeomorph U.cutCarrier U.components j))

def relativeGeometry (τ : PieceTransfer T i U j)
    (g : T.cutCarrier.InteriorGeometry (T.components.piece i)) :
    U.cutCarrier.InteriorGeometry (U.components.piece j) :=
  transportInteriorGeometry τ.relativeInteriorDiffeomorph.symm g

theorem relativeGeometry_model (τ : PieceTransfer T i U j)
    (g : T.cutCarrier.InteriorGeometry (T.components.piece i)) :
    letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := Manifold.interiorChartedSpace U.cutCarrier.model ∞
      (M := U.cutCarrier.pieceInterior (U.components.piece j))
    letI := Manifold.interiorIsManifold U.cutCarrier.model ∞
      (M := U.cutCarrier.pieceInterior (U.components.piece j))
    (τ.relativeGeometry g).model = g.model := rfl

end GC.Seifert.PieceTransfer
