import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerKept
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry

/-!
# Actual kept interior geometries under selected contraction

The compact kept-component diffeomorphism restricts to actual intrinsic interiors. Transport
through the component-interior identifications preserves the geometry model. Thus frozen
hyperbolic geometries can be retained through selected contraction without assuming an
extension of a bare interior comparison or choosing new collars.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))
  {i : Fin T.components.count} (hi : i ∉ S)

def relativeKeptInteriorDiffeomorph :
    T.cutCarrier.pieceInterior (T.components.piece i) ≃ₘ⟮T.cutCarrier.model,
      (T.contractAlong S K hK hext hk hconn).cutCarrier.model⟯
      (T.contractAlong S K hK hext hk hconn).cutCarrier.pieceInterior
        ((T.contractAlong S K hK hext hk hconn).components.piece
          (T.contractAlongKeptIndex S K hK hext hk hconn hi)) := by
  let U := T.contractAlong S K hK hext hk hconn
  let j := T.contractAlongKeptIndex S K hK hext hk hconn hi
  let C := componentCarrier T.cutCarrier T.components i
  let D := componentCarrier U.cutCarrier U.components j
  let e := T.contractAlongKeptDiffeomorph S K hK hext hk hconn hi
  let et : (⊤ : TopologicalSpace.Opens C.Carrier) ≃ₘ⟮C.model, D.model⟯
      (⊤ : TopologicalSpace.Opens D.Carrier) :=
    (topOpensDiffeomorph (I := C.model) C.Carrier).trans
      (e.trans (topOpensDiffeomorph (I := D.model) D.Carrier).symm)
  exact (componentInteriorDiffeomorph T.cutCarrier T.components i).symm.trans
    ((pieceInteriorCongr et).trans (componentInteriorDiffeomorph U.cutCarrier U.components j))

def relativeKeptGeometry (g : T.cutCarrier.InteriorGeometry (T.components.piece i)) :
    (T.contractAlong S K hK hext hk hconn).cutCarrier.InteriorGeometry
      ((T.contractAlong S K hK hext hk hconn).components.piece
        (T.contractAlongKeptIndex S K hK hext hk hconn hi)) :=
  transportInteriorGeometry (T.relativeKeptInteriorDiffeomorph S K hK hext hk hconn hi).symm g

theorem relativeKeptGeometry_model
    (g : T.cutCarrier.InteriorGeometry (T.components.piece i)) :
    letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := Manifold.interiorChartedSpace
      (T.contractAlong S K hK hext hk hconn).cutCarrier.model ∞
      (M := (T.contractAlong S K hK hext hk hconn).cutCarrier.pieceInterior
        ((T.contractAlong S K hK hext hk hconn).components.piece
          (T.contractAlongKeptIndex S K hK hext hk hconn hi)))
    letI := Manifold.interiorIsManifold
      (T.contractAlong S K hK hext hk hconn).cutCarrier.model ∞
      (M := (T.contractAlong S K hK hext hk hconn).cutCarrier.pieceInterior
        ((T.contractAlong S K hK hext hk hconn).components.piece
          (T.contractAlongKeptIndex S K hK hext hk hconn hi)))
    (T.relativeKeptGeometry S K hK hext hk hconn hi g).model = g.model := rfl

end GC.Seifert.TorusPresentation
