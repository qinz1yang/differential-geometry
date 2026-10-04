import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts

/-!
# Positive Seifert data as actual primitive filling data

Changing the host port count along the balance equality preserves all actual collars and piece
maps. The resulting primitive filling presentation retains the original actual presentation.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

variable {W : CompactCarrier.{u}} {T : TorusPresentation W}
    {i : Fin T.components.count} {k l : ℕ}

def ProductFibredPiece.fillingCast (P : ProductFibredPiece T i k) (h : k = l) :
    ProductFibredPiece T i l := h ▸ P

theorem ProductFibredPiece.fillingCast_port (P : ProductFibredPiece T i k) (h : k = l)
    (j : Fin k) : (P.fillingCast h).port (Fin.cast h j) = P.port j := by
  subst l
  rfl

theorem ProductFibredPiece.fillingCast_pieceDiffeomorph {W' : CompactCarrier.{u}}
    {D : TorusPresentation W'} {i' : Fin D.components.count}
    (P : ProductFibredPiece T i k) (Q : ProductFibredPiece D i' k) (h : k = l) :
    (P.fillingCast h).pieceDiffeomorph (Q.fillingCast h) = P.pieceDiffeomorph Q := by
  subst l
  rfl

def SeifertBlock.toPrimitiveFilling {d : SeifertData} (B : SeifertBlock W d) :
    PrimitiveFillingPresentation W d.fillingCount d.ports where
  presentation := B.presentation
  piece := B.piece
  product := B.product.fillingCast d.ports_add_fillingCount.symm
  solid := B.solid
  port := B.port.trans (Fin.castOrderIso d.ports_add_fillingCount.symm).toEquiv
  seam := B.seam
  free := B.free
  free_port r := by
    change ((B.product.fillingCast d.ports_add_fillingCount.symm).port
      (Fin.cast d.ports_add_fillingCount.symm (B.port (.inl r)))).val = _
    rw [ProductFibredPiece.fillingCast_port]
    exact B.free_port r
  filled_port m := by
    change ((B.product.fillingCast d.ports_add_fillingCount.symm).port
      (Fin.cast d.ports_add_fillingCount.symm (B.port (.inr m)))).val = _
    rw [ProductFibredPiece.fillingCast_port]
    exact B.filled_port m
  solid_port := B.solid_port
  slope m := PrimitiveSlope.mk (d.fillingSlope m) (d.isPrimitive_fillingSlope m)
  slope_eq := B.slope

end GC.Seifert
