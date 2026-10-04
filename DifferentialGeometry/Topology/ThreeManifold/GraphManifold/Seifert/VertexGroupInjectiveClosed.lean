import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PieceInteriorSurjective

/-!
# Fundamental group injectivity of closed pieces

The interior inclusion is surjective on fundamental groups by the finite boundary collar push.
Its factorization with the carrier map proves injectivity at interior basepoints, and the inward
homotopy track transfers this to every basepoint of the closed piece.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold GC.Endpoint
open scoped Topology ContinuousMap

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W)

theorem pieceInteriorToCarrier_eq_pieceToCarrier_comp (i : Fin G.components.count) :
    G.pieceInteriorToCarrier i = (G.pieceToCarrier i).comp (G.pieceInteriorToPiece i) :=
  ContinuousMap.ext fun x => congrArg G.cutMap (rfl : x.1 = x.1)

theorem injective_pieceInteriorToPiece_of_ports (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (i : Fin G.components.count)
    (x : G.cutCarrier.pieceInterior (G.components.piece i)) :
    Function.Injective (FundamentalGroup.map (G.pieceInteriorToPiece i) x) := by
  apply GC.Topology.injective_inner_of_composite (G.pieceInteriorToPiece i)
    (G.pieceToCarrier i) x
  rw [← G.pieceInteriorToCarrier_eq_pieceToCarrier_comp i]
  exact G.injective_pieceInterior_of_ports hext hports i x

theorem injective_piece_of_ports (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (i : Fin G.components.count)
    (x : G.components.piece i) :
    Function.Injective (FundamentalGroup.map (G.pieceToCarrier i) x) := by
  let y := G.pieceInwardEndpoint i x
  have hy : Function.Injective
      (FundamentalGroup.map (G.pieceToCarrier i) (G.pieceInteriorToPiece i y)) := by
    apply GC.Seifert.injective_fundamentalGroup_map_of_comp (G.pieceInteriorToPiece i)
      (G.pieceToCarrier i) y (G.surjective_pieceInteriorToPiece i y)
    rw [← G.pieceInteriorToCarrier_eq_pieceToCarrier_comp i]
    exact G.injective_pieceInterior_of_ports hext hports i y
  exact (GC.Topology.injective_fundamentalGroup_map_iff_of_path (G.pieceToCarrier i)
    ((G.pieceInwardHomotopy i).evalAt x)).mpr hy

end GC.Seifert.TorusPresentation
