import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.VertexGroupInjectiveClosed

/-!
# Seam and piece injectivity for unions of good blocks

Chapter 5 plan P4, tier T1. For a union of good blocks `B : BlockedPresentation (NoCuts.carrier Q)`
of a closed `Q` the ports of the pieces of `B.base` are the free ports of the blocks, hence
π₁-injective (`pieceBoundaryTori_incompressible_of_isGood`, X12). So every seam torus of `B.base`
is π₁-injective into `Q` at every basepoint (`injective_seamTorus_of_isGood`, through K09c) and so
is every piece, closed or open (`injective_piece_of_isGood`, `injective_pieceInterior_of_isGood`,
through K19 and X7). With at least one seam every block has a free port
(`ports_ne_zero_of_pairing_pos`, the contrapositive of `unique_block_of_ports_eq_zero`), and the
free ports of a good block are π₁-injective into the block (`injective_freePort_of_isGood`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

universe u

namespace GC.Seifert

namespace BlockedPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem injective_seamTorus_of_isGood (B : BlockedPresentation (NoCuts.carrier Q))
    (hB : B.IsGood) (k : Fin B.base.pairing.count) (t : Torus) :
    Function.Injective (FundamentalGroup.map (B.base.seamTorus k) t) :=
  B.base.injective_seamTorus_of_ports B.base.externalCount_eq_zero
    (B.pieceBoundaryTori_incompressible_of_isGood hB) k t

theorem injective_piece_of_isGood (B : BlockedPresentation (NoCuts.carrier Q))
    (hB : B.IsGood) (i : Fin B.base.components.count) (x : B.base.components.piece i) :
    Function.Injective (FundamentalGroup.map (B.base.pieceToCarrier i) x) :=
  B.base.injective_piece_of_ports B.base.externalCount_eq_zero
    (B.pieceBoundaryTori_incompressible_of_isGood hB) i x

theorem injective_pieceInterior_of_isGood (B : BlockedPresentation (NoCuts.carrier Q))
    (hB : B.IsGood) (i : Fin B.base.components.count)
    (x : B.base.cutCarrier.pieceInterior (B.base.components.piece i)) :
    Function.Injective (FundamentalGroup.map (B.base.pieceInteriorToCarrier i) x) :=
  B.base.injective_pieceInterior_of_ports B.base.externalCount_eq_zero
    (B.pieceBoundaryTori_incompressible_of_isGood hB) i x

theorem ports_ne_zero_of_pairing_pos (B : BlockedPresentation (NoCuts.carrier Q))
    (hn : 0 < B.base.pairing.count) (i : Fin B.base.components.count) : (B.data i).ports ≠ 0 :=
  fun h => by
    have := (B.unique_block_of_ports_eq_zero i h).2
    omega

theorem injective_freePort_of_isGood {W : CompactCarrier.{u}} (B : BlockedPresentation W)
    (hB : B.IsGood) (i : Fin B.base.components.count) (r : Fin (B.data i).ports)
    (x : Torus) :
    Function.Injective (FundamentalGroup.map
      ((B.block i).presentation.external.boundaryMap ((B.block i).free r)) x) :=
  ((B.block i).isGoodBlock_iff.mp (hB i)) r x

end BlockedPresentation

end GC.Seifert
