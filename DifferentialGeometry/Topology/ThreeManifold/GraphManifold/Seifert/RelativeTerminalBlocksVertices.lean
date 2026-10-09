import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeTwo
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusDecompositionPresentation

/-!
# Actual good-block vertices in relative terminal presentations

The full collar equality of a piece block identifies its native ports with the component's
actual boundary tori. Goodness gives their incompressibility. On a closed reconstructed
carrier with positive seam count, the actual port equivalence gives positive free-port count
and hence the existing freely indecomposable, noncyclic block group at every basepoint.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.PieceBlock

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {i : Fin T.components.count} (B : PieceBlock T i)

theorem relativeBoundary_torusMap_eq (r : Fin B.block.presentation.externalCount) :
    B.block.presentation.external.torusMap r =
      (T.pieceBoundaryTori i).torusMap (Fintype.equivFin _ (B.port r)) := by
  funext t
  change _ = T.pieceCollar i ((Fintype.equivFin _).symm (Fintype.equivFin _ (B.port r)))
    (t, halfZero)
  rw [Equiv.symm_apply_apply]
  exact B.collar_eq r _ (zero_mem_halfCollarSource t)

theorem relativePorts_incompressible (h : B.block.IsGoodBlock) :
    (T.pieceBoundaryTori i).incompressible := by
  intro j x
  let r := B.port.symm ((Fintype.equivFin (T.OwnedSide i)).symm j)
  have he : Fintype.equivFin (T.OwnedSide i) (B.port r) = j := by simp [r]
  have hm := B.relativeBoundary_torusMap_eq r
  rw [he] at hm
  have hb : B.block.presentation.external.boundaryMap r =
      (T.pieceBoundaryTori i).boundaryMap j := ContinuousMap.ext (congrFun hm)
  rw [← hb]
  exact h r x

variable {Q : ConnectedClosedOrientedManifold.{u} 3}
  {T : TorusPresentation (NoCuts.carrier Q)} {i : Fin T.components.count} (B : PieceBlock T i)

theorem relativeData_ports_pos (hn : 0 < T.pairing.count) : 0 < B.data.ports := by
  have he : B.data.ports = Fintype.card (T.OwnedSide i) := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (B.block.free.trans B.port)
  rw [he]
  exact T.card_ownedSide_pos hn i

theorem relativeVertex_indecomposableNoncyclic (h : B.block.IsGoodBlock)
    (hn : 0 < T.pairing.count) (x : T.components.piece i) :
    IndecomposableNoncyclic (FundamentalGroup (T.components.piece i) x) :=
  B.block.indecomposableNoncyclic h (Nat.ne_of_gt (B.relativeData_ports_pos hn)) x

end GC.Seifert.PieceBlock
