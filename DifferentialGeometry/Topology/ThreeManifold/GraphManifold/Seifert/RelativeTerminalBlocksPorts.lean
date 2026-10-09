import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminal
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeRegions

/-!
# Actual boundary incompressibility under compact piece transport

A piece transfer identifies the finite actual ports and their continuous torus maps through
its full compact diffeomorphism. The induced fundamental-group isomorphism transports
boundary incompressibility at every torus basepoint, in both directions.
-/

set_option autoImplicit false

noncomputable section

open Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.PieceTransfer

variable {W W' : CompactCarrier.{u}} {T : TorusPresentation W} {U : TorusPresentation W'}
  {i : Fin T.components.count} {j : Fin U.components.count} (τ : PieceTransfer T i U j)

def carrierHomeomorph : (componentCarrier T.cutCarrier T.components i).Carrier ≃ₜ
    (componentCarrier U.cutCarrier U.components j).Carrier := τ.map.toHomeomorph

theorem carrierHomeomorph_apply (x : (componentCarrier T.cutCarrier T.components i).Carrier) :
    τ.carrierHomeomorph x = τ.map x := rfl


def portIndexEquiv : Fin (Fintype.card (T.OwnedSide i)) ≃
    Fin (Fintype.card (U.OwnedSide j)) :=
  ((Fintype.equivFin (T.OwnedSide i)).symm.trans τ.side).trans
    (Fintype.equivFin (U.OwnedSide j))

theorem boundaryMap_portIndexEquiv (a : Fin (Fintype.card (T.OwnedSide i))) :
    (U.pieceBoundaryTori j).boundaryMap (τ.portIndexEquiv a) =
      (τ.carrierHomeomorph : C((componentCarrier T.cutCarrier T.components i).Carrier,
        (componentCarrier U.cutCarrier U.components j).Carrier)).comp
        ((T.pieceBoundaryTori i).boundaryMap a) := by
  apply ContinuousMap.ext
  intro t
  change U.pieceCollar j ((Fintype.equivFin (U.OwnedSide j)).symm
    (Fintype.equivFin (U.OwnedSide j) (τ.side
      ((Fintype.equivFin (T.OwnedSide i)).symm a)))) (t, halfZero) = _
  rw [Equiv.symm_apply_apply]
  exact τ.collar_eq _ (t, halfZero) (zero_mem_halfCollarSource t)

include τ in
theorem incompressible (h : (T.pieceBoundaryTori i).incompressible) :
    (U.pieceBoundaryTori j).incompressible := by
  intro a t
  obtain ⟨b, rfl⟩ := τ.portIndexEquiv.surjective a
  rw [τ.boundaryMap_portIndexEquiv, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (bijective_map_homeomorph τ.carrierHomeomorph
    ((T.pieceBoundaryTori i).boundaryMap b t)).1.comp (h b t)

include τ in
theorem incompressible_iff :
    (U.pieceBoundaryTori j).incompressible ↔ (T.pieceBoundaryTori i).incompressible := by
  refine ⟨?_, τ.incompressible⟩
  intro h a t
  have ht := h (τ.portIndexEquiv a) t
  rw [τ.boundaryMap_portIndexEquiv, GC.Topology.fundamentalGroup_map_comp,
    MonoidHom.coe_comp] at ht
  exact ht.of_comp

end GC.Seifert.PieceTransfer
