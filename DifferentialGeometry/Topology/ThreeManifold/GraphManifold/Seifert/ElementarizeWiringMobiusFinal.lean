import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusProducer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SyncedMobiusPiece

/-!
# `ElementarizeOnSubCollar`, unconditionally

Lane P1X2 (P1 wiring). The last hypothesis `hMD5` of `elementarizeOnSubCollar_of_mobiusPiece`
(the synchronised Möbius piece) is lane MD5b's `exists_syncedMobiusPiece`, so the P1 statement
`ElementarizeOnSubCollar` holds (`elementarizeOnSubCollar`).
-/

set_option autoImplicit false

universe u

namespace GC.Seifert.Wiring

theorem elementarizeOnSubCollar : ElementarizeOnSubCollar.{u} :=
  elementarizeOnSubCollar_of_mobiusPiece exists_syncedMobiusPiece

end GC.Seifert.Wiring
