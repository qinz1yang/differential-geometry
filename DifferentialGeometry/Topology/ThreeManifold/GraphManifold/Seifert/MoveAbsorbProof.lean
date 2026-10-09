import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MergedSolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
# The absorb move

The (S⁺) move M3 holds unconditionally: `moveAbsorb : MoveAbsorb` applies N3b's
`moveAbsorb_of_contractionRecollar` (which already uses `mergedSolidTorus`) to CS2's
`contractionRecollar`.
-/

set_option autoImplicit false

universe u

namespace GC.Seifert

theorem moveAbsorb : MoveAbsorb.{u} :=
  moveAbsorb_of_contractionRecollar contractionRecollar

end GC.Seifert
