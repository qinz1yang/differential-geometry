import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitMain
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataProved

/-!
# The mixed split producer (unconditional)

Lane MS-b, tier MS6. Lane N2f's `existsMixedSideData_proved` discharges the side-data input of
`mixedSplit_of_sideData`, so the input `hMS : MixedSplit` of BE's mixed endpoint
`exists_prime_geometric_decomposition_mixed_of_inputs` and of lane W6's chapter-6 (b) endgame
`exists_prime_geometric_decomposition_of_pieceProfile_of_inputs` is a theorem (`mixedSplit`).
The application of both consumers to `mixedSplit` is checked in
`GraphManifold/Checks/MixedSplitConsumers`, outside this module, because their import closures
contain modules this one must not import.
-/

set_option autoImplicit false

universe u

namespace GC.Seifert.RelativeNormalization

theorem mixedSplit : MixedSplit.{u} :=
  mixedSplit_of_sideData existsMixedSideData_proved

example : MixedSplit.{u} := mixedSplit

end GC.Seifert.RelativeNormalization
