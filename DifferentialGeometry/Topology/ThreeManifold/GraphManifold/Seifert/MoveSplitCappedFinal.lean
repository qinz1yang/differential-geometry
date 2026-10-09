import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedBelow
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof

/-!
# The split move

Lane N2c, tier 4. For presentations whose seams are linear the named input
`FibreFillingSphereSurgery` of `Seifert/MoveSplit.lean` holds at every split seam
(`fibreFillingSphereSurgery_of_hasLinearSeams`, tier 3 at the seam). Linearizing an arbitrary
presentation (`ElementaryPresentation.linearize`, which keeps the complexity and the split seams)
needs `TorusMappingClassLinear`: `fibreFillingSphereSurgery_of_torusMappingClassLinear` and
`moveSplit_of_torusMappingClassLinear`. With the proof `torusMappingClassLinear_holds` of
`Seifert/TorusMappingClassProof.lean` both are unconditional: `fibreFillingSphereSurgery` and
`moveSplit`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

universe u

open ElementaryPresentation

end GC.Seifert
