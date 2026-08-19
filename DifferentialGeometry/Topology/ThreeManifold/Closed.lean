import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

namespace DifferentialGeometry.Topology.ThreeManifold

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def isClosedThreeManifold : Prop :=
  CompactSpace M ∧ ConnectedSpace M ∧ I.Boundaryless ∧
    Module.finrank ℝ E = 3

end DifferentialGeometry.Topology.ThreeManifold
