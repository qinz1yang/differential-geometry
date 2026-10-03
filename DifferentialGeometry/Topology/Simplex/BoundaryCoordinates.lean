import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def stdSimplexBoundaryHomeomorphSimplexBoundary (n : ℕ) :
    stdSimplexBoundary n ≃ₜ DifferentialGeometry.Simplex.boundary (Fin (n + 1)) where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _x := rfl
  right_inv _x := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end DifferentialGeometry.Topology.PiecewiseLinear
