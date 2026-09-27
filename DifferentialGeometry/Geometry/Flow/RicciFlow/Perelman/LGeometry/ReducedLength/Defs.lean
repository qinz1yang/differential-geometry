import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open scoped ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def redLength
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (tau : Real) : Real :=
  lCost S T x y tau / (2 * Real.sqrt tau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
