import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

def redDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (tau : Real) : Real :=
  Real.exp
    (-redLength S T x y tau -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))

end DifferentialGeometry.PDE.RicciFlow.Perelman
