import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Operator.MetricFamilyGram

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory
open scoped ContDiff Manifold

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

noncomputable def lChartLagrangian
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) : Real :=
  inner Real
    (((1 / 2 : Real) • chartGramOp (I := I) S.family p
      (T - (a + r) ^ 2, u.toFun r)) (u.deriv r))
    (u.deriv r) +
  2 * (a + r) ^ 2 * S.scalar (T - (a + r) ^ 2)
    ((extChartAt I p).symm (u.toFun r))

noncomputable def lChartAction
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) : Real :=
  ∫ r in (0 : Real)..L, lChartLagrangian S T a p u r

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
