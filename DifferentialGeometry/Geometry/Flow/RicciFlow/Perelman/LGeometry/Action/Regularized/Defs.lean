import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Reparametrization

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

noncomputable def lRegularizedSpeedSq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : Real :=
  (S.base.metric (T - s ^ 2)).inner (alpha s)
    (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)

noncomputable def lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : Real :=
  let g := S.base.metric (T - s ^ 2)
  let A := lVelocity (I := I) alpha s
  (1 / 2 : Real) * g.inner (alpha s) A A +
    2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)

noncomputable def lRegularizedAction
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b : Real) : Real :=
  ∫ s in a..b, lRegularizedLagrangian S T alpha s

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
