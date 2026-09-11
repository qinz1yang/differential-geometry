import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.MovingMetric
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open scoped Manifold ContDiff

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

def IsLAdaptedAt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (P : ∀ s, TangentSpace I (alpha s))
    (s : Real) : Prop :=
  covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha P s =
    (-2 * s) •
      ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (P s)

def IsLAdapted
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (P : ∀ s, TangentSpace I (alpha s))
    (J : Set Real) : Prop :=
  ∀ s ∈ J, IsLAdaptedAt S T alpha P s

end DifferentialGeometry.PDE.RicciFlow.Perelman
