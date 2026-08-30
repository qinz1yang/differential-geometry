import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

def lCost
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x y : M) (tau : Real) : Real :=
  sInf {r : Real | ∃ alpha : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      lLength S T (sqrtReparam alpha) 0 tau = r}

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
