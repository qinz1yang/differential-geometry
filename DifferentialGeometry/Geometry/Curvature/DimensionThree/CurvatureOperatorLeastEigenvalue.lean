import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M]

def algebraicCurvatureIdentityQuadraticEval
    (g : SmoothRiemannianMetric I M) {x : M} {n : Nat}
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) : Real :=
  ∑ i, ∑ j, c i * c j *
    ((g.inner x (v i) (v j)) * (g.inner x (w i) (w j)) -
      (g.inner x (v i) (w j)) * (g.inner x (w i) (v j)))

def CurvatureOperatorLowerBoundAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) (K : Real) : Prop :=
  ∀ (n : Nat) (c : Fin n → Real) (v w : Fin n → TangentSpace I x),
    0 ≤ algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w +
      K * algebraicCurvatureIdentityQuadraticEval (I := I) g c v w

noncomputable def leastCurvatureOperatorEigenvalueAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) : Real :=
  -sInf {K : Real | CurvatureOperatorLowerBoundAt (I := I) g x A K}

end DifferentialGeometry.Geometry.Curvature.DimensionThree
