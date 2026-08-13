import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ↔
      ∀ (n : Nat) (c : Fin n → Real)
        (v w : Fin n → TangentSpace I x),
        0 ≤ ∑ i, ∑ j, c i * c j *
          metricRm04StdAt (I := I) (M := M) g x
            (v i) (w i) (w j) (v j) := by
  simp [algebraicCurvatureOperatorQuadraticEval,
    metricRm04StdAt_apply]

end DifferentialGeometry.Geometry.Curvature
