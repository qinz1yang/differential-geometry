import DifferentialGeometry.Analysis.Convex.Tensor04SectionalNonnegativeCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicSectionalCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Geometry.Curvature.Metric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem tensor04SectionalEval_metricRm04At
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        (metricRm04At (I := I) (M := M) g x) v w =
      metricRm04StdAt (I := I) (M := M) g x v w w v := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) (M := M) g x ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ metricRm04StdAt (I := I) (M := M) g x v w w v := by
  simp

omit [SigmaCompactSpace M] in
theorem metricRm04_mem_tensor04SectionalNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) :
    (∀ x : M, metricRm04 (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) ↔
      ∀ x : M, ∀ v w : TangentSpace I x,
        0 ≤ metricRm04StdAt (I := I) (M := M) g x v w w v := by
  simp

omit [SigmaCompactSpace M] in
theorem metricAlgebraicCurvatureTensorAt_mem_algebraicSectionalNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ metricRm04StdAt (I := I) (M := M) g x v w w v := by
  simp

end DifferentialGeometry.Geometry.Curvature
