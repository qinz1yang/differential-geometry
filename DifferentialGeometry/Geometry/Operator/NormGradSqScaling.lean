import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.Operator.Scaling

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normGradSqFun_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (f : M → Real) (x : M) :
    normGradSqFun (I := I) (scaleMetric (I := I) c hc g) f x =
      c⁻¹ * normGradSqFun (I := I) g f x := by
  rw [normGradSqFun_def, normGradSqFun_def]
  rw [show gradFun (I := I) (scaleMetric (I := I) c hc g) f x =
      c⁻¹ • gradFun (I := I) g f x by
    exact gradientFun_scale (I := I) c hc g f x]
  rw [scaleMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hc]

end DifferentialGeometry.Geometry.Operator
