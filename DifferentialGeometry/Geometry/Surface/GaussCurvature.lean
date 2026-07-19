import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.EinsteinMetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]


def gaussCurvature (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  (2 : Real)⁻¹ * scalarCurv (I := I) g x


theorem gaussCurvature_def (g : SmoothRiemannianMetric I M) (x : M) :
    gaussCurvature (I := I) g x = (2 : Real)⁻¹ * scalarCurv (I := I) g x := rfl


theorem ricci_eq_gaussCurvature_smul_metric_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
      gaussCurvature (I := I) g x * g.inner x v w := by
  sorry


end DifferentialGeometry.Integral.Connection
