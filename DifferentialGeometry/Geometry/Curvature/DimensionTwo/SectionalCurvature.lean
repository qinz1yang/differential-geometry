import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem sectionalCurvature_eq_scalar_div_two_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (x : M) (v w : TangentSpace I x) (hvw : LinearIndependent Real ![v, w]) :
    sectionalCurvature (I := I) g x v w = metricScalarAt (I := I) g x / 2 := by
  have hden := sectionalCurvatureDenominator_pos_of_linearIndependent g x v w hvw
  rw [sectionalCurvatureDenominator_def] at hden
  rw [sectionalCurvature_eq_metricRm04StandardAt_div,
    Curvature.metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hdim]
  rw [g.symm x w v, ← pow_two]
  exact mul_div_cancel_right₀ _ hden.ne'

theorem sectionalCurvature_pos_of_metricScalarAt_pos_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (x : M) (hscalar : 0 < metricScalarAt (I := I) g x)
    (v w : TangentSpace I x) (hvw : LinearIndependent Real ![v, w]) :
    0 < sectionalCurvature (I := I) g x v w := by
  rw [sectionalCurvature_eq_scalar_div_two_of_finrank_eq_two g hdim x v w hvw]
  exact div_pos hscalar (by norm_num)

end DifferentialGeometry.Geometry.Riemannian
