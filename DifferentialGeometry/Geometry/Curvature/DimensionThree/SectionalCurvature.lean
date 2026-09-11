import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem leastCurvatureOperatorEigenvalueAt_le_sectionalCurvature
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v w : TangentSpace I x) (hvw : LinearIndependent Real ![v, w]) :
    leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) ≤
      Riemannian.sectionalCurvature g x v w := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  have hray := leastCurvatureOperatorEigenvalueAt_mul_identity_le g x basis horth
    (metricAlgebraicCurvatureTensorAt g x) (fun _ : Fin 1 => (1 : Real))
      (fun _ => v) (fun _ => w)
  have hden := Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g x v w hvw
  rw [Riemannian.sectionalCurvatureDenominator_def] at hden
  rw [Riemannian.sectionalCurvature_eq_metricRm04StdAt_div]
  apply (le_div_iff₀ hden).mpr
  simpa only [algebraicCurvatureIdentityQuadraticEval, algebraicCurvatureOperatorQuadraticEval,
    Fin.sum_univ_one, one_mul, g.symm x w v, pow_two,
    metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt_apply, tensor04StandardAt_apply] using hray

theorem leastCurvatureOperatorEigenvalueAt_eq_zero_of_sectionalCurvature_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hcone : metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (v w : TangentSpace I x) (hvw : LinearIndependent Real ![v, w])
    (hzero : Riemannian.sectionalCurvature g x v w = 0) :
    leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) = 0 := by
  apply le_antisymm
  · exact (leastCurvatureOperatorEigenvalueAt_le_sectionalCurvature g x hdim v w hvw).trans_eq hzero
  · exact (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
      g hdim).mpr hcone

end DifferentialGeometry.Geometry.Curvature.DimensionThree
