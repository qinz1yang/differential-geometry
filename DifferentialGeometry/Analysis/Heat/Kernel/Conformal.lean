import DifferentialGeometry.Analysis.Heat.Kernel.Basic
import DifferentialGeometry.Analysis.Heat.Smoothing.ScalarHeatFlow
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Rellich

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open Bundle MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_divergence_mul_heatKernel_diagonal_eq_zero_of_conformal
    (hn : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : Geometry.IsConformalVectorField g X) {t : Real} (ht : 0 < t) :
    (∫ x, divergenceG g X x * heatKernel g t x x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have hdiv := DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
    (divergence_g_contMDiff g X).continuous
    (HasCompactSupport.of_compactSpace (divergenceG g X))
  rw [integral_mul_heatKernel_diagonal g ht hdiv]
  calc
    _ = ∑' _i : TensorEigenIdx00 g, (0 : Real) := by
      apply tsum_congr
      intro i
      have h := integral_divergence_mul_sq_eq_zero_of_conformal_of_eigenfunction hn g
        ⟨(scalarEigenFunction g i).toFun, (scalarEigenFunction g i).smooth⟩ X hX
        (fun x => congrArg (fun u => u.toFun x) (scalarEigenFunction_laplacian_eq g i))
      change (∫ x, divergenceG g X x * (scalarEigenFunction g i).toFun x ^ 2
        ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 at h
      rw [h, mul_zero]
    _ = 0 := tsum_zero

end DifferentialGeometry.Analysis.HeatEquation
