import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Endomorphism
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ E = 3)
    (hzero : curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04At (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0) :
    metricRm04At (I := I) g x = 0 := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x (by
    have hfin : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [hfin, hdim])
  have hAzero :
      (⟨metricRm04At (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) = 0 := by
    apply curvatureOperatorMatrixAt_eq_zero_of_orthonormal (I := I) g x basis horth
    ext i j
    have hpair : curvatureOperatorPairingAt (I := I) g x
        ⟨metricRm04At (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩
        (curvatureTwoFormBasisAt (I := I) basis i)
        (curvatureTwoFormBasisAt (I := I) basis j) = 0 := by
      rw [← twoFormMetricData_inner_curvatureOperatorEndomorphismAt, hzero]
      simp
    rw [curvatureOperatorPairingAt_curvatureTwoFormBasisAt
      (I := I) g x basis horth] at hpair
    change 2 * curvatureOperatorMatrixAt (I := I) x basis
      ⟨metricRm04At (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ i j = 0 at hpair
    have hij : curvatureOperatorMatrixAt (I := I) x basis
        ⟨metricRm04At (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ i j = 0 := by
      linarith
    simpa using hij
  exact congrArg Subtype.val hAzero

end DifferentialGeometry.Geometry.Curvature.DimensionThree

end
