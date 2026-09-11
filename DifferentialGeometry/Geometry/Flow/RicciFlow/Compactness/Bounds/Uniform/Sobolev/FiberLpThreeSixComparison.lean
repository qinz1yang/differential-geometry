import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.LpProduct

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.GagliardoNirenberg

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem fiber_lp_three_le_uniform_constant_mul_lp_six
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        ∀ (r s : ℕ) (S : SmoothCcTensor g r s),
          lpNorm (fiberLpFun g r s S) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) ≤
            C * lpNorm (fiberLpFun g r s S) 6
              (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let VBase : ℝ :=
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let C : ℝ :=
    (volCompareC (E := E) Λ * VBase) ^ (1 / 6 : ℝ)
  have hbase : 0 ≤ VBase := by
    dsimp [VBase]
    exact ENNReal.toReal_nonneg
  have hvolC : 0 ≤ volCompareC (E := E) Λ := by
    exact Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg (mul_nonneg hvolC hbase) _
  refine ⟨C, hC, ?_⟩
  intro g hEq r s S
  have hroot :
      (((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ) ^
          (1 / 6 : ℝ)).toReal ≤ C := by
    rw [← ENNReal.toReal_rpow]
    dsimp only [C, VBase]
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      (volumeReal_cross (I := I) (M := M) gBase g hEq).1 (by norm_num)
  calc
    lpNorm (fiberLpFun g r s S) 3
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ) ^
          (1 / 6 : ℝ)).toReal *
        lpNorm (fiberLpFun g r s S) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
      fiberLp3_le_6 (I := I) (M := M) g r s S
    _ ≤ C * lpNorm (fiberLpFun g r s S) 6
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      mul_le_mul_of_nonneg_right hroot lpNorm_nonneg

end RicciFlow
end PDE
end DifferentialGeometry

end
