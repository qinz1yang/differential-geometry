import DifferentialGeometry.Analysis.Elliptic.MetricExtension

noncomputable section

open Manifold
open scoped ContDiff Matrix

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem densityOnEuclid_eq_sqrt_det
    (g : SmoothRiemannianMetric I M) (α : M) (y : EuclN) :
    densityOnEuclid g α y = Real.sqrt (Matrix.of (fun i j => gramOnEuclid g α i j y)).det := rfl

theorem invGramOnEuclid_eq_matrix_inv
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (y : EuclN) :
    invGramOnEuclid g α i j y = (Matrix.of (fun k l => gramOnEuclid g α k l y))⁻¹ i j := rfl

theorem weightedInvGramOnEuclid_eq_sqrt_det_mul_inv
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (y : EuclN) :
    weightedInvGramOnEuclid g α i j y =
      Real.sqrt (Matrix.of (fun k l => gramOnEuclid g α k l y)).det *
        (Matrix.of (fun k l => gramOnEuclid g α k l y))⁻¹ i j := rfl

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
