import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian

/-!
# The round metric's chart Gram matrix at a pole (Step 5B, P1)

Working notes file: the 0-jet milestone `chartGramOnE roundMetric x₀ i j 0 = δ i j`.
-/

noncomputable section

open Manifold Metric Module Set
open scoped Manifold RealInnerProductSpace
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

instance instNeZeroFinrankModel : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]; infer_instance

omit [NeZero n] in
/-- The inverse stereographic chart sends the chart origin back to the chart centre. -/
theorem extChartAt_symm_zero_sphere (x₀ : sphere (0 : E) 1) :
    (extChartAt (𝓡 n) x₀).symm 0 = x₀ := by
  have hchart : (extChartAt (𝓡 n) x₀).symm 0 = (stereographic' n (-x₀)).symm 0 := rfl
  rw [hchart]
  apply Subtype.ext
  have hz : ((OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere (-x₀))).repr.symm (0 : EuclideanSpace ℝ (Fin n)) : E) = 0 := by
    rw [map_zero]; rfl
  simp only [stereographic'_symm_apply]
  rw [hz]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
    smul_zero, zero_sub, coe_neg_sphere]
  module

/-- **Chart Gram of the round metric, reduced to the ambient inner product.**  The chart
Gram matrix of the round metric is the ambient inner product of the chart coordinate-frame
vectors pushed forward by the inclusion differential `dIncl`.  This is the project-side
reduction; the remaining content (that these pushed frames are an orthonormal/conformal frame)
is the explicit stereographic computation. -/
theorem chartGramOnE_roundMetric (x₀ : sphere (0 : E) 1)
    (i j : Fin (finrank ℝ (EuclideanSpace ℝ (Fin n)))) (y : EuclideanSpace ℝ (Fin n)) :
    chartGramOnE (roundMetric (E := E) (n := n)) x₀ i j y =
      ⟪dIncl ((extChartAt (𝓡 n) x₀).symm y)
          (chartBasisVecFiber x₀ i ((extChartAt (𝓡 n) x₀).symm y)),
        dIncl ((extChartAt (𝓡 n) x₀).symm y)
          (chartBasisVecFiber x₀ j ((extChartAt (𝓡 n) x₀).symm y))⟫ := by
  rw [chartGramOnE_def, chartGramMatrix_apply, roundMetric_inner]

end Geometry
end DifferentialGeometry
