import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian

/-!
# Chart inverse Gram matrix as an intrinsic inverse metric

This file connects the inverse Gram matrix of a chart-induced tangent basis to
the basis-level inverse-metric predicate used by intrinsic tensor formulas.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The chart inverse Gram matrix is the inverse metric in the chart-induced
tangent basis at every point of the chart trivialization. -/
theorem chartInvGram_inverse
    (g : SmoothRiemannianMetric I M) (alpha : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) alpha).baseSet) :
    MetricInverseInBasis_gen (I := I) g x
      (chartBasisFamily (I := I) alpha hx)
      (fun i j => chartInvGramMatrix (I := I) g alpha x i j) := by
  classical
  have hgram : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (chartBasisFamily (I := I) alpha hx i)
          (chartBasisFamily (I := I) alpha hx j) =
        chartGramMatrix (I := I) g alpha x i j := by
    intro i j
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    exact (chartGramMatrix_apply (I := I) g alpha x i j).symm
  intro i j
  refine ⟨?_, ?_⟩
  · simp only [hgram]
    rw [← Matrix.mul_apply,
      chartInvGramMatrix_mul_chartGramMatrix (I := I) g alpha hx,
      Matrix.one_apply]
  · simp only [hgram]
    rw [← Matrix.mul_apply,
      chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hx,
      Matrix.one_apply]

end DifferentialGeometry.Integral.Connection
