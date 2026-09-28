import DifferentialGeometry.Geometry.Operator.Gradient.QuadraticForm
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Tensor.Coordinates
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner_gradientFun_eq_chartGradientBilin
    (g : SmoothRiemannianMetric I M) (alpha : M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x)
    (hx : x ∈ (chartAt H alpha).source) :
    g.inner x (gradientFun g f x) (gradientFun g h x) =
      chartGradientBilin g alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha h) (extChartAt I alpha x)) := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hxint : extChartAt I alpha x ∈ interior (extChartAt I alpha).target := by
    have hxsrc : x ∈ (extChartAt I alpha).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hx
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) alpha
      ((extChartAt I alpha).map_source hxsrc)
  have hgrad := gradChartLocal_eq_gradFun g alpha hf hbase hxint
  change g.inner x (gradFun g f x) (gradFun g h x) = _
  rw [g.symm x, inner_gradFun g h x, ← hgrad, chartGradientBilin_apply]
  unfold gradChartLocal
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, mfderiv_chartBasisVecFiber_of_mdifferentiableAt alpha hh hx hxint i]
  change gradChartCoeff g alpha f i x *
      partialDeriv (E := E) i (scalarOnE (I := I) alpha h) (extChartAt I alpha x) = _
  unfold gradChartCoeff
  rw [Finset.sum_mul]
  rfl

theorem abs_chartGradientBilin_fderiv_le
    (g : SmoothRiemannianMetric I M) (alpha : M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x)
    (hx : x ∈ (chartAt H alpha).source) :
    |chartGradientBilin g alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha h) (extChartAt I alpha x))| ≤
      Real.sqrt (g.inner x (gradientFun g f x) (gradientFun g f x)) *
        Real.sqrt (g.inner x (gradientFun g h x) (gradientFun g h x)) := by
  rw [← inner_gradientFun_eq_chartGradientBilin g alpha hf hh hx]
  exact DifferentialGeometry.SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic
    g x _ _

end DifferentialGeometry.Geometry.Operator
