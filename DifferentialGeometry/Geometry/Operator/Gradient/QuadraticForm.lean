import DifferentialGeometry.Analysis.Normed.Matrix.CovectorBilinear
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry.Operator

open Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinearNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def chartGradientBilin (g : SmoothRiemannianMetric I M) (alpha x : M) :
    (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  Matrix.covectorBilin (chartModelBasis E) (chartInvGramMatrix g alpha x)

theorem chartGradientBilin_apply (g : SmoothRiemannianMetric I M)
    (alpha x : M) (u v : E →L[ℝ] ℝ) :
    chartGradientBilin g alpha x u v =
      ∑ i, ∑ j, chartInvGramMatrix g alpha x i j *
        u (chartModelBasis E j) * v (chartModelBasis E i) :=
  Matrix.covectorBilin_apply _ _ _ _

theorem grad_norm_sq_eq_chartGradientBilin [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (alpha : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H alpha).source) :
    g.inner x (gradFun g f x) (gradFun g f x) =
      chartGradientBilin g alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x)) := by
  rw [chartGradientBilin_apply, grad_norm_sq_chart g alpha hf hx]
  rfl

end DifferentialGeometry.Geometry.Operator
