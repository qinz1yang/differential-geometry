import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import Mathlib.LinearAlgebra.Matrix.BilinearForm

set_option autoImplicit false
noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff Matrix
open DifferentialGeometry DifferentialGeometry.Tensor.Coordinates

namespace DifferentialGeometry.Integral.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartGramMatrix_det_linear_change
    (q h : SmoothRiemannianMetric I M) (α x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (L : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hL : ∀ v w, h.inner x v w = q.inner x (L v) (L w)) :
    (chartGramMatrix h α x).det =
      LinearMap.det L ^ 2 * (chartGramMatrix q α x).det := by
  classical
  let b := chartBasisFamily (I := I) α hx
  let B : LinearMap.BilinForm ℝ (TangentSpace I x) := (q.inner x).toBilinForm
  have hb (i : Fin (Module.finrank ℝ E)) :
      b i = chartBasisVecFiber (I := I) α i x :=
    chartBasisFamily_apply (I := I) α hx i
  have hq : chartGramMatrix q α x = LinearMap.BilinForm.toMatrix b B := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, hb, hb]
    rfl
  have hh : chartGramMatrix h α x = LinearMap.BilinForm.toMatrix b (B.comp L L) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.comp_apply, hb, hb]
    exact hL _ _
  rw [hh, B.toMatrix_comp b b, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, LinearMap.det_toMatrix, hq]
  ring

theorem chartDensity_eq_abs_det_mul_of_inner_eq
    (q h : SmoothRiemannianMetric I M) (α x : M)
    (hx : x ∈ (chartAt H α).source)
    (L : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hL : ∀ v w, h.inner x v w = q.inner x (L v) (L w)) :
    chartDensity h α x = |LinearMap.det L| * chartDensity q α x := by
  unfold chartDensity
  rw [chartGramMatrix_det_linear_change q h α x hx L hL,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem riemannianVolumeDensity_eq_abs_det_of_inner_eq
    [T2Space M] [SigmaCompactSpace M]
    (q h : SmoothRiemannianMetric I M) (x : M)
    (L : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hL : ∀ v w, h.inner x v w = q.inner x (L v) (L w)) :
    riemannianVolumeDensity q h x = |LinearMap.det L| := by
  rw [riemannianVolumeDensity_apply_of_mem_chart_source q h x (mem_chart_source H x),
    chartDensity_eq_abs_det_mul_of_inner_eq q h x x (mem_chart_source H x) L hL]
  exact mul_div_cancel_right₀ _ (ne_of_gt (chartDensity_pos q x (mem_chart_source H x)))

end DifferentialGeometry.Integral.Measure
