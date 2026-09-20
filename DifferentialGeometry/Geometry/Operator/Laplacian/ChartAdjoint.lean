import DifferentialGeometry.Analysis.Calculus.Derivative.DivergenceProduct
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem sum_partialDeriv_chartDensity_invGram_mul_partialDeriv
    (g : SmoothRiemannianMetric I M) (a : M) {y : E}
    (hy : y ∈ (extChartAt I a).target) {ψ : E → ℝ} (hψ : ContDiffAt ℝ 2 ψ y) :
    (∑ i : Fin (Module.finrank ℝ E), partialDeriv i
      (fun z => ∑ j : Fin (Module.finrank ℝ E),
        (chartDensityOnE g a z * chartInvGramOnE g a i j z) * partialDeriv j ψ z) y) =
      ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ((chartDensityOnE g a y * chartInvGramOnE g a ij.1 ij.2 y) *
          iteratedFDeriv ℝ 2 ψ y ![chartModelBasis E ij.1, chartModelBasis E ij.2] +
        iteratedFDeriv ℝ 1
          (fun z => chartDensityOnE g a z * chartInvGramOnE g a ij.1 ij.2 z) y
          (fun _ => chartModelBasis E ij.1) *
          iteratedFDeriv ℝ 1 ψ y (fun _ => chartModelBasis E ij.2)) := by
  have hc (i j : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ
      (fun z => chartDensityOnE g a z * chartInvGramOnE g a i j z) y :=
    (((chartDensityOnE_contDiffOn g a).mul (chartInvGramOnE_contDiffOn g a i j)).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hy)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp (j : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ (partialDeriv j ψ) y :=
    hd.clm_apply (differentiableAt_const (chartModelBasis E j))
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  unfold partialDeriv
  have hs := fderiv_fun_sum (u := Finset.univ)
    (fun j _ => (hc i j).mul (hp j))
  simp only [Pi.mul_apply, partialDeriv] at hs
  rw [hs]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact DifferentialGeometry.Analysis.Calculus.fderiv_mul_fderiv_apply
    (hc i j) hψ (chartModelBasis E j) (chartModelBasis E i)

end DifferentialGeometry.Geometry.Operator
