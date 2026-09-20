import DifferentialGeometry.Geometry.Operator.Laplacian.ChartAdjoint


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem sum_chartDensity_invGram_mul_iteratedFDeriv_two
    (g : SmoothRiemannianMetric I M) (a : M) {y : E}
    (hy : y ∈ (extChartAt I a).target) {f : M → ℝ}
    (hf : ContDiffAt ℝ 2 (scalarOnE (I := I) a f) y) :
    (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      (chartDensityOnE g a y * chartInvGramOnE g a ij.1 ij.2 y) *
        iteratedFDeriv ℝ 2 (scalarOnE (I := I) a f) y
          ![chartModelBasis E ij.1, chartModelBasis E ij.2]) =
      chartDensityOnE g a y * chartVossWeylLaplacian g a f ((extChartAt I a).symm y) -
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          iteratedFDeriv ℝ 1
            (fun z => chartDensityOnE g a z * chartInvGramOnE g a ij.1 ij.2 z) y
            (fun _ => chartModelBasis E ij.1) *
              iteratedFDeriv ℝ 1 (scalarOnE (I := I) a f) y
                (fun _ => chartModelBasis E ij.2) := by
  have heq (i : Fin (Module.finrank ℝ E)) :
      chartVossWeylIntegrand g a f i =
        fun z => ∑ j : Fin (Module.finrank ℝ E),
          (chartDensityOnE g a z * chartInvGramOnE g a i j z) *
            partialDeriv j (scalarOnE (I := I) a f) z := by
    funext z
    simp only [chartVossWeylIntegrand, gradChartCoeffOnE, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpos : 0 < chartDensityOnE g a y :=
    chartDensity_pos g a (extChartAt_symm_mem_trivializationAt_baseSet a hy)
  have hsum := sum_partialDeriv_chartDensity_invGram_mul_partialDeriv g a hy hf
  rw [Finset.sum_add_distrib] at hsum
  unfold chartVossWeylLaplacian
  rw [(extChartAt I a).right_inv hy]
  change _ = chartDensityOnE g a y *
    ((∑ i, partialDeriv i (chartVossWeylIntegrand g a f i) y) /
      chartDensityOnE g a y) - _
  simp_rw [heq]
  rw [mul_div_cancel₀ _ (ne_of_gt hpos), hsum]
  ring

end DifferentialGeometry.Geometry.Operator
