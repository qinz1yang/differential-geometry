import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Family.Defs
import DifferentialGeometry.Geometry.Connection.ChartBridge.Metric.InverseGram
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem hasDerivAt_chartDensity_of_isSolutionOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ D.regular) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) a).baseSet) :
    HasDerivAt (fun s => chartDensity (S.base.metric s) a x)
      (-S.scalar t x * chartDensity (S.base.metric t) a x) t := by
  classical
  let G := chartGramMatrix (S.base.metric t) a x
  let B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => S.ricciAt t x (vec2 (chartBasisVecFiber (I := I) a i x) (chartBasisVecFiber (I := I) a j x))
  have hentries (i j : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun s => chartGramMatrixFamily S.base.metric a x s i j) ((-2 : ℝ) * B i j) t :=
    metricDerivAt S hS ⟨t, ht⟩ x (chartBasisVecFiber (I := I) a i x) (chartBasisVecFiber (I := I) a j x)
  have hd := hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul S.base.metric a t hx
    (fun i j => (-2 : ℝ) * B i j) hentries
  have hscalar : S.scalar t x = ∑ i, ∑ j, G⁻¹ i j * B i j := by
    rw [S.scalar_eq_metricTrace]
    have h := metricTracePair0SAt_eq_sum_basis (S.base.metric t) (chartBasisFamily (I := I) a hx)
      (fun i j => chartInvGramMatrix (S.base.metric t) a x i j)
      (chartInvGram_inverse (S.base.metric t) a hx) (S.ricciAt t x)
    simpa only [chartBasisFamily_apply, chartInvGramMatrix, G, B, SolutionOn.family] using h
  have hsym (i j : Fin (Module.finrank ℝ E)) : G⁻¹ j i = G⁻¹ i j := by
    have h := (chartGramMatrix_isHermitian (S.base.metric t) a x).inv.apply i j
    simpa only [star_trivial] using h
  have htrace : Matrix.trace (G⁻¹ * Matrix.of (fun i j => (-2 : ℝ) * B i j)) = (-2 : ℝ) * S.scalar t x := by
    rw [hscalar, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    simp_rw [hsym]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change HasDerivAt (fun s => chartDensity (S.base.metric s) a x)
    ((1 / 2) * Matrix.trace (G⁻¹ * Matrix.of (fun i j => (-2 : ℝ) * B i j)) * chartDensity (S.base.metric t) a x) t at hd
  rw [htrace] at hd
  convert hd using 1
  ring

end DifferentialGeometry.PDE.RicciFlow
