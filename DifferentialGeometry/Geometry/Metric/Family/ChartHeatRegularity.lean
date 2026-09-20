import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Operator.TimeLaplacian

noncomputable section

open Bundle Manifold Set
open scoped BigOperators ContDiff Manifold

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Geometry.Operator (chartGramOnE)
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartDensityOnE_contDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => chartDensityOnE (I := I) (g p.1) α p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  let A : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun p => Matrix.of fun i j => chartGramOnE (I := I) (g p.1) α i j p.2
  have hA (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
      (fun p : ℝ × E => A p i j) (J ×ˢ interior (extChartAt I α).target) :=
    hg.chartGramOnE_contDiffOn hJ α i j
  have hdet : ContDiffOn ℝ ∞ (fun p => (A p).det)
      (J ×ˢ interior (extChartAt I α).target) := by
    simp_rw [Matrix.det_apply']
    refine ContDiffOn.sum fun σ _ => ?_
    exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hA (σ i) i)
  have hne (p : ℝ × E) (hp : p ∈ J ×ˢ interior (extChartAt I α).target) :
      (A p).det ≠ 0 := by
    have hbase := extChartAt_symm_mem_trivializationAt_baseSet (I := I) α
      (interior_subset hp.2)
    have heq : A p = chartGramMatrix (I := I) (g p.1) α ((extChartAt I α).symm p.2) := by
      ext i j
      rfl
    rw [heq]
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (g p.1) α hbase)
  have hsqrt := hdet.sqrt hne
  exact hsqrt.congr (fun p _ => rfl)

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartDensity_mul_scalar_contDiffOn_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ} (hJreg : J ⊆ D.regular)
    {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (J ×ˢ univ)) (α : M) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartDensityOnE (I := I) (g p.1) α p.2 *
        u p.1 ((extChartAt I α).symm p.2))
      (J ×ˢ interior (extChartAt I α).target) := by
  have hscalar := (scalarOnE_contDiffOn_prod α hu).mono
    (Set.prod_mono Subset.rfl interior_subset)
  exact (hg.chartDensityOnE_contDiffOn hJreg α).mul hscalar

theorem chartVossWeylIntegrand_contDiffOn_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ} (hJreg : J ⊆ D.regular)
    (hJ : UniqueDiffOn ℝ J) {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (J ×ˢ univ))
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  have hscalar := (scalarOnE_contDiffOn_prod α hu).mono
    (Set.prod_mono Subset.rfl interior_subset)
  have hdf := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => scalarOnE (I := I) α (u t) y)
    hJ isOpen_interior hscalar
  have hpd (j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
      (fun p : ℝ × E => partialDeriv j (scalarOnE (I := I) α (u p.1)) p.2)
      (J ×ˢ interior (extChartAt I α).target) :=
    (hdf.clm_apply (contDiffOn_const (c := chartModelBasis E j))).congr (fun _ _ => rfl)
  have hgrad : ContDiffOn ℝ ∞
      (fun p : ℝ × E => gradChartCoeffOnE (I := I) (g p.1) α (u p.1) i p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
    exact ContDiffOn.sum fun j _ => (hg.chartInvGramOnE_contDiffOn hJreg α i j).mul (hpd j)
  exact hgrad.mul (hg.chartDensityOnE_contDiffOn hJreg α)

end DifferentialGeometry.Geometry.Operator
