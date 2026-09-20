import DifferentialGeometry.Analysis.Parabolic.ScalarHeat.SmoothMetricWeakEquation
import DifferentialGeometry.Analysis.Parabolic.ScalarHeat.SmoothPotential

noncomputable section

open Manifold MeasureTheory Set
open scoped BigOperators ContDiff Manifold

namespace DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

theorem of_chart_weighted_weak_equation
    {μ : Measure (ℝ × E)} [Measure.IsAddHaarMeasure μ]
    {D Dg : RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (hg : MetricFamilySmoothOn Dg G.metric) {J : Set ℝ} (hJ : IsOpen J)
    (hJreg : J ⊆ Dg.regular) (hcarrier : D.carrier ⊆ J)
    (hconnection : ∀ t ∈ D.regular, G.connection t = LeviCivita (I := I) (G.metric t))
    {R u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (J ×ˢ univ))
    (hρ : ∀ t ∈ D.regular, ∀ x : M,
      HasDerivAt
        (fun s => chartDensityOnE (I := I) (G.metric s) x (extChartAt I x x))
        (R t x * chartDensityOnE (I := I) (G.metric t) x (extChartAt I x x)) t)
    (hweak : ∀ α : M, ∀ φ : ℝ × E → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ interior (extChartAt I α).target →
      (∫ p in J ×ˢ interior (extChartAt I α).target,
        (chartDensityOnE (I := I) (G.metric p.1) α p.2 *
          u p.1 ((extChartAt I α).symm p.2)) * fderiv ℝ φ p (1, 0) ∂μ) =
      ∑ i : Fin (Module.finrank ℝ E), ∫ p in J ×ˢ interior (extChartAt I α).target,
        chartVossWeylIntegrand (I := I) (G.metric p.1) α (u p.1) i p.2 *
          fderiv ℝ φ p (0, chartModelBasis E i) ∂μ) :
    IsHeatPotOn D G (fun t x => -R t x) u := by
  apply of_contMDiffOn hu hcarrier
  intro t ht x
  have heq := hasDerivAt_of_metricFamilySmoothOn_chart_weak_equation (μ := μ)
    hg hJ hJreg hu x (hcarrier (D.regular_subset ht)) (mem_chart_source H x)
    Subset.rfl (hρ t ht x) (hweak x)
  simpa only [laplacianAt, hconnection t ht, sub_eq_add_neg, neg_mul] using heq

end DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
