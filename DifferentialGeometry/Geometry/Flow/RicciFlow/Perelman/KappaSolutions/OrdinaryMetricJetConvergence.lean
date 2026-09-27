import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.TimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricJetFormula

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ordinaryConvergenceC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem closedWindow_metric_time_jet_components_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular) (ht : t ∈ Icc c b)
    (q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y =>
      (iteratedDerivWithin q
        (fun s => metricTensorField (S.base.metric s) ((extChartAt I x₀).symm y)) (Icc c b) t)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  exact ordinary_metric_time_jet_components_contDiffOn_of_closed_interval
    S hS hac hcb hcarrier hregular ht q x₀ hWt slots


theorem closedWindow_metric_time_jet_components_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {a c b a₀ c₀ b₀ : ℝ} (hac : a < c) (hcb : c < b)
    (ha₀c₀ : a₀ < c₀) (hc₀b₀ : c₀ < b₀)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (hcarrier₀ : D₀.carrier = Icc a₀ b₀) (hregular₀ : Ioo a₀ b₀ ⊆ D₀.regular)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc c b) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc c₀ b₀) (x₀ : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x₀).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) x₀ i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j)) (q : ℕ)
    (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I x₀).symm y)) (Icc c b) (τ n))
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I x₀).symm y)) (Icc c₀ b₀) t₀)
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) := by
  exact ordinary_metric_time_jet_components_mapCInf_of_gram_on_closed_interval
    S hS S₀ hS₀ hac hcb ha₀c₀ hc₀b₀ hcarrier hregular hcarrier₀ hregular₀
    τ hτ t₀ ht₀ x₀ hW hWt hgram q slots

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
