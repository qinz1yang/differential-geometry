import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricJetFormula
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureConvergence


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
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
theorem ordinary_metric_time_jet_components_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b) (ht : t ≤ b)
    (q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y =>
      (iteratedDerivWithin q
        (fun s => metricTensorField (S.base.metric s) ((extChartAt I x₀).symm y)) (Iic b) t)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  obtain ⟨B, _hB₀, hB⟩ := exists_ancient_ordinary_metric_time_jets S hS hcarrier hregular
  apply (tensor_field_chart_components_contDiffOn (B q t) x₀ hWt slots).congr
  intro y _hy
  rw [(hB q t ht ((extChartAt I x₀).symm y)).1]


theorem ordinary_metric_time_jet_components_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {b b₀ : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (hcarrier₀ : D₀.carrier = Iic b₀) (hregular₀ : D₀.regular = Iio b₀)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ≤ b) (t₀ : ℝ) (ht₀ : t₀ ≤ b₀) (x₀ : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x₀).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) x₀ i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j)) (q : ℕ)
    (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I x₀).symm y)) (Iic b) (τ n))
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I x₀).symm y)) (Iic b₀) t₀)
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) := by
  cases q with
  | zero =>
    apply (hgram (slots 0) (slots 1)).congr hW
    · intro n y _hy
      simp only [iteratedDerivWithin_zero, metricTensorField_apply,
        chartGramOnE_def, chartGramMatrix_apply]
    · intro y _hy
      simp only [iteratedDerivWithin_zero, metricTensorField_apply,
        chartGramOnE_def, chartGramMatrix_apply]
  | succ q =>
    let v {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D') (s : ℝ) (y : E) :
        CurvatureTimePolynomialVariable (Module.finrank ℝ E) → ℝ
      | Sum.inl ij => chartInvGramOnE (I := I) (T.base.metric s) x₀ ij.1 ij.2 y
      | Sum.inr rs => mixedCurvatureTensor T 0 rs.1 s ((extChartAt I x₀).symm y)
          (fun j => chartBasisVecFiber (I := I) x₀ (rs.2 j) ((extChartAt I x₀).symm y))
    have hvc {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
        (hT : IsSolutionOn T) {c s : ℝ}
        (hcar : D'.carrier = Iic c) (hreg : D'.regular = Iio c) (hs : s ≤ c)
        (z : CurvatureTimePolynomialVariable (Module.finrank ℝ E)) :
        ContDiffOn ℝ ∞ (fun y => v T s y z) W := by
      cases z with
      | inl ij => exact (chartInvGramOnE_contDiffOn (I := I) (T.base.metric s) x₀ ij.1 ij.2).mono hWt
      | inr rs => exact mixed_curvature_components_contDiffOn T hT hcar hreg hs 0 rs.1 x₀ hWt rs.2
    have hv (z : CurvatureTimePolynomialVariable (Module.finrank ℝ E)) :
        MapCInfConvergenceOnCompacts W (fun n y => v (S n) (τ n) y z) (fun y => v S₀ t₀ y z) := by
      cases z with
      | inl ij =>
        exact mapCInfConvergence_chartInvGram_of_gram (fun n => (S n).base.metric (τ n))
          (S₀.base.metric t₀) x₀ hW hWt hgram ij.1 ij.2
      | inr rs =>
        exact mixed_curvature_components_mapCInf_of_gram S hS S₀ hS₀
          hcarrier hregular hcarrier₀ hregular₀ τ hτ t₀ ht₀ x₀ hW hWt hgram 0 rs.1 rs.2
    have hpoly := mapCInfConvergence_polynomial_eval hW hv
      (fun n => hvc (S n) (hS n) hcarrier hregular (hτ n))
      (hvc S₀ hS₀ hcarrier₀ hregular₀ ht₀) (ordinaryMetricJetPolynomial q slots)
    have hcomp {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
        (hT : IsSolutionOn T) {c s : ℝ}
        (hcar : D'.carrier = Iic c) (hreg : D'.regular = Iio c) (hs : s ≤ c)
        (y : E) (hy : y ∈ W) :
        (iteratedDerivWithin (q + 1)
          (fun s => metricTensorField (T.base.metric s) ((extChartAt I x₀).symm y)) (Iic c) s)
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)) =
        MvPolynomial.eval (v T s y) (ordinaryMetricJetPolynomial q slots) := by
      have hb : (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I) x₀).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        have hh := (extChartAt I x₀).map_target (hWt hy)
        rwa [extChartAt_source_eq_chartAt_source (I := I)] at hh
      have hh := ordinary_metric_time_jet_component_eq_polynomial T hT hcar hreg hs
        ((extChartAt I x₀).symm y) (chartBasisFamily (I := I) x₀ hb) q slots
      have hvalues : curvatureTimePolynomialValues T.base.metric
          (fun r s => mixedCurvatureTensor T 0 r s ((extChartAt I x₀).symm y))
          (chartBasisFamily (I := I) x₀ hb) s = v T s y := by
        funext z
        cases z with
        | inl ij =>
          have heq := congrFun (curvatureJetPolynomialValues_eq_chart T 0 s x₀ hb) (Sum.inl ij)
          simpa only [curvatureTimePolynomialValues, curvatureJetPolynomialValues,
            chartCurvatureJetPolynomialValues, v] using heq
        | inr rs =>
          simp only [curvatureTimePolynomialValues, component0S_apply, chartBasisFamily_apply, v]
      rw [hvalues] at hh
      simpa only [component0S_apply, chartBasisFamily_apply] using hh
    exact hpoly.congr hW
      (fun n y hy => hcomp (S n) (hS n) hcarrier hregular (hτ n) y hy)
      (fun y hy => hcomp S₀ hS₀ hcarrier₀ hregular₀ ht₀ y hy)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
