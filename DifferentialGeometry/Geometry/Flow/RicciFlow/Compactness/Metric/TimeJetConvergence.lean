import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeJets
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
theorem mixed_curvature_components_contDiffOn_on_Ioc {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b t : ℝ} (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (ht : t ∈ Ioc a b) (p q : ℕ) (x₀ : M) {W : Set E}
    (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => mixedCurvatureTensor S p q t ((extChartAt I x₀).symm y)
      (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  obtain ⟨A, hA⟩ := exists_curvature_polynomial_field S (p + 2 * q) (4 + p) t
    (mixedJetPolynomial (Module.finrank ℝ E) p q) (fun x => mixedCurvatureTensor S p q t x)
    (fun x basis slots => (mixed_curvature_polynomial_on_Ioc S hS hcarrier hregular ht p q x basis).2 slots)
  apply (tensor_field_chart_components_contDiffOn A x₀ hWt slots).congr
  intro y _hy
  rw [hA]

theorem mixed_curvature_components_mapCInf_of_gram_on_closed_interval {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {a b a₀ b₀ : ℝ} (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (hcarrier₀ : D₀.carrier = Icc a₀ b₀) (hregular₀ : Ioo a₀ b₀ ⊆ D₀.regular)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Ioc a b) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioc a₀ b₀) (x₀ : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x₀).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) x₀ i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j)) (p q : ℕ)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y => mixedCurvatureTensor (S n) p q (τ n) ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y => mixedCurvatureTensor S₀ p q t₀ ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) := by
  classical
  let P := mixedJetPolynomial (Module.finrank ℝ E) p
  have hpoly := curvature_jet_polynomial_mapCInf_of_gram S S₀ τ t₀ x₀ hW hWt hgram
    (p + 2 * q) (P q slots)
  have hcomp {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
      (hT : IsSolutionOn T) {a c s : ℝ}
      (hcar : D'.carrier = Icc a c) (hreg : Ioo a c ⊆ D'.regular) (hs : s ∈ Ioc a c)
      (y : E) (hy : y ∈ W) :
      mixedCurvatureTensor T p q s ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)) =
      MvPolynomial.eval (chartCurvatureJetPolynomialValues T (p + 2 * q) s x₀ y) (P q slots) := by
    have hb : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hh := (extChartAt I x₀).map_target (hWt hy)
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hh
    have hh := (mixed_curvature_polynomial_on_Ioc T hT hcar hreg hs p q
      ((extChartAt I x₀).symm y) (chartBasisFamily (I := I) x₀ hb)).2 slots
    rw [curvatureJetPolynomialValues_eq_chart T (p + 2 * q) s x₀ hb] at hh
    simpa only [component0S_apply, chartBasisFamily_apply] using hh
  exact hpoly.congr hW
    (fun n y hy => hcomp (S n) (hS n) hcarrier hregular (hτ n) y hy)
    (fun y hy => hcomp S₀ hS₀ hcarrier₀ hregular₀ ht₀ y hy)


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


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem ordinary_metric_time_jet_components_mapCInf_of_jets {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D)
    (S₀ : SolutionOn (I := I) (M := M) D₀)
    (J J₀ : Set ℝ) (τ : ℕ → ℝ) (t₀ : ℝ) (x₀ : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x₀).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) x₀ i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j))
    (hformula : ∀ n q (x : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
      (slots : Fin 2 → Fin (Module.finrank ℝ E)),
      component0S (I := I) basis
        (iteratedDerivWithin (q + 1) (fun s => metricTensorField ((S n).base.metric s) x) J (τ n)) slots =
      MvPolynomial.eval (curvatureTimePolynomialValues (S n).base.metric
        (fun r s => mixedCurvatureTensor (S n) 0 r s x) basis (τ n))
        (ordinaryMetricJetPolynomial q slots))
    (hformula₀ : ∀ q (x : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
      (slots : Fin 2 → Fin (Module.finrank ℝ E)),
      component0S (I := I) basis
        (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S₀.base.metric s) x) J₀ t₀) slots =
      MvPolynomial.eval (curvatureTimePolynomialValues S₀.base.metric
        (fun r s => mixedCurvatureTensor S₀ 0 r s x) basis t₀)
        (ordinaryMetricJetPolynomial q slots))
    (hcurv : ∀ r (slots : Fin 4 → CoordinateIdx (𝕜 := ℝ) E), MapCInfConvergenceOnCompacts W
      (fun n y => mixedCurvatureTensor (S n) 0 r (τ n) ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y => mixedCurvatureTensor S₀ 0 r t₀ ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))))
    (hcurvc : ∀ n r (slots : Fin 4 → CoordinateIdx (𝕜 := ℝ) E),
      ContDiffOn ℝ ∞ (fun y => mixedCurvatureTensor (S n) 0 r (τ n) ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W)
    (hcurvc₀ : ∀ r (slots : Fin 4 → CoordinateIdx (𝕜 := ℝ) E),
      ContDiffOn ℝ ∞ (fun y => mixedCurvatureTensor S₀ 0 r t₀ ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W)
    (q : ℕ) (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I x₀).symm y)) J (τ n))
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I x₀).symm y)) J₀ t₀)
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
    have hv (z : CurvatureTimePolynomialVariable (Module.finrank ℝ E)) :
        MapCInfConvergenceOnCompacts W (fun n y => v (S n) (τ n) y z) (fun y => v S₀ t₀ y z) := by
      cases z with
      | inl ij =>
        exact mapCInfConvergence_chartInvGram_of_gram (fun n => (S n).base.metric (τ n))
          (S₀.base.metric t₀) x₀ hW hWt hgram ij.1 ij.2
      | inr rs => exact hcurv rs.1 rs.2
    have hvc (n : ℕ) (z : CurvatureTimePolynomialVariable (Module.finrank ℝ E)) :
        ContDiffOn ℝ ∞ (fun y => v (S n) (τ n) y z) W := by
      cases z with
      | inl ij => exact (chartInvGramOnE_contDiffOn (I := I) ((S n).base.metric (τ n)) x₀ ij.1 ij.2).mono hWt
      | inr rs => exact hcurvc n rs.1 rs.2
    have hvc₀ (z : CurvatureTimePolynomialVariable (Module.finrank ℝ E)) :
        ContDiffOn ℝ ∞ (fun y => v S₀ t₀ y z) W := by
      cases z with
      | inl ij => exact (chartInvGramOnE_contDiffOn (I := I) (S₀.base.metric t₀) x₀ ij.1 ij.2).mono hWt
      | inr rs => exact hcurvc₀ rs.1 rs.2
    have hpoly := mapCInfConvergence_polynomial_eval hW hv hvc hvc₀ (ordinaryMetricJetPolynomial q slots)
    have hcomp {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
        (J' : Set ℝ) (s : ℝ)
        (hformulaT : ∀ (x : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
          component0S (I := I) basis
            (iteratedDerivWithin (q + 1) (fun u => metricTensorField (T.base.metric u) x) J' s) slots =
          MvPolynomial.eval (curvatureTimePolynomialValues T.base.metric
            (fun r u => mixedCurvatureTensor T 0 r u x) basis s) (ordinaryMetricJetPolynomial q slots))
        (y : E) (hy : y ∈ W) :
        (iteratedDerivWithin (q + 1)
          (fun s => metricTensorField (T.base.metric s) ((extChartAt I x₀).symm y)) J' s)
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)) =
        MvPolynomial.eval (v T s y) (ordinaryMetricJetPolynomial q slots) := by
      have hb : (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I) x₀).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        have hh := (extChartAt I x₀).map_target (hWt hy)
        rwa [extChartAt_source_eq_chartAt_source (I := I)] at hh
      have hh := hformulaT ((extChartAt I x₀).symm y) (chartBasisFamily (I := I) x₀ hb)
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
      (fun n y hy => hcomp (S n) J (τ n) (fun x basis => hformula n q x basis slots) y hy)
      (fun y hy => hcomp S₀ J₀ t₀ (fun x basis => hformula₀ q x basis slots) y hy)

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
  apply ordinary_metric_time_jet_components_mapCInf_of_jets S S₀ (Iic b) (Iic b₀) τ t₀ x₀ hW hWt hgram
  · intro n q x basis slots
    exact ordinary_metric_time_jet_component_eq_polynomial (S n) (hS n) hcarrier hregular (hτ n)
      x basis q slots
  · intro q x basis slots
    exact ordinary_metric_time_jet_component_eq_polynomial S₀ hS₀ hcarrier₀ hregular₀ ht₀ x basis q slots
  · intro r slots
    exact mixed_curvature_components_mapCInf_of_gram S hS S₀ hS₀
      hcarrier hregular hcarrier₀ hregular₀ τ hτ t₀ ht₀ x₀ hW hWt hgram 0 r slots
  · intro n r slots
    exact mixed_curvature_components_contDiffOn (S n) (hS n) hcarrier hregular (hτ n) 0 r x₀ hWt slots
  · intro r slots
    exact mixed_curvature_components_contDiffOn S₀ hS₀ hcarrier₀ hregular₀ ht₀ 0 r x₀ hWt slots

omit [BoundarylessManifold I M] in
theorem ordinary_metric_time_jet_components_contDiffOn_of_closed_interval {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular) (ht : t ∈ Icc c b)
    (q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y =>
      (iteratedDerivWithin q
        (fun s => metricTensorField (S.base.metric s) ((extChartAt I x₀).symm y)) (Icc c b) t)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  obtain ⟨B, _hB₀, hB⟩ := exists_ordinary_metric_time_jets_on_closed_interval S hS hac hcb hcarrier hregular
  apply (tensor_field_chart_components_contDiffOn (B q t) x₀ hWt slots).congr
  intro y _hy
  rw [(hB q t ht ((extChartAt I x₀).symm y)).1]


theorem ordinary_metric_time_jet_components_mapCInf_of_gram_on_closed_interval {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {a c b a₀ c₀ b₀ : ℝ} (hac : a < c) (hcb : c < b) (hac₀ : a₀ < c₀) (hcb₀ : c₀ < b₀)
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
  apply ordinary_metric_time_jet_components_mapCInf_of_jets S S₀ (Icc c b) (Icc c₀ b₀) τ t₀ x₀ hW hWt hgram
  · intro n q x basis slots
    exact ordinary_metric_time_jet_component_eq_polynomial_on_closed_interval
      (S n) (hS n) hac hcb hcarrier hregular (hτ n) x basis q slots
  · intro q x basis slots
    exact ordinary_metric_time_jet_component_eq_polynomial_on_closed_interval
      S₀ hS₀ hac₀ hcb₀ hcarrier₀ hregular₀ ht₀ x basis q slots
  · intro r slots
    exact mixed_curvature_components_mapCInf_of_gram_on_closed_interval S hS S₀ hS₀
      hcarrier hregular hcarrier₀ hregular₀ τ
      (fun n => ⟨hac.trans_le (hτ n).1, (hτ n).2⟩) t₀ ⟨hac₀.trans_le ht₀.1, ht₀.2⟩
      x₀ hW hWt hgram 0 r slots
  · intro n r slots
    exact mixed_curvature_components_contDiffOn_on_Ioc (S n) (hS n) hcarrier hregular
      ⟨hac.trans_le (hτ n).1, (hτ n).2⟩ 0 r x₀ hWt slots
  · intro r slots
    exact mixed_curvature_components_contDiffOn_on_Ioc S₀ hS₀ hcarrier₀ hregular₀
      ⟨hac₀.trans_le ht₀.1, ht₀.2⟩ 0 r x₀ hWt slots

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
