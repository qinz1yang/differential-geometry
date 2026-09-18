import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvaturePolynomialConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureFields


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

private local instance mixedConvergenceC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [BoundarylessManifold I M] in
private theorem polynomial_on_ancient_carrier {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : ℕ) {n : ℕ}
    (P : (q : ℕ) → (Fin (4 + p) → Fin n) →
      MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ)
    (hP : ∀ q t, t ∈ D.regular → ∀ x : M,
      ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
      DifferentiableAt ℝ (fun s => mixedCurvatureTensor S p q s x) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots))
    (q : ℕ) {t : ℝ} (ht : t ≤ b) (x : M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin (4 + p) → Fin n) :
    component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots) := by
  rcases ht.lt_or_eq with ht | htb
  · exact (hP q t (by rwa [hregular]) x basis).2 slots
  · subst t
    have hreg : Ioo (b - 1) b ⊆ D.regular := by
      intro s hs
      rw [hregular]
      exact hs.2
    exact (mixedCurvature_polynomial_terminal_of_regular S hS p
      (by linarith : b - 1 < b) hcarrier hreg P x basis
      (fun q s hs => hP q s (hreg hs) x basis) q).2 slots

omit [BoundarylessManifold I M] in
theorem mixed_curvature_components_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b) (ht : t ≤ b)
    (p q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => mixedCurvatureTensor S p q t ((extChartAt I x₀).symm y)
      (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  obtain ⟨A, hA⟩ := exists_ancient_mixed_curvature_fields S hS hcarrier hregular p
  apply (tensor_field_chart_components_contDiffOn (A q t) x₀ hWt slots).congr
  intro y _hy
  rw [(hA q t ht ((extChartAt I x₀).symm y)).1]


theorem mixed_curvature_components_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {b b₀ : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (hcarrier₀ : D₀.carrier = Iic b₀) (hregular₀ : D₀.regular = Iio b₀)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ≤ b) (t₀ : ℝ) (ht₀ : t₀ ≤ b₀) (x₀ : M)
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
  choose P hP using fun q : ℕ =>
    exists_mixed_curvature_jet_polynomials (Module.finrank ℝ E) p q
  have hpoly := curvature_jet_polynomial_mapCInf_of_gram S S₀ τ t₀ x₀ hW hWt hgram
    (p + 2 * q) (P q slots)
  have hcomp {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
      (hT : IsSolutionOn T) {c s : ℝ}
      (hcar : D'.carrier = Iic c) (hreg : D'.regular = Iio c) (hs : s ≤ c)
      (y : E) (hy : y ∈ W) :
      mixedCurvatureTensor T p q s ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)) =
      MvPolynomial.eval (chartCurvatureJetPolynomialValues T (p + 2 * q) s x₀ y) (P q slots) := by
    have hb : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hh := (extChartAt I x₀).map_target (hWt hy)
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hh
    have hh := polynomial_on_ancient_carrier T hT hcar hreg p P
      (fun q s hs x basis => hP q T hT s hs x basis) q hs
      ((extChartAt I x₀).symm y) (chartBasisFamily (I := I) x₀ hb) slots
    rw [curvatureJetPolynomialValues_eq_chart T (p + 2 * q) s x₀ hb] at hh
    simpa only [component0S_apply, chartBasisFamily_apply] using hh
  exact hpoly.congr hW
    (fun n y hy => hcomp (S n) (hS n) hcarrier hregular (hτ n) y hy)
    (fun y hy => hcomp S₀ hS₀ hcarrier₀ hregular₀ ht₀ y hy)

omit [BoundarylessManifold I M] in
private theorem polynomial_on_closedWindow {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (p : ℕ) {n : ℕ}
    (P : (q : ℕ) → (Fin (4 + p) → Fin n) →
      MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ)
    (hP : ∀ q t, t ∈ D.regular → ∀ x : M,
      ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
      DifferentiableAt ℝ (fun s => mixedCurvatureTensor S p q s x) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc c b) (x : M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin (4 + p) → Fin n) :
    component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots) := by
  rcases ht.2.lt_or_eq with htb | htb
  · exact (hP q t (hregular ⟨hac.trans_le ht.1, htb⟩) x basis).2 slots
  · subst t
    exact (mixedCurvature_polynomial_terminal_of_regular_Icc S hS p le_rfl
      (hac.trans hcb) hcarrier hregular P x basis
      (fun q s hs => hP q s (hregular hs) x basis) q).2 slots

omit [BoundarylessManifold I M] in
theorem closedWindow_mixed_curvature_components_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular) (ht : t ∈ Icc c b)
    (p q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => mixedCurvatureTensor S p q t ((extChartAt I x₀).symm y)
      (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  obtain ⟨A, hA⟩ := exists_closedWindow_mixed_curvature_fields S hS hac hcb hcarrier hregular p
  apply (tensor_field_chart_components_contDiffOn (A q t) x₀ hWt slots).congr
  intro y _hy
  rw [(hA q t ht ((extChartAt I x₀).symm y)).1]


theorem closedWindow_mixed_curvature_components_mapCInf_of_gram {D D₀ : RealTimeInterval}
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
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j)) (p q : ℕ)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y => mixedCurvatureTensor (S n) p q (τ n) ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y => mixedCurvatureTensor S₀ p q t₀ ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) := by
  classical
  choose P hP using fun q : ℕ =>
    exists_mixed_curvature_jet_polynomials (Module.finrank ℝ E) p q
  have hpoly := curvature_jet_polynomial_mapCInf_of_gram S S₀ τ t₀ x₀ hW hWt hgram
    (p + 2 * q) (P q slots)
  have hcomp {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
      (hT : IsSolutionOn T) {a' c' b' s : ℝ}
      (hac' : a' < c') (hcb' : c' < b')
      (hcar : D'.carrier = Icc a' b') (hreg : Ioo a' b' ⊆ D'.regular)
      (hs : s ∈ Icc c' b')
      (y : E) (hy : y ∈ W) :
      mixedCurvatureTensor T p q s ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)) =
      MvPolynomial.eval (chartCurvatureJetPolynomialValues T (p + 2 * q) s x₀ y) (P q slots) := by
    have hb : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hh := (extChartAt I x₀).map_target (hWt hy)
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hh
    have hh := polynomial_on_closedWindow T hT hac' hcb' hcar hreg p P
      (fun q s hs x basis => hP q T hT s hs x basis) q hs
      ((extChartAt I x₀).symm y) (chartBasisFamily (I := I) x₀ hb) slots
    rw [curvatureJetPolynomialValues_eq_chart T (p + 2 * q) s x₀ hb] at hh
    simpa only [component0S_apply, chartBasisFamily_apply] using hh
  exact hpoly.congr hW
    (fun n y hy => hcomp (S n) (hS n) hac hcb hcarrier hregular (hτ n) y hy)
    (fun y hy => hcomp S₀ hS₀ ha₀c₀ hc₀b₀ hcarrier₀ hregular₀ ht₀ y hy)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
