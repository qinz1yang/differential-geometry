import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialCurvatureJetContinuity
import DifferentialGeometry.Analysis.Calculus.TimeJet.PolynomialEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.PolynomialField


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology BigOperators
open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open CanonicalNeighborhood

section Scalar

variable {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem polynomial_eval_contDiffOn {W : Set E} {v : E → σ → ℝ}
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun y => v y i) W) (P : MvPolynomial σ ℝ) :
    ContDiffOn ℝ ∞ (fun y => MvPolynomial.eval (v y) P) W := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiffOn_const (c := c))
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.eval_X] using hP.mul (hv i)


theorem mapCInfConvergence_polynomial_eval {W : Set E} (hW : IsOpen W)
    {v : ℕ → E → σ → ℝ} {v₀ : E → σ → ℝ}
    (h : ∀ i, MapCInfConvergenceOnCompacts W (fun n y => v n y i) (fun y => v₀ y i))
    (hv : ∀ n i, ContDiffOn ℝ ∞ (fun y => v n y i) W)
    (hv₀ : ∀ i, ContDiffOn ℝ ∞ (fun y => v₀ y i) W) (P : MvPolynomial σ ℝ) :
    MapCInfConvergenceOnCompacts W (fun n y => MvPolynomial.eval (v n y) P)
      (fun y => MvPolynomial.eval (v₀ y) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C] using (mapCInfConvergence_const (fun _ : E => c) (U := W))
  | add P Q hP hQ =>
    have hh := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 + z.2)
      (contDiff_fst.add contDiff_snd) hP hQ
      (fun n => polynomial_eval_contDiffOn (hv n) P)
      (polynomial_eval_contDiffOn hv₀ P)
      (fun n => polynomial_eval_contDiffOn (hv n) Q)
      (polynomial_eval_contDiffOn hv₀ Q)
    simpa only [map_add] using hh
  | mul_X P i hP =>
    have hh := mapCInfConvergence_scalar_binopOn hW (fun z => z.1 * z.2)
      (contDiff_fst.mul contDiff_snd) hP (h i)
      (fun n => polynomial_eval_contDiffOn (hv n) P)
      (polynomial_eval_contDiffOn hv₀ P) (fun n => hv n i) (hv₀ i)
    simpa only [map_mul, MvPolynomial.eval_X] using hh

end Scalar

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance curvaturePolynomialC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


export DifferentialGeometry.CheegerGromovCompactness (mapCInfConvergence_chartInvGram_of_gram)

variable [T2Space M]


def chartCurvatureJetPolynomialValues {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) (p : M) (y : E) :
    CurvatureJetPolynomialVariable (Module.finrank ℝ E) N → ℝ
  | Sum.inl ij => chartInvGramOnE (I := I) (S.base.metric t) p ij.1 ij.2 y
  | Sum.inr js => nablaKRm04Field S t js.1.val ((extChartAt I p).symm y)
      (fun k => chartBasisVecFiber (I := I) p (js.2 k) ((extChartAt I p).symm y))


theorem chartCurvatureJetPolynomialValues_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) (p : M)
    {W : Set E} (hWt : W ⊆ (extChartAt I p).target)
    (v : CurvatureJetPolynomialVariable (Module.finrank ℝ E) N) :
    ContDiffOn ℝ ∞ (fun y => chartCurvatureJetPolynomialValues S N t p y v) W := by
  cases v with
  | inl ij => exact (chartInvGramOnE_contDiffOn (I := I) (S.base.metric t) p ij.1 ij.2).mono hWt
  | inr js =>
    exact tensor_field_chart_components_contDiffOn (nablaKRm04Field S t js.1.val) p hWt js.2


theorem curvatureJetPolynomialValues_eq_chart {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) (p : M) {y : E}
    (hy : (extChartAt I p).symm y ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    curvatureJetPolynomialValues S N t (chartBasisFamily (I := I) p hy) =
      chartCurvatureJetPolynomialValues S N t p y := by
  funext v
  cases v with
  | inl ij =>
    simp only [curvatureJetPolynomialValues, chartCurvatureJetPolynomialValues,
      basisInvMetric_eq_matrix_inv, chartInvGramOnE_def, chartInvGramMatrix]
    have hGram : Matrix.of (fun i j => (S.base.metric t).inner ((extChartAt I p).symm y)
        (chartBasisFamily (I := I) p hy i) (chartBasisFamily (I := I) p hy j)) =
        chartGramMatrix (S.base.metric t) p ((extChartAt I p).symm y) := by
      ext i j
      simp only [Matrix.of_apply, chartBasisFamily_apply, chartGramMatrix_apply]
    rw [hGram]
  | inr js =>
    simp only [curvatureJetPolynomialValues, chartCurvatureJetPolynomialValues,
      component0S_apply, chartBasisFamily_apply]

variable [CompleteSpace E] [I.Boundaryless] [BoundarylessManifold I M]


theorem curvature_jet_polynomial_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (S₀ : SolutionOn (I := I) (M := M) D₀)
    (τ : ℕ → ℝ) (t₀ : ℝ) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) p i j))
    (N : ℕ) (P : MvPolynomial (CurvatureJetPolynomialVariable (Module.finrank ℝ E) N) ℝ) :
    MapCInfConvergenceOnCompacts W
      (fun n y => MvPolynomial.eval (chartCurvatureJetPolynomialValues (S n) N (τ n) p y) P)
      (fun y => MvPolynomial.eval (chartCurvatureJetPolynomialValues S₀ N t₀ p y) P) := by
  apply mapCInfConvergence_polynomial_eval hW
    (hv := fun n => chartCurvatureJetPolynomialValues_contDiffOn (S n) N (τ n) p hWt)
    (hv₀ := chartCurvatureJetPolynomialValues_contDiffOn S₀ N t₀ p hWt)
  intro v
  cases v with
  | inl ij =>
    exact mapCInfConvergence_chartInvGram_of_gram (fun n => (S n).base.metric (τ n))
      (S₀.base.metric t₀) p hW hWt hgram ij.1 ij.2
  | inr js =>
    apply mapCInf_apply hW (spatial_curvature_jets_mapCInf_of_gram S S₀ τ t₀ p hW hWt hgram js.1.val)
    · intro n
      exact contDiffOn_pi.mpr
        (tensor_field_chart_components_contDiffOn (nablaKRm04Field (S n) (τ n) js.1.val) p hWt)
    · exact contDiffOn_pi.mpr
        (tensor_field_chart_components_contDiffOn (nablaKRm04Field S₀ t₀ js.1.val) p hWt)

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
