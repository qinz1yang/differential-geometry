import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeCoefficientContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Chart.Inner
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Multilinear
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance polynomialFieldC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance polynomialFieldC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem polynomial_eval_contMDiffAt
    {σ : Type*} [Finite σ] (P : MvPolynomial σ ℝ)
    {v : M → σ → ℝ} {x : M}
    (hv : ∀ i, ContMDiffAt I 𝓘(ℝ) ∞ (fun y => v y i) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => MvPolynomial.eval (v y) P) x := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  simp only [MvPolynomial.eval_eq']
  exact ContMDiffAt.sum fun d _ => contMDiffAt_const.mul
    (ContMDiffAt.prod fun i _ => (hv i).pow (d i))

private def chartCurvatureValues {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) (x₀ x : M) :
    CurvatureJetPolynomialVariable (Module.finrank ℝ E) N → ℝ
  | Sum.inl ij => (chartGramMatrix (S.base.metric t) x₀ x)⁻¹ ij.1 ij.2
  | Sum.inr js => nablaKRm04Field S t js.1.val x
      (fun k => chartBasisVecFiber (I := I) x₀ (js.2 k) x)

private theorem chartCurvatureValues_contMDiffAt {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) (x₀ : M)
    (v : CurvatureJetPolynomialVariable (Module.finrank ℝ E) N) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun x => chartCurvatureValues S N t x₀ x v) x₀ := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  cases v with
  | inl ij =>
    exact (Tensor.Tensor0SRiemannian.chartGramMatrix_inv_entry_contMDiffOn
      (I := I) (S.base.metric t) x₀ ij.1 ij.2 x₀ hx₀).contMDiffAt
      (e.open_baseSet.mem_nhds hx₀)
  | inr js =>
    exact TensorMultilinear.contMDiffAt_section_apply
      (I := I) (T := fun x => nablaKRm04Field S t js.1.val x)
      ((nablaKRm04Field S t js.1.val).contMDiff x₀)
      (v := fun k x => chartBasisVecFiber (I := I) x₀ (js.2 k) x)
      (fun k => (chartBasisVec_contMDiffOn (I := I) x₀ (js.2 k) x₀ hx₀).contMDiffAt
        (e.open_baseSet.mem_nhds hx₀))

private theorem curvatureValues_eq_chartValues {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    curvatureJetPolynomialValues S N t (chartBasisFamily (I := I) x₀ hx) =
      chartCurvatureValues S N t x₀ x := by
  funext v
  cases v with
  | inl ij =>
    simp only [curvatureJetPolynomialValues, chartCurvatureValues,
      basisInvMetric_eq_matrix_inv]
    have hGram : Matrix.of (fun i j => (S.base.metric t).inner x
        (chartBasisFamily (I := I) x₀ hx i) (chartBasisFamily (I := I) x₀ hx j)) =
        chartGramMatrix (S.base.metric t) x₀ x := by
      ext i j
      simp only [Matrix.of_apply, chartBasisFamily_apply, chartGramMatrix_apply]
    rw [hGram]
  | inr js =>
    simp only [curvatureJetPolynomialValues, chartCurvatureValues,
      component0S_apply, chartBasisFamily_apply]


theorem exists_curvature_polynomial_field {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N r : ℕ) (t : ℝ)
    (P : (Fin r → Fin (Module.finrank ℝ E)) →
      MvPolynomial (CurvatureJetPolynomialVariable (Module.finrank ℝ E) N) ℝ)
    (T : (x : M) → Tensor0SSpace r I x)
    (hT : ∀ x : M, ∀ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ slots, component0S (I := I) basis (T x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S N t basis) (P slots)) :
    ∃ A : Tensor0SField (I := I) (M := M) (n := ∞) r, ∀ x, A x = T x := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (I := I) (M := M) r
  refine ⟨⟨T, ?_⟩, fun _ => rfl⟩
  let b := chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b T).mpr ?_
  intro slots x₀
  have hpoly := polynomial_eval_contMDiffAt (I := I) (P slots)
    (chartCurvatureValues_contMDiffAt S N t x₀)
  refine hpoly.congr_of_eventuallyEq ?_
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
  rw [continuousMultilinearMap_basis_repr]
  change (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) r x (T x)).compContinuousLinearMap
    (fun _ : Fin r => e.symmL ℝ x) (fun k => b (slots k)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
  have h := hT x (chartBasisFamily (I := I) x₀ hx) slots
  rw [curvatureValues_eq_chartValues S N t x₀ hx] at h
  simpa only [component0S_apply, chartBasisFamily_apply, chartBasisVecFiber, b, e] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
