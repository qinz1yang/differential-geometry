import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureTimePolynomialEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.PolynomialField


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor.Multilinear
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance timeFieldC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem tensor0S_hasDerivWithinAt_of_components {n r : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {A : ℝ → Tensor0SSpace r I x} {A' : Tensor0SSpace r I x} {J : Set ℝ} {t : ℝ}
    (hA : ∀ slots, HasDerivWithinAt (fun s => component0S (I := I) basis (A s) slots)
      (component0S (I := I) basis A' slots) J t) : HasDerivWithinAt A A' J t := by
  have hsum : HasDerivWithinAt
      (fun s => ∑ slots, component0S (I := I) basis (A s) slots • tensor0SBasis (I := I) basis r slots)
      (∑ slots, component0S (I := I) basis A' slots • tensor0SBasis (I := I) basis r slots) J t :=
    HasDerivWithinAt.fun_sum fun slots _ => (hA slots).smul_const (tensor0SBasis (I := I) basis r slots)
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

private def timePolynomialChartValues
    (g : ℝ → SmoothRiemannianMetric I M)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 4) (t : ℝ) (x₀ x : M) :
    CurvatureTimePolynomialVariable (Module.finrank ℝ E) → ℝ
  | Sum.inl ij => (chartGramMatrix (g t) x₀ x)⁻¹ ij.1 ij.2
  | Sum.inr qs => A qs.1 t x (fun k => chartBasisVecFiber (I := I) x₀ (qs.2 k) x)

private theorem timePolynomialChartValues_contMDiffAt
    (g : ℝ → SmoothRiemannianMetric I M)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 4) (t : ℝ) (x₀ : M)
    (v : CurvatureTimePolynomialVariable (Module.finrank ℝ E)) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun x => timePolynomialChartValues g A t x₀ x v) x₀ := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  cases v with
  | inl ij =>
    exact (Tensor.Tensor0SRiemannian.chartGramMatrix_inv_entry_contMDiffOn
      (I := I) (g t) x₀ ij.1 ij.2 x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)
  | inr qs =>
    exact TensorMultilinear.contMDiffAt_section_apply (I := I)
      (T := fun x => A qs.1 t x) ((A qs.1 t).contMDiff x₀)
      (v := fun k x => chartBasisVecFiber (I := I) x₀ (qs.2 k) x)
      (fun k => (chartBasisVec_contMDiffOn (I := I) x₀ (qs.2 k) x₀ hx₀).contMDiffAt
        (e.open_baseSet.mem_nhds hx₀))

private theorem timePolynomialValues_eq_chartValues
    (g : ℝ → SmoothRiemannianMetric I M)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 4) (t : ℝ) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    curvatureTimePolynomialValues g (fun q s => A q s x) (chartBasisFamily (I := I) x₀ hx) t =
      timePolynomialChartValues g A t x₀ x := by
  funext v
  cases v with
  | inl ij =>
    simp only [curvatureTimePolynomialValues, timePolynomialChartValues, basisInvMetric_eq_matrix_inv]
    have hGram : Matrix.of (fun i j => (g t).inner x
        (chartBasisFamily (I := I) x₀ hx i) (chartBasisFamily (I := I) x₀ hx j)) =
        chartGramMatrix (g t) x₀ x := by
      ext i j
      simp only [Matrix.of_apply, chartBasisFamily_apply, chartGramMatrix_apply]
    rw [hGram]
  | inr qs =>
    simp only [curvatureTimePolynomialValues, timePolynomialChartValues,
      component0S_apply, chartBasisFamily_apply]


theorem exists_time_polynomial_field
    (g : ℝ → SmoothRiemannianMetric I M)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 4) (t : ℝ) (r : ℕ)
    (P : (Fin r → Fin (Module.finrank ℝ E)) →
      MvPolynomial (CurvatureTimePolynomialVariable (Module.finrank ℝ E)) ℝ)
    (T : (x : M) → Tensor0SSpace r I x)
    (hT : ∀ x, ∀ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ slots, component0S (I := I) basis (T x) slots =
        MvPolynomial.eval (curvatureTimePolynomialValues g (fun q s => A q s x) basis t) (P slots)) :
    ∃ B : Tensor0SField (I := I) (M := M) (n := ∞) r, ∀ x, B x = T x := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (I := I) (M := M) r
  refine ⟨⟨T, ?_⟩, fun _ => rfl⟩
  let b := chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b T).mpr ?_
  intro slots x₀
  have hpoly := polynomial_eval_contMDiffAt_of_variables (I := I)
    (timePolynomialChartValues_contMDiffAt g A t x₀) (P slots)
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
  rw [timePolynomialValues_eq_chartValues g A t x₀ hx] at h
  simpa only [component0S_apply, chartBasisFamily_apply, chartBasisVecFiber, b, e] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
