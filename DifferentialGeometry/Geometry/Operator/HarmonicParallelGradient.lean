import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.CoordinateFormula
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

open Bundle Set Manifold
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem covariantDerivative_eq_zero_of_frobeniusSq_eq_zero
    (g : SmoothRiemannianMetric I M) (V : ∀ x : M, TangentSpace I x) (x : M)
    (hzero : frobeniusSqGradVector g V x = 0) :
    (LeviCivita g).toFun V x = 0 := by
  classical
  let e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i ↦ smoothOrthoFrame g x i x
  let L : TangentSpace I x →L[ℝ] TangentSpace I x := (LeviCivita g).toFun V x
  have he (i j : Fin (Module.finrank ℝ E)) :
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    smoothOrthoFrame_orthonormal_at_center g x i j
  have hLI : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hpair := congrArg (g.inner x (e i)) ha
    simpa [map_sum, map_smul, he, smul_eq_mul] using hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have hB (i : Fin (Module.finrank ℝ E)) : B i = e i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard) i
  have hnonneg (i : Fin (Module.finrank ℝ E)) :
      0 ≤ g.inner x (L (e i)) (L (e i)) := by
    by_cases hi : L (e i) = 0
    · simp [hi]
    · exact (g.pos x _ hi).le
  have hsum : ∑ i, g.inner x (L (e i)) (L (e i)) = 0 := hzero
  have hterm (i : Fin (Module.finrank ℝ E)) :
      g.inner x (L (e i)) (L (e i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnonneg j)).mp hsum i (Finset.mem_univ i)
  have hL (i : Fin (Module.finrank ℝ E)) : L (e i) = 0 := by
    by_contra hi
    exact (ne_of_gt (g.pos x _ hi)) (hterm i)
  ext v
  change L v = 0
  calc
    L v = L (∑ i, B.repr v i • B i) := congrArg L (B.sum_repr v).symm
    _ = 0 := by
      simp only [map_sum, map_smul, hB, hL, smul_zero, Finset.sum_const_zero]

variable [I.Boundaryless] [T2Space M]

theorem covariantDerivative_gradient_eq_zero_of_harmonic_constant_norm
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hharmonic : ∀ x : M, laplacian (LeviCivita g) g f x = 0)
    (c : ℝ)
    (hnorm : ∀ x : M, g.inner x (gradientFun g f x) (gradientFun g f x) = c)
    (hRic : ∀ x : M, ∀ v : TangentSpace I x, 0 ≤ ricciTensor g x v v)
    (x : M) :
    (LeviCivita g).toFun (fun y ↦ gradientFun g f y) x = 0 := by
  have hnormFun : normGradSqFun g f = fun _ : M ↦ c := by
    funext y
    simpa only [normGradSqFun_def, gradient_eq_gradFun] using hnorm y
  have hdeltaFun : ΔG g ⟨f, hf⟩ = fun _ : M ↦ (0 : ℝ) := by
    funext y
    rw [← laplacian_levi_eq g hf y]
    exact hharmonic y
  have hdeltaNorm : ΔG g ⟨normGradSqFun g f, normGradSqFun_contMDiff g hf⟩ x = 0 := by
    rw [← laplacian_levi_eq g (normGradSqFun_contMDiff g hf) x, hnormFun]
    exact laplacian_const (LeviCivita g) g c x
  have hbochner := bochner_pointwise_grad_normSq_of_boundaryless g hf x
  rw [hdeltaNorm, hdeltaFun,
    DifferentialGeometry.Geometry.Operator.gradFun_const] at hbochner
  simp only [map_zero, mul_zero, add_zero] at hbochner
  have hnonneg := frobeniusSq_grad_vector_nonneg g (fun y ↦ gradFun g f y) x
  have hRicGrad := hRic x (gradFun g f x)
  have hzero : frobeniusSqGradVector g (fun y ↦ gradFun g f y) x = 0 := by
    linarith
  apply covariantDerivative_eq_zero_of_frobeniusSq_eq_zero g _ x
  simpa only [gradient_eq_gradFun] using hzero

end DifferentialGeometry.Geometry.Operator

end
