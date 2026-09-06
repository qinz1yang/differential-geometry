import DifferentialGeometry.Geometry.Connection.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I] [IsContMDiffRiemannianBundle I 1 F₁ V₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 1 F₂ V₂ I] [IsContMDiffRiemannianBundle I 1 F₂ V₂]

theorem IsMetricCompatible.pullbackFiberwiseLinearEquiv
    {cov : CovariantDerivative I F₂ V₂} (hcov : cov.IsMetricCompatible)
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (hφinner : ∀ x v w, inner ℝ (φ x v) (φ x w) = inner ℝ v w) :
    (CovariantDerivative.pullbackFiberwiseLinearEquiv φ hφ cov).IsMetricCompatible := by
  classical
  unfold CovariantDerivative.IsMetricCompatible
  funext x
  ext v w X
  rw [derivMetricTensor_apply_eq_extend]
  let σ := FiberBundle.extend F₁ v
  let τ := FiberBundle.extend F₁ w
  have hσ : MDiffAt (T% σ) x := FiberBundle.mdifferentiableAt_extend I F₁ v
  have hτ : MDiffAt (T% τ) x := FiberBundle.mdifferentiableAt_extend I F₁ w
  have hφσ : MDiffAt (T% (fun y => φ y (σ y))) x :=
    (hφ.mdifferentiableAt one_ne_zero).comp x hσ
  have hφτ : MDiffAt (T% (fun y => φ y (τ y))) x :=
    (hφ.mdifferentiableAt one_ne_zero).comp x hτ
  have hmetric := hcov.mvfderiv_inner_eq
    (Function.update (fun y => (0 : TangentSpace I y)) x X) hφσ hφτ
  simp only [Function.update_self] at hmetric
  rw [← map_pullbackFiberwiseLinearEquiv_apply φ hφ cov σ x X,
    ← map_pullbackFiberwiseLinearEquiv_apply φ hφ cov τ x X] at hmetric
  simp_rw [hφinner] at hmetric
  simp only [σ, τ, FiberBundle.extend_apply_self] at hmetric
  simp only [Pi.zero_apply, zero_apply]
  linarith [hmetric]

end CovariantDerivative
