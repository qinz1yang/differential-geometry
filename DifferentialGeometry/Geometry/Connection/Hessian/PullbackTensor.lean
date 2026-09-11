import DifferentialGeometry.Geometry.Connection.TensorNabla.Pullback
import DifferentialGeometry.Geometry.Connection.Hessian

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

theorem multilinear_hessian_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (φ x).toContinuousLinearMap))
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) (k : ℕ)
    {T : ∀ x, Bundle.continuousMultilinearMap ℝ k F₂ V₂ x} {x : M}
    (hT : ContMDiffAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)) 2
      (fun y => TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ) y (T y)) x)
    (X Y : TangentSpace I x) :
    let hφ₁ := hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let D := multilinear
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map cov) k
    let U := fun y => (T y).compContinuousLinearMap (fun _ => (φ y).toContinuousLinearMap)
    D.hessian base U x X Y =
      ((multilinear cov k).hessian base T x X Y).compContinuousLinearMap
        (fun _ => (φ x).toContinuousLinearMap) := by
  let hφ₁ := hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let d := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ₁.clm_bundle_map cov
  let D := multilinear d k
  let U := fun y => (T y).compContinuousLinearMap (fun _ : Fin k => (φ y).toContinuousLinearMap)
  let : CompleteSpace F₁ := FiniteDimensional.complete ℝ F₁
  have hφinv : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) ∞
      (fun y => TotalSpace.mk' (F₂ →L[ℝ] F₁) y (φ y).symm.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  let : ContMDiffCovariantDerivative d ∞ :=
    ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map hφinv.clm_bundle_map cov
  have hU := hT.multilinear_bundle_comp (fun _ : Fin k =>
    (hφ x).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  change D.hessian base U x X Y = _
  rw [← hZ, hessian_apply_of_contMDiffAt D inferInstance base hU Z.mdifferentiableAt,
    hessian_apply_of_contMDiffAt (multilinear cov k) inferInstance base hT Z.mdifferentiableAt]
  exact multilinear_secondCovDeriv_pullbackFiberwiseLinearEquiv φ hφ₁ cov base k hT
    Z.mdifferentiableAt X

end CovariantDerivative
