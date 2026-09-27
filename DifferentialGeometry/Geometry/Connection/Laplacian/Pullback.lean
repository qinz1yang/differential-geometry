import DifferentialGeometry.Geometry.Connection.Pullback
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]

section SecondCovDeriv

variable [IsManifold I 1 M]

theorem map_secondCovDeriv_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov : CovariantDerivative I F₂ V₂) (s : ∀ x, V₁ x)
    (Y : ∀ x, TangentSpace I x) (x : M) (X : TangentSpace I x) :
    φ x
        (pullbackFiberwiseLinearEquiv φ hφ cov
            (fun y => pullbackFiberwiseLinearEquiv φ hφ cov s y (Y y)) x X -
          pullbackFiberwiseLinearEquiv φ hφ cov s x (base Y x X)) =
      cov (fun y => cov (fun z => φ z (s z)) y (Y y)) x X -
        cov (fun y => φ y (s y)) x (base Y x X) := by
  simp only [map_sub, map_pullbackFiberwiseLinearEquiv_apply]

theorem secondCovDeriv_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov : CovariantDerivative I F₂ V₂) (s : ∀ x, V₁ x)
    (Y : ∀ x, TangentSpace I x) (x : M) (X : TangentSpace I x) :
    pullbackFiberwiseLinearEquiv φ hφ cov
          (fun y => pullbackFiberwiseLinearEquiv φ hφ cov s y (Y y)) x X -
        pullbackFiberwiseLinearEquiv φ hφ cov s x (base Y x X) =
      (φ x).symm
        (cov (fun y => cov (fun z => φ z (s z)) y (Y y)) x X -
          cov (fun y => φ y (s y)) x (base Y x X)) := by
  apply (φ x).injective
  rw [LinearEquiv.apply_symm_apply]
  exact map_secondCovDeriv_pullbackFiberwiseLinearEquiv φ hφ base cov s Y x X

end SecondCovDeriv

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

theorem map_rawBundleConnLap_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F₂ V₂)
    (s : ∀ x, V₁ x) (x : M) :
    φ x (rawBundleConnLap g (pullbackFiberwiseLinearEquiv φ hφ cov) s x) =
      rawBundleConnLap g cov (fun y => φ y (s y)) x := by
  simp only [rawBundleConnLap_def, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact map_secondCovDeriv_pullbackFiberwiseLinearEquiv
    φ hφ (LeviCivita g) cov s (smoothOrthoFrame g x i) x (smoothOrthoFrame g x i x)

theorem rawBundleConnLap_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F₂ V₂)
    (s : ∀ x, V₁ x) (x : M) :
    rawBundleConnLap g (pullbackFiberwiseLinearEquiv φ hφ cov) s x =
      (φ x).symm (rawBundleConnLap g cov (fun y => φ y (s y)) x) := by
  apply (φ x).injective
  rw [LinearEquiv.apply_symm_apply]
  exact map_rawBundleConnLap_pullbackFiberwiseLinearEquiv φ hφ g cov s x

end DifferentialGeometry.Geometry.Connection
