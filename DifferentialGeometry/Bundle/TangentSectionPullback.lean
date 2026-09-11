import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Bundle.PartialMfderiv.Composition
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]

def pullbackTangentSection (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hφinv : ∀ x, (mfderiv I J φ x).IsInvertible)
    (X : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun := VectorField.mpullback I J φ X
  contMDiff_toFun := X.contMDiff.mpullback_vectorField hφ hφinv (by simp)

theorem mfderiv_pullbackTangentSection (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hφinv : ∀ x, (mfderiv I J φ x).IsInvertible)
    (X : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) (x : M) :
    mfderiv I J φ x (pullbackTangentSection φ hφ hφinv X x) = X (φ x) :=
  (hφinv x).self_apply_inverse _

theorem mvfderiv_pullbackTangentSection (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hφinv : ∀ x, (mfderiv I J φ x).IsInvertible)
    (X : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯)
    (u : N → ℝ) (x : M) (hu : MDifferentiableAt J 𝓘(ℝ, ℝ) u (φ x)) :
    mvfderiv I (u ∘ φ) x (pullbackTangentSection φ hφ hφinv X x) =
      mvfderiv J u (φ x) (X (φ x)) := by
  rw [mvfderiv_comp_apply x hu (hφ x |>.mdifferentiableAt (by simp)),
    mfderiv_pullbackTangentSection]

end

end DifferentialGeometry
