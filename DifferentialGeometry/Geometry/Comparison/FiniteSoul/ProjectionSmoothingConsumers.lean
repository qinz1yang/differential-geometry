import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ProjectionSmoothing
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Consumers of S-BUNDLE on the round circle

Lane CMS-BUN (consumer of G3). On the compact Hausdorff smooth circle `S¹ ⊆ ℝ²`, a `C^k` field of
orthogonal projections is `δ`-close to a smooth one, and the two are conjugate by a `C^k` field of
linear isometric equivalences of the whole space (packaged through `Unitary.linearIsometryEquiv`).
The frozen D-CMS form elaborates on the circle with the instances found by Mathlib.
-/

set_option autoImplicit false

noncomputable section

open Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- On the circle: a smooth projection field `δ`-close to `P`, conjugate to `P` by a `C^k` field of
linear isometric equivalences of `F`. -/
theorem exists_smooth_projection_linearIsometryEquiv_circle {k : ℕ}
    (P : sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1 → F →L[ℝ] F)
    (hP : ContMDiff (𝓡 1) 𝓘(ℝ, F →L[ℝ] F) k P) (hidem : ∀ s, P s ∘L P s = P s)
    (hsymm : ∀ s, (P s).adjoint = P s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Phat : sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1 → F →L[ℝ] F)
      (B : sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1 → F ≃ₗᵢ[ℝ] F),
      ContMDiff (𝓡 1) 𝓘(ℝ, F →L[ℝ] F) ∞ Phat ∧
      ContMDiff (𝓡 1) 𝓘(ℝ, F →L[ℝ] F) k (fun s => ((B s).toContinuousLinearEquiv : F →L[ℝ] F)) ∧
      (∀ s, ‖Phat s - P s‖ < δ) ∧ ∀ s v, B s (P s v) = Phat s (B s v) := by
  obtain ⟨Phat, Bmap, hPhat, hB, hδs, -, -, hint, hBB, hBB', -, -, -, -⟩ :=
    exists_smooth_projection_and_orthogonal_intertwiner P hP hidem hsymm hδ
  have hmem : ∀ s, Bmap s ∈ unitary (F →L[ℝ] F) := fun s => by
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
    exact ⟨hBB s, hBB' s⟩
  refine ⟨Phat, fun s => Unitary.linearIsometryEquiv ⟨Bmap s, hmem s⟩, hPhat, ?_, hδs,
    fun s v => congrArg (fun L : F →L[ℝ] F => L v) (hint s)⟩
  have hfun : (fun s => ((Unitary.linearIsometryEquiv ⟨Bmap s, hmem s⟩ : F ≃ₗᵢ[ℝ] F)
      |>.toContinuousLinearEquiv : F →L[ℝ] F)) = Bmap := by
    funext s
    ext v
    rfl
  rw [hfun]
  exact hB

/-- The frozen D-CMS interface (with `[T2Space S]`) applies on the circle. -/
example {k : ℕ} (P : sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1 → F →L[ℝ] F)
    (hP : ContMDiff (𝓡 1) 𝓘(ℝ, F →L[ℝ] F) k P) (hidem : ∀ s, P s ∘L P s = P s)
    (hsymm : ∀ s, (P s).adjoint = P s) :
    ∃ (Phat : sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1 → F →L[ℝ] F)
      (Bmap : sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1 → F →L[ℝ] F),
      ContMDiff (𝓡 1) 𝓘(ℝ, F →L[ℝ] F) ∞ Phat ∧ ContMDiff (𝓡 1) 𝓘(ℝ, F →L[ℝ] F) k Bmap ∧
      (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
      (∀ s, Module.finrank ℝ (LinearMap.range (Phat s : F →ₗ[ℝ] F)) =
        Module.finrank ℝ (LinearMap.range (P s : F →ₗ[ℝ] F))) ∧
      (∀ s v, P s v = v → Phat s (Bmap s v) = Bmap s v ∧ ‖Bmap s v‖ = ‖v‖) ∧
      (∀ s w, Phat s w = w → ∃ v, P s v = v ∧ Bmap s v = w) :=
  exists_smooth_projection_and_isometry P hP hidem hsymm

end DifferentialGeometry.Geometry.FiniteSoul
