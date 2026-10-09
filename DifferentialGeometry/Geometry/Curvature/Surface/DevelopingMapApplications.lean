import DifferentialGeometry.Geometry.Curvature.Surface.DevelopingMapFlat
import DifferentialGeometry.Geometry.Curvature.Surface.PeriodicGaussBonnetApplications

/-!
# Consumer of the developing map: constant coefficient fields

A constant positive symmetric coefficient field `b ≡ B₀` on a two-dimensional space is flat
(SF-B2's `coefficientSectional_const_eq_zero`), and FT1 produces its developing map for every
basis of periods; the closed-connection form applies directly since its connection potentials
vanish.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The developing map of a constant field, for any basis of periods (via FT1). -/
theorem exists_developing_const (hE : Module.finrank ℝ E = 2) {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ u v, B₀ u v = B₀ v u) (hpos : ∀ v, v ≠ 0 → 0 < B₀ v v) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ∃ (φ : E ≃ₜ ℂ) (l₁ l₂ : ℂ), ContDiff ℝ 1 φ ∧
      (∀ y u v, inner ℝ (fderiv ℝ φ y u) (fderiv ℝ φ y v) = B₀ u v) ∧
      (∀ y, φ (y + v₁) = φ y + l₁) ∧ (∀ y, φ (y + v₂) = φ y + l₂) :=
  exists_developing_of_periodic_flat hE (b := fun _ => B₀) contDiff_const (fun _ => hsymm)
    (fun _ => hpos) hli (fun _ => rfl) (fun _ => rfl)
    (fun y => coefficientSectional_const_eq_zero hE B₀ hsymm hpos y v₁ v₂)

/-- The closed-connection form applied to a constant field (vanishing potentials). -/
theorem exists_developing_const_of_closed (hE : Module.finrank ℝ E = 2)
    {B₀ : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ u v, B₀ u v = B₀ v u)
    (hpos : ∀ v, v ≠ 0 → 0 < B₀ v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ∃ (φ : E ≃ₜ ℂ) (l₁ l₂ : ℂ), ∀ y, φ (y + v₁) = φ y + l₁ ∧ φ (y + v₂) = φ y + l₂ := by
  have hP : surfaceConnectionP (fun _ => B₀) v₁ v₂ = fun _ => 0 :=
    funext fun y => surfaceConnectionP_const B₀ v₁ v₂ y
  have hQ : surfaceConnectionQ (fun _ => B₀) v₁ v₂ = fun _ => 0 :=
    funext fun y => surfaceConnectionQ_const B₀ v₁ v₂ y
  obtain ⟨φ, -, l₁, l₂, -, -, -, -, -, h₁, h₂⟩ := exists_developing_of_closed_connection hE
    (b := fun _ => B₀) contDiff_const (fun _ => hsymm) (fun _ => hpos) hli (fun _ => rfl)
    (fun _ => rfl) (fun y => by rw [hP, hQ]; simp)
  exact ⟨φ, l₁, l₂, fun y => ⟨h₁ y, h₂ y⟩⟩

end DifferentialGeometry.Analysis
