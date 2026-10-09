import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false
noncomputable section

open Set Metric

namespace DifferentialGeometry.Geometry

/-- Deleting a countable set from the open complex unit disk leaves a connected
set. The deleted points may accumulate at the boundary. -/
theorem isConnected_openDisk_diff_countable {S : Set ℂ} (hS : S.Countable) :
    IsConnected (ball (0 : ℂ) 1 \ S) := by
  let e : ℂ ≃ₜ ball (0 : ℂ) 1 := Homeomorph.unitBall
  let f : ℂ → ℂ := fun z => (e z : ℂ)
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hbad : (f ⁻¹' S).Countable := hS.preimage hf
  have hplane : IsConnected ((f ⁻¹' S)ᶜ : Set ℂ) :=
    hbad.isConnected_compl_of_one_lt_rank (by simp)
  have himage : f '' (f ⁻¹' S)ᶜ = ball (0 : ℂ) 1 \ S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(e x).property, hx⟩
    · rintro ⟨hz, hnot⟩
      obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
      have hxz : f x = z := congrArg Subtype.val hx
      exact ⟨x, fun h => hnot (hxz ▸ h), hxz⟩
  rw [← himage]
  exact hplane.image f (continuous_subtype_val.comp e.continuous).continuousOn

end DifferentialGeometry.Geometry
