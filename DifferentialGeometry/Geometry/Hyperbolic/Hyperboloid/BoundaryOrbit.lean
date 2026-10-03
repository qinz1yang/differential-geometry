import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryFixedPoint
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.FixedPoint
import Mathlib.Algebra.Group.Action.End
import Mathlib.Basic.Finite.Prod

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem boundary_orbit_encard_le_two_of_finite
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E))
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : Hyperboloid E,
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x)
    (ξ : Metric.sphere (0 : E) 1)
    (hfinite : (Set.range (fun γ : Γ => boundaryHomeomorph
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).Finite) :
    (Set.range (fun γ : Γ => boundaryHomeomorph
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).encard ≤ 2 := by
  classical
  let _ : MulAction Γ (Metric.sphere (0 : E) 1) :=
    { smul := fun γ ξ => boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ
      one_smul := fun ξ => by
        change boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) ξ = ξ
        rw [boundaryHomeomorph_refl]
        rfl
      mul_smul := fun γ δ ξ => by
        change boundaryHomeomorph ((δ : Hyperboloid E ≃ᵢ Hyperboloid E).trans
          (γ : Hyperboloid E ≃ᵢ Hyperboloid E)) ξ = _
        rw [boundaryHomeomorph_trans]
        rfl }
  change (MulAction.orbit Γ ξ).Finite at hfinite
  change (MulAction.orbit Γ ξ).encard ≤ 2
  by_contra hlarge
  let _ : Finite (MulAction.orbit Γ ξ) := hfinite.to_subtype
  let ρ := MulAction.toPermHom Γ (MulAction.orbit Γ ξ)
  have hinj : Function.Injective ρ := by
    apply (injective_iff_map_eq_one ρ).mpr
    intro γ hγ
    by_contra hne
    apply hlarge
    apply (Set.encard_mono ?_).trans
      (fixedPoints_boundaryHomeomorph_encard_le_two
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) (hfree γ hne))
    intro η hη
    exact congrArg (fun f : Equiv.Perm (MulAction.orbit Γ ξ) =>
      (f ⟨η, hη⟩ : Metric.sphere (0 : E) 1)) hγ
  let _ : Finite Γ := Finite.of_injective ρ hinj
  let _ : MulAction Γ (Hyperboloid E) :=
    { smul := fun γ x => (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  let _ : IsIsometricSMul Γ (Hyperboloid E) := ⟨fun γ => γ.val.isometry⟩
  obtain ⟨p, hp⟩ := fixedPoints_nonempty_of_finite (E := E) Γ
  have hone (γ : Γ) : γ = 1 := by
    by_contra hγ
    exact hfree γ hγ p (hp γ)
  apply hlarge
  apply (Set.encard_mono (b := {ξ}) ?_).trans (by simp)
  rintro η ⟨γ, rfl⟩
  change γ • ξ ∈ {ξ}
  rw [hone γ, one_smul]
  exact Set.mem_singleton ξ

end DifferentialGeometry.Hyperboloid
