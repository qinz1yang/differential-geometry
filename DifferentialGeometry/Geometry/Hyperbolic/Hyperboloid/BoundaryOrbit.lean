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

theorem boundaryHomeomorph_eq_self_of_finite_orbit
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E))
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : Hyperboloid E,
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x)
    (ξ : Metric.sphere (0 : E) 1)
    (hfinite : (Set.range (fun γ : Γ => boundaryHomeomorph
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).Finite) :
    ∀ γ : Γ, boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ := by
  classical
  intro γ
  by_contra hmove
  let η := boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ
  have hne : ξ ≠ η := Ne.symm hmove
  let S := Set.range (fun δ : Γ => boundaryHomeomorph
    (δ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)
  have hcard : S.encard ≤ 2 := boundary_orbit_encard_le_two_of_finite Γ hfree ξ hfinite
  have hξ : ξ ∈ S := by
    refine ⟨1, ?_⟩
    change boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) ξ = ξ
    rw [boundaryHomeomorph_refl]
    rfl
  have hη : η ∈ S := ⟨γ, rfl⟩
  have hpair : ({ξ, η} : Set (Metric.sphere (0 : E) 1)) = S :=
    ((Set.finite_singleton η).insert ξ).eq_of_subset_of_encard_le (Set.pair_subset hξ hη)
      (by simpa only [Set.encard_pair hne] using hcard)
  have himage : boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) η ∈ S := by
    refine ⟨γ * γ, ?_⟩
    change boundaryHomeomorph ((γ : Hyperboloid E ≃ᵢ Hyperboloid E).trans
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E)) ξ = _
    rw [boundaryHomeomorph_trans]
    rfl
  rw [← hpair] at himage
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at himage
  have hswap : boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) η = ξ := by
    rcases himage with hswap | hfix
    · exact hswap
    · exact (hne ((boundaryHomeomorph
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E)).injective hfix).symm).elim
  have hγ : γ ≠ 1 := by
    intro heq
    apply hmove
    rw [heq]
    change boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) ξ = ξ
    rw [boundaryHomeomorph_refl]
    rfl
  obtain ⟨p, hp⟩ := exists_fixedPoint_of_boundary_swap
    (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ η hne rfl hswap
  exact hfree γ hγ p hp

end DifferentialGeometry.Hyperboloid
