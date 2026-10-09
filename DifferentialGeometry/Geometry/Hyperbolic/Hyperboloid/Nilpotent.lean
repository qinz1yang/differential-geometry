import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryFixedPoint
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.GroupTheory.Nilpotent

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem boundaryHomeomorph_mul_apply (f g : Hyperboloid E ≃ᵢ Hyperboloid E)
    (ξ : Metric.sphere (0 : E) 1) :
    boundaryHomeomorph (f * g) ξ = boundaryHomeomorph f (boundaryHomeomorph g ξ) := by
  change boundaryHomeomorph (g.trans f) ξ = _
  rw [boundaryHomeomorph_trans]
  rfl

theorem exists_boundary_orbit_encard_le_two_of_isNilpotent
    [FiniteDimensional ℝ E] [Nontrivial E]
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [Group.IsNilpotent Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : Hyperboloid E,
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x) :
    ∃ ξ : Metric.sphere (0 : E) 1,
      (Set.range (fun γ : Γ => boundaryHomeomorph
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).encard ≤ 2 := by
  classical
  by_cases hΓ : Γ = ⊥
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    let ξ : Metric.sphere (0 : E) 1 := ⟨NormedSpace.normalize v, by
      simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩
    refine ⟨ξ, (Set.encard_mono (b := {ξ}) ?_).trans (by simp)⟩
    rintro _ ⟨γ, rfl⟩
    have hγ : (γ : Hyperboloid E ≃ᵢ Hyperboloid E) = 1 := by
      exact hΓ.le γ.property
    change boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ ∈ {ξ}
    rw [hγ]
    change boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) ξ ∈ {ξ}
    simp only [boundaryHomeomorph_refl, Homeomorph.refl_apply, Set.mem_singleton_iff, id_eq]
  · let _ : Nontrivial Γ := (Subgroup.nontrivial_iff_ne_bot Γ).mpr hΓ
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.center_ne_bot Γ)
    let c : Γ := z
    have hc : c ≠ 1 := by
      intro h
      exact hz (Subtype.ext h)
    obtain ⟨ξ, hξ⟩ := fixedPoints_boundaryHomeomorph_nonempty
      (c : Hyperboloid E ≃ᵢ Hyperboloid E) (hfree c hc)
    have hcard := fixedPoints_boundaryHomeomorph_encard_le_two
      (c : Hyperboloid E ≃ᵢ Hyperboloid E) (hfree c hc)
    refine ⟨ξ, (Set.encard_mono ?_).trans hcard⟩
    rintro _ ⟨γ, rfl⟩
    change boundaryHomeomorph (c : Hyperboloid E ≃ᵢ Hyperboloid E)
      (boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ) =
        boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ
    have hcomm : (c : Hyperboloid E ≃ᵢ Hyperboloid E) *
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) =
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) * (c : Hyperboloid E ≃ᵢ Hyperboloid E) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property γ).symm
    rw [← boundaryHomeomorph_mul_apply, hcomm, boundaryHomeomorph_mul_apply]
    exact congrArg (boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E)) hξ

end DifferentialGeometry.Hyperboloid
