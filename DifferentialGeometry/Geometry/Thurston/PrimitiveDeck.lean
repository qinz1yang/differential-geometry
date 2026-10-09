import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Primitive integer periods of an actual affine deck coordinate

The integer displacement character is constructed from the given invariant covector.
Its cyclic image has a nonzero generator because the actual translations span. Rescaling
by that generator gives every integer period while preserving the same hyperplane kernel.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V] [instR : NormedSpace ℝ V]

theorem exists_primitive_deck_covector
    (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) (ell : V →L[ℝ] ℝ)
    (hel : Function.Surjective ell)
    (hlin : ∀ (γ : G) (v : V), ell ((γ : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv v) = ell v)
    (hint : ∀ γ : G, ∃ m : ℤ, ell ((γ : V ≃ᵃⁱ[ℝ] V) 0) = m)
    (hspan : Submodule.span ℝ (affineTranslationModule G : Set V) = ⊤) :
    ∃ a : ℝ, a ≠ 0 ∧ Function.Surjective (a • ell) ∧
      (a • ell).ker = ell.ker ∧
      (∀ γ : G, ∃ m : ℤ, (a • ell) ((γ : V ≃ᵃⁱ[ℝ] V) 0) = m) ∧
      ∀ m : ℤ, ∃ γ : G, (a • ell) ((γ : V ≃ᵃⁱ[ℝ] V) 0) = m := by
  classical
  choose z hz using hint
  have hmul (g h : G) : z (g * h) = z g + z h := by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_add, ← hz, ← hz, ← hz]
    change ell ((g : V ≃ᵃⁱ[ℝ] V) ((h : V ≃ᵃⁱ[ℝ] V) 0)) = _
    rw [affineIsometry_apply, map_add, hlin]
    exact add_comm _ _
  let χ : G →* Multiplicative ℤ :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by
        change z 1 = 0
        apply Int.cast_injective (α := ℝ)
        simpa using (hz 1).symm
      map_mul' := hmul }
  have hχ (g : G) : (χ g).toAdd = z g := rfl
  obtain ⟨r, hr⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic χ.range)
  obtain ⟨g₀, hg₀⟩ := χ.rangeRestrict_surjective r
  have hgen (g : G) : ∃ m : ℤ, z g = m * z g₀ := by
    have hg : χ.rangeRestrict g ∈ Subgroup.zpowers r := by rw [hr]; trivial
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hg₀] at hm
    have he := congrArg (fun t : χ.range => Multiplicative.toAdd t.val) hm
    change (χ g₀ ^ m).toAdd = (χ g).toAdd at he
    rw [toAdd_zpow, hχ, hχ] at he
    exact ⟨m, by simpa only [zsmul_eq_mul, Int.cast_id] using he.symm⟩
  have hz₀ : z g₀ ≠ 0 := by
    intro hzero
    have hall (g : G) : ell ((g : V ≃ᵃⁱ[ℝ] V) 0) = 0 := by
      obtain ⟨m, hm⟩ := hgen g
      rw [hz, hm, hzero, mul_zero, Int.cast_zero]
    have hk : Submodule.span ℝ (affineTranslationModule G : Set V) ≤ ell.ker := by
      apply Submodule.span_le.mpr
      intro v hv
      have he := hall ⟨AffineIsometryEquiv.constVAdd ℝ V v, hv⟩
      simpa using he
    rw [hspan] at hk
    obtain ⟨v, hv⟩ := hel 1
    have he : ell v = 0 := hk (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ V))
    rw [hv] at he
    exact one_ne_zero he
  have hs : (z g₀ : ℝ) ≠ 0 := by exact_mod_cast hz₀
  refine ⟨(z g₀ : ℝ)⁻¹, inv_ne_zero hs, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hel ((z g₀ : ℝ) * y)
    refine ⟨v, ?_⟩
    simp only [smul_apply, smul_eq_mul, hv]
    field_simp
  · ext v
    change (z g₀ : ℝ)⁻¹ * ell v = 0 ↔ ell v = 0
    exact mul_eq_zero.trans (or_iff_right (inv_ne_zero hs))
  · intro g
    obtain ⟨m, hm⟩ := hgen g
    refine ⟨m, ?_⟩
    simp only [smul_apply, smul_eq_mul, hz, hm, Int.cast_mul]
    field_simp
  · intro m
    refine ⟨g₀ ^ m, ?_⟩
    have he := congrArg Multiplicative.toAdd (χ.map_zpow g₀ m)
    rw [toAdd_zpow, hχ, hχ] at he
    have hm : z (g₀ ^ m) = m * z g₀ := by
      simpa only [zsmul_eq_mul, Int.cast_id] using he
    simp only [smul_apply, smul_eq_mul, hz, hm, Int.cast_mul]
    field_simp

end DifferentialGeometry.Geometry.FlatSurface
