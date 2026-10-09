import DifferentialGeometry.Geometry.Exponential.Flat.InvolutionAxis
import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanAxis

/-!
An actual free positive affine three-dimensional group with involutive linear parts has
an invariant unoriented axis. The linear image commutes, a nontranslation motion supplies
its nonzero screw displacement, and half-turn fixed-space uniqueness produces the signs.
No invariant direction, rational axis, or classification output is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_involutiveDeck_axis (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (htwo : ∀ γ : G, γ.val.linearIsometryEquiv ^ 2 = 1) :
    ∃ q : E3, q ≠ 0 ∧ ∀ γ : G, γ.val.linearIsometryEquiv q = q ∨
      γ.val.linearIsometryEquiv q = -q := by
  by_cases hex : ∃ g : G, g.val.linearIsometryEquiv ≠ 1
  · obtain ⟨g, hgn⟩ := hex
    have hg : g ≠ 1 := by
      intro he
      apply hgn
      rw [he]
      rfl
    obtain ⟨p, q, hp, hq⟩ := exists_affineAxis_point g.val
    have hq0 : q ≠ 0 := by
      intro hz
      exact hfree g hg p (by simpa only [hz, add_zero] using hp)
    refine ⟨q, hq0, ?_⟩
    intro γ
    let A := g.val.linearIsometryEquiv
    let B := γ.val.linearIsometryEquiv
    have hA : A ^ 2 = 1 := htwo g
    have hB : B ^ 2 = 1 := htwo γ
    have hAB : (A * B) ^ 2 = 1 := by
      have he := htwo (g * γ)
      change (affineLinearHom (g.val * γ.val)) ^ 2 = 1 at he
      rw [map_mul] at he
      exact he
    have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hA)
    have hBi : B⁻¹ = B := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hB)
    have hABi : (A * B)⁻¹ = A * B :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hAB)
    have hc : Commute A B := by
      change A * B = B * A
      calc
        A * B = (A * B)⁻¹ := hABi.symm
        _ = B⁻¹ * A⁻¹ := mul_inv_rev A B
        _ = B * A := by rw [hAi, hBi]
    exact commuting_involution_preserves_axis A B hA hgn (hpos g) hc q hq0 hq
  · let e := EuclideanSpace.basisFun (Fin 3) ℝ
    have hq0 : e 0 ≠ 0 := by
      intro hz
      have hn := e.norm_eq_one 0
      rw [hz, norm_zero] at hn
      norm_num at hn
    refine ⟨e 0, hq0, ?_⟩
    intro γ
    have he : γ.val.linearIsometryEquiv = 1 := by
      by_contra hn
      exact hex ⟨γ, hn⟩
    left
    rw [he]
    rfl

end DifferentialGeometry.Geometry.FlatSurface
