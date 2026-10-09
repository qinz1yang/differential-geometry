import DifferentialGeometry.Geometry.Exponential.Flat.SmallRotations
import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanAxis
import DifferentialGeometry.Geometry.Exponential.Flat.UniformDisplacement

/-!
# Near-axis separation of actual affine conjugates

The rotational norm is invariant under affine conjugation. The exact displacement formula
bounds the movement between conjugates at actual axis points. Uniform displacement derived from
the free cocompact discrete action then forces sufficiently near conjugate axes to agree.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

omit instFD in
theorem affineRotationNorm_conjugate (g k : V ≃ᵃⁱ[ℝ] V) :
    affineRotationNorm (k * g * k⁻¹) = affineRotationNorm g := by
  have hop : affineLinearOperator (k * g * k⁻¹) - ContinuousLinearMap.id ℝ V =
      (k.linearIsometryEquiv : V →L[ℝ] V).comp
        ((affineLinearOperator g - ContinuousLinearMap.id ℝ V).comp
          ((k⁻¹).linearIsometryEquiv : V →L[ℝ] V)) := by
    ext x
    change k.linearIsometryEquiv (g.linearIsometryEquiv ((k⁻¹).linearIsometryEquiv x)) - x =
      k.linearIsometryEquiv
        (g.linearIsometryEquiv ((k⁻¹).linearIsometryEquiv x) - (k⁻¹).linearIsometryEquiv x)
    rw [map_sub]
    have hid := congrArg (fun L : V ≃ₗᵢ[ℝ] V => L x) (affineLinearHom.map_mul k k⁻¹)
    simp only [mul_inv_cancel, map_one] at hid
    change x = k.linearIsometryEquiv ((k⁻¹).linearIsometryEquiv x) at hid
    rw [← hid]
  unfold affineRotationNorm
  rw [hop, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

omit instFD in
theorem affine_axis_displacement_formula (g : V ≃ᵃⁱ[ℝ] V) {p q : V}
    (hp : g p = p + q) (x : V) :
    g x - x = q + (g.linearIsometryEquiv (x - p) - (x - p)) := by
  have hx := affineIsometry_apply g x
  have hp' := affineIsometry_apply g p
  rw [hp] at hp'
  rw [map_sub]
  linear_combination (norm := abel) hx - hp'

omit instFD in
theorem affineRotationNorm_le_two (g : V ≃ᵃⁱ[ℝ] V) : affineRotationNorm g ≤ 2 := by
  have hlin : ‖affineLinearOperator g‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [affineLinearOperator]
  have hid : ‖ContinuousLinearMap.id ℝ V‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  exact (norm_sub_le _ _).trans (by linarith)

omit instFD in
theorem affine_conjugate_axis_movement (g k : V ≃ᵃⁱ[ℝ] V) {p q p' : V}
    (hp : g p = p + q) (hp' : (k * g * k⁻¹) p' = p' + k.linearIsometryEquiv q) :
    ‖(k * g * k⁻¹) p - g p‖ ≤
      affineRotationNorm g * ‖p - p'‖ + affineRotationNorm k * ‖q‖ := by
  have hformula := affine_axis_displacement_formula (k * g * k⁻¹) hp' p
  have hval : (k * g * k⁻¹) p - g p =
      (affineLinearOperator (k * g * k⁻¹) - ContinuousLinearMap.id ℝ V) (p - p') +
        (affineLinearOperator k - ContinuousLinearMap.id ℝ V) q := by
    change (k * g * k⁻¹) p - g p =
      ((k * g * k⁻¹).linearIsometryEquiv (p - p') - (p - p')) +
        (k.linearIsometryEquiv q - q)
    rw [hp]
    linear_combination (norm := abel) hformula
  rw [hval]
  refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
    (ContinuousLinearMap.le_opNorm _ _)) |>.trans ?_
  rw [← affineRotationNorm, ← affineRotationNorm, affineRotationNorm_conjugate]

theorem exists_near_conjugate_axis_separation (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ a : G, a ≠ 1 → ∀ x : V, (a : V ≃ᵃⁱ[ℝ] V) x ≠ x)
    (g : G) (q : V) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ k : G,
      affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) < η → ∀ p p' : V,
      (g : V ≃ᵃⁱ[ℝ] V) p = p + q →
      ((k * g * k⁻¹ : G) : V ≃ᵃⁱ[ℝ] V) p' =
        p' + (k : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv q →
      ‖p - p'‖ < c → k * g * k⁻¹ = g := by
  obtain ⟨m, hm, hmin⟩ := exists_uniform_affine_displacement G hdisc hcov hfree
  refine ⟨m / (4 * (‖q‖ + 1)), m / 8, by positivity, by positivity, ?_⟩
  intro k hk p p' hp hp' hdist
  have hbound := affine_conjugate_axis_movement (g : V ≃ᵃⁱ[ℝ] V)
    (k : V ≃ᵃⁱ[ℝ] V) hp hp'
  change ‖((k * g * k⁻¹ : G) : V ≃ᵃⁱ[ℝ] V) p - (g : V ≃ᵃⁱ[ℝ] V) p‖ ≤
    affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) * ‖p - p'‖ +
      affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) * ‖q‖ at hbound
  have hrot := affineRotationNorm_le_two (g : V ≃ᵃⁱ[ℝ] V)
  have hrotk : 0 ≤ affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) := norm_nonneg _
  have hkq : affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) * ‖q‖ < m / 4 := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < 4 * (‖q‖ + 1))).mp hk
    nlinarith [norm_nonneg q]
  have hsmall : ‖((k * g * k⁻¹ : G) : V ≃ᵃⁱ[ℝ] V) p - (g : V ≃ᵃⁱ[ℝ] V) p‖ < m := by
    have hproduct := mul_le_mul_of_nonneg_right hrot (norm_nonneg (p - p'))
    nlinarith
  by_contra hne
  have hne' : (k * g * k⁻¹) * g⁻¹ ≠ 1 := by
    intro heq
    exact hne (mul_inv_eq_one.mp heq)
  have hh := hmin ((k * g * k⁻¹) * g⁻¹) hne' ((g : V ≃ᵃⁱ[ℝ] V) p)
  change m ≤ ‖((k * g * k⁻¹ : G) : V ≃ᵃⁱ[ℝ] V)
    ((g : V ≃ᵃⁱ[ℝ] V).symm ((g : V ≃ᵃⁱ[ℝ] V) p)) - (g : V ≃ᵃⁱ[ℝ] V) p‖ at hh
  rw [AffineIsometryEquiv.symm_apply_apply] at hh
  exact (not_lt_of_ge hh) hsmall

end DifferentialGeometry.Geometry.FlatSurface
