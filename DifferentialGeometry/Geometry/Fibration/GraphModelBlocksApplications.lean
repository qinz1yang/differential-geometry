import DifferentialGeometry.Geometry.Fibration.GraphModelBlocks

/-!
# Consumers of the shared model blocks

* `sgpModelBlock_eq_of_plateau`: on the plateau `|λ| ≤ 8sℓ` the slim model block is `(λ, s)` —
  the identity block of SGP04's graph (EGP06's listed slim block at a point of the slim plateau).
* `zeroModelBlock_eq_zero_of_le`: the zero model block vanishes for `λ ≤ s/5` (zero core side).
* `sgpModelBlock_pointwise_c1_sub_le`: the directional `C¹` composition error of the slim model
  block, `200(P + 1)θ`, as used on a manifold source.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

/-- On the plateau `|λ| ≤ 8sℓ` the slim model block is `(λ, s)`. -/
theorem sgpModelBlock_eq_of_plateau {ℓ s x : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (hx : |x| ≤ 8 * (s * ℓ)) : sgpModelBlock ℓ s x = WithLp.toLp 2 (x, s) := by
  have h1 : slimCutoffProfile_LC87 (x / (s * ℓ)) = 1 := by
    have h := sgpProfile_eq_one (ℓ := s * ℓ) (z := x) (mul_pos hs hℓ) hx
    exact h
  rw [sgpModelBlock_apply, h1, one_mul, mul_one]

/-- The zero model block vanishes for `λ ≤ s/5`. -/
theorem zeroModelBlock_eq_zero_of_le {s x : ℝ} (hs : 0 < s) (hx : x ≤ s / 5) :
    zeroModelBlock s x = 0 := by
  have h : s⁻¹ * x ≤ 1 / 5 := by
    rw [inv_mul_le_iff₀ hs]
    linarith
  rw [zeroModelBlock_apply,
    annularCutoff_eq_zero_of_le (fun t ht => cutoffProfile_eq_zero ht) h, zero_mul, mul_zero]
  rfl

/-- The directional `C¹` composition error of the slim model block (`ℓ ≥ 1`, `s ≥ 99/100`). -/
theorem sgpModelBlock_pointwise_c1_sub_le {ℓ s θ u v du dv : ℝ} (hℓ : 1 ≤ ℓ)
    (hs : 99 / 100 ≤ s) (hθ1 : θ ≤ 1) (huv : |u - v| ≤ θ) (hd : |du - dv| ≤ θ)
    (hdv : |dv| ≤ 2) :
    ‖sgpModelBlock ℓ s u - sgpModelBlock ℓ s v‖ ≤ 200 * (sgpProfileBound + 1) * θ ∧
      ‖fderiv ℝ (sgpModelBlock ℓ s) u du - fderiv ℝ (sgpModelBlock ℓ s) v dv‖ ≤
        200 * (sgpProfileBound + 1) * θ := by
  have hP := sgpProfileBound_spec.1
  have h := modelBlock_pointwise_c1_sub_le ((contDiff_sgpModelBlock ℓ s).of_le (by simp))
    (by linarith : (0 : ℝ) ≤ 50 * (sgpProfileBound + 1))
    (fun y => (sgpModelBlock_derivative_bounds hℓ hs y).1)
    (fun y => (sgpModelBlock_derivative_bounds hℓ hs y).2) hθ1 huv hd hdv
  have e : 4 * (50 * (sgpProfileBound + 1)) * θ = 200 * (sgpProfileBound + 1) * θ := by ring
  rw [e] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
