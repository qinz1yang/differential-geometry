import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The affine height comparison: Taylor step (blueprint 207B, BCG02, (BCG02.b), B:8925–8935)

`abs_deriv_sub_slope_le`: along a segment of length `ℓ`, `|f'(0) - (f(ℓ) - f(0))/ℓ| ≤ K ℓ / 2` when
`|f''| ≤ K`; with `K = 2 R_a` (`‖∇²U_b‖ ≤ 2R_a` in reference units) this is the printed `R_a ℓ`.
The pointwise Riesz step of BCG02 is the existing FC15 kernel
`ContinuousLinearMap.norm_sub_le_of_common_unit_saturation`.
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

/-- (BCG02.b) Taylor integration along a minimizing segment of length `ℓ`. -/
theorem abs_deriv_sub_slope_le {f f' f'' : ℝ → ℝ} {K ℓ : ℝ} (hℓ : 0 < ℓ)
    (hf : ∀ t ∈ Icc 0 ℓ, HasDerivAt f (f' t) t) (hf' : ∀ t ∈ Icc 0 ℓ, HasDerivAt f' (f'' t) t)
    (hK : ∀ t ∈ Icc 0 ℓ, |f'' t| ≤ K) : |f' 0 - (f ℓ - f 0) / ℓ| ≤ K * ℓ / 2 := by
  have h0 : (0 : ℝ) ∈ Icc 0 ℓ := ⟨le_refl _, hℓ.le⟩
  have hℓm : ℓ ∈ Icc 0 ℓ := ⟨hℓ.le, le_refl _⟩
  -- `|f'(t) - f'(0)| ≤ K t` on the segment
  have hmv : ∀ t ∈ Icc 0 ℓ, ‖f' t - f' 0‖ ≤ K * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht => (hf' t ht).hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hK t (Ico_subset_Icc_self ht))
  have hcont : ∀ g : ℝ → ℝ, (∀ t ∈ Icc 0 ℓ, DifferentiableAt ℝ g t) → ContinuousOn g (Icc 0 ℓ) :=
    fun g hg t ht => (hg t ht).continuousAt.continuousWithinAt
  -- upper and lower comparison functions
  let up : ℝ → ℝ := fun t => f t - t * f' 0 + K / 2 * t ^ 2
  let lo : ℝ → ℝ := fun t => -(f t - t * f' 0) + K / 2 * t ^ 2
  have hup' : ∀ t ∈ Icc 0 ℓ, HasDerivAt up (f' t - f' 0 + K * t) t := by
    intro t ht
    have := ((hf t ht).sub ((hasDerivAt_id' t).mul_const (f' 0))).add
      ((hasDerivAt_pow 2 t).const_mul (K / 2))
    exact this.congr_deriv (by push_cast; ring)
  have hlo' : ∀ t ∈ Icc 0 ℓ, HasDerivAt lo (-(f' t - f' 0) + K * t) t := by
    intro t ht
    have := (((hf t ht).sub ((hasDerivAt_id' t).mul_const (f' 0))).neg).add
      ((hasDerivAt_pow 2 t).const_mul (K / 2))
    exact this.congr_deriv (by push_cast; ring)
  have hupmono : MonotoneOn up (Icc 0 ℓ) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 ℓ)
      (hcont up fun t ht => (hup' t ht).differentiableAt)
      (fun t ht => (hup' t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' := interior_subset ht
    have := hmv t ht'
    rw [Real.norm_eq_abs, sub_zero] at this
    linarith [(abs_le.mp this).1]
  have hlomono : MonotoneOn lo (Icc 0 ℓ) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 ℓ)
      (hcont lo fun t ht => (hlo' t ht).differentiableAt)
      (fun t ht => (hlo' t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' := interior_subset ht
    have := hmv t ht'
    rw [Real.norm_eq_abs, sub_zero] at this
    linarith [(abs_le.mp this).2]
  have hu := hupmono h0 hℓm hℓ.le
  have hl := hlomono h0 hℓm hℓ.le
  simp only [up, lo] at hu hl
  have hkey : |ℓ * f' 0 - (f ℓ - f 0)| ≤ K / 2 * ℓ ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hrw : f' 0 - (f ℓ - f 0) / ℓ = (ℓ * f' 0 - (f ℓ - f 0)) / ℓ := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]
  nlinarith

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
