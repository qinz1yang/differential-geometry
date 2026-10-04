import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Whole boundary support lists and their original domains (blueprint 207B, BCG01, B:8727–8820)

Row-local metric kernels:
* `reference_radius_lt_two_mul` — a reference domain `B(p_a, C_a R_a)` meeting a point of scale
  `ρ < r_∂` has `R_a < 2 r_∂` (slow variation, `Λ C_a ≤ 1/2`).
* `dist_lt_of_mem_reference_ball` — with `C_a ≤ .95 L`, `R_a < 2 r_∂`, `r_∂ < 1/(1000L)` the domain has
  diameter `< 1/250`.
* `eq_of_supports_meet_small_set` — sets with mutual separation `δ` cannot both meet a set of diameter
  `< δ` (so at most ONE boundary support meets `D_a`, using BCP03's separation `≥ 1`).
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

variable {X : Type*} [PseudoMetricSpace X]

/-- BCG01: `R_a < 2 r_∂` from slow variation of the scale on the reference domain. -/
theorem reference_radius_lt_two_mul {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ) {p x : X}
    {C r : ℝ} (hp : 0 ≤ ρ p) (hsmall : (Λ : ℝ) * C ≤ 1 / 2) (hx : dist x p ≤ C * ρ p)
    (hxr : ρ x < r) : ρ p < 2 * r := by
  have h1 := hρ.dist_le_mul p x
  rw [Real.dist_eq, dist_comm] at h1
  have h2 : (Λ : ℝ) * dist x p ≤ (Λ : ℝ) * (C * ρ p) := mul_le_mul_of_nonneg_left hx Λ.coe_nonneg
  have h3 : (Λ : ℝ) * C * ρ p ≤ 1 / 2 * ρ p := mul_le_mul_of_nonneg_right hsmall hp
  have h4 : ρ p - ρ x ≤ |ρ p - ρ x| := le_abs_self _
  nlinarith

/-- BCG01: the original reference domain has diameter `< 4 L r_∂ < 1/250`. -/
theorem dist_lt_of_mem_reference_ball {p x y : X} {C R L r : ℝ} (hC : C ≤ 95 / 100 * L)
    (hL : 0 < L) (hR0 : 0 ≤ R) (hR : R < 2 * r) (hr : r * (1000 * L) < 1)
    (hx : dist x p < C * R) (hy : dist y p < C * R) : dist x y < 1 / 250 := by
  have htri := dist_triangle_right x y p
  have h1 : C * R ≤ 95 / 100 * L * R := mul_le_mul_of_nonneg_right hC hR0
  have h2 : L * R < L * (2 * r) := mul_lt_mul_of_pos_left hR hL
  nlinarith

/-- BCG01: two supports with mutual separation `δ` cannot both meet a set of diameter `< δ`. -/
theorem eq_of_supports_meet_small_set {ι : Type*} (S : ι → Set X) (D : Set X) {δ : ℝ}
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, δ ≤ dist x y)
    (hD : ∀ x ∈ D, ∀ y ∈ D, dist x y < δ) {i j : ι} (hi : (S i ∩ D).Nonempty)
    (hj : (S j ∩ D).Nonempty) : i = j := by
  by_contra hij
  obtain ⟨x, hxS, hxD⟩ := hi
  obtain ⟨y, hyS, hyD⟩ := hj
  exact absurd (hD x hxD y hyD) (not_lt.mpr (hsep i j hij x hxS y hyS))

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
