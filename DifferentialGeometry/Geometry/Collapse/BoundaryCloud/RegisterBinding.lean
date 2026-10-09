import DifferentialGeometry.Geometry.Collapse.BoundaryRegister
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.RowConsequences

/-!
# BCG kernels with the constants of the boundary register (blueprint 207B, B:8699–9470, B:10476)

The physical parameter `r_∂ = R.physicalScale`, the long length `L = 10⁶Δ` and `c₃ = R.stage.c 2`
of W4-PBR's `BoundaryRegister` (BBR01, (BRegPhysical)) feed the row-local kernels:
* `BoundaryRegister.subsingleton_supports_meeting_reference_ball` — BCG01 with `r_∂ < 1/(1000L)`.
* `BoundaryRegister.boundary_marker_eq_one_of_near_band_point` — BCG05 with `r_∂ < 10⁻⁴`.
* `BoundaryRegister.block_error_lt` — BCG04: the block error is `< ε_∂ = 20 c₃ r_∂ < 10⁻⁶`.
* `BoundaryRegister.abs_height_sub_forty_lt_thousandth` — BCG06 frontier window with that `ε_∂`.
-/

set_option autoImplicit false
open Set Metric

namespace DifferentialGeometry.Geometry.Collapse.BoundaryRegister

open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Collapse.BoundaryCloud

variable {D : BoundaryEarlyData} {T : BoundaryThresholds D}

/-- BCG01 with the register's `r_∂` and `L = 10⁶Δ`: at most one closed boundary support meets a
reference domain `B(p_a, C_a R_a)` with `C_a ≤ .95L`, `R_a < 2 r_∂`. -/
theorem subsingleton_supports_meeting_reference_ball (R : BoundaryRegister D T)
    {X ι : Type*} [PseudoMetricSpace X] (S : ι → Set X)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, 1 ≤ dist x y) {p : X} {C Ra : ℝ}
    (hC : C ≤ 95 / 100 * closedLongLength R.later.excl) (hRa0 : 0 ≤ Ra)
    (hRa : Ra < 2 * R.physicalScale) :
    {i | (S i ∩ ball p (C * Ra)).Nonempty}.Subsingleton := by
  have hL : 0 < closedLongLength R.later.excl := by
    unfold closedLongLength
    exact mul_pos (by norm_num) R.later.Δ_pos
  have hr : R.physicalScale * (1000 * closedLongLength R.later.excl) < 1 := by
    have h := R.physicalScale_lt_long
    rw [lt_div_iff₀ (by positivity)] at h
    exact h
  exact BoundaryCloud.subsingleton_supports_meeting_reference_ball S hsep hC hL hRa0 hRa hr

/-- BCG05 with the register's `r_∂ < 10⁻⁴`: a core preimage whose physical block is within `r_∂` of
the block at a band height `32 ≤ t ≤ 78` has marker exactly one and height in `(31, 79)`. -/
theorem boundary_marker_eq_one_of_near_band_point (R : BoundaryRegister D T) {s t : ℝ}
    (ht : t ∈ Icc (32 : ℝ) 78) (hnear : ‖boundaryBlock s - boundaryBlock t‖ < R.physicalScale) :
    s ∈ Ioo (31 : ℝ) 79 ∧ boundaryProfile s = 1 := by
  have h := R.physicalScale_lt_small
  exact BoundaryCloud.boundary_marker_eq_one_of_near_band_point ht hnear
    (by norm_num at h ⊢; exact h)

/-- BCG04 with the register's `c₃` and `r_∂`: the whole-block error is `< ε_∂ = 20 c₃ r_∂ < 10⁻⁶`. -/
theorem block_error_lt (R : BoundaryRegister D T) {K : Type*} [NormedAddCommGroup K] {a A : K}
    {ρp : ℝ} (hzero : 20 * R.physicalScale < ρp → a = 0 ∧ A = 0)
    (herr : ‖a - A‖ < R.stage.c 2 * ρp) : ‖a - A‖ < 1 / 1000000 := by
  have h := norm_sub_lt_of_isolation (R.stage.c_pos 2) R.physicalScale_pos hzero herr
  have h2 := R.twenty_c₃_mul_lt
  norm_num at h2 ⊢
  linarith

/-- BCG06 with the register's `ε_∂`: on the internal frontier `u_b = 40 v_b`, `v_b ≥ .9`, every
point of the full preimage has `|η_b - 40| < .001`. -/
theorem abs_height_sub_forty_lt_thousandth (R : BoundaryRegister D T) {u v η ζ : ℝ}
    (hu : |u - η * ζ| < 20 * R.stage.c 2 * R.physicalScale)
    (hv : |v - ζ| < 20 * R.stage.c 2 * R.physicalScale) (hv9 : 9 / 10 ≤ v) (heq : u = 40 * v) :
    |η - 40| < 1 / 1000 := by
  have h := R.twenty_c₃_mul_lt
  exact BoundaryCloud.abs_height_sub_forty_lt_thousandth hu hv hv9 (by norm_num at h ⊢; linarith)
    heq

end DifferentialGeometry.Geometry.Collapse.BoundaryRegister
