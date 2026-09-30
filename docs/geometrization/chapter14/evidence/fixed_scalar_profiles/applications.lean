import DifferentialGeometry.Analysis.Calculus.FixedJointCutoffNetwork
import Mathlib.Tactic

set_option autoImplicit false
open Set DifferentialGeometry.Analysis Filter
open scoped Topology

namespace FixedProfileRegression

theorem corrected_inverse_affine_endpoints :
    descendingIntervalProfile 2 3 2 = 1 ∧ descendingIntervalProfile 2 3 3 = 0 ∧
      edgeCoordinateProfile (-8) = 1 ∧ edgeCoordinateProfile 9 = 0 ∧
      jointHeightProfile (1 / 5) = 0 ∧ jointHeightProfile (3 / 10) = 1 := by
  exact ⟨descendingIntervalProfile_one (by norm_num) le_rfl,
    descendingIntervalProfile_zero (by norm_num) le_rfl,
    (edgeProfiles_plateaus).1 (by norm_num),
    intervalPlateauProfile_zero_right (by norm_num) le_rfl,
    intervalPlateauProfile_zero_left (by norm_num) le_rfl,
    (edgeProfiles_plateaus).2 (by norm_num)⟩

private abbrev Space := EuclideanSpace ℝ (Fin 2)
private noncomputable def point (a b : ℝ) : Space := WithLp.toLp 2 (fun i => if i = 0 then a else b)
private noncomputable def u (_ : Unit) : Space →L[ℝ] ℝ := EuclideanSpace.proj 0
private noncomputable def v : Space →L[ℝ] ℝ := EuclideanSpace.proj 1
private def weights (_ : Unit) : ℝ := 2
private noncomputable def W (Δ : ℝ) := fixedJointCutoffNetwork Δ weights u v

private theorem profile_center_values : edgeCoordinateProfile 0 = 1 ∧
    edgeCoordinateProfile 10000 = 0 ∧ edgeHeightProfile 1 = 1 ∧ jointHeightProfile 1 = 1 :=
  ⟨(edgeProfiles_plateaus).1 (by norm_num),
    intervalPlateauProfile_zero_right (by norm_num) (by norm_num),
    descendingIntervalProfile_one (by norm_num) (by norm_num),
    (edgeProfiles_plateaus).2 (by norm_num)⟩

theorem fixed_joint_block_depends_on_actual_edge_sum :
    W 1 (point 0 1) none = WithLp.toLp 2 ((1 : ℝ), (1 : ℝ)) ∧
      W 1 (point 10000 1) none = 0 := by
  have hc0 := edgeSumProfile_zero (x := 0) (by norm_num)
  have hc1 := edgeSumProfile_one (x := 1) le_rfl
  constructor
  all_goals
    rw [W, fixedJointCutoffNetwork, jointCutoffNetwork_none]
    simp [jointEdgeCutoff, edgeCutoff, point, u, v,
      profile_center_values.1, profile_center_values.2.1, profile_center_values.2.2.1,
      profile_center_values.2.2.2, hc0, hc1]

theorem low_height_eliminates_nonsmooth_auxiliary_argument {x : ℝ} (hx : |x| < 1) :
    W 1 (point x (|x| / 10)) none = 0 ∧
      W 1 (point x (|x| / 10)) (some ()) = WithLp.toLp 2 (2 * x, (2 : ℝ)) := by
  have h := fixedJointCutoffNetwork_low_height (by norm_num : (0 : ℝ) < 1)
    weights u v (x := point x (|x| / 10)) (by simpa [v, point] using (show |x| / 10 < 3 / 20 by linarith))
  have hf : edgeCoordinateProfile x = 1 := (edgeProfiles_plateaus).1
    ⟨by linarith [(abs_lt.mp hx).1], by linarith [(abs_lt.mp hx).2]⟩
  refine ⟨h.1, ?_⟩
  simpa [W, weights, u, point, hf] using h.2 ()

theorem fixed_network_bounds_for_every_scale (Δ : ℝ) (hΔ : 1 ≤ Δ) (x : Space) :
    ‖W Δ x‖ ≤ 20 * Real.sqrt 2 * Δ ∧
      ‖fderiv ℝ (W Δ) x‖ ≤ Real.sqrt 2 * (2 + 800 * edgeProfileDerivativeBound ^ 3) ∧
      ‖fderiv ℝ (fderiv ℝ (W Δ)) x‖ ≤
        960 * Real.sqrt 2 * edgeProfileDerivativeBound ^ 3 / Δ := by
  have hu (i : Unit) : ‖u i‖ ≤ 1 := by
    apply (u i).opNorm_le_bound (by norm_num)
    intro y
    change ‖y (0 : Fin 2)‖ ≤ 1 * ‖y‖
    simpa using PiLp.norm_apply_le y (0 : Fin 2)
  have hv : ‖v‖ ≤ 1 := by
    apply v.opNorm_le_bound (by norm_num)
    intro y
    change ‖y (1 : Fin 2)‖ ≤ 1 * ‖y‖
    simpa using PiLp.norm_apply_le y (1 : Fin 2)
  have h := fixedJointCutoffNetwork_bounds hΔ weights (fun _ => by norm_num [weights]) u v hu hv x
  convert h using 1 <;> norm_num [W]
  all_goals ring_nf

end FixedProfileRegression
