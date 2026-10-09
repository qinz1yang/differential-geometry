import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {v : E} (hv : ‖v‖ = 1)

theorem dist_stereoInvFun_sq (u w : (ℝ ∙ v)ᗮ) :
    dist (stereoInvFun hv u) (stereoInvFun hv w) ^ 2 =
      16 * dist u w ^ 2 / ((‖u‖ ^ 2 + 4) * (‖w‖ ^ 2 + 4)) := by
  have hu : inner ℝ (u : E) v = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.property
  have hw : inner ℝ v (w : E) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  have hnu : ‖(stereoInvFun hv u : E)‖ = 1 := norm_eq_of_mem_sphere _
  have hnw : ‖(stereoInvFun hv w : E)‖ = 1 := norm_eq_of_mem_sphere _
  have hdu : ‖u‖ ^ 2 + 4 ≠ 0 := by positivity
  have hdw : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  change dist (stereoInvFun hv u : E) (stereoInvFun hv w : E) ^ 2 = _
  rw [dist_eq_norm, norm_sub_sq_real, hnu, hnw, stereoInvFun_apply, stereoInvFun_apply]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    hu, hw, real_inner_self_eq_norm_sq, hv, dist_eq_norm, norm_sub_sq_real, Submodule.coe_inner]
  field_simp [hdu, hdw]
  ring

theorem dist_stereoInvFun_pole_sq (w : (ℝ ∙ v)ᗮ) :
    dist (stereoInvFun hv w : E) v ^ 2 = 16 / (‖w‖ ^ 2 + 4) := by
  have hw : inner ℝ (w : E) v = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.property
  have hnw : ‖(stereoInvFun hv w : E)‖ = 1 := norm_eq_of_mem_sphere _
  have hdw : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  rw [dist_eq_norm, norm_sub_sq_real, hnw, hv, stereoInvFun_apply]
  simp only [real_inner_smul_left, inner_add_left, hw, real_inner_self_eq_norm_sq, hv]
  field_simp [hdw]
  ring

theorem dist_stereoInvFun_neg_pole_sq (w : (ℝ ∙ v)ᗮ) :
    dist (stereoInvFun hv w : E) (-v) ^ 2 =
      4 * ‖w‖ ^ 2 / (‖w‖ ^ 2 + 4) := by
  have hzero : (stereoInvFun hv (0 : (ℝ ∙ v)ᗮ) : E) = -v := by
    simp [stereoInvFun_apply, smul_smul]
  have hdw : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  calc
    dist (stereoInvFun hv w : E) (-v) ^ 2 =
        dist (stereoInvFun hv w) (stereoInvFun hv 0) ^ 2 := by rw [← hzero]; rfl
    _ = 16 * dist w 0 ^ 2 / ((‖w‖ ^ 2 + 4) * (‖(0 : (ℝ ∙ v)ᗮ)‖ ^ 2 + 4)) :=
      dist_stereoInvFun_sq hv w 0
    _ = 4 * ‖w‖ ^ 2 / (‖w‖ ^ 2 + 4) := by
      simp only [dist_zero_right, norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_add]
      field_simp [hdw]
      ring

end DifferentialGeometry
