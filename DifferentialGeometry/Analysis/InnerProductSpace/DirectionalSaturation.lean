import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped InnerProductSpace

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sub_le_sqrt_of_unit_saturation {v w : E} {ε : ℝ}
    (hε : 0 ≤ ε) (hv : ‖v‖ ≤ 1 + ε) (hw : ‖w‖ = 1)
    (hi : 1 - ε ≤ ⟪v, w⟫_ℝ) : ‖v - w‖ ≤ Real.sqrt (4 * ε + ε ^ 2) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  have hn := norm_sub_sq_real v w
  rw [hw] at hn
  nlinarith [norm_nonneg v]

end InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem norm_sub_le_of_common_unit_saturation (f g : StrongDual ℝ E) {ε : ℝ}
    (hε : 0 ≤ ε) (hf : ‖f‖ ≤ 1 + ε) (hg : ‖g‖ ≤ 1 + ε)
    (w : E) (hw : ‖w‖ = 1) (hfw : 1 - ε ≤ f w) (hgw : 1 - ε ≤ g w) :
    ‖f - g‖ ≤ 2 * Real.sqrt (4 * ε + ε ^ 2) := by
  let v := (InnerProductSpace.toDual ℝ E).symm f
  let u := (InnerProductSpace.toDual ℝ E).symm g
  have hv : ‖v‖ ≤ 1 + ε := by simpa only [v, LinearIsometryEquiv.norm_map] using hf
  have hu : ‖u‖ ≤ 1 + ε := by simpa only [u, LinearIsometryEquiv.norm_map] using hg
  have hvw : ⟪v, w⟫_ℝ = f w := by
    exact InnerProductSpace.toDual_symm_apply
  have huw : ⟪u, w⟫_ℝ = g w := by
    exact InnerProductSpace.toDual_symm_apply
  have h1 := InnerProductSpace.norm_sub_le_sqrt_of_unit_saturation hε hv hw (by rwa [hvw])
  have h2 := InnerProductSpace.norm_sub_le_sqrt_of_unit_saturation hε hu hw (by rwa [huw])
  have ht := norm_sub_le (v - w) (u - w)
  rw [sub_sub_sub_cancel_right] at ht
  have he : ‖v - u‖ = ‖f - g‖ := by rw [← map_sub]; exact LinearIsometryEquiv.norm_map _ _
  rw [he] at ht
  linarith

end ContinuousLinearMap
