import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace GC.MetricGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_coordinate_sub_lt_of_marker {u v : E} {ζ ε A : ℝ}
    (hε : 0 < ε) (hεone : ε < 1) (hu : ‖u‖ ≤ A)
    (hmarker : |ζ - 1| < ε) (hvector : ‖ζ • v - u‖ < ε) :
    1 - ε < ζ ∧ ‖v - u‖ < (1 + A) * ε / (1 - ε) := by
  have hζ : 1 - ε < ζ := by linarith [(abs_lt.mp hmarker).1]
  have hζ0 : 0 < ζ := by linarith
  have hA : 0 ≤ A := (norm_nonneg u).trans hu
  have heq : ζ • (v - u) = (ζ • v - u) + (1 - ζ) • u := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  have hn := norm_add_le (ζ • v - u) ((1 - ζ) • u)
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos hζ0,
    norm_smul, Real.norm_eq_abs, abs_sub_comm 1 ζ] at hn
  have hb := mul_le_mul hmarker.le hu (norm_nonneg u) hε.le
  refine ⟨hζ, (lt_div_iff₀ (by linarith : 0 < 1 - ε)).mpr ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hζ.le (norm_nonneg (v - u))]

theorem norm_coordinate_sub_lt_of_block_dist {u v : E} {ζ ε A : ℝ}
    (hε : 0 < ε) (hεone : ε < 1) (hu : ‖u‖ ≤ A)
    (hblock : dist (WithLp.toLp 2 (ζ • v, ζ)) (WithLp.toLp 2 (u, (1 : ℝ))) < ε) :
    1 - ε < ζ ∧ ‖v - u‖ < (1 + A) * ε / (1 - ε) := by
  apply norm_coordinate_sub_lt_of_marker hε hεone hu
  · exact (WithLp.dist_snd_le _ _).trans_lt hblock
  · simpa only [WithLp.toLp_fst, dist_eq_norm] using (WithLp.dist_fst_le _ _).trans_lt hblock

end GC.MetricGeometry
