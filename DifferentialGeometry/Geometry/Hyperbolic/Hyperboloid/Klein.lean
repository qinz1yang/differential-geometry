import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Defs
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def kleinHomeomorph : Hyperboloid E ≃ₜ Metric.ball (0 : E) 1 :=
  spaceHomeomorph.trans Homeomorph.unitBall

theorem kleinHomeomorph_apply_coe (x : Hyperboloid E) :
    (kleinHomeomorph x : E) = x.time⁻¹ • x.space := by
  change (Homeomorph.unitBall x.space : E) = x.time⁻¹ • x.space
  rw [Homeomorph.unitBall_apply_coe, OpenPartialHomeomorph.univUnitBall_apply,
    ← x.time_eq_sqrt]

theorem kleinHomeomorph_symm_space (z : Metric.ball (0 : E) 1) :
    (kleinHomeomorph.symm z).space = (Real.sqrt (1 - ‖(z : E)‖ ^ 2))⁻¹ • (z : E) := by
  change Homeomorph.unitBall.symm z = _
  exact Homeomorph.unitBall_symm_apply z

theorem kleinHomeomorph_symm_time (z : Metric.ball (0 : E) 1) :
    (kleinHomeomorph.symm z).time = (Real.sqrt (1 - ‖(z : E)‖ ^ 2))⁻¹ := by
  have hz : ‖(z : E)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using z.property
  have hpos : 0 < 1 - ‖(z : E)‖ ^ 2 := by
    nlinarith [norm_nonneg (z : E)]
  have hroot := Real.sqrt_pos.mpr hpos
  apply (sq_eq_sq₀ (kleinHomeomorph.symm z).time_pos.le (inv_nonneg.mpr hroot.le)).mp
  rw [time_sq, kleinHomeomorph_symm_space, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hroot)]
  have ha := Real.sq_sqrt hpos.le
  field_simp
  nlinarith

end DifferentialGeometry.Hyperboloid
