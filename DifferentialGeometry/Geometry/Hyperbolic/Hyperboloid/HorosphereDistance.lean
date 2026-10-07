import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric

namespace DifferentialGeometry.Hyperboloid

theorem cosh_dist_northPoleHorosphereHomeomorph_symm
    (h k : ℝ) (hh : 0 < h) (hk : 0 < k) (z w : ℂ) :
    Real.cosh (dist
      ((northPoleHorosphereHomeomorph h hh).symm z).val
      ((northPoleHorosphereHomeomorph k hk).symm w).val) =
      (h / k + k / h) / 2 + h * k * dist z w ^ 2 / 8 := by
  have hz := northPoleHorosphereHomeomorph_symm_coordinates h hh z
  have hw := northPoleHorosphereHomeomorph_symm_coordinates k hk w
  have hzt := congrArg Prod.fst hz
  have hzs := congrArg Prod.snd hz
  have hwt := congrArg Prod.fst hw
  have hws := congrArg Prod.snd hw
  dsimp only at hzt hzs hwt hws
  rw [cosh_dist, hzt, hzs, hwt, hws]
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, Real.inner_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  field_simp
  ring

end DifferentialGeometry.Hyperboloid
