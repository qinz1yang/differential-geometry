import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp



namespace DifferentialGeometry.Analysis



theorem deriv_diagonal {F : ℝ × ℝ → ℝ} {t : ℝ} (hF : DifferentiableAt ℝ F (t, t)) :
    deriv (fun s => F (s, s)) t =
      deriv (fun s => F (s, t)) t + deriv (fun s => F (t, s)) t := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (s, s)) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t))
  have hl := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (s, t)) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t))
  have hr := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (t, s)) t
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t))
  dsimp only [Function.comp_def] at hd hl hr
  rw [hd.deriv, hl.deriv, hr.deriv, show ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) by ext <;> simp,
    map_add]

end DifferentialGeometry.Analysis
