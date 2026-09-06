import Mathlib.Analysis.Calculus.DerivativeTest

open Filter
open scoped Topology

theorem IsLocalMax.deriv_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hcont : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y hle hge
    exact le_antisymm hle hge
  have hzero : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  exact hpos.ne' hzero
