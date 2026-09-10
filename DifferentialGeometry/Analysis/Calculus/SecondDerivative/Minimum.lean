import Mathlib.Analysis.Calculus.DerivativeTest



open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem second_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hn : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hy hz
    exact le_antisymm hz hy
  have hd : deriv f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [heq.deriv] with y hy
    simpa only [deriv_const] using hy
  have hdd : deriv (deriv f) x = 0 := by
    simpa only [deriv_const] using hd.deriv_eq
  linarith

end DifferentialGeometry.Analysis
