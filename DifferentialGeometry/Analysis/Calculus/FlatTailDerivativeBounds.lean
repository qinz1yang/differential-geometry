import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem hasCompactSupport_fderiv_of_constant_tails {f : ℝ → H} {a b : ℝ} {cl cr : H}
    (hl : ∀ x ≤ a, f x = cl) (hr : ∀ x, b ≤ x → f x = cr) :
    HasCompactSupport (fderiv ℝ f) := by
  apply (isCompact_Icc (a := a) (b := b)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hout
  rcases not_and_or.mp hout with hlo | hhi
  · have hloc : f =ᶠ[𝓝 x] fun _ => cl := by
      filter_upwards [Iio_mem_nhds (lt_of_not_ge hlo)] with y hy
      exact hl y hy.le
    exact hx (by rw [hloc.fderiv_eq, fderiv_const_apply])
  · have hloc : f =ᶠ[𝓝 x] fun _ => cr := by
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge hhi)] with y hy
      exact hr y hy.le
    exact hx (by rw [hloc.fderiv_eq, fderiv_const_apply])

theorem exists_derivative_bounds_of_constant_tails {f : ℝ → H}
    (hf : ContDiff ℝ 2 f) {a b : ℝ} {cl cr : H}
    (hl : ∀ x ≤ a, f x = cl) (hr : ∀ x, b ≤ x → f x = cr) :
    ∃ P : ℝ, 1 ≤ P ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ P) ∧
      ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDD : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hD.fderiv_right (by norm_num)
  have hs := hasCompactSupport_fderiv_of_constant_tails hl hr
  obtain ⟨A, hA⟩ := hD.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hs.comp_left norm_zero)
  obtain ⟨B, hB⟩ := hDD.continuous.norm.bddAbove_range_of_hasCompactSupport
    ((hs.fderiv ℝ).comp_left norm_zero)
  refine ⟨max 1 (max A B), le_max_left _ _, ?_, ?_⟩
  · exact fun x => (hA (mem_range_self x)).trans ((le_max_left A B).trans (le_max_right _ _))
  · exact fun x => (hB (mem_range_self x)).trans ((le_max_right A B).trans (le_max_right _ _))

end DifferentialGeometry.Analysis
