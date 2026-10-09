import DifferentialGeometry.Analysis.Calculus.EdgeLineSection
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Consumer of EGP05's section kernel: the identity line with zero height

On `X = ℝ` with `j = η = id`, height `t = 0`, `Δ = 1`, `μ = 1/400`, the section over `[-8.5, 8.5]` exists,
with `η ∘ s = id` and zero height.
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Analysis

theorem identity_line_edge_section :
    ∃ s : ℝ → ℝ, ContinuousOn s (Icc (-(17 / 2 * 1)) (17 / 2 * 1)) ∧
      ∀ a ∈ Icc (-(17 / 2 * 1)) (17 / 2 * 1),
        id (s a) = a ∧ 0 ≤ (fun _ : ℝ => (0 : ℝ)) (s a) ∧
          (fun _ : ℝ => (0 : ℝ)) (s a) < 1 / 100 ∧ s a ∈ (univ : Set ℝ) :=
  exists_edge_cloud_section id id (fun _ => 0) univ (μ := 1 / 400) one_pos (by norm_num)
    continuousOn_id continuousOn_id (fun a _ => by simp) (by norm_num) (by norm_num)
    (fun a _ => by norm_num)

end DifferentialGeometry.Analysis
