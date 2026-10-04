import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic

/-!
# The one-sheet proximity budget (CGP07, arithmetic kernel)

Blueprint 207B, CGP07 (`thm:fibration-marked-base-one-sheet`, B:4176–4247). Under (OS)
`Ω ≥ 1`, `e ≤ Σ/1000`, `ε ≤ 1/(1000(Ω+1))`, every candidate `w` with `u_i(w)/R_i = a` satisfies
(SN) `|w - x| ≤ (2e + (25/12)(1+Ω) ε Σ) R_i < Σ R_i/100 < r_x/4` (with `r_x ≥ (9/20) Σ R_i`), so CFS13
puts it on the single graph `G_x`; moreover `ε < 1/(2Ω)` (the CGP06 margin) and the existence map
moves points by `(5/4)/1000 < 1/100`.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Collapse

theorem one_sheet_proximity_budget {Ω e ε S R rx : ℝ} (hΩ : 1 ≤ Ω) (hS : 0 < S) (hR : 0 < R)
    (he : e ≤ S / 1000) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (1000 * (Ω + 1)))
    (hrx : 9 / 20 * S * R ≤ rx) :
    (2 * e + 25 / 12 * (1 + Ω) * ε * S) * R < S * R / 100 ∧ S * R / 100 < rx / 4 ∧
      ε < 1 / (2 * Ω) := by
  have hΩ1 : 0 < Ω + 1 := by linarith
  have hεΩ : ε * (Ω + 1) ≤ 1 / 1000 := by
    rw [le_div_iff₀ (by positivity)] at hε
    nlinarith
  have h1 : 25 / 12 * (1 + Ω) * ε * S ≤ 25 / 12 * S / 1000 := by nlinarith
  refine ⟨?_, by nlinarith, ?_⟩
  · have : 2 * e + 25 / 12 * (1 + Ω) * ε * S < S / 100 := by nlinarith
    nlinarith
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith

end DifferentialGeometry.Geometry.Collapse
