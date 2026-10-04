import DifferentialGeometry.Analysis.Calculus.MonotoneLineSection

/-!
# The exact edge section for cloud coverage (EGP05, kernel form)

Blueprint `master207B.tex`, EGP05 (`lem:fibration-edge-cloud-section`, lines 5042–5086). Along the
core line `a ↦ j(a, z₀)` of LFR28's buffered product embedding on `[-8.9 Δ, 8.9 Δ]`, the tangential
coordinate `η ∘ j` has positive derivative, its endpoint values are within `2 μ Δ < Δ/100` of `± 8.9 Δ`,
and along the whole segment the height satisfies `0 ≤ t < Δ/100` and the points lie in the stated ball
`B` (the radius-`10 Δ R_i` ball). Then there is a continuous section `s` over `[-8.5 Δ, 8.5 Δ]` with
`η ∘ s = id`, `0 ≤ t ∘ s < Δ/100` and image in `B`.

The proof is W4-CGP's `exists_continuousOn_section_of_deriv_pos` (the CGP03 argument). Strengthenings:
the near-identity bound is used only at the two endpoints, the derivative only needs to be positive, and
the section is defined on the closed interval. The binding `j = j_i(·, z₀)` is LFR28's embedding on
LFR14's fixed buffer (modulo LFR14 data; LFR18/LFR28 actual estimates not in the tree).
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Analysis

/-- EGP05, kernel form. -/
theorem exists_edge_cloud_section {X : Type*} [TopologicalSpace X] (j : ℝ → X) (η t : X → ℝ)
    (B : Set X) {Δ μ : ℝ} (hΔ : 0 < Δ) (hμ : 2 * μ < 1 / 100)
    (hj : ContinuousOn j (Icc (-(89 / 10 * Δ)) (89 / 10 * Δ)))
    (hφ : ContinuousOn (η ∘ j) (Icc (-(89 / 10 * Δ)) (89 / 10 * Δ)))
    (hderiv : ∀ a ∈ Ioo (-(89 / 10 * Δ)) (89 / 10 * Δ), 0 < deriv (η ∘ j) a)
    (hlo : |η (j (-(89 / 10 * Δ))) - (-(89 / 10 * Δ))| < 2 * μ * Δ)
    (hhi : |η (j (89 / 10 * Δ)) - 89 / 10 * Δ| < 2 * μ * Δ)
    (hheight : ∀ a ∈ Icc (-(89 / 10 * Δ)) (89 / 10 * Δ),
      0 ≤ t (j a) ∧ t (j a) < Δ / 100 ∧ j a ∈ B) :
    ∃ s : ℝ → X, ContinuousOn s (Icc (-(17 / 2 * Δ)) (17 / 2 * Δ)) ∧
      ∀ a ∈ Icc (-(17 / 2 * Δ)) (17 / 2 * Δ),
        η (s a) = a ∧ 0 ≤ t (s a) ∧ t (s a) < Δ / 100 ∧ s a ∈ B := by
  have hμΔ : 2 * μ * Δ < Δ / 100 := by nlinarith
  have hl := (abs_lt.mp hlo).2
  have hh := (abs_lt.mp hhi).1
  obtain ⟨s, hs, hsec⟩ := exists_continuousOn_section_of_deriv_pos j η
    (p := -(89 / 10 * Δ)) (q := 89 / 10 * Δ) (u := -(17 / 2 * Δ)) (v := 17 / 2 * Δ)
    (by linarith) hj hφ hderiv (by linarith) (by linarith)
  refine ⟨s, hs, fun a ha => ?_⟩
  obtain ⟨hηs, b, hb, hjb⟩ := hsec a ha
  obtain ⟨h1, h2, h3⟩ := hheight b hb
  rw [← hjb]
  exact ⟨hjb ▸ hηs, h1, h2, h3⟩

end DifferentialGeometry.Analysis
