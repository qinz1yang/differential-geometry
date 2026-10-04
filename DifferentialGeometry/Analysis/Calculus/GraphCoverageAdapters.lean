import DifferentialGeometry.Analysis.Calculus.GraphCoverage

/-!
# Coverage adapters for the actual cloudy packets (SGP06, EGP07, TCP06)

Blueprint 207B, SGP06 (`thm:fibration-actual-third-cloud`, B:4711–4786). FC25's coverage kernel
`hausdorffDist_graph_tangent_closedBall_le` asks for two hypotheses on the image set `X`:
every point of `X` in the test ball is within `e` of the graph over its own first coordinate,
and every parameter of the test ball has a point of `X` within `e` of its graph point.
In the packets both come from source points `q` of a set `D` (the original enlarged
threshold-`8ℓ` set): FC03 localizes every image point to a full-marker preimage, whose first
coordinate is then EXACTLY `η(q)`; the graph approximation is the packet's (SG)/(EG)/(TG);
coverage of parameters is the actual bundle coordinate `η(q_u) = u`.
`hausdorffDist_coordinate_graph_coverage_le` packages this generically.

The numerical inputs of SGP06 are `marker_localization_lt` (FC03's bound
`(1+7ℓ)R/(1-R) < ℓ/10` for `R < 1/100`), `test_radius_lt_of_parameters`, and
`coverage_budget_lt_half` (the strict bound `3q/r̂ < Γ/2` under (CP)).
-/

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

variable {M E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- SGP06/EGP07/TCP06: FC25's coverage bound from source-level localization, exact coordinates,
the graph approximation and exact coordinate coverage. -/
theorem hausdorffDist_coordinate_graph_coverage_le (F : M → H) (η : M → E) (D : Set M)
    (Φ : E → H) (P : H →L[ℝ] E) (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (hgraph : ∀ u, P (Φ u) = u)
    (X : Set H) (x : H) (hx : x ∈ X) {R B e : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hreg : ∀ u ∈ closedBall (P x) R, ContDiffAt ℝ 2 Φ u)
    (hsecond : ∀ u ∈ closedBall (P x) R, ‖iteratedFDeriv ℝ 2 Φ u‖ ≤ B)
    (hlocal : ∀ y ∈ X ∩ closedBall x R, ∃ q ∈ D, F q = y ∧ P y = η q)
    (happrox : ∀ q ∈ D, dist (F q) (Φ (η q)) ≤ e)
    (hcover : ∀ u ∈ closedBall (P x) R, ∃ q ∈ D, η q = u ∧ F q ∈ X) :
    hausdorffDist (X ∩ closedBall x R)
      ((fun v => x + fderiv ℝ Φ (P x) v) '' (univ : Set E) ∩ closedBall x R) ≤
        3 * (2 * e + B * R ^ 2 / 2) := by
  refine hausdorffDist_graph_tangent_closedBall_le Φ P hP hgraph X x hx hR hB he hreg hsecond
    ?_ ?_
  · intro y hy
    obtain ⟨q, hq, rfl, hPq⟩ := hlocal y hy
    rw [hPq]
    exact happrox q hq
  · intro u hu
    obtain ⟨q, hq, rfl, hX⟩ := hcover u hu
    exact ⟨F q, hX, happrox q hq⟩

/-- FC03's localization bound in SGP06: for `R < 1/100`, `ℓ ≥ 1` and `A ≤ 7ℓ`,
`(1 + A) R / (1 - R) < ℓ/10`. -/
theorem marker_localization_lt {R ℓ A : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 100) (hℓ : 1 ≤ ℓ)
    (hA : A ≤ 7 * ℓ) : (1 + A) * R / (1 - R) < ℓ / 10 := by
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- SGP06: with `r̂ ≤ 5σ/4` and `σ < Γ/200` the test radius `R = r̂/Γ` is below `1/100`. -/
theorem test_radius_lt_of_parameters {σ Γ r : ℝ} (hΓ : 0 < Γ) (hS : σ < Γ / 200)
    (hr : r ≤ 5 * σ / 4) : r / Γ < 1 / 100 := by
  rw [div_lt_iff₀ hΓ]
  linarith

/-- SGP06's coverage budget under (CP): `σ < Γ³/(100 C)`, `e < Γσ/100` and `σ/2 ≤ r ≤ 2σ` give
`3 (2e + C (r/Γ)²/2) < (Γ/2) r`, i.e. both truncated coverage directions with strict slack. -/
theorem coverage_budget_lt_half {σ Γ C e r : ℝ} (hΓ : 0 < Γ) (hS : 0 < σ) (hC : 0 < C)
    (hSC : C * σ < Γ ^ 3 / 100) (he : e < Γ * σ / 100) (hrlow : σ / 2 ≤ r) (hrhigh : r ≤ 2 * σ) :
    3 * (2 * e + C * (r / Γ) ^ 2 / 2) < Γ / 2 * r := by
  have hr : 0 < r := by linarith
  set t := r / Γ with ht
  have htr : t * Γ = r := by rw [ht]; field_simp
  have ht0 : 0 < t := div_pos hr hΓ
  -- `6e < 12Γr/100` and `3 C t²/2 ≤ 3 C t · 2σ / (2Γ) < 3 Γ r / 100`
  have h1 : 6 * e < 12 / 100 * (Γ * r) := by nlinarith
  have h2 : C * t ^ 2 * Γ ^ 2 = C * r ^ 2 := by rw [← htr]; ring
  have h3 : C * r ^ 2 ≤ 2 * (C * σ) * r := by
    have := mul_le_mul_of_nonneg_left hrhigh (mul_nonneg hC.le hr.le)
    nlinarith
  have h4 : 2 * (C * σ) * r < 2 * (Γ ^ 3 / 100) * r := by nlinarith
  have hΓ2 : 0 < Γ ^ 2 := by positivity
  have h5 : C * t ^ 2 < 2 / 100 * Γ * r := by
    by_contra hcon
    have := mul_le_mul_of_nonneg_right (le_of_not_gt hcon) hΓ2.le
    nlinarith
  nlinarith

end GC.MetricGeometry
