import DifferentialGeometry.Geometry.Metric.SupportComparisonLists
import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation

/-!
# The slim graph packet: comparison lists and original tests (SGP01, SGP03 kernels)

Blueprint 207B, § "Actual slim graph models and the third cloudy image" (B:4334–4808).

* SGP01 (`lem:fibration-slim-comparison-list`, B:4353): a slim closed support
  `closedBall p_j (.95 L R_j)` meeting `D_i = B(p_i, .95 L R_i)` gives `.99 < R_j/R_i < 1.01` and
  `d(p_i, p_j) < 2 L R_i` once `L Λ < 10⁻⁵` (`slim_comparison_list_bounds`, an application of
  W4-EGP's `support_meeting_sharp_bounds` with `a = c = .95 L`); every point of the original set
  `{|η_i| ≤ 8ℓ}` lies within `.81 L` (`slim_plateau_inside_comparison_ball`).
  The list cardinality `N_*` is W4-EGP's `ncard_supports_meeting_ball_le_of_scaled_ricci_bound`
  with `R' = .95·10⁶`, `C' = 10⁶`, `a' = 1/3`.
* SGP03 (`lem:fibration-slim-actual-affine-comparison`, B:4483): under the budgets (SB) the common
  reference-axis test gives `‖DU_j - a_j Dη_i‖ < θ` (`slim_derivative_comparison`, using FC15's
  Riesz step), the value error `s_j v_s + E + v_s < θ` (`slim_value_comparison`), and a positive
  model cutoff lies inside `B(p_j, .91 L R_j)` (`slim_model_support_inside`).

Units: `ℓ = 10⁵ Δ`, `L = 10⁶ Δ`.
-/

set_option autoImplicit false
open Metric

namespace DifferentialGeometry.Geometry.Collapse

/-- SGP01 (SL): a slim support meeting the reference comparison ball. -/
theorem slim_comparison_list_bounds {X : Type*} [PseudoMetricSpace X] {ρ : X → ℝ}
    {Λ : NNReal} (hρ : LipschitzWith Λ ρ) {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z) {L : ℝ}
    (hL : 0 ≤ L) (hΛ : L * Λ < 1 / 100000)
    (hmeet : (closedBall z (95 / 100 * L * ρ z) ∩ ball p (95 / 100 * L * ρ p)).Nonempty) :
    99 / 100 < ρ z / ρ p ∧ ρ z / ρ p < 101 / 100 ∧ dist p z < 2 * L * ρ p := by
  have hb : 250 * ((Λ : ℝ) * (95 / 100 * L)) ≤ 1 := by nlinarith
  obtain ⟨h1, h2, h3, -⟩ := GC.MetricGeometry.support_meeting_sharp_bounds hρ hp hz
    (by positivity) (by positivity) hb hb hmeet
  refine ⟨h1, h2, h3.trans_le ?_⟩
  have := mul_nonneg hL hp.le
  nlinarith

private theorem sqrt_sq_add_sq_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A ^ 2 + B ^ 2) ≤ A + B := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- SGP01: the original plateau `|η_i| ≤ 8ℓ` lies strictly inside `D_i` (radius `.81 L < .95 L`). -/
theorem slim_plateau_inside_comparison_ball {Δ : ℝ} (hΔ : 0 < Δ) :
    Real.sqrt ((8 * (100000 * Δ) + Δ / 100) ^ 2 + (1000 * Δ) ^ 2) + Δ / 100 <
      81 / 100 * (1000000 * Δ) := by
  have := sqrt_sq_add_sq_le (A := 8 * (100000 * Δ) + Δ / 100) (B := 1000 * Δ)
    (by positivity) (by positivity)
  linarith

/-- SGP03: a positive model cutoff puts the point within `.91 L R_j` of `p_j`. -/
theorem slim_model_support_inside {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    Real.sqrt ((9 * (100000 * Δ) + 1) ^ 2 + (1000 * Δ) ^ 2) + Δ / 100 <
      91 / 100 * (1000000 * Δ) := by
  have := sqrt_sq_add_sq_le (A := 9 * (100000 * Δ) + 1) (B := 1000 * Δ)
    (by positivity) (by positivity)
  linarith

/-- SGP03 (SC), values: `s_j v_s + E + v_s < θ` under (SB). -/
theorem slim_value_comparison {s v E θ : ℝ} (hs : s < 101 / 100) (hv0 : 0 ≤ v)
    (hv : v < θ / 100) (hE : E < θ / 100) : s * v + E + v < θ := by
  have h := mul_le_mul_of_nonneg_right hs.le hv0
  nlinarith

/-- SGP03 (SC), derivatives: two covectors of norm at most `1 + σ` that both exceed `1 - ε` on a
common unit vector, `ε = σ + (3δ + 2E)/(10L - 2δ)`, differ by less than `θ` under (SB). -/
theorem slim_derivative_comparison {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f g : StrongDual ℝ E) {θ σ δ e L : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hσ0 : 0 ≤ σ) (hσ : σ < θ ^ 2 / 10 ^ 6) (hδ0 : 0 ≤ δ) (hδ : δ < θ ^ 2 / 10 ^ 6)
    (he0 : 0 ≤ e) (he : e < θ ^ 2 / 10 ^ 6) (hL : 1 ≤ L)
    (hf : ‖f‖ ≤ 1 + σ) (hg : ‖g‖ ≤ 1 + σ) (w : E) (hw : ‖w‖ = 1)
    (hfw : 1 - (σ + (3 * δ + 2 * e) / (10 * L - 2 * δ)) ≤ f w)
    (hgw : 1 - (σ + (3 * δ + 2 * e) / (10 * L - 2 * δ)) ≤ g w) : ‖f - g‖ < θ := by
  set ε := σ + (3 * δ + 2 * e) / (10 * L - 2 * δ) with hεdef
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hden : 9 < 10 * L - 2 * δ := by nlinarith
  have hfrac0 : 0 ≤ (3 * δ + 2 * e) / (10 * L - 2 * δ) := by positivity
  have hfrac : (3 * δ + 2 * e) / (10 * L - 2 * δ) < θ ^ 2 / 10 ^ 6 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hε0 : 0 ≤ ε := by positivity
  have hε : ε < 2 * (θ ^ 2 / 10 ^ 6) := by rw [hεdef]; linarith
  have hfε : ‖f‖ ≤ 1 + ε := by linarith
  have hgε : ‖g‖ ≤ 1 + ε := by linarith
  have hsat := ContinuousLinearMap.norm_sub_le_of_common_unit_saturation f g hε0 hfε hgε w hw
    hfw hgw
  have hsq : 4 * ε + ε ^ 2 < (θ / 2) ^ 2 := by nlinarith
  have hroot : Real.sqrt (4 * ε + ε ^ 2) < θ / 2 :=
    (Real.sqrt_lt' (by positivity)).mpr hsq
  linarith

end DifferentialGeometry.Geometry.Collapse
