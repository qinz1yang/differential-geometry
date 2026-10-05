import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Requests

/-!
# A consumer of the requests record: SGP03's parameter requests in ONE assignment

Lane C14-FAM (design `build-logs/resume/design-C14-FAM.md` (g)). `sgp03Requests_FAM θ` is the
request record of SGP03's parameter side conditions (C14-SGP2's `sgp03_row`, C14-SGP3's
`sgp03_zero_row`: `σs < θ²/10⁶`, `vs < θ/100`, `ζ < θ²/10⁶`, `ζ < 1/(100L)`, `εr < θ/(100L)`,
`T ≥ 1600L`, `10⁶ΔΛ < 10⁻⁵`, `e < 1/40`, `L = 10⁶Δ`); `C14Assignment.sgp03_FAM` shows that
EVERY assignment for it (e.g. the one of `exists_c14_assignment`, whose family it parametrizes)
meets them.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Collapse

/-- The request record of SGP03's parameter side conditions (the other requests are trivial). -/
def sgp03Requests_FAM (θ : ℝ) (hθ : 0 < θ) : C14Requests where
  γ := 1
  γc := 1
  β₂ := 1
  Δ := 0
  σc _ _ := 1
  ε _ _ := 1
  μ _ _ := 1
  τ _ _ := 1
  s _ _ := 1
  b' _ _ := 1
  s' _ _ := 1
  Λ _ Δ := 1 / (10 ^ 12 * (|Δ| + 1))
  b _ _ := 1
  σs _ _ := θ ^ 2 / (2 * 10 ^ 6)
  vs _ _ := θ / 200
  β₁ _ _ := 1
  ζ _ Δ := min (θ ^ 2 / (2 * 10 ^ 6)) (1 / (200 * (10 ^ 6 * (|Δ| + 1))))
  cap _ Δ := θ / (100 * (10 ^ 6 * (|Δ| + 1)))
  e _ _ := 1 / 80
  T _ Δ := 1600 * (10 ^ 6 * Δ)
  Lmax _ _ _ := 0
  γ_pos := one_pos
  γc_pos := one_pos
  β₂_pos := one_pos
  σc_pos _ _ := one_pos
  ε_pos _ _ := one_pos
  μ_pos _ _ := one_pos
  τ_pos _ _ := one_pos
  s_pos _ _ := one_pos
  b'_pos _ _ := one_pos
  s'_pos _ _ := one_pos
  Λ_pos _ _ := by positivity
  b_pos _ _ := one_pos
  σs_pos _ _ := by positivity
  vs_pos _ _ := by positivity
  β₁_pos _ _ := one_pos
  ζ_pos _ _ := lt_min (by positivity) (by positivity)
  cap_pos _ _ := by positivity
  e_pos _ _ := by norm_num

/-- **SGP03's parameter side conditions in ONE assignment**: every assignment for
`sgp03Requests_FAM θ` has `σs < θ²/10⁶`, `vs < θ/100`, `ζ < θ²/10⁶`, `ζ < 1/(100L)`,
`εr < θ/(100L)`, `T ≥ 1600L`, `10⁶ΔΛ < 10⁻⁵` and `e < 1/40` (`L = 10⁶Δ`). -/
theorem C14Assignment.sgp03_FAM {θ : ℝ} (hθ : 0 < θ) (P : C14Assignment (sgp03Requests_FAM θ hθ)) :
    P.σs < θ ^ 2 / 10 ^ 6 ∧ P.vs < θ / 100 ∧ P.ζ < θ ^ 2 / 10 ^ 6 ∧
      P.ζ < 1 / (100 * (10 ^ 6 * P.Δ)) ∧ P.εr < θ / (100 * (10 ^ 6 * P.Δ)) ∧
      1600 * (10 ^ 6 * P.Δ) ≤ P.T ∧ 10 ^ 6 * P.Δ * P.Λ < 1 / 10 ^ 5 ∧ P.e < 1 / 40 := by
  have hΔ : 0 < P.Δ := (by have := P.β₂_pos; positivity : (0 : ℝ) < 100 / P.β₂).trans P.Δ_gt
  have habs : |P.Δ| = P.Δ := abs_of_pos hΔ
  have hσs := P.σs_le
  have hvs := P.vs_le
  have hζ := P.ζ_le
  have hcap := P.cap_eq
  have hT := P.T_ge
  have hΛ := P.Λ_le
  simp only [sgp03Requests_FAM, habs] at hσs hvs hζ hcap hT hΛ
  have hθ2 : 0 < θ ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, hT, ?_, P.e_lt⟩
  · refine hσs.trans_lt ?_
    rw [div_lt_div_iff_of_pos_left hθ2 (by positivity) (by positivity)]
    norm_num
  · refine hvs.trans_lt ?_
    rw [div_lt_div_iff_of_pos_left hθ (by positivity) (by positivity)]
    norm_num
  · refine (hζ.trans (min_le_left _ _)).trans_lt ?_
    rw [div_lt_div_iff_of_pos_left hθ2 (by positivity) (by positivity)]
    norm_num
  · refine (hζ.trans (min_le_right _ _)).trans_lt ?_
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
    nlinarith
  · refine P.εr_lt_cap.trans_le ?_
    rw [hcap]
    rw [div_le_div_iff_of_pos_left hθ (by positivity) (by positivity)]
    nlinarith
  · have hΛ' : P.Λ * (10 ^ 12 * (P.Δ + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hΛ
    have hpos := P.Λ_pos
    nlinarith

end DifferentialGeometry.Geometry.Collapse
