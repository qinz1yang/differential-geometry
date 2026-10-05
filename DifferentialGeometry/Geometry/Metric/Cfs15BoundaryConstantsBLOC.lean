import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentLocalityBLOC
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The constant chain of BCG04 / BCG05

Blueprint `master207B.tex`, (AM) (B:3705–3730), BCG04 (B:9132–9200), BCG05 (B:9202–9290); external
draft 61 §3.4–3.5, disposition D61-8. The arithmetic that turns the contributor window into the
rows' conclusions:

* (AM) `am_radius_chain_BLOC`: `R_a ≥ (4/5)(3/5)³ρ(p) = (108/625)ρ(p)`;
  `radius_gt_two_BLOC`: with `ρ(p) > 20 r_∂ ≥ 0`, `R_a ≥ (108/625)ρ(p) > (2160/625) r_∂ ≥ 2 r_∂`.
* The window: `dist_lt_of_window_BLOC` (`B̄(y, R_y) ∩ B(x, R_x) ≠ ∅ ⟹ |y − x| < R_y + R_x`);
  `contributor_dist_lt_BLOC` (`r_y ≤ (5/3) r_x`, `r_x ≤ (5/3) Σ_j ρ(p)` ⟹
  `|y − x| < 250 b Σ_j ρ(p)`); `buffer_le_BLOC` (`Σ_j ≤ ε_j/10000`, `b = ε_j⁻¹` ⟹
  `250 b Σ_j ρ(p) ≤ .025 ρ(p)`); `contributor_near_BLOC` (BCG05.a, the window form of
  `Cfs15StageOutput`, with `.025ρ(p) < r_∂` when `ρ(p) < 40 r_∂`).
* BCG05's marker division: `marker_division_BLOC` (`|u − η| < r`, `|v − 1| < r`, `0 ≤ η ≤ 78`,
  `r < 1` ⟹ `|u/v − η| < 79r/(1 − r)`), `height_shift_lt_BLOC` (`r ≤ 10⁻⁴ ⟹ 79r/(1 − r) < .01`),
  `height_band_BLOC` (`32 ≤ η_p ≤ 78 ⟹ 31 < η_q < 79`), `model_height_band_BLOC` (`30 < h < 80`).
* BCG04's error: `boundary_error_lt_BLOC` (exact zero when `ρ(p) > 20 r_∂`, `< c_jρ(p) ≤ c₃ρ(p) ≤
  20c₃r_∂` otherwise, so `< ε_∂ = 20c₃r_∂` everywhere), its block form
  `boundary_error_norm_lt_BLOC` (`‖J‖ ≤ 1`) and the segment form `segment_error_lt_BLOC`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Analysis

/-- **(AM)**: `R_a ≥ (4/5)ρ(q_u)`, `ρ(q_u) ≥ (3/5)σ_u`, `σ_u ≥ (3/5)σ_x`, `σ_x ≥ (3/5)ρ(p)` give
`R_a ≥ (108/625)ρ(p)`. -/
theorem am_radius_chain_BLOC {R ρq σu σx ρp : ℝ} (h₁ : 4 / 5 * ρq ≤ R) (h₂ : 3 / 5 * σu ≤ ρq)
    (h₃ : 3 / 5 * σx ≤ σu) (h₄ : 3 / 5 * ρp ≤ σx) : 108 / 625 * ρp ≤ R := by
  linarith

/-- **BCG04's radius comparison**: `R_a ≥ (108/625)ρ(p)` and `ρ(p) > 20 r_∂ ≥ 0` give
`(2160/625) r_∂ < (108/625)ρ(p)` and `2 r_∂ < R_a`. -/
theorem radius_gt_two_BLOC {R ρ rb : ℝ} (hrb : 0 ≤ rb) (hρ : 20 * rb < ρ)
    (hR : 108 / 625 * ρ ≤ R) : 2160 / 625 * rb < 108 / 625 * ρ ∧ 2 * rb < R :=
  ⟨by linarith, by linarith⟩

/-- **The window bound**: `B̄(y, R_y) ∩ B(x, R_x) ≠ ∅` gives `dist y x < R_y + R_x`. -/
theorem dist_lt_of_window_BLOC {X : Type*} [PseudoMetricSpace X] {x y : X} {Ry Rx : ℝ}
    (h : (closedBall y Ry ∩ ball x Rx).Nonempty) : dist y x < Ry + Rx := by
  obtain ⟨w, hwy, hwx⟩ := h
  rw [mem_closedBall] at hwy
  rw [mem_ball] at hwx
  calc dist y x ≤ dist y w + dist w x := dist_triangle y w x
    _ < Ry + Rx := by rw [dist_comm y w]; linarith

/-- **The contributor distance (BCG05)**: `d < 80b r_y + 8b r_x` with `b ≥ 0`, `r_x ≥ 0`,
`r_y ≤ (5/3) r_x`, `r_x ≤ (5/3) sρ` gives `d < 250 b sρ`. -/
theorem contributor_dist_lt_BLOC {d b ry rx sρ : ℝ} (hd : d < 80 * b * ry + 8 * b * rx)
    (hb : 0 ≤ b) (hrx : 0 ≤ rx) (hy : ry ≤ 5 / 3 * rx) (hx : rx ≤ 5 / 3 * sρ) :
    d < 250 * b * sρ := by
  have h1 : b * ry ≤ b * (5 / 3 * rx) := mul_le_mul_of_nonneg_left hy hb
  have h2 : b * rx ≤ b * (5 / 3 * sρ) := mul_le_mul_of_nonneg_left hx hb
  have h3 : 0 ≤ b * sρ := mul_nonneg hb (by linarith)
  nlinarith

/-- **The buffer bound (BCG05)**: `Σ_j ≤ ε_j/10000`, `ε_j > 0`, `ρ ≥ 0` give
`250 ε_j⁻¹ Σ_j ρ ≤ ρ/40`. -/
theorem buffer_le_BLOC {ε sj ρ : ℝ} (hε : 0 < ε) (hsj : sj ≤ ε / 10000) (hρ : 0 ≤ ρ) :
    250 * ε⁻¹ * (sj * ρ) ≤ ρ / 40 := by
  have h1 : ε⁻¹ * sj ≤ 1 / 10000 := by
    rw [inv_mul_le_iff₀ hε]
    linarith
  have h2 : ε⁻¹ * sj * ρ ≤ 1 / 10000 * ρ := mul_le_mul_of_nonneg_right h1 hρ
  have h3 : 250 * ε⁻¹ * (sj * ρ) = 250 * (ε⁻¹ * sj * ρ) := by ring
  rw [h3]
  linarith

/-- **BCG05.a in the window form of `Cfs15StageOutput`**: if `B̄(y, 80ε⁻¹r_y) ∩ B(x, 8ε⁻¹r_x) ≠ ∅`,
`r_y ≤ (5/3) r_x`, `0 ≤ r_x ≤ (5/3) Σ_j ρ`, `Σ_j ≤ ε/10000` (`ε > 0`, `ρ ≥ 0`), then
`|y − x| < 250 ε⁻¹ Σ_j ρ ≤ .025 ρ`; if moreover `ρ < 40 r_∂`, then `|y − x| < r_∂`. -/
theorem contributor_near_BLOC {X : Type*} [PseudoMetricSpace X] {x y : X} {ε ry rx sj ρ : ℝ}
    (h : (closedBall y (80 * ε⁻¹ * ry) ∩ ball x (8 * ε⁻¹ * rx)).Nonempty) (hε : 0 < ε)
    (hrx : 0 ≤ rx) (hy : ry ≤ 5 / 3 * rx) (hx : rx ≤ 5 / 3 * (sj * ρ)) (hsj : sj ≤ ε / 10000)
    (hρ : 0 ≤ ρ) :
    dist y x < 250 * ε⁻¹ * (sj * ρ) ∧ 250 * ε⁻¹ * (sj * ρ) ≤ ρ / 40 ∧
      ∀ rb : ℝ, ρ < 40 * rb → dist y x < rb := by
  have hd := contributor_dist_lt_BLOC (dist_lt_of_window_BLOC h) (inv_nonneg.mpr hε.le) hrx hy hx
  have hb := buffer_le_BLOC hε hsj hρ
  exact ⟨hd, hb, fun rb hrb => by linarith⟩

/-- **BCG05's marker division**: `|u − η| < r`, `|v − 1| < r`, `0 ≤ η ≤ 78`, `r < 1` give
`|u/v − η| < 79r/(1 − r)`. -/
theorem marker_division_BLOC {u v η r : ℝ} (hu : |u - η| < r) (hv : |v - 1| < r) (hη₀ : 0 ≤ η)
    (hη : η ≤ 78) (hr : r < 1) : |u / v - η| < 79 * r / (1 - r) := by
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg _) hu
  have hv' := abs_lt.mp hv
  have hvpos : 0 < v := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hnum : |u - η * v| < 79 * r := by
    have heq : u - η * v = (u - η) + η * (1 - v) := by ring
    have hb : |η * (1 - v)| ≤ 78 * r := by
      rw [abs_mul, abs_of_nonneg hη₀, abs_sub_comm]
      exact mul_le_mul hη hv.le (abs_nonneg _) (by norm_num)
    calc |u - η * v| = |(u - η) + η * (1 - v)| := by rw [heq]
      _ ≤ |u - η| + |η * (1 - v)| := abs_add_le _ _
      _ < r + 78 * r := by linarith
      _ = 79 * r := by ring
  have hdiv : u / v - η = (u - η * v) / v := by field_simp
  rw [hdiv, abs_div, abs_of_pos hvpos, div_lt_div_iff₀ hvpos h1r]
  have hn0 : 0 ≤ |u - η * v| := abs_nonneg _
  nlinarith

/-- **BCG05's height shift**: `r ≤ 10⁻⁴` gives `79r/(1 − r) < .01`. -/
theorem height_shift_lt_BLOC {r : ℝ} (hr : r ≤ 1 / 10000) :
    79 * r / (1 - r) < 1 / 100 := by
  have h1r : 0 < 1 - r := by linarith
  rw [div_lt_iff₀ h1r]
  linarith

/-- **BCG05's height band**: `32 ≤ η_p ≤ 78` and `|η_q − η_p| < .01` give `31 < η_q < 79`. -/
theorem height_band_BLOC {ηp ηq : ℝ} (hp₀ : 32 ≤ ηp) (hp₁ : ηp ≤ 78) (h : |ηq - ηp| < 1 / 100) :
    31 < ηq ∧ ηq < 79 := by
  have := abs_lt.mp h
  constructor <;> linarith

/-- **BCG05's model height band**: `31 < η < 79`, `|h − η| < Rθ`, `Rθ ≤ 1` give `30 < h < 80`. -/
theorem model_height_band_BLOC {η h R θ : ℝ} (hη₀ : 31 < η) (hη₁ : η < 79) (hh : |h - η| < R * θ)
    (hRθ : R * θ ≤ 1) : 30 < h ∧ h < 80 := by
  have := abs_lt.mp hh
  constructor <;> linarith

/-- **BCG04's error, scalar form**: exact zero when `ρ > 20 r_∂`, and `e < c_jρ` with `c_j ≤ c₃`,
`0 < c₃`, `0 < r_∂`, `0 ≤ ρ`, give `e < ε_∂ = 20c₃r_∂` (no global bound on `ρ`). -/
theorem boundary_error_lt_BLOC {e ρ rb cj c₃ : ℝ} (hexact : 20 * rb < ρ → e = 0)
    (he : e < cj * ρ) (hc : cj ≤ c₃) (hc₃ : 0 < c₃) (hrb : 0 < rb) (hρ : 0 ≤ ρ) :
    e < 20 * c₃ * rb := by
  by_cases hbig : 20 * rb < ρ
  · rw [hexact hbig]
    positivity
  · have h1 : cj * ρ ≤ c₃ * ρ := mul_le_mul_of_nonneg_right hc hρ
    have h2 : c₃ * ρ ≤ c₃ * (20 * rb) := mul_le_mul_of_nonneg_left (not_lt.mp hbig) hc₃.le
    linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **BCG04's error, block form**: for `‖J‖ ≤ 1`, `J g = J f` when `ρ > 20 r_∂`, and
`‖g − f‖ < c_jρ` (`c_j ≤ c₃`, `0 < c₃`, `0 < r_∂`, `0 ≤ ρ`): `‖J (g − f)‖ < 20c₃r_∂`. -/
theorem boundary_error_norm_lt_BLOC (J : H →L[ℝ] F) (hJ : ‖J‖ ≤ 1) {g f : H} {ρ rb cj c₃ : ℝ}
    (hexact : 20 * rb < ρ → J g = J f) (he : ‖g - f‖ < cj * ρ) (hc : cj ≤ c₃) (hc₃ : 0 < c₃)
    (hrb : 0 < rb) (hρ : 0 ≤ ρ) : ‖J (g - f)‖ < 20 * c₃ * rb := by
  refine boundary_error_lt_BLOC (fun hbig => ?_) ?_ hc hc₃ hrb hρ
  · rw [map_sub, hexact hbig, sub_self, norm_zero]
  · calc ‖J (g - f)‖ ≤ ‖J‖ * ‖g - f‖ := J.le_opNorm _
      _ ≤ 1 * ‖g - f‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
      _ = ‖g - f‖ := one_mul _
      _ < cj * ρ := he

/-- **BCG04's error along the segment `[F(p), E(p)]`**: if `‖J (E − F)‖ < ε_∂`, every point `q` of
the segment has `‖J (q − F)‖ < ε_∂`. -/
theorem segment_error_lt_BLOC (J : H →L[ℝ] F) {u w : H} {εb : ℝ} (h : ‖J (w - u)‖ < εb) :
    ∀ q ∈ segment ℝ u w, ‖J (q - u)‖ < εb :=
  fun q hq => (segment_norm_sub_le_BLOC J q hq).trans_lt h

end DifferentialGeometry.Analysis
