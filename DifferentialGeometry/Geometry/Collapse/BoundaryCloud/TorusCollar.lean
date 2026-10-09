import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# The adjusted torus collar and its internal frontier (blueprint 207B, BCG06, B:9290–9470)

Row-local kernels:
* `height_sub_forty_lt_of_marked`, `abs_height_sub_forty_lt_of_frontier` — (BCG06.c): marker division
  with a global block error `ε`, valid at every point of the full preimage (no localization assumed).
* `height_frontier_bound` — with `ε < 10⁻⁶` the frontier lies in `39.999 < η < 40.001`.
* `apply_gt_of_norm_sub_lt` — `du_b(X_b) > 1 - 1.02 c₃ > .99` along the height field.
* `existsUnique_crossing` — every height-flow line across `[38, 42]` meets `u_b = 40` exactly once,
  between `40 - ε` and `40 + ε`.
* `height_lt_of_marker_ne_one` — the strict-marker step: a marked-branch point with marker `≠ 1`
  lies below height `32`.
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

/-- (BCG06.c), first line: `u_b ≤ 40 v_b` forces `η_b ≤ 40 + 41ε/(.9 - ε)`. -/
theorem height_sub_forty_lt_of_marked {u v η ζ ε : ℝ} (hu : |u - η * ζ| < ε) (hv : |v - ζ| < ε)
    (hv9 : 9 / 10 ≤ v) (hε : ε < 9 / 10) (hle : u ≤ 40 * v) :
    η - 40 < 41 * ε / (9 / 10 - ε) := by
  have hζ : 9 / 10 - ε < ζ := by linarith [(abs_lt.mp hv).2]
  have hden : 0 < 9 / 10 - ε := by linarith
  have hε0 : 0 < ε := (abs_nonneg _).trans_lt hu
  have hkey : (η - 40) * ζ < 41 * ε := by
    have : (η - 40) * ζ = (η * ζ - u) + (u - 40 * v) + 40 * (v - ζ) := by ring
    rw [this]
    linarith [(abs_lt.mp hu).1, (abs_lt.mp hv).2]
  rw [lt_div_iff₀ hden]
  by_cases hη : η - 40 ≤ 0
  · nlinarith
  · have : (η - 40) * (9 / 10 - ε) ≤ (η - 40) * ζ :=
      mul_le_mul_of_nonneg_left hζ.le (le_of_not_ge hη)
    linarith

/-- (BCG06.c), second line: on the frontier `u_b = 40 v_b`, `|η_b - 40| < 41ε/(.9 - ε)`. -/
theorem abs_height_sub_forty_lt_of_frontier {u v η ζ ε : ℝ} (hu : |u - η * ζ| < ε)
    (hv : |v - ζ| < ε) (hv9 : 9 / 10 ≤ v) (hε : ε < 9 / 10) (heq : u = 40 * v) :
    |η - 40| < 41 * ε / (9 / 10 - ε) := by
  have hζ : 9 / 10 - ε < ζ := by linarith [(abs_lt.mp hv).2]
  have hden : 0 < 9 / 10 - ε := by linarith
  have hζ0 : 0 < ζ := by linarith
  have hkey : |η - 40| * ζ < 41 * ε := by
    have h1 : (η - 40) * ζ = (η * ζ - u) + 40 * (v - ζ) := by rw [heq]; ring
    have h2 : |(η - 40) * ζ| ≤ |η * ζ - u| + 40 * |v - ζ| := by
      rw [h1]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 40)]
    rw [abs_mul, abs_of_pos hζ0, abs_sub_comm (η * ζ) u] at h2
    linarith
  rw [lt_div_iff₀ hden]
  have : |η - 40| * (9 / 10 - ε) ≤ |η - 40| * ζ :=
    mul_le_mul_of_nonneg_left hζ.le (abs_nonneg _)
  linarith

/-- With `ε_∂ < 10⁻⁶` the frontier lies in `|η_b - 40| < .001`. -/
theorem height_frontier_bound {ε : ℝ} (hε : ε < 1 / 1000000) :
    41 * ε / (9 / 10 - ε) < 1 / 1000 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- `du_b(X_b) > .99`: `dη_b(X) = 1`, `‖X‖ ≤ 1.02` and `‖du_b - dη_b‖ < c₃ ≤ 10⁻⁵`. -/
theorem apply_gt_of_norm_sub_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dη du : E →L[ℝ] ℝ) (X : E) {c₃ : ℝ} (hX : dη X = 1) (hXn : ‖X‖ ≤ 1.02)
    (herr : ‖du - dη‖ < c₃) (hc : c₃ ≤ 1 / 100000) : 99 / 100 < du X := by
  have h1 : |(du - dη) X| ≤ ‖du - dη‖ * ‖X‖ := by
    simpa [Real.norm_eq_abs] using (du - dη).le_opNorm X
  have h2 : ‖du - dη‖ * ‖X‖ ≤ c₃ * 1.02 :=
    mul_le_mul herr.le hXn (norm_nonneg _) ((norm_nonneg _).trans herr.le)
  have h3 : (du - dη) X = du X - 1 := by
    rw [sub_apply, hX]
  rw [h3] at h1
  linarith [(abs_le.mp (h1.trans h2)).1]

/-- Every flow line across the band `[38, 42]` crosses `u_b = 40` exactly once, at a height within
`ε` of `40` (BCG06, implicit-function step in one variable). -/
theorem existsUnique_crossing {g : ℝ → ℝ} {ε : ℝ} (hg : ContinuousOn g (Icc 38 42))
    (hmono : StrictMonoOn g (Icc 38 42)) (hclose : ∀ t ∈ Icc (38 : ℝ) 42, |g t - t| < ε)
    (hε : ε ≤ 1 / 100) :
    ∃ t ∈ Ioo (40 - ε) (40 + ε), g t = 40 ∧ ∀ s ∈ Icc (38 : ℝ) 42, g s = 40 → s = t := by
  have h38 : (38 : ℝ) ∈ Icc (38 : ℝ) 42 := ⟨le_refl _, by norm_num⟩
  have h42 : (42 : ℝ) ∈ Icc (38 : ℝ) 42 := ⟨by norm_num, le_refl _⟩
  have hlo : g 38 ≤ 40 := by linarith [(abs_lt.mp (hclose 38 h38)).2]
  have hhi : 40 ≤ g 42 := by linarith [(abs_lt.mp (hclose 42 h42)).1]
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (by norm_num : (38 : ℝ) ≤ 42) hg ⟨hlo, hhi⟩
  have hc := abs_lt.mp (hclose t ht)
  refine ⟨t, ⟨by linarith [hc.2], by linarith [hc.1]⟩, hgt, fun s hs hgs => ?_⟩
  exact hmono.injOn hs ht (hgs.trans hgt.symm)

/-- Strict-marker step of BCG06: if the marker is one on the band `32 ≤ η ≤ 78` (BCG05) and the
point is below height `41`, a marker different from one forces `η < 32`. -/
theorem height_lt_of_marker_ne_one {η v : ℝ} (hband : 32 ≤ η → η ≤ 78 → v = 1) (hη : η < 41)
    (hv : v ≠ 1) : η < 32 := by
  by_contra h
  exact hv (hband (le_of_not_gt h) (by linarith))

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
