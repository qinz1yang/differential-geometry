import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# ZSP02's two global profiles `ψ` and `χ` for the isotopy family (ZH)

Lane C14-ZSP35. Blueprint `master207B.tex`, ZSP02 (`thm:fibration-actual-zero-domains`,
B:6449–6458): "Choose a smooth nondecreasing `ψ` equal to the identity on `[.31, .49]`, constant
`.3` below `.30` and constant `.5` above `.50`, with `ψ(s) ≤ .4` exactly when `s ≤ .4`. Choose a
smooth `χ` equal to one on `[.34, .46]` with support in `(.32, .48)`."

* `zspPsi_ZSP35 s = s + (.3 − s)·S((.31 − s)·100) + (.5 − s)·S((s − .49)·100)` (`S` =
  `Real.smoothTransition`): smooth, the identity on `[.31, .49]`, `.3` on `s ≤ .3`, `.5` on
  `s ≥ .5`, and `ψ(s) ≤ .4 ↔ s ≤ .4`, `ψ(s) = .4 ↔ s = .4` (monotonicity is not needed).
* `zspChi_ZSP35 s = S((s − .33)·100)·S((.47 − s)·100)`: smooth, values in `[0, 1]`, one on
  `[.34, .46]`, zero for `s ≤ .33` and for `s ≥ .47` (support in `[.33, .47] ⊂ (.32, .48)`).
* `zsp_level_location_ZSP35`: for `τ ∈ [0, 1]`, if `|q − η| < 1/500` whenever `.33 < η < .47`,
  then `ψ(η) + τχ(η)(q − η) = .4` forces `|η − .4| < 1/500` (the level of (ZH) lies where `ψ = id`
  and `χ = 1`).
-/

set_option autoImplicit false

noncomputable section

open Real
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

/-- ZSP02's profile `ψ`: the identity on `[.31, .49]`, `.3` below `.3`, `.5` above `.5`. -/
def zspPsi_ZSP35 (s : ℝ) : ℝ :=
  s + (3 / 10 - s) * smoothTransition ((31 / 100 - s) * 100) +
    (1 / 2 - s) * smoothTransition ((s - 49 / 100) * 100)

/-- ZSP02's cutoff `χ`: one on `[.34, .46]`, zero outside `(.33, .47)`. -/
def zspChi_ZSP35 (s : ℝ) : ℝ :=
  smoothTransition ((s - 33 / 100) * 100) * smoothTransition ((47 / 100 - s) * 100)

theorem contDiff_zspPsi_ZSP35 : ContDiff ℝ ∞ zspPsi_ZSP35 := by
  unfold zspPsi_ZSP35
  have h1 : ContDiff ℝ ∞ fun s : ℝ => smoothTransition ((31 / 100 - s) * 100) :=
    (smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.sub contDiff_id).mul contDiff_const)
  have h2 : ContDiff ℝ ∞ fun s : ℝ => smoothTransition ((s - 49 / 100) * 100) :=
    (smoothTransition.contDiff (n := ⊤)).comp ((contDiff_id.sub contDiff_const).mul contDiff_const)
  exact (contDiff_id.add ((contDiff_const.sub contDiff_id).mul h1)).add
    ((contDiff_const.sub contDiff_id).mul h2)

theorem contDiff_zspChi_ZSP35 : ContDiff ℝ ∞ zspChi_ZSP35 := by
  unfold zspChi_ZSP35
  exact ((smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_id.sub contDiff_const).mul contDiff_const)).mul
    ((smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.sub contDiff_id).mul contDiff_const))

theorem zspPsi_eq_self_ZSP35 {s : ℝ} (h1 : 31 / 100 ≤ s) (h2 : s ≤ 49 / 100) :
    zspPsi_ZSP35 s = s := by
  unfold zspPsi_ZSP35
  rw [smoothTransition.zero_of_nonpos (by nlinarith),
    smoothTransition.zero_of_nonpos (by nlinarith)]
  ring

theorem zspPsi_eq_low_ZSP35 {s : ℝ} (h : s ≤ 3 / 10) : zspPsi_ZSP35 s = 3 / 10 := by
  unfold zspPsi_ZSP35
  rw [smoothTransition.one_of_one_le (by nlinarith), smoothTransition.zero_of_nonpos (by nlinarith)]
  ring

theorem zspPsi_eq_high_ZSP35 {s : ℝ} (h : 1 / 2 ≤ s) : zspPsi_ZSP35 s = 1 / 2 := by
  unfold zspPsi_ZSP35
  rw [smoothTransition.zero_of_nonpos (by nlinarith), smoothTransition.one_of_one_le (by nlinarith)]
  ring

/-- Below `.31`, `ψ` stays in `(-∞, .31]`; above `.49`, it stays in `[.49, ∞)`. -/
theorem zspPsi_bounds_ZSP35 (s : ℝ) :
    (s ≤ 31 / 100 → zspPsi_ZSP35 s ≤ 31 / 100) ∧ (49 / 100 ≤ s → 49 / 100 ≤ zspPsi_ZSP35 s) := by
  have hL0 := smoothTransition.nonneg ((31 / 100 - s) * 100)
  have hL1 := smoothTransition.le_one ((31 / 100 - s) * 100)
  have hU0 := smoothTransition.nonneg ((s - 49 / 100) * 100)
  have hU1 := smoothTransition.le_one ((s - 49 / 100) * 100)
  unfold zspPsi_ZSP35
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [smoothTransition.zero_of_nonpos (show (s - 49 / 100) * 100 ≤ 0 by nlinarith)]
    nlinarith
  · rw [smoothTransition.zero_of_nonpos (show (31 / 100 - s) * 100 ≤ 0 by nlinarith)]
    nlinarith

theorem zspPsi_le_iff_ZSP35 {s : ℝ} : zspPsi_ZSP35 s ≤ 2 / 5 ↔ s ≤ 2 / 5 := by
  obtain ⟨hlo, hhi⟩ := zspPsi_bounds_ZSP35 s
  constructor
  · intro h
    by_contra hs
    push Not at hs
    by_cases h49 : s ≤ 49 / 100
    · rw [zspPsi_eq_self_ZSP35 (by linarith) h49] at h
      linarith
    · have := hhi (by linarith)
      linarith
  · intro h
    by_cases h31 : s ≤ 31 / 100
    · linarith [hlo h31]
    · rw [zspPsi_eq_self_ZSP35 (by linarith) (by linarith)]
      exact h

theorem zspPsi_eq_iff_ZSP35 {s : ℝ} : zspPsi_ZSP35 s = 2 / 5 ↔ s = 2 / 5 := by
  obtain ⟨hlo, hhi⟩ := zspPsi_bounds_ZSP35 s
  constructor
  · intro h
    by_cases h31 : s ≤ 31 / 100
    · linarith [hlo h31]
    · by_cases h49 : s ≤ 49 / 100
      · rwa [zspPsi_eq_self_ZSP35 (by linarith) h49] at h
      · linarith [hhi (by linarith)]
  · intro h
    rw [h, zspPsi_eq_self_ZSP35 (by norm_num) (by norm_num)]

theorem zspChi_mem_ZSP35 (s : ℝ) : 0 ≤ zspChi_ZSP35 s ∧ zspChi_ZSP35 s ≤ 1 := by
  unfold zspChi_ZSP35
  have h1 := smoothTransition.nonneg ((s - 33 / 100) * 100)
  have h2 := smoothTransition.le_one ((s - 33 / 100) * 100)
  have h3 := smoothTransition.nonneg ((47 / 100 - s) * 100)
  have h4 := smoothTransition.le_one ((47 / 100 - s) * 100)
  exact ⟨mul_nonneg h1 h3, by nlinarith⟩

theorem zspChi_eq_one_ZSP35 {s : ℝ} (h1 : 34 / 100 ≤ s) (h2 : s ≤ 46 / 100) :
    zspChi_ZSP35 s = 1 := by
  unfold zspChi_ZSP35
  rw [smoothTransition.one_of_one_le (by nlinarith), smoothTransition.one_of_one_le (by nlinarith),
    mul_one]

theorem zspChi_eq_zero_ZSP35 {s : ℝ} (h : s ≤ 33 / 100 ∨ 47 / 100 ≤ s) : zspChi_ZSP35 s = 0 := by
  unfold zspChi_ZSP35
  rcases h with h | h
  · rw [smoothTransition.zero_of_nonpos (by nlinarith), zero_mul]
  · rw [smoothTransition.zero_of_nonpos (show (47 / 100 - s) * 100 ≤ 0 by nlinarith), mul_zero]

/-- **The level of (ZH) lies where `ψ = id` and `χ = 1`**: for `τ ∈ [0, 1]`, if `|q − η| < 1/500`
whenever `.33 < η < .47`, then `ψ(η) + τχ(η)(q − η) = .4` forces `|η − .4| < 1/500`. -/
theorem zsp_level_location_ZSP35 {η q τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hq : 33 / 100 < η → η < 47 / 100 → |q - η| < 1 / 500)
    (hlev : zspPsi_ZSP35 η + τ * (zspChi_ZSP35 η * (q - η)) = 2 / 5) : |η - 2 / 5| < 1 / 500 := by
  by_cases hlo : η ≤ 33 / 100
  · rw [zspChi_eq_zero_ZSP35 (Or.inl hlo), zero_mul, mul_zero, add_zero,
      zspPsi_eq_iff_ZSP35] at hlev
    linarith
  by_cases hhi : 47 / 100 ≤ η
  · rw [zspChi_eq_zero_ZSP35 (Or.inr hhi), zero_mul, mul_zero, add_zero,
      zspPsi_eq_iff_ZSP35] at hlev
    linarith
  push Not at hlo hhi
  rw [zspPsi_eq_self_ZSP35 (by linarith) (by linarith)] at hlev
  have hqη := hq hlo hhi
  obtain ⟨c0, c1⟩ := zspChi_mem_ZSP35 η
  have hb : |τ * (zspChi_ZSP35 η * (q - η))| ≤ |q - η| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hτ.1, abs_of_nonneg c0]
    have h1 : zspChi_ZSP35 η * |q - η| ≤ |q - η| :=
      mul_le_of_le_one_left (abs_nonneg _) c1
    have h2 : τ * (zspChi_ZSP35 η * |q - η|) ≤ zspChi_ZSP35 η * |q - η| :=
      mul_le_of_le_one_left (mul_nonneg c0 (abs_nonneg _)) hτ.2
    linarith
  have : η - 2 / 5 = -(τ * (zspChi_ZSP35 η * (q - η))) := by linarith
  rw [this, abs_neg]
  linarith

end DifferentialGeometry.Geometry.Collapse
