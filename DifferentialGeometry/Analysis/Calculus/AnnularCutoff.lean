import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

/-!
# The scalar annular cutoff of LC31

Blueprint 207A, before LC31 (A:21275–21292). Fix a smooth `φ : ℝ → ℝ` with values in `[0, 1]`,
equal to one on `(-∞, 0]` and to zero on `[1, ∞)`. For `a < b` put
`χ_{a,b}(t) = φ ((t - a) / (b - a))` (the inverse affine change; the project's repair of KL
equation (2.1)) and `Φ(t) = χ_{-3/10,-1/5}(-t) · χ_{4/5,9/10}(t)`. Then `Φ` is smooth, valued in
`[0, 1]`, vanishes for `t ≤ 1/5` and for `t ≥ 9/10`, equals one on `[3/10, 4/5]`, and has a
finite derivative bound `L_Φ`. A profile `φ` exists: `t ↦ smoothTransition (1 - t)`; it is also
nonincreasing (the blueprint's extra requirement, not used by the endpoint properties).
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis.Calculus

/-- The affine cutoff `χ_{a,b}(t) = φ ((t - a) / (b - a))`. -/
def affineCutoff (φ : ℝ → ℝ) (a b t : ℝ) : ℝ := φ ((t - a) / (b - a))

/-- The LC31 annular cutoff `Φ(t) = χ_{-3/10,-1/5}(-t) · χ_{4/5,9/10}(t)`. -/
def annularCutoff (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  affineCutoff φ (-3 / 10) (-1 / 5) (-t) * affineCutoff φ (4 / 5) (9 / 10) t

theorem annularCutoff_eq (φ : ℝ → ℝ) (t : ℝ) :
    annularCutoff φ t = φ (3 - 10 * t) * φ (10 * t - 8) := by
  unfold annularCutoff affineCutoff
  congr 2 <;> ring

/-- The standard profile `t ↦ smoothTransition (1 - t)`. -/
def cutoffProfile (t : ℝ) : ℝ := Real.smoothTransition (1 - t)

theorem cutoffProfile_contDiff : ContDiff ℝ ∞ cutoffProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem cutoffProfile_mem_Icc (t : ℝ) : cutoffProfile t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoffProfile_eq_one {t : ℝ} (ht : t ≤ 0) : cutoffProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoffProfile_eq_zero {t : ℝ} (ht : 1 ≤ t) : cutoffProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoffProfile_antitone : Antitone cutoffProfile :=
  fun _ _ h => Real.smoothTransition.monotone (by linarith)

variable {φ : ℝ → ℝ}

theorem annularCutoff_contDiff (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (annularCutoff φ) := by
  have h : annularCutoff φ = fun t => φ (3 - 10 * t) * φ (10 * t - 8) :=
    funext (annularCutoff_eq φ)
  rw [h]
  exact (hφ.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).mul
    (hφ.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem annularCutoff_mem_Icc (hrange : ∀ t, φ t ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    annularCutoff φ t ∈ Icc (0 : ℝ) 1 := by
  rw [annularCutoff_eq]
  obtain ⟨h1, h2⟩ := hrange (3 - 10 * t)
  obtain ⟨h3, h4⟩ := hrange (10 * t - 8)
  exact ⟨mul_nonneg h1 h3, by nlinarith⟩

theorem annularCutoff_eq_zero_of_le (hzero : ∀ t, 1 ≤ t → φ t = 0) {t : ℝ} (ht : t ≤ 1 / 5) :
    annularCutoff φ t = 0 := by
  rw [annularCutoff_eq, hzero _ (by linarith), zero_mul]

theorem annularCutoff_eq_zero_of_ge (hzero : ∀ t, 1 ≤ t → φ t = 0) {t : ℝ} (ht : 9 / 10 ≤ t) :
    annularCutoff φ t = 0 := by
  rw [annularCutoff_eq, hzero (10 * t - 8) (by linarith), mul_zero]

theorem annularCutoff_eq_one (hone : ∀ t, t ≤ 0 → φ t = 1) {t : ℝ}
    (ht : t ∈ Icc (3 / 10 : ℝ) (4 / 5)) : annularCutoff φ t = 1 := by
  rw [annularCutoff_eq, hone _ (by linarith [ht.1]), hone _ (by linarith [ht.2]), mul_one]

theorem annularCutoff_eq_zero_of_not_mem (hzero : ∀ t, 1 ≤ t → φ t = 0) {t : ℝ}
    (ht : t ∉ Ioo (1 / 5 : ℝ) (9 / 10)) : annularCutoff φ t = 0 := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
  rcases ht with ht | ht
  · exact annularCutoff_eq_zero_of_le hzero ht
  · exact annularCutoff_eq_zero_of_ge hzero ht

theorem hasCompactSupport_annularCutoff (hzero : ∀ t, 1 ≤ t → φ t = 0) :
    HasCompactSupport (annularCutoff φ) :=
  HasCompactSupport.intro (isCompact_Icc (a := (1 / 5 : ℝ)) (b := 9 / 10)) fun _ ht =>
    annularCutoff_eq_zero_of_not_mem hzero fun h => ht (Ioo_subset_Icc_self h)

/-- The finite derivative bound `L_Φ`. -/
theorem exists_abs_deriv_annularCutoff_le (hφ : ContDiff ℝ ∞ φ) (hzero : ∀ t, 1 ≤ t → φ t = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, |deriv (annularCutoff φ) t| ≤ L := by
  obtain ⟨C, hC⟩ := ((annularCutoff_contDiff hφ).continuous_deriv (by simp)).bounded_above_of_compact_support
    (hasCompactSupport_annularCutoff hzero).deriv
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

end DifferentialGeometry.Analysis.Calculus
