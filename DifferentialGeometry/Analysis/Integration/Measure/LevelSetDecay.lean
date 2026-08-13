import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Measure

variable {X : Type*} [MeasurableSpace X]

theorem level_set_decay_iterate
    (μ : Measure X)
    {levelSet : ℝ → Set X} {step ratio : ℝ}
    (hstep : 0 < step)
    (hdecay : ∀ level : ℝ, 0 < level →
      μ (levelSet (level + step)) ≤
        ENNReal.ofReal ratio * μ (levelSet level))
    (level : ℝ) (hlevel : 0 < level) (n : ℕ) :
    μ (levelSet (level + n * step)) ≤
      ENNReal.ofReal ratio ^ n * μ (levelSet level) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hlevel_n : 0 < level + n * step := by positivity
      have hone :
          μ (levelSet (level + ((n : ℝ) + 1) * step)) ≤
            ENNReal.ofReal ratio * μ (levelSet (level + n * step)) := by
        have h := hdecay (level + (n : ℝ) * step) hlevel_n
        simpa only [add_mul, one_mul, add_assoc] using h
      simpa only [Nat.cast_succ] using
        (calc
          μ (levelSet (level + ((n : ℝ) + 1) * step))
              ≤ ENNReal.ofReal ratio * μ (levelSet (level + (n : ℝ) * step)) := hone
          _ ≤ ENNReal.ofReal ratio *
              (ENNReal.ofReal ratio ^ n * μ (levelSet level)) := by
            gcongr
          _ = ENNReal.ofReal ratio ^ (n + 1) * μ (levelSet level) := by
            ring)

theorem ennreal_of_real_pow (ratio : ℝ) (hratio : 0 ≤ ratio) (n : ℕ) :
    ENNReal.ofReal ratio ^ n = ENNReal.ofReal (ratio ^ n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, ← ENNReal.ofReal_mul (pow_nonneg hratio n)]

theorem geometric_decay_exponential_bound
    (ratio level step : ℝ)
    (hratio_pos : 0 < ratio) (hratio_lt : ratio < 1)
    (n : ℕ) (hn : level / step - 1 ≤ n) :
    ENNReal.ofReal (ratio ^ n) ≤
      ENNReal.ofReal (1 / ratio) *
        ENNReal.ofReal
          (Real.exp (-level * (-Real.log ratio / step))) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [show (ratio ^ n : ℝ) = ratio ^ (n : ℝ) from by rw [Real.rpow_natCast]]
  have hone : ratio ^ (n : ℝ) ≤ ratio ^ (level / step - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hratio_pos (le_of_lt hratio_lt) hn
  have htwo :
      ratio ^ (level / step - 1) =
        1 / ratio * Real.exp (-level * (-Real.log ratio / step)) := by
    rw [Real.rpow_def_of_pos hratio_pos]
    have hinv : (1 : ℝ) / ratio = Real.exp (-Real.log ratio) := by
      rw [Real.exp_neg, Real.exp_log hratio_pos, one_div]
    rw [hinv, ← Real.exp_add]
    congr 1
    ring
  linarith

theorem level_set_exponential_decay
    (μ : Measure X)
    {base : Set X} {levelSet : ℝ → Set X}
    (hsub : ∀ level, levelSet level ⊆ base)
    {step : ℝ} (hstep : 0 < step)
    {ratio : ℝ} (hratio_pos : 0 < ratio) (hratio_lt : ratio < 1)
    (hdecay : ∀ level : ℝ, 0 < level →
      μ (levelSet (level + step)) ≤
        ENNReal.ofReal ratio * μ (levelSet level)) :
    ∀ level : ℝ, 0 < level →
      μ (levelSet level) ≤
        ENNReal.ofReal (1 / ratio) * μ base *
          ENNReal.ofReal
            (Real.exp (-level * (-Real.log ratio / step))) := by
  intro level hlevel
  have hquotient : 0 < level / step := div_pos hlevel hstep
  have hceil : 1 ≤ ⌈level / step⌉₊ := Nat.ceil_pos.mpr hquotient
  let n := ⌈level / step⌉₊ - 1
  let level₀ := level - n * step
  have hlevel₀ : 0 < level₀ := by
    have hn_lt : (n : ℝ) < level / step := by
      dsimp only [n]
      rw [Nat.cast_sub hceil]
      push_cast
      linarith [Nat.ceil_lt_add_one (le_of_lt hquotient)]
    have hmul := mul_lt_mul_of_pos_right hn_lt hstep
    rw [div_mul_cancel₀] at hmul
    · dsimp only [level₀]
      linarith
    · exact ne_of_gt hstep
  have hlevel_eq : level₀ + n * step = level := by
    dsimp only [level₀]
    ring
  have hiter := level_set_decay_iterate μ hstep hdecay level₀ hlevel₀ n
  rw [hlevel_eq] at hiter
  have hbase : μ (levelSet level₀) ≤ μ base := measure_mono (hsub level₀)
  have hn_ge : level / step - 1 ≤ (n : ℝ) := by
    dsimp only [n]
    rw [Nat.cast_sub hceil]
    push_cast
    linarith [Nat.le_ceil (level / step)]
  calc
    μ (levelSet level) ≤
        ENNReal.ofReal ratio ^ n * μ (levelSet level₀) := hiter
    _ ≤ ENNReal.ofReal ratio ^ n * μ base := by
      gcongr
    _ = ENNReal.ofReal (ratio ^ n) * μ base := by
      rw [ennreal_of_real_pow ratio (le_of_lt hratio_pos) n]
    _ ≤ (ENNReal.ofReal (1 / ratio) *
          ENNReal.ofReal
            (Real.exp (-level * (-Real.log ratio / step)))) * μ base := by
      gcongr
      exact geometric_decay_exponential_bound
        ratio level step hratio_pos hratio_lt n hn_ge
    _ = ENNReal.ofReal (1 / ratio) * μ base *
        ENNReal.ofReal
          (Real.exp (-level * (-Real.log ratio / step))) := by
      ring

theorem level_set_exponential_decay_from_base
    (μ : Measure X)
    {base : Set X} {levelSet : ℝ → Set X}
    (hsub : ∀ level, levelSet level ⊆ base)
    {step : ℝ} (hstep : 0 < step)
    {ratio : ℝ} (hratio_pos : 0 < ratio) (hratio_lt : ratio < 1)
    (hdecay : ∀ level : ℝ, step ≤ level →
      μ (levelSet (level + step)) ≤
        ENNReal.ofReal ratio * μ (levelSet level))
    (level : ℝ) :
    μ (levelSet level) ≤
      ENNReal.ofReal (1 / ratio ^ 2) * μ base *
        ENNReal.ofReal
          (Real.exp (-level * (-Real.log ratio / step))) := by
  let shifted : ℝ → Set X := fun s => levelSet (s + step)
  have hshifted_sub : ∀ s, shifted s ⊆ base := by
    intro s
    exact hsub (s + step)
  have hshifted_decay : ∀ s : ℝ, 0 < s →
      μ (shifted (s + step)) ≤
        ENNReal.ofReal ratio * μ (shifted s) := by
    intro s hs
    have hs_step : step ≤ s + step := by linarith
    simpa only [shifted, add_assoc] using hdecay (s + step) hs_step
  have hmain := level_set_exponential_decay μ hshifted_sub hstep
    hratio_pos hratio_lt hshifted_decay
  have hstep_rate : step * (-Real.log ratio / step) = -Real.log ratio := by
    field_simp [hstep.ne']
  have hexp_step :
      Real.exp (-step * (-Real.log ratio / step)) = ratio := by
    have harg : -step * (-Real.log ratio / step) = Real.log ratio := by
      calc
        -step * (-Real.log ratio / step) =
            -(step * (-Real.log ratio / step)) := by ring
        _ = -(-Real.log ratio) := by rw [hstep_rate]
        _ = Real.log ratio := by ring
    rw [harg, Real.exp_log hratio_pos]
  by_cases hstep_level : step < level
  · have hpositive : 0 < level - step := by linarith
    have hbound :
        μ (levelSet level) ≤
          ENNReal.ofReal (1 / ratio) * μ base *
            ENNReal.ofReal
              (Real.exp (-(level - step) *
                (-Real.log ratio / step))) := by
      simpa only [shifted, sub_add_cancel] using hmain (level - step) hpositive
    have hexp_shift :
        Real.exp (-(level - step) * (-Real.log ratio / step)) =
          (1 / ratio) *
            Real.exp (-level * (-Real.log ratio / step)) := by
      have hinv : (1 / ratio : ℝ) = Real.exp (-Real.log ratio) := by
        rw [Real.exp_neg, Real.exp_log hratio_pos, one_div]
      rw [hinv, ← Real.exp_add]
      congr 1
      calc
        -(level - step) * (-Real.log ratio / step) =
            -level * (-Real.log ratio / step) +
              step * (-Real.log ratio / step) := by ring
        _ = -level * (-Real.log ratio / step) +
              (-Real.log ratio) := by rw [hstep_rate]
        _ = -Real.log ratio +
              -level * (-Real.log ratio / step) := by ring
    calc
      μ (levelSet level) ≤
          ENNReal.ofReal (1 / ratio) * μ base *
            ENNReal.ofReal
              (Real.exp (-(level - step) *
                (-Real.log ratio / step))) := hbound
      _ = ENNReal.ofReal (1 / ratio ^ 2) * μ base *
          ENNReal.ofReal
            (Real.exp (-level * (-Real.log ratio / step))) := by
        rw [hexp_shift, ENNReal.ofReal_mul (by positivity)]
        calc
          ENNReal.ofReal (1 / ratio) * μ base *
              (ENNReal.ofReal (1 / ratio) *
                ENNReal.ofReal
                  (Real.exp (-level * (-Real.log ratio / step)))) =
              (ENNReal.ofReal (1 / ratio) *
                ENNReal.ofReal (1 / ratio)) * μ base *
                  ENNReal.ofReal
                    (Real.exp (-level * (-Real.log ratio / step))):= by
            ring
          _ = ENNReal.ofReal ((1 / ratio) * (1 / ratio)) * μ base *
                ENNReal.ofReal
                  (Real.exp (-level * (-Real.log ratio / step))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (1 / ratio ^ 2) * μ base *
                ENNReal.ofReal
                  (Real.exp (-level * (-Real.log ratio / step))) := by
            congr 1
            field_simp [pow_two, hratio_pos.ne']
  · have hlevel_le : level ≤ step := le_of_not_gt hstep_level
    have hmeasure : μ (levelSet level) ≤ μ base := measure_mono (hsub level)
    have hrate : 0 < -Real.log ratio / step := by
      have hlog : Real.log ratio < 0 := Real.log_neg hratio_pos hratio_lt
      exact div_pos (by linarith) hstep
    have hexp_lower :
        ratio ≤ Real.exp (-level * (-Real.log ratio / step)) := by
      have harg :
          -step * (-Real.log ratio / step) ≤
            -level * (-Real.log ratio / step) := by
        nlinarith [hlevel_le, le_of_lt hrate]
      calc
        ratio = Real.exp (-step * (-Real.log ratio / step)) := by
          rw [hexp_step]
        _ ≤ Real.exp (-level * (-Real.log ratio / step)) :=
          Real.exp_le_exp.2 harg
    have hone : 1 ≤ (1 / ratio ^ 2) * ratio := by
      rw [pow_two]
      field_simp [hratio_pos.ne']
      linarith
    have hcoefficient :
        1 ≤ (1 / ratio ^ 2) *
          Real.exp (-level * (-Real.log ratio / step)) := by
      calc
        1 ≤ (1 / ratio ^ 2) * ratio := hone
        _ ≤ (1 / ratio ^ 2) *
            Real.exp (-level * (-Real.log ratio / step)) := by
          gcongr
    calc
      μ (levelSet level) ≤ μ base := hmeasure
      _ = ENNReal.ofReal 1 * μ base := by simp
      _ ≤ ENNReal.ofReal
            ((1 / ratio ^ 2) *
              Real.exp (-level * (-Real.log ratio / step))) * μ base := by
        gcongr
      _ = ENNReal.ofReal (1 / ratio ^ 2) * μ base *
          ENNReal.ofReal
            (Real.exp (-level * (-Real.log ratio / step))) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring

theorem level_set_exponential_decay_from_base_real
    (μ : Measure X) [IsFiniteMeasure μ]
    {base : Set X} {levelSet : ℝ → Set X}
    (hsub : ∀ level, levelSet level ⊆ base)
    {step : ℝ} (hstep : 0 < step)
    {ratio : ℝ} (hratio_pos : 0 < ratio) (hratio_lt : ratio < 1)
    (hdecay : ∀ level : ℝ, step ≤ level →
      μ (levelSet (level + step)) ≤
        ENNReal.ofReal ratio * μ (levelSet level))
    (level : ℝ) :
    μ (levelSet level) ≤
      ENNReal.ofReal
        ((1 / ratio ^ 2 * μ.real base) *
          Real.exp (-level * (-Real.log ratio / step))) := by
  have hbound := level_set_exponential_decay_from_base μ hsub hstep
    hratio_pos hratio_lt hdecay level
  have hbase : μ base = ENNReal.ofReal (μ.real base) := by
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ base)]
  have hbase_nonneg : 0 ≤ μ.real base := ENNReal.toReal_nonneg
  calc
    μ (levelSet level) ≤
        ENNReal.ofReal (1 / ratio ^ 2) * μ base *
          ENNReal.ofReal
            (Real.exp (-level * (-Real.log ratio / step))) := hbound
    _ = ENNReal.ofReal
        ((1 / ratio ^ 2 * μ.real base) *
          Real.exp (-level * (-Real.log ratio / step))) := by
      rw [hbase, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul
          (mul_nonneg (by positivity) hbase_nonneg)]

end DifferentialGeometry.Analysis.Measure

end
