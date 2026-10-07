import DifferentialGeometry.Analysis.Calculus.SmoothMonotoneInterpolation
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-! # HPS04: the fixed plateau function and dyadic windows

Contract: `master207A.tex`, HPS04--05, lines 17441--17590, and CH12-R1
section 5.2, at `032e54fd8`. Thresholds are combined by a maximum; permitted
errors by a minimum. The interpolation has plateaus before 7/4 and after 15/8.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace GC.LongTime.Ch12

/-- The single interpolation used on every dyadic window. -/
theorem exists_smoothingTheta_CX5 :
    ∃ (θ : ℝ → ℝ) (B : ℝ), 0 < B ∧ ContDiff ℝ ∞ θ ∧ Monotone θ ∧
      (∀ s, θ s ∈ Icc (0 : ℝ) 1) ∧
      (∀ s, s ≤ 7 / 4 → θ s = 0) ∧
      (∀ s, 15 / 8 ≤ s → θ s = 1) ∧
      ∀ s, |deriv θ s| ≤ B := by
  obtain ⟨C, hC, hstep⟩ := DifferentialGeometry.Analysis.exists_uniform_smooth_interval_step
  obtain ⟨θ, hs, hm, hr, h0, h1, hd⟩ := hstep (7 / 4) (15 / 8) (by norm_num)
  refine ⟨θ, 8 * C, by positivity, hs, hm, hr, h0, h1, ?_⟩
  intro s
  convert hd s using 1
  ring

/-- The times are exactly `2^j T`; no monotonicity of an unrelated slice sequence
is used. -/
def dyadicTime_CX5 (T : ℝ) (j : ℕ) : ℝ := 2 ^ j * T

@[simp] theorem dyadicTime_zero_CX5 (T : ℝ) : dyadicTime_CX5 T 0 = T := by
  simp [dyadicTime_CX5]

theorem dyadicTime_succ_CX5 (T : ℝ) (j : ℕ) :
    dyadicTime_CX5 T (j + 1) = 2 * dyadicTime_CX5 T j := by
  simp only [dyadicTime_CX5, pow_succ]
  ring

theorem dyadicTime_pos_CX5 {T : ℝ} (hT : 0 < T) (j : ℕ) :
    0 < dyadicTime_CX5 T j := by
  unfold dyadicTime_CX5
  positivity

theorem dyadicTime_strictMono_CX5 {T : ℝ} (hT : 0 < T) :
    StrictMono (dyadicTime_CX5 T) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [dyadicTime_succ_CX5]
  linarith [dyadicTime_pos_CX5 hT j]

theorem dyadicTime_tendsto_CX5 {T : ℝ} (hT : 0 < T) :
    Tendsto (dyadicTime_CX5 T) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hT

/-- A selector for the half-open windows. The value before the first window is
irrelevant to the late-time statements. -/
def dyadicIndex_CX5 (T t : ℝ) : ℕ := by
  classical
  exact if h : ∃ j, t ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))
    then h.choose else 0

theorem dyadicIndex_mem_CX5 {T t : ℝ} (hT : 0 < T) (ht : T ≤ t) :
    t ∈ Ico (dyadicTime_CX5 T (dyadicIndex_CX5 T t))
      (dyadicTime_CX5 T (dyadicIndex_CX5 T t + 1)) := by
  have hex : ∃ j, t ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) := by
    obtain ⟨j, _, hj⟩ := DifferentialGeometry.Analysis.exists_mem_Ico_of_tendsto_atTop
      (dyadicTime_strictMono_CX5 hT).monotone (dyadicTime_tendsto_CX5 hT) 0
      (by simpa using ht)
    exact ⟨j, hj⟩
  simpa only [dyadicIndex_CX5, dite_eq_left hex] using hex.choose_spec

theorem dyadicIndex_eq_CX5 {T t : ℝ} (hT : 0 < T) {j : ℕ}
    (ht : t ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))) :
    dyadicIndex_CX5 T t = j := by
  have hm := dyadicTime_strictMono_CX5 hT
  have hstart : T ≤ t := calc
    T = dyadicTime_CX5 T 0 := by simp
    _ ≤ dyadicTime_CX5 T j := hm.monotone (Nat.zero_le j)
    _ ≤ t := ht.1
  have hs := dyadicIndex_mem_CX5 hT hstart
  apply le_antisymm
  · by_contra h
    have hj : j + 1 ≤ dyadicIndex_CX5 T t := by omega
    exact (not_lt_of_ge ((hm.monotone hj).trans hs.1)) ht.2
  · by_contra h
    have hj : dyadicIndex_CX5 T t + 1 ≤ j := by omega
    exact (not_lt_of_ge ((hm.monotone hj).trans ht.1)) hs.2

theorem dyadicTime_add_CX5 (T : ℝ) (N j : ℕ) :
    dyadicTime_CX5 (dyadicTime_CX5 T N) j = dyadicTime_CX5 T (N + j) := by
  simp only [dyadicTime_CX5, pow_add]
  ring

theorem le_dyadicIndex_CX5 {T t : ℝ} (hT : 0 < T) (N : ℕ)
    (ht : dyadicTime_CX5 T N ≤ t) : N ≤ dyadicIndex_CX5 T t := by
  have hm := (dyadicTime_strictMono_CX5 hT).monotone
  have hs : T ≤ t := calc
    T = dyadicTime_CX5 T 0 := by simp
    _ ≤ dyadicTime_CX5 T N := hm (Nat.zero_le N)
    _ ≤ t := ht
  have hj := dyadicIndex_mem_CX5 hT hs
  by_contra h
  have hn : dyadicIndex_CX5 T t + 1 ≤ N := by omega
  exact (not_lt_of_ge ((hm hn).trans ht)) hj.2

/-- The dyadic selector tends to infinity with physical time. -/
theorem dyadicIndex_tendsto_CX5 {T : ℝ} (hT : 0 < T) :
    Tendsto (dyadicIndex_CX5 T) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop (dyadicTime_CX5 T N)] with t ht
  exact le_dyadicIndex_CX5 hT N ht

/-- Turn the H1 isotopy bounds tending to zero into a uniform late-time speed
margin. Taking `η j = 1/m(j)` gives HPS04's `4*B/m(j)` factor. -/
theorem eventually_dyadic_speed_margin_CX5 {T : ℝ} (hT : 0 < T) (B : ℝ)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, T < S ∧ ∀ t : ℝ, S ≤ t → 4 * B * η (dyadicIndex_CX5 T t) < ε := by
  have hlim : Tendsto (fun t => 4 * B * η (dyadicIndex_CX5 T t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul (hη.comp (dyadicIndex_tendsto_CX5 hT))
  obtain ⟨S, hS⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨max S (T + 1), ?_, fun t ht => hS t ((le_max_left _ _).trans ht)⟩
  linarith [le_max_right S (T + 1)]

end GC.LongTime.Ch12
