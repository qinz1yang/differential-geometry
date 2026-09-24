import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ScalarThreshold

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

def widthComparisonBound (T W : ℝ) (t : ℝ) : ℝ :=
  W * ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) +
    2 * Real.pi * (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) -
      2 * Real.pi * (4 * t + 1)

private theorem widthComparisonBound_factor {T W t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    widthComparisonBound T W t =
      (4 * t + 1) ^ (3 / 4 : ℝ) *
        (W * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ + 2 * Real.pi * (4 * T + 1) ^ (1 / 4 : ℝ) -
          2 * Real.pi * (4 * t + 1) ^ (1 / 4 : ℝ)) := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  have hd14 : (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) = 4 * t + 1 := by
    rw [← Real.rpow_add hd]
    norm_num
  have hdiv : ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) =
      (4 * t + 1) ^ (3 / 4 : ℝ) * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [Real.div_rpow hd.le hc.le, div_eq_mul_inv]
  rw [widthComparisonBound, hdiv]
  set A := (4 * t + 1) ^ (3 / 4 : ℝ)
  set B := (4 * t + 1) ^ (1 / 4 : ℝ)
  set C := ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹
  set E := (4 * T + 1) ^ (1 / 4 : ℝ)
  have hAB : A * B = 4 * t + 1 := hd14
  rw [← hAB]
  ring

private theorem widthComparisonBound_slope {T W t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    -2 * Real.pi + 3 / (1 + 4 * t) * widthComparisonBound T W t =
      W * (3 * ((4 * t + 1) ^ (1 / 4 : ℝ))⁻¹ * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹) +
        2 * Real.pi * (3 * ((4 * t + 1) ^ (1 / 4 : ℝ))⁻¹) * (4 * T + 1) ^ (1 / 4 : ℝ) -
          8 * Real.pi := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  set A := (4 * t + 1) ^ (3 / 4 : ℝ) with hA
  set B := (4 * t + 1) ^ (1 / 4 : ℝ) with hB
  set C := ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ with hC
  set E := (4 * T + 1) ^ (1 / 4 : ℝ) with hE
  have hAB : A * B = 1 + 4 * t := by
    rw [hA, hB, ← Real.rpow_add hd]
    norm_num
    ring
  have hBne : B ≠ 0 := by
    rw [hB]
    exact (Real.rpow_pos_of_pos hd _).ne'
  have hAne : A ≠ 0 := by
    rw [hA]
    exact (Real.rpow_pos_of_pos hd _).ne'
  have hbc : widthComparisonBound T W t = A * (W * C + 2 * Real.pi * E - 2 * Real.pi * B) := by
    rw [widthComparisonBound_factor hT ht, ← hA, ← hB, ← hC, ← hE]
  refine mul_left_cancel₀ hBne ?_
  have hABne : A * B ≠ 0 := by
    rw [hAB]
    positivity
  rw [hbc, ← hAB]
  field_simp [hAne, hBne]
  ring

theorem hasDerivAt_widthComparisonBound {T W t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    HasDerivAt (widthComparisonBound T W)
      (-2 * Real.pi + 3 / (1 + 4 * t) * widthComparisonBound T W t) t := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  set B := (4 * t + 1) ^ (1 / 4 : ℝ) with hB
  set C := ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ with hC
  set E := (4 * T + 1) ^ (1 / 4 : ℝ) with hE
  have hlin : HasDerivAt (fun s : ℝ => 4 * s + 1) 4 t := by
    simpa using ((hasDerivAt_id t).const_mul (4 : ℝ)).const_add (1 : ℝ)
  have hpow : HasDerivAt (fun s : ℝ => (4 * s + 1) ^ (3 / 4 : ℝ)) (3 * B⁻¹) t := by
    have h := (Real.hasDerivAt_rpow_const (x := 4 * t + 1) (p := (3 / 4 : ℝ))
      (Or.inl hd.ne')).comp t hlin
    refine h.congr_deriv ?_
    rw [show ((3 : ℝ) / 4 - 1) = -(1 / 4) by norm_num, Real.rpow_neg hd.le, hB]
    ring
  have h1 : HasDerivAt (fun s : ℝ => W * ((4 * s + 1) ^ (3 / 4 : ℝ) * C))
      (W * (3 * B⁻¹ * C)) t := by
    have := (hpow.mul_const C).const_mul W
    simpa only [mul_assoc] using this
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.pi * (4 * s + 1) ^ (3 / 4 : ℝ) * E)
      (2 * Real.pi * (3 * B⁻¹) * E) t := by
    have := (hpow.const_mul (2 * Real.pi)).mul_const E
    simpa only [mul_assoc] using this
  have h3 : HasDerivAt (fun s : ℝ => 2 * Real.pi * (4 * s + 1)) (8 * Real.pi) t := by
    have h := hlin.const_mul (2 * Real.pi)
    have hval : 2 * Real.pi * 4 = 8 * Real.pi := by ring
    rwa [hval] at h
  have hD := (h1.add h2).sub h3
  have hfun : widthComparisonBound T W =ᶠ[𝓝 t]
      (fun s : ℝ => W * ((4 * s + 1) ^ (3 / 4 : ℝ) * C) +
        2 * Real.pi * (4 * s + 1) ^ (3 / 4 : ℝ) * E - 2 * Real.pi * (4 * s + 1)) := by
    filter_upwards [eventually_gt_nhds (show (-(1 : ℝ) / 4) < t by linarith)] with s hs
    have hs' : 0 < 4 * s + 1 := by linarith
    rw [widthComparisonBound, Real.div_rpow hs'.le hc.le, div_eq_mul_inv, ← hC, ← hE]
  refine (hD.congr_of_eventuallyEq hfun).congr_deriv ?_
  exact (widthComparisonBound_slope hT ht).symm

theorem widthComparisonBound_self {T W : ℝ} (hT : 0 ≤ T) :
    widthComparisonBound T W T = W := by
  have hc : 0 < 4 * T + 1 := by linarith
  have hdiv : (4 * T + 1) / (4 * T + 1) = (1 : ℝ) := by field_simp
  have h34 : (4 * T + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) = 4 * T + 1 := by
    rw [← Real.rpow_add hc]
    norm_num
  rw [widthComparisonBound, hdiv, Real.one_rpow, mul_one]
  have hmid : 2 * Real.pi * (4 * T + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) =
      2 * Real.pi * (4 * T + 1) := by
    rw [mul_assoc, h34]
  rw [hmid]
  ring

theorem widthComparisonBound_mono_width {T t W W' : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t)
    (h : W ≤ W') : widthComparisonBound T W t ≤ widthComparisonBound T W' t := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  have hpow : 0 ≤ ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (div_nonneg hd.le hc.le) _
  have hmul := mul_le_mul_of_nonneg_right h hpow
  unfold widthComparisonBound
  linarith

theorem widthComparisonBound_neg_iff_extinctionThreshold_lt {T W t : ℝ} (hT : 0 ≤ T)
    (hW : 0 ≤ W) (hTt : T ≤ t) :
    widthComparisonBound T W t < 0 ↔
      extinctionThreshold (4 * T + 1) (4 * W) < 4 * (t - T) := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  have hC : 0 ≤ 4 * W := by linarith
  have hH : 0 ≤ 4 * (t - T) := by linarith
  have hsum : 4 * (t - T) + (4 * T + 1) = 4 * t + 1 := by ring
  set A := (4 * t + 1) ^ (3 / 4 : ℝ) with hA
  set B := (4 * t + 1) ^ (1 / 4 : ℝ) with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos hd _
  set X := W * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ + 2 * Real.pi * (4 * T + 1) ^ (1 / 4 : ℝ) -
    2 * Real.pi * B with hX
  have hsplit : (4 * W) / (4 * T + 1) ^ (3 / 4 : ℝ) =
      4 * (W * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹) := by
    rw [div_eq_mul_inv]
    ring
  have hright : (4 * W) / (4 * T + 1) ^ (3 / 4 : ℝ) -
      8 * Real.pi * (B - (4 * T + 1) ^ (1 / 4 : ℝ)) = 4 * X := by
    rw [hsplit, hX]
    ring
  have hleft : A * X < 0 ↔ X < 0 := by
    constructor
    · intro h
      by_contra hx
      have := mul_nonneg hApos.le (le_of_not_gt hx)
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg hApos h
  have hright' : 4 * X < 0 ↔ X < 0 := by
    constructor
    · intro h
      by_contra hx
      have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (le_of_not_gt hx)
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg (by norm_num) h
  rw [show widthComparisonBound T W t = A * X from by
    rw [widthComparisonBound_factor hT (by linarith), hA, hX, hB]]
  rw [extinctionThreshold_lt_iff hc hC hH, hsum, hright, hleft, hright']

theorem widthComparisonBound_zero (t : ℝ) :
    widthComparisonBound 0 0 t = 2 * Real.pi * (4 * t + 1) ^ (3 / 4 : ℝ) -
      2 * Real.pi * (4 * t + 1) := by
  rw [widthComparisonBound]
  simp only [mul_zero, zero_mul, zero_add, div_one, Real.one_rpow, mul_one]

theorem widthComparisonBound_zero_self {T : ℝ} (hT : 0 ≤ T) : widthComparisonBound T 0 T = 0 := by
  rw [widthComparisonBound_self hT]

theorem widthComparisonBound_zero_zero_neg_iff {t : ℝ} (ht : 0 ≤ t) :
    widthComparisonBound 0 0 t < 0 ↔ 0 < t := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hone : (1 : ℝ) < (4 * t + 1) ^ (1 / 4 : ℝ) ↔ 0 < t := by
    constructor
    · intro h
      by_contra hle
      have ht0 : t = 0 := le_antisymm (not_lt.mp hle) ht
      rw [ht0] at h
      norm_num at h
    · intro h
      exact Real.one_lt_rpow (by linarith) (by norm_num)
  have h34 : (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) = 4 * t + 1 := by
    rw [← Real.rpow_add hd]
    norm_num
  have hfac : widthComparisonBound 0 0 t =
      2 * Real.pi * (4 * t + 1) ^ (3 / 4 : ℝ) * (1 - (4 * t + 1) ^ (1 / 4 : ℝ)) := by
    rw [widthComparisonBound_zero]
    have hmid : 2 * Real.pi * (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) =
        2 * Real.pi * (4 * t + 1) := by
      rw [mul_assoc, h34]
    linarith [hmid]
  have hpos : 0 < 2 * Real.pi * (4 * t + 1) ^ (3 / 4 : ℝ) := by positivity
  have hmul : 2 * Real.pi * (4 * t + 1) ^ (3 / 4 : ℝ) * (1 - (4 * t + 1) ^ (1 / 4 : ℝ)) < 0 ↔
      1 - (4 * t + 1) ^ (1 / 4 : ℝ) < 0 := by
    constructor
    · intro h
      by_contra hx
      exact absurd (mul_nonneg hpos.le (le_of_not_gt hx)) (not_le.mpr h)
    · intro h
      exact mul_neg_of_pos_of_neg hpos h
  rw [hfac, hmul, sub_neg]
  exact hone

theorem exists_widthComparisonBound_neg {T W : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W) :
    ∃ t : ℝ, T < t ∧ widthComparisonBound T W t < 0 := by
  have hc : 0 < 4 * T + 1 := by linarith
  have hC : 0 ≤ 4 * W := by linarith
  have hθ : 0 ≤ extinctionThreshold (4 * T + 1) (4 * W) := extinctionThreshold_nonneg hc hC
  refine ⟨T + (extinctionThreshold (4 * T + 1) (4 * W) + 1) / 4, by linarith, ?_⟩
  rw [widthComparisonBound_neg_iff_extinctionThreshold_lt hT hW (by linarith)]
  linarith

theorem eventually_widthComparisonBound_neg {T W : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, widthComparisonBound T W t < 0 := by
  have hc : 0 < 4 * T + 1 := by linarith
  have hC : 0 ≤ 4 * W := by linarith
  have hθ : 0 ≤ extinctionThreshold (4 * T + 1) (4 * W) := extinctionThreshold_nonneg hc hC
  refine Eventually.mono
    (eventually_ge_atTop (T + (extinctionThreshold (4 * T + 1) (4 * W) + 1) / 4))
    fun t ht => ?_
  rw [widthComparisonBound_neg_iff_extinctionThreshold_lt hT hW (by linarith)]
  linarith

theorem le_of_le_widthComparisonBound {T W₁ W t : ℝ} (hT : 0 ≤ T) (hW₁ : 0 ≤ W₁)
    (hTt : T ≤ t) (h0 : 0 ≤ W) (hle : W ≤ widthComparisonBound T W₁ t) :
    t ≤ T + extinctionThreshold (4 * T + 1) (4 * W₁) / 4 := by
  by_contra hcon
  have hlt : extinctionThreshold (4 * T + 1) (4 * W₁) < 4 * (t - T) := by linarith
  have := (widthComparisonBound_neg_iff_extinctionThreshold_lt hT hW₁ hTt).mpr hlt
  linarith

def widthNormalized (T : ℝ) (W : ℝ → ℝ) (z : ℝ) : ℝ :=
  W z * (4 * z + 1) ^ (-(3 / 4) : ℝ) +
    2 * Real.pi * ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * T + 1) ^ (1 / 4 : ℝ))

theorem widthNormalized_self (T : ℝ) (W : ℝ → ℝ) :
    widthNormalized T W T = W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) := by
  rw [widthNormalized]
  ring

private theorem hasDerivAt_widthNormalizationFactor {x : ℝ} (hx : 0 < 4 * x + 1) :
    HasDerivAt (fun z : ℝ => (4 * z + 1) ^ (-(3 / 4) : ℝ))
      (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) x := by
  have hlin : HasDerivAt (fun z : ℝ => 4 * z + 1) 4 x := by
    simpa using ((hasDerivAt_id x).const_mul (4 : ℝ)).const_add (1 : ℝ)
  have h := (Real.hasDerivAt_rpow_const (x := 4 * x + 1) (p := (-(3 / 4) : ℝ))
    (Or.inl hx.ne')).comp x hlin
  refine h.congr_deriv ?_
  rw [show -((3 : ℝ) / 4) - 1 = -(7 / 4) by norm_num]
  ring

private theorem hasDerivAt_widthGrowthFactor {x : ℝ} (hx : 0 < 4 * x + 1) :
    HasDerivAt (fun z : ℝ => (4 * z + 1) ^ (1 / 4 : ℝ))
      ((4 * x + 1) ^ (-(3 / 4) : ℝ)) x := by
  have hlin : HasDerivAt (fun z : ℝ => 4 * z + 1) 4 x := by
    simpa using ((hasDerivAt_id x).const_mul (4 : ℝ)).const_add (1 : ℝ)
  have h := (Real.hasDerivAt_rpow_const (x := 4 * x + 1) (p := (1 / 4 : ℝ))
    (Or.inl hx.ne')).comp x hlin
  refine h.congr_deriv ?_
  rw [show ((1 : ℝ) / 4 - 1) = -(3 / 4) by norm_num]
  ring

def HasNonincreasingWidthNormalizationOn (T t : ℝ) (W : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ico T t, ∀ r, 0 < r →
    ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ *
      (widthNormalized T W z - widthNormalized T W x) < r

theorem continuousOn_widthNormalized {T t : ℝ} (hT : 0 ≤ T) {W : ℝ → ℝ}
    (hcont : ContinuousOn W (Icc T t)) :
    ContinuousOn (widthNormalized T W) (Icc T t) := by
  have hpos : ∀ z ∈ Icc T t, (0 : ℝ) < 4 * z + 1 := by
    intro z hz
    have := hz.1
    linarith
  have hlin : ContinuousOn (fun z : ℝ => 4 * z + 1) (Icc T t) := by fun_prop
  have h34 : ContinuousOn (fun z : ℝ => (4 * z + 1) ^ (-(3 / 4) : ℝ)) (Icc T t) :=
    hlin.rpow_const fun z hz => Or.inl (hpos z hz).ne'
  have h14 : ContinuousOn (fun z : ℝ => (4 * z + 1) ^ (1 / 4 : ℝ)) (Icc T t) :=
    hlin.rpow_const fun z hz => Or.inr (by norm_num)
  have hc14 : ContinuousOn (fun _ : ℝ => (4 * T + 1) ^ (1 / 4 : ℝ)) (Icc T t) :=
    continuousOn_const
  have hG : ContinuousOn (fun z : ℝ => 2 * Real.pi *
      ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * T + 1) ^ (1 / 4 : ℝ))) (Icc T t) :=
    continuousOn_const.mul (h14.sub hc14)
  unfold widthNormalized
  exact (hcont.mul h34).add hG

theorem le_widthComparisonBound_of_nonincreasing_normalization {T t : ℝ} {W : ℝ → ℝ}
    (hT : 0 ≤ T) (hTt : T ≤ t) (hcont : ContinuousOn W (Icc T t))
    (h : HasNonincreasingWidthNormalizationOn T t W) :
    W t ≤ widthComparisonBound T (W T) t := by
  have hconty := continuousOn_widthNormalized hT hcont
  have hgrön : widthNormalized T W t ≤ widthNormalized T W T := by
    have hmain := le_gronwallBound_of_liminf_deriv_right_le (f := widthNormalized T W)
      (f' := fun _ : ℝ => 0) (δ := widthNormalized T W T) (K := 0) (ε := 0)
      (a := T) (b := t) hconty
      (fun x hx r hr => h x hx r hr) le_rfl (fun x hx => by simp)
    have ht := hmain t ⟨hTt, le_rfl⟩
    simpa only [gronwallBound_K0, zero_mul, add_zero] using ht
  have hdT : (0 : ℝ) < 4 * t + 1 := by linarith
  have hdt : (0 : ℝ) < (4 * t + 1) ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hdT _
  have hkey : W t * (4 * t + 1) ^ (-(3 / 4) : ℝ) ≤
      W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) +
        2 * Real.pi * ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ)) := by
    have := hgrön
    rw [widthNormalized, widthNormalized_self T W] at this
    linarith
  have hident : (W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) +
      2 * Real.pi * ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ))) /
        (4 * t + 1) ^ (-(3 / 4) : ℝ) = widthComparisonBound T (W T) t := by
    have hcT : (0 : ℝ) < 4 * T + 1 := by linarith
    have hDT : (4 * T + 1) ^ (-(3 / 4) : ℝ) = ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ :=
      Real.rpow_neg hcT.le _
    have hDt : (4 * t + 1) ^ (-(3 / 4) : ℝ) = ((4 * t + 1) ^ (3 / 4 : ℝ))⁻¹ :=
      Real.rpow_neg hdT.le _
    have hprod : (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) = 4 * t + 1 := by
      rw [← Real.rpow_add hdT]
      norm_num
    have h1 : (4 * T + 1) ^ (-(3 / 4) : ℝ) / (4 * t + 1) ^ (-(3 / 4) : ℝ) =
        ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) := by
      rw [hDT, hDt, Real.div_rpow hdT.le hcT.le (3 / 4 : ℝ)]
      field_simp
    have h2 : ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ)) /
        (4 * t + 1) ^ (-(3 / 4) : ℝ) =
        (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) := by
      have key : ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ)) /
          ((4 * t + 1) ^ (3 / 4 : ℝ))⁻¹ =
          (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) -
            (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) := by
        field_simp
      rw [hDt, key, hprod]
    rw [add_div, mul_div_assoc, mul_div_assoc, h1, h2, widthComparisonBound]
    ring
  calc W t ≤ (W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) +
        2 * Real.pi * ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ))) /
          (4 * t + 1) ^ (-(3 / 4) : ℝ) := (le_div_iff₀ hdt).mpr hkey
    _ = widthComparisonBound T (W T) t := hident


private theorem widthNormalizationFactor_inv_mul {x : ℝ} (hx : 0 < 4 * x + 1) :
    3 / (1 + 4 * x) * (4 * x + 1) ^ (-(3 / 4) : ℝ) =
      3 * (4 * x + 1) ^ (-(7 / 4) : ℝ) := by
  have hid : 1 + 4 * x = 4 * x + 1 := by ring
  rw [hid, div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hx]
  norm_num

private theorem widthGrowthFactor_cancel {x : ℝ} (hx : 0 < 4 * x + 1) (Wx : ℝ) :
    (3 / (1 + 4 * x) * Wx - 2 * Real.pi) * (4 * x + 1) ^ (-(3 / 4) : ℝ) +
      Wx * (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) +
        2 * Real.pi * (4 * x + 1) ^ (-(3 / 4) : ℝ) = 0 := by
  have h : 3 / (1 + 4 * x) * Wx * (4 * x + 1) ^ (-(3 / 4) : ℝ) =
      Wx * (3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) := by
    rw [show 3 / (1 + 4 * x) * Wx * (4 * x + 1) ^ (-(3 / 4) : ℝ) =
        Wx * (3 / (1 + 4 * x) * (4 * x + 1) ^ (-(3 / 4) : ℝ)) by ring,
      widthNormalizationFactor_inv_mul hx]
  rw [sub_mul, h]
  ring

def HasWidthForwardDifferenceBoundOn (T t : ℝ) (W : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ico T t, ∀ r, 3 / (1 + 4 * x) * W x - 2 * Real.pi < r →
    ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (W z - W x) < r

theorem hasNonincreasingWidthNormalizationOn_of_forwardDifference {T t : ℝ} (hT : 0 ≤ T)
    {W : ℝ → ℝ} (h0 : ∀ z ∈ Icc T t, 0 ≤ W z) (h : HasWidthForwardDifferenceBoundOn T t W) :
    HasNonincreasingWidthNormalizationOn T t W := by
  intro x hxI r hr
  have hTx : T ≤ x := hxI.1
  have hx : 0 ≤ x := le_trans hT hTx
  have hdx : 0 < 4 * x + 1 := by linarith
  have hWx : 0 ≤ W x := h0 x ⟨hTx, hxI.2.le⟩
  set Dx := (4 * x + 1) ^ (-(3 / 4) : ℝ) with hDx
  have hDxpos : 0 < Dx := by
    rw [hDx]
    exact Real.rpow_pos_of_pos hdx _
  set δ := Dx + W x + 2 * Real.pi + 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    linarith [hDxpos, hWx, Real.pi_pos]
  set ε := min (r / (2 * δ)) (1 / 2) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact lt_min (by positivity) (by norm_num)
  have hεle : ε ≤ 1 / 2 := by
    rw [hε]
    exact min_le_right _ _
  have hεδ : ε * δ ≤ r / 2 := by
    rw [hε]
    have h2 : (r / (2 * δ)) * δ = r / 2 := by
      field_simp
    calc min (r / (2 * δ)) (1 / 2) * δ ≤ (r / (2 * δ)) * δ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hδpos.le
      _ = r / 2 := h2
  set a := 3 / (1 + 4 * x) * W x - 2 * Real.pi with ha
  set ε₂ := ε / (|a| + 1) with hε₂
  have hε₂pos : 0 < ε₂ := by
    rw [hε₂]
    exact div_pos hεpos (by positivity)
  have hε₂ε : (|a| + ε) * ε₂ ≤ ε := by
    have hden : 0 < |a| + 1 := by positivity
    have hkey : ε₂ * (|a| + 1) = ε := by
      rw [hε₂]
      field_simp
    calc (|a| + ε) * ε₂ = ε₂ * (|a| + ε) := by ring
      _ ≤ ε₂ * (|a| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [hεle] : |a| + ε ≤ |a| + 1) hε₂pos.le
      _ = ε := hkey
  have hε₂le : ε₂ ≤ ε := by
    have hden : 0 < |a| + 1 := by positivity
    rw [hε₂, div_le_iff₀ hden]
    nlinarith [abs_nonneg a, hεpos]
  have hfreqW : ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (W z - W x) < a + ε := by
    refine h x hxI (a + ε) ?_
    rw [ha]
    linarith
  have hDtend : Tendsto (fun z : ℝ => (z - x)⁻¹ *
      ((4 * z + 1) ^ (-(3 / 4) : ℝ) - (4 * x + 1) ^ (-(3 / 4) : ℝ)))
      (𝓝[>] x) (𝓝 (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ))) := by
    have hbase := (hasDerivAt_widthNormalizationFactor hdx).tendsto_slope.mono_left
      (nhdsGT_le_nhdsNE x)
    have hfun : slope (fun z : ℝ => (4 * z + 1) ^ (-(3 / 4) : ℝ)) x =
        fun z : ℝ => (z - x)⁻¹ *
          ((4 * z + 1) ^ (-(3 / 4) : ℝ) - (4 * x + 1) ^ (-(3 / 4) : ℝ)) := by
      funext z
      rw [slope_def_module]
      rfl
    rwa [hfun] at hbase
  have hGtend : Tendsto (fun z : ℝ => (z - x)⁻¹ *
      ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ)))
      (𝓝[>] x) (𝓝 ((4 * x + 1) ^ (-(3 / 4) : ℝ))) := by
    have hbase := (hasDerivAt_widthGrowthFactor hdx).tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
    have hfun : slope (fun z : ℝ => (4 * z + 1) ^ (1 / 4 : ℝ)) x =
        fun z : ℝ => (z - x)⁻¹ *
          ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ)) := by
      funext z
      rw [slope_def_module]
      rfl
    rwa [hfun] at hbase
  have hDevent : ∀ᶠ z in 𝓝[>] x, (z - x)⁻¹ *
      ((4 * z + 1) ^ (-(3 / 4) : ℝ) - (4 * x + 1) ^ (-(3 / 4) : ℝ)) <
        (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + ε₂ :=
    hDtend.eventually (eventually_lt_nhds (by linarith))
  have hGevent : ∀ᶠ z in 𝓝[>] x, (z - x)⁻¹ *
      ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ)) <
        ((4 * x + 1) ^ (-(3 / 4) : ℝ)) + ε₂ :=
    hGtend.eventually (eventually_lt_nhds (by linarith))
  have hDclose : ∀ᶠ z in 𝓝[>] x,
      |(4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx| < ε₂ := by
    have hcont : ContinuousAt (fun z : ℝ => (4 * z + 1) ^ (-(3 / 4) : ℝ)) x :=
      (hasDerivAt_widthNormalizationFactor hdx).continuousAt
    have hball : ∀ᶠ z in 𝓝 x,
        dist ((4 * z + 1) ^ (-(3 / 4) : ℝ)) ((4 * x + 1) ^ (-(3 / 4) : ℝ)) < ε₂ :=
      hcont.tendsto.eventually (Metric.ball_mem_nhds _ hε₂pos)
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds] with z hz
    simpa only [Real.dist_eq, ← hDx] using hz
  have hcomb : ∃ᶠ z in 𝓝[>] x,
      x < z ∧ (z - x)⁻¹ * (W z - W x) < a + ε ∧
        (z - x)⁻¹ * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx) <
          (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + ε₂ ∧
        (z - x)⁻¹ * ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ)) <
          Dx + ε₂ ∧ |(4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx| < ε₂ := by
    have hev : ∀ᶠ z in 𝓝[>] x,
        x < z ∧ (z - x)⁻¹ * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx) <
            (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + ε₂ ∧
          (z - x)⁻¹ * ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ)) < Dx + ε₂ ∧
          |(4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx| < ε₂ := by
      filter_upwards [self_mem_nhdsWithin, hDevent, hGevent, hDclose] with z hzx h1 h2 h3
      exact ⟨hzx, h1, h2, h3⟩
    refine (hfreqW.and_eventually hev).mono fun z hz => ?_
    exact ⟨hz.2.1, hz.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2⟩
  refine hcomb.mono fun z hz => ?_
  obtain ⟨hzx, hz1, hz2, hz3, hz4⟩ := hz
  have hdz : 0 < 4 * z + 1 := by linarith
  have hDzpos : 0 < (4 * z + 1) ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hdz _
  have hzxpos : 0 < z - x := by linarith
  have hdecomp : widthNormalized T W z - widthNormalized T W x =
      (W z - W x) * (4 * z + 1) ^ (-(3 / 4) : ℝ) +
        W x * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx) +
          2 * Real.pi * ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ)) := by
    unfold widthNormalized
    rw [hDx]
    ring
  have t1 : (z - x)⁻¹ * ((W z - W x) * (4 * z + 1) ^ (-(3 / 4) : ℝ)) <
      (a + ε) * (4 * z + 1) ^ (-(3 / 4) : ℝ) :=
    calc (z - x)⁻¹ * ((W z - W x) * (4 * z + 1) ^ (-(3 / 4) : ℝ))
        = ((z - x)⁻¹ * (W z - W x)) * (4 * z + 1) ^ (-(3 / 4) : ℝ) := by ring
      _ < (a + ε) * (4 * z + 1) ^ (-(3 / 4) : ℝ) :=
          mul_lt_mul_of_pos_right hz1 hDzpos
  have t1b : (a + ε) * (4 * z + 1) ^ (-(3 / 4) : ℝ) <
      (a + ε) * Dx + (|a| + ε) * ε₂ := by
    have hDzlt : (4 * z + 1) ^ (-(3 / 4) : ℝ) < Dx + ε₂ := by
      have := (abs_lt.mp hz4).2
      linarith
    have habs : |a + ε| ≤ |a| + ε := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le a]
      · linarith [le_abs_self a]
    have hpos2 : 0 < |a| + ε := by positivity
    calc (a + ε) * (4 * z + 1) ^ (-(3 / 4) : ℝ)
        = (a + ε) * Dx + (a + ε) * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx) := by ring
      _ ≤ (a + ε) * Dx + |a + ε| * |(4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx| := by
          have := le_abs_self ((a + ε) * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx))
          rw [abs_mul] at this
          linarith
      _ < (a + ε) * Dx + (|a| + ε) * ε₂ := by
          have hle : |a + ε| * |(4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx| ≤
              (|a| + ε) * |(4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx| :=
            mul_le_mul_of_nonneg_right habs (abs_nonneg _)
          have hlt := lt_of_le_of_lt hle (mul_lt_mul_of_pos_left hz4 hpos2)
          linarith [hlt]
  have t2 : (z - x)⁻¹ * (W x * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx)) ≤
      W x * ((-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + ε₂) := by
    calc (z - x)⁻¹ * (W x * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx))
        = W x * ((z - x)⁻¹ * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx)) := by ring
      _ ≤ W x * ((-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + ε₂) :=
          mul_le_mul_of_nonneg_left hz2.le hWx
  have t3 : (z - x)⁻¹ *
      (2 * Real.pi * ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ))) <
        2 * Real.pi * (Dx + ε₂) := by
    calc (z - x)⁻¹ * (2 * Real.pi * ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ)))
        = 2 * Real.pi * ((z - x)⁻¹ *
            ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ))) := by ring
      _ < 2 * Real.pi * (Dx + ε₂) := mul_lt_mul_of_pos_left hz3 (by positivity)
  have hfinal : (z - x)⁻¹ * (widthNormalized T W z - widthNormalized T W x) <
      ε * Dx + (|a| + ε) * ε₂ + W x * ε₂ + 2 * Real.pi * ε₂ := by
    rw [hdecomp, mul_add, mul_add]
    have hsum : (z - x)⁻¹ * ((W z - W x) * (4 * z + 1) ^ (-(3 / 4) : ℝ)) +
        (z - x)⁻¹ * (W x * ((4 * z + 1) ^ (-(3 / 4) : ℝ) - Dx)) +
          (z - x)⁻¹ * (2 * Real.pi *
            ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * x + 1) ^ (1 / 4 : ℝ))) <
        (a + ε) * Dx + (|a| + ε) * ε₂ + W x * ((-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + ε₂) +
          2 * Real.pi * (Dx + ε₂) := by
      linarith [t1, t1b, t2, t3]
    have hw : W x * ((-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + ε₂) =
        W x * (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + W x * ε₂ := by ring
    have hg : 2 * Real.pi * (Dx + ε₂) = 2 * Real.pi * Dx + 2 * Real.pi * ε₂ := by ring
    have hcancel : a * Dx + W x * (-3 * (4 * x + 1) ^ (-(7 / 4) : ℝ)) + 2 * Real.pi * Dx = 0 := by
      rw [ha]
      exact widthGrowthFactor_cancel hdx (W x)
    linarith [hsum, hw, hg, hcancel]
  have hbound : ε * Dx + (|a| + ε) * ε₂ + W x * ε₂ + 2 * Real.pi * ε₂ ≤ r / 2 := by
    have hWle : W x * ε₂ ≤ W x * ε := mul_le_mul_of_nonneg_left hε₂le hWx
    have hPle : 2 * Real.pi * ε₂ ≤ 2 * Real.pi * ε :=
      mul_le_mul_of_nonneg_left hε₂le (by positivity)
    have hδle : Dx + W x + 2 * Real.pi + 1 ≤ δ := by
      rw [hδ]
      linarith
    have h1 : ε * Dx + ε * W x + ε * (2 * Real.pi) + ε ≤ ε * δ := by
      have := mul_le_mul_of_nonneg_left hδle hεpos.le
      linarith
    linarith [hε₂ε, hWle, hPle, h1, hεδ]
  linarith [hfinal, hbound, hr]

theorem exists_continuousOn_nonneg_hasWidthForwardDifferenceBoundOn {T t : ℝ} (hT : 0 ≤ T)
    (hTt : T ≤ t) :
    ∃ W : ℝ → ℝ, ContinuousOn W (Icc T t) ∧ (∀ z ∈ Icc T t, 0 ≤ W z) ∧
      HasWidthForwardDifferenceBoundOn T t W := by
  refine ⟨fun z => (2 * Real.pi / 3) * (1 + 4 * t) + 1 + 3 * (t - z), (by fun_prop), ?_, ?_⟩
  · intro z hz
    have hzt : z ≤ t := hz.2
    nlinarith [Real.pi_pos]
  · intro x hxI r hr
    have hxt : x ≤ t := hxI.2.le
    have hxT : T ≤ x := hxI.1
    have hdx : 0 < (1 : ℝ) + 4 * x := by linarith
    have hWx : (2 * Real.pi / 3) * (1 + 4 * x) + 1 ≤
        (2 * Real.pi / 3) * (1 + 4 * t) + 1 + 3 * (t - x) := by
      nlinarith [Real.pi_pos]
    have hbound : 0 < 3 / (1 + 4 * x) *
        ((2 * Real.pi / 3) * (1 + 4 * t) + 1 + 3 * (t - x)) - 2 * Real.pi := by
      have hstep : 3 / (1 + 4 * x) * ((2 * Real.pi / 3) * (1 + 4 * x) + 1) =
          2 * Real.pi + 3 / (1 + 4 * x) := by
        field_simp
      have h1 : 2 * Real.pi < 3 / (1 + 4 * x) *
          ((2 * Real.pi / 3) * (1 + 4 * x) + 1) := by
        rw [hstep]
        have : 0 < 3 / (1 + 4 * x) := by positivity
        linarith
      have h3 : 0 < 3 / (1 + 4 * x) := by positivity
      nlinarith [h1, mul_le_mul_of_nonneg_left hWx h3.le]
    have hslope : ∀ᶠ z in 𝓝[>] x,
        (z - x)⁻¹ * ((2 * Real.pi / 3) * (1 + 4 * t) + 1 + 3 * (t - z) -
          ((2 * Real.pi / 3) * (1 + 4 * t) + 1 + 3 * (t - x))) < r := by
      have hlt : (-3 : ℝ) < r := by linarith
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzx : z - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hz)
      have hdiff : (2 * Real.pi / 3) * (1 + 4 * t) + 1 + 3 * (t - z) -
          ((2 * Real.pi / 3) * (1 + 4 * t) + 1 + 3 * (t - x)) = -3 * (z - x) := by ring
      rw [hdiff, mul_comm (-3) (z - x), inv_mul_cancel_left₀ hzx]
      exact hlt
    exact hslope.frequently

theorem le_widthComparisonBound_of_forwardDifference {T t : ℝ} {W : ℝ → ℝ} (hT : 0 ≤ T)
    (hTt : T ≤ t) (hcont : ContinuousOn W (Icc T t)) (h0 : ∀ z ∈ Icc T t, 0 ≤ W z)
    (h : HasWidthForwardDifferenceBoundOn T t W) :
    W t ≤ widthComparisonBound T (W T) t :=
  le_widthComparisonBound_of_nonincreasing_normalization hT hTt hcont
    (hasNonincreasingWidthNormalizationOn_of_forwardDifference hT h0 h)

theorem le_extinctionThreshold_of_forwardDifference {T t : ℝ} {W : ℝ → ℝ} (hT : 0 ≤ T)
    (hTt : T ≤ t) (hcont : ContinuousOn W (Icc T t)) (h0 : ∀ z ∈ Icc T t, 0 ≤ W z)
    (h : HasWidthForwardDifferenceBoundOn T t W) :
    t ≤ T + extinctionThreshold (4 * T + 1) (4 * W T) / 4 :=
  le_of_le_widthComparisonBound hT (h0 T ⟨le_rfl, hTt⟩) hTt (h0 t ⟨hTt, le_rfl⟩)
    (le_widthComparisonBound_of_forwardDifference hT hTt hcont h0 h)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
