import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ContDiff

namespace Real.smoothTransition

theorem one_sub (x : ℝ) : Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  unfold Real.smoothTransition
  rw [sub_sub_cancel, add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x)]
  field_simp [(pos_denom x).ne']
  ring

@[simp] theorem half : Real.smoothTransition ((2 : ℝ)⁻¹) = (2 : ℝ)⁻¹ := by
  rw [Real.smoothTransition, div_eq_iff (pos_denom _).ne']
  rw [show (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by norm_num]
  ring

theorem eq_half_iff {x : ℝ} : Real.smoothTransition x = (2 : ℝ)⁻¹ ↔ x = (2 : ℝ)⁻¹ := by
  constructor
  · intro h
    have heq : expNegInvGlue x = expNegInvGlue (1 - x) := by
      rw [Real.smoothTransition, div_eq_iff (pos_denom x).ne'] at h
      linarith
    have hp : 0 < expNegInvGlue x := by linarith [pos_denom x]
    have hx : 0 < x := by
      by_contra hx
      rw [expNegInvGlue.zero_of_nonpos (not_lt.mp hx)] at hp
      exact lt_irrefl 0 hp
    have hy : 0 < 1 - x := by
      by_contra hy
      rw [heq, expNegInvGlue.zero_of_nonpos (not_lt.mp hy)] at hp
      exact lt_irrefl 0 hp
    simp only [expNegInvGlue, if_neg (not_le.mpr hx), if_neg (not_le.mpr hy)] at heq
    have hi := inv_injective (neg_injective (Real.exp_injective heq))
    linarith
  · rintro rfl
    exact half

private theorem expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x

theorem hasDerivAt_half : HasDerivAt Real.smoothTransition 2 ((2 : ℝ)⁻¹) := by
  have he : HasDerivAt expNegInvGlue (4 * expNegInvGlue ((2 : ℝ)⁻¹)) ((2 : ℝ)⁻¹) := by
    convert! expNegInvGlue_hasDerivAt ((2 : ℝ)⁻¹) using 1
    norm_num
  have he' : HasDerivAt (fun x : ℝ => expNegInvGlue (1 - x))
      (-(4 * expNegInvGlue ((2 : ℝ)⁻¹))) ((2 : ℝ)⁻¹) := by
    convert! (expNegInvGlue_hasDerivAt (1 - (2 : ℝ)⁻¹)).comp ((2 : ℝ)⁻¹)
      ((hasDerivAt_id ((2 : ℝ)⁻¹)).const_sub 1) using 1
    norm_num [Function.comp_def]
  have h := he.div (he.add he') (pos_denom ((2 : ℝ)⁻¹)).ne'
  have hp : expNegInvGlue ((2 : ℝ)⁻¹) ≠ 0 :=
    (expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).ne'
  change HasDerivAt (fun x => expNegInvGlue x /
    (expNegInvGlue x + expNegInvGlue (1 - x))) 2 ((2 : ℝ)⁻¹)
  convert! h using 1
  simp only [Pi.add_apply]
  rw [show (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by norm_num]
  field_simp [hp]
  ring

@[simp] theorem deriv_half : deriv Real.smoothTransition ((2 : ℝ)⁻¹) = 2 :=
  hasDerivAt_half.deriv

open scoped Topology

theorem hasCompactSupport_deriv : HasCompactSupport (_root_.deriv Real.smoothTransition) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
  intro t ht
  constructor
  · by_contra h
    have heq : Real.smoothTransition =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds (not_le.mp h)] with u hu
      exact Real.smoothTransition.zero_of_nonpos hu.le
    exact ht (by simpa only [deriv_const] using heq.deriv_eq)
  · by_contra h
    have heq : Real.smoothTransition =ᶠ[nhds t] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds (not_le.mp h)] with u hu
      exact Real.smoothTransition.one_of_one_le hu.le
    exact ht (by simpa only [deriv_const] using heq.deriv_eq)

end Real.smoothTransition

namespace Real

noncomputable def smoothAbs (ε x : ℝ) : ℝ :=
  x + 2 * ∫ t in x..ε, smoothTransition ((ε - t) / (2 * ε))

namespace smoothAbs

private theorem contDiff_integrand (ε : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => smoothTransition ((ε - t) / (2 * ε))) :=
  smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const (2 * ε))

theorem hasDerivAt (ε x : ℝ) :
    HasDerivAt (smoothAbs ε) (1 - 2 * smoothTransition ((ε - x) / (2 * ε))) x := by
  have hc := (contDiff_integrand ε).continuous
  have hi := intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable x ε)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert! (hasDerivAt_id x).add (hi.const_mul 2) using 1
  ring

theorem deriv (ε x : ℝ) :
    _root_.deriv (smoothAbs ε) x = 1 - 2 * smoothTransition ((ε - x) / (2 * ε)) :=
  (hasDerivAt ε x).deriv

theorem contDiff (ε : ℝ) : ContDiff ℝ ∞ (smoothAbs ε) := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun x => (hasDerivAt ε x).differentiableAt, ?_⟩
  have h : _root_.deriv (smoothAbs ε) =
      fun x => 1 - 2 * smoothTransition ((ε - x) / (2 * ε)) := funext (deriv ε)
  rw [h]
  exact contDiff_const.sub (contDiff_const.mul (contDiff_integrand ε))

theorem deriv_eq_zero_iff {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    _root_.deriv (smoothAbs ε) x = 0 ↔ x = 0 := by
  rw [deriv]
  constructor
  · intro h
    have hhalf : smoothTransition ((ε - x) / (2 * ε)) = (2 : ℝ)⁻¹ := by linarith
    have heq := smoothTransition.eq_half_iff.mp hhalf
    field_simp [hε] at heq
    linarith
  · rintro rfl
    have heq : (ε - 0) / (2 * ε) = (2 : ℝ)⁻¹ := by field_simp [hε]; ring
    rw [heq, smoothTransition.half]
    norm_num

theorem abs_deriv_le_one (ε x : ℝ) : |_root_.deriv (smoothAbs ε) x| ≤ 1 := by
  rw [deriv, abs_le]
  constructor <;> linarith [smoothTransition.nonneg ((ε - x) / (2 * ε)),
    smoothTransition.le_one ((ε - x) / (2 * ε))]

theorem lipschitzWith (ε : ℝ) : LipschitzWith 1 (smoothAbs ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((contDiff ε).differentiable (by simp))
  intro x
  exact NNReal.coe_le_coe.mp (by simpa using abs_deriv_le_one ε x)

theorem hasDerivAt_deriv_zero {ε : ℝ} (hε : ε ≠ 0) :
    HasDerivAt (_root_.deriv (smoothAbs ε)) (2 / ε) 0 := by
  have ha : HasDerivAt (fun x : ℝ => (ε - x) / (2 * ε)) (-1 / (2 * ε)) 0 :=
    ((hasDerivAt_id 0).const_sub ε).div_const (2 * ε)
  have heq : (ε - 0) / (2 * ε) = (2 : ℝ)⁻¹ := by field_simp [hε]; ring
  have hh : HasDerivAt smoothTransition 2 ((ε - 0) / (2 * ε)) := by
    rw [heq]
    exact smoothTransition.hasDerivAt_half
  have hd := ((hh.comp 0 ha).const_mul 2).const_sub 1
  convert! hd using 1
  · funext x
    exact deriv ε x
  · field_simp

theorem deriv_deriv_zero {ε : ℝ} (hε : ε ≠ 0) :
    _root_.deriv (_root_.deriv (smoothAbs ε)) 0 = 2 / ε :=
  (hasDerivAt_deriv_zero hε).deriv

theorem convexOn {ε : ℝ} (hε : 0 < ε) : ConvexOn ℝ Set.univ (smoothAbs ε) := by
  apply Monotone.convexOn_univ_of_deriv ((contDiff ε).differentiable (by simp))
  intro x y hxy
  rw [deriv, deriv]
  have h := smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_left hxy ε) (by positivity : 0 ≤ 2 * ε))
  linarith

private theorem eq_self_of_le_aux {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ x) :
    smoothAbs ε x = x := by
  have hi : (∫ t in x..ε, smoothTransition ((ε - t) / (2 * ε))) = 0 := by
    calc
      _ = ∫ _ in x..ε, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_ge hx] at ht
        exact smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.1) (by positivity))
      _ = 0 := by simp
  simp [smoothAbs, hi]

theorem neg {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) : smoothAbs ε (-x) = smoothAbs ε x := by
  have hd (y : ℝ) : HasDerivAt (fun z => smoothAbs ε (-z) - smoothAbs ε z) 0 y := by
    have harg : (ε - -y) / (2 * ε) = 1 - (ε - y) / (2 * ε) := by
      field_simp [hε]
      ring
    convert! ((hasDerivAt ε (-y)).comp y (hasDerivAt_neg y)).sub (hasDerivAt ε y) using 1
    rw [harg, smoothTransition.one_sub]
    ring
  have h := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) x 0
  have hz : smoothAbs ε (-x) - smoothAbs ε x = 0 := by simpa using h
  exact sub_eq_zero.mp hz

theorem eq_abs_of_le {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ |x|) : smoothAbs ε x = |x| := by
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx ⊢
    exact eq_self_of_le_aux hε hx
  · rw [abs_of_neg hx0] at hx ⊢
    rw [← neg hε.ne' x]
    exact eq_self_of_le_aux hε hx

theorem eq_self_of_le {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ x) : smoothAbs ε x = x :=
  (eq_abs_of_le hε (hx.trans (le_abs_self x))).trans (abs_of_nonneg (hε.le.trans hx))

theorem eq_neg_of_le {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ -ε) : smoothAbs ε x = -x := by
  have hx0 : x ≤ 0 := by linarith
  rw [eq_abs_of_le hε (by rw [abs_of_nonpos hx0]; linarith), abs_of_nonpos hx0]

theorem abs {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) : smoothAbs ε |x| = smoothAbs ε x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, neg hε]

theorem sub_abs_mem_Icc {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    smoothAbs ε x - |x| ∈ Set.Icc 0 (2 * ε) := by
  by_cases hx : ε ≤ |x|
  · rw [eq_abs_of_le hε hx, sub_self]
    exact ⟨le_rfl, by positivity⟩
  · have hxε : |x| ≤ ε := (not_le.mp hx).le
    have hl := (lipschitzWith ε).dist_le_mul |x| ε
    rw [abs hε.ne', eq_self_of_le hε le_rfl] at hl
    have hb : |smoothAbs ε x - ε| ≤ ε - |x| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul,
        abs_of_nonpos (sub_nonpos.mpr hxε), neg_sub] using hl
    have h := abs_le.mp hb
    constructor <;> linarith [abs_nonneg x]

end smoothAbs

end Real
