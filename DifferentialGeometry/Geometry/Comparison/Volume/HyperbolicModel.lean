import DifferentialGeometry.Analysis.Calculus.RatioMonotonicity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Hyperbolic radial comparison model

This file defines the nonpositive-curvature radial model used by the
Bishop--Gromov route.  The parameter `q >= 0` is the square root of the
absolute curvature scale, so the warping function is `sinh (q r) / q`, with
its continuous `q = 0` specialization `r`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

/-- Hyperbolic radial warping function, including the Euclidean `q = 0`
case. -/
def hypSn (q r : ℝ) : ℝ :=
  if q = 0 then r else Real.sinh (q * r) / q

/-- Radial derivative of `hypSn`. -/
def hypSnDeriv (q r : ℝ) : ℝ :=
  if q = 0 then 1 else Real.cosh (q * r)

/-- The hyperbolic warping function has the expected radial derivative. -/
theorem hasDerivAt_hypSn (q r : ℝ) :
    HasDerivAt (hypSn q) (hypSnDeriv q r) r := by
  by_cases hq : q = 0
  · subst q
    have hfun : hypSn 0 = fun x : ℝ => x := by
      funext x
      simp [hypSn]
    rw [hfun]
    simp only [hypSnDeriv]
    exact hasDerivAt_id r
  · have h := ((hasDerivAt_id r).const_mul q).sinh.div_const q
    have hfun : hypSn q = fun x : ℝ => Real.sinh (q * x) / q := by
      funext x
      simp [hypSn, hq]
    rw [hfun]
    simpa [hypSnDeriv, hq] using h

/-- The radial derivative of the hyperbolic warping function satisfies the
model Jacobi equation. -/
theorem hasDerivAt_hypSnD (q r : ℝ) :
    HasDerivAt (hypSnDeriv q) (q ^ 2 * hypSn q r) r := by
  by_cases hq : q = 0
  · subst q
    have hfun : hypSnDeriv 0 = fun _ : ℝ => 1 := by
      funext x
      simp [hypSnDeriv]
    rw [hfun]
    simpa [hypSn] using
      (hasDerivAt_const (x := r) (c := (1 : ℝ)))
  · have h := ((hasDerivAt_id r).const_mul q).cosh
    have hfun : hypSnDeriv q = fun x : ℝ => Real.cosh (q * x) := by
      funext x
      simp [hypSnDeriv, hq]
    have hderiv : Real.sinh (q * r) * q = q ^ 2 * hypSn q r := by
      rw [hypSn, if_neg hq]
      field_simp
    have hderiv' : Real.sinh (q * id r) * (q * 1) = q ^ 2 * hypSn q r := by
      simpa only [id_eq, mul_one] using hderiv
    rw [hfun]
    simpa only [id_eq, mul_one] using h.congr_deriv hderiv'

/-- Conserved energy identity for the hyperbolic warping function. -/
theorem hypSn_energy (q r : ℝ) :
    hypSnDeriv q r ^ 2 - q ^ 2 * hypSn q r ^ 2 = 1 := by
  by_cases hq : q = 0
  · subst q
    simp [hypSnDeriv, hypSn]
  · rw [hypSnDeriv, if_neg hq, hypSn, if_neg hq]
    calc
      Real.cosh (q * r) ^ 2 - q ^ 2 * (Real.sinh (q * r) / q) ^ 2 =
          Real.cosh (q * r) ^ 2 - Real.sinh (q * r) ^ 2 := by
        field_simp
      _ = 1 := Real.cosh_sq_sub_sinh_sq (q * r)

/-- The hyperbolic radial warping function is continuous in the radius. -/
theorem hypSn_continuous (q : ℝ) : Continuous (hypSn q) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_hypSn q r).continuousAt

/-- `hypSn q r` is positive at positive radius when `q` is nonnegative. -/
theorem hypSn_pos {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) :
    0 < hypSn q r := by
  by_cases hq0 : q = 0
  · simpa [hypSn, hq0] using hr
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [hypSn, if_neg hq0]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hqpos hr)) hqpos

/-- Hyperbolic radial area density in transverse dimension `d`. -/
def hypDensity (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  hypSn q r ^ d

/-- Radial derivative of the hyperbolic area density. -/
def hypDensityDeriv (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  (d : ℝ) * hypSn q r ^ (d - 1) * hypSnDeriv q r

/-- The hyperbolic area density has the power-rule derivative. -/
theorem hasDerivAt_hypDen (q : ℝ) (d : ℕ) (r : ℝ) :
    HasDerivAt (hypDensity q d) (hypDensityDeriv q d r) r := by
  simpa [hypDensity, hypDensityDeriv] using (hasDerivAt_hypSn q r).pow d

/-- The hyperbolic radial area density is continuous in the radius. -/
theorem hypDen_continuous (q : ℝ) (d : ℕ) : Continuous (hypDensity q d) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_hypDen q d r).continuousAt

/-- Logarithmic radial derivative of the hyperbolic area density. -/
def hypMeanCurv (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  (d : ℝ) * hypSnDeriv q r / hypSn q r

/-- The hyperbolic model mean curvature is bounded by its Euclidean pole term
plus the curvature scale. -/
theorem hypMeanCurv_le
    {q r : ℝ} (d : ℕ) (hq : 0 ≤ q) (hr : 0 < r) :
    hypMeanCurv q d r ≤ (d : ℝ) / r + (d : ℝ) * q := by
  by_cases hq0 : q = 0
  · subst q
    simp [hypMeanCurv, hypSnDeriv, hypSn]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hqr : 0 < q * r := mul_pos hqpos hr
    have hsinh : 0 < Real.sinh (q * r) :=
      Real.sinh_pos_iff.mpr hqr
    have hcosh :
        Real.cosh (q * r) ≤ Real.sinh (q * r) + 1 := by
      have hexp : Real.exp (-(q * r)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqr.le)
      calc
        Real.cosh (q * r) =
            Real.sinh (q * r) + Real.exp (-(q * r)) := by
          linarith [Real.cosh_sub_sinh (q * r)]
        _ ≤ Real.sinh (q * r) + 1 := add_le_add le_rfl hexp
    have hsinh_ge : q * r ≤ Real.sinh (q * r) :=
      Real.self_le_sinh_iff.mpr hqr.le
    have hmain :
        q * r * Real.cosh (q * r) ≤
          (1 + q * r) * Real.sinh (q * r) := by
      calc
        q * r * Real.cosh (q * r) ≤
            q * r * (Real.sinh (q * r) + 1) :=
          mul_le_mul_of_nonneg_left hcosh hqr.le
        _ ≤ (1 + q * r) * Real.sinh (q * r) := by
          nlinarith
    have hmodel :
        Real.cosh (q * r) ≤
          (1 / r + q) * (Real.sinh (q * r) / q) := by
      have hdiv := (div_le_div_iff_of_pos_right hqr).mpr hmain
      convert hdiv using 1 <;> field_simp
    have hratio :
        Real.cosh (q * r) / (Real.sinh (q * r) / q) ≤ 1 / r + q :=
      (div_le_iff₀ (div_pos hsinh hqpos)).mpr hmodel
    rw [hypMeanCurv, hypSnDeriv, if_neg hq0, hypSn, if_neg hq0]
    calc
      (d : ℝ) * Real.cosh (q * r) / (Real.sinh (q * r) / q) =
          (d : ℝ) * (Real.cosh (q * r) /
            (Real.sinh (q * r) / q)) := by ring
      _ ≤ (d : ℝ) * (1 / r + q) :=
        mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg d)
      _ = (d : ℝ) / r + (d : ℝ) * q := by ring

/-- The hyperbolic model mean curvature satisfies its scalar Riccati equation. -/
theorem hasDerivAt_hypMean
    {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) (hd : 0 < d) :
    HasDerivAt (hypMeanCurv q d)
      ((d : ℝ) * q ^ 2 - hypMeanCurv q d r ^ 2 / (d : ℝ)) r := by
  have hsn : hypSn q r ≠ 0 := ne_of_gt (hypSn_pos hq hr)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have h := ((hasDerivAt_hypSnD q r).const_mul (d : ℝ)).fun_div
    (hasDerivAt_hypSn q r) hsn
  refine h.congr_deriv ?_
  simp only [hypMeanCurv]
  field_simp

/-- The logarithmic derivative of the model warping function has derivative
`-1 / hypSn^2`. -/
theorem hasDerivAt_hypLog
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) :
    HasDerivAt (fun x => hypSnDeriv q x / hypSn q x)
      (-1 / hypSn q r ^ 2) r := by
  have hsn : hypSn q r ≠ 0 := ne_of_gt (hypSn_pos hq hr)
  have h := (hasDerivAt_hypSnD q r).fun_div (hasDerivAt_hypSn q r) hsn
  refine h.congr_deriv ?_
  have henergy := hypSn_energy q r
  field_simp [hsn]
  nlinarith

/-- The logarithmic derivative of the model warping function diverges to
`+∞` at the pole. -/
theorem hypLog_tendsto {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun r => hypSnDeriv q r / hypSn q r)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hsn : Tendsto (hypSn q) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hsn0 : Tendsto (hypSn q) (𝓝 (0 : ℝ)) (𝓝 (hypSn q 0)) :=
        (hypSn_continuous q).continuousAt
      simpa [hypSn] using hsn0.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact hypSn_pos hq hr
  have hsd : Tendsto (hypSnDeriv q) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    by_cases hq0 : q = 0
    · subst q
      have hfun : hypSnDeriv 0 = fun _ : ℝ => 1 := by
        funext r
        simp [hypSnDeriv]
      rw [hfun]
      exact tendsto_const_nhds
    · have hc : Continuous (fun r : ℝ => Real.cosh (q * r)) :=
        Real.continuous_cosh.comp (continuous_const.mul continuous_id)
      have hc0 : Tendsto (fun r : ℝ => Real.cosh (q * r)) (𝓝 0) (𝓝 1) := by
        simpa only [mul_zero, Real.cosh_zero] using (hc.continuousAt.tendsto :
          Tendsto (fun r : ℝ => Real.cosh (q * r)) (𝓝 0)
            (𝓝 (Real.cosh (q * 0))))
      have hfun : hypSnDeriv q = fun r : ℝ => Real.cosh (q * r) := by
        funext r
        simp [hypSnDeriv, hq0]
      rw [hfun]
      exact hc0.mono_left inf_le_left
  convert hsn.inv_tendsto_nhdsGT_zero.atTop_mul_pos zero_lt_one hsd using 1
  simp only [Pi.inv_apply, inv_mul_eq_div]

/-- The model warping function is asymptotic to the radius at the pole. -/
theorem hypSnRatio_tendsto (q : ℝ) :
    Tendsto (fun r => hypSn q r / r) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := (hasDerivAt_hypSn q 0).tendsto_slope_zero_right
  convert h using 1
  · funext r
    simp [hypSn, div_eq_inv_mul, smul_eq_mul]
  · simp [hypSnDeriv]

/-- Near the pole, the model warping function is at most twice the radius. -/
theorem hypSn_le_two (q : ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), hypSn q r ≤ 2 * r := by
  have hratio := (hypSnRatio_tendsto q).eventually
    (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hratio, self_mem_nhdsWithin] with r hratio hr
  change 0 < r at hr
  calc
    hypSn q r = (hypSn q r / r) * r := (div_mul_cancel₀ _ hr.ne').symm
    _ ≤ 2 * r := mul_le_mul_of_nonneg_right hratio.le hr.le

/-- The model density derivative is its mean curvature times the density. -/
theorem hypDenDeriv_eq_mean
    {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) :
    hypDensityDeriv q d r = hypMeanCurv q d r * hypDensity q d r := by
  have hsn : hypSn q r ≠ 0 := ne_of_gt (hypSn_pos hq hr)
  cases d with
  | zero => simp [hypDensityDeriv, hypMeanCurv, hypDensity]
  | succ d =>
      simp only [hypDensityDeriv, hypMeanCurv, hypDensity, Nat.cast_succ,
        Nat.succ_sub_one, pow_succ]
      field_simp

/-- The hyperbolic area density is positive at positive radius. -/
theorem hypDensity_pos {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) :
    0 < hypDensity q d r := by
  exact pow_pos (hypSn_pos hq hr) d

/-- A density whose logarithmic derivative is `m` has ratio derivative equal
to the ratio times the difference from the model mean curvature. -/
theorem hasDerivAt_hypRatio
    {j j' m : ℝ → ℝ} {q r : ℝ} {d : ℕ}
    (hq : 0 ≤ q) (hr : 0 < r)
    (hj : HasDerivAt j (j' r) r)
    (hj' : j' r = m r * j r) :
    HasDerivAt (fun x => j x / hypDensity q d x)
      ((j r / hypDensity q d r) * (m r - hypMeanCurv q d r)) r := by
  have hden : hypDensity q d r ≠ 0 := ne_of_gt (hypDensity_pos hq hr)
  have h := hj.fun_div (hasDerivAt_hypDen q d r) hden
  refine h.congr_deriv ?_
  rw [hj', hypDenDeriv_eq_mean hq hr]
  field_simp [hden]

/-- The model-weighted difference between a scalar Riccati subsolution and
the hyperbolic mean curvature is antitone. -/
theorem weightedMean_anti
    {m m' : ℝ → ℝ} {q b : ℝ} {d : ℕ}
    (hq : 0 ≤ q) (hd : 0 < d)
    (hm : ∀ r ∈ Ioo (0 : ℝ) b, HasDerivAt m (m' r) r)
    (hmle : ∀ r ∈ Ioo (0 : ℝ) b,
      m' r ≤ (d : ℝ) * q ^ 2 - m r ^ 2 / (d : ℝ)) :
    AntitoneOn
      (fun r => hypSn q r ^ 2 * (m r - hypMeanCurv q d r))
      (Ioo (0 : ℝ) b) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  let F : ℝ → ℝ := fun r =>
    hypSn q r ^ 2 * (m r - hypMeanCurv q d r)
  let F' : ℝ → ℝ := fun r =>
    2 * hypSn q r * hypSnDeriv q r * (m r - hypMeanCurv q d r) +
      hypSn q r ^ 2 *
        (m' r - ((d : ℝ) * q ^ 2 - hypMeanCurv q d r ^ 2 / (d : ℝ)))
  have hF (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) b) : HasDerivAt F (F' r) r := by
    have hs := (hasDerivAt_hypSn q r).pow 2
    have hz := (hm r hr).sub (hasDerivAt_hypMean hq hr.1 hd)
    refine (hs.mul hz).congr_deriv ?_
    simp only [F', Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.sub_apply, Pi.pow_apply]
  have hFle (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) b) : F' r ≤ 0 := by
    let D : ℝ := d
    let S : ℝ := hypSn q r
    let SD : ℝ := hypSnDeriv q r
    let mm : ℝ := m r
    let hh : ℝ := hypMeanCurv q d r
    let mp : ℝ := m' r
    let hp : ℝ := D * q ^ 2 - hh ^ 2 / D
    have hD : 0 < D := by simpa only [D] using hdR
    have hS : 0 < S := by simpa only [S] using hypSn_pos hq hr.1
    have hweight : D * (2 * S * SD) = 2 * S ^ 2 * hh := by
      dsimp only [D, S, SD, hh]
      rw [hypMeanCurv]
      field_simp [ne_of_gt hS]
    have hmp : mp ≤ D * q ^ 2 - mm ^ 2 / D := by
      simpa only [mp, D, mm] using hmle r hr
    have hmpD : D * mp ≤ D ^ 2 * q ^ 2 - mm ^ 2 := by
      calc
        D * mp ≤ D * (D * q ^ 2 - mm ^ 2 / D) :=
          mul_le_mul_of_nonneg_left hmp hD.le
        _ = D ^ 2 * q ^ 2 - mm ^ 2 := by
          field_simp [ne_of_gt hD]
    have hdiffD : D * (mp - hp) ≤ hh ^ 2 - mm ^ 2 := by
      calc
        D * (mp - hp) = D * mp - (D ^ 2 * q ^ 2 - hh ^ 2) := by
          dsimp only [hp]
          field_simp [ne_of_gt hD]
        _ ≤ (D ^ 2 * q ^ 2 - mm ^ 2) - (D ^ 2 * q ^ 2 - hh ^ 2) :=
          sub_le_sub_right hmpD _
        _ = hh ^ 2 - mm ^ 2 := by ring
    have hscaled : S ^ 2 * (D * (mp - hp)) ≤ S ^ 2 * (hh ^ 2 - mm ^ 2) :=
      mul_le_mul_of_nonneg_left hdiffD (sq_nonneg S)
    have hDderiv :
        D * (2 * S * SD * (mm - hh) + S ^ 2 * (mp - hp)) ≤ 0 := by
      calc
        D * (2 * S * SD * (mm - hh) + S ^ 2 * (mp - hp)) =
            (D * (2 * S * SD)) * (mm - hh) + S ^ 2 * (D * (mp - hp)) := by ring
        _ = 2 * S ^ 2 * hh * (mm - hh) + S ^ 2 * (D * (mp - hp)) := by
          rw [hweight]
        _ ≤ 2 * S ^ 2 * hh * (mm - hh) + S ^ 2 * (hh ^ 2 - mm ^ 2) :=
          by linarith
        _ = -(S ^ 2 * (mm - hh) ^ 2) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (sq_nonneg S) (sq_nonneg (mm - hh)))
    change 2 * S * SD * (mm - hh) + S ^ 2 * (mp - hp) ≤ 0
    by_contra hpos
    have hprod := mul_pos hD (lt_of_not_ge hpos)
    linarith
  have hdiff : DifferentiableOn ℝ F (Ioo (0 : ℝ) b) := by
    intro r hr
    exact (hF r hr).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn F (Ioo (0 : ℝ) b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 b) hdiff.continuousOn ?_ ?_
    · simpa using hdiff
    · intro r hr
      have hr' : r ∈ Ioo (0 : ℝ) b := by simpa using hr
      rw [(hF r hr').deriv]
      exact hFle r hr'
  simpa only [F] using hanti

/-- A scalar Riccati subsolution with the radial weighted asymptotic at zero
is bounded above by the hyperbolic model mean curvature. -/
theorem mean_le_hyp
    {m m' : ℝ → ℝ} {q b : ℝ} {d : ℕ}
    (hq : 0 ≤ q) (hd : 0 < d)
    (hm : ∀ r ∈ Ioo (0 : ℝ) b, HasDerivAt m (m' r) r)
    (hmle : ∀ r ∈ Ioo (0 : ℝ) b,
      m' r ≤ (d : ℝ) * q ^ 2 - m r ^ 2 / (d : ℝ))
    (hlim : Tendsto
      (fun r => hypSn q r ^ 2 * (m r - hypMeanCurv q d r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ r ∈ Ioo (0 : ℝ) b, m r ≤ hypMeanCurv q d r := by
  have hanti := weightedMean_anti hq hd hm hmle
  intro r hr
  have hFr :
      hypSn q r ^ 2 * (m r - hypMeanCurv q d r) ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hr.1] with x hx
    have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
    exact hanti hxb hr hx.2.le
  have hSpos : 0 < hypSn q r ^ 2 := sq_pos_of_pos (hypSn_pos hq hr.1)
  nlinarith

/-- A scalar Riccati subsolution is bounded by the hyperbolic model when the
associated radial density ratio stays uniformly positive at the pole. -/
theorem mean_le_hyp_of_ratio
    {m m' R : ℝ → ℝ} {q b : ℝ} {d : ℕ}
    (hq : 0 ≤ q) (hd : 0 < d)
    (hm : ∀ r ∈ Ioo (0 : ℝ) b, HasDerivAt m (m' r) r)
    (hmle : ∀ r ∈ Ioo (0 : ℝ) b,
      m' r ≤ (d : ℝ) * q ^ 2 - m r ^ 2 / (d : ℝ))
    (hR : ∀ r ∈ Ioo (0 : ℝ) b,
      HasDerivAt R (R r * (m r - hypMeanCurv q d r)) r)
    (hRpos : ∀ r ∈ Ioo (0 : ℝ) b, 0 < R r)
    (hRlower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), C ≤ R r) :
    ∀ r ∈ Ioo (0 : ℝ) b, m r ≤ hypMeanCurv q d r := by
  have hanti := weightedMean_anti hq hd hm hmle
  intro r hr
  by_contra hle
  have hdiff : 0 < m r - hypMeanCurv q d r := sub_pos.mpr (lt_of_not_ge hle)
  let c : ℝ := hypSn q r ^ 2 * (m r - hypMeanCurv q d r)
  have hc : 0 < c := mul_pos (sq_pos_of_pos (hypSn_pos hq hr.1)) hdiff
  have hweighted (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) r) :
      c ≤ hypSn q x ^ 2 * (m x - hypMeanCurv q d x) := by
    dsimp only [c]
    have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
    exact hanti hxb hr hx.2.le
  let W : ℝ → ℝ := fun x => hypSnDeriv q x / hypSn q x
  let G : ℝ → ℝ := fun x => R x * Real.exp (c * W x)
  let G' : ℝ → ℝ := fun x =>
    R x * (m x - hypMeanCurv q d x) * Real.exp (c * W x) +
      R x * (Real.exp (c * W x) * (c * (-1 / hypSn q x ^ 2)))
  have hG (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) r) : HasDerivAt G (G' x) x := by
    have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
    have hW := hasDerivAt_hypLog hq hx.1
    have hExp := (hW.const_mul c).exp
    refine ((hR x hxb).mul hExp).congr_deriv ?_
    simp only [G', W]
  have hGnonneg (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) r) : 0 ≤ G' x := by
    have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
    have hS : 0 < hypSn q x ^ 2 := sq_pos_of_pos (hypSn_pos hq hx.1)
    have hquot : c / hypSn q x ^ 2 ≤ m x - hypMeanCurv q d x := by
      rw [div_le_iff₀ hS]
      simpa only [mul_comm] using hweighted x hx
    have heq : G' x =
        R x * Real.exp (c * W x) *
          ((m x - hypMeanCurv q d x) - c / hypSn q x ^ 2) := by
      dsimp only [G']
      ring
    rw [heq]
    exact mul_nonneg
      (mul_nonneg (hRpos x hxb).le (Real.exp_pos _).le)
      (sub_nonneg.mpr hquot)
  have hGdiff : DifferentiableOn ℝ G (Ioo (0 : ℝ) r) := by
    intro x hx
    exact (hG x hx).differentiableAt.differentiableWithinAt
  have hGmono : MonotoneOn G (Ioo (0 : ℝ) r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 r) hGdiff.continuousOn ?_ ?_
    · simpa using hGdiff
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) r := by simpa using hx
      rw [(hG x hx').deriv]
      exact hGnonneg x hx'
  let y : ℝ := r / 2
  have hy : y ∈ Ioo (0 : ℝ) r := by
    dsimp only [y]
    constructor <;> linarith [hr.1]
  have hGbound : ∀ᶠ x in 𝓝[>] (0 : ℝ), G x ≤ G y := by
    filter_upwards [Ioo_mem_nhdsGT hy.1] with x hx
    have hxr : x ∈ Ioo (0 : ℝ) r := ⟨hx.1, hx.2.trans hy.2⟩
    exact hGmono hxr hy hx.2.le
  obtain ⟨C, hC, hClower⟩ := hRlower
  have hWtop : Tendsto W (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [W] using hypLog_tendsto hq
  have hExpTop : Tendsto (fun x => Real.exp (c * W x))
      (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_exp_atTop.comp (hWtop.const_mul_atTop hc)
  have hGtop : Tendsto G (𝓝[>] (0 : ℝ)) atTop := by
    rw [tendsto_atTop]
    intro A
    filter_upwards [hClower, hExpTop.eventually_ge_atTop (A / C)] with x hxR hxE
    dsimp only [G]
    calc
      A = C * (A / C) := by field_simp [ne_of_gt hC]
      _ ≤ C * Real.exp (c * W x) := mul_le_mul_of_nonneg_left hxE hC.le
      _ ≤ R x * Real.exp (c * W x) :=
        mul_le_mul_of_nonneg_right hxR (Real.exp_pos _).le
  have hlarge := (tendsto_atTop.1 hGtop (G y + 1))
  have hfalse : ∀ᶠ x in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hGbound, hlarge] with x hxBound hxLarge
    linarith
  exact hfalse.exists.elim fun _ hx => hx

/-- A radial density satisfying the Bishop cross-derivative inequality has
antitone ratio to the hyperbolic model density. -/
theorem hypRatio_anti
    {j j' : ℝ → ℝ} {q a b : ℝ} {d : ℕ}
    (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hj : ∀ r ∈ Ioo a b, HasDerivAt j (j' r) r)
    (hcross : ∀ r ∈ Ioo a b,
      j' r * hypDensity q d r ≤ j r * hypDensityDeriv q d r) :
    AntitoneOn (fun r => j r / hypDensity q d r) (Ioo a b) := by
  refine ratio_anti_of_cross hj
    (fun r _hr => hasDerivAt_hypDen q d r) ?_ hcross
  intro r hr
  exact hypDensity_pos hq (lt_of_le_of_lt ha hr.1)

/-- The Bishop cross-derivative inequality implies monotonicity of the
cumulative radial volume ratio. -/
theorem hypVolumeRatio_anti
    {j j' : ℝ → ℝ} {q b : ℝ} {d : ℕ}
    (hq : 0 ≤ q)
    (hjcont : Continuous j)
    (hj : ∀ r ∈ Ioo (0 : ℝ) b, HasDerivAt j (j' r) r)
    (hcross : ∀ r ∈ Ioo (0 : ℝ) b,
      j' r * hypDensity q d r ≤ j r * hypDensityDeriv q d r) :
    AntitoneOn
      (fun r => (∫ x in 0..r, j x) / ∫ x in 0..r, hypDensity q d x)
      (Ioo (0 : ℝ) b) := by
  refine integralRatio_anti hjcont (hypDen_continuous q d) ?_ ?_
  · intro r hr
    exact hypDensity_pos hq hr.1
  · exact hypRatio_anti hq le_rfl hj hcross

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
