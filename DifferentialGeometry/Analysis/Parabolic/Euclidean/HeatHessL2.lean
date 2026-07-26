import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The spacetime `L²` heat-Hessian multiplier

This file isolates the Plancherel anchor for the singular late-time arm in the
Koch--Lamm heat map.  The multiplier is scalar-valued; finite-dimensional
codomains can later be recovered componentwise.
-/

noncomputable section

open Complex MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier symbol of `∂_v ∂_w (∂_t - Δ)⁻¹` on spacetime.

Mathlib uses `exp (-2 π i ⟪x, ξ⟫)` for the Fourier transform.  Cancelling one
common factor `2 π` from numerator and denominator gives the normalization
used here.  The value at the single zero frequency is the field-theoretic
value `0 / 0 = 0`. -/
def heatHessSym (v w : V) (z : WithLp 2 (ℝ × V)) : ℂ :=
  -((2 * π * inner ℝ v z.snd * inner ℝ w z.snd : ℝ) : ℂ) /
    (((2 * π * ‖z.snd‖ ^ 2 : ℝ) : ℂ) + I * (z.fst : ℂ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The heat-Hessian symbol is bounded by the product of the two directional
norms.  This is the pointwise estimate behind the spacetime `L²` bound. -/
theorem heatHessSym_norm (v w : V) (z : WithLp 2 (ℝ × V)) :
    ‖heatHessSym v w z‖ ≤ ‖v‖ * ‖w‖ := by
  by_cases hz : z.snd = 0
  · simp [heatHessSym, hz, mul_nonneg]
  let k : ℝ := 2 * π
  let d : ℂ := ((k * ‖z.snd‖ ^ 2 : ℝ) : ℂ) + I * (z.fst : ℂ)
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hzn : 0 < ‖z.snd‖ := norm_pos_iff.mpr hz
  have hd_re : d.re = k * ‖z.snd‖ ^ 2 := by
    change (↑(k * ‖z.snd‖ ^ 2) + I * ↑z.fst : ℂ).re = _
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, I_re, zero_mul,
      I_im, one_mul, Complex.ofReal_im, sub_zero, add_zero]
  have hd_lower : k * ‖z.snd‖ ^ 2 ≤ ‖d‖ := by
    rw [← hd_re]
    exact re_le_norm d
  have hd_pos : 0 < ‖d‖ :=
    lt_of_lt_of_le (mul_pos hk (sq_pos_of_pos hzn)) hd_lower
  have hv := norm_inner_le_norm (𝕜 := ℝ) v z.snd
  have hw := norm_inner_le_norm (𝕜 := ℝ) w z.snd
  have hv' : |inner ℝ v z.snd| ≤ ‖v‖ * ‖z.snd‖ := by
    simpa only [Real.norm_eq_abs] using hv
  have hw' : |inner ℝ w z.snd| ≤ ‖w‖ * ‖z.snd‖ := by
    simpa only [Real.norm_eq_abs] using hw
  change ‖-((k * inner ℝ v z.snd * inner ℝ w z.snd : ℝ) : ℂ) /
    d‖ ≤ ‖v‖ * ‖w‖
  rw [norm_div]
  apply (div_le_iff₀ hd_pos).2
  calc
    ‖-((k * inner ℝ v z.snd * inner ℝ w z.snd : ℝ) : ℂ)‖
        = k * |inner ℝ v z.snd| * |inner ℝ w z.snd| := by
            simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    _ ≤ k * (‖v‖ * ‖z.snd‖) * (‖w‖ * ‖z.snd‖) := by
      gcongr
    _ = (‖v‖ * ‖w‖) * (k * ‖z.snd‖ ^ 2) := by ring
    _ ≤ (‖v‖ * ‖w‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_left hd_lower (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The heat-Hessian symbol is Borel measurable despite its harmless
discontinuity at the zero frequency. -/
theorem heatHessSym_meas (v w : V) : Measurable (heatHessSym v w) := by
  unfold heatHessSym
  measurability

/-- The heat-Hessian symbol belongs to `L∞` on spacetime. -/
theorem heatHessSym_memLp (v w : V) :
    MemLp (heatHessSym v w) ⊤ (volume : Measure (WithLp 2 (ℝ × V))) :=
  memLp_top_of_bound (heatHessSym_meas v w).aestronglyMeasurable
    (‖v‖ * ‖w‖) (Filter.Eventually.of_forall (heatHessSym_norm v w))

/-- Pointwise multiplication by the heat-Hessian symbol on spacetime `L²`. -/
def heatHessFreq (v w : V)
    (f : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V)))) :
    Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V))) :=
  let hmem : MemLp (fun z => heatHessSym v w z * f z) 2
      (volume : Measure (WithLp 2 (ℝ × V))) := by
    simpa only [smul_eq_mul] using (Lp.memLp f).smul (heatHessSym_memLp v w)
  hmem.toLp (fun z => heatHessSym v w z * f z)

theorem heatHessFreq_ae (v w : V)
    (f : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V)))) :
    heatHessFreq v w f =ᵐ[volume] fun z => heatHessSym v w z * f z := by
  unfold heatHessFreq
  apply MemLp.coeFn_toLp

/-- Multiplication by the heat-Hessian symbol is bounded on spacetime `L²`. -/
theorem heatHessFreq_norm (v w : V)
    (f : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V)))) :
    ‖heatHessFreq v w f‖ ≤ (‖v‖ * ‖w‖) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [heatHessFreq_ae v w f] with z hz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right (heatHessSym_norm v w z) (norm_nonneg _)

/-- The spacetime `L²` heat-Hessian Fourier multiplier. -/
def heatHessL2 (v w : V)
    (f : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V)))) :
    Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V))) :=
  (Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ).symm
    (heatHessFreq v w (Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ f))

/-- The multiplier has exactly the advertised Fourier-side representative. -/
theorem heatHessL2_fourier (v w : V)
    (f : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V)))) :
    Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ (heatHessL2 v w f) =
      heatHessFreq v w (Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ f) := by
  unfold heatHessL2
  exact (Lp.fourierTransformₗᵢ (WithLp 2 (ℝ × V)) ℂ).apply_symm_apply _

/-- Plancherel transfers the symbol bound to the spacetime `L²` multiplier. -/
theorem heatHessL2_norm (v w : V)
    (f : Lp ℂ 2 (volume : Measure (WithLp 2 (ℝ × V)))) :
    ‖heatHessL2 v w f‖ ≤ (‖v‖ * ‖w‖) * ‖f‖ := by
  rw [heatHessL2, LinearIsometryEquiv.norm_map]
  exact (heatHessFreq_norm v w _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

end DifferentialGeometry.Analysis.Parabolic.Euclidean
