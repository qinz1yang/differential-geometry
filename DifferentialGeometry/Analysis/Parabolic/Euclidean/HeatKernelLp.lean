import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Euclidean heat kernels on `L^p`

This file starts the dimension-general Euclidean parametrix used by the
low-regularity Ricci--DeTurck construction.  The basic operator is defined as
a Bochner integral *in the Banach space* `L^p`, rather than as a pointwise
convolution.  This has two useful consequences:

* an `L^1` scalar kernel acts boundedly on every `L^p`, `1 <= p < infinity`,
  by nothing more than translation invariance and the triangle inequality;
* the Gaussian heat kernel and its first two spatial derivative kernels have
  the expected `1`, `t^(-1/2)`, and `t^(-1)` operator bounds.

The constants below are finite-dimensional Euclidean constants.  No Sobolev
regularity of the input is used in this file.
-/

noncomputable section

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section KernelOperator

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

/-- Translation of an `L^p` class by `y`.  The sign agrees with the usual
convolution convention: a representative is sent to `x ↦ u (x - y)`. -/
def lpTranslate (y : V) (u : Lp F p (volume : Measure V)) :
    Lp F p (volume : Measure V) :=
  DomAddAct.mk (-y) +ᵥ u

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The translation orbit of one `L^p` class is continuous. -/
theorem lpTranslate_cont (u : Lp F p (volume : Measure V)) :
    Continuous (fun y : V => lpTranslate y u) := by
  unfold lpTranslate
  fun_prop

omit [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ p)] [Fact (p ≠ ∞)] in
/-- Translation preserves the `L^p` norm. -/
@[simp] theorem lpTranslate_norm (y : V) (u : Lp F p (volume : Measure V)) :
    ‖lpTranslate y u‖ = ‖u‖ := by
  simp [lpTranslate]

/-- An `L^1` scalar kernel acts on `L^p` by a Banach-valued average of
translations.  The Bochner integral is defined for all kernels; the useful
estimates below assume integrability. -/
def lpKernel (η : V → ℝ) (u : Lp F p (volume : Measure V)) :
    Lp F p (volume : Measure V) :=
  ∫ y, η y • lpTranslate y u

omit [CompleteSpace F] in
/-- The Banach-valued integrand defining `lpKernel` is integrable whenever
the scalar kernel is integrable. -/
theorem lpKernel_integrable {η : V → ℝ} (hη : Integrable η)
    (u : Lp F p (volume : Measure V)) :
    Integrable (fun y : V => η y • lpTranslate y u) := by
  refine (hη.norm.mul_const ‖u‖).mono' ?_ ?_
  · exact hη.aestronglyMeasurable.smul (lpTranslate_cont u).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_smul, lpTranslate_norm, Real.norm_eq_abs]

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
/-- Young's `L^1 * L^p → L^p` estimate, phrased for the Banach-valued
translation average. -/
theorem lpKernel_norm_le {η : V → ℝ} (hη : Integrable η)
    (u : Lp F p (volume : Measure V)) :
    ‖lpKernel η u‖ ≤ (∫ y, ‖η y‖) * ‖u‖ := by
  unfold lpKernel
  calc
    ‖∫ y, η y • lpTranslate y u‖
        ≤ ∫ y, ‖η y‖ * ‖u‖ :=
      norm_integral_le_of_norm_le (hη.norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul, lpTranslate_norm, Real.norm_eq_abs])
    _ = (∫ y, ‖η y‖) * ‖u‖ := by rw [integral_mul_const]

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
/-- A nonnegative probability density acts contractively on every finite
`L^p`. -/
theorem lpKernel_contract {η : V → ℝ} (hη : Integrable η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∫ y, η y = 1)
    (u : Lp F p (volume : Measure V)) :
    ‖lpKernel η u‖ ≤ ‖u‖ := by
  refine (lpKernel_norm_le hη u).trans_eq ?_
  have habs : (fun y : V => ‖η y‖) = η := by
    funext y
    simp [Real.norm_eq_abs, abs_of_nonneg (hη0 y)]
  rw [habs, hη1, one_mul]

end KernelOperator

section OperatorKernel

variable {V F G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

/-- A bounded linear map of fibres induces a bounded linear map of the
corresponding `L^p` spaces.  Packaging this dependence linearly lets us
integrate operator-valued kernels without choosing representatives. -/
def liftLp : (F →L[ℝ] G) →L[ℝ]
    (Lp F p (volume : Measure V) →L[ℝ] Lp G p (volume : Measure V)) :=
  LinearMap.mkContinuous
    { toFun := fun A => A.compLpL p (volume : Measure V)
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun c A => ContinuousLinearMap.smul_compLpL c A }
    1
    (fun A => by
      simpa only [one_mul] using
        (ContinuousLinearMap.norm_compLpL_le (p := p) (μ := (volume : Measure V)) A))

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
@[simp] theorem liftLp_apply (A : F →L[ℝ] G) :
    liftLp (V := V) (p := p) A = A.compLpL p (volume : Measure V) := rfl

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
/-- The fibrewise lift does not increase operator norm. -/
theorem liftLp_norm_le (A : F →L[ℝ] G) :
    ‖liftLp (V := V) (p := p) A‖ ≤ ‖A‖ := by
  simpa [liftLp_apply] using
    (ContinuousLinearMap.norm_compLpL_le (p := p) (μ := (volume : Measure V)) A)

/-- The integrand associated with an operator-valued kernel. -/
def lpOpIntegrand (K : V → F →L[ℝ] G)
    (u : Lp F p (volume : Measure V)) (y : V) :
    Lp G p (volume : Measure V) :=
  (liftLp (V := V) (p := p) (K y)) (lpTranslate y u)

/-- An operator-valued `L^1` kernel acts by averaging its action on translated
`L^p` classes. -/
def lpOpKernel (K : V → F →L[ℝ] G)
    (u : Lp F p (volume : Measure V)) :
    Lp G p (volume : Measure V) :=
  ∫ y, lpOpIntegrand K u y

omit [CompleteSpace F] [CompleteSpace G] in
/-- Strong measurability of the operator-kernel integrand. -/
theorem lpOpIntegrand_aesm {K : V → F →L[ℝ] G} (hK : AEStronglyMeasurable K)
    (u : Lp F p (volume : Measure V)) :
    AEStronglyMeasurable (lpOpIntegrand K u) := by
  have hKl : AEStronglyMeasurable
      (fun y : V => liftLp (V := V) (p := p) (K y)) :=
    (liftLp (V := V) (p := p)).continuous.comp_aestronglyMeasurable hK
  have htr : AEStronglyMeasurable (fun y : V => lpTranslate y u) :=
    (lpTranslate_cont u).aestronglyMeasurable
  have h := (ContinuousLinearMap.apply ℝ (Lp G p (volume : Measure V))).aestronglyMeasurable_comp₂
    htr hKl
  simpa only [lpOpIntegrand, ContinuousLinearMap.apply_apply] using h

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
/-- Pointwise norm control for an operator-kernel integrand. -/
theorem lpOpIntegrand_norm (K : V → F →L[ℝ] G)
    (u : Lp F p (volume : Measure V)) (y : V) :
    ‖lpOpIntegrand K u y‖ ≤ ‖K y‖ * ‖u‖ := by
  calc
    ‖lpOpIntegrand K u y‖
        ≤ ‖liftLp (V := V) (p := p) (K y)‖ * ‖lpTranslate y u‖ :=
      (liftLp (V := V) (p := p) (K y)).le_opNorm _
    _ ≤ ‖K y‖ * ‖u‖ := by
      rw [lpTranslate_norm]
      exact mul_le_mul_of_nonneg_right (liftLp_norm_le (V := V) (p := p) (K y))
        (norm_nonneg _)

omit [CompleteSpace F] [CompleteSpace G] in
/-- Integrability of the operator-kernel integrand. -/
theorem lpOpKernel_int {K : V → F →L[ℝ] G} (hK : Integrable K)
    (u : Lp F p (volume : Measure V)) :
    Integrable (lpOpIntegrand K u) := by
  refine (hK.norm.mul_const ‖u‖).mono' (lpOpIntegrand_aesm hK.aestronglyMeasurable u) ?_
  filter_upwards with y
  exact lpOpIntegrand_norm K u y

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
/-- Young's inequality for a continuous-linear-map-valued `L^1` kernel. -/
theorem lpOpKernel_norm {K : V → F →L[ℝ] G} (hK : Integrable K)
    (u : Lp F p (volume : Measure V)) :
    ‖lpOpKernel K u‖ ≤ (∫ y, ‖K y‖) * ‖u‖ := by
  unfold lpOpKernel
  calc
    ‖∫ y, lpOpIntegrand K u y‖
        ≤ ∫ y, ‖K y‖ * ‖u‖ :=
      norm_integral_le_of_norm_le (hK.norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => lpOpIntegrand_norm K u y)
    _ = (∫ y, ‖K y‖) * ‖u‖ := by rw [integral_mul_const]

end OperatorKernel

section Gaussian

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- Radial Gaussian integrability in a finite-dimensional real inner-product
space.  This is the real-valued consequence of Mathlib's finite-dimensional
Gaussian theorem. -/
theorem gauss_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : V => Real.exp (-a * ‖x‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure V)
    (f := fun r : ℝ => Real.exp (-a * r ^ 2))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_sq ha
    (s := ((Module.finrank ℝ V - 1 : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  simpa only [smul_eq_mul, Real.rpow_natCast] using h

/-- Every fixed polynomial radial moment of a Gaussian is integrable. -/
theorem gaussMoment_int (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : V => ‖x‖ ^ k * Real.exp (-a * ‖x‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure V)
    (f := fun r : ℝ => r ^ k * Real.exp (-a * r ^ 2))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_sq ha
    (s := ((Module.finrank ℝ V - 1 + k : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  simpa only [smul_eq_mul, Real.rpow_natCast, pow_add, mul_assoc] using h

/-- The mass of the unnormalised time-one heat Gaussian. -/
def baseHeatMass (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (Real.pi / (4 : ℝ)⁻¹) ^ (Module.finrank ℝ V / 2 : ℝ)

/-- The normalized time-one Euclidean heat kernel. -/
def baseHeat (x : V) : ℝ :=
  (baseHeatMass V)⁻¹ * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The normalizing mass is positive. -/
theorem baseHeatMass_pos : 0 < baseHeatMass V := by
  unfold baseHeatMass
  exact Real.rpow_pos_of_pos (div_pos Real.pi_pos (by positivity)) _

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The time-one heat kernel is nonnegative. -/
theorem baseHeat_nonneg (x : V) : 0 ≤ baseHeat x := by
  exact mul_nonneg (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
    (Real.exp_pos _).le

/-- The time-one heat kernel is integrable. -/
theorem baseHeat_int : Integrable (baseHeat : V → ℝ) := by
  unfold baseHeat
  exact (gauss_integrable (V := V) (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul _

omit [Nontrivial V] in
/-- The normalized time-one heat kernel has mass one. -/
theorem integral_baseHeat : ∫ x : V, baseHeat x = 1 := by
  unfold baseHeat
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := V) (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)]
  exact inv_mul_cancel₀ (baseHeatMass_pos (V := V)).ne'

/-- Spatial scale `sqrt t` used in the heat-kernel dilation. -/
def heatScale (t : ℝ) : ℝ := Real.sqrt t

/-- The Euclidean heat kernel at time `t`, obtained by dilation of the
time-one kernel. -/
def heatKernel (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
    baseHeat ((heatScale t)⁻¹ • x)

/-- Positive time has positive heat scale. -/
theorem heatScale_pos {t : ℝ} (ht : 0 < t) : 0 < heatScale t := by
  simpa [heatScale] using Real.sqrt_pos.2 ht

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The heat kernel is nonnegative at positive time. -/
theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatKernel t x := by
  unfold heatKernel
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
    (baseHeat_nonneg _)

/-- The heat kernel is integrable at every positive time. -/
theorem heatKernel_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel t : V → ℝ) := by
  unfold heatKernel
  exact (baseHeat_int (V := V)).comp_smul (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
/-- The positive-time heat kernel has mass one. -/
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatKernel t x = 1 := by
  let r := heatScale t
  have hr : 0 < r := heatScale_pos ht
  unfold heatKernel
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseHeat hr.le,
    integral_baseHeat]
  simp only [smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')

end Gaussian

section GaussianDeriv

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- First directional derivative of the normalized time-one heat kernel. -/
def baseD1 (v x : V) : ℝ :=
  -(2 : ℝ)⁻¹ * ⟪x, v⟫ * baseHeat x

/-- Second directional derivative of the normalized time-one heat kernel. -/
def baseD2 (v w x : V) : ℝ :=
  ((4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ -
      (2 : ℝ)⁻¹ * ⟪v, w⟫) * baseHeat x

/-- Frechet derivative of `baseHeat`, as a continuous linear functional. -/
def baseD1Map (x : V) : V →L[ℝ] ℝ :=
  (-(2 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ x

/-- Frechet derivative of `baseD1 v`, as a continuous linear functional. -/
def baseD2Map (v x : V) : V →L[ℝ] ℝ :=
  ((4 : ℝ)⁻¹ * ⟪x, v⟫ * baseHeat x) • innerSL ℝ x -
    ((2 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ v

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem baseD1Map_apply (x v : V) :
    baseD1Map x v = baseD1 v x := by
  simp [baseD1Map, baseD1]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem baseD2Map_apply (v x w : V) :
    baseD2Map v x w = baseD2 v w x := by
  simp [baseD2Map, baseD2]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The explicit first Gaussian kernel is the Frechet derivative of the
time-one heat kernel. -/
theorem baseHeat_hasFDeriv (x : V) :
    HasFDerivAt (baseHeat : V → ℝ) (baseD1Map x) x := by
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(4 : ℝ)⁻¹)
  have he := hq.exp
  have hc := he.const_mul (baseHeatMass V)⁻¹
  convert hc using 1
  ext v
  simp [baseD1Map, baseHeat]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The explicit second Gaussian kernel differentiates the first one. -/
theorem baseD1_hasFDeriv (v x : V) :
    HasFDerivAt (baseD1 v) (baseD2Map v x) x := by
  have hi : HasFDerivAt (fun y : V => ⟪y, v⟫) (innerSL ℝ v) x := by
    simpa [real_inner_comm] using (innerSL ℝ v).hasFDerivAt
  have h := (hi.mul (baseHeat_hasFDeriv x)).const_mul (-(2 : ℝ)⁻¹)
  convert h using 1
  · funext y
    simp only [baseD1, Pi.mul_apply]
    ring
  · ext w
    simp only [baseD1Map, baseD2Map, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    ring

/-- Radial `L^1` majorant for the first derivative kernel. -/
def baseD1Maj (x : V) : ℝ :=
  (2 : ℝ)⁻¹ * ‖x‖ * baseHeat x

/-- Radial `L^1` majorant for the second derivative kernel. -/
def baseD2Maj (x : V) : ℝ :=
  ((4 : ℝ)⁻¹ * ‖x‖ ^ 2 + (2 : ℝ)⁻¹) * baseHeat x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Maj_nonneg (x : V) : 0 ≤ baseD1Maj x := by
  unfold baseD1Maj
  exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg x)) (baseHeat_nonneg x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2Maj_nonneg (x : V) : 0 ≤ baseD2Maj x := by
  unfold baseD2Maj
  exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) (sq_nonneg ‖x‖)) (by positivity))
    (baseHeat_nonneg x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The first derivative kernel is bounded by the radial first-moment
majorant, with the direction norm factored out. -/
theorem baseD1_bound (v x : V) :
    ‖baseD1 v x‖ ≤ ‖v‖ * baseD1Maj x := by
  rw [baseD1, baseD1Maj, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
    abs_of_nonneg (baseHeat_nonneg x)]
  calc
    (2 : ℝ)⁻¹ * |⟪x, v⟫| * baseHeat x
        ≤ (2 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * baseHeat x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x v) (by positivity))
        (baseHeat_nonneg x)
    _ = ‖v‖ * ((2 : ℝ)⁻¹ * ‖x‖ * baseHeat x) := by ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The second derivative kernel is bounded by the radial second-moment
majorant, with both direction norms factored out. -/
theorem baseD2_bound (v w x : V) :
    ‖baseD2 v w x‖ ≤ ‖v‖ * ‖w‖ * baseD2Maj x := by
  rw [baseD2, baseD2Maj, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (baseHeat_nonneg x)]
  have htri :
      |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫| ≤
        (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
          (2 : ℝ)⁻¹ * |⟪v, w⟫| := by
    calc
      |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫|
          = |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ +
              -((2 : ℝ)⁻¹ * ⟪v, w⟫)| := by ring
      _ ≤ |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫| +
            |-((2 : ℝ)⁻¹ * ⟪v, w⟫)| := abs_add_le _ _
      _ = (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
            (2 : ℝ)⁻¹ * |⟪v, w⟫| := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ)⁻¹),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  calc
    |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫| * baseHeat x
        ≤ ((4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
            (2 : ℝ)⁻¹ * |⟪v, w⟫|) * baseHeat x := by
          exact mul_le_mul_of_nonneg_right htri (baseHeat_nonneg x)
    _ ≤ ((4 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) +
            (2 : ℝ)⁻¹ * (‖v‖ * ‖w‖)) * baseHeat x := by
          apply mul_le_mul_of_nonneg_right _ (baseHeat_nonneg x)
          apply add_le_add
          · have hp : |⟪x, v⟫| * |⟪x, w⟫| ≤
                (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) :=
              mul_le_mul (abs_real_inner_le_norm x v) (abs_real_inner_le_norm x w)
                (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg v))
            calc
              (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫|
                  = (4 : ℝ)⁻¹ * (|⟪x, v⟫| * |⟪x, w⟫|) := by ring
              _ ≤ (4 : ℝ)⁻¹ * ((‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) :=
                mul_le_mul_of_nonneg_left hp (by positivity)
              _ = (4 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) := by ring
          · exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v w) (by positivity)
    _ = ‖v‖ * ‖w‖ *
          (((4 : ℝ)⁻¹ * ‖x‖ ^ 2 + (2 : ℝ)⁻¹) * baseHeat x) := by ring

/-- The first radial derivative majorant is integrable. -/
theorem baseD1Maj_int : Integrable (baseD1Maj : V → ℝ) := by
  have h := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : baseD1Maj = fun x : V =>
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
        (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD1Maj baseHeat
    ring
  rw [heq]
  exact h

/-- The second radial derivative majorant is integrable. -/
theorem baseD2Maj_int : Integrable (baseD2Maj : V → ℝ) := by
  have h2 := (gaussMoment_int (V := V) 2
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h0 := (gaussMoment_int (V := V) 0
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : baseD2Maj = fun x : V =>
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 2 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 0 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD2Maj baseHeat
    ring
  rw [heq]
  exact h2.add h0

/-- Dimension-dependent first derivative constant. -/
def heatC1 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD1Maj x

/-- Dimension-dependent second derivative constant. -/
def heatC2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD2Maj x

omit [Nontrivial V] in
theorem heatC1_nonneg : 0 ≤ heatC1 V :=
  integral_nonneg baseD1Maj_nonneg

omit [Nontrivial V] in
theorem heatC2_nonneg : 0 ≤ heatC2 V :=
  integral_nonneg baseD2Maj_nonneg

/-- First-derivative majorant at time `t`. -/
def heatD1Maj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD1Maj ((heatScale t)⁻¹ • x)

/-- Second-derivative majorant at time `t`. -/
def heatD2Maj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD2Maj ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1Maj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD1Maj t x := by
  unfold heatD1Maj
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD1Maj_nonneg _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Maj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD2Maj t x := by
  unfold heatD2Maj
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr (heatScale_pos ht).le))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD2Maj_nonneg _)

theorem heatD1Maj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD1Maj t : V → ℝ) := by
  unfold heatD1Maj
  exact (baseD1Maj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

theorem heatD2Maj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD2Maj t : V → ℝ) := by
  unfold heatD2Maj
  exact (baseD2Maj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
/-- Exact integral scaling of the first derivative majorant. -/
theorem integral_heatD1Maj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD1Maj t x = (heatScale t)⁻¹ * heatC1 V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD1Maj heatC1
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD1Maj hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

omit [Nontrivial V] in
/-- Exact integral scaling of the second derivative majorant. -/
theorem integral_heatD2Maj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD2Maj t x = t⁻¹ * heatC2 V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hsqrt : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  unfold heatD2Maj heatC2
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD2Maj hr.le]
  simp only [smul_eq_mul]
  have hscale : (heatScale t)⁻¹ * (heatScale t)⁻¹ = t⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsqrt]
  calc
    (heatScale t ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ *
          (heatScale t ^ Module.finrank ℝ V * ∫ x : V, baseD2Maj x)
        = ((heatScale t)⁻¹ * (heatScale t)⁻¹) *
            ∫ x : V, baseD2Maj x := by
          field_simp [hr.ne']
    _ = t⁻¹ * ∫ x : V, baseD2Maj x := by rw [hscale]

/-- First spatial derivative kernel of the heat kernel. -/
def heatD1 (t : ℝ) (v x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD1 v ((heatScale t)⁻¹ • x)

/-- Second spatial derivative kernel of the heat kernel. -/
def heatD2 (t : ℝ) (v w x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD2 v w ((heatScale t)⁻¹ • x)

/-- Frechet derivative map of the positive-time heat kernel. -/
def heatD1Map (t : ℝ) (x : V) : V →L[ℝ] ℝ :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹) •
    baseD1Map ((heatScale t)⁻¹ • x)

/-- Frechet derivative map of `heatD1 t v`. -/
def heatD2Map (t : ℝ) (v x : V) : V →L[ℝ] ℝ :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹) •
    baseD2Map v ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem heatD1Map_apply (t : ℝ) (x v : V) :
    heatD1Map t x v = heatD1 t v x := by
  simp [heatD1Map, heatD1]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem heatD2Map_apply (t : ℝ) (v x w : V) :
    heatD2Map t v x w = heatD2 t v w x := by
  simp [heatD2Map, heatD2]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- At positive time, `heatD1` is exactly the Frechet derivative of the heat
kernel. -/
theorem heatKernel_hasFDeriv {t : ℝ} (_ht : 0 < t) (x : V) :
    HasFDerivAt (heatKernel t) (heatD1Map t x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using S.hasFDerivAt
  have h := ((baseHeat_hasFDeriv ((heatScale t)⁻¹ • x)).comp x hS).const_mul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹)
  convert h using 1
  ext v
  simp [heatD1Map, S, baseD1Map]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- At positive time, `heatD2` is exactly the Frechet derivative of the first
heat derivative kernel. -/
theorem heatD1_hasFDeriv {t : ℝ} (_ht : 0 < t) (v x : V) :
    HasFDerivAt (heatD1 t v) (heatD2Map t v x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using S.hasFDerivAt
  have h := ((baseD1_hasFDeriv v ((heatScale t)⁻¹ • x)).comp x hS).const_mul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹)
  convert h using 1
  ext w
  simp [heatD2Map, S, baseD2Map]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise first-derivative kernel bound. -/
theorem heatD1_bound {t : ℝ} (ht : 0 < t) (v x : V) :
    ‖heatD1 t v x‖ ≤ ‖v‖ * heatD1Maj t x := by
  unfold heatD1 heatD1Maj
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _)),
    abs_of_nonneg (inv_nonneg.mpr (heatScale_pos ht).le)]
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
        ‖baseD1 v ((heatScale t)⁻¹ • x)‖
      ≤ ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (‖v‖ * baseD1Maj ((heatScale t)⁻¹ • x)) := by
        exact mul_le_mul_of_nonneg_left (baseD1_bound v _)
          (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
            (inv_nonneg.mpr (heatScale_pos ht).le))
    _ = ‖v‖ * (((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹ * baseD1Maj ((heatScale t)⁻¹ • x)) := by ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise second-derivative kernel bound. -/
theorem heatD2_bound {t : ℝ} (ht : 0 < t) (v w x : V) :
    ‖heatD2 t v w x‖ ≤ ‖v‖ * ‖w‖ * heatD2Maj t x := by
  unfold heatD2 heatD2Maj
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  simp only [abs_inv, abs_pow, abs_of_nonneg (heatScale_pos ht).le]
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
        ‖baseD2 v w ((heatScale t)⁻¹ • x)‖
      ≤ ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          (‖v‖ * ‖w‖ * baseD2Maj ((heatScale t)⁻¹ • x)) := by
        exact mul_le_mul_of_nonneg_left (baseD2_bound v w _)
          (mul_nonneg
            (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
              (inv_nonneg.mpr (heatScale_pos ht).le))
            (inv_nonneg.mpr (heatScale_pos ht).le))
    _ = ‖v‖ * ‖w‖ * (((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          baseD2Maj ((heatScale t)⁻¹ • x)) := by ring

/-- Integrability of the first heat derivative kernel. -/
theorem heatD1_int {t : ℝ} (ht : 0 < t) (v : V) :
    Integrable (heatD1 t v : V → ℝ) := by
  refine ((heatD1Maj_int (V := V) ht).const_mul ‖v‖).mono'
    (by
      apply Continuous.aestronglyMeasurable
      unfold heatD1 baseD1 baseHeat baseHeatMass heatScale
      fun_prop) ?_
  filter_upwards with x
  exact heatD1_bound ht v x

/-- Integrability of the second heat derivative kernel. -/
theorem heatD2_int {t : ℝ} (ht : 0 < t) (v w : V) :
    Integrable (heatD2 t v w : V → ℝ) := by
  refine (((heatD2Maj_int (V := V) ht).const_mul ‖w‖).const_mul ‖v‖).mono'
    (by
      apply Continuous.aestronglyMeasurable
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop) ?_
  filter_upwards with x
  simpa [mul_assoc] using heatD2_bound ht v w x

/-- `L^1` norm of the first derivative kernel, with `t^(-1/2)` scaling. -/
theorem integral_norm_D1 {t : ℝ} (ht : 0 < t) (v : V) :
    (∫ x : V, ‖heatD1 t v x‖) ≤
      ‖v‖ * (heatScale t)⁻¹ * heatC1 V := by
  calc
    (∫ x : V, ‖heatD1 t v x‖)
        ≤ ∫ x : V, ‖v‖ * heatD1Maj t x := by
      exact integral_mono (heatD1_int ht v).norm
        ((heatD1Maj_int (V := V) ht).const_mul ‖v‖)
        (fun x => heatD1_bound ht v x)
    _ = ‖v‖ * ((heatScale t)⁻¹ * heatC1 V) := by
      rw [integral_const_mul, integral_heatD1Maj ht]
    _ = ‖v‖ * (heatScale t)⁻¹ * heatC1 V := by ring

/-- `L^1` norm of the second derivative kernel, with `t^(-1)` scaling. -/
theorem integral_norm_D2 {t : ℝ} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2 t v w x‖) ≤
      ‖v‖ * ‖w‖ * t⁻¹ * heatC2 V := by
  calc
    (∫ x : V, ‖heatD2 t v w x‖)
        ≤ ∫ x : V, (‖v‖ * ‖w‖) * heatD2Maj t x := by
      exact integral_mono (heatD2_int ht v w).norm
        ((heatD2Maj_int (V := V) ht).const_mul (‖v‖ * ‖w‖))
        (fun x => by simpa [mul_assoc] using heatD2_bound ht v w x)
    _ = (‖v‖ * ‖w‖) * (t⁻¹ * heatC2 V) := by
      rw [integral_const_mul, integral_heatD2Maj ht]
    _ = ‖v‖ * ‖w‖ * t⁻¹ * heatC2 V := by ring

end GaussianDeriv

section HeatLp

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

/-- The Euclidean heat operator on `L^p`. -/
def heatLp (t : ℝ) (u : Lp F p (volume : Measure V)) :
    Lp F p (volume : Measure V) :=
  lpKernel (heatKernel t) u

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
/-- The positive-time Euclidean heat operator is an `L^p` contraction. -/
theorem heatLp_contract {t : ℝ} (ht : 0 < t)
    (u : Lp F p (volume : Measure V)) :
    ‖heatLp t u‖ ≤ ‖u‖ := by
  exact lpKernel_contract (heatKernel_int ht) (heatKernel_nonneg ht)
    (integral_heatKernel ht) u

/-- First spatial derivative heat operator in direction `v`. -/
def heatD1Lp (t : ℝ) (v : V) (u : Lp F p (volume : Measure V)) :
    Lp F p (volume : Measure V) :=
  lpKernel (heatD1 t v) u

/-- Second spatial derivative heat operator in directions `v,w`. -/
def heatD2Lp (t : ℝ) (v w : V) (u : Lp F p (volume : Measure V)) :
    Lp F p (volume : Measure V) :=
  lpKernel (heatD2 t v w) u

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
/-- First-derivative `L^p` smoothing estimate. -/
theorem heatD1Lp_norm {t : ℝ} (ht : 0 < t) (v : V)
    (u : Lp F p (volume : Measure V)) :
    ‖heatD1Lp t v u‖ ≤
      (‖v‖ * (heatScale t)⁻¹ * heatC1 V) * ‖u‖ := by
  refine (lpKernel_norm_le (heatD1_int ht v) u).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D1 ht v) (norm_nonneg _)

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
/-- Second-derivative `L^p` smoothing estimate. -/
theorem heatD2Lp_norm {t : ℝ} (ht : 0 < t) (v w : V)
    (u : Lp F p (volume : Measure V)) :
    ‖heatD2Lp t v w u‖ ≤
      (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ := by
  refine (lpKernel_norm_le (heatD2_int ht v w) u).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D2 ht v w) (norm_nonneg _)

end HeatLp

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
