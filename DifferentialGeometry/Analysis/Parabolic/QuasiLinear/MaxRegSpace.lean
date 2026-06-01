import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.OperatorEquation
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Inclusion

/-!
# The maximal-regularity solution space and the affine Duhamel map

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a Sobolev exponent
`a ≥ 0` and a time horizon `0 < T ≤ 1`, this file sets up the **strong-solution
space** of the quasi-linear tensor heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`,

together with the **affine Duhamel solution map** whose fixed point is a strong
solution.

## The strong solution as a fixed point

A strong solution of `∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`, is the fixed point of
the affine **Duhamel map**

  `𝒯(u)(t) := e^{tΔ_∇} u₀ + ∫₀ᵗ e^{(t−s)Δ_∇} N(u(s)) ds`,

i.e. `𝒯(u) = (homogeneous part) + maximalRegularityOp (N ∘ u)`.  A fixed point
`u = 𝒯(u)` solves the equation.  This file builds the three structural pieces:

* the **solution space** `E_T` — the carrier on which `𝒯` acts;
* the **homogeneous part** `t ↦ e^{tΔ_∇} u₀` as an element of `E_T`;
* the **affine Duhamel map** `u₀, g ↦ (homogeneous) + maximalRegularityOp g`,
  with its initial-condition, equation, and Lipschitz properties.

The contraction estimate and the extraction of the fixed point are left to the
downstream construction.

## The solution space `E_T`

A strong solution lies in `L²([0,T]; H^{a+2})` with `∂_t u ∈ L²([0,T]; Hᵃ)` and
trace `u(0) ∈ H^{a+2}`.  The purely functional-analytic carrier of "`∂_t u`
exists in `L²` and `u(0)` is a trace" is the time-Sobolev space `H¹([0,T]; Hᵃ)`
(`timeH1`): an element *is* the data of its initial value `u(0) ∈ Hᵃ` together
with its `L²` time derivative `∂_t u ∈ L²([0,T]; Hᵃ)`.  We therefore take

  `MaxRegSolutionSpace a T := H¹([0,T]; Hᵃ)`,

a complete real Hilbert space (all four Hilbert instances inherited).  The extra
`H^{a+2}` spatial regularity — the two-derivative gain of maximal regularity —
is *not* a refinement of the carrier (which would destroy completeness for free)
but is recorded by **companion fields**: each constructed element of `E_T` (the
homogeneous part, the Duhamel image) is accompanied by an
`H^{a+2}`-valued solution field in `L²([0,T]; H^{a+2})`, exactly mirroring the
coexistence of `maximalRegularityOp` (an `H¹([0,T]; Hᵃ)` element) and
`maximalRegularitySolField` (its `L²([0,T]; H^{a+2})` field).

## Main definitions

* `MaxRegSolutionSpace a T` — the solution space `E_T`, `= H¹([0,T];
  Hᵃ)`.
* `maxRegHomogeneousSolField a u₀` — the `H^{a+2}`-valued field
  `t ↦ e^{tΔ_∇} u₀`, an element of `L²([0,T]; H^{a+2})`.
* `maxRegHomogeneousDerivField a u₀` — its time derivative
  `t ↦ Δ_∇ e^{tΔ_∇} u₀`, an element of `L²([0,T]; Hᵃ)`.
* `maxRegHomogeneous a u₀` — the homogeneous part `t ↦ e^{tΔ_∇} u₀` as
  an element of `E_T`.
* `maxRegDuhamelSolField a hT hT1 u₀ g` — the `H^{a+2}`-valued field of
  the Duhamel image.
* `maxRegDuhamelMap a hT hT1 u₀ g` — the affine Duhamel map
  `(homogeneous) + maximalRegularityOp g`, an element of `E_T`.

## Main results

* `maxRegHomogeneous_trace0` — `(homogeneous)(0) = u₀` (in `Hᵃ`, via the
  spectral inclusion `H^{a+2} ↪ Hᵃ`).
* `maxRegHomogeneous_timeDeriv_eq` — `∂_t (homogeneous) = Δ_∇ (homogeneous)`:
  the homogeneous part solves the homogeneous heat equation.
* `maxRegDuhamelMap_trace0` — `(maxRegDuhamelMap … u₀ g)(0) = u₀`.
* `maxRegDuhamelMap_timeDeriv_eq` — `∂_t (maxRegDuhamelMap … u₀ g) = Δ_∇ (field)
  + g`: the Duhamel image solves `∂_t u = Δ_∇ u + g`.
* `maxRegDuhamelMap_dist_le` — the Lipschitz bound `‖maxRegDuhamelMap … u₀ g −
  maxRegDuhamelMap … u₀ g'‖ ≤ 2·‖g − g'‖`, the contraction-in-the-forcing
  estimate underlying the downstream fixed-point argument.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

/-- **The maximal-regularity solution space** `E_T` of the quasi-linear tensor
heat equation: the time-Sobolev space `H¹([0,T]; Hᵃ)`.

An element of `E_T` carries an initial value `u(0) ∈ Hᵃ` (`timeH1.trace0`) and an
`L²` time derivative `∂_t u ∈ L²([0,T]; Hᵃ)` (`timeH1.timeDeriv`); it represents
the indefinite Bochner integral `t ↦ u(0) + ∫₀ᵗ ∂_t u`.  The space is a complete
real Hilbert space with the graph norm `‖u‖² = ‖u(0)‖² + ‖∂_t u‖²` — all four
Hilbert-space instances (`NormedAddCommGroup`, `NormedSpace ℝ`, `InnerProductSpace
ℝ`, `CompleteSpace`) are inherited transparently from `timeH1`, the completeness
being exactly what the downstream Banach fixed-point argument consumes.  The
two-derivative-gain `H^{a+2}` regularity of genuine maximal-regularity solutions
is recorded by the companion solution fields (`maxRegHomogeneousSolField`,
`maxRegDuhamelSolField`).

This is a reducible abbreviation, so an element of `MaxRegSolutionSpace …` is
definitionally an element of `timeH1 …` and the `timeH1` API (`mk`, `init`,
`deriv`, `trace0`, `timeDeriv`, `toFun`, …) applies verbatim. -/
abbrev MaxRegSolutionSpace (a : ℝ) (T : ℝ) : Type _ :=
  timeH1 (tensorHs (I := I) (M := M) g r s a) T

/-- The `i`-th eigen-coordinate of the homogeneous heat flow `e^{tΔ_∇} u₀`:
the element of `L²(0,T)` represented by the continuous decay function
`t ↦ e^{−λᵢ t} · cᵢ`, with `cᵢ = u₀.coeff i`. -/
def homModeCoeff {a : ℝ}
    {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
      u₀.coeff i)
    (Continuous.continuousOn (by fun_prop))

/-- The `i`-th eigen-coordinate of the time derivative `Δ_∇ e^{tΔ_∇} u₀` of the
homogeneous heat flow: the element of `L²(0,T)` represented by the continuous
function `t ↦ −λᵢ · e^{−λᵢ t} · cᵢ`. -/
def homDerivModeCoeff {a : ℝ}
    {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => -(TensorEigenIdx.lambda (I := I) (M := M) i) *
      (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * u₀.coeff i))
    (Continuous.continuousOn (by fun_prop))

/-- The homogeneous-flow time-derivative coordinate is `−λᵢ` times the
homogeneous-flow coordinate: `homDerivModeCoeff u₀ i = −λᵢ • homModeCoeff u₀ i`,
an identity of `L²(0,T)` elements. -/
theorem homDerivModeCoeff_eq_smul
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i := by
  refine Lp.ext ?_
  have hderiv : ⇑(homDerivModeCoeff (I := I) (M := M) (a := a) (T := T)
        u₀ i) =ᵐ[timeMeasure T]
      fun t => -(TensorEigenIdx.lambda (I := I) (M := M) i) *
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * u₀.coeff i) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hmode : ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T)
        u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hsmul := Lp.coeFn_smul (-(TensorEigenIdx.lambda (I := I) (M := M) i))
    (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
  filter_upwards [hderiv, hmode, hsmul] with t htderiv htmode htsmul
  rw [htderiv, htsmul, Pi.smul_apply, htmode, smul_eq_mul]

/-- The squared `L²(0,T)` norm of the homogeneous-flow coordinate is bounded by
`T · cᵢ²`: the decay kernel is `≤ 1`, so `∫₀ᵀ (e^{−λᵢ t} cᵢ)² ≤ T · cᵢ²`. -/
theorem norm_homModeCoeff_sq_le (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 ≤
      T * (u₀.coeff i) ^ 2 := by
  rw [show homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i =
        TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
          (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            u₀.coeff i)
          (Continuous.continuousOn (by fun_prop)) from rfl]
  have hbound : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop))‖ ≤
      Real.sqrt T * |u₀.coeff i| := by
    refine TimeSobolev.norm_ofContinuousOn_le_of_bound _ (fun t ht => ?_)
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have hexp_le : Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have hexp_pos : 0 < Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
      Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt hexp_pos)]
    nlinarith [abs_nonneg (u₀.coeff i), hexp_le, hexp_pos]
  have hsq : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop))‖ ^ 2 ≤
      (Real.sqrt T * |u₀.coeff i|) ^ 2 := by
    have hrhs_nonneg : 0 ≤ Real.sqrt T * |u₀.coeff i| :=
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    nlinarith [hbound, norm_nonneg (TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
      (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i)
      (Continuous.continuousOn (by fun_prop))), hrhs_nonneg]
  calc ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
          (f := fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            u₀.coeff i)
          (Continuous.continuousOn (by fun_prop))‖ ^ 2
      ≤ (Real.sqrt T * |u₀.coeff i|) ^ 2 := hsq
    _ = T * (u₀.coeff i) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hT, sq_abs]

/-- **The weighted per-mode `H^{a+2}` bound for the homogeneous flow.**  For
every eigen-index `i`,

  `(1 + λᵢ)^{a+2} · ‖homModeCoeff u₀ i‖² ≤ T · (1 + λᵢ)^{a+2} · cᵢ²`. -/
theorem weighted_homModeCoeff_le (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i (a + 2) *
        ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 ≤
      T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
  have hbase :=
    norm_homModeCoeff_sq_le (I := I) (M := M) (a := a) (T := T) hT u₀ i
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
  calc tensorSobolevWeight (I := I) (M := M) i (a + 2) *
          ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) * (T * (u₀.coeff i) ^ 2) :=
        mul_le_mul_of_nonneg_left hbase hw_nonneg
    _ = T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
        ring

/-- The homogeneous-flow mode family `i ↦ homModeCoeff u₀ i` is
weighted-summable at the `H^{a+2}` scale. -/
theorem summable_homModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 2) *
      ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
  have hdom : Summable (fun i => T *
      (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2)) :=
    u₀.weighted_summable.mul_left T
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2))
      (sq_nonneg _)
  · exact weighted_homModeCoeff_le (I := I) (M := M) (a := a) (T := T) hT u₀ i

/-- The pointwise bound `(1 + λᵢ)ᵃ · ‖homDerivModeCoeff u₀ i‖² ≤ T · (1 +
λᵢ)^{a+2} · cᵢ²`: the time-derivative coordinate is `−λᵢ` times the homogeneous-
flow coordinate, and `λᵢ²` factors of the weight `(1 + λᵢ)²` upgrade scale `a`
to scale `a+2`. -/
theorem weighted_homDerivModeCoeff_le (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i a *
        ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 ≤
      T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hderiv_eq :=
    homDerivModeCoeff_eq_smul (I := I) (M := M) (a := a) (T := T) u₀ i
  have hnorm : ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 =
      lam ^ 2 *
        ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 := by
    rw [hderiv_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_pow,
      neg_one_sq, one_mul]
  have hmode :=
    norm_homModeCoeff_sq_le (I := I) (M := M) (a := a) (T := T) hT u₀ i
  have hweight : tensorSobolevWeight (I := I) (M := M) i a * (1 + lam) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (a + 2) := by
    have hexpand : tensorSobolevWeight (I := I) (M := M) i (a + 2) =
        (1 + lam) ^ (a + 2 : ℝ) := by rw [tensorSobolevWeight, hlam_def]
    have hbase : tensorSobolevWeight (I := I) (M := M) i a =
        (1 + lam) ^ (a : ℝ) := by rw [tensorSobolevWeight, hlam_def]
    rw [hexpand, hbase, ← Real.rpow_natCast (1 + lam) 2,
      ← Real.rpow_add hbase_pos]
    norm_num
  have hlam_sq_le : lam ^ 2 ≤ (1 + lam) ^ 2 := by nlinarith
  calc tensorSobolevWeight (I := I) (M := M) i a *
          ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2
      = tensorSobolevWeight (I := I) (M := M) i a *
          (lam ^ 2 *
            ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
        rw [hnorm]
    _ ≤ tensorSobolevWeight (I := I) (M := M) i a *
          ((1 + lam) ^ 2 * (T * (u₀.coeff i) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hw_nonneg
        have hmode_nn : 0 ≤ ‖homModeCoeff (I := I) (M := M)
            (a := a) (T := T) u₀ i‖ ^ 2 := sq_nonneg _
        have hT_c_nn : 0 ≤ T * (u₀.coeff i) ^ 2 :=
          mul_nonneg hT (sq_nonneg _)
        calc lam ^ 2 *
                ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2
            ≤ (1 + lam) ^ 2 *
                ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hlam_sq_le hmode_nn
          _ ≤ (1 + lam) ^ 2 * (T * (u₀.coeff i) ^ 2) :=
              mul_le_mul_of_nonneg_left hmode (sq_nonneg _)
    _ = T * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2) := by
        rw [← hweight]; ring

/-- The homogeneous-flow time-derivative mode family `i ↦ homDerivModeCoeff u₀ i`
is weighted-summable at the `Hᵃ` scale. -/
theorem summable_homDerivModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i a *
      ‖homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
  have hdom : Summable (fun i => T *
      (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i) ^ 2)) :=
    u₀.weighted_summable.mul_left T
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a)
      (sq_nonneg _)
  · exact weighted_homDerivModeCoeff_le (I := I) (M := M) (a := a) (T := T) hT u₀ i

/-- **The `H^{a+2}`-valued field of the homogeneous heat flow.**  For initial
datum `u₀ ∈ H^{a+2}`, this is the element of `L²([0,T]; H^{a+2})` whose `i`-th
eigen-coordinate is the scalar decay `t ↦ e^{−λᵢ t} · cᵢ`.  It is the homogeneous
flow `t ↦ e^{tΔ_∇} u₀` viewed in its full `H^{a+2}` spatial regularity. -/
def maxRegHomogeneousSolField (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T :=
  timeL2OfModes (I := I) (M := M) (σ := a + 2)
    (fun i => homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)

/-- The `i`-th eigen-coordinate of the homogeneous-flow field is the scalar decay
`t ↦ e^{−λᵢ t} · cᵢ`. -/
theorem maxRegHomogeneousSolField_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) i =
      homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a + 2) _
    (summable_homModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀) i

/-- The homogeneous-flow mode family is weighted-summable at the intermediate
`H^{a+1}` scale (it is summable at `a+2`, hence at any smaller exponent). -/
theorem summable_homModeCoeff_Ha1 (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      ‖homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    (summable_homModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀)
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1))
      (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (tensorSobolevWeight_mono (I := I) (M := M) i (by linarith)) (sq_nonneg _)

/-- **The `H^{a+1}`-view of the homogeneous heat-flow field.**  For initial datum
`u₀ ∈ H^{a+2}`, the element of `L²([0,T]; H^{a+1})` whose `i`-th eigen-coordinate
is the scalar decay `t ↦ e^{−λᵢ t} · cᵢ` — the homogeneous flow `e^{tΔ_∇} u₀`
viewed one Sobolev order below its full `H^{a+2}` regularity, the order at which
the subcritical small-time Duhamel field is measured. -/
def maxRegHomogeneousSolFieldHa1 (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T :=
  timeL2OfModes (I := I) (M := M) (σ := a + 1)
    (fun i => homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)

/-- The `i`-th eigen-coordinate of the `H^{a+1}`-view homogeneous-flow field is
the scalar decay `t ↦ e^{−λᵢ t} · cᵢ`. -/
theorem maxRegHomogeneousSolFieldHa1_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀) i =
      homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a + 1) _
    (summable_homModeCoeff_Ha1 (I := I) (M := M) (a := a) (T := T) hT u₀) i

/-- **The `Hᵃ`-valued time-derivative field of the homogeneous heat flow.**  For
initial datum `u₀ ∈ H^{a+2}`, this is the element of `L²([0,T]; Hᵃ)` whose `i`-th
eigen-coordinate is `t ↦ −λᵢ · e^{−λᵢ t} · cᵢ`.  It is `∂_t (e^{tΔ_∇} u₀) = Δ_∇
e^{tΔ_∇} u₀`. -/
def maxRegHomogeneousDerivField (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  timeL2OfModes (I := I) (M := M) (σ := a)
    (fun i => homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)

/-- The `i`-th eigen-coordinate of the homogeneous-flow time-derivative field is
`t ↦ −λᵢ · e^{−λᵢ t} · cᵢ`. -/
theorem maxRegHomogeneousDerivField_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousDerivField (I := I) (M := M) a T u₀) i =
      homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a) _
    (summable_homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀) i

/-- **The homogeneous part of the Duhamel map.**  For initial datum `u₀ ∈
H^{a+2}`, this is the homogeneous heat flow `t ↦ e^{tΔ_∇} u₀`, packaged as an
element of the solution space `E_T = H¹([0,T]; Hᵃ)`: its initial value is `u₀`
(included into `Hᵃ` via the spectral inclusion `H^{a+2} ↪ Hᵃ`) and its `L²` time
derivative is the homogeneous-flow time-derivative field `∂_t (e^{tΔ_∇} u₀)`. -/
def maxRegHomogeneous (a : ℝ) (T : ℝ)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := r) (s := s) a T :=
  TimeSobolev.timeH1.mk
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) u₀)
    (maxRegHomogeneousDerivField (I := I) (M := M) a T u₀)

/-- The initial value of the homogeneous part is `u₀`, included into `Hᵃ` via the
spectral inclusion `H^{a+2} ↪ Hᵃ`. -/
@[simp] theorem maxRegHomogeneous_init
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    (maxRegHomogeneous (I := I) (M := M) a T u₀).init =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ :=
  rfl

/-- **Initial condition of the homogeneous part.**  At `t = 0` the homogeneous
heat flow recovers the initial datum: `(maxRegHomogeneous … u₀)(0) = u₀`, with
the trace taken in `Hᵃ` via the spectral inclusion `H^{a+2} ↪ Hᵃ`. -/
theorem maxRegHomogeneous_trace0
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    TimeSobolev.timeH1.trace0 _ T
        (maxRegHomogeneous (I := I) (M := M) a T u₀) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ :=
  rfl

/-- The `L²` time derivative of the homogeneous part is the homogeneous-flow
time-derivative field. -/
@[simp] theorem maxRegHomogeneous_deriv
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    (maxRegHomogeneous (I := I) (M := M) a T u₀).deriv =
      maxRegHomogeneousDerivField (I := I) (M := M) a T u₀ :=
  rfl

/-- Chart-locality-free version of
`maxRegHomogeneousDerivField_eq_scaleLaplacian`, parameterized on resolvent
compactness `h_compact`: `∂_t (e^{tΔ_∇} u₀) = Δ_∇ (e^{tΔ_∇} u₀)`. -/
theorem maxRegHomogeneousDerivField_eq_scaleLaplacian (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    maxRegHomogeneousDerivField (I := I) (M := M) a T u₀ =
      timeScaleLaplacian (I := I) (M := M) a
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maxRegHomogeneousDerivField_timeModeCoeff (I := I) (M := M) (a := a)
      (T := T) hT u₀ i,
    timeModeCoeff_timeScaleLaplacian (I := I) (M := M) (τ := a)
      (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) i,
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a)
      (T := T) hT u₀ i]
  exact homDerivModeCoeff_eq_smul (I := I) (M := M) (a := a) (T := T) u₀ i

/-- Chart-locality-free version of `maxRegHomogeneous_timeDeriv_eq`,
parameterized on resolvent compactness `h_compact`:
`∂_t (maxRegHomogeneous … u₀) = Δ_∇ (maxRegHomogeneousSolField … u₀)`. -/
theorem maxRegHomogeneous_timeDeriv_eq (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maxRegHomogeneous (I := I) (M := M) a T u₀) =
      timeScaleLaplacian (I := I) (M := M) a
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) := by
  rw [TimeSobolev.timeH1.timeDeriv_apply, maxRegHomogeneous_deriv (I := I) (M := M)
    (a := a) (T := T) u₀]
  exact maxRegHomogeneousDerivField_eq_scaleLaplacian (I := I) (M := M)
    (h_compact := h_compact) (a := a) (T := T) hT u₀

/-- Chart-locality-free version of `maximalRegularityDerivField_add`,
parameterized on resolvent compactness `h_compact`. -/
theorem maximalRegularityDerivField_add (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityDerivField (I := I) (M := M) a hT (f + f') =
      maximalRegularityDerivField (I := I) (M := M) a hT f +
        maximalRegularityDerivField (I := I) (M := M) a hT f' := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT (f + f') i,
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i,
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f' i]
  rw [derivModeCoeff, derivModeCoeff, derivModeCoeff,
    timeModeCoeff_add (I := I) (M := M), map_add]

/-- Chart-locality-free version of `maximalRegularityDerivField_smul`,
parameterized on resolvent compactness `h_compact`. -/
theorem maximalRegularityDerivField_smul (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (c : ℝ) (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityDerivField (I := I) (M := M) a hT (c • f) =
      c • maximalRegularityDerivField (I := I) (M := M) a hT f := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT (c • f) i,
    timeModeCoeff_smul (I := I) (M := M),
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i]
  rw [derivModeCoeff, derivModeCoeff, timeModeCoeff_smul (I := I) (M := M),
    map_smul]

/-- Chart-locality-free version of `maximalRegularityOp_add`, parameterized on
resolvent compactness `h_compact`. -/
theorem maximalRegularityOp_add (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityOp (I := I) (M := M) a hT hT1 (f + f') =
      maximalRegularityOp (I := I) (M := M) a hT hT1 f +
        maximalRegularityOp (I := I) (M := M) a hT hT1 f' := by
  refine TimeSobolev.timeH1.ext ?_ ?_
  · rw [TimeSobolev.timeH1.init_add]
    change (0 : tensorHs (I := I) (M := M) g r s a) =
      (0 : tensorHs (I := I) (M := M) g r s a) +
        (0 : tensorHs (I := I) (M := M) g r s a)
    rw [add_zero]
  · rw [TimeSobolev.timeH1.deriv_add]
    exact maximalRegularityDerivField_add (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le f f'

/-- Chart-locality-free version of `maximalRegularityOp_smul`, parameterized on
resolvent compactness `h_compact`. -/
theorem maximalRegularityOp_smul (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (c : ℝ) (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityOp (I := I) (M := M) a hT hT1 (c • f) =
      c • maximalRegularityOp (I := I) (M := M) a hT hT1 f := by
  refine TimeSobolev.timeH1.ext ?_ ?_
  · rw [TimeSobolev.timeH1.init_smul]
    change (0 : tensorHs (I := I) (M := M) g r s a) =
      c • (0 : tensorHs (I := I) (M := M) g r s a)
    rw [smul_zero]
  · rw [TimeSobolev.timeH1.deriv_smul]
    exact maximalRegularityDerivField_smul (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le c f

/-- Chart-locality-free version of `maximalRegularityOp_sub`, parameterized on
resolvent compactness `h_compact`. -/
theorem maximalRegularityOp_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityOp (I := I) (M := M) a hT hT1 (f - f') =
      maximalRegularityOp (I := I) (M := M) a hT hT1 f -
        maximalRegularityOp (I := I) (M := M) a hT hT1 f' := by
  have hadd := maximalRegularityOp_add (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

/-- **The `H^{a+2}`-valued field of the affine Duhamel map.**  For initial datum
`u₀ ∈ H^{a+2}` and forcing term `g ∈ L²([0,T]; Hᵃ)`, this is the element of
`L²([0,T]; H^{a+2})` representing the candidate solution in its full `H^{a+2}`
spatial regularity: the sum of the homogeneous-flow field and the
maximal-regularity solution field of the forcing. -/
def maxRegDuhamelSolField (a : ℝ) {T : ℝ} (hT : 0 < T) (_hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T :=
  maxRegHomogeneousSolField (I := I) (M := M) a T u₀ +
    maximalRegularitySolField (I := I) (M := M) a hT.le gforce

/-- **The `H^{a+1}`-view of the affine Duhamel field.**  For initial datum `u₀ ∈
H^{a+2}` and forcing term `g ∈ L²([0,T]; Hᵃ)`, the element of `L²([0,T]; H^{a+1})`
representing the candidate solution one Sobolev order below its full regularity:
the sum of the `H^{a+1}`-view homogeneous-flow field and the `H^{a+1}`-view
maximal-regularity solution field of the forcing.  It is the field on which the
subcritical nonlinearity `N : H^{a+1} → Hᵃ` is evaluated in the small-time
fixed-point construction. -/
def maxRegDuhamelSolFieldHa1 (a : ℝ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T :=
  maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ +
    maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 gforce

/-- **The affine Duhamel solution map.**  For initial datum `u₀ ∈ H^{a+2}` and
forcing term `g ∈ L²([0,T]; Hᵃ)`,

  `maxRegDuhamelMap … u₀ g := (homogeneous part) + maximalRegularityOp g`,

an element of the solution space `E_T = H¹([0,T]; Hᵃ)`.  It represents `t ↦
e^{tΔ_∇} u₀ + ∫₀ᵗ e^{(t−s)Δ_∇} g(s) ds`, the Duhamel mild solution of `∂_t u =
Δ_∇ u + g`, `u(0) = u₀`.  The candidate strong solution of the quasi-linear
equation `∂_t u = Δ_∇ u + N(u)` is the fixed point `u = maxRegDuhamelMap … u₀
(N ∘ u)`. -/
def maxRegDuhamelMap (a : ℝ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := r) (s := s) a T :=
  maxRegHomogeneous (I := I) (M := M) a T u₀ +
    maximalRegularityOp (I := I) (M := M) a hT hT1 gforce

/-- The initial value of the affine Duhamel map is `u₀` (included into `Hᵃ` via
the spectral inclusion `H^{a+2} ↪ Hᵃ`): the maximal-regularity operator
contributes `0` to the trace, so the trace of the Duhamel image is the trace of
the homogeneous part. -/
@[simp] theorem maxRegDuhamelMap_init (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).init =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ := by
  rw [maxRegDuhamelMap, TimeSobolev.timeH1.init_add,
    maxRegHomogeneous_init (I := I) (M := M) (a := a) (T := T) u₀]
  rw [show (maximalRegularityOp (I := I) (M := M) a hT hT1 gforce).init =
        (0 : tensorHs (I := I) (M := M) g r s a) from rfl, add_zero]

/-- **Initial condition of the affine Duhamel map.**  At `t = 0` the Duhamel
image recovers the initial datum: `(maxRegDuhamelMap … u₀ g)(0) = u₀`, with the
trace taken in `Hᵃ` via the spectral inclusion `H^{a+2} ↪ Hᵃ`. -/
theorem maxRegDuhamelMap_trace0 (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ := by
  rw [TimeSobolev.timeH1.trace0_apply]
  exact maxRegDuhamelMap_init (I := I) (M := M) (a := a) (T := T) hT hT1 u₀ gforce

/-- The `L²` time derivative of the affine Duhamel map splits as the sum of the
homogeneous-flow time-derivative field and the maximal-regularity time-
derivative field. -/
@[simp] theorem maxRegDuhamelMap_deriv (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv =
      maxRegHomogeneousDerivField (I := I) (M := M) a T u₀ +
        maximalRegularityDerivField (I := I) (M := M) a hT.le gforce := by
  rw [maxRegDuhamelMap, TimeSobolev.timeH1.deriv_add]
  rfl

/-- Chart-locality-free version of `maxRegDuhamelMap_timeDeriv_eq`,
parameterized on resolvent compactness `h_compact`: the Duhamel image solves
`∂_t u = Δ_∇ u + g` as an identity of `L²([0,T]; Hᵃ)` elements. -/
theorem maxRegDuhamelMap_timeDeriv_eq (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) =
      timeScaleLaplacian (I := I) (M := M) a
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
        gforce := by
  rw [TimeSobolev.timeH1.timeDeriv_apply,
    maxRegDuhamelMap_deriv (I := I) (M := M) (a := a) (T := T) hT hT1 u₀ gforce]
  rw [maxRegHomogeneousDerivField_eq_scaleLaplacian (I := I) (M := M)
    (h_compact := h_compact) (a := a) (T := T) hT.le u₀]
  have hsolve := maximalRegularityOp_solves (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce
  rw [maximalRegularityOp_timeDeriv (I := I) (M := M)
    (a := a) hT hT1 gforce] at hsolve
  rw [hsolve]
  rw [maxRegDuhamelSolField, map_add]
  abel

/-- Chart-locality-free version of `maxRegDuhamelMap_dist_le`, parameterized on
resolvent compactness `h_compact`:
`‖maxRegDuhamelMap … u₀ g − maxRegDuhamelMap … u₀ g'‖ ≤ 2·‖g − g'‖`. -/
theorem maxRegDuhamelMap_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce'‖ ≤
      2 * ‖gforce - gforce'‖ := by
  have hdiff : maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce' =
      maximalRegularityOp (I := I) (M := M) a hT hT1
        (gforce - gforce') := by
    rw [maximalRegularityOp_sub (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce gforce']
    change (maxRegHomogeneous (I := I) (M := M) a T u₀ +
          maximalRegularityOp (I := I) (M := M) a hT hT1 gforce) -
        (maxRegHomogeneous (I := I) (M := M) a T u₀ +
          maximalRegularityOp (I := I) (M := M) a hT hT1 gforce') =
      maximalRegularityOp (I := I) (M := M) a hT hT1 gforce -
        maximalRegularityOp (I := I) (M := M) a hT hT1 gforce'
    abel
  rw [hdiff]
  exact maximalRegularityOp_norm_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (gforce - gforce')

/-- Chart-locality-free version of `maxRegDuhamelMap_lipschitzWith`,
parameterized on resolvent compactness `h_compact`: for a fixed initial datum
`u₀`, the map `g ↦ maxRegDuhamelMap … u₀ g` is Lipschitz with constant `2`. -/
theorem maxRegDuhamelMap_lipschitzWith (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) :
    LipschitzWith 2 (fun gforce :
        timeL2 (tensorHs (I := I) (M := M) g r s a) T =>
      maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) := by
  refine LipschitzWith.of_dist_le_mul (fun gforce gforce' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have h := maxRegDuhamelMap_dist_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce'
  rw [show ((2 : ℝ≥0) : ℝ) = (2 : ℝ) from by norm_num]
  exact h

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
