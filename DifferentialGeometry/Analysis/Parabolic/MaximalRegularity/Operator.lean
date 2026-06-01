import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Synthesis

/-!
# The `L²`-maximal-regularity operator for the inhomogeneous heat equation

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a Sobolev exponent
`a ≥ 0` and a time horizon `0 < T ≤ 1`, this file constructs the **Duhamel
solution operator** of the inhomogeneous heat equation

  `∂_t u = Δ_∇ u + f`,  `u(0) = 0`,

with forcing `f ∈ L²([0,T]; Hᵃ)`, and proves the `L²`-maximal-regularity
estimates: the solution gains *two* Sobolev derivatives over the forcing.

## Mathematical content

After the spatial spectral decomposition the inhomogeneous heat equation
decouples mode by mode.  On the eigen-coordinate belonging to the connection-
Laplacian eigenvalue `λᵢ ≥ 0` the Duhamel formula `u(t) = ∫₀ᵗ e^{(t−s)Δ_∇} f(s)
ds` reduces to the scalar per-mode convolution `φᵢ = perModeConvL2 λᵢ fᵢ`, where
`fᵢ = timeModeCoeff f i`.  The solution is the time-dependent field with
`timeModeCoeff u i = φᵢ`.

The **maximal-regularity bounds** (the deliverables), with `C(T) = 1 + T`:

* `u ∈ L²([0,T]; H^{a+2})` with `‖u‖_{L²([0,T];H^{a+2})} ≤ C(T)·‖f‖_{L²([0,T];Hᵃ)}`
  — the two-derivative gain.  Per mode `(1 + λᵢ)·‖φᵢ‖ ≤ C(T)·‖fᵢ‖`, uniform in
  `λᵢ ≥ 0`.
* `∂_t u ∈ L²([0,T]; Hᵃ)` with `‖∂_t u‖_{L²([0,T];Hᵃ)} ≤ 2·‖f‖_{L²([0,T];Hᵃ)}`.
* `u(0) = 0`.

## Main definitions

* `maximalRegularityDerivField a hT f` — the time derivative `∂_t u`,
  an element of `L²([0,T]; Hᵃ)`, with `i`-th mode `fᵢ − λᵢ·φᵢ`.
* `maximalRegularitySolField a hT f` — the solution `u`, viewed as
  an element of `L²([0,T]; H^{a+2})` (the two-derivative-gain regularity).
* `maximalRegularityOp a hT hT1 f` — the solution operator, landing in
  the strong-solution space `H¹([0,T]; Hᵃ)` (initial value `0`, `L²` time
  derivative `∂_t u`).

## Main results

* `maximalRegularitySolField_timeModeCoeff` — the `i`-th mode of the
  solution is `perModeConvL2 λᵢ (timeModeCoeff f i)`.
* `maximalRegularityOp_norm_Ha2_le` — the `H^{a+2}`
  maximal-regularity bound.
* `maximalRegularityOp_norm_deriv_le` — the `∂_t` bound.
* `maximalRegularityOp_trace0` — the initial condition `u(0) = 0`.
* `maximalRegularityOp_norm_le` — the combined `H¹`-graph-norm bound.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

/-- The per-mode solution coordinate: `perModeConvL2 λᵢ (timeModeCoeff f i)`,
the convolution of the `i`-th eigen-coordinate of the forcing against the heat
kernel of eigenvalue `λᵢ`. -/
def solModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  perModeConvL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)

/-- The per-mode time-derivative coordinate: `perModeConvDerivL2 λᵢ (timeModeCoeff
f i)`, the right-hand side `fᵢ − λᵢ·φᵢ` of the per-mode scalar ODE. -/
def derivModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) : timeL2 ℝ T :=
  perModeConvDerivL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)

/-- The auxiliary per-mode bound on the convolution itself:
`‖perModeConvL2 λᵢ (timeModeCoeff f i)‖ ≤ T · ‖timeModeCoeff f i‖`. -/
theorem norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      T * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  rw [solModeCoeff, perModeConvL2_apply]
  exact norm_perModeConvL2Fun_le (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT _

/-- The per-mode maximal-regularity estimate `λᵢ · ‖φᵢ‖ ≤ ‖fᵢ‖`. -/
theorem lambda_mul_norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorEigenIdx.lambda (I := I) (M := M) i *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  have hbase := perModeConvL2_sq_le (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (tensor_lambda_nonneg (I := I) (M := M) i)] at hbase
  exact hbase

/-- **The per-mode two-derivative-gain estimate.**  For `0 ≤ T`,

  `(1 + λᵢ) · ‖φᵢ‖ ≤ (1 + T) · ‖fᵢ‖`,

the per-mode bound underlying the `H^{a+2}` maximal-regularity estimate.  It is
the sum of the convolution bound `‖φᵢ‖ ≤ T‖fᵢ‖` and the maximal-regularity
estimate `λᵢ‖φᵢ‖ ≤ ‖fᵢ‖`. -/
theorem one_add_lambda_mul_norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  have h1 := norm_solModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have h2 := lambda_mul_norm_solModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have hexpand : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖
      = ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ +
        TensorEigenIdx.lambda (I := I) (M := M) i *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ := by ring
  rw [hexpand]
  calc ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ +
        TensorEigenIdx.lambda (I := I) (M := M) i *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖
      ≤ T * ‖timeModeCoeff (I := I) (M := M) f i‖ +
          ‖timeModeCoeff (I := I) (M := M) f i‖ := by gcongr
    _ = (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ := by ring

/-- **The per-mode half-derivative-gain estimate.**  For `0 ≤ T`,

  `√λᵢ · ‖φᵢ‖ ≤ √T · ‖fᵢ‖`.

This is the geometric-mean interpolation `(√λᵢ‖φᵢ‖)² = (λᵢ‖φᵢ‖)·‖φᵢ‖ ≤
‖fᵢ‖·(T‖fᵢ‖)` between the maximal-regularity estimate `λᵢ‖φᵢ‖ ≤ ‖fᵢ‖`
(`lambda_mul_norm_solModeCoeff_le`) and the convolution bound `‖φᵢ‖ ≤ T‖fᵢ‖`
(`norm_solModeCoeff_le`).  Unlike the two-derivative gain it carries the
parabolic factor `√T`, which `→ 0` as `T → 0`. -/
theorem sqrt_lambda_mul_norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Real.sqrt (TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  set φ := ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ with hφ_def
  set ff := ‖timeModeCoeff (I := I) (M := M) f i‖ with hff_def
  have hφ_nn : 0 ≤ φ := norm_nonneg _
  have hff_nn : 0 ≤ ff := norm_nonneg _
  have h1 : φ ≤ T * ff := norm_solModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have h2 : lam * φ ≤ ff :=
    lambda_mul_norm_solModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have hlhs_nn : 0 ≤ Real.sqrt lam * φ :=
    mul_nonneg (Real.sqrt_nonneg _) hφ_nn
  have hrhs_nn : 0 ≤ Real.sqrt T * ff :=
    mul_nonneg (Real.sqrt_nonneg _) hff_nn
  have hsqL : (Real.sqrt lam * φ) ^ 2 = lam * φ * φ := by
    rw [mul_pow, Real.sq_sqrt hlam_nn]; ring
  have hsqR : (Real.sqrt T * ff) ^ 2 = T * ff * ff := by
    rw [mul_pow, Real.sq_sqrt hT]; ring
  have hsq_le : (Real.sqrt lam * φ) ^ 2 ≤ (Real.sqrt T * ff) ^ 2 := by
    rw [hsqL, hsqR]
    calc lam * φ * φ ≤ ff * φ := mul_le_mul_of_nonneg_right h2 hφ_nn
      _ ≤ ff * (T * ff) := mul_le_mul_of_nonneg_left h1 hff_nn
      _ = T * ff * ff := by ring
  nlinarith [hsq_le, hlhs_nn, hrhs_nn]

/-- **The per-mode one-derivative-gain estimate with `√T` decay.**  For
`0 < T ≤ 1`,

  `(1 + λᵢ)^{1/2} · ‖φᵢ‖ ≤ 2·√T · ‖fᵢ‖`.

The per-mode bound underlying the `H^{a+1}` maximal-regularity estimate with
parabolic decay.  It uses `√(1 + λᵢ) ≤ 1 + √λᵢ`, the convolution bound `‖φᵢ‖ ≤
T‖fᵢ‖ ≤ √T‖fᵢ‖` (for `T ≤ 1`), and the half-gain estimate `√λᵢ·‖φᵢ‖ ≤
√T·‖fᵢ‖`. -/
theorem one_add_lambda_sqrt_mul_norm_solModeCoeff_le (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (1 / 2 : ℝ) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ≤
      2 * Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖ := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_nn : (0 : ℝ) ≤ 1 + lam := by linarith
  set φ := ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ with hφ_def
  set ff := ‖timeModeCoeff (I := I) (M := M) f i‖ with hff_def
  have hφ_nn : 0 ≤ φ := norm_nonneg _
  have hff_nn : 0 ≤ ff := norm_nonneg _
  have hsqrt_le : (1 + lam) ^ (1 / 2 : ℝ) ≤ 1 + Real.sqrt lam := by
    have hrw : (1 + lam) ^ (1 / 2 : ℝ) = Real.sqrt (1 + lam) := by
      rw [Real.sqrt_eq_rpow]
    rw [hrw]
    have hsl_nn : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ 1 + Real.sqrt lam := by linarith
    have hsl_sq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam_nn
    rw [show (1 + Real.sqrt lam) = Real.sqrt ((1 + Real.sqrt lam) ^ 2) from
      (Real.sqrt_sq hrhs_nn).symm]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [hsl_nn, hsl_sq]
  have hconv : φ ≤ Real.sqrt T * ff := by
    have hTle : T ≤ Real.sqrt T := by
      have hsqrt_ge : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
      have hsqrt_le_one : Real.sqrt T ≤ 1 :=
        Real.sqrt_le_one.mpr hT1
      nlinarith [Real.sqrt_nonneg T, hsqrt_ge, hsqrt_le_one]
    calc φ ≤ T * ff := norm_solModeCoeff_le (I := I) (M := M) (a := a) hT.le f i
      _ ≤ Real.sqrt T * ff := mul_le_mul_of_nonneg_right hTle hff_nn
  have hhalf : Real.sqrt lam * φ ≤ Real.sqrt T * ff :=
    sqrt_lambda_mul_norm_solModeCoeff_le (I := I) (M := M) (a := a) hT.le f i
  calc (1 + lam) ^ (1 / 2 : ℝ) * φ
      ≤ (1 + Real.sqrt lam) * φ := mul_le_mul_of_nonneg_right hsqrt_le hφ_nn
    _ = φ + Real.sqrt lam * φ := by ring
    _ ≤ Real.sqrt T * ff + Real.sqrt T * ff := by gcongr
    _ = 2 * Real.sqrt T * ff := by ring

/-- The per-mode time-derivative estimate `‖fᵢ − λᵢ·φᵢ‖ ≤ 2·‖fᵢ‖`. -/
theorem norm_derivModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ≤
      2 * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
  perModeConvDerivL2_sq_le (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f i)

/-- The spectral weight at `σ + 2` factors as the weight at `σ` times
`(1 + λᵢ)²`. -/
private theorem tensorSobolevWeight_add_two
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ + 2) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight, Real.rpow_add hbase_pos,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-- **The weighted per-mode `H^{a+2}` bound.**  For every eigen-index `i`,

  `(1 + λᵢ)^{a+2} · ‖φᵢ‖² ≤ (1 + T)² · (1 + λᵢ)ᵃ · ‖fᵢ‖²`. -/
theorem weighted_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i (a + 2) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
      (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  have hperMode := one_add_lambda_mul_norm_solModeCoeff_le (I := I) (M := M)
    (a := a) hT f i
  have hwa_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hlam_nonneg : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hsol_nonneg : 0 ≤ ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
    norm_nonneg _
  have hsq : ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2 ≤
      ((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
    have hrhs_nonneg : 0 ≤ (1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
    have hlhs_nonneg : 0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ :=
      mul_nonneg hlam_nonneg hsol_nonneg
    nlinarith [hperMode, hlhs_nonneg, hrhs_nonneg]
  calc tensorSobolevWeight (I := I) (M := M) i (a + 2) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2
      = tensorSobolevWeight (I := I) (M := M) i a *
          (((1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
            ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖) ^ 2) := by
        rw [tensorSobolevWeight_add_two (I := I) (M := M) i a]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i a *
          (((1 + T) * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = (1 + T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring

/-- The spectral weight at `σ + 1` factors as the weight at `σ` times
`(1 + λᵢ)`. -/
private theorem tensorSobolevWeight_add_one
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ + 1) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight, Real.rpow_add hbase_pos,
    Real.rpow_one]

/-- **The weighted per-mode `H^{a+1}` bound with `T`-decay.**  For `0 < T ≤ 1`
and every eigen-index `i`,

  `(1 + λᵢ)^{a+1} · ‖φᵢ‖² ≤ (2√T)² · (1 + λᵢ)ᵃ · ‖fᵢ‖²`.

The constant `(2√T)² = 4T → 0` as `T → 0`, the source of the small-time
contraction.  It is the squared one-derivative-gain estimate
`one_add_lambda_sqrt_mul_norm_solModeCoeff_le`, weighted by `(1 + λᵢ)ᵃ` and using
that `(1 + λᵢ)^{a+1} = (1 + λᵢ)ᵃ · ((1 + λᵢ)^{1/2})²`. -/
theorem weighted_solModeCoeff_Ha1_le (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ^ 2 ≤
      (2 * Real.sqrt T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_nn : (0 : ℝ) ≤ 1 + lam := by linarith
  have hperMode := one_add_lambda_sqrt_mul_norm_solModeCoeff_le (I := I) (M := M)
    (a := a) hT hT1 f i
  have hwa_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsol_nonneg : 0 ≤ ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ :=
    norm_nonneg _
  have hweight_sq : (1 + lam) = ((1 + lam) ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast ((1 + lam) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hbase_nn]
    norm_num
  have hsq : ((1 + lam) ^ (1 / 2 : ℝ) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖) ^ 2 ≤
      (2 * Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
    have hlhs_nonneg : 0 ≤ (1 + lam) ^ (1 / 2 : ℝ) *
        ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ :=
      mul_nonneg (Real.rpow_nonneg hbase_nn _) hsol_nonneg
    have hrhs_nonneg : 0 ≤ 2 * Real.sqrt T *
        ‖timeModeCoeff (I := I) (M := M) f i‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    nlinarith [hperMode, hlhs_nonneg, hrhs_nonneg]
  calc tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ^ 2
      = tensorSobolevWeight (I := I) (M := M) i a *
          (((1 + lam) ^ (1 / 2 : ℝ) *
            ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖) ^ 2) := by
        rw [tensorSobolevWeight_add_one (I := I) (M := M) i a, hlam_def]
        rw [mul_pow]
        rw [← hweight_sq]; ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i a *
          ((2 * Real.sqrt T *
            ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = (2 * Real.sqrt T) ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring

/-- Chart-locality-free version, parameterized on
resolvent compactness `h_compact`: the mode family `i ↦ φᵢ` of solution
coordinates is weighted-summable at the `H^{a+1}` scale (`0 < T ≤ 1`), the
precondition for synthesising the `H^{a+1}`-valued solution field. -/
theorem summable_solModeCoeff_Ha1 (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      ‖solModeCoeff (I := I) (M := M) (a := a) hT.le f i‖ ^ 2) := by
  have hdom : Summable (fun i => (2 * Real.sqrt T) ^ 2 *
      (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1))
      (sq_nonneg _)
  · exact weighted_solModeCoeff_Ha1_le (I := I) (M := M) (a := a) hT hT1 f i

/-- Chart-locality-free version, parameterized on
resolvent compactness `h_compact`: the mode family `i ↦ φᵢ` of solution
coordinates is weighted-summable at the `H^{a+2}` scale. -/
theorem summable_solModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 2) *
      ‖solModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2) := by
  have hdom : Summable (fun i => (1 + T) ^ 2 *
      (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2))
      (sq_nonneg _)
  · exact weighted_solModeCoeff_le (I := I) (M := M) (a := a) hT f i

/-- **The weighted per-mode derivative bound.**  For every eigen-index `i`,

  `(1 + λᵢ)ᵃ · ‖fᵢ − λᵢ·φᵢ‖² ≤ 2² · (1 + λᵢ)ᵃ · ‖fᵢ‖²`. -/
theorem weighted_derivModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i a *
        ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
      2 ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  have hbase := norm_derivModeCoeff_le (I := I) (M := M) (a := a) hT f i
  have hwa_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsq : ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2 ≤
      2 ^ 2 * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
    nlinarith [hbase, norm_nonneg (derivModeCoeff (I := I) (M := M) (a := a) hT f i),
      norm_nonneg (timeModeCoeff (I := I) (M := M) f i)]
  calc tensorSobolevWeight (I := I) (M := M) i a *
          ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i a *
          (2 ^ 2 * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = 2 ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring

/-- Chart-locality-free version, parameterized on
resolvent compactness `h_compact`: the mode family `i ↦ fᵢ − λᵢ·φᵢ` of
time-derivative coordinates is weighted-summable at the `Hᵃ` scale. -/
theorem summable_derivModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i a *
      ‖derivModeCoeff (I := I) (M := M) (a := a) hT f i‖ ^ 2) := by
  have hdom : Summable (fun i => 2 ^ 2 *
      (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a)
      (sq_nonneg _)
  · exact weighted_derivModeCoeff_le (I := I) (M := M) (a := a) hT f i

/-- **The time-derivative field `∂_t u`.**  For a forcing term `f ∈ L²([0,T];
Hᵃ)`, this is the element of `L²([0,T]; Hᵃ)` whose `i`-th eigen-coordinate is
`fᵢ − λᵢ·φᵢ`, the per-mode scalar ODE right-hand side. -/
def maximalRegularityDerivField (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  timeL2OfModes (I := I) (M := M)
    (fun i => derivModeCoeff (I := I) (M := M) (a := a) hT f i)

/-- Chart-locality-free version,
parameterized on resolvent compactness `h_compact`: the `i`-th eigen-coordinate
of the time-derivative field is `fᵢ − λᵢ·φᵢ`. -/
theorem maximalRegularityDerivField_timeModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularityDerivField (I := I) (M := M) a hT f) i =
      derivModeCoeff (I := I) (M := M) (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) _
    (summable_derivModeCoeff (I := I) (M := M) (a := a) hT h_compact f) i

/-- **The solution field `u`, viewed in `L²([0,T]; H^{a+2})`.**  For a forcing
term `f ∈ L²([0,T]; Hᵃ)`, this is the element of `L²([0,T]; H^{a+2})` whose
`i`-th eigen-coordinate is `φᵢ = perModeConvL2 λᵢ fᵢ`.  The two-derivative gain
(`H^{a+2}` from a forcing in `Hᵃ`) is exactly what the maximal-regularity bound
quantifies. -/
def maximalRegularitySolField (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T :=
  timeL2OfModes (I := I) (M := M)
    (fun i => solModeCoeff (I := I) (M := M) (a := a) hT f i)

/-- Chart-locality-free version,
parameterized on resolvent compactness `h_compact`: the `i`-th eigen-coordinate
of the solution field is `φᵢ = perModeConvL2 λᵢ (timeModeCoeff f i)`. -/
theorem maximalRegularitySolField_timeModeCoeff (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularitySolField (I := I) (M := M) a hT f) i =
      solModeCoeff (I := I) (M := M) (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) _
    (summable_solModeCoeff (I := I) (M := M) (a := a) hT h_compact f) i

/-- **The solution field `u`, viewed in `L²([0,T]; H^{a+1})`.**  For a forcing
term `f ∈ L²([0,T]; Hᵃ)` and `0 < T ≤ 1`, the element of `L²([0,T]; H^{a+1})`
whose `i`-th eigen-coordinate is `φᵢ = perModeConvL2 λᵢ fᵢ` — the same per-mode
coordinates as `maximalRegularitySolField`, synthesised one Sobolev order lower.
This is the one-derivative-gain (subcritical) view of the Duhamel solution, the
order at which the maximal-regularity smoothing carries the decaying constant
`2√T`. -/
def maximalRegularitySolFieldHa1 (a : ℝ) {T : ℝ} (hT : 0 < T) (_hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T :=
  timeL2OfModes (I := I) (M := M) (σ := a + 1)
    (fun i => solModeCoeff (I := I) (M := M) (a := a) hT.le f i)

/-- Chart-locality-free version,
parameterized on resolvent compactness `h_compact`: the `i`-th eigen-coordinate
of the `H^{a+1}`-view solution field is `φᵢ = perModeConvL2 λᵢ
(timeModeCoeff f i)`. -/
theorem maximalRegularitySolFieldHa1_timeModeCoeff (hT : 0 < T)
    (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 f) i =
      solModeCoeff (I := I) (M := M) (a := a) hT.le f i :=
  timeL2OfModes_timeModeCoeff (I := I) (M := M) (σ := a + 1) _
    (summable_solModeCoeff_Ha1 (I := I) (M := M) (a := a) hT hT1
      h_compact f) i

/-- Chart-locality-free version of `maximalRegularitySolFieldHa1_norm_le`
(the `H^{a+1}` one-derivative-gain bound with `√T`-decay), parameterized on
resolvent compactness `h_compact`:
`‖u‖_{L²([0,T];H^{a+1})} ≤ 2√T · ‖f‖_{L²([0,T];Hᵃ)}`. -/
theorem maximalRegularitySolFieldHa1_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 f‖ ≤
      2 * Real.sqrt T * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M) (b := a + 1)
    h_compact (C := 2 * Real.sqrt T)
    (by positivity) _ f (fun i => ?_)
  rw [maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 f i]
  exact weighted_solModeCoeff_Ha1_le (I := I) (M := M) (a := a) hT hT1 f i

/-- Chart-locality-free version: the `H^{a+1}`-view solution field is additive in
the forcing term. -/
theorem maximalRegularitySolFieldHa1_add (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 (f + f') =
      maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 f +
        maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 f' := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 (f + f') i,
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 f i,
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 f' i]
  rw [solModeCoeff, solModeCoeff, solModeCoeff,
    timeModeCoeff_add (I := I) (M := M), map_add]

/-- Chart-locality-free version: the `H^{a+1}`-view solution field commutes with
subtraction of forcing terms — the form consumed by the small-time contraction
estimate. -/
theorem maximalRegularitySolFieldHa1_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 (f - f') =
      maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 f -
        maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 f' := by
  have hadd := maximalRegularitySolFieldHa1_add (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

/-- **The `L²`-maximal-regularity operator.**  For a forcing term `f ∈ L²([0,T];
Hᵃ)`, `maximalRegularityOp a hT hT1 f` is the Duhamel solution of
`∂_t u = Δ_∇ u + f`, `u(0) = 0`, packaged as an element of the strong-solution
space `H¹([0,T]; Hᵃ)`: its initial value is `0` and its `L²` time derivative is
the time-derivative field `∂_t u`. -/
def maximalRegularityOp (a : ℝ) {T : ℝ} (hT : 0 < T) (_hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeH1 (tensorHs (I := I) (M := M) g r s a) T :=
  TimeSobolev.timeH1.mk (0 : tensorHs (I := I) (M := M) g r s a)
    (maximalRegularityDerivField (I := I) (M := M) a hT.le f)

@[simp] theorem maximalRegularityOp_trace0_eq
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maximalRegularityOp (I := I) (M := M) a hT hT1 f) =
      0 :=
  rfl

@[simp] theorem maximalRegularityOp_timeDeriv
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT hT1 f) =
      maximalRegularityDerivField (I := I) (M := M) a hT.le f :=
  rfl

/-- **Initial condition.**  The Duhamel solution vanishes at `t = 0`:
`u(0) = 0`. -/
theorem maximalRegularityOp_trace0 (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maximalRegularityOp (I := I) (M := M) a hT hT1 f) = 0 :=
  rfl

/-- Chart-locality-free version of `maximalRegularityOp_norm_Ha2_le`
(the `H^{a+2}` two-derivative-gain bound), parameterized on resolvent
compactness `h_compact`:
`‖u‖_{L²([0,T];H^{a+2})} ≤ (1 + T) · ‖f‖_{L²([0,T];Hᵃ)}`. -/
theorem maximalRegularityOp_norm_Ha2_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (_hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularitySolField (I := I) (M := M) a hT.le f‖ ≤
      (1 + T) * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M) (b := a + 2)
    h_compact (C := 1 + T) (by linarith [hT.le]) _ f (fun i => ?_)
  rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le f i]
  exact weighted_solModeCoeff_le (I := I) (M := M) (a := a) hT.le f i

/-- Chart-locality-free version of `maximalRegularityOp_norm_deriv_le`
(the `∂_t` bound), parameterized on resolvent compactness `h_compact`:
`‖∂_t u‖_{L²([0,T];Hᵃ)} ≤ 2 · ‖f‖_{L²([0,T];Hᵃ)}`. -/
theorem maximalRegularityOp_norm_deriv_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (_hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularityDerivField (I := I) (M := M) a hT.le f‖ ≤
      2 * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M) (b := a)
    h_compact (C := 2) (by norm_num) _ f (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le f i]
  exact weighted_derivModeCoeff_le (I := I) (M := M) (a := a) hT.le f i

/-- Chart-locality-free version of `maximalRegularityOp_norm_le` (the combined
`H¹`-graph-norm bound), parameterized on resolvent compactness `h_compact`:
`‖maximalRegularityOp f‖_{H¹([0,T];Hᵃ)} ≤ 2 · ‖f‖_{L²([0,T];Hᵃ)}`. -/
theorem maximalRegularityOp_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularityOp (I := I) (M := M) a hT hT1 f‖ ≤ 2 * ‖f‖ := by
  have hnormsq := TimeSobolev.timeH1.norm_sq_eq
    (maximalRegularityOp (I := I) (M := M) a hT hT1 f)
  have hinit : (maximalRegularityOp (I := I) (M := M) a hT hT1 f).init = 0 :=
    rfl
  have hderiv : (maximalRegularityOp (I := I) (M := M) a hT hT1 f).deriv =
      maximalRegularityDerivField (I := I) (M := M) a hT.le f := rfl
  have hderiv_le := maximalRegularityOp_norm_deriv_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 f
  have hsq : ‖maximalRegularityOp (I := I) (M := M) a hT hT1 f‖ ^ 2 ≤
      (2 * ‖f‖) ^ 2 := by
    rw [hnormsq, hinit, hderiv, norm_zero]
    have h2f_nonneg : 0 ≤ 2 * ‖f‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    nlinarith [hderiv_le, norm_nonneg
      (maximalRegularityDerivField (I := I) (M := M) a hT.le f)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (by norm_num) (norm_nonneg _))] at h

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
