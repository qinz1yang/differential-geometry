import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator

/-!
# The maximal-regularity operator solves the inhomogeneous heat equation

This file completes the construction of the `L²`-maximal-regularity operator
(`Operator.lean`) by proving that its output `u = maximalRegularityOp f` solves
the inhomogeneous heat equation

  `∂_t u = Δ_∇ u + f`

in the time-`L²` sense, as an identity of `L²([0,T]; Hᵃ)` elements.

## The rough Laplacian on the spectral scale

The connection (rough) Laplacian `Δ_∇` acts diagonally on the eigenbasis: on the
`i`-th eigen-coordinate it is multiplication by the connection-Laplacian
eigenvalue, with the geometer sign convention `Δ_∇ = -∇*∇` giving eigenvalue
`-λᵢ` (`λᵢ ≥ 0`).  Squaring the eigen-coordinate, the `Hˢ`-weight `(1 + λᵢ)ˢ`
absorbs two factors of `(1 + λᵢ)`, so `Δ_∇` maps `H^{τ+2}` boundedly to `Hᵗ`:
it gains exactly two Sobolev derivatives of room — equivalently, it loses two.

* `tensorScaleLaplacian τ` — the diagonal operator `Δ_∇ : H^{τ+2}
  →L[ℝ] Hᵗ`, multiplying the `i`-th coordinate by `-λᵢ`.
* `timeScaleLaplacian τ` — its action on time-`L²` tensor fields,
  `L²([0,T]; H^{τ+2}) →L[ℝ] L²([0,T]; Hᵗ)`.

## Main result

* `maximalRegularityOp_solves` — `∂_t u = Δ_∇ u + f`: the time derivative of the
  solution equals the rough Laplacian of the solution plus the forcing, as an
  identity in `L²([0,T]; Hᵃ)`.  Mode by mode this is the per-mode scalar ODE
  `φᵢ' = -λᵢ·φᵢ + fᵢ`.
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

variable {τ : ℝ}

/-- The base inequality `λᵢ² ≤ (1 + λᵢ)²` for the connection-Laplacian
eigenvalue `λᵢ ≥ 0`. -/
private theorem lambda_sq_le (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 := by
  have hlam := tensor_lambda_nonneg (I := I) (M := M) i
  nlinarith

/-- The spectral weight identity `(1 + λᵢ)ᵗ · (1 + λᵢ)² = (1 + λᵢ)^{τ+2}`. -/
private theorem scaleLaplacianWeightMulTwo
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i τ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (τ + 2) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight,
    ← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) 2,
    ← Real.rpow_add hbase_pos]
  norm_num

/-- The pointwise bound `(1 + λᵢ)ᵗ · (λᵢ · v_i)² ≤ (1 + λᵢ)^{τ+2} · v_i²`. -/
private theorem weightLambdaMulSqLe
    (v : tensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i τ *
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i (τ + 2) * (v.coeff i) ^ 2 := by
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i τ
  have hsq : (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2 ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 * (v.coeff i) ^ 2 := by
    have h := lambda_sq_le (I := I) (M := M) i
    nlinarith [sq_nonneg (v.coeff i), h]
  calc tensorSobolevWeight (I := I) (M := M) i τ *
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i τ *
          ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 *
            (v.coeff i) ^ 2) := mul_le_mul_of_nonneg_left hsq hw_nonneg
    _ = tensorSobolevWeight (I := I) (M := M) i (τ + 2) * (v.coeff i) ^ 2 := by
        rw [← mul_assoc, scaleLaplacianWeightMulTwo (I := I) (M := M) i]

/-- The coordinate family `i ↦ -λᵢ · v_i` is weighted-summable at the scale
`τ` whenever `v ∈ H^{τ+2}`: the rough Laplacian of `v` lies in `Hᵗ`. -/
private theorem scaleLaplacianWeightedSummable
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i τ *
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) v.weighted_summable
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i τ)
      (sq_nonneg _)
  · exact weightLambdaMulSqLe (I := I) (M := M) v i

/-- The underlying coordinate function of the rough Laplacian on the spectral
scale: it multiplies the `i`-th coordinate by `-λᵢ`, carrying `H^{τ+2}` into
`Hᵗ`. -/
def scaleLaplacianFun (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    tensorHs (I := I) (M := M) g r s τ where
  coeff i := -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i
  weighted_summable := scaleLaplacianWeightedSummable (I := I) (M := M) v

@[simp] theorem scaleLaplacianFun_coeff
    (v : tensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (scaleLaplacianFun (I := I) (M := M) v).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i := rfl

/-- The rough Laplacian on the scale is additive. -/
theorem scaleLaplacianFun_add
    (v w : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    scaleLaplacianFun (I := I) (M := M) (v + w) =
      scaleLaplacianFun (I := I) (M := M) v + scaleLaplacianFun (I := I) (M := M) w := by
  refine tensorHs.ext (funext (fun i => ?_))
  simp only [scaleLaplacianFun_coeff, tensorHs.add_coeff]
  ring

/-- The rough Laplacian on the scale is `ℝ`-homogeneous. -/
theorem scaleLaplacianFun_smul (c : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    scaleLaplacianFun (I := I) (M := M) (c • v) =
      c • scaleLaplacianFun (I := I) (M := M) v := by
  refine tensorHs.ext (funext (fun i => ?_))
  simp only [scaleLaplacianFun_coeff, tensorHs.smul_coeff]
  ring

/-- The rough Laplacian on the scale is norm-non-increasing:
`‖Δ_∇ v‖_{Hᵗ} ≤ ‖v‖_{H^{τ+2}}`. -/
theorem norm_scaleLaplacianFun_le
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    ‖scaleLaplacianFun (I := I) (M := M) v‖ ≤ ‖v‖ := by
  have hsq : ‖scaleLaplacianFun (I := I) (M := M) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M),
      tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((scaleLaplacianFun (I := I) (M := M) v).weighted_summable)
      v.weighted_summable
    rw [scaleLaplacianFun_coeff]
    exact weightLambdaMulSqLe (I := I) (M := M) v i
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- **The rough Laplacian on the spectral Sobolev scale**, as a continuous
linear operator `Δ_∇ : H^{τ+2} →L[ℝ] Hᵗ`.  It multiplies the `i`-th
eigen-coordinate by `-λᵢ` (geometer convention `Δ_∇ = -∇*∇`), losing exactly two
Sobolev derivatives.  Its operator norm is at most `1`. -/
def tensorScaleLaplacian (τ : ℝ) :
    tensorHs (I := I) (M := M) g r s (τ + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g r s τ :=
  LinearMap.mkContinuous
    { toFun := scaleLaplacianFun (I := I) (M := M)
      map_add' := scaleLaplacianFun_add (I := I) (M := M)
      map_smul' := fun c v => scaleLaplacianFun_smul (I := I) (M := M) c v }
    1
    (fun v => by
      change ‖scaleLaplacianFun (I := I) (M := M) v‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact norm_scaleLaplacianFun_le (I := I) (M := M) v)

@[simp] theorem tensorScaleLaplacian_apply (τ : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (τ + 2)) :
    tensorScaleLaplacian (I := I) (M := M) τ v =
      scaleLaplacianFun (I := I) (M := M) v := rfl

/-- The coordinate formula for the rough Laplacian: `Δ_∇` multiplies the `i`-th
coordinate by `-λᵢ`. -/
@[simp] theorem tensorScaleLaplacian_coeff (τ : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (τ + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorScaleLaplacian (I := I) (M := M) τ v).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) * v.coeff i := rfl

variable {τ : ℝ} {T : ℝ}

/-- **The rough Laplacian on time-`L²` tensor fields**, as a continuous linear
map `L²([0,T]; H^{τ+2}) →L[ℝ] L²([0,T]; Hᵗ)`: the rough Laplacian `Δ_∇` applied
pointwise in time. -/
def timeScaleLaplacian (τ : ℝ) {T : ℝ} :
    timeL2 (tensorHs (I := I) (M := M) g r s (τ + 2)) T →L[ℝ]
      timeL2 (tensorHs (I := I) (M := M) g r s τ) T :=
  (tensorScaleLaplacian (I := I) (M := M) τ).compLpL 2 (timeMeasure T)

/-- `timeScaleLaplacian τ v` is represented a.e. by the pointwise rough
Laplacian `t ↦ Δ_∇ (v t)`. -/
theorem timeScaleLaplacian_coeFn
    (v : timeL2 (tensorHs (I := I) (M := M) g r s (τ + 2)) T) :
    timeScaleLaplacian (I := I) (M := M) τ v =ᵐ[timeMeasure T]
      fun t => tensorScaleLaplacian (I := I) (M := M) τ (v t) :=
  (tensorScaleLaplacian (I := I) (M := M) τ).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) v

/-- The time-mode coordinate of the rough Laplacian of a field: the rough
Laplacian multiplies the `i`-th time-mode coordinate by `-λᵢ`. -/
theorem timeModeCoeff_timeScaleLaplacian
    (v : timeL2 (tensorHs (I := I) (M := M) g r s (τ + 2)) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (timeScaleLaplacian (I := I) (M := M) τ v) i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
        timeModeCoeff (I := I) (M := M) v i := by
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M)
    (timeScaleLaplacian (I := I) (M := M) τ v) i
  have hΔ := timeScaleLaplacian_coeFn (I := I) (M := M)
    (τ := τ) v
  have hsmul := Lp.coeFn_smul (-(TensorEigenIdx.lambda (I := I) (M := M) i))
    (timeModeCoeff (I := I) (M := M) v i)
  have hvcoe := timeModeCoeff_coeFn (I := I) (M := M) v i
  filter_upwards [hlhs, hΔ, hsmul, hvcoe] with t ht hΔt hsmt hvt
  rw [ht, hΔt, tensorScaleLaplacian_coeff, hsmt, Pi.smul_apply, hvt, smul_eq_mul]

/-- Chart-locality-free version of `maximalRegularityOp_solves_perMode`,
parameterized on resolvent compactness `h_compact`. -/
theorem maximalRegularityOp_solves_perMode {a : ℝ} (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (maximalRegularityDerivField (I := I) (M := M) a hT f) i =
      (-(TensorEigenIdx.lambda (I := I) (M := M) i)) •
          timeModeCoeff (I := I) (M := M)
            (maximalRegularitySolField (I := I) (M := M) a hT f) i +
        timeModeCoeff (I := I) (M := M) f i := by
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i]
  rw [derivModeCoeff, perModeConvDerivL2_apply, solModeCoeff, neg_smul,
    ← sub_eq_neg_add]

/-- Chart-locality-free version of `maximalRegularityOp_solves`, parameterized
on resolvent compactness `h_compact`: `∂_t u = Δ_∇ u + f` as an identity in
`L²([0,T]; Hᵃ)`. -/
theorem maximalRegularityOp_solves {a : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT hT1 f) =
      timeScaleLaplacian (I := I) (M := M) a
          (maximalRegularitySolField (I := I) (M := M) a hT.le f) +
        f := by
  rw [maximalRegularityOp_timeDeriv (I := I) (M := M)
    (a := a) hT hT1 f]
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeModeCoeff_add (I := I) (M := M),
    timeModeCoeff_timeScaleLaplacian (I := I) (M := M) (τ := a)
      (maximalRegularitySolField (I := I) (M := M) a hT.le f) i]
  exact maximalRegularityOp_solves_perMode (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le f i

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
