import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing

/-!
# Uniform-in-time spectral-mass bound for the maximal-regularity solution

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the inhomogeneous
heat equation `∂_t u = Δ_∇ u + f`, `u(0) = 0`, has the `L²`-maximal-regularity
solution field whose `i`-th eigen-coordinate is the per-mode Duhamel convolution
`t ↦ perModeConv λᵢ (timeModeCoeff f i) t = ∫₀ᵗ e^{−λᵢ(t−s)} (timeModeCoeff f i)(s) ds`.

The companion file `ParabolicInteriorSmoothing.lean` establishes the
`L²`-in-time interior smoothing: under the first-order coupling of the
nonlinearity (`hcouple`) and a base regularity (`hbase`), the solution-field
masses `solFieldMass hT f σ i = (1 + λᵢ)^σ · ‖solModeCoeff hT f i‖²` are summable
at *every* spatial order `σ` (`solFieldMass_summable_all`).  That controls the
*time-integrated* mass `∫₀ᵀ ∑ᵢ (1+λᵢ)^σ |φᵢ(t)|² dt`.

This file strengthens the statement to a **pointwise-in-time** (`L∞`-in-time)
spectral-mass bound, uniform over `t ∈ [0,T]`: for every `σ` there is a single
constant `C`, independent of `t`, with

  `∑ᵢ (1 + λᵢ)^σ · (perModeConv λᵢ (timeModeCoeff f i) t)² ≤ C`   for all `t ∈ [0,T]`,

together with the summability of the summed family at every fixed `t`.

## The analytic content

The bridge is the per-mode, pointwise-in-time Duhamel estimate
`abs_perModeConv_timeL2_le`:

  `|perModeConv λᵢ (timeModeCoeff f i) t| ≤ √T · ‖timeModeCoeff f i‖`   for `t ∈ [0,T]`,

obtained by dominating the heat kernel `e^{−λᵢ(t−s)} ≤ 1` on the triangle and
applying `L¹ ⊆ L²` (Cauchy–Schwarz on `[0,T]`).  The bound is uniform in `t` and
the constant `√T` is independent of the mode `λᵢ`.  Squaring and multiplying by
the Sobolev weight gives, mode by mode and for every `t ∈ [0,T]`,

  `(1 + λᵢ)^σ · (perModeConv λᵢ (timeModeCoeff f i) t)² ≤ T · forcingMass f σ i`,

a `t`-independent dominating family.  Its sum is finite because the *forcing*
masses `forcingMass f σ` are summable at every order — which follows from the
all-order interior-smoothing bootstrap (`solFieldMass_summable_all` gives the
solution masses summable at order `σ + 1`, and `hcouple` then transports this to
the forcing masses at order `σ`).  Summing the pointwise domination against the
summable, `t`-independent majorant `T · forcingMass f σ` yields the uniform
bound with `C = T · ∑ᵢ forcingMass f σ i`.

Since the initial datum is zero, no separate semigroup-of-the-data term enters;
the whole solution is the Duhamel term, and the sup over `t ∈ [0,T]` is finite,
uniformly in `t`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ} {T : ℝ}

/-- The summability of the *forcing* masses at every spatial order, extracted
from the interior-smoothing hypotheses.  The all-order bootstrap
`solFieldMass_summable_all` makes the solution masses summable at order `σ + 1`;
the first-order coupling `hcouple` then transports this to the forcing masses at
order `σ`. -/
private theorem forcingMass_summable_of_couple (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT f b)) (σ : ℝ) :
    Summable (forcingMass (I := I) (M := M) f σ) :=
  hcouple σ
    (solFieldMass_summable_all (I := I) (M := M) hT f hcouple hbase (σ + 1))

/-- The per-mode, **pointwise-in-time** Duhamel square bound.  For `0 ≤ T` and
`t ∈ [0,T]`, at every eigen-index `i`,

  `(1 + λᵢ)^σ · (perModeConv λᵢ (timeModeCoeff f i) t)² ≤ T · forcingMass f σ i`,

with a constant `T` independent of both the mode `λᵢ` and the time `t`.  This is
the pointwise heat-kernel estimate `abs_perModeConv_timeL2_le` squared and
weighted. -/
private theorem weighted_perModeConv_sq_le (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) (σ : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
      T * forcingMass (I := I) (M := M) f σ i := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  have habs := abs_perModeConv_timeL2_le lam hlam_nn
    (timeModeCoeff (I := I) (M := M) f i) ht
  have hconv_sq :
      (perModeConv lam
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
        T * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
    have hsq : (perModeConv lam
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
        (Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := by
      have habs_nn : 0 ≤ |perModeConv lam
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t| := abs_nonneg _
      have hrhs_nn : 0 ≤ Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      have hbase :
          (perModeConv lam
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 =
            |perModeConv lam
              (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t| ^ 2 := by
        rw [sq_abs]
      rw [hbase]
      exact pow_le_pow_left₀ habs_nn habs 2
    calc (perModeConv lam
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2
        ≤ (Real.sqrt T * ‖timeModeCoeff (I := I) (M := M) f i‖) ^ 2 := hsq
      _ = T * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hT]
  calc tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv lam
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i σ *
          (T * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hconv_sq hwt_nn
    _ = T * (tensorSobolevWeight (I := I) (M := M) i σ *
          ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by ring
    _ = T * forcingMass (I := I) (M := M) f σ i := by rw [forcingMass]

/-- **The uniform-in-time spectral-mass bound (L∞([0,T]; Hˢ)).**  Let `f` be a
forcing field coupled to its own Duhamel solution by the first-order loss of a
subcritical nonlinearity (`hcouple`: solution masses at order `d + 1` summable
⟹ forcing masses at order `d` summable, for every `d`), with base regularity
`b` (`hbase`: solution masses summable at order `b`), and zero initial datum.

Then for *every* spatial Sobolev order `σ` there is a single constant `C`,
independent of `t`, such that for all `t ∈ [0,T]` the order-`σ` spectral mass of
the maximal-regularity solution at time `t` — the weighted sum over the spectrum
of the squared per-mode Duhamel convolutions
`perModeConv λᵢ (timeModeCoeff f i) t` — is summable and bounded by `C`.

This is the pointwise-in-time (`L∞`-in-time) strengthening of the
`L²`-in-time interior smoothing `solField_into_all_tensorHs_interior`: the sup
over `t ∈ [0,T]` of the order-`σ` spectral mass is finite, uniformly in `t`.
The constant is `C = T · ∑ᵢ forcingMass f σ i`, finite by the all-order
bootstrap and the first-order coupling. -/
theorem spectralMass_sup_le_of_timeL2_allHs (hT : 0 < T)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) {b : ℝ}
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le f (d + 1)) →
        Summable (forcingMass (I := I) (M := M) f d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT.le f b)) :
    ∀ σ : ℝ, ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤ C := by
  intro σ
  have hforce : Summable (forcingMass (I := I) (M := M) f σ) :=
    forcingMass_summable_of_couple (I := I) (M := M) hT.le f hcouple hbase σ
  have hmaj : Summable (fun i => T * forcingMass (I := I) (M := M) f σ i) :=
    hforce.mul_left T
  refine ⟨T * ∑' i, forcingMass (I := I) (M := M) f σ i, fun t ht => ?_⟩
  have hle : ∀ i, tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 ≤
      T * forcingMass (I := I) (M := M) f σ i :=
    fun i => weighted_perModeConv_sq_le (I := I) (M := M) hT.le f σ i ht
  have hnn : ∀ i, 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2 :=
    fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  have hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2) :=
    Summable.of_nonneg_of_le hnn hle hmaj
  refine ⟨hsum, ?_⟩
  calc ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) f i) u) t) ^ 2
      ≤ ∑' i, T * forcingMass (I := I) (M := M) f σ i :=
        hsum.tsum_le_tsum hle hmaj
    _ = T * ∑' i, forcingMass (I := I) (M := M) f σ i := by
        rw [tsum_mul_left]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
