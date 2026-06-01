import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Strong existence for the abstract quasi-linear tensor heat equation

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a Sobolev exponent
`a ≥ 0` and a time horizon `0 < T ≤ 1`, this file proves the **abstract
quasi-linear strong-existence theorem**: for a nonlinearity
`N : H^{a+2} → Hᵃ` which is Lipschitz with a small enough constant, the
quasi-linear tensor heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`,

has a strong solution on `[0,T]`.  The solution is produced by a Banach
fixed-point argument built on the maximal-regularity machinery.

## The forcing-space fixed point

A strong solution of `∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`, is the affine Duhamel
image `u = maxRegDuhamelMap … u₀ g` of a forcing term `g` that reproduces
`N(u)`: the equation `g = N ∘ (field of u)` is the fixed-point equation.  The
fixed point is taken **on the forcing space** `L²([0,T]; Hᵃ)`, not on the
solution space.  The solution space carries the `H¹`-graph norm, which does not
control the `H^{a+2}` spatial field of a strong solution; a contraction phrased
on the solution space would therefore fail.  The forcing-space route avoids
this: the contraction is measured purely in `L²([0,T]; Hᵃ)`, and the
two-derivative gain of maximal regularity is used only as a *bound* (via
`maximalRegularityOp_norm_Ha2_le`) inside the contraction estimate.

Concretely, the fixed-point map on `L²([0,T]; Hᵃ)` is

  `Φ(g) := N ∘ (maxRegDuhamelSolField … u₀ g)`,

i.e.: take the forcing `g`, form the Duhamel solution's `H^{a+2}`-valued field
`maxRegDuhamelSolField … u₀ g`, then apply `N` pointwise in time.  A fixed point
`g⋆ = Φ(g⋆)` yields the strong solution `u⋆ = maxRegDuhamelMap … u₀ g⋆`, which
satisfies `g⋆ = N ∘ (field of u⋆)`, hence `∂_t u⋆ = Δ_∇ u⋆ + N(field of u⋆)`.

## The Nemytskii operator

Pointwise composition with `N` lifts to a map of time-`L²` spaces

  `nemytskii hN : L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)`,  `f ↦ N ∘ f`,

Lipschitz with the **same** constant `L`.  Membership in `L²` holds because `N`
is Lipschitz: `‖N x‖ ≤ ‖N 0‖ + L‖x‖`, so `N ∘ f` is square-integrable whenever
`f` is and the time measure is finite (`N` need not fix `0`).  The Lipschitz
bound is the pointwise estimate `‖N x − N y‖ ≤ L‖x − y‖` integrated in time.

## Main definitions

* `nemytskii hN` — the Nemytskii (pointwise-composition) operator
  `L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)`, `f ↦ N ∘ f`.
* `quasilinearDuhamelMap a hT hT1 u₀ hN` — the forcing-space
  fixed-point map `Φ` of the quasi-linear equation.

## Main results

* `nemytskii_coeFn` — `nemytskii hN f` is represented a.e. by `t ↦ N (f t)`.
* `nemytskii_lipschitzWith` — `nemytskii hN` is Lipschitz with constant `L`.
* `maximalRegularitySolField_sub` — additivity of the maximal-regularity
  solution field, the algebraic input to the contraction estimate.
* `quasilinearDuhamelMap_contracting` — `Φ` is a contraction with constant
  `(L : ℝ)·(1 + T)` whenever `2·L < 1` (then `(L : ℝ)·(1 + T) < 1`).
* `quasilinear_strong_existence` — **the headline theorem**: for `0 < T ≤ 1`,
  `N` Lipschitz with `2·L < 1`, there is a strong solution `u` of
  `∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`, in the maximal-regularity solution
  space.
* `quasilinear_strong_unique` — the strong solution produced by the fixed-point
  construction is unique.
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

section Nemytskii

variable {L : ℝ≥0}
  {N : tensorHs (I := I) (M := M) g r s (a + 2) →
    tensorHs (I := I) (M := M) g r s a}

/-- The pointwise composition `t ↦ N (f t)` of a Lipschitz nonlinearity `N` with
a time-`L²` field `f ∈ L²([0,T]; H^{a+2})` is itself square-integrable for the
(finite) time measure: it is the sum of the `0`-fixing Lipschitz part
`t ↦ N (f t) − N 0` (square-integrable by `LipschitzWith.comp_memLp`) and the
constant `N 0` (square-integrable on a finite measure space). -/
theorem memLp_comp_nemytskii (hN : LipschitzWith L N)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T) :
    MemLp (fun t => N (f t)) 2 (timeMeasure T) := by
  have hshift : LipschitzWith L (fun x => N x - N 0) := by
    have hsubL := hN.sub (LipschitzWith.const (N 0))
    rwa [add_zero] at hsubL
  have hshift0 : (fun x => N x - N 0) (0 : tensorHs (I := I) (M := M) g r s
      (a + 2)) = 0 := by simp
  have hcomp : MemLp ((fun x => N x - N 0) ∘ fun t => f t) 2 (timeMeasure T) :=
    hshift.comp_memLp hshift0 (Lp.memLp f)
  have hconst : MemLp (fun _ : ℝ => N 0) 2 (timeMeasure T) :=
    memLp_const (N 0)
  have hsum : MemLp (fun t => (N (f t) - N 0) + N 0) 2 (timeMeasure T) :=
    hcomp.add hconst
  have hfun : (fun t => N (f t)) =
      fun t => (N (f t) - N 0) + N 0 := by
    funext t; abel
  rw [hfun]
  exact hsum

/-- **The Nemytskii operator.**  For a Lipschitz nonlinearity `N : H^{a+2} →
Hᵃ`, this is the pointwise-composition map

  `nemytskii hN : L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)`,  `f ↦ N ∘ f`,

sending a time-`L²` field `f` to the time-`L²` field represented by `t ↦ N (f
t)`.  The output lands in `L²` because `N` is Lipschitz (`memLp_comp_nemytskii`)
and the underlying function agrees a.e. with `t ↦ N (f t)`
(`nemytskii_coeFn`). -/
def nemytskii (hN : LipschitzWith L N) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun f => (memLp_comp_nemytskii (I := I) (M := M) hN f).toLp (fun t => N (f t))

/-- `nemytskii hN f` is represented almost everywhere by the pointwise
composition `t ↦ N (f t)`. -/
theorem nemytskii_coeFn (hN : LipschitzWith L N)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T) :
    nemytskii (I := I) (M := M) hN f =ᵐ[timeMeasure T] fun t => N (f t) :=
  (memLp_comp_nemytskii (I := I) (M := M) hN f).coeFn_toLp

/-- **The pointwise-in-time contraction estimate of the Nemytskii operator.**
For two time-`L²` fields `f, f'` the squared `L²` distance of their Nemytskii
images is bounded by `L²` times the squared `L²` distance of the fields:

  `‖nemytskii hN f − nemytskii hN f'‖² ≤ L²·‖f − f'‖²`.

This is the pointwise Lipschitz estimate `‖N (f t) − N (f' t)‖ ≤ L·‖f t − f' t‖`
squared and integrated in time. -/
theorem nemytskii_dist_sq_le (hN : LipschitzWith L N)
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T) :
    ‖nemytskii (I := I) (M := M) hN f - nemytskii (I := I) (M := M) hN f'‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ‖f - f'‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  have hdiff : ⇑(nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f') =ᵐ[timeMeasure T]
      fun t => N (f t) - N (f' t) := by
    have hsub := Lp.coeFn_sub (nemytskii (I := I) (M := M) hN f)
      (nemytskii (I := I) (M := M) hN f')
    have hf := nemytskii_coeFn (I := I) (M := M) hN f
    have hf' := nemytskii_coeFn (I := I) (M := M) hN f'
    filter_upwards [hsub, hf, hf'] with t ht htf htf'
    rw [ht, Pi.sub_apply, htf, htf']
  have hfdiff : ⇑(f - f') =ᵐ[timeMeasure T] fun t => f t - f' t :=
    Lp.coeFn_sub f f'
  have hint_fdiff : Integrable (fun t => ‖(f - f') t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (f - f'))).mp (Lp.memLp (f - f'))
  refine integral_mono_ae ?_ ?_ ?_
  · exact (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'))).mp
      (Lp.memLp (nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'))
  · exact hint_fdiff.const_mul ((L : ℝ) ^ 2)
  · filter_upwards [hdiff, hfdiff] with t ht htf
    rw [ht]
    have hlip : ‖N (f t) - N (f' t)‖ ≤ (L : ℝ) * ‖f t - f' t‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hN.dist_le_mul (f t) (f' t)
    have hnn : 0 ≤ ‖N (f t) - N (f' t)‖ := norm_nonneg _
    have hsq : ‖N (f t) - N (f' t)‖ ^ 2 ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := by
      have hrhs_nn : 0 ≤ (L : ℝ) * ‖f t - f' t‖ :=
        mul_nonneg L.coe_nonneg (norm_nonneg _)
      nlinarith [hlip, hnn, hrhs_nn]
    calc ‖N (f t) - N (f' t)‖ ^ 2
        ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := hsq
      _ = (L : ℝ) ^ 2 * ‖(f - f') t‖ ^ 2 := by rw [htf, mul_pow]

/-- **The Nemytskii operator is Lipschitz with the same constant.**  For a
Lipschitz nonlinearity `N : H^{a+2} → Hᵃ` with constant `L`, the Nemytskii
operator `nemytskii hN : L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)` is Lipschitz with
the same constant `L`: pointwise composition does not enlarge the Lipschitz
constant.  This is the squared estimate `nemytskii_dist_sq_le` after taking
square roots. -/
theorem nemytskii_lipschitzWith (hN : LipschitzWith L N) :
    LipschitzWith L (nemytskii (I := I) (M := M) (T := T) hN) := by
  refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsq := nemytskii_dist_sq_le (I := I) (M := M) hN f f'
  have hrhs_nn : 0 ≤ (L : ℝ) * ‖f - f'‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
  have hsq' : ‖nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'‖ ^ 2 ≤ ((L : ℝ) * ‖f - f'‖) ^ 2 := by
    rw [mul_pow]; exact hsq
  have h := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrhs_nn] at h

end Nemytskii

/-- Chart-locality-free version of `maximalRegularitySolField_add`,
parameterized on resolvent compactness `h_compact`. -/
theorem maximalRegularitySolField_add (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolField (I := I) (M := M) a hT (f + f') =
      maximalRegularitySolField (I := I) (M := M) a hT f +
        maximalRegularitySolField (I := I) (M := M) a hT f' := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact
    (fun i => ?_)
  rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT (f + f') i,
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT f' i]
  rw [solModeCoeff, solModeCoeff, solModeCoeff,
    timeModeCoeff_add (I := I) (M := M), map_add]

/-- Chart-locality-free version of `maximalRegularitySolField_sub`,
parameterized on resolvent compactness `h_compact`. -/
theorem maximalRegularitySolField_sub (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolField (I := I) (M := M) a hT (f - f') =
      maximalRegularitySolField (I := I) (M := M) a hT f -
        maximalRegularitySolField (I := I) (M := M) a hT f' := by
  have hadd := maximalRegularitySolField_add (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

/-- Chart-locality-free version of `maxRegDuhamelSolField_sub`, parameterized on
resolvent compactness `h_compact`. -/
theorem maxRegDuhamelSolField_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce' =
      maximalRegularitySolField (I := I) (M := M) a hT.le
        (gforce - gforce') := by
  rw [maximalRegularitySolField_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT.le gforce gforce']
  rw [maxRegDuhamelSolField, maxRegDuhamelSolField]
  abel

/-- Chart-locality-free version of `maxRegDuhamelSolField_dist_le`,
parameterized on resolvent compactness `h_compact`:
`‖maxRegDuhamelSolField … u₀ g − maxRegDuhamelSolField … u₀ g'‖ ≤
(1 + T)·‖g − g'‖`. -/
theorem maxRegDuhamelSolField_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce'‖ ≤
      (1 + T) * ‖gforce - gforce'‖ := by
  rw [maxRegDuhamelSolField_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce']
  exact maximalRegularityOp_norm_Ha2_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (gforce - gforce')

section FixedPoint

/-- **The forcing-space fixed-point map of the quasi-linear equation.**  For an
initial datum `u₀ ∈ H^{a+2}` and a Lipschitz nonlinearity `N`,

  `quasilinearDuhamelMap … u₀ hN (g) := N ∘ (maxRegDuhamelSolField … u₀ g)`,

a self-map of the forcing space `L²([0,T]; Hᵃ)`.  It first forms the
`H^{a+2}`-valued Duhamel solution field of the forcing `g`, then applies the
Nemytskii operator (pointwise composition with `N`).  A fixed point `g⋆ = Φ(g⋆)`
is a forcing term reproducing `N(u)` along its own Duhamel solution; the
quasi-linear strong solution is the Duhamel image of `g⋆`. -/
def quasilinearDuhamelMap (a : ℝ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun gforce => nemytskii (I := I) (M := M) hN
    (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce)

@[simp] theorem quasilinearDuhamelMap_apply (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN gforce =
      nemytskii (I := I) (M := M) hN
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) :=
  rfl

/-- Chart-locality-free version of `quasilinearDuhamelMap_dist_le`,
parameterized on resolvent compactness `h_compact`:
`‖Φ(g) − Φ(g')‖ ≤ (L : ℝ)·(1 + T)·‖g − g'‖`. -/
theorem quasilinearDuhamelMap_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    dist (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN gforce)
        (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN
          gforce') ≤
      (L : ℝ) * (1 + T) * dist gforce gforce' := by
  have hnem := (nemytskii_lipschitzWith (I := I) (M := M) hN).dist_le_mul
    (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce)
    (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce')
  have hfield : dist
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce)
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce') ≤
        (1 + T) * dist gforce gforce' := by
    rw [dist_eq_norm, dist_eq_norm]
    exact maxRegDuhamelSolField_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce'
  calc dist
        (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN gforce)
        (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN
          gforce')
      ≤ (L : ℝ) * dist
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce)
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀
            gforce') := hnem
    _ ≤ (L : ℝ) * ((1 + T) * dist gforce gforce') :=
        mul_le_mul_of_nonneg_left hfield L.coe_nonneg
    _ = (L : ℝ) * (1 + T) * dist gforce gforce' := by ring

/-- The contraction constant `(L : ℝ)·(1 + T)` is `< 1` whenever `2·L < 1` and
`T ≤ 1`: from `T ≤ 1` one has `1 + T ≤ 2`, so `(L : ℝ)·(1 + T) ≤ 2·L < 1`. -/
theorem quasilinear_contraction_const_lt_one {L : ℝ≥0} {T : ℝ} (hT1 : T ≤ 1)
    (hL : 2 * (L : ℝ) < 1) :
    (L : ℝ) * (1 + T) < 1 := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  calc (L : ℝ) * (1 + T) ≤ (L : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left h1T hLnn
    _ = 2 * (L : ℝ) := by ring
    _ < 1 := hL

/-- Chart-locality-free version of `quasilinearDuhamelMap_contracting`,
parameterized on resolvent compactness `h_compact`: the quasi-linear Duhamel map
`Φ` is a `ContractingWith` self-map of `L²([0,T]; Hᵃ)` with contraction constant
`(L : ℝ)·(1 + T)` whenever `2·L < 1` and `T ≤ 1`. -/
theorem quasilinearDuhamelMap_contracting (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1) :
    ContractingWith
      ⟨(L : ℝ) * (1 + T),
        mul_nonneg L.coe_nonneg (by linarith [hT.le])⟩
      (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN) := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using quasilinear_contraction_const_lt_one
      (L := L) (T := T) hT1 hL
  · refine LipschitzWith.of_dist_le_mul (fun gforce gforce' => ?_)
    have h := quasilinearDuhamelMap_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u₀ hN gforce gforce'
    simpa only [NNReal.coe_mk] using h

end FixedPoint

/-- **Chart-locality-free strong existence for the quasi-linear tensor heat
equation.**

Identical to `quasilinear_strong_existence` but parameterized on the resolvent
compactness hypothesis `h_compact : IsCompactOperator (tensorResolventL2 g r s)`
in place of any chart-locality assumption.  For a closed Riemannian manifold
`(M, g)`, ranks `(r, s)`, a Sobolev exponent `a ≥ 0`, an initial datum
`u₀ ∈ H^{a+2}`, a time horizon `0 < T ≤ 1`, and a nonlinearity
`N : H^{a+2} → Hᵃ` Lipschitz with constant `L` satisfying `2·L < 1`, there is a
**strong solution** `u` in the maximal-regularity solution space `H¹([0,T]; Hᵃ)`
of the quasi-linear tensor heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`.

The solution is the affine Duhamel image of the unique fixed point of the
forcing-space contraction `quasilinearDuhamelMap`, obtained from the
chart-locality-free contraction `quasilinearDuhamelMap_contracting`.
The data `u, gforce` satisfy the same four conclusions as
`quasilinear_strong_existence`: `u` is the Duhamel image of `gforce`; `gforce`
reproduces `N` along the solution field; the initial value is `u₀`; and the time
derivative is `∂_t u = Δ_∇ u + N(u)`. -/
theorem quasilinear_strong_existence {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
      (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
      u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
        gforce = nemytskii (I := I) (M := M) hN
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀
              gforce) ∧
        TimeSobolev.timeH1.trace0 _ T u =
            tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a ≤ a + 2 by linarith) u₀ ∧
        TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) a
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀
                gforce) +
            nemytskii (I := I) (M := M) hN
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀
                gforce) := by
  have hcontr := quasilinearDuhamelMap_contracting (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ hN hL
  set gStar := ContractingWith.fixedPoint
    (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN) hcontr
    with hgStar_def
  have hgStar_fix :
      quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN gStar =
        gStar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hgStar_eq : gStar = nemytskii (I := I) (M := M) hN
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gStar) := by
    rw [← quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT hT1 u₀ hN
      gStar, hgStar_fix]
  refine ⟨maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gStar,
    gStar, rfl, hgStar_eq, ?_, ?_⟩
  · exact maxRegDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT hT1 u₀ gStar
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT hT1 u₀ gStar]
    exact congrArg₂ (· + ·) rfl hgStar_eq

/-- Chart-locality-free version of `quasilinear_strong_unique`, parameterized on
resolvent compactness `h_compact`: the strong solution produced by the
forcing-space fixed-point construction is unique. -/
theorem quasilinear_strong_unique {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1)
    {gforce₁ gforce₂ : timeL2 (tensorHs (I := I) (M := M) g r s a) T}
    (hg₁ : gforce₁ = nemytskii (I := I) (M := M) hN
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce₁))
    (hg₂ : gforce₂ = nemytskii (I := I) (M := M) hN
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce₂)) :
    gforce₁ = gforce₂ ∧
      maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce₁ =
        maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce₂ := by
  have hcontr := quasilinearDuhamelMap_contracting (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ hN hL
  have hfix₁ :
      Function.IsFixedPt
        (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN)
        gforce₁ := by
    change quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN
        gforce₁ = gforce₁
    rw [quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT hT1 u₀ hN
      gforce₁]
    exact hg₁.symm
  have hfix₂ :
      Function.IsFixedPt
        (quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN)
        gforce₂ := by
    change quasilinearDuhamelMap (I := I) (M := M) a hT hT1 u₀ hN
        gforce₂ = gforce₂
    rw [quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT hT1 u₀ hN
      gforce₂]
    exact hg₂.symm
  have hgeq : gforce₁ = gforce₂ := by
    rw [ContractingWith.fixedPoint_unique hcontr hfix₁,
      ContractingWith.fixedPoint_unique hcontr hfix₂]
  exact ⟨hgeq, by rw [hgeq]⟩

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
