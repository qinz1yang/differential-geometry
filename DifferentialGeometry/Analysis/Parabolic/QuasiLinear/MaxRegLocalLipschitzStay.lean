import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegLocalLipschitz

/-!
# Time-`L²` modulus of continuity at `t = 0` of the subcritical Duhamel field

The locally-Lipschitz small-time cutoff
`de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent`
(`MaxRegLocalLipschitz`) carries one genuine analytic hypothesis — that the
constructed `H^{a+1}`-view solution field stays, for a.e. time, in the closed
ball `closedBall (ι u₀) R` on which the nonlinearity `N` is Lipschitz.  This
file proves the quantitative smallness statement that underlies that
hypothesis: in the time-`L²` norm of `L²([0,T]; H^{a+1})` the field

  `maxRegDuhamelSolFieldHa1 … u₀ gforce`

converges to the constant-in-time field `t ↦ ι u₀` as the horizon `T → 0+`.

## The two contributions

The `H^{a+1}`-view Duhamel field splits as

  `field = (homogeneous heat flow) + (Duhamel integral of the forcing)`,

with the two summands measured against `ι u₀` separately.

* **Homogeneous part.**  Its `i`-th eigen-coordinate is the scalar decay
  `t ↦ e^{−λᵢ t} · cᵢ`, with `cᵢ = u₀.coeff i`.  The defect against the
  constant `cᵢ` is `t ↦ (e^{−λᵢ t} − 1) · cᵢ`.  The kernel bound
  `0 ≤ 1 − e^{−λᵢ t} ≤ 1` on `[0,T]` gives the per-mode `L²(0,T)` estimate
  `‖(e^{−λᵢ ·} − 1) cᵢ‖² ≤ T · cᵢ²`, hence — assembled over the eigen-modes at
  the `H^{a+1}` scale —

    `‖(homogeneous part) − const (ι u₀)‖_{L²([0,T];H^{a+1})} ≤ √T · ‖ι u₀‖`.

* **Duhamel part.**  Bounded by the committed one-derivative-gain `√T`-decay
  estimate `maximalRegularitySolFieldHa1_norm_le`:

    `‖(Duhamel part)‖_{L²([0,T];H^{a+1})} ≤ 2√T · ‖gforce‖`.

Both vanish as `T → 0+`, so

  `‖field − const (ι u₀)‖_{L²([0,T];H^{a+1})} ≤ √T · (‖ι u₀‖ + 2‖gforce‖) → 0`.

## Main results

* `maxRegHomogeneousSolFieldHa1_sub_const_norm_le` — the homogeneous-part
  time-`L²` defect bound `√T · ‖ι u₀‖`.
* `maxRegDuhamelSolFieldHa1_sub_const_norm_le_ofCompact` — the full field
  time-`L²` defect bound `√T · ‖ι u₀‖ + 2√T · ‖gforce‖`.
* `maxRegDuhamelSolFieldHa1_tendsto_const_ofCompact` — the continuity-at-`0`
  statement: as `T → 0+` along nonnegative horizons, the field defect in the
  `L²([0,T]; H^{a+1})` norm tends to `0`.

## Relation to the stays-in-ball hypothesis

The hypothesis `hstay` of the cutoff is the *pointwise-a.e.-in-time* membership
`field t ∈ closedBall (ι u₀) R`.  The results here establish the corresponding
*time-`L²`* smallness `∫₀ᵀ ‖field t − ι u₀‖² dt → 0`.  Upgrading the time-`L²`
modulus to the pointwise-a.e. one requires a *continuous-in-time `H^{a+1}`*
representative of the field — the field is currently a pure
`L²([0,T]; H^{a+1})` element synthesised by `timeL2OfModes`, and the continuous
representative carried by the solution space (`TimeSobolev.timeH1.toFun`,
`continuousOn_toFun`) lives one Sobolev order lower, at the scale `a`.  The
quantitative input recorded here is exactly the smallness half of that
argument; the missing half is the lift of the continuous representative to the
scale `a + 1`.
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

/-- The `i`-th time-mode coordinate of the constant field `const T (ι u₀)` is
the constant scalar field `const T cᵢ`, `cᵢ = u₀.coeff i`: the inclusion
`H^{a+2} ↪ H^{a+1}` preserves the eigen-coordinates, and the time-mode
coordinate of a constant tensor field is the constant scalar field of that
coordinate. -/
theorem timeModeCoeff_const_inclusion
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) i =
      TimeSobolev.const T (u₀.coeff i) := by
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M)
    (TimeSobolev.const T
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀)) i
  have hconst := TimeSobolev.coeFn_const (X := tensorHs (I := I) (M := M) g r s (a + 1))
    (T := T)
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show (a + 1) ≤ a + 2 by linarith) u₀)
  have hrhs := TimeSobolev.coeFn_const (X := ℝ) (T := T) (u₀.coeff i)
  filter_upwards [hlhs, hconst, hrhs] with t htlhs htconst htrhs
  rw [htlhs, htconst, htrhs, tensorHsInclusion_coeff_apply]

/-- The `i`-th time-mode coordinate of the homogeneous-defect field
`maxRegHomogeneousSolFieldHa1 − const (ι u₀)` is represented a.e. by the scalar
function `t ↦ (e^{−λᵢ t} − 1) · cᵢ`. -/
theorem timeModeCoeff_homog_sub_const_coeFn
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ⇑(timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)) i) =ᵐ[timeMeasure T]
      fun t => (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
        u₀.coeff i := by
  have hhom : timeModeCoeff (I := I) (M := M)
      (maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀) i =
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i :=
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M) (a := a) hT u₀ i
  have hneg : timeModeCoeff (I := I) (M := M)
      (-TimeSobolev.const T
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show (a + 1) ≤ a + 2 by linarith) u₀)) i =
        -TimeSobolev.const T (u₀.coeff i) := by
    rw [show (-TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) =
        (-1 : ℝ) • TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀) by rw [neg_one_smul],
      timeModeCoeff_smul (I := I) (M := M),
      timeModeCoeff_const_inclusion (I := I) (M := M) u₀ i, neg_one_smul]
  rw [show (maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ -
        TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) =
      maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ +
        (-TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)) from by rw [sub_eq_add_neg],
    timeModeCoeff_add (I := I) (M := M), hhom, hneg]
  have hmode : ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hconst := TimeSobolev.coeFn_const (X := ℝ) (T := T) (u₀.coeff i)
  have hadd := Lp.coeFn_add (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
    (-TimeSobolev.const T (u₀.coeff i))
  have hnegc := Lp.coeFn_neg (TimeSobolev.const T (u₀.coeff i))
  filter_upwards [hadd, hmode, hconst, hnegc] with t htadd htmode htconst htnegc
  rw [htadd, Pi.add_apply, htmode, htnegc, Pi.neg_apply, htconst]
  ring

/-- The per-mode `L²(0,T)` defect of the homogeneous flow against the constant
`cᵢ` is bounded by `√T · |cᵢ|`: on `[0,T]` the kernel defect satisfies
`|e^{−λᵢ t} − 1| ≤ 1`, so `∫₀ᵀ ((e^{−λᵢ t} − 1) cᵢ)² ≤ T · cᵢ²`. -/
theorem norm_timeModeCoeff_homog_sub_const_sq_le
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)) i‖ ^ 2 ≤
      T * (u₀.coeff i) ^ 2 := by
  set fdiff : ℝ → ℝ :=
    fun t => (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
      u₀.coeff i with hfdiff_def
  have hcont : Continuous fdiff := by rw [hfdiff_def]; fun_prop
  have hae := timeModeCoeff_homog_sub_const_coeFn (I := I) (M := M) u₀ hT i
  have heq : timeModeCoeff (I := I) (M := M)
        (maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)) i =
      TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
        (hcont.continuousOn) := by
    refine Lp.ext ?_
    exact hae.trans (TimeSobolev.coeFn_ofContinuousOn _).symm
  rw [heq]
  have hbound : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
        (hcont.continuousOn)‖ ≤ Real.sqrt T * |u₀.coeff i| := by
    refine TimeSobolev.norm_ofContinuousOn_le_of_bound _ (fun t ht => ?_)
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have hexp_le : Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have hexp_pos : 0 < Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
      Real.exp_pos _
    rw [hfdiff_def, Real.norm_eq_abs, abs_mul]
    have habs_le : |Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [hexp_le, hexp_pos]
    calc |Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1| * |u₀.coeff i|
        ≤ 1 * |u₀.coeff i| :=
          mul_le_mul_of_nonneg_right habs_le (abs_nonneg _)
      _ = |u₀.coeff i| := one_mul _
  have hrhs_nonneg : 0 ≤ Real.sqrt T * |u₀.coeff i| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hsq : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
        (hcont.continuousOn)‖ ^ 2 ≤ (Real.sqrt T * |u₀.coeff i|) ^ 2 := by
    nlinarith [hbound, norm_nonneg (TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
      (f := fdiff) (hcont.continuousOn)), hrhs_nonneg]
  calc ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T) (f := fdiff)
          (hcont.continuousOn)‖ ^ 2
      ≤ (Real.sqrt T * |u₀.coeff i|) ^ 2 := hsq
    _ = T * (u₀.coeff i) ^ 2 := by rw [mul_pow, Real.sq_sqrt hT, sq_abs]

/-- **The homogeneous-part time-`L²` defect bound.**  In the `L²([0,T]; H^{a+1})`
norm the homogeneous heat flow `e^{tΔ_∇} u₀` differs from the constant-in-time
field `t ↦ ι u₀` by at most `√T · ‖ι u₀‖`:

  `‖maxRegHomogeneousSolFieldHa1 … u₀ − const (ι u₀)‖ ≤ √T · ‖ι u₀‖`.

The factor `√T` **vanishes as `T → 0`**: at `t = 0` the homogeneous flow is the
identity, and the per-mode kernel defect `e^{−λᵢ t} − 1` is uniformly bounded by
`1`. -/
theorem maxRegHomogeneousSolFieldHa1_sub_const_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T) :
    ‖maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ -
        TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)‖ ≤
      Real.sqrt T *
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show (a + 1) ≤ a + 2 by linarith) u₀‖ := by
  set ιu₀ := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (a + 1) ≤ a + 2 by linarith) u₀ with hιu₀
  rw [show Real.sqrt T * ‖ιu₀‖ = 1 * ‖TimeSobolev.const T ιu₀‖ by
    rw [TimeSobolev.norm_const, one_mul]]
  refine norm_le_of_weighted_perMode_le (I := I) (M := M)
    (a := a + 1) (b := a + 1)
    (h_compact := h_compact) (C := 1) (by norm_num) _ _ (fun i => ?_)
  have hdefect := norm_timeModeCoeff_homog_sub_const_sq_le (I := I) (M := M) u₀ hT i
  have hconst : timeModeCoeff (I := I) (M := M) (TimeSobolev.const T ιu₀) i =
      TimeSobolev.const T (u₀.coeff i) :=
    timeModeCoeff_const_inclusion (I := I) (M := M) u₀ i
  have hconst_norm : ‖timeModeCoeff (I := I) (M := M) (TimeSobolev.const T ιu₀) i‖ ^ 2 =
      T * (u₀.coeff i) ^ 2 := by
    rw [hconst, TimeSobolev.norm_const, mul_pow, Real.sq_sqrt hT, Real.norm_eq_abs,
      sq_abs]
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (a + 1) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)
  rw [one_pow, one_mul, hconst_norm]
  exact mul_le_mul_of_nonneg_left hdefect hw_nonneg

/-- **The full `H^{a+1}`-view Duhamel field time-`L²` defect bound.**  For the
forcing `gforce ∈ L²([0,T]; Hᵃ)`, in the `L²([0,T]; H^{a+1})` norm the Duhamel
field differs from the constant-in-time field `t ↦ ι u₀` by at most

  `√T · ‖ι u₀‖ + 2√T · ‖gforce‖`,

the sum of the homogeneous-part defect `√T · ‖ι u₀‖`
(`maxRegHomogeneousSolFieldHa1_sub_const_norm_le`) and the Duhamel-part bound
`2√T · ‖gforce‖` (the one-derivative-gain `√T`-decay
`maximalRegularitySolFieldHa1_norm_le`).  Both contributions vanish as
`T → 0`. -/
theorem maxRegDuhamelSolFieldHa1_sub_const_norm_le_ofCompact (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
        TimeSobolev.const T
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀)‖ ≤
      Real.sqrt T *
          ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀‖ +
        2 * Real.sqrt T * ‖gforce‖ := by
  set ιu₀ := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (a + 1) ≤ a + 2 by linarith) u₀ with hιu₀
  have hsplit : maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
        TimeSobolev.const T ιu₀ =
      (maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T u₀ -
          TimeSobolev.const T ιu₀) +
        maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1 gforce := by
    rw [maxRegDuhamelSolFieldHa1]; abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hhom := maxRegHomogeneousSolFieldHa1_sub_const_norm_le (I := I) (M := M)
    (h_compact := h_compact) u₀ hT.le
  have hduh := maximalRegularitySolFieldHa1_norm_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce
  exact add_le_add hhom hduh

/-- **Time-`L²` continuity of the subcritical Duhamel field at `T = 0`.**  As the
horizon `T → 0+` (through nonnegative values), the `H^{a+1}`-view Duhamel field
converges, in the `L²([0,T]; H^{a+1})` norm, to the constant-in-time field
`t ↦ ι u₀`.  Concretely: for every `ε > 0` there is `T₀ > 0` such that for every
horizon `0 < T ≤ T₀` (with `T ≤ 1`) and every forcing `gforce` with
`‖gforce‖ ≤ B`,

  `‖maxRegDuhamelSolFieldHa1 … u₀ gforce − const (ι u₀)‖ ≤ ε`.

This is the quantitative smallness underlying the stays-in-ball requirement of
the locally-Lipschitz small-time cutoff: the field starts (in the time-`L²`
sense) at `ι u₀` and stays `√T`-close to it on a short interval, uniformly over
forcings of bounded norm. -/
theorem maxRegDuhamelSolFieldHa1_tendsto_const_ofCompact
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (_hTT₀ : T ≤ T₀)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
        (_hgB : ‖gforce‖ ≤ B),
      ‖maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
          TimeSobolev.const T
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (a + 1) ≤ a + 2 by linarith) u₀)‖ ≤ ε := by
  set ιu₀ := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (a + 1) ≤ a + 2 by linarith) u₀ with hιu₀
  set Mcoef := ‖ιu₀‖ + 2 * max B 0 with hMcoef
  have hMcoef_nonneg : 0 ≤ Mcoef := by
    have : 0 ≤ 2 * max B 0 := by positivity
    positivity
  refine ⟨min 1 ((ε / (Mcoef + 1)) ^ 2), ?_, ?_⟩
  · have hden : 0 < Mcoef + 1 := by positivity
    have : 0 < (ε / (Mcoef + 1)) ^ 2 := by positivity
    exact lt_min one_pos this
  intro T hT hT1 hTT₀ gforce hgB
  have hden : 0 < Mcoef + 1 := by positivity
  have hT_le : T ≤ (ε / (Mcoef + 1)) ^ 2 := le_trans hTT₀ (min_le_right _ _)
  have hsqrtT_le : Real.sqrt T ≤ ε / (Mcoef + 1) := by
    rw [show ε / (Mcoef + 1) = Real.sqrt ((ε / (Mcoef + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hT_le
  have hsqrtT_nonneg : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  refine le_trans (maxRegDuhamelSolFieldHa1_sub_const_norm_le_ofCompact (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ gforce) ?_
  have hgforce_le : ‖gforce‖ ≤ max B 0 := le_trans hgB (le_max_left _ _)
  have hcombine : Real.sqrt T * ‖ιu₀‖ + 2 * Real.sqrt T * ‖gforce‖ ≤
      Real.sqrt T * Mcoef := by
    rw [hMcoef, mul_add]
    refine add_le_add (le_refl _) ?_
    rw [show Real.sqrt T * (2 * max B 0) = 2 * Real.sqrt T * max B 0 by ring]
    exact mul_le_mul_of_nonneg_left hgforce_le (by positivity)
  refine le_trans hcombine ?_
  calc Real.sqrt T * Mcoef
      ≤ (ε / (Mcoef + 1)) * Mcoef :=
        mul_le_mul_of_nonneg_right hsqrtT_le hMcoef_nonneg
    _ = ε * (Mcoef / (Mcoef + 1)) := by rw [div_mul_eq_mul_div, mul_div_assoc]
    _ ≤ ε * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hε.le
        rw [div_le_one hden]; linarith
    _ = ε := mul_one _

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
