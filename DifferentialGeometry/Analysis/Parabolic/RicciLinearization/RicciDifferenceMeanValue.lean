import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The mean-value (FTC) core for the Ricci-tensor difference of two realized metrics

For a closed smooth Riemannian manifold `(M, g₀)` and two endpoint perturbation tensor
sections `T, T' : SmoothCcTensor g₀ 0 2`, both `g₀`-fibre small with constant `< 1`, this
file builds the **mean-value (fundamental theorem of calculus) reduction** of the Ricci-arm
difference
$$\operatorname{Ric}(g_1)_{x}(v, w) - \operatorname{Ric}(g_1')_{x}(v, w)
    = \int_0^1 \bigl(D\!\operatorname{Ric}\bigr)_{g_s}[T - T']_x(v, w)\, ds,$$
where `g₁ = realize(g₀, T)`, `g₁' = realize(g₀, T')`, and `g_s = realize(g₀, (1-s)·T' + s·T)`
is the straight-line metric path joining them through the convex combination of the two
perturbations.  The integrand is the **linearized Ricci operator** `linearizedRicciAt g_s`
applied to the perturbation velocity `T - T'`.

This replaces the single-endpoint Palatini telescope (which leaves un-capturable
two-endpoint cross terms) with the classical mean-value identity: the difference of a
nonlinear functional at two points is the integral of its derivative along any path joining
them.

## Contents

* `convexPerturbation g₀ T T' s` — the convex-combination perturbation
  `(1 - s)·T' + s·T : SmoothCcTensor g₀ 0 2`, with endpoint identities at `s = 0, 1`.
* `convexPerturbation_gFibreOpBound` — the convex-combination smallness bound: on `[0,1]`
  the perturbation `convexPerturbation g₀ T T' s` is `g₀`-fibre bounded by the convex
  combination `(1 - s)·δ' + s·δ < 1`, so the realized metric path is positive-definite.
* `realizedMetricPath g₀ T T' hδ_lt hδ hδ'_lt hδ' s` — the realized metric path
  `realize(g₀, convexPerturbation g₀ T T' s)` for `s ∈ [0,1]`, with endpoint identities
  `path 0 = realize T'`, `path 1 = realize T`.
* `linearizedRicciAt g₀ T T' x v w s₀` — the linearized Ricci operator at the path metric
  `g_{s₀}` in the perturbation direction `T - T'`, defined as the `s`-derivative of the
  Ricci tensor along the (re-anchored) realized path.
* `hasDerivAt_ricciTensor_realizedMetricPath` (posited child) — the path `s`-derivative of
  the realized Ricci tensor, identified with `linearizedRicciAt` at each `s₀ ∈ [0,1]`, with
  interval-integrability of the integrand.  This is the deep mean-value derivative content
  (the metric-derivative of the curvature functional equals the linearized Ricci operator).
* `ricciTensor_realized_sub_eq_integral_linearizedRicci` — the FTC headline: the realized
  Ricci-arm difference equals `∫₀¹ linearizedRicciAt g_s (T - T') ds`.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ### Additivity of the symmetric extraction (mirroring `ccTensorBilinSymm_smul`) -/

/-- The underlying multilinear field `ccTensorMultilinear` is additive in the tensor
section. -/
theorem ccTensorMultilinear_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (T + T') x : Tensor0SSpace 2 I x)
      = (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x)
        + (ccTensorMultilinear (I := I) g T' x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_add]
  rfl

/-- The model value `ccTensorModel` is additive in the tensor section. -/
theorem ccTensorModel_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (T + T') x =
      ccTensorModel (I := I) g T x + ccTensorModel (I := I) g T' x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_add, Tensor0SSpace.toModel_add]

/-- The symmetrized extraction is additive in the tensor section. -/
theorem ccTensorBilinSymm_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (T + T') x v w =
      ccTensorBilinSymm (I := I) g T x v w + ccTensorBilinSymm (I := I) g T' x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorModel_add,
    ContinuousMultilinearMap.add_apply]
  ring

/-! ### The convex-combination perturbation and its smallness bound -/

/-- The **convex-combination perturbation** `(1 - s)·T' + s·T` of two endpoint
perturbation tensor sections, as a `SmoothCcTensor g₀ 0 2`.  As `s` runs over `[0,1]` this
traces the straight line in perturbation space from `T'` (at `s = 0`) to `T` (at `s = 1`). -/
def convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) : SmoothCcTensor g₀ 0 2 :=
  (1 - s) • T' + s • T

@[simp] lemma convexPerturbation_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 0 = T' := by
  simp [convexPerturbation]

@[simp] lemma convexPerturbation_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 1 = T := by
  simp [convexPerturbation]

/-- The fibre form of the convex perturbation is the convex combination of the two endpoint
fibre forms. -/
lemma ccTensorBilinSymm_convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w =
      (1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [convexPerturbation, ccTensorBilinSymm_add, ccTensorBilinSymm_smul,
    ccTensorBilinSymm_smul]

/-- **Convex-combination smallness bound.**  If `T` is `g₀`-fibre bounded by `δ` and `T'`
by `δ'`, then the convex perturbation `(1 - s)·T' + s·T` is `g₀`-fibre bounded by the convex
combination `(1 - s)·δ' + s·δ` for every `s ∈ [0,1]`. -/
theorem convexPerturbation_gFibreOpBound (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) := by
  intro x v w
  have hsqv : (0 : ℝ) ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsqw : (0 : ℝ) ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hprod : (0 : ℝ) ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsqv hsqw
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hbT := hδ x v w
  have hbT' := hδ' x v w
  rw [ccTensorBilinSymm_convexPerturbation]
  calc
    |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w|
        ≤ |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s * ccTensorBilinSymm (I := I) g₀ T x v w| := abs_add_le _ _
    _ = (1 - s) * |ccTensorBilinSymm (I := I) g₀ T' x v w| +
            s * |ccTensorBilinSymm (I := I) g₀ T x v w| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * (δ' * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) +
            s * (δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
        gcongr
    _ = ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by ring

/-- For `s ∈ [0,1]` the convex smallness constant `(1 - s)·δ' + s·δ` is `< 1` whenever both
`δ, δ' < 1`. -/
theorem convex_smallConstant_lt_one {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * δ' + s * δ < 1 := by
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  nlinarith [mul_nonneg h1ms (le_of_lt (by linarith : (0 : ℝ) < 1 - δ')),
    mul_nonneg hs0 (le_of_lt (by linarith : (0 : ℝ) < 1 - δ))]

/-! ### The realized metric path -/

/-- **The realized metric path** `s ↦ realize(g₀, (1 - s)·T' + s·T)` for `s ∈ [0,1]`.
The convex-combination smallness bound (`convexPerturbation_gFibreOpBound`,
`convex_smallConstant_lt_one`) guarantees that the convex perturbation stays `g₀`-fibre
small with constant `< 1`, so each `realizedMetricPath … s` is a genuine positive-definite
`SmoothRiemannianMetric I M`.  At `s = 0` it is `realize(g₀, T')` and at `s = 1` it is
`realize(g₀, T)` (`realizedMetricPath_zero_inner`, `realizedMetricPath_one_inner`). -/
def realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    (convex_smallConstant_lt_one hδ_lt hδ'_lt hs0 hs1)
    (convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' hs0 hs1)

/-- The realized metric path is fibrewise `g₀ + ` the convex perturbation form. -/
theorem realizedMetricPath_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : M) (v w : TangentSpace I x) :
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedMetricPath, tensorSectionRealizeMetric_inner]

/-! ### Endpoint metric equalities -/

/-- **Metric extensionality through the fibre inner product.**  Two smooth Riemannian
metrics with the same fibrewise inner product are equal (the remaining structure fields are
propositions, hence proof-irrelevant). -/
theorem riemannianMetric_eq_of_inner (g g' : SmoothRiemannianMetric I M)
    (h : ∀ (b : M) (v w : TangentSpace I b), g.inner b v w = g'.inner b v w) :
    g = g' := by
  have hinner : g.inner = g'.inner := by
    funext b
    exact ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h b v w
  cases g; cases g'
  congr

/-- The clamped path metric at a parameter `s ∈ [0,1]` (clamped to `max 0 (min s 1)`) is the
genuine path metric at `s`. -/
private lemma clamp_eq_of_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (min s 1) = s := by
  obtain ⟨hs0, hs1⟩ := hs
  rw [min_eq_left hs1, max_eq_right hs0]

/-! ### The linearized Ricci operator along the path and the FTC -/

/-- **The scalar realized Ricci value along the path** as a function of `s ∈ ℝ`, used as the
`f` of the fundamental theorem of calculus.  For `s` outside `[0,1]` the path metric is not
defined, so the value is the path metric clamped to the nearest endpoint; on `[0,1]` it is
the genuine realized Ricci value `Ric(g_s)_x(v, w)`. -/
def realizedRicciPathValue (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ricciTensor (I := I)
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (le_max_left 0 (min s 1)) (by
        have : min s 1 ≤ 1 := min_le_right s 1
        exact max_le (zero_le_one) this)) x v w

/-- The path-value at `s = 1` equals the realized Ricci tensor of `realize(g₀, T)`. -/
theorem realizedRicciPathValue_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 1 =
      ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w := by
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (1 : ℝ) 1))
          (max_le (zero_le_one) (le_trans (min_le_right (1 : ℝ) 1) (le_refl 1))) =
        tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, tensorSectionRealizeMetric_inner,
      ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 1 1) = 1 := by norm_num
    rw [this]; ring
  rw [hmetric]

/-- The path-value at `s = 0` equals the realized Ricci tensor of `realize(g₀, T')`. -/
theorem realizedRicciPathValue_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 0 =
      ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w := by
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (0 : ℝ) 1))
          (max_le (zero_le_one) (le_trans (min_le_right (0 : ℝ) 1) (le_refl 1))) =
        tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, tensorSectionRealizeMetric_inner,
      ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 0 1) = 0 := by norm_num
    rw [this]; ring
  rw [hmetric]

/-- **The linearized Ricci operator at the path metric `g_{s₀}` in direction `T - T'`.**
By definition it is the `s`-derivative of the realized Ricci value along the path at `s₀`;
this is the genuine differential `D\!\operatorname{Ric}_{g_{s₀}}[T - T']_x(v, w)` of the
Ricci tensor functional in the metric-perturbation direction `T - T'`.  It is the integrand
of the mean-value reduction. -/
def linearizedRicciAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s₀ : ℝ) : ℝ :=
  deriv (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀

/-! ### abs-value smallness, valid on a neighborhood of `[0,1]` -/

theorem convexPerturbation_gFibreOpBound_abs (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      (|1 - s| * δ' + |s| * δ) := by
  intro x v w
  have hbT := hδ x v w
  have hbT' := hδ' x v w
  rw [ccTensorBilinSymm_convexPerturbation]
  calc
    |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w|
        ≤ |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s * ccTensorBilinSymm (I := I) g₀ T x v w| := abs_add_le _ _
    _ = |1 - s| * |ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s| * |ccTensorBilinSymm (I := I) g₀ T x v w| := by rw [abs_mul, abs_mul]
    _ ≤ |1 - s| * (δ' * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) +
            |s| * (δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
        have ha1 : (0:ℝ) ≤ |1 - s| := abs_nonneg _
        have ha2 : (0:ℝ) ≤ |s| := abs_nonneg _
        gcongr
    _ = (|1 - s| * δ' + |s| * δ) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by ring

theorem abs_convex_smallConstant_lt_one {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    |1 - s| * δ' + |s| * δ < 1 := by
  obtain ⟨h0, h1⟩ := hs
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg h0]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) < 1 - δ').le,
    mul_nonneg h0 (by linarith : (0:ℝ) < 1 - δ).le]

/-! ### The open realized metric family -/

/-- The realized metric of the convex perturbation at any `s` whose abs-convex smallness
constant is `< 1`. -/
def realizedMetricPathOpen (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    hs (convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s)

theorem realizedMetricPathOpen_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) (x : M) (v w : TangentSpace I x) :
    (realizedMetricPathOpen (I := I) g₀ T T' hδ hδ' s hs).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedMetricPathOpen, tensorSectionRealizeMetric_inner]

/-! ### Generic joint `(s,y)`-smoothness tower -/

lemma gen_joint_partialDeriv
    (Ψ : ℝ → E → ℝ) (q : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}
    (hΨ : ContDiffAt ℝ ∞ (fun r : ℝ × E => Ψ r.1 r.2) (s₀, y₀)) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) q (fun y => Ψ p.1 y) p.2) (s₀, y₀) := by
  have hf : ContDiffAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y))
      ((s₀, y₀), (fun p : ℝ × E => p.2) (s₀, y₀)) := by
    have huncurry : (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y)) =
        (fun r : ℝ × E => Ψ r.1 r.2) ∘ (fun z : (ℝ × E) × E => (z.1.1, z.2)) := by
      funext z; rfl
    rw [huncurry]
    refine hΨ.comp ((s₀, y₀), y₀) ?_
    exact (contDiffAt_fst.comp ((s₀, y₀), y₀) contDiffAt_fst).prodMk contDiffAt_snd
  have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (s₀, y₀) := contDiffAt_snd
  have hfd := ContDiffAt.fderiv hf hg (le_refl _)
  exact (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E q)).contDiff.contDiffAt.comp (s₀, y₀) hfd

variable (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)

/-- Hypothesis bundle: joint Gram C∞ at every base point with `s₀ ∈ S`, `y₀` chart-interior;
plus positive-definiteness of the path Gram over the chart base set for `s₀ ∈ S`. -/
def GenJointGram (S : Set ℝ) : Prop :=
  (∀ (i j : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}, s₀ ∈ S →
      y₀ ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2) (s₀, y₀)) ∧
  (∀ {s₀ : ℝ}, s₀ ∈ S →
      ∀ {x : M}, x ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      0 < (chartGramMatrix (I := I) (gfam s₀) α x).det)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- A jointly smooth realized metric family has jointly smooth chart Gram entries on its regular
time set. -/
theorem genGram_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (α : M) :
    GenJointGram (I := I) (fun t => G.metric t) α D.regular := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    set e := trivializationAt E (TangentSpace I) α with he
    have hframe :
        IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame (chartModelBasis E)) e.baseSet :=
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
    have hbridge : ∀ {x : M}, x ∈ e.baseSet → ∀ k : Fin (Module.finrank ℝ E),
        e.localFrame (chartModelBasis E) k x = chartBasisVecFiber (I := I) α k x := by
      intro x hx k
      rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
      rfl
    have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (G.metric p.1) α p.2 i j)
        (D.regular ×ˢ e.baseSet) := by
      have hcomp := hG.frameCompSmooth (e.localFrame (chartModelBasis E)) hframe i j
      refine hcomp.congr ?_
      intro p hp
      simp only [chartGramMatrix_apply, hbridge hp.2 i, hbridge hp.2 j]
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hsubset : (extChartAt I α).target ⊆ (extChartAt I α).symm ⁻¹' e.baseSet := by
      intro y hy'
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy'
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
      rw [he, trivializationAt_baseSet_eq_chartAt_source]
      exact hsource
    have hσ1 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => p.1) (D.regular ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞
        (fun p : ℝ × E => p.2) (D.regular ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
    have hmaps2 : Set.MapsTo (fun p : ℝ × E => p.2)
        (D.regular ×ˢ interior (extChartAt I α).target) (extChartAt I α).target :=
      fun p hp => interior_subset hp.2
    have hσ2 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
        (fun p : ℝ × E => (extChartAt I α).symm p.2)
        (D.regular ×ˢ interior (extChartAt I α).target) :=
      hsymm.comp hsnd hmaps2
    have hσ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
        (D.regular ×ˢ interior (extChartAt I α).target) :=
      hσ1.prodMk hσ2
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (G.metric p.1) α i j p.2)
        (D.regular ×ˢ interior (extChartAt I α).target) := by
      refine (hsmooth.comp hσ (fun p hp => ⟨hp.1, hsubset (interior_subset hp.2)⟩)).congr ?_
      intro p _
      rfl
    exact hcomp.contDiffOn.contDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hs) (isOpen_interior.mem_nhds hy))
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (G.metric s₀) α hx

lemma gen_joint_invGram {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) (s₀, y₀) := by
  classical
  have hGentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2) a b) (s₀, y₀) := by
    intro a b
    have := hG.1 a b hs hy
    simpa only [chartGramOnE_def] using this
  have hdet : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
        ((extChartAt I α).symm p.2)).det) (s₀, y₀) := by
    have hdet_eq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ kk, chartGramMatrix (I := I) (gfam p.1) α
              ((extChartAt I α).symm p.2) (σ kk) kk) := by
      funext p; rw [Matrix.det_apply]; simp [Units.smul_def]
    rw [hdet_eq]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    exact contDiffAt_prod (fun kk _ => hGentry (σ kk) kk)
  have hx_base : (extChartAt I α).symm y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hy_t : y₀ ∈ (extChartAt I α).target := interior_subset hy
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_t
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    exact hsource
  have hdet_ne : (chartGramMatrix (I := I) (gfam (s₀, y₀).1) α
      ((extChartAt I α).symm (s₀, y₀).2)).det ≠ 0 := ne_of_gt (hG.2 hs hx_base)
  have hadj : ∀ kk ll : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) (s₀, y₀) := by
    intro kk ll
    have hexp : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ m, (chartGramMatrix (I := I) (gfam p.1) α
                ((extChartAt I α).symm p.2)).updateRow ll
                (Pi.single kk (1 : ℝ)) (σ m) m) := by
      funext p; rw [Matrix.adjugate_apply, Matrix.det_apply]; simp [Units.smul_def]
    rw [hexp]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    refine contDiffAt_prod (fun m _ => ?_)
    by_cases hσm : σ m = ll
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun _ : ℝ × E => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) kk
            (1 : ℝ)) m) := by
        funext p; rw [hσm, Matrix.updateRow_self]
      rw [heq]; exact contDiffAt_const
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2) (σ m) m) := by
        funext p; rw [Matrix.updateRow_ne hσm]
      rw [heq]; exact hGentry (σ m) m
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) =
      (fun p : ℝ × E => ((chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det)⁻¹ *
        (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate k l) := by
    funext p
    rw [chartInvGramOnE_def]
    change (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2))⁻¹ k l = _
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2)).det •
            (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate) k l = _
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiffAt_inv _ hdet_ne).comp (s₀, y₀) hdet).mul (hadj k l)

/-- The chart inverse-Gram entries of a jointly smooth realized metric family are jointly smooth
on each chart source and the regular time set. -/
theorem invGram_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I) (G.metric p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ D.regular) := by
  have hGram := genGram_of_family (I := I) G hG α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_invGram (I := I) (fun t => G.metric t) α hGram i j ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I) (G.metric r.1) α i j r.2)
      (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ D.regular) p := by
    have hm := hmove p ⟨hx, ht⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]
      exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

lemma gen_joint_gramBracket {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i j l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) i (fun y => chartGramOnE (I := I) (gfam r.1) α l j y) r.2 +
          partialDeriv (E := E) j (fun y => chartGramOnE (I := I) (gfam r.1) α l i y) r.2 -
          partialDeriv (E := E) l (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2) := by
    funext r; rw [gramBracket]
  rw [heq]
  exact ((gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α l j y) i
      (hG.1 l j hs hy)).add
    (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α l i y) j
      (hG.1 l i hs hy))).sub
    (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α i j y) l
      (hG.1 i j hs hy))

lemma gen_joint_christoffel {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) =
      (fun r : ℝ × E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α k l r.2 *
          gramBracket (I := I) (gfam r.1) α i j l r.2) := by
    funext r; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  exact (gen_joint_invGram (I := I) gfam α hG k l hs hy).mul
    (gen_joint_gramBracket (I := I) gfam α hG i j l hs hy)

/-- The chart Christoffel entries of a jointly smooth realized metric family are jointly smooth
on each chart source and the regular time set. -/
theorem christ_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        chartChristoffel (I := I) (G.metric p.2) α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
  have hGram := genGram_of_family (I := I) G hG α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I) (fun t => G.metric t) α hGram i j k ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (G.metric r.1) α i j k r.2)
      (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ D.regular) p := by
    have hm := hmove p ⟨hx, ht⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  simpa only [Function.comp_apply] using hentryM.comp_contMDiffWithinAt p hmoveAt

lemma gen_joint_partial_christoffel {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (m i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m (fun y => chartChristoffel (I := I) (gfam r.1) α i j k y) r.2)
      (s₀, y₀) :=
  gen_joint_partialDeriv (fun s y => chartChristoffel (I := I) (gfam s) α i j k y) m
    (gen_joint_christoffel (I := I) gfam α hG i j k hs hy)

lemma gen_joint_riemann {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) j (fun y => chartChristoffel (I := I) (gfam r.1) α i k l y) r.2 -
          partialDeriv (E := E) k (fun y => chartChristoffel (I := I) (gfam r.1) α i j l y) r.2 +
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) (gfam r.1) α j m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i k m r.2 -
              chartChristoffel (I := I) (gfam r.1) α k m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i j m r.2))) := by
    funext r; rw [chartRiemannTensor_def]
  rw [heq]
  refine ((gen_joint_partial_christoffel (I := I) gfam α hG j i k l hs hy).sub
    (gen_joint_partial_christoffel (I := I) gfam α hG k i j l hs hy)).add ?_
  refine ContDiffAt.sum (fun m _ => ?_)
  exact ((gen_joint_christoffel (I := I) gfam α hG j m l hs hy).mul
      (gen_joint_christoffel (I := I) gfam α hG i k m hs hy)).sub
    ((gen_joint_christoffel (I := I) gfam α hG k m l hs hy).mul
      (gen_joint_christoffel (I := I) gfam α hG i j m hs hy))

private lemma gen_joint_ricci {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) =
      (fun r : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (gfam r.1) α i j k j r.2) := by
    funext r; rw [chartRicciTensor_def]
  rw [heq]
  exact ContDiffAt.sum (fun j _ => gen_joint_riemann (I := I) gfam α hG i j k j hs hy)

/-! ### Generic joint smoothness of the DeTurck chart polynomials

The DeTurck (gauge) chart scalars `chartDeTurckVFComp`, `chartLieDeTurckComp` and the combined
`chartDeTurckRicciRHS` are finite chart polynomials in the inverse Gram, the Christoffel symbols (of
both the family metric `gfam s` and a fixed background `g_bg`) and their first chart partials.  Each
is therefore jointly `(s, y)`-`C^∞` over the joint-Gram set, by combining the generic joint bricks
above with the fixed-background Christoffel smoothness `chartChristoffel_contDiffOn_interior`. -/

/-- The chart DeTurck-vector-field component `W^k(gfam s) = ∑_{a,b} G^{ab}·(Γ^k_{ab}(gfam s) −
Γ^k_{ab}(g_bg))` is jointly `(s, y)`-`C^∞`.  The fixed-background Christoffel `Γ(g_bg)` is
`s`-independent (joint smooth via `chartChristoffel_contDiffOn_interior` composed with the `y`
projection); the family parts come from `gen_joint_invGram` and `gen_joint_christoffel`. -/
lemma gen_joint_chartDeTurckVFComp {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) (s₀, y₀) := by
  have hbg : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) (s₀, y₀) := by
    intro a b
    have hbase : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g_bg α a b k) y₀ :=
      (chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k).contDiffAt
        (isOpen_interior.mem_nhds hy)
    have hcomp : (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) =
        (chartChristoffel (I := I) g_bg α a b k) ∘ (fun r : ℝ × E => r.2) := rfl
    rw [hcomp]
    exact ContDiffAt.comp (s₀, y₀) hbase contDiffAt_snd
  have heq : (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) =
      (fun r : ℝ × E => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α a b r.2 *
          (chartChristoffel (I := I) (gfam r.1) α a b k r.2 -
            chartChristoffel (I := I) g_bg α a b k r.2)) := by
    funext r; rw [chartDeTurckVFComp_def]
  rw [heq]
  refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ?_))
  exact (gen_joint_invGram (I := I) gfam α hG a b hs hy).mul
    ((gen_joint_christoffel (I := I) gfam α hG a b k hs hy).sub (hbg a b))

/-- The chart partial `∂_m W^k(gfam s)` of the DeTurck-vector-field component is jointly
`(s, y)`-`C^∞`, by `gen_joint_partialDeriv` applied to `gen_joint_chartDeTurckVFComp`. -/
lemma gen_joint_partial_chartDeTurckVFComp {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (m k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)
      (s₀, y₀) :=
  gen_joint_partialDeriv (fun s y => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y) m
    (gen_joint_chartDeTurckVFComp (I := I) gfam α hG g_bg k hs hy)

/-- The chart DeTurck-Lie summand `(𝓛_{W(gfam s)} gfam s)_{ij}` is jointly `(s, y)`-`C^∞`, by
expanding `chartLieDeTurckComp` into the three Leibniz groups and combining the joint
DeTurck-VF component / chart Gram / their partials. -/
lemma gen_joint_chartLieDeTurckComp {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i j r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i j r.2) =
      (fun r : ℝ × E =>
        (∑ k : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2 *
              partialDeriv (E := E) k (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam r.1) α k j r.2 *
              partialDeriv (E := E) i
                (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam r.1) α i k r.2 *
              partialDeriv (E := E) j
                (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)) := by
    funext r; rw [chartLieDeTurckComp_def]
  rw [heq]
  refine ((ContDiffAt.sum (fun k _ => ?_)).add (ContDiffAt.sum (fun k _ => ?_))).add
    (ContDiffAt.sum (fun k _ => ?_))
  · exact (gen_joint_chartDeTurckVFComp (I := I) gfam α hG g_bg k hs hy).mul
      (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α i j y) k
        (hG.1 i j hs hy))
  · exact (hG.1 k j hs hy).mul
      (gen_joint_partial_chartDeTurckVFComp (I := I) gfam α hG g_bg i k hs hy)
  · exact (hG.1 i k hs hy).mul
      (gen_joint_partial_chartDeTurckVFComp (I := I) gfam α hG g_bg j k hs hy)

/-- The combined chart DeTurck–Ricci right-hand side `−2·Rc(gfam s) + (𝓛_{W} gfam s)` is jointly
`(s, y)`-`C^∞`, by `chartDeTurckRicciRHS_def` over `gen_joint_ricci` and
`gen_joint_chartLieDeTurckComp`. -/
lemma gen_joint_chartDeTurckRicciRHS {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (i k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam r.1) g_bg α i k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam r.1) g_bg α i k r.2) =
      (fun r : ℝ × E => -2 * chartRicciTensor (I := I) (gfam r.1) α i k r.2 +
        chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i k r.2) := by
    funext r; rw [chartDeTurckRicciRHS_def]
  rw [heq]
  exact (contDiffAt_const.mul (gen_joint_ricci (I := I) gfam α hG i k hs hy)).add
    (gen_joint_chartLieDeTurckComp (I := I) gfam α hG g_bg i k hs hy)

/-! ### The keystone: GenJointGram for the realized open family -/

/-- The open `s`-set where the abs-convex smallness holds. -/
def realizedSmallSet {δ δ' : ℝ} : Set ℝ := {s : ℝ | |1 - s| * δ' + |s| * δ < 1}

theorem realizedSmallSet_isOpen {δ δ' : ℝ} :
    IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcont : Continuous (fun s : ℝ => |1 - s| * δ' + |s| * δ) := by fun_prop
  exact isOpen_lt hcont continuous_const

theorem Icc_subset_realizedSmallSet {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1) :
    Set.Icc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
  fun _ hs => abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs

/-- The total realized family (junk-extended off the small set by `g₀`). -/
def realizedFam (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothRiemannianMetric I M :=
  if h : |1 - s| * δ' + |s| * δ < 1 then
    realizedMetricPathOpen (I := I) g₀ T T' hδ hδ' s h
  else g₀

theorem realizedFam_inner_of_mem (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) (x : M) (v w : TangentSpace I x) :
    (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedFam, dif_pos (Set.mem_setOf.mp hs), realizedMetricPathOpen_inner]

/-- On the small set the realized-family chart Gram is the convex combination of the two
endpoint realized-metric chart Grams. -/
theorem realizedFam_chartGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) α i j y =
      (1 - s) *
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j y +
        s * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j y := by
  rw [chartGramOnE_def, chartGramOnE_def, chartGramOnE_def, chartGramMatrix_apply,
    chartGramMatrix_apply, chartGramMatrix_apply,
    realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner,
    ccTensorBilinSymm_convexPerturbation]
  ring

theorem realizedFam_genJointGram (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) :
    GenJointGram (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') α
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
    set F : E → ℝ :=
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j with hF
    set G : E → ℝ :=
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j with hG
    have heq : (fun p : ℝ × E =>
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.1) α i j p.2)
        =ᶠ[nhds (s₀, y₀)] (fun p : ℝ × E => (1 - p.1) * F p.2 + p.1 * G p.2) := by
      have hmem : (realizedSmallSet (δ := δ) (δ' := δ')) ×ˢ (Set.univ : Set E) ∈ nhds (s₀, y₀) :=
        (hSopen.prod isOpen_univ).mem_nhds ⟨hs, Set.mem_univ _⟩
      filter_upwards [hmem] with p hp
      exact realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hp.1 α i j p.2
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    have hFc : ContDiffAt ℝ ∞ (fun p : ℝ × E => F p.2) (s₀, y₀) :=
      (((chartGramOnE_contDiffOn (I := I) _ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) contDiffAt_snd
    have hGc : ContDiffAt ℝ ∞ (fun p : ℝ × E => G p.2) (s₀, y₀) :=
      (((chartGramOnE_contDiffOn (I := I) _ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) contDiffAt_snd
    exact ((contDiffAt_const.sub contDiffAt_fst).mul hFc).add (contDiffAt_fst.mul hGc)
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) α hx

/-! ### A `δ < 1`-free joint chart Gram for the realized family -/

/-- **Spatial smoothness of the symmetric perturbation chart-Gram entry.**  For the smooth
symmetric bilinear `Hom`-section `ccTensorBilinSymm g₀ T`, the scalar
`x ↦ ccTensorBilinSymm g₀ T x (e_i x) (e_j x)` (Gram-style entry against the chart-`α` frame) is
`C^∞` on the chart-`α` trivialization base set.  A direct mirror of
`chartGramMatrix_entry_contMDiffOn` with the metric Hom-section `g.inner` replaced by the smooth
perturbation Hom-section (`ccTensorBilinSymm_contMDiff`); it carries NO `δ < 1` smallness
hypothesis (the bilinear form is smooth regardless of fibre size). -/
private lemma chartBilinSymmEntry_contMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => ccTensorBilinSymm (I := I) g₀ T x
        (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hB := ccTensorBilinSymm_contMDiff (I := I) g₀ T
  have hv := chartBasisVec_contMDiffOn (I := I) α i
  have hw := chartBasisVec_contMDiffOn (I := I) α j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ccTensorBilinSymm (I := I) g₀ T m
              (chartBasisVecFiber (I := I) α i m)
              (chartBasisVecFiber (I := I) α j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hB.contMDiffOn hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

/-- **Spatial smoothness of the symmetric perturbation chart-Gram entry, pulled back to the chart
target.**  The chart-`α` pullback of `chartBilinSymmEntry` is `C^∞` on `(extChartAt I α).target`.
Mirror of `chartGramOnE_contDiffOn`, no `δ < 1`. -/
private lemma chartBilinSymmOnE_contDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E => ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)))
      (extChartAt I α).target := by
  have hbase := chartBilinSymmEntry_contMDiffOn (I := I) g₀ T α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  exact (hbase.comp hsymm hsubset).contDiffOn

/-- **A `δ < 1`-free joint chart Gram for the realized family.**  The realized family chart-Gram
joint `(s, y)`-smoothness over `realizedSmallSet`, NOT requiring the individual smallness bounds
`δ < 1`, `δ' < 1`.  On the small set the chart Gram entry is
`chartGramOnE g₀ + (1 - s)·B_{T'} + s·B_T`, with `B_T` the (spatially smooth, `s`-independent)
perturbation chart-Gram entry — an affine-in-`s` combination of spatially smooth fields, hence
jointly smooth.  The positive-definiteness arm is `chartGramMatrix_det_pos` (also `δ`-free). -/
theorem realizedFam_genJointGram_free (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) :
    GenJointGram (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') α
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
    have heq : (fun p : ℝ × E =>
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.1) α i j p.2)
        =ᶠ[nhds (s₀, y₀)] (fun p : ℝ × E =>
          chartGramOnE (I := I) g₀ α i j p.2 +
            ((1 - p.1) * (fun y : E => ccTensorBilinSymm (I := I) g₀ T' ((extChartAt I α).symm y)
                (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
                (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))) p.2 +
              p.1 * (fun y : E => ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm y)
                (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
                (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))) p.2)) := by
      have hmem : (realizedSmallSet (δ := δ) (δ' := δ')) ×ˢ (Set.univ : Set E) ∈ nhds (s₀, y₀) :=
        (hSopen.prod isOpen_univ).mem_nhds ⟨hs, Set.mem_univ _⟩
      filter_upwards [hmem] with p hp
      have hps : p.1 ∈ realizedSmallSet (δ := δ) (δ' := δ') := hp.1
      rw [chartGramOnE_def, chartGramMatrix_apply,
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hps,
        ccTensorBilinSymm_convexPerturbation, chartGramOnE_def, chartGramMatrix_apply]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    have hsnd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) (s₀, y₀) := contDiffAt_snd
    have hG₀c : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) g₀ α i j p.2) (s₀, y₀) := by
      have h0 := (((chartGramOnE_contDiffOn (I := I) g₀ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
      exact h0
    have hBc : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
        ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm p.2)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm p.2))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm p.2))) (s₀, y₀) := by
      have h0 := (((chartBilinSymmOnE_contDiffOn (I := I) g₀ T α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
      exact h0
    have hB'c : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
        ccTensorBilinSymm (I := I) g₀ T' ((extChartAt I α).symm p.2)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm p.2))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm p.2))) (s₀, y₀) := by
      have h0 := (((chartBilinSymmOnE_contDiffOn (I := I) g₀ T' α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
      exact h0
    exact hG₀c.add (((contDiffAt_const.sub contDiffAt_fst).mul hB'c).add (contDiffAt_fst.mul hBc))
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) α hx

/-! ### Generic joint operator-field lift over the product base `M × ℝ` -/

/-- **Source-model-generic pointwise-to-operator smoothness bridge.**  The joint analog of
`contMDiffAt_clm_of_pointwise` with the *source* model `IX` decoupled from the target operator
model: per-vector `ContMDiffAt` lifts to operator `ContMDiffAt` over a finite-dimensional source
fibre, via the basis-evaluation embedding `F₁ →L F₂ ↪ Fin (rank F₁) → F₂` and a continuous-linear
left inverse. -/
lemma contMDiffAt_clm_of_pointwise_jointSource
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {n : WithTop ℕ∞}
    {A : X → (F₁ →L[ℝ] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IX 𝓘(ℝ, F₂) n (fun q => A q v) x) :
    ContMDiffAt IX 𝓘(ℝ, F₁ →L[ℝ] F₂) n A x := by
  haveI : FiniteDimensional ℝ (F₁ →L[ℝ] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis ℝ F₁
  let evalBasis : (F₁ →L[ℝ] F₂) →L[ℝ] (Fin (Module.finrank ℝ F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  haveI : FiniteDimensional ℝ (Fin (Module.finrank ℝ F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let gCLM : (Fin (Module.finrank ℝ F₁) → F₂) →L[ℝ] (F₁ →L[ℝ] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ y, gCLM (evalBasis y) = y := fun y => congr($(hgLM) y)
  have hEA : ContMDiffAt IX 𝓘(ℝ, Fin _ → F₂) n (evalBasis ∘ A) x :=
    contMDiffAt_pi_space.mpr fun i => h (bF₁ i)
  have hcompose : A = gCLM ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [hcompose]
  exact gCLM.contDiff.contMDiff.contMDiffAt.comp _ hEA

/-- **The joint pointwise-to-operator section bridge over the product base `M × ℝ`.**  For an
`s`-family of fibre operators `φ : ∀ p : M × ℝ, V₁ p.1 →L V₂ p.1`, if for every globally smooth
`M`-section `Y` of `V₁` the `M × ℝ`-section `(x, s) ↦ φ (x, s) (Y x)` is jointly `(x, s)`-`C^∞`
over `M × ℝ`, then the operator field `(x, s) ↦ φ (x, s)` is itself jointly `C^∞` as a section of
the Hom-bundle `Hom(V₁, V₂)`.  This is the product-base (`M × ℝ`) analog of
`contMDiff_clm_section_of_pointwise`: the hom-bundle smoothness is reduced through
`contMDiffAt_hom_bundle` to (i) the base projection (`contMDiffAt_fst`) and (ii) the `inCoordinates`
smoothness, the latter handled by `contMDiffAt_clm_of_pointwise_jointSource` evaluated against a
local frame of `V₁` near the spatial base point. -/
theorem contMDiff_clm_section_of_pointwise_jointMR
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
    [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
    [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
    [ContMDiffVectorBundle ∞ F₁ V₁ I]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [ContMDiffVectorBundle ∞ F₂ V₂ I]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    (φ : ∀ p : M × ℝ, V₁ p.1 →L[ℝ] V₂ p.1)
    (h : ∀ (Y : Cₛ^∞⟮I; F₁, V₁⟯),
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
        (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y p.1)))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (F₁ →L[ℝ] F₂)
        (E := fun x : M => V₁ x →L[ℝ] V₂ x) p.1 (φ p)) := by
  intro p₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  apply contMDiffAt_clm_of_pointwise_jointSource (IX := I.prod 𝓘(ℝ, ℝ)) (X := M × ℝ)
  intro v
  let e₁ := trivializationAt F₁ V₁ x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ F₁
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ V₁ x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hφY : ∀ i, ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y i p.1))) := fun i => h (Y i)
  have hφY_fiber : ∀ i, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => (e₂ ⟨p.1, φ p (Y i p.1)⟩).2) p₀ := fun i => by
    have hi := (Bundle.contMDiffAt_totalSpace (F := F₂) (E := V₂)).mp ((hφY i) p₀)
    exact hi.2
  have hsum : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => ∑ i, b.repr v i • (e₂ ⟨p.1, φ p (Y i p.1)⟩).2) p₀ := by
    apply ContMDiffAt.sum
    intro i _
    exact (contMDiffAt_const (c := (b.repr v i : ℝ))).smul (hφY_fiber i)
  refine hsum.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ p : M × ℝ in 𝓝 p₀, p.1 ∈ e₁.baseSet :=
    continuousAt_fst (e₁.open_baseSet.mem_nhds he₁)
  have h_base₂ : ∀ᶠ p : M × ℝ in 𝓝 p₀, p.1 ∈ e₂.baseSet :=
    continuousAt_fst (e₂.open_baseSet.mem_nhds he₂)
  have h_frame : ∀ᶠ p : M × ℝ in 𝓝 p₀, ∀ i, (Y i) p.1 = e₁.localFrame b i p.1 := by
    have hYnhd : ∀ᶠ x in 𝓝 x₀, ∀ i, (Y i) x = e₁.localFrame b i x := hY
    exact continuousAt_fst hYnhd
  filter_upwards [h_base₁, h_base₂, h_frame] with p hx₁ hx₂ hYp
  have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have h_inCoord : (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ p.1 x₀ p.1 (φ p)) v =
      e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 v)) := rfl
  rw [h_inCoord]
  have h₁ : e₁.symmL ℝ p.1 v = ∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i) := by
    conv_lhs => rw [hv_decomp]
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₂ : (φ p) (∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i)) =
      ∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i)) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₃ : e₂.continuousLinearMapAt ℝ p.1 (∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i))) =
      ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 (b i))) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  rw [h₁, h₂, h₃]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  have h_lf : e₁.symmL ℝ p.1 (b i) = (Y i) p.1 := by
    rw [hYp i]
    rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  rw [h_lf]
  rw [Trivialization.continuousLinearMapAt_apply]
  exact congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e₂) hx₂) _

/-- **Within-set source-model-generic pointwise-to-operator smoothness bridge.**  The
`ContMDiffWithinAt` analog of `contMDiffAt_clm_of_pointwise_jointSource`: per-vector
`ContMDiffWithinAt` lifts to operator `ContMDiffWithinAt` over a finite-dimensional source
fibre, via the basis-evaluation embedding `F₁ →L F₂ ↪ Fin (rank F₁) → F₂` and a continuous-linear
left inverse. -/
lemma contMDiffWithinAt_clm_of_pointwise_jointSource
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {n : WithTop ℕ∞}
    {A : X → (F₁ →L[ℝ] F₂)} {sX : Set X} {x : X}
    (h : ∀ v, ContMDiffWithinAt IX 𝓘(ℝ, F₂) n (fun q => A q v) sX x) :
    ContMDiffWithinAt IX 𝓘(ℝ, F₁ →L[ℝ] F₂) n A sX x := by
  haveI : FiniteDimensional ℝ (F₁ →L[ℝ] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis ℝ F₁
  let evalBasis : (F₁ →L[ℝ] F₂) →L[ℝ] (Fin (Module.finrank ℝ F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  haveI : FiniteDimensional ℝ (Fin (Module.finrank ℝ F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let gCLM : (Fin (Module.finrank ℝ F₁) → F₂) →L[ℝ] (F₁ →L[ℝ] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ y, gCLM (evalBasis y) = y := fun y => congr($(hgLM) y)
  have hEA : ContMDiffWithinAt IX 𝓘(ℝ, Fin _ → F₂) n (evalBasis ∘ A) sX x :=
    contMDiffWithinAt_pi_space.mpr fun i => h (bF₁ i)
  have hcompose : A = gCLM ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [hcompose]
  exact gCLM.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt _ hEA

/-- **The within-slab joint pointwise-to-operator section bridge over the product base `M × ℝ`.**
The `ContMDiffOn (univ ×ˢ S)` analog of `contMDiff_clm_section_of_pointwise_jointMR`: for an
`s`-family of fibre operators `φ : ∀ p : M × ℝ, V₁ p.1 →L V₂ p.1`, if for every globally smooth
`M`-section `Y` of `V₁` the `M × ℝ`-section `(x, s) ↦ φ (x, s) (Y x)` is jointly `(x, s)`-`C^∞`
on the slab `univ ×ˢ S`, then the operator field `(x, s) ↦ φ (x, s)` is itself jointly `C^∞` on
`univ ×ˢ S` as a section of the Hom-bundle `Hom(V₁, V₂)`.  This is the key missing slab analog of
the global bridge: the hom-bundle within-smoothness is reduced through `contMDiffWithinAt_hom_bundle`
to (i) the base projection and (ii) the `inCoordinates` within-smoothness, the latter handled by
`contMDiffWithinAt_clm_of_pointwise_jointSource` evaluated against a local frame of `V₁` near the
spatial base point. -/
theorem contMDiffOn_clm_section_of_pointwise_jointMR
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
    [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
    [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
    [ContMDiffVectorBundle ∞ F₁ V₁ I]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [ContMDiffVectorBundle ∞ F₂ V₂ I]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    (φ : ∀ p : M × ℝ, V₁ p.1 →L[ℝ] V₂ p.1) {S : Set ℝ}
    (h : ∀ (Y : Cₛ^∞⟮I; F₁, V₁⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
        (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y p.1)))
        ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (F₁ →L[ℝ] F₂)
        (E := fun x : M => V₁ x →L[ℝ] V₂ x) p.1 (φ p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  apply contMDiffWithinAt_clm_of_pointwise_jointSource (IX := I.prod 𝓘(ℝ, ℝ)) (X := M × ℝ)
  intro v
  let e₁ := trivializationAt F₁ V₁ x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ F₁
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ V₁ x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hφY : ∀ i, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y i p.1)))
      ((Set.univ : Set M) ×ˢ S) := fun i => h (Y i)
  have hφY_fiber : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => (e₂ ⟨p.1, φ p (Y i p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := fun i => by
    have hi := (Bundle.contMDiffWithinAt_totalSpace (F := F₂) (E := V₂)).mp ((hφY i) p₀ hp₀)
    exact hi.2
  have hsum : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => ∑ i, b.repr v i • (e₂ ⟨p.1, φ p (Y i p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    apply ContMDiffWithinAt.sum
    intro i _
    exact (contMDiffWithinAt_const (c := (b.repr v i : ℝ))).smul (hφY_fiber i)
  refine hsum.congr_of_eventuallyEq ?_ ?_
  · have h_base₁ : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e₁.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e₁.open_baseSet.mem_nhds he₁)
    have h_base₂ : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e₂.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e₂.open_baseSet.mem_nhds he₂)
    have h_frame : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        ∀ i, (Y i) p.1 = e₁.localFrame b i p.1 := by
      have hYnhd : ∀ᶠ x in 𝓝 x₀, ∀ i, (Y i) x = e₁.localFrame b i x := hY
      exact (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀)) hYnhd
    filter_upwards [h_base₁, h_base₂, h_frame] with p hx₁ hx₂ hYp
    have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    have h_inCoord : (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ p.1 x₀ p.1 (φ p)) v =
        e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 v)) := rfl
    rw [h_inCoord]
    have h₁ : e₁.symmL ℝ p.1 v = ∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i) := by
      conv_lhs => rw [hv_decomp]
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₂ : (φ p) (∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i)) =
        ∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i)) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₃ : e₂.continuousLinearMapAt ℝ p.1 (∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i))) =
        ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 (b i))) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    rw [h₁, h₂, h₃]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    have h_lf : e₁.symmL ℝ p.1 (b i) = (Y i) p.1 := by
      rw [hYp i]
      rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    rw [h_lf]
    rw [Trivialization.continuousLinearMapAt_apply]
    exact congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e₂) hx₂) _
  · have hx₁ : x₀ ∈ e₁.baseSet := he₁
    have hx₂ : x₀ ∈ e₂.baseSet := he₂
    have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    have h_inCoord : (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ p₀.1 x₀ p₀.1 (φ p₀)) v =
        e₂.continuousLinearMapAt ℝ p₀.1 ((φ p₀) (e₁.symmL ℝ p₀.1 v)) := rfl
    rw [h_inCoord]
    have h₁ : e₁.symmL ℝ p₀.1 v = ∑ i, (b.repr v) i • e₁.symmL ℝ p₀.1 (b i) := by
      conv_lhs => rw [hv_decomp]
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₂ : (φ p₀) (∑ i, (b.repr v) i • e₁.symmL ℝ p₀.1 (b i)) =
        ∑ i, (b.repr v) i • (φ p₀) (e₁.symmL ℝ p₀.1 (b i)) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₃ : e₂.continuousLinearMapAt ℝ p₀.1 (∑ i, (b.repr v) i • (φ p₀) (e₁.symmL ℝ p₀.1 (b i))) =
        ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ p₀.1 ((φ p₀) (e₁.symmL ℝ p₀.1 (b i))) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    rw [h₁, h₂, h₃]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    have hYnhd : ∀ᶠ x in 𝓝 x₀, ∀ i, (Y i) x = e₁.localFrame b i x := hY
    have hY0 : ∀ i, (Y i) x₀ = e₁.localFrame b i x₀ := hYnhd.self_of_nhds
    have h_lf : e₁.symmL ℝ p₀.1 (b i) = (Y i) p₀.1 := by
      rw [← hx₀, hY0 i]
      rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    rw [h_lf]
    rw [Trivialization.continuousLinearMapAt_apply]
    exact congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e₂) hx₂) _

/-! ### Joint `(x, s)`-smoothness of the chart inverse-Gram entry along the realized family -/

/-- **Joint `(x, s)`-smoothness of the chart inverse-Gram entry.**  On the product of the chart-`α`
source and the realized small set, the intrinsic chart inverse-Gram entry
`(x, s) ↦ G^{ij}(realizedFam g₀ T T' s)(α, x)` is jointly `C^∞`.  Obtained by composing the joint
Euclidean inverse-Gram smoothness `gen_joint_invGram` (from the joint-Gram tower
`realizedFam_genJointGram`) with the smooth moving point `(x, s) ↦ (s, extChartAt I α x)`, then
reading off `chartInvGramOnE g α i j (extChartAt I α x) = G^{ij}(g)(α, x)` on the source. -/
theorem realizedFam_chartInvGramMatrix_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_invGram (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

/-- **A `δ < 1`-free joint chart inverse-Gram for the realized family.**  Identical to
`realizedFam_chartInvGramMatrix_jointContMDiffOn` but threaded through the `δ`-free joint Gram
`realizedFam_genJointGram_free`, so it carries NO individual smallness hypotheses `δ < 1`,
`δ' < 1`.  This is the `hinv` input to `metricSharp_jointContMDiffOn` that keeps the keystone
signature frozen. -/
theorem realizedFam_chartInvGramMatrix_jointContMDiffOn_free
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_invGram (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

/-! ### Joint `(x, s)`-smoothness of the metric sharp along the realized family -/

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint chart-basis frame section over `M × ℝ`.**  The chart-`α` frame vector
`chartBasisVecFiber α i x` is `s`-independent; its `M × ℝ`-section `(x, s) ↦ ⟨x, e_i(x)⟩` is jointly
`C^∞` on the chart-`α` source × `univ`, by pulling the spatial smoothness `chartBasisVec_contMDiffOn`
back along the smooth first projection. -/
theorem chartBasisVec_jointContMDiffOn (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (chartBasisVecFiber (I := I) α i p.1))
      ((chartAt H α).source ×ˢ (Set.univ : Set ℝ)) := by
  have hbase := chartBasisVec_contMDiffOn (I := I) α i
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  rw [hbase_eq] at hbase
  exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the chart-local sharp coefficient.**  For a metric family `gfam`
whose chart inverse-Gram is jointly `(x, s)`-`C^∞` on the chart-`α` source × `S`, and a covector
family `cv` whose chart-frame components `(x, s) ↦ cv s x (e_j(x))` are jointly `C^∞` there, the
`i`-th sharp coefficient `(x, s) ↦ ∑_j G^{ij}(gfam s)(α, x) · cv_j(s, x)` is jointly `C^∞`. -/
theorem metricSharpChartCoeff_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ}
    (hinv : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  have heq : (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1) =
      (fun p : M × ℝ => ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j *
          cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1)) := by
    funext p; rw [metricSharpChartCoeff_def]
  rw [heq]
  exact contMDiffOn_finset_sum (fun j _ => (hinv i j).mul (hcv j))

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the chart-local sharp representative total-space map over `M × ℝ`,
on the chart-`α` source.**  The chart-local linear-combination representative
`(x, s) ↦ ⟨x, ∑_i coeff_i(x, s) • e_i(x)⟩` is jointly `C^∞` into the tangent-bundle total space on
chart-`α` source × `S`.  Worked pointwise through the total-space characterization
`contMDiffWithinAt_totalSpace`: the projection is `(x, s) ↦ x` (smooth), and the trivialized fibre
coordinate at the chart-center trivialization is `∑_i coeff_i(x, s) • b_i`, jointly `C^∞` by the joint
coefficient smoothness `metricSharpChartCoeff_jointContMDiffOn`.  Stated with the trivialization at
`α` fixed via `contMDiffWithinAt_totalSpace_of_baseSet`. -/
theorem metricSharpChartLocal_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ}
    (hinv : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (metricSharpChartLocal (I := I) (gfam p.2) α (cv p.2) p.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hcoeff : ∀ i, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1)
      ((chartAt H α).source ×ˢ S) :=
    fun i => metricSharpChartCoeff_jointContMDiffOn (I := I) gfam α cv hinv hcv i
  set e := trivializationAt E (TangentSpace I) α with he

  have hcoord_eq : ∀ q ∈ (chartAt H α).source ×ˢ S,
      (e ⟨q.1, metricSharpChartLocal (I := I) (gfam q.2) α (cv q.2) q.1⟩).2 =
        ∑ i, metricSharpChartCoeff (I := I) (gfam q.2) α (cv q.2) i q.1 •
          (chartModelBasis E) i := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ e.baseSet := by
      rw [he, trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    have hclm : ∀ w : TangentSpace I q.1,
        (e ⟨q.1, w⟩).2 = e.continuousLinearMapAt ℝ q.1 w := fun w => by
      rw [Trivialization.continuousLinearMapAt_apply]
      exact (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) w).symm
    unfold metricSharpChartLocal
    rw [hclm, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, ← hclm]
    congr 1
    rw [trivializationAt_chartBasisVec_snd (I := I) α i hqbase]

  have hcoordSmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => (e ⟨q.1, metricSharpChartLocal (I := I) (gfam q.2) α (cv q.2) q.1⟩).2)
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.congr ?_ hcoord_eq
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    exact (hcoeff i).smul contMDiffOn_const

  haveI : MemTrivializationAtlas e := by rw [he]; infer_instance
  rw [Bundle.Trivialization.contMDiffOn_iff (e := e) ?_]
  · exact ⟨contMDiffOn_fst, hcoordSmooth⟩
  · rintro q ⟨hqx, _⟩
    rw [Trivialization.mem_source, he, trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hqx

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Global joint `(x, s)`-smoothness of the metric sharp over `M × ℝ`, on the small set.**  For a
metric family `gfam` with jointly-`C^∞` chart inverse-Gram on every chart source × `S`, and a covector
family `cv` with jointly-`C^∞` chart-frame components, the metric-sharp total-space map
`(x, s) ↦ ⟨x, metricSharp (gfam s) x (cv s x)⟩` is jointly `C^∞` on `M × ℝ` over the slab
`univ ×ˢ S`.  The global statement is patched from the chart-local representative
(`metricSharpChartLocal_jointContMDiffOn`), which agrees with the abstract pointwise sharp on each
chart source (`metricSharpChartLocal_eq_metricSharp`), localised at each base point through the open
chart source. -/
theorem metricSharp_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ} (hS : IsOpen S)
    (hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (metricSharp (I := I) (gfam p.2) p.1 (cv p.2 p.1)))
      (Set.univ ×ˢ S) := by
  intro p hp
  obtain ⟨_, hps⟩ := hp

  have hlocal := metricSharpChartLocal_jointContMDiffOn (I := I) gfam p.1 cv
    (hinv p.1) (hcv p.1)

  have heqOn : ∀ q ∈ (chartAt H p.1).source ×ˢ S,
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (metricSharpChartLocal (I := I) (gfam q.2) p.1 (cv q.2) q.1) =
        TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (metricSharp (I := I) (gfam q.2) q.1 (cv q.2 q.1)) := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    rw [metricSharpChartLocal_eq_metricSharp (I := I) (gfam q.2) p.1 (cv q.2) hqbase]

  have hpmem : p ∈ (chartAt H p.1).source ×ˢ S := ⟨mem_chart_source H p.1, hps⟩
  have hnhd : (chartAt H p.1).source ×ˢ S ∈ nhdsWithin p (Set.univ ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H p.1).source ×ˢ S,
      (chartAt H p.1).open_source.prod hS, hpmem, fun q hq => hq.1⟩

  have hlocalAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (metricSharpChartLocal (I := I) (gfam q.2) p.1 (cv q.2) q.1))
      (Set.univ ×ˢ S) p :=
    (hlocal p hpmem).mono_of_mem_nhdsWithin hnhd

  refine hlocalAt.congr_of_eventuallyEq ?_ (heqOn p hpmem).symm
  filter_upwards [hnhd] with q hq using (heqOn q hq).symm

/-! ### Joint `(x, s)`-smoothness of the inverse-metric (cometric) sharp along the realized family -/

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- The inverse-metric sharp Hom-section of a jointly smooth realized metric family is jointly
smooth on the regular spacetime slab. -/
theorem invSharp_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (G.metric p.2) p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => inverseMetricSharpFib (I := I) (G.metric p.2) p.1)
    (S := D.regular)
  intro Y
  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun _ b => cotangentToDualLinear (I := I) (x := b) (Y b) with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (G.metric p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ D.regular) :=
    fun α i j => invGram_of_family (I := I) G hG α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ D.regular) := by
    intro α j
    have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Y α j
    have heqfn : (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1)) =
        (fun p : M × ℝ => (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b)) p.1) := by
      funext p
      rw [hcvdef]
      simp only
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [heqfn]
    exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun t => G.metric t) (cv := cv) (S := D.regular)
    D.regular_isOpen hinv hcv
  refine hjoint.congr (fun p _ => ?_)
  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (metricSharp (I := I) (G.metric p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (inverseMetricSharpFib (I := I) (G.metric p.2) p.1 (Y p.1))
  rw [inverseMetricSharpFib_apply, hcvdef]

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the inverse-metric (cometric) sharp Hom-section along the
realized family, on the slab `univ ×ˢ realizedSmallSet`.**  The joint-parameter lift of the
single-metric `inverseMetricSharpField_contMDiff`: the cometric Hom-section
`x ↦ inverseMetricSharpFib (realizedFam s) x : Hom(T^*M, TM)` is jointly `C^∞` in `(x, s)` over
the realized small set.  Via the within-slab CLM-section bridge
(`contMDiffOn_clm_section_of_pointwise_jointMR`) it reduces, on each globally smooth covector
field `Y`, to the joint smoothness of `(x, s) ↦ ♯_{g_s} (Y x) = metricSharp (g_s) x
(cotangentToDual (Y x))`, supplied by the LANDED `metricSharp_jointContMDiffOn` threaded through
the `δ`-free joint chart inverse-Gram (`realizedFam_chartInvGramMatrix_jointContMDiffOn_free`) and
the `s`-independent chart-frame components of the smooth covector field `Y`. -/
theorem inverseMetricSharpField_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => inverseMetricSharpFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y

  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun _ b => cotangentToDualLinear (I := I) (x := b) (Y b) with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun α i j => realizedFam_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro α j
    have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Y α j
    have heqfn : (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1)) =
        (fun p : M × ℝ => (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b)) p.1) := by
      funext p
      rw [hcvdef]
      simp only
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [heqfn]
    exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s) (cv := cv)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen hinv hcv
  refine hjoint.congr (fun p hp => ?_)

  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
  rw [inverseMetricSharpFib_apply, hcvdef]

/-! ### s-slice smoothness of the chart Ricci along the realized family -/

/-- The s-slice of the joint chart-Ricci smoothness: `s ↦ chartRicciTensor (gfam s) α i k y₀`
is `ContDiffAt ℝ ∞` at every `s₀ ∈ S` (chart-interior `y₀`). -/
private lemma gen_s_contDiffAt_ricci (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) s₀ := by
  have hjoint := gen_joint_ricci (I := I) gfam α hG i k hs hy
  have hcomp : (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) =
      (fun p : ℝ × E => chartRicciTensor (I := I) (gfam p.1) α i k p.2) ∘
        (fun s : ℝ => (s, y₀)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

/-- The `s`-slice of the joint DeTurck–Ricci chart smoothness: at a fixed chart-interior point `y₀`,
the scalar `s ↦ chartDeTurckRicciRHS (gfam s) g_bg α i k y₀` is `C^∞` in `s`.  The DeTurck analog of
`gen_s_contDiffAt_ricci`, threaded through `gen_joint_chartDeTurckRicciRHS`. -/
private lemma gen_s_contDiffAt_deTurckRicciRHS (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S) (g_bg : SmoothRiemannianMetric I M)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i k y₀) s₀ := by
  have hjoint := gen_joint_chartDeTurckRicciRHS (I := I) gfam α hG g_bg i k hs hy
  have hcomp : (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i k y₀) =
      (fun p : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam p.1) g_bg α i k p.2) ∘
        (fun s : ℝ => (s, y₀)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

/-- For `s` in the small set, the realized family metric equals the genuine realized metric
path metric (same fibre inner product). -/
theorem realizedMetricPath_eq_realizedFam (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1 =
      realizedFam (I := I) g₀ T T' hδ hδ' s := by
  refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
  rw [realizedMetricPath_inner, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem]

/-! ### The realized Ricci value as a chart sum + differentiability -/

/-- The chart-sum form of the realized Ricci path value (valid on the small set, off the
clamp), as a `C^∞`-in-`s` scalar function. -/
def realizedRicciChartSum (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ k,
    ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
      chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k
        (extChartAt I x x)

theorem realizedRicciChartSum_contDiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold realizedRicciChartSum
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  exact contDiffAt_const.mul (gen_s_contDiffAt_ricci (I := I) _ x hG i k hs hy)

/-- **The combined DeTurck–Ricci realized chart sum is `C^∞` in `s` on the small set.**
The DeTurck analog of `realizedRicciChartSum_contDiffAt`: the coordinate sum of the chart
components of `deTurckRicciRHS g_bg (realizedFam s)` is `C^∞` in `s` at every `s₀` of the
realized small set, since each chart component equals the chart scalar `chartDeTurckRicciRHS`
(`chartFComponentOnE_deTurckRicciRHS_eq` at the chart-centre interior point) which is `C^∞` in
`s` by `gen_s_contDiffAt_deTurckRicciRHS`.  This is the FTC differentiability input for the
combined Ricci–DeTurck mean-value arm (it matches the body of the downstream
`realizedDeTurckRicciChartSum`, which must live downstream because it carries the `g_bg`
background but is otherwise the same coordinate sum). -/
theorem realizedDeTurckRicciChartSum_contDiffAt (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have heq : (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          chartDeTurckRicciRHS (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i k
            (extChartAt I x x)) := by
    funext s
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartFComponentOnE_deTurckRicciRHS_eq
      (I := I) g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k hy]
  rw [heq]
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  exact contDiffAt_const.mul
    (gen_s_contDiffAt_deTurckRicciRHS (I := I) _ x hG g_bg i k hs hy)

/-- On `Icc 0 1`, the (clamped) realized Ricci path value equals the chart-sum form. -/
theorem realizedRicciPathValue_eq_chartSum_on_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w s := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : max 0 (min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le (zero_le_one) (le_trans (min_le_right s 1) (le_refl 1))) =
        realizedFam (I := I) g₀ T T' hδ hδ' s := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem,
      hclamp]
  rw [hmetric]

  rw [realizedRicciChartSum]
  exact ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) x
    (chartRiemannBasisIdentity_holds (I := I) _ x) v w

/-! ### Differentiability and integrability, closing the FTC child -/

/-- `realizedRicciPathValue` is differentiable at every `s₀ ∈ Ioo 0 1`. -/
theorem realizedRicciPathValue_differentiableAt_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ
      (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s₀] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo hs)
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  exact ((realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
    hmem).differentiableAt (by simp)).congr_of_eventuallyEq heq

/-- On `Ioo 0 1`, the linearized Ricci integrand equals the derivative of the chart-sum. -/
theorem linearizedRicciAt_eq_deriv_chartSum_on_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo ht)
  rw [linearizedRicciAt]
  exact Filter.EventuallyEq.deriv_eq heq

/-- The derivative of the chart-sum is continuous on the open small set. -/
theorem deriv_realizedRicciChartSum_continuousOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcd : ContDiffOn ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w)
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun s hs =>
    (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).contDiffWithinAt
  exact hcd.continuousOn_deriv_of_isOpen realizedSmallSet_isOpen (by exact_mod_cast le_top)

/-- The linearized Ricci integrand is interval-integrable on `[0,1]`. -/
theorem linearizedRicciAt_intervalIntegrable (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      MeasureTheory.volume 0 1 := by

  have hcont : ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (Set.Icc (0:ℝ) 1) :=
    (deriv_realizedRicciChartSum_continuousOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w).mono
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
  have hii : IntervalIntegrable
      (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one

  refine hii.congr_ae ?_
  have hsub : Set.Ioo (0:ℝ) 1 ⊆
      {s | deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s =
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact (linearizedRicciAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).symm
  have hnull : (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1)ᶜ = 0 := by
    rw [Set.uIoc_of_le zero_le_one]
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (Set.Ioo (0:ℝ) 1)ᶜ ∩ Set.Ioc 0 1 ⊆ {1} := by
      intro t ht
      obtain ⟨htc, ht0, ht1⟩ := ht
      rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at htc
      rcases htc with h | h
      · exact absurd ht0 (not_lt.mpr h)
      · exact (le_antisymm ht1 h) ▸ rfl
    exact MeasureTheory.measure_mono_null hsub1 (by simp)
  refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

/-- `realizedRicciPathValue` is continuous on `Icc 0 1`. -/
theorem realizedRicciPathValue_continuousOn_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.congr
    (f := realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) ?_ ?_
  · exact fun s hs =>
      (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs


/-- **The path `s`-derivative of the realized Ricci tensor.**

For the realized metric path `g_s = realize(g₀, (1 - s)·T' + s·T)` joining `realize(g₀, T')`
to `realize(g₀, T)`, the scalar `s ↦ Ric(g_s)_x(v, w)` has, at every interior parameter
`s₀ ∈ (0,1)`, the derivative `linearizedRicciAt g_s (T - T')_x(v, w)` (the linearized Ricci
operator at the path metric in the perturbation direction), and the derivative is
interval-integrable on `[0,1]`.

The interior parameter range `(0,1)` (rather than the closed `[0,1]`) is forced by the
endpoint clamp in `realizedRicciPathValue`: outside `[0,1]` the value is constant in `s`, so
the clamped scalar is only one-sided differentiable at the endpoints; the genuine `s`-derivative
extends continuously to `[0,1]` and the FTC reduction uses the open-interval form
`integral_eq_sub_of_hasDerivAt_of_le` together with continuity on `[0,1]`
(`realizedRicciPathValue_continuousOn_Icc`).

This is the **mean-value content**: via the intrinsic↔chart Ricci bridge
(`ricciTensor_eq_chartRicciSwap_of_basis_identity`) the path Ricci value equals a fixed linear
combination of chart Ricci tensors of the path metric, and the realized chart Gram is affine
in `s` × smooth in `y`, so the joint `(s,y)`-smoothness of the whole chart Christoffel→Riemann
polynomial (`realizedRicciChartSum_contDiffAt`) makes `s ↦ Ric(g_s)_x(v, w)` `C^∞` in `s` on a
neighbourhood of `[0,1]`, hence differentiable with continuous (integrable) derivative. -/
theorem hasDerivAt_ricciTensor_realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    (∀ s₀ ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
          (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s₀) s₀) ∧
      IntervalIntegrable
        (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
        MeasureTheory.volume 0 1 := by
  refine ⟨fun s₀ hs₀ => ?_, ?_⟩
  · rw [linearizedRicciAt]
    exact (realizedRicciPathValue_differentiableAt_Ioo (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs₀).hasDerivAt
  · exact linearizedRicciAt_intervalIntegrable (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w

/-- **The mean-value (FTC) reduction of the realized Ricci-arm difference.**

For two endpoint perturbation tensor sections `T, T' : SmoothCcTensor g₀ 0 2`, both
`g₀`-fibre small with constant `< 1`, the difference of the two realized Ricci tensors
equals the integral over `[0,1]` of the linearized Ricci operator along the straight-line
metric path joining `realize(g₀, T')` to `realize(g₀, T)`, applied to the perturbation
velocity `T - T'`:
$$\operatorname{Ric}(g_1)_x(v, w) - \operatorname{Ric}(g_1')_x(v, w)
    = \int_0^1 \bigl(D\!\operatorname{Ric}\bigr)_{g_s}[T - T']_x(v, w)\, ds.$$

This is the mean-value foundation that the Ricci-arm rebuild consumes in place of the
single-endpoint Palatini telescope: the difference is recovered as the integral of the
genuine metric-derivative (linearized Ricci) along a path, with no two-endpoint cross
terms. -/
theorem ricciTensor_realized_sub_eq_integral_linearizedRicci
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w -
        ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w =
      ∫ s in (0 : ℝ)..1,
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  obtain ⟨hderiv, hint⟩ :=
    hasDerivAt_ricciTensor_realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hcont := realizedRicciPathValue_continuousOn_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hFTC :
      ∫ s in (0 : ℝ)..1,
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
        realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 1 -
          realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 0 :=
    integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [hFTC, realizedRicciPathValue_one, realizedRicciPathValue_zero]

/-! ### The joint `(s, x)`-smoothness keystone: the intrinsic fibre coefficient operators
along the realized path are jointly smooth -/

private local instance instCompleteSpaceE_keystone : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

/-- **Continuity-in-`s` slice of a joint `(s, x)`-smooth coefficient family.**  Given a family
`Φ : ℝ → SmoothCcTensor g₀ r s` whose joint `(x, s)`-data is `C^∞` over the product base `M × ℝ`,
at every fixed base point `x` the model-fibre value `s ↦ (Φ s).toSection x |>.toModel` is
continuous in `s`.  The joint section restricted to the smooth slice `t ↦ (x, t)` is continuous
into the total space; the trivialization at the constant base `x` is a homeomorphism on its base
set (which contains `x`), so the fibre value `t ↦ (Φ t).toSection x` is continuous in the fibre
topology, and post-composing with the continuous model coercion `TensorRSSpace.toModel`
(`toModel_continuous`) yields the claim. -/
theorem jointContMDiff_toModel_continuous_slice
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) S := by

  have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) :=
    (contMDiff_const).prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) S ((Set.univ : Set M) ×ˢ S) :=
    fun t ht => ⟨Set.mem_univ _, ht⟩
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun t : ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x)) S :=
    hjoint.comp hmap.contMDiffOn hmaps

  have hcont_total : ContinuousOn (fun t : ℝ =>
      TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x)) S :=
    hslice.continuousOn

  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x with he
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hcoord : ContinuousOn (fun t : ℝ =>
      (e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x ((Φ t).toSection x))).2) S :=
    continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp hcont_total
      (fun t _ => e.mem_source.mpr hxbase))

  have hfibre : ContinuousOn (fun t : ℝ => (Φ t).toSection x) S := by
    have hkey : ∀ t : ℝ, (Φ t).toSection x =
        (e.continuousLinearEquivAt ℝ x hxbase).symm
          ((e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
            ((Φ t).toSection x))).2) := by
      intro t
      have hp := Trivialization.apply_eq_prod_continuousLinearEquivAt
        (R := ℝ) (e := e) (b := x) hxbase ((Φ t).toSection x)
      have hsnd := congrArg Prod.snd hp
      simp only at hsnd
      rw [hsnd, ContinuousLinearEquiv.symm_apply_apply]
    have hrhs : ContinuousOn (fun t : ℝ =>
        (e.continuousLinearEquivAt ℝ x hxbase).symm
          ((e (TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
            ((Φ t).toSection x))).2)) S :=
      (e.continuousLinearEquivAt ℝ x hxbase).symm.continuous.comp_continuousOn hcoord
    exact hrhs.congr (fun t _ => hkey t)
  exact Tensor0SBundle.TensorRSSpace.toModel_continuous.comp_continuousOn hfibre

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the interior-product field over the product base, with a joint
vector slot.**  For a joint-smooth vector field `X` and a joint-smooth `(0, s + 1)`-tensor family
`α` over `M × ℝ`, the interior product `(p ↦ ⟨p.1, interior_product s p.1 (X p) (α p)⟩)` is jointly
`C^∞` on the slab `univ ×ˢ S`.  The product-base `ContMDiffOn (univ ×ˢ S)` analog of
`interiorProductField_contMDiff`, worked pointwise through `Bundle.contMDiffWithinAt_totalSpace`:
the trivialized fibre coordinate at the chart-center trivialization is `model_interior_bilinear` (a
constant continuous-bilinear model map) applied to the trivialized joint `X` and the trivialized
joint `α`. -/
theorem interiorProductField_jointContMDiffOn_vecJoint (s : ℕ) {S : Set ℝ}
    (X : ∀ p : M × ℝ, TangentSpace I p.1)
    (hX : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (X p))
      ((Set.univ : Set M) ×ˢ S))
    (α : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 1) I p.1)
    (hα : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1 (α p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) p.1
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s p.1 (X p) (α p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hα' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z)).mp (hα p₀ hp₀)
  have hX' := (Bundle.contMDiffWithinAt_totalSpace (F := E) (E := TangentSpace I)).mp (hX p₀ hp₀)
  have h_combine :
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E) ∞
        (fun p : M × ℝ => Tensor0SBundle.model_interior_bilinear ℝ E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨p.1, X p⟩).2)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀ ⟨p.1, α p⟩).2))
        ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := Tensor0SBundle.model_interior_bilinear ℝ E s)).clm_apply
      hX'.2).clm_apply hα'.2
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    apply ContinuousMultilinearMap.ext
    intro v
    set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 with hsymmL
    set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨p.1, X p⟩).2 with hgtilde
    change (α p) (@Fin.cons s (fun _ => E) ((X p : TangentSpace I p.1) : E) (fun i => symmL (v i))) =
      (α p) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · change ((X p : TangentSpace I p.1) : E) = symmL gtilde
      have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := ℝ) hx (X p)
      have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p.1 (X p) =
          gtilde := by
        change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p.1 (X p) = _
        rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
      rw [hcl] at h
      exact h.symm
    · intro j
      rfl
  · have hx : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt _ _ x₀
    apply ContinuousMultilinearMap.ext
    intro v
    set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1 with hsymmL
    set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨p₀.1, X p₀⟩).2 with hgtilde
    change (α p₀) (@Fin.cons s (fun _ => E) ((X p₀ : TangentSpace I p₀.1) : E)
        (fun i => symmL (v i))) =
      (α p₀) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · change ((X p₀ : TangentSpace I p₀.1) : E) = symmL gtilde
      have hx0 : p₀.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
      have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := ℝ) hx0 (X p₀)
      have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p₀.1 (X p₀) =
          gtilde := by
        change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p₀.1 (X p₀) = _
        rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx0]
      rw [hcl] at h
      exact h.symm
    · intro j
      rfl

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- Raising the first slot of a jointly smooth covariant tensor by a smooth metric family is
jointly smooth on the regular spacetime slab. -/
theorem comRaise_of_family (s : ℕ)
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (Y : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 2) I p.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) p.1 (Y p))
      ((Set.univ : Set M) ×ˢ D.regular)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) p.1
        (cometricRaiseSlot0Fib (I := I) (G.metric p.2) s p.1 (Y p)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
      cometricRaiseSlot0Fib (I := I) (G.metric p.2) s p.1 (Y p)))
    (S := D.regular)
  intro β
  have hsharp := invSharp_of_family (I := I) G hG
  have hβjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (β p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    have hβM : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x (β x)) := β.contMDiff
    exact hβM.comp_contMDiffOn contMDiffOn_fst
  have hsharpβ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (G.metric p.2) p.1 (β p.1)))
      ((Set.univ : Set M) ×ˢ D.regular) :=
    ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharp hβjoint
  set sharpβ : ∀ p : M × ℝ, TangentSpace I p.1 :=
    fun p => inverseMetricSharpFib (I := I) (G.metric p.2) p.1 (β p.1)
  have hraise := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := s + 1)
    (S := D.regular) (X := sharpβ) hsharpβ (α := fun p => Y p) hY
  refine hraise.congr (fun p _ => ?_)
  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) p.1
        (sharpβ p) (Y p)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
        cometricRaiseSlot0Fib (I := I) (G.metric p.2) s p.1 (Y p)) (β p.1))
  congr 1

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the cometric raise-slot-0 field over the product base.**  For a
joint-smooth `(0, s + 2)`-tensor family `Y` over `M × ℝ`, the cometric raise of slot `0` by the
realized-family cometric `♯_{g_s}`, `(p ↦ ⟨p.1, cometricRaiseSlot0Fib (g_s) s p.1 (Y p)⟩)`, is jointly
`C^∞` on the slab `univ ×ˢ S`.  The product-base analog of `cometricRaiseSlot0Fib_section_contMDiff`:
via the within-slab CLM-section bridge `contMDiffOn_clm_section_of_pointwise_jointMR` (over the
covector slot) it reduces, per global covector field `β`, to the joint interior product
(`interiorProductField_jointContMDiffOn`) of `Y` against the joint smooth raised vector field
`(p ↦ ♯_{g_s}(β p.1))`, the latter being the Mathlib joint apply `ContMDiffOn.clm_bundle_apply`
(base `Prod.fst`) of the LANDED joint cometric Hom-section
`inverseMetricSharpField_realizedFam_jointContMDiffOn` on `β`. -/
theorem cometricRaiseSlot0Fib_realizedFam_jointContMDiffOn [BoundarylessManifold I M] (s : ℕ)
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 2) I p.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) p.1 (Y p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) p.1
        (cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
      cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro β

  have hsharp := inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hβjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (β p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hβM : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x (β x)) := β.contMDiff
    exact (hβM.comp_contMDiffOn contMDiffOn_fst)
  have hsharpβ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (β p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharp hβjoint

  set sharpβ : ∀ p : M × ℝ, TangentSpace I p.1 :=
    fun p => inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (β p.1)
    with hsharpβdef

  have hraise := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := s + 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (X := sharpβ) hsharpβ (α := fun p => Y p) hY
  refine hraise.congr (fun p hp => ?_)

  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) p.1 (sharpβ p) (Y p)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
        cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)) (β p.1))
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Frame-naturality of the natural trace at a fixed trivialization** (metric-independent).  For a
trivialization-centre `x₀` and a point `z` in its base set, the trivialized fibre coordinate of the
natural trace `contract_trace r s z (Tz)` equals `model_contract_trace r s` of the trivialized fibre
coordinate of `Tz`.  This is the pointwise frame-naturality block extracted from
`contractTraceField_contMDiff`, valid pointwise without any smoothness, used to identify the joint
trace fibre coordinate. -/
private theorem contractTraceField_joint_pointwise (r s : ℕ) (x₀ : M) (z : M)
    (Tz : Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z)
    (hx : z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x₀
        ⟨z, Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz⟩).2 =
      Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
        ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I y) x₀ ⟨z, Tz⟩).2) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).symmL ℝ z with hLdef
  set Linv : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ z with hLinvdef
  set Tx : Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E :=
    Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) z Tz with hTxdef
  have hL : L.comp Linv = ContinuousLinearMap.id ℝ E := by
    ext y
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ) hx y
  have hR : Linv.comp L = ContinuousLinearMap.id ℝ E := by
    ext y
    exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL (R := ℝ) hx y
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SSpace k I z) (v : Fin k → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt ℝ z U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).linearMapAt ℝ z) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀ ⟨z, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SModel k ℝ E) (u : Fin k → E),
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ y : E, L (Linv y) = y := by
      intro y
      have h := congrArg (fun f : E →L[ℝ] E => f y) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i; exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U) u
          = ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt ℝ z
            ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt_symmL
              (R := ℝ) hx]
  have h_input :
      ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I y) x₀ ⟨z, Tz⟩).2) =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L).comp
        (Tx.comp (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace (s + 1) I y) x₀).continuousLinearMapAt ℝ z
        ((Tz) ((trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (1 + r) I y) x₀).symmL ℝ z β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L)
        (Tx ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (1 + r) I y) x₀).symmL ℝ z β =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]; rfl
    rw [hβ]; rfl
  have h_output :
      (trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x₀
        ⟨z, Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz⟩).2 =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L).comp
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx).comp
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) x₀).continuousLinearMapAt ℝ z
        ((Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L)
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx)
          ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    change ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
          ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) z) Tz))
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r z)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β))) (fun i => L (v i)) =
      (((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s) Tx)
        ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β)) (fun i => L (v i))
    have hβ2 : (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r z)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β) =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [Tensor0SBundle.model_covariantChange_apply]
      exact h_symmL r β u
    rw [hβ2]
  rw [h_input, h_output]
  exact (Tensor0SBundle.model_contract_trace_naturality (𝕜 := ℝ) (E := E)
    r s L Linv hL hR Tx).symm

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the natural-trace field over the product base.**  For a
joint-smooth `(1 + r, s + 1)`-tensor family `T` over `M × ℝ`, the fibrewise frame-free natural
trace `(p ↦ ⟨p.1, contract_trace r s p.1 (T p)⟩)` is jointly `C^∞` on the slab `univ ×ˢ S`.  The
product-base `ContMDiffOn (univ ×ˢ S)` analog of `contractTraceField_contMDiff`, worked pointwise
through `Bundle.contMDiffWithinAt_totalSpace`: the trivialized fibre coordinate is `model_contract_trace`
(a constant continuous-linear model map) post-composed with the trivialized joint `T`, through the
metric-independent frame-naturality of the trace (`model_contract_trace_naturality`). -/
theorem contractTraceField_jointContMDiffOn (r s : ℕ) {S : Set ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I p.1)
    (hT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) p.1 (T p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1
        (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s p.1 (T p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hT' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z)).mp (hT p₀ hp₀)
  have hTrace : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ => Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
        ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨p.1, T p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s).contMDiff.contMDiffAt.comp_contMDiffWithinAt
      p₀ hT'.2
  refine hTrace.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact contractTraceField_joint_pointwise (I := I) r s x₀ p.1 (T p) hx
  · have hx : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt _ _ x₀
    have hx0 : p₀.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
    exact contractTraceField_joint_pointwise (I := I) r s x₀ p₀.1 (T p₀) hx0

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- The cometric double trace of a jointly smooth covariant tensor by a smooth metric family is
jointly smooth on the regular spacetime slab. -/
theorem comTrace_of_family (p : ℕ)
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (Y : ∀ q : M × ℝ, Tensor0SBundle.Tensor0SSpace (p + 2) I q.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) q.1 (Y q))
      ((Set.univ : Set M) ×ˢ D.regular)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) q.1
        (cometricDoubleTraceFib (I := I) (G.metric q.2) p q.1 (Y q)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  have hraise := comRaise_of_family (I := I) p G hG Y hY
  have htrace := contractTraceField_jointContMDiffOn (I := I) 0 p
    (S := D.regular)
    (fun q : M × ℝ => cometricRaiseSlot0Fib (I := I) (G.metric q.2) p q.1 (Y q))
    hraise
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) q.1
        (Integral.Connection.unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ D.regular) :=
    (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have htraceUnit := ContMDiffOn.clm_bundle_apply (b := Prod.fst) htrace hunit
  refine htraceUnit.congr (fun q _ => ?_)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p
    (cometricLmodel (I := I) (G.metric q.2) q.1)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y q))]
  rw [contract_trace_unitZero_toModel (I := I) p q.1
    (cometricRaiseSlot0Fib (I := I) (G.metric q.2) p q.1 (Y q))]
  congr 1

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the cometric double-trace fibre operator over the product base.**
For a joint-smooth `(0, p + 2)`-tensor family `Y` over `M × ℝ`, the realized-family cometric
double-trace `(q ↦ ⟨q.1, cometricDoubleTraceFib (g_s) p q.1 (Y q)⟩)` is jointly `C^∞` on the slab
`univ ×ˢ S`.  The product-base analog of `cometricDoubleTraceFib_contMDiff`: per joint `Y`, the
fibre value is the natural trace (`contractTraceField_jointContMDiffOn`, `r = 0`) of the joint
cometric raise (`cometricRaiseSlot0Fib_realizedFam_jointContMDiffOn`), evaluated at the unit
`(0, 0)`-section via the Mathlib joint apply `ContMDiffOn.clm_bundle_apply` (base `Prod.fst`). -/
theorem cometricDoubleTraceFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M] (p : ℕ)
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : ∀ q : M × ℝ, Tensor0SBundle.Tensor0SSpace (p + 2) I q.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) q.1 (Y q))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) q.1
        (cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by

  have hraise := cometricRaiseSlot0Fib_realizedFam_jointContMDiffOn (I := I) (s := p) g₀ T T' hδ hδ' Y hY

  have htrace := contractTraceField_jointContMDiffOn (I := I) 0 p
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun q : M × ℝ => cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q))
    hraise

  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) q.1
        (Integral.Connection.unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    ((Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn contMDiffOn_fst)
  have htraceUnit := ContMDiffOn.clm_bundle_apply (b := Prod.fst) htrace hunit
  refine htraceUnit.congr (fun q hq => ?_)

  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p
    (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) q.1)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y q))]
  rw [contract_trace_unitZero_toModel (I := I) p q.1
    (cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q))]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Frame-relabel of the slot reindex at a fixed trivialization** (metric-independent).  For a
trivialization-centre `x₀`, a base-set point `z` and a model `(0, d)`-tensor fibre value `Zz`, the
trivialized fibre coordinate of the slot-reindexed `ofModel (domDomCongr ρ (toModel Zz))` equals the
constant model reindex `domDomCongr ρ` applied to the trivialized coordinate of `Zz`.  The pointwise
relabel identity behind the joint constant-reindex smoothness, mirroring the coordinate identity of
`hreindex` in `ricciArmPrincipalCoeffFib_contMDiff`. -/
private theorem domDomCongrField_joint_pointwise {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x₀ : M) (z : M)
    (Zz : Tensor0SBundle.Tensor0SSpace d I z)
    (hx : z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀
        ⟨z, Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel Zz))⟩).2 =
      ContinuousMultilinearMap.domDomCongr ρ
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, Zz⟩).2) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).symmL ℝ z with hLdef

  have h_cLMAt : ∀ (U : Tensor0SBundle.Tensor0SSpace d I z) (v : Fin d → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).continuousLinearMapAt ℝ z U v =
      U (fun i => L (v i)) := by
    intro U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).linearMapAt ℝ z) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_coord : ∀ (U : Tensor0SBundle.Tensor0SSpace d I z) (v : Fin d → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, U⟩).2 v =
      U (fun i => L (v i)) := by
    intro U v
    rw [← h_cLMAt U v, Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).linearMapAt ℝ z) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [h_coord, h_coord]

  have hof : ∀ (m : Fin d → E),
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
        (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m =
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz)) m := by
    intro m
    have h := Tensor0SBundle.Tensor0SSpace.toModel_ofModel (𝕜 := ℝ) (I := I) (x := z)
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))
    calc (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
            (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m
        = Tensor0SBundle.Tensor0SSpace.toModel
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
              (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m := rfl
      _ = (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz)) m := by
            rw [h]
  rw [hof, ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of a constant model slot-reindex of a joint `(0, d)`-tensor family
over the product base.**  For a fixed model slot permutation `ρ` and a joint-smooth `(0, d)`-tensor
family `Z` over `M × ℝ`, the fibrewise reindexed family `(p ↦ ⟨p.1, ofModel (domDomCongr ρ (toModel
(Z p)))⟩)` is jointly `C^∞` on the slab `univ ×ˢ S`.  The product-base analog of the constant-reindex
`hreindex` step inside `ricciArmPrincipalCoeffFib_contMDiff`: the slot reindex is a fixed model
continuous-linear map (`domDomCongr ρ`), so the trivialized fibre coordinate of the reindexed family
is that constant map applied to the trivialized coordinate of `Z`. -/
theorem domDomCongrField_jointContMDiffOn {d : ℕ} (ρ : Equiv.Perm (Fin d)) {S : Set ℝ}
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z p)))))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hZ' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hZ p₀ hp₀)
  have hcongr : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ => ContinuousMultilinearMap.domDomCongr ρ
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ ⟨p.1, Z p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SBundle.Tensor0SModel d ℝ E => ContinuousMultilinearMap.domDomCongr ρ U) :=
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ ρ).toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hZ'.2
  refine hcongr.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (domDomCongrField_joint_pointwise (I := I) ρ x₀ p.1 (Z p) hx).symm
  · have hx : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt _ _ x₀
    have hx0 : p₀.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
    exact (domDomCongrField_joint_pointwise (I := I) ρ x₀ p₀.1 (Z p₀) hx0).symm

/-! ### Joint `(x, s)`-smoothness of the order-`2` principal coefficient FIBRE operator

The joint-parameter lift of the single-metric base-point smoothness
`ricciArmPrincipalCoeffFib_contMDiff`: the fibre operator
`x ↦ ricciArmPrincipalCoeffFib (realizedFam s) x : Hom(Tensor0S 4, Tensor0S 2)` is jointly `C^∞`
in `(x, s)` over the realized small set.  The operator depends on `g_s` *only* through the smooth
cometric Hom-section `inverseMetricSharpField g_s` (the model raise `cometricLmodel g_s x`, through
`cometricDoubleTraceFib` / `combinedTrace42Model`), whose JOINT smoothness over the slab is the
LANDED `inverseMetricSharpField_realizedFam_jointContMDiffOn` (built from the `δ`-free joint
chart-inverse-Gram tower `realizedFam_chartInvGramMatrix_jointContMDiffOn_free` →
`metricSharp_jointContMDiffOn`).

It is the joint analog of the single-metric structural tower
`inverseMetricSharpField_contMDiff` → `cometricRaiseSlot0Fib_section_contMDiff` →
`cometricDoubleTraceFib_contMDiff` → `ricciArmPrincipalCoeffFib_contMDiff`, lifted to the product
base `M × ℝ` over the slab `univ ×ˢ realizedSmallSet` through the within-slab CLM-section bridge
`contMDiffOn_clm_section_of_pointwise_jointMR` and the Mathlib joint apply `ContMDiffOn.clm_bundle_apply`
(base map `Prod.fst`).  The metric-dependent input (the joint cometric Hom-section) is supplied; the
remaining tower is the metric-INDEPENDENT joint structural mirror (interior product / natural trace /
constant slot reindex / `±1`-section algebra), whose product-base `ContMDiffOn (univ ×ˢ S)` analogs
are *posited* here as this single joint-fibre keystone.  Non-vacuous: it constrains the section to the
realized-family principal coefficient, consumed only as the joint smoothness of that exact fibre
operator. -/
/-- Pointwise addition of two joint total-space maps over base `M` (source `M × ℝ`) is jointly
`C^∞` on the slab.  Worked through the within-slab total-space characterization, adding trivialized
fibre coordinates (a vector-bundle operation). -/
private theorem jointTotalSpace_add {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_add (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)).symm

/-- Pointwise subtraction of two joint total-space maps over base `M`. -/
private theorem jointTotalSpace_sub {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_sub (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)).symm

/-- Pointwise constant scaling of a joint total-space map over base `M`. -/
private theorem jointTotalSpace_smul {d : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_smul a (A p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)).symm

/-- Pointwise addition of two joint `(r, s)`-operator total-space maps over base `M` is jointly
`C^∞` on the slab.  The `TensorRSModel` analog of `jointTotalSpace_add`, worked through the
within-slab total-space characterization, adding trivialized fibre coordinates (a vector-bundle
operation). -/
private theorem jointTotalSpaceRS_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    rw [Pi.add_apply]
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · rw [Pi.add_apply]
    exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option backward.isDefEq.respectTransparency false in
theorem ricciArmPrincipalCoeffFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        (ricciArmPrincipalCoeffFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciArmPrincipalCoeffFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  set κ : Equiv.Perm (Fin 4) := koszulSlotPerm with hκ
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s with hg_s

  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst

  have hYκ := domDomCongrField_jointContMDiffOn (I := I) κ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint

  have hT03 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hYκ

  have hCDT := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Y p.1) hYjoint

  have hswap := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap (0 : Fin 2) 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 4 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        cometricDoubleTraceFib (I := I) (g_s p.2) 2 p.1)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))))
    hT03

  have hcomb := jointTotalSpace_smul (I := I) (d := 2) (1 / 2 : ℝ) _
    (jointTotalSpace_sub (I := I) (d := 2) _ _ (jointTotalSpace_add (I := I) (d := 2) _ _ hT03 hswap) hCDT)
  refine hcomb.congr (fun p hp => ?_)

  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [ricciArmPrincipalCoeffFib_toModel]
  simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [combinedTrace42Model]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

/-- **Joint `(s, x)`-smoothness of the order-`2` principal coefficient along the realized path.**

For the realized metric family `g_s = realizedFam g₀ T T' s`, the intrinsic order-`2`
principal coefficient operator field `ricciArmPrincipalCoeff g₀ g_s` (the combined three-trace
`(4, 2)`-operator field of `g_s`, `RicciDeTurckSectionDifference`) is jointly `C^∞` in the pair
`(x, s)`, as a section over `M × ℝ` of the `(4, 2)`-tensor bundle, **on the slab
`univ ×ˢ realizedSmallSet`** — the realized family is junk-extended to `g₀` off the small set, where it
jumps at the boundary, so the joint smoothness holds only over the open parameter set `realizedSmallSet`
(which contains the integration interval `[0, 1]`), not globally in `s` (`ContMDiffOn`, not `ContMDiff`).

This is the joint-parameter lift of the single-metric base-point smoothness
`ricciArmPrincipalCoeffFib_contMDiff`: the operator depends on `g_s` *only* through the smooth
cometric Hom-section `inverseMetricSharpField g_s` (the model raise `cometricLmodel g_s x`,
through `cometricDoubleTraceFib`/`combinedTrace42Model`), and the chart inverse-Gram of `g_s` is
jointly `(s, y)`-`C^∞` by the joint-Gram tower (`realizedFam_genJointGram` / `gen_joint_invGram`,
which already give the realized-family chart Gram, inverse-Gram and Christoffel jets jointly
`(s, y)`-`C^∞`).  Through the chart-coordinate form of the metric sharp
(`metricSharpChartLocal`/`metricSharpChartCoeff`, whose coefficient is `∑_j G^{ij}(g_s) · cv_j`)
the joint chart-inverse-Gram smoothness lifts the single-metric `contMDiff_clm_section_of_pointwise`
construction to the product base `M × ℝ` via `Bundle.contMDiffAt_totalSpace` (the
`cutoffField_contMDiff` product-base section pattern).  This irreducible joint manifold-section
lift over the product base `M × ℝ` (a complete joint analog of the
`metricSharp_contMDiff_total` → `inverseMetricSharpField_contMDiff` →
`ricciArmPrincipalCoeffFib_contMDiff` tower, threaded through the joint-Gram tower) is *posited*
here as the single joint-fibre-smoothness keystone, to be discharged by recursing into it.  It
genuinely constrains the section to the realized-family principal coefficient (it is consumed only
as the joint smoothness of that exact fibre operator), so it is non-vacuous. -/
theorem ricciArmPrincipalCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((ricciArmPrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by

  have hfib := ricciArmPrincipalCoeffFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  refine hfib.congr (fun p _ => ?_)
  rw [ricciArmPrincipalCoeff_toSection]

/-- **Continuity-in-`s` slice of the order-`2` principal coefficient along the realized path.**

The continuity slice of the joint `(s, x)`-smoothness keystone
`ricciArmPrincipalCoeff_realizedFam_jointContMDiff`: at every fixed base point `x`, the
model-fibre value `s ↦ (ricciArmPrincipalCoeff g₀ g_s).toSection x |>.toModel` is continuous in
`s`.  Obtained by restricting the joint section to the slice `t ↦ (x, t)` (smooth), reading the
fibre coordinate through the trivialization at the constant base `x`, and post-composing with the
continuous model coercion `TensorRSSpace.toModel`. -/
theorem ricciArmPrincipalCoeff_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciArmPrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := ricciArmPrincipalCoeff_realizedFam_jointContMDiff
    (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
    (fun t => ricciArmPrincipalCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t)) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

/-! ### Joint `(x, s)`-smoothness of the raised-Ricci endomorphism along the realized family -/

/-- **Joint `(x, s)`-smoothness of the chart-coordinate Ricci entry along the realized family.**
On the product of the chart-`α` source and the realized small set, the chart Ricci scalar
`(x, s) ↦ Rc_{ik}(realizedFam g₀ T T' s)(α, ϕ_α x)` is jointly `C^∞`.  Mirror of
`realizedFam_chartInvGramMatrix_jointContMDiffOn_free`, substituting the joint Euclidean chart-Ricci
smoothness `gen_joint_ricci` (from the `δ`-free joint Gram `realizedFam_genJointGram_free`) for the
inverse-Gram entry, then composing with the smooth moving point `(x, s) ↦ (s, ϕ_α x)`. -/
theorem realizedFam_chartRicciTensor_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartRicciTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_ricci (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartRicciTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

set_option backward.isDefEq.respectTransparency false in
/-- **(Posited sub-child — joint `(x, s)`-smoothness of the chart-frame Ricci component along the
realized family.)**

For a globally smooth tangent field `Y` and the chart-`α` frame vector `chartBasisVecFiber α j`, the
scalar `(x, s) ↦ Ric(g_s)(Y x, e_j(x))` is jointly `C^∞` on the chart-`α` source × the realized small
set.  This is the joint-parameter lift of the single-metric on-source component smoothness
`ricciTensor_pairing_contMDiff` (specialised to the chart frame): it is the manifold read-off of the
chart Euclidean joint Ricci smoothness `gen_joint_ricci` (from the joint-Gram tower
`realizedFam_genJointGram`) threaded — through the off-centre chart-`α` Ricci basis identity
`ricciTensor_chartBasisVec_alpha_eq` (valid on the full chart source, where
`chartLeviCivitaGoodSet α = (extChartAt I α).source`) and the chart-frame decomposition of the smooth
field `Y` with `s`-independent chart-source-smooth coefficients — to the manifold.  It is the joint
analog of the `s`-independent chart-component input `cotangentSection_chartComponent_contMDiffOn` that
discharges the `hcv` hypothesis of `metricSharp_jointContMDiffOn`; the only `s`-dependence enters
through the curvature `2`-jet of `g_s`, supplied jointly by `gen_joint_ricci`.  It genuinely constrains
the section to the realized-family Ricci component (consumed only as the joint smoothness of that exact
scalar against a smooth field and the chart frame), so it is non-vacuous. -/
theorem ricciTensorSection_chartComponent_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; E, (fun x : M => TangentSpace I x)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ricciTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1)
        (chartBasisVecFiber (I := I) α j p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α

  have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ q : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α Y q p.1 *
          chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α q j
            (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun q _ => ?_)
    have hcoeff : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartCoeff (I := I) α Y q p.1)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
      have hc := chartCoeff_contMDiffOn (I := I) α Y q
      rw [hbase_eq] at hc
      exact hc.comp contMDiffOn_fst (fun p hp => hp.1)
    exact hcoeff.mul
      (realizedFam_chartRicciTensor_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α q j)
  refine hsum.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hx
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx

  set gs := realizedFam (I := I) g₀ T T' hδ hδ' p.2 with hgs
  rw [chartCoeff_recompose (I := I) α Y hxbase]
  rw [map_sum (ricciTensor (I := I) gs p.1), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ricciTensor_chartBasisVec_alpha_eq (I := I) gs α q j hxgood]

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint `(x, s)`-smoothness of the raised-Ricci endomorphism Hom-section along the realized
family, on the slab `univ ×ˢ realizedSmallSet`.**  The joint-parameter lift of the single-metric
`ricEndoRaisedFib_contMDiff`: the raised-Ricci `(1, 1)`-operator field
`x ↦ ricEndoRaisedFib (realizedFam s) x : Hom(TM, TM)` is jointly `C^∞` in `(x, s)` over the realized
small set.  Via the within-slab CLM-section bridge `contMDiffOn_clm_section_of_pointwise_jointMR` it
reduces, on each globally smooth tangent field `Y`, to the joint smoothness of
`(x, s) ↦ ricEndoRaisedFib (g_s) x (Y x) = metricSharp (g_s) x (Ric(g_s)(Y x, ·))`, supplied by the
LANDED `metricSharp_jointContMDiffOn` threaded through the `δ`-free joint chart inverse-Gram
(`realizedFam_chartInvGramMatrix_jointContMDiffOn_free`) and the joint chart-frame Ricci components
`ricciTensorSection_chartComponent_realizedFam_jointContMDiffOn` (the `s`-dependent covector family
`cv s b := (Ric(g_s) b (Y b)).toLinearMap`).  Mirrors `inverseMetricSharpField_realizedFam_jointContMDiffOn`,
substituting the joint Ricci component for the `s`-independent cotangent component. -/
theorem ricEndoRaisedFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (ricEndoRaisedFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => ricEndoRaisedFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y

  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun s b => (ricciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Y b)).toLinearMap
    with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun α i j => realizedFam_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro α j
    have hbase := ricciTensorSection_chartComponent_realizedFam_jointContMDiffOn
      (I := I) g₀ T T' hδ hδ' Y α j
    refine hbase.congr (fun p _ => ?_)
    rw [hcvdef]
    rfl
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s) (cv := cv)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen hinv hcv
  refine hjoint.congr (fun p hp => ?_)

  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (ricEndoRaisedFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
  rw [ricEndoRaisedFib_apply, hcvdef]

/-! ### Generic joint leading-slot endomorphism insertion over the product base -/

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint curry of a joint `(0, d + 1)`-tensor family over the product base.**  For a joint-smooth
`(0, d + 1)`-tensor family `A` over `M × ℝ`, the curried `Hom(TM, T^{(0, d)})`-section
`(p ↦ ⟨p.1, tensor0S_curry d p.1 (A p)⟩)` is jointly `C^∞` on the slab `univ ×ˢ S`.  The product-base
analog of `contMDiffAt_curriedSection_of_contMDiffAt_section`: the curry is the fixed model
continuous-linear-equiv `continuousMultilinearCurryLeftEquiv`, so the trivialized fibre coordinate of
the curried family is that constant map applied to the trivialized coordinate of `A`. -/
private theorem curriedField_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z)).mp (hA p₀ hp₀)
  have hcurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) x₀ ⟨p.1, A p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SBundle.Tensor0SModel (d + 1) ℝ E =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hA'.2
  refine hcurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    have hc := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun z : M => A ⟨z, p.2⟩) x₀ p.1 hx
    rw [TensorMultilinear.curriedSection] at hc
    exact hc
  · have hx0 : p₀.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀
    have hc := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun z : M => A ⟨z, p₀.2⟩) x₀ p₀.1 hx0
    rw [TensorMultilinear.curriedSection] at hc
    exact hc

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **Joint uncurry of a joint `Hom(TM, T^{(0, d)})`-family over the product base.**  Inverse of
`curriedField_jointContMDiffOn`: for a joint-smooth `Hom(TM, T^{(0, d)})`-family `G`, the uncurried
`(0, d + 1)`-tensor family `(p ↦ ⟨p.1, (tensor0S_curry d p.1).symm (G p)⟩)` is jointly `C^∞` on the
slab `univ ×ˢ S`.  The product-base analog of `contMDiff_uncurriedSection_of_contMDiff_homSection`,
threaded through the fixed model uncurry equiv `(continuousMultilinearCurryLeftEquiv).symm`. -/
private theorem uncurriedField_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (G : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace d I p.1)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1 (G p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hG' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z)).mp (hG p₀ hp₀)
  have huncurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E) ∞
      (fun p : M × ℝ => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm
        ((trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) x₀
          ⟨p.1, G p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E) ∞
        (fun U : E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E =>
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hG'.2

  have hpt : ∀ p : M × ℝ,
      p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).baseSet →
      (trivializationAt (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (d + 1) I y) x₀
          ⟨p.1, (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p)⟩).2 =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm
          ((trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
            (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace d I y) x₀
            ⟨p.1, G p⟩).2) := by
    intro p hz
    have hUcurry : TensorMultilinear.curriedSection (I := I) (M := M)
        (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, p.2⟩)) p.1 =
          G p := by
      rw [TensorMultilinear.curriedSection]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have hfwd := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, p.2⟩)) x₀ p.1 hz
    rw [hUcurry] at hfwd
    rw [show (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, p.2⟩)) p.1 =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p) from rfl] at hfwd
    rw [hfwd]
    exact (LinearIsometryEquiv.symm_apply_apply
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ) _).symm
  refine huncurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpt p hx
  · have hx0 : p₀.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀
    exact hpt p₀ hx0

set_option backward.isDefEq.respectTransparency false in
/-- **Joint leading-slot endomorphism insertion applied to a joint `(0, d + 1)`-section.**  For a
joint-smooth endomorphism Hom-field `Λ` and a joint-smooth `(0, d + 1)`-tensor family `A` over
`M × ℝ`, the leading-slot insertion `(p ↦ ⟨p.1, slotInsertEndoFib (d + 1) 0 p.1 (Λ p) (A p)⟩)` is
jointly `C^∞` on the slab `univ ×ˢ S`.  By `slotInsertEndoFib_zero` it equals the joint uncurry
(`uncurriedField_jointContMDiffOn`) of the composition of the joint curried `(0, d + 1)`-section
(`curriedField_jointContMDiffOn`) with the joint endomorphism field, the composition assembled per
smooth tangent test field through the within-slab bridge and the Mathlib joint apply
`ContMDiffOn.clm_bundle_apply` (twice). -/
theorem slotInsertEndo0Field_apply_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (Λ : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hΛ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (Λ p))
      ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p) (A p)))
      ((Set.univ : Set M) ×ˢ S) := by

  have hcurry := curriedField_jointContMDiffOn (I := I) (M := M) (d := d) (S := S) A hA

  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p)))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace d I x)
      (φ := fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p))
      (S := S)
    intro Z

    have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hΛZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Λ p (Z p.1)))
        ((Set.univ : Set M) ×ˢ S) :=
      ContMDiffOn.clm_bundle_apply (b := Prod.fst) hΛ hZjoint

    have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hcurry hΛZ
    refine happ.congr (fun p _ => ?_)
    rfl

  have huncurry := uncurriedField_jointContMDiffOn (I := I) (M := M) (d := d) (S := S)
    (fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p)) hcomp
  refine huncurry.congr (fun p _ => ?_)
  congr 1
  exact slotInsertEndoFib_zero (I := I) (M := M) d p.1 (Λ p) (A p)

set_option backward.isDefEq.respectTransparency false in
/-- **Joint trailing-slot (slot `1`) endomorphism insertion applied to a joint `(0, d + 2)`-section.**
The slot-`1` mirror of `slotInsertEndo0Field_apply_jointContMDiffOn`.  For a joint-smooth endomorphism
Hom-field `Λ` and a joint-smooth `(0, d + 2)`-tensor family `A` over `M × ℝ`, the trailing-slot
insertion `(p ↦ ⟨p.1, slotInsertEndoFib (d + 2) 1 p.1 (Λ p) (A p)⟩)` is jointly `C^∞` on the slab
`univ ×ˢ S`.  By `slotInsertEndoFib_succ` the slot-`1` insertion is the slot extension
`slotExtendFib (d + 1) (d + 1) x (slotInsertEndoFib (d + 1) 0 x (Λ x))` of the slot-`0` insertion one
rank below, i.e. the joint uncurry (`uncurriedField_jointContMDiffOn`) of the left-composition of the
joint curried `(0, d + 1)`-section (`curriedField_jointContMDiffOn`) with the joint inner slot-`0`
insertion operator, the latter applied per smooth tangent test field through the leading-slot bridge
`slotInsertEndo0Field_apply_jointContMDiffOn` (at rank `d`) and the within-slab joint apply
`ContMDiffOn.clm_bundle_apply`. -/
theorem slotInsertEndo1Field_apply_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (g : SmoothRiemannianMetric I M)
    (Λ : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hΛ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (Λ p))
      ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 2) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 2) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 2) I z) p.1
        (slotInsertEndoFib (I := I) (M := M) (d + 2) 1 p.1 (Λ p) (A p)))
      ((Set.univ : Set M) ×ˢ S) := by

  have hcurry := curriedField_jointContMDiffOn (I := I) (M := M) (d := d + 1) (S := S) A hA

  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p))))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (d + 1) I x)
      (φ := fun p : M × ℝ => (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p)))
      (S := S)
    intro Z

    have hcurryZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p) (Z p.1)))
        ((Set.univ : Set M) ×ˢ S) := by
      have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
          ((Set.univ : Set M) ×ˢ S) :=
        Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
      exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hcurry hZjoint

    have happ := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := d) (S := S)
      (Λ := Λ) hΛ
      (A := fun p : M × ℝ =>
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p) (Z p.1)) hcurryZ
    refine happ.congr (fun p _ => ?_)
    rfl

  have huncurry := uncurriedField_jointContMDiffOn (I := I) (M := M) (d := d + 1) (S := S)
    (fun p : M × ℝ => (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p))) hcomp
  refine huncurry.congr (fun p _ => ?_)
  congr 1
  rw [show (1 : Fin (d + 2)) = (0 : Fin (d + 1)).succ from rfl,
    slotInsertEndoFib_succ (I := I) (M := M) g (d + 1) 0 p.1 (Λ p),
    slotExtendFib_apply (I := I) (M := M) g (d + 1) (d + 1) p.1]

set_option backward.isDefEq.respectTransparency false in
/-- **Joint `(x, s)`-smoothness of the leading-slot order-`0` curvature coefficient fibre operator along
the realized family.**  The fibrewise joint analog of `ricciArmOrder0CurvCoeffFibSlot_contMDiff` at the
leading slot: the leading-slot insertion `slotInsertEndoFib 2 0 x (ricEndoRaisedFib (g_s) x)` is jointly
`C^∞` in `(x, s)` as a `(2, 2)`-operator section, on the slab `univ ×ˢ realizedSmallSet`.  Via the
within-slab CLM-section bridge `contMDiffOn_clm_section_of_pointwise_jointMR` it reduces, on each globally
smooth `(0, 2)`-tensor field `Y`, to the joint `(0, 2)`-section
`(x, s) ↦ Y x ∘ (ricEndoRaisedFib (g_s) x, id)` — the leading covariant slot precomposed by the
joint-smooth raised-Ricci endomorphism `ricEndoRaisedFib_realizedFam_jointContMDiffOn`, threaded
through the fixed smooth slot-insertion `slotInsertEndoFib`.  This is the leading slot of the two-slot
Bochner order-`0` coefficient; the trailing slot is the posited
`ricciArmOrder0CurvCoeffFib_realizedFam_jointContMDiffOn`. -/
theorem ricciArmOrder0CurvCoeffFibSlot0_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciArmOrder0CurvCoeffFibSlot (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 0 p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciArmOrder0CurvCoeffFibSlot (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 0 p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s with hg_s

  have hric := ricEndoRaisedFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'

  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst

  have happ := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ => ricEndoRaisedFib (I := I) (g_s p.2) p.1) hric
    (A := fun p : M × ℝ => Y p.1) hYjoint
  refine happ.congr (fun p _ => ?_)

  rw [ricciArmOrder0CurvCoeffFibSlot]

set_option backward.isDefEq.respectTransparency false in
/-- **Joint `(x, s)`-smoothness of the trailing-slot order-`0` curvature coefficient fibre operator along
the realized family.**  The slot-`1` mirror of `ricciArmOrder0CurvCoeffFibSlot0_realizedFam_jointContMDiffOn`:
the trailing-slot insertion `slotInsertEndoFib 2 1 x (ricEndoRaisedFib (g_s) x)` is jointly `C^∞` in
`(x, s)` as a `(2, 2)`-operator section, on the slab `univ ×ˢ realizedSmallSet`.  Via the within-slab
CLM-section bridge `contMDiffOn_clm_section_of_pointwise_jointMR` it reduces, on each globally smooth
`(0, 2)`-tensor field `Y`, to the joint `(0, 2)`-section `(x, s) ↦ Y x ∘ (id, ricEndoRaisedFib (g_s) x)`
— the trailing covariant slot precomposed by the joint-smooth raised-Ricci endomorphism
`ricEndoRaisedFib_realizedFam_jointContMDiffOn`, threaded through the trailing slot-insertion bridge
`slotInsertEndo1Field_apply_jointContMDiffOn` (at `d = 0`).  This is the trailing slot of the two-slot
Bochner order-`0` coefficient. -/
theorem ricciArmOrder0CurvCoeffFibSlot1_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciArmOrder0CurvCoeffFibSlot (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 1 p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciArmOrder0CurvCoeffFibSlot (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 1 p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s with hg_s

  have hric := ricEndoRaisedFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'

  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst

  have happ := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0) g₀
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ => ricEndoRaisedFib (I := I) (g_s p.2) p.1) hric
    (A := fun p : M × ℝ => Y p.1) hYjoint
  refine happ.congr (fun p _ => ?_)

  rw [ricciArmOrder0CurvCoeffFibSlot]

set_option backward.isDefEq.respectTransparency false in
/-- **(Posited deep input — joint `(x, s)`-smoothness of the genuine TWO-SLOT order-`0` curvature
coefficient fibre operator along the realized family.)**

The fibrewise joint analog of `ricciArmOrder0CurvCoeffFib_contMDiff`: the SUM of the leading-slot and
trailing-slot insertions of the joint-smooth raised-Ricci endomorphism `ricEndoRaisedFib (g_s) x` is
jointly `C^∞` in `(x, s)` as a `(2, 2)`-operator section, on the slab `univ ×ˢ realizedSmallSet`.

The order-`0` of the Weitzenböck fold is the SYMMETRIC two-slot Bochner Ricci action
`D(Ric♯·, ·) + D(·, Ric♯·)` (`RicciDeTurckSectionDifference.ricciArmOrder0CurvCoeff`), i.e.
`ricciArmOrder0CurvCoeffFib = slotInsertEndoFib 2 0 (ricEndoRaisedFib g_s) + slotInsertEndoFib 2 1
(ricEndoRaisedFib g_s)`.  Its joint smoothness is the sum of the leading-slot joint smoothness — the
PROVED, sorry-free `ricciArmOrder0CurvCoeffFibSlot0_realizedFam_jointContMDiffOn` (above, via
`slotInsertEndo0Field_apply_jointContMDiffOn`) — and the trailing-slot (`slot 1`) joint smoothness.  The
trailing slot needs the slot-`1` analog of `slotInsertEndo0Field_apply_jointContMDiffOn` (a slot-`1`
joint curry/uncurry insertion bridge — the slot-`1` mirror of `slotInsertEndoFib_zero`'s leading-slot
uncurry), which is not yet on disk; together with the joint additivity of the two bundle sections into the
normed `(2, 2)`-operator fibre.

This irreducible joint manifold-section lift over the product base `M × ℝ` — the two-slot analog of the
`ricEndoRaisedFib_contMDiff` → `slotInsertEndoFib_contMDiff` → `ricciArmOrder0CurvCoeffFib_contMDiff`
tower, threaded through the joint-Gram/Riemann tower `gen_joint_riemann` for both slots — is *posited*
here as the single joint-fibre-smoothness keystone, to be discharged by recursing into the slot-`1` joint
currying tower (a complete mirror of the proved leading-slot tower) plus the bundle-section sum.  It
genuinely constrains the section to the realized-family two-slot curvature coefficient (consumed only as
the joint smoothness of that exact fibre operator), so it is non-vacuous. -/
theorem ricciArmOrder0CurvCoeffFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciArmOrder0CurvCoeffFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hslot0 := ricciArmOrder0CurvCoeffFibSlot0_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  have hslot1 := ricciArmOrder0CurvCoeffFibSlot1_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add (I := I) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (ricciArmOrder0CurvCoeffFibSlot (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 0 p.1))
    (B := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (ricciArmOrder0CurvCoeffFibSlot (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 1 p.1))
    hslot0 hslot1
  refine hadd.congr (fun p _ => ?_)
  rfl

/-- **(Posited deep input — joint `(s, x)`-smoothness of the genuine order-`0` curvature coefficient
along the realized path.)**

For the realized metric family `g_s = realizedFam g₀ T T' s`, the genuine order-`0` **curvature**
coefficient operator field `ricciArmOrder0CurvCoeff g₀ g_s` (the leading-slot insertion of the raised
curvature endomorphism `ricEndoRaisedFib g_s`, `RicciDeTurckSectionDifference`) is jointly `C^∞` in the
pair `(x, s)`, as a section over `M × ℝ` of the `(2, 2)`-tensor bundle, **on the slab
`univ ×ˢ realizedSmallSet`** (the realized family is junk-extended to `g₀` off the small set and jumps at
the boundary, so the joint smoothness is `ContMDiffOn` over `realizedSmallSet ⊇ [0, 1]`, not global).

This is the joint-parameter lift of the single-metric base-point smoothness
`ricciArmOrder0CurvCoeffFib_contMDiff`: the operator depends on `g_s` *only* through the smooth raised
curvature (Ricci) endomorphism Hom-section `ricEndoRaisedFib g_s` (in the leading slot, through
`slotInsertEndoFib`), and the chart Christoffel/Riemann/Ricci jet of `g_s` is jointly `(s, y)`-`C^∞` by
the joint-Gram tower (`realizedFam_genJointGram` / `gen_joint_riemann`).  Through the chart-coordinate
form of the Ricci tensor and the metric sharp (`ricciTensor`/`metricSharp`, whose chart coefficients are
the curvature `2`-jet of `g_s` contracted/raised by `G^{ij}(g_s)`) the joint chart curvature smoothness
lifts the single-metric `slotInsertEndoFib_contMDiff`/`ricEndoRaisedFib_contMDiff` construction to the
product base `M × ℝ` via `Bundle.contMDiffAt_totalSpace` (the `cutoffField_contMDiff` product-base
section pattern).  This irreducible joint manifold-section lift over the product base `M × ℝ` (a complete
joint analog of the `ricEndoRaisedFib_contMDiff` → `slotInsertEndoFib_contMDiff` →
`ricciArmOrder0CurvCoeffFib_contMDiff` tower, threaded through the joint-Gram/Riemann tower
`gen_joint_riemann`) is *posited* here as the single joint-fibre-smoothness keystone, to be discharged
by recursing into it.  It genuinely constrains the section to the realized-family curvature coefficient
(it is consumed only as the joint smoothness of that exact fibre operator), so it is non-vacuous. -/
theorem ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((ricciArmOrder0CurvCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by

  have hfib := ricciArmOrder0CurvCoeffFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  refine hfib.congr (fun p _ => ?_)
  rw [ricciArmOrder0CurvCoeff_toSection]

/-- **Continuity-in-`s` slice of the genuine order-`0` curvature coefficient along the realized path.**

The continuity slice of the joint `(s, x)`-smoothness keystone
`ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff`: at every fixed base point `x`, the model-fibre
value `s ↦ (ricciArmOrder0CurvCoeff g₀ g_s).toSection x |>.toModel` is continuous in `s`.  Obtained by
restricting the joint section to the slice `t ↦ (x, t)` (smooth), reading the fibre coordinate through
the trivialization at the constant base `x`, and post-composing with the continuous model coercion
`TensorRSSpace.toModel`. -/
theorem ricciArmOrder0CurvCoeff_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciArmOrder0CurvCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff
    (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
    (fun t => ricciArmOrder0CurvCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t)) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
