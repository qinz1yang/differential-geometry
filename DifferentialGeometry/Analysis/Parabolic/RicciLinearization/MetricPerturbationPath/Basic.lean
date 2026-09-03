import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.InverseMetricDifferenceCoefficient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.ManifoldSmoothness
import DifferentialGeometry.Geometry.Metric.Family.InverseMetricRegularity
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartSmoothness
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ParametricSmoothness
import DifferentialGeometry.Tensor.RSTensor.ParametricSmoothness
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotInsertionParametricSmoothness
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Spectral.DeTurck
    DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
    DifferentialGeometry.Analysis.Spectral.MetricRealization DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Set Function MeasureTheory intervalIntegral Bundle DifferentialGeometry.Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization


open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorMultilinear_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (T + T') x : Tensor0SSpace 2 I x)
      = (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x)
        + (ccTensorMultilinear (I := I) g T' x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_add]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorModel_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (T + T') x =
      ccTensorModel (I := I) g T x + ccTensorModel (I := I) g T' x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_add, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (T + T') x v w =
      ccTensorBilinSymm (I := I) g T x v w + ccTensorBilinSymm (I := I) g T' x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorModel_add,
    add_apply]
  ring

def convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) : SmoothCcTensor g₀ 0 2 :=
  (1 - s) • T' + s • T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma convexPerturbation_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 0 = T' := by
  simp [convexPerturbation]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma convexPerturbation_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 1 = T := by
  simp [convexPerturbation]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma ccTensorBilinSymm_convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w =
      (1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [convexPerturbation, ccTensorBilinSymm_add, ccTensorBilinSymm_smul,
    ccTensorBilinSymm_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem convexPerturbation_gFibreOpBound (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    metricCauchySchwarzBound (I := I) (M := M) g₀
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

theorem convex_smallConstant_lt_one {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * δ' + s * δ < 1 := by
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  nlinarith [mul_nonneg h1ms (le_of_lt (by linarith : (0 : ℝ) < 1 - δ')),
    mul_nonneg hs0 (le_of_lt (by linarith : (0 : ℝ) < 1 - δ))]

def realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    (convex_smallConstant_lt_one hδ_lt hδ'_lt hs0 hs1)
    (convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' hs0 hs1)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem realizedMetricPath_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : M) (v w : TangentSpace I x) :
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedMetricPath, tensorSectionRealizeMetric_inner]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem riemannianMetric_eq_of_inner (g g' : SmoothRiemannianMetric I M)
    (h : ∀ (b : M) (v w : TangentSpace I b), g.inner b v w = g'.inner b v w) :
    g = g' := by
  have hinner : g.inner = g'.inner := by
    funext b
    exact ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h b v w
  cases g; cases g'
  congr

private lemma clamp_eq_of_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (min s 1) = s := by
  obtain ⟨hs0, hs1⟩ := hs
  rw [min_eq_left hs1, max_eq_right hs0]

def realizedRicciPathValue (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ricciTensor (I := I)
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (le_max_left 0 (min s 1)) (by
        have : min s 1 ≤ 1 := min_le_right s 1
        exact max_le (zero_le_one) this)) x v w

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem realizedRicciPathValue_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem realizedRicciPathValue_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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

def linearizedRicciAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s₀ : ℝ) : ℝ :=
  deriv (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem convexPerturbation_gFibreOpBound_abs (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀
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
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |1 - s| * δ' + |s| * δ < 1 := by
  obtain ⟨h0, h1⟩ := hs
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg h0]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) < 1 - δ').le,
    mul_nonneg h0 (by linarith : (0:ℝ) < 1 - δ).le]

def metricPerturbationPathOnDomain (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    hs (convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPathOnDomain_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) (x : M) (v w : TangentSpace I x) :
    (metricPerturbationPathOnDomain (I := I) g₀ T T' hδ hδ' s hs).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [metricPerturbationPathOnDomain, tensorSectionRealizeMetric_inner]

def metricPerturbationPathDomain {δ δ' : ℝ} : Set ℝ := {s : ℝ | |1 - s| * δ' + |s| * δ < 1}

theorem metricPerturbationPathDomain_isOpen {δ δ' : ℝ} :
    IsOpen (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hcont : Continuous (fun s : ℝ => |1 - s| * δ' + |s| * δ) := by fun_prop
  exact isOpen_lt hcont continuous_const

theorem Icc_subset_metricPerturbationPathDomain {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1) :
    Set.Icc (0:ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
  fun _ hs => abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs

def metricPerturbationPath (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) : SmoothRiemannianMetric I M :=
  if h : |1 - s| * δ' + |s| * δ < 1 then
    metricPerturbationPathOnDomain (I := I) g₀ T T' hδ hδ' s h
  else g₀

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPath_inner_of_mem (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    {s : ℝ} (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) (x : M) (v w : TangentSpace I x) :
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [metricPerturbationPath, dif_pos (Set.mem_ofPred.mp hs), metricPerturbationPathOnDomain_inner]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPath_chartGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) α i j y =
      (1 - s) *
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j y +
        s * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j y := by
  rw [chartGramOnE_def, chartGramOnE_def, chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
    metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner,
    ccTensorBilinSymm_convexPerturbation]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [SigmaCompactSpace M] in
private lemma chartBilinSymmEntry_contMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => ccTensorBilinSymm (I := I) g₀ T x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hB := ccTensorBilinSymm_contMDiff (I := I) g₀ T
  have hv := DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α i
  have hw := DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ccTensorBilinSymm (I := I) g₀ T m
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i m)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hB.contMDiffOn hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [SigmaCompactSpace M] in
private lemma chartBilinSymmOnE_contDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E => ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm y)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)))
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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPath_chartGramFamilyJointSmoothOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (α : M) :
    chartGramFamilyJointSmoothOn (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ') α
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  intro i j s₀ y₀ hs hy
  have hSopen : IsOpen (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := metricPerturbationPathDomain_isOpen
  have heq : (fun p : ℝ × E =>
        chartGramOnE (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.1) α i j p.2)
      =ᶠ[nhds (s₀, y₀)] (fun p : ℝ × E =>
        chartGramOnE (I := I) g₀ α i j p.2 +
          ((1 - p.1) * (fun y : E => ccTensorBilinSymm (I := I) g₀ T' ((extChartAt I α).symm y)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))) p.2 +
            p.1 * (fun y : E => ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm y)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))) p.2)) := by
    have hmem : (metricPerturbationPathDomain (δ := δ) (δ' := δ')) ×ˢ (Set.univ : Set E) ∈ nhds (s₀, y₀) :=
      (hSopen.prod isOpen_univ).mem_nhds ⟨hs, Set.mem_univ _⟩
    filter_upwards [hmem] with p hp
    have hps : p.1 ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') := hp.1
    rw [chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
      metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ' hps,
      ccTensorBilinSymm_convexPerturbation, chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  have hsnd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) (s₀, y₀) := contDiffAt_snd
  have hG₀c : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) g₀ α i j p.2) (s₀, y₀) := by
    have h0 := (((chartGramOnE_contDiffOn (I := I) g₀ α i j).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
    exact h0
  have hBc : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
      ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm p.2)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm p.2))
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm p.2))) (s₀, y₀) := by
    have h0 := (((chartBilinSymmOnE_contDiffOn (I := I) g₀ T α i j).mono
      interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
    exact h0
  have hB'c : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
      ccTensorBilinSymm (I := I) g₀ T' ((extChartAt I α).symm p.2)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm p.2))
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm p.2))) (s₀, y₀) := by
    have h0 := (((chartBilinSymmOnE_contDiffOn (I := I) g₀ T' α i j).mono
      interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
    exact h0
  exact hG₀c.add (((contDiffAt_const.sub contDiffAt_fst).mul hB'c).add (contDiffAt_fst.mul hBc))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPath_chartInvGramMatrix_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hG := metricPerturbationPath_chartGramFamilyJointSmoothOn (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartInvGramOnE_joint_contDiffAt (I := I)
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ') α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPath_chartInvGramMatrix_jointContMDiffOn_free
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hG := metricPerturbationPath_chartGramFamilyJointSmoothOn (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartInvGramOnE_joint_contDiffAt (I := I)
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ') α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

open DifferentialGeometry.Integral.DivergenceTheorem in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    [SigmaCompactSpace M] in
theorem inverseMetricSharpField_metricPerturbationPath_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => inverseMetricSharpFib (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro Y
  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun _ b => cotangentToDualLinear (I := I) (x := b) (Y b) with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    fun α i j => metricPerturbationPath_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    intro α j
    have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Y α j
    have heqfn : (fun p : M × ℝ => cv p.2 p.1 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1)) =
        (fun p : M × ℝ => (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)) p.1) := by
      funext p
      rw [hcvdef]
      simp only
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [heqfn]
    exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s => metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) (cv := cv)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) metricPerturbationPathDomain_isOpen hinv hcv
  refine hjoint.congr (fun p hp => ?_)
  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (DifferentialGeometry.Geometry.Operator.metricSharp
        (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (inverseMetricSharpFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
  rw [inverseMetricSharpFib_apply, hcvdef]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gen_s_contDiffAt_ricci (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    {S : Set ℝ} (hG : chartGramFamilyJointSmoothOn (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) s₀ := by
  have hjoint := chartRicciTensor_joint_contDiffAt (I := I) gfam α hG i k hs hy
  have hcomp : (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) =
      (fun p : ℝ × E => chartRicciTensor (I := I) (gfam p.1) α i k p.2) ∘
        (fun s : ℝ => (s, y₀)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gen_s_contDiffAt_deTurckRicciRHS (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    {S : Set ℝ} (hG : chartGramFamilyJointSmoothOn (I := I) gfam α S)
      (g_bg : SmoothRiemannianMetric I M)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i k y₀) s₀ := by
  have hjoint := chartDeTurckRicciRHS_joint_contDiffAt (I := I) gfam α hG g_bg i k hs hy
  have hcomp : (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i k y₀) =
      (fun p : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam p.1) g_bg α i k p.2) ∘
        (fun s : ℝ => (s, y₀)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem realizedMetricPath_eq_metricPerturbationPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1 =
      metricPerturbationPath (I := I) g₀ T T' hδ hδ' s := by
  refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
  rw [realizedMetricPath_inner, metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem]

def realizedRicciChartSum (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ k,
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
      chartRicciTensor (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k
        (extChartAt I x x)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem realizedRicciChartSum_contDiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s₀ := by
  have hG := metricPerturbationPath_chartGramFamilyJointSmoothOn (I := I) g₀ T T' hδ hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold realizedRicciChartSum
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  exact contDiffAt_const.mul (gen_s_contDiffAt_ricci (I := I) _ x hG i k hs hy)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem realizedDeTurckRicciChartSum_contDiffAt (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)) s₀ := by
  have hG := metricPerturbationPath_chartGramFamilyJointSmoothOn (I := I) g₀ T T' hδ hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have heq : (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v) k *
          ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w) i *
          chartDeTurckRicciRHS (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i k
            (extChartAt I x x)) := by
    funext s
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartFComponentOnE_deTurckRicciRHS_eq
      (I := I) g_bg (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i k hy]
  rw [heq]
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  exact contDiffAt_const.mul
    (gen_s_contDiffAt_deTurckRicciRHS (I := I) _ x hG g_bg i k hs hy)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem realizedRicciPathValue_eq_chartSum_on_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w s := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : max 0 (min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le (zero_le_one) (le_trans (min_le_right s 1) (le_refl 1))) =
        metricPerturbationPath (I := I) g₀ T T' hδ hδ' s := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem,
      hclamp]
  rw [hmetric]
  rw [realizedRicciChartSum]
  exact ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x
    (chartRiemannBasisIdentity_holds (I := I) _ x) v w

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem realizedRicciPathValue_differentiableAt_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ
      (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s₀] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo hs)
  have hmem : s₀ ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  exact ((realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ hδ' x v w
    hmem).differentiableAt (by simp)).congr_of_eventuallyEq heq

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem linearizedRicciAt_eq_deriv_chartSum_on_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo ht)
  rw [linearizedRicciAt]
  exact Filter.EventuallyEq.deriv_eq heq

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deriv_realizedRicciChartSum_continuousOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hcd : ContDiffOn ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := fun s hs =>
    (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ hδ' x v w
      hs).contDiffWithinAt
  exact hcd.continuousOn_deriv_of_isOpen metricPerturbationPathDomain_isOpen (by exact_mod_cast le_top)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem linearizedRicciAt_intervalIntegrable (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      MeasureTheory.volume 0 1 := by
  have hcont : ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (Set.Icc (0:ℝ) 1) :=
    (deriv_realizedRicciChartSum_continuousOn (I := I) g₀ T T' hδ hδ' x v w).mono
      (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)
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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem realizedRicciPathValue_continuousOn_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.congr
    (f := realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) ?_ ?_
  · exact fun s hs =>
      (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ hδ' x v w
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem hasDerivAt_ricciTensor_realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem ricciTensor_realized_sub_eq_integral_linearizedRicci
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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

private local instance instCompleteSpaceE_keystone : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

open DifferentialGeometry.Integral.DivergenceTheorem in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem cometricRaiseSlot0Fib_metricPerturbationPath_jointContMDiffOn (s : ℕ)
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (Y : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 2) I p.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) p.1 (Y p))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) p.1
        (cometricRaiseSlot0Fib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
      cometricRaiseSlot0Fib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)))
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro β
  have hsharp := inverseMetricSharpField_metricPerturbationPath_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hβjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (β p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    have hβM : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x (β x)) := β.contMDiff
    exact (hβM.comp_contMDiffOn contMDiffOn_fst)
  have hsharpβ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1 (β p.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharp hβjoint
  set sharpβ : ∀ p : M × ℝ, TangentSpace I p.1 :=
    fun p => inverseMetricSharpFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1 (β p.1)
    with hsharpβdef
  have hraise := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := s + 1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) (X := sharpβ) hsharpβ (α := fun p => Y p) hY
  refine hraise.congr (fun p hp => ?_)
  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) p.1 (sharpβ p) (Y p)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
        cometricRaiseSlot0Fib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p))
          (β p.1))
  congr 1

open DifferentialGeometry.Integral.DivergenceTheorem in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn (p : ℕ)
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (Y : ∀ q : M × ℝ, Tensor0SBundle.Tensor0SSpace (p + 2) I q.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) q.1 (Y q))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) q.1
        (cometricDoubleTraceFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hraise := cometricRaiseSlot0Fib_metricPerturbationPath_jointContMDiffOn (I := I) (s := p) g₀ T T' hδ hδ'
    Y hY
  have htrace := contractTraceField_jointContMDiffOn (I := I) 0 p
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun q : M × ℝ => cometricRaiseSlot0Fib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' q.2) p q.1
      (Y q))
    hraise
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) q.1
        (DifferentialGeometry.Geometry.Connection.unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    ((DifferentialGeometry.Geometry.Connection.unitZeroSec (I := I)
      (M := M)).contMDiff.comp_contMDiffOn contMDiffOn_fst)
  have htraceUnit := ContMDiffOn.clm_bundle_apply (b := Prod.fst) htrace hunit
  refine htraceUnit.congr (fun q hq => ?_)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p
    (cometricLmodel (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' q.2) q.1)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y q))]
  rw [contract_trace_unitZero_toModel (I := I) p q.1
    (cometricRaiseSlot0Fib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q))]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem ricciDeTurckPrincipalCoefficientFiber_metricPerturbationPath_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        (ricciDeTurckPrincipalCoefficientAtPoint (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  let _ := (inferInstance : (BoundarylessManifold I M))
  classical
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciDeTurckPrincipalCoefficientAtPoint (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro Y
  set κ : Equiv.Perm (Fin 4) := koszulDoubleTraceSlotPerm with hκ
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with
                                                         hg_s
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hYκ := domDomCongrField_jointContMDiffOn (I := I) κ
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hT03 := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hYκ
  have hCDT := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Y p.1) hYjoint
  have hswap := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap (0 : Fin 2) 1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 4 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace
      2 I p.1 from
        cometricDoubleTraceFib (I := I) (g_s p.2) 2 p.1)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))))
    hT03
  have hcomb := jointTotalSpace_smul (I := I) (d := 2) (1 / 2 : ℝ) _
    (jointTotalSpace_sub (I := I) (d := 2) _ _
      (jointTotalSpace_add (I := I) (d := 2) _ _ hT03 hswap) hCDT)
  refine hcomb.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [ricciDeTurckPrincipalCoefficientFiber_toModel]
  simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [ricciPrincipalCoefficientDoubleTraceModel]
  rw [smul_apply, sub_apply,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciDeTurckPrincipalCoefficient_metricPerturbationPath_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((ricciDeTurckPrincipalCoefficient (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hfib := ricciDeTurckPrincipalCoefficientFiber_metricPerturbationPath_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  refine hfib.congr (fun p _ => ?_)
  rw [ricciDeTurckPrincipalCoefficient_toSection]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciDeTurckPrincipalCoefficient_metricPerturbationPath_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciDeTurckPrincipalCoefficient (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hjoint := ricciDeTurckPrincipalCoefficient_metricPerturbationPath_jointContMDiff
    (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
    (fun t => ricciDeTurckPrincipalCoefficient (I := I) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t)) (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hjoint x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricPerturbationPath_chartRicciTensor_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (α : M) (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartRicciTensor (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) α i k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hG := metricPerturbationPath_chartGramFamilyJointSmoothOn (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartRicciTensor_joint_contDiffAt (I := I)
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ') α hG i k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartRicciTensor (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' r.1) α i k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensorSection_chartComponent_metricPerturbationPath_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (Y : Cₛ^∞⟮I; E, (fun x : M => TangentSpace I x)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ricciTensor (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  classical
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ q : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α Y q p.1 *
          chartRicciTensor (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) α q j
            (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finsetSum (fun q _ => ?_)
    have hcoeff : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartCoeff (I := I) α Y q p.1)
        ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
      have hc := chartCoeff_contMDiffOn (I := I) α Y q
      rw [hbase_eq] at hc
      exact hc.comp contMDiffOn_fst (fun p hp => hp.1)
    exact hcoeff.mul
      (metricPerturbationPath_chartRicciTensor_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α q j)
  refine hsum.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hx
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx
  set gs := metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2 with hgs
  rw [chartCoeff_recompose (I := I) α Y hxbase]
  rw [map_sum (ricciTensor (I := I) gs p.1), sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_apply, smul_eq_mul,
    ricciTensor_chartBasisVec_alpha_eq (I := I) gs α q j hxgood]

open DifferentialGeometry.Integral.DivergenceTheorem in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricEndoRaisedFib_metricPerturbationPath_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (ricEndoRaisedFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => ricEndoRaisedFib (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro Y
  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun s b => (ricciTensor (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) b (Y b)).toLinearMap
    with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    fun α i j => metricPerturbationPath_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    intro α j
    have hbase := ricciTensorSection_chartComponent_metricPerturbationPath_jointContMDiffOn
      (I := I) g₀ T T' hδ hδ' Y α j
    refine hbase.congr (fun p _ => ?_)
    rw [hcvdef]
    rfl
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s => metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) (cv := cv)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) metricPerturbationPathDomain_isOpen hinv hcv
  refine hjoint.congr (fun p hp => ?_)
  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (DifferentialGeometry.Geometry.Operator.metricSharp
        (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (ricEndoRaisedFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
  rw [ricEndoRaisedFib_apply, hcvdef]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciOrderZeroCurvCoeffFibSlot0_metricPerturbationPath_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciOrderZeroCurvCoeffFibSlot (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) 0 p.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciOrderZeroCurvCoeffFibSlot (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) 0 p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro Y
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with
                                                         hg_s
  have hric := ricEndoRaisedFib_metricPerturbationPath_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have happ := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ => ricEndoRaisedFib (I := I) (g_s p.2) p.1) hric
    (A := fun p : M × ℝ => Y p.1) hYjoint
  refine happ.congr (fun p _ => ?_)
  rw [ricciOrderZeroCurvCoeffFibSlot]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciOrderZeroCurvCoeffFibSlot1_metricPerturbationPath_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciOrderZeroCurvCoeffFibSlot (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) 1 p.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciOrderZeroCurvCoeffFibSlot (I := I)
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) 1 p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
  intro Y
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => metricPerturbationPath (I := I) g₀ T T' hδ hδ' s with
                                                         hg_s
  have hric := ricEndoRaisedFib_metricPerturbationPath_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have happ := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ => ricEndoRaisedFib (I := I) (g_s p.2) p.1) hric
    (A := fun p : M × ℝ => Y p.1) hYjoint
  refine happ.congr (fun p _ => ?_)
  rw [ricciOrderZeroCurvCoeffFibSlot]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem ricciOrderZeroCurvCoeffFib_metricPerturbationPath_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciOrderZeroCurvCoeffFib (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) p.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hslot0 := ricciOrderZeroCurvCoeffFibSlot0_metricPerturbationPath_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  have hslot1 := ricciOrderZeroCurvCoeffFibSlot1_metricPerturbationPath_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add (I := I) (r := 2) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (ricciOrderZeroCurvCoeffFibSlot (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) 0 p.1))
    (B := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (ricciOrderZeroCurvCoeffFibSlot (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2) 1 p.1))
    hslot0 hslot1
  refine hadd.congr (fun p _ => ?_)
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciOrderZeroCurvCoeff_metricPerturbationPath_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((ricciOrderZeroCurvCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hfib := ricciOrderZeroCurvCoeffFib_metricPerturbationPath_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  refine hfib.congr (fun p _ => ?_)
  rw [ricciOrderZeroCurvCoeff_toSection]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciOrderZeroCurvCoeff_metricPerturbationPath_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciOrderZeroCurvCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hjoint := ricciOrderZeroCurvCoeff_metricPerturbationPath_jointContMDiff
    (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
    (fun t => ricciOrderZeroCurvCoeff (I := I) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t)) (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hjoint x

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
