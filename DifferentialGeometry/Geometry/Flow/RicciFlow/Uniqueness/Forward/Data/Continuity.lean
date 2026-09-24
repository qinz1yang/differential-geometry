import DifferentialGeometry.Geometry.Curvature.Metric.Relowering
import DifferentialGeometry.Geometry.Metric.Family.TensorNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.DifferenceFields
import DifferentialGeometry.Geometry.Metric.Family.MetricDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Basic

noncomputable section
open Bundle Filter Set
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem continuous_tensor_eval_time
    {s : ℕ} {K : Set ℝ}
    (A : (t : ℝ) → (x : M) → Tensor0SSpace s I x)
    (hA : tensor0SFamilyContinuousOnSet s K A)
    (x : M) (v : Fin s → TangentSpace I x) :
    Continuous (fun t : K => A t x v) := by
  exact hA.eval_continuous continuous_subtype_val (fun t => t.2) continuous_const
    (fun _ => continuous_const)

private theorem continuous_metric_inner_time
    {K : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g t) x))
    (x : M) (v w : TangentSpace I x) :
    Continuous (fun t : K => (g t).inner x v w) := by
  simpa only [metricTensorField_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using
    continuous_tensor_eval_time (fun t x => metricTensorField (g t) x) hg x ![v, w]

private theorem continuous_chartInvGram_time
    {K : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g t) x))
    (x : M) :
    Continuous (fun t : K => chartInvGramMatrix (g t) x x) := by
  let G : K → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun t => chartGramMatrix (g t) x x
  have hG : Continuous G := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_metric_inner_time g hg x
      (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)
  have hd : ∀ t : K, (G t).det ≠ 0 := by
    intro t
    exact ne_of_gt (chartGramMatrix_det_pos (g t) x
      (mem_baseSet_trivializationAt E (TangentSpace I) x))
  have hi : Continuous (fun t : K => ((G t).det)⁻¹ • (G t).adjugate) :=
    (hG.matrix_det.inv₀ hd).smul hG.matrix_adjugate
  simpa only [chartInvGramMatrix, Matrix.inv_def, Ring.inverse_eq_inv] using hi

private theorem continuous_normSq0S_time
    {s : ℕ} {K : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g t) x))
    (x : M) (A : ℝ → Tensor0SSpace s I x)
    (hA : ∀ v : Fin s → TangentSpace I x, Continuous (fun t : K => A t v)) :
    Continuous (fun t : K => normSq0S (g t) x s (A t)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  apply tendsto_normSq0S_of_chart_components
    (fun t : K => g t) (g t₀) x (fun t : K => A t) (A t₀)
  · intro i j
    exact (continuous_metric_inner_time g hg x
      (chartBasisVecFiber (I := I) x i x)
      (chartBasisVecFiber (I := I) x j x)).continuousAt
  · intro slots
    exact (hA _).continuousAt

theorem continuous_rmDiffSq_time
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x))
    (hR₁ : tensor0SFamilyContinuousOnSet 4 K (fun t x => metricRm04At (g₁ t) x))
    (hR₂ : tensor0SFamilyContinuousOnSet 4 K (fun t x => metricRm04At (g₂ t) x))
    (x : M) :
    Continuous (fun t : K => rmDiffSq (g₁ t) (g₂ t) x) := by
  classical
  change Continuous (fun t : K =>
    normSq0S (g₁ t) x 4 (rmDiffLowAt (g₁ t) (g₂ t) x))
  refine continuous_normSq0S_time g₁ hg₁ x
    (fun t => rmDiffLowAt (g₁ t) (g₂ t) x) ?_
  intro v
  let hx := mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := chartBasisFamily (I := I) x hx
  have hcross : Continuous (fun t : K =>
      CovariantDerivative.riemannCurvature04At (g₁ t) (metricCov (g₂ t))
        (metricCov_smooth (g₂ t)) x v) := by
    have heq (t : K) := riemannCurvature04At_eq_sum_metricRm04At (g₁ t) (g₂ t) b
      (chartInvGramMatrix (g₂ t) x x) (chartInvGram_inverse (g₂ t) x hx) v
    simp_rw [heq]
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_chartInvGram_time g₂ hg₂ x))).mul
        ((continuous_tensor_eval_time (fun t x => metricRm04At (g₂ t) x) hR₂ x _).mul
          (continuous_metric_inner_time g₁ hg₁ x _ _)))
  exact ((continuous_tensor_eval_time
    (fun t x => metricRm04At (g₁ t) x) hR₁ x v).sub hcross).congr
      (fun t => (rmDiffLowAt_apply (g₁ t) (g₂ t) x v).symm)

theorem tendsto_rmDiffSq_of_metricTensor_continuous
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x))
    (hR₁ : tensor0SFamilyContinuousOnSet 4 K (fun t x => metricRm04At (g₁ t) x))
    (hR₂ : tensor0SFamilyContinuousOnSet 4 K (fun t x => metricRm04At (g₂ t) x))
    {a : ℝ} (ha : a ∈ K) (hinit : g₁ a = g₂ a) (x : M) :
    Tendsto (fun t => rmDiffSq (g₁ t) (g₂ t) x) (𝓝[K] a) (𝓝 0) := by
  have hc : ContinuousOn (fun t => rmDiffSq (g₁ t) (g₂ t) x) K :=
    continuousOn_iff_continuous_domRestrict.mpr
      (continuous_rmDiffSq_time g₁ g₂ hg₁ hg₂ hR₁ hR₂ x)
  have hzero : rmDiffSq (g₁ a) (g₂ a) x = 0 := by
    rw [hinit, rmDiffSq_def, rmDiffLowAt_self]
    exact (normSq0S_eq_zero_iff (g₂ a) x 4 0).2 rfl
  rw [← hzero]
  exact hc a ha

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

theorem tendsto_forwardUniqueDensity_zero_of_connectionDifferenceSq_tendsto
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a b : ℝ} (hab : a < b)
    (hcarrier₁ : Icc a b ⊆ D₁.carrier) (hcarrier₂ : Icc a b ⊆ D₂.carrier)
    (hinit : S₁.base.metric a = S₂.base.metric a) (x : M)
    (hconn : Tendsto
      (fun t => connectionDifferenceSq (S₁.base.metric t) (S₂.base.metric t) x)
      (𝓝[Ioo a b] a) (𝓝 0)) :
    Tendsto (fun t => forwardUniqueDensity S₁.base.metric S₂.base.metric t x)
      (𝓝[Ioo a b] a) (𝓝 0) := by
  have hg₁ : tensor0SFamilyContinuousOnSet 2 (Icc a b)
      (fun t y => metricTensorField (S₁.base.metric t) y) :=
    hS₁.smoothMetric.metricTensor_cont.mono hcarrier₁
  have hg₂ : tensor0SFamilyContinuousOnSet 2 (Icc a b)
      (fun t y => metricTensorField (S₂.base.metric t) y) :=
    hS₂.smoothMetric.metricTensor_cont.mono hcarrier₂
  have hmetric := tendsto_metricDiffSq_of_metricTensor_continuous
    S₁.base.metric S₂.base.metric hg₁ hg₂ (left_mem_Icc.mpr hab.le) hinit x
  have hmetric' := hmetric.mono_left (nhdsWithin_mono a Ioo_subset_Icc_self)
  have hrm₁ : tensor0SFamilyContinuousOnSet 4 (Icc a b)
      (fun t y => metricRm04At (S₁.base.metric t) y) :=
    hS₁.rm04Cont.mono hcarrier₁
  have hrm₂ : tensor0SFamilyContinuousOnSet 4 (Icc a b)
      (fun t y => metricRm04At (S₂.base.metric t) y) :=
    hS₂.rm04Cont.mono hcarrier₂
  have hcurv := tendsto_rmDiffSq_of_metricTensor_continuous
    S₁.base.metric S₂.base.metric hg₁ hg₂ hrm₁ hrm₂
    (left_mem_Icc.mpr hab.le) hinit x
  have hcurv' := hcurv.mono_left (nhdsWithin_mono a Ioo_subset_Icc_self)
  simpa only [forwardUniqueDensity, zero_add] using (hmetric'.add hconn).add hcurv'

end DifferentialGeometry.PDE.RicciFlow

end
