import DifferentialGeometry.Geometry.Metric.Family.TensorNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.MetricDifference

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuous_metricDiffSq_family
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x)) :
    Continuous (fun q : K × M => metricDiffSq (g₁ q.1.1) (g₂ q.1.1) q.2) := by
  apply continuous_normSq0S_family g₁ (fun t x => metricDiffAt (g₁ t) (g₂ t) x) hg₁
  convert hg₁.add (hg₂.const_smul (-1)) using 1
  simp only [metricDiffAt, neg_one_smul, sub_eq_add_neg]

theorem continuousOn_metricDiffSq_family
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x))
    (x : M) : ContinuousOn (fun t => metricDiffSq (g₁ t) (g₂ t) x) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hpair : Continuous (fun t : K => (t, x)) := continuous_id.prodMk continuous_const
  have hc : Continuous (fun q : K × M => metricDiffSq (g₁ q.1.1) (g₂ q.1.1) q.2) :=
    continuous_metricDiffSq_family (I := I) g₁ g₂ hg₁ hg₂
  exact Continuous.comp (f := fun t : K => (t, x))
    (g := fun q : K × M => metricDiffSq (g₁ q.1.1) (g₂ q.1.1) q.2) hc hpair

theorem tendsto_metricDiffSq_of_metricTensor_continuous
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x))
    {a : ℝ} (ha : a ∈ K) (hinit : g₁ a = g₂ a) (x : M) :
    Tendsto (fun t => metricDiffSq (g₁ t) (g₂ t) x) (𝓝[K] a) (𝓝 0) := by
  have h := (continuousOn_metricDiffSq_family g₁ g₂ hg₁ hg₂ x) a ha
  have hz : metricDiffSq (g₁ a) (g₂ a) x = 0 := by
    rw [hinit, metricDiffSq, metricDiffAt_self]
    exact (normSq0S_eq_zero_iff (g₂ a) x 2 0).2 rfl
  exact hz ▸ h

end DifferentialGeometry.PDE.RicciFlow
