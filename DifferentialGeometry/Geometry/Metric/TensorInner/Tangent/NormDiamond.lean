import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.ContinuousRiemannianMetric
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Basic


noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem tensor0SBundle_enorm_eq_riemannianBundle_enorm
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  have hinner : (inner ℝ v v : ℝ) = g.inner x v v := rfl
  rw [hinner]

section MetricNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
def IsMetricNorm (g : SmoothRiemannianMetric I M)
    [RiemannianBundle (fun (x : M) => TangentSpace I x)] : Prop :=
  ∀ (x : M) (w : TangentSpace I x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem isMetricNorm_of_riemannianBundle (g : SmoothRiemannianMetric I M) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    IsMetricNorm (I := I) (M := M) g :=
  fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem IsMetricNorm.inner_eq
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    (x : M) (v w : TangentSpace I x) : inner ℝ v w = g.inner x v w := by
  have hdiag (z : TangentSpace I x) : inner ℝ z z = g.inner x z z := by
    have hn : ‖z‖ = Real.sqrt (g.inner x z z) := by
      have h := hEnorm x z
      rw [← ofReal_norm] at h
      have ht := congrArg ENNReal.toReal h
      simpa only [ENNReal.toReal_ofReal (norm_nonneg z),
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using ht
    rw [real_inner_self_eq_norm_sq, hn,
      Real.sq_sqrt (metric_inner_self_nonneg (I := I) g x z)]
  have h := hdiag (v + w)
  simp only [inner_add_left, inner_add_right, map_add, add_apply] at h
  rw [hdiag v, hdiag w, g.symm x w v] at h
  linarith [real_inner_comm v w]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem IsMetricNorm.isContinuousRiemannianBundle
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g) :
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
  ⟨g.inner, g.contMDiff.continuous, hEnorm.inner_eq⟩

end MetricNorm

end DifferentialGeometry.Geometry.Riemannian

end
