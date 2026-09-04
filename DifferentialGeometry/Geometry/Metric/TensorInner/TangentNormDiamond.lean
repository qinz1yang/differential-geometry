import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentContinuousRiemannianMetric
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
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
theorem inner_eq_of_isMetricNorm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v w : TangentSpace I x) :
    (inner ℝ v w : ℝ) = g.inner x v w := by
  have hnonneg : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · exact (g.pos x z hz).le
  have hdiag : ∀ z : TangentSpace I x,
      (inner ℝ z z : ℝ) = g.inner x z z := by
    intro z
    have hnorm : ‖z‖ = Real.sqrt (g.inner x z z) := by
      have hz := hEnorm x z
      rw [← ofReal_norm] at hz
      exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg z) (Real.sqrt_nonneg _)).mp hz
    rw [real_inner_self_eq_norm_sq, hnorm, Real.sq_sqrt (hnonneg z)]
  have hinner : (inner ℝ v w : ℝ) =
      ((inner ℝ (v + w) (v + w) : ℝ) - inner ℝ v v - inner ℝ w w) / 2 := by
    rw [real_inner_add_add_self]
    ring
  have hginner : g.inner x v w =
      (g.inner x (v + w) (v + w) - g.inner x v v - g.inner x w w) / 2 := by
    have hadd : g.inner x (v + w) (v + w) =
        g.inner x v v + g.inner x v w + g.inner x w v + g.inner x w w := by
      simp [map_add, add_apply]
      ring
    rw [hadd, g.symm x w v]
    ring
  rw [hinner, hginner, hdiag (v + w), hdiag v, hdiag w]

end MetricNorm

end DifferentialGeometry.Geometry.Riemannian

end
