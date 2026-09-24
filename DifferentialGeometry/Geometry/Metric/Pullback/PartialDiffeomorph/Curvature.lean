import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Basic
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Set TopologicalSpace
open Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace PartialDiffeomorph

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem metricScalarAt_pullbackMetricOn
    (Φ : PartialDiffeomorph I I M N ∞) (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (g : SmoothRiemannianMetric I N) (x : U) :
    metricScalarAt (I := I) (PartialDiffeomorph.pullbackMetricOn Φ U hU g) x =
      metricScalarAt (I := I) g (Φ x) := by
  have hloc : IsLocalDiffeomorph I I ∞ (fun x : U => Φ (x : M)) := by
    intro x
    exact IsLocalDiffeomorphAt.comp I N
      (isLocalDiffeomorph_subtype_val U x) (Φ.isLocalDiffeomorphAt I I ∞ (hU x.2))
  have heq : PartialDiffeomorph.pullbackMetricOn Φ U hU g = localPullMetric g (fun x : U => Φ (x : M)) hloc := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [pullbackMetricOn_inner, localPullMetric_inner]
    have hcomp := mfderiv_comp_apply x
      ((Φ.isLocalDiffeomorphAt I I ∞ (hU x.2)).mdifferentiableAt (by simp))
      ((isLocalDiffeomorph_subtype_val U x).mdifferentiableAt (by simp))
    simp only [mfderiv_subtype_val_apply] at hcomp
    exact congrArg₂ (fun v w => g.inner (Φ (x : M)) v w) (hcomp v).symm (hcomp w).symm
  rw [heq, metricScalarAt_localPull]

end PartialDiffeomorph

end DifferentialGeometry
