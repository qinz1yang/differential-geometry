import DifferentialGeometry.Geometry.Metric.DirectLimit.Defs
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Set TopologicalSpace
open Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace SmoothSeqSystem

variable {A : ℕ → Type*} [∀ j, TopologicalSpace (A j)] [∀ j, ChartedSpace H (A j)]
  [∀ j, IsManifold I ∞ (A j)] [∀ j, T2Space (A j)] [∀ j, Nonempty (A j)]

theorem metricScalarAt_limitMetric_incl
    (S : SmoothSeqSystem I A) (gInf : ∀ j, SmoothRiemannianMetric I (A j))
    (hg : S.MetricCocycle gInf) (j : ℕ) (a : A j) :
    metricScalarAt (I := I) (S.limitMetric gInf hg) (S.toSeqSystem.incl j a) =
      metricScalarAt (I := I) (gInf j) a := by
  have hloc : IsLocalDiffeomorph I I ∞ (S.toSeqSystem.incl j) := fun a =>
    (S.inclPartialDiffeo j).symm.isLocalDiffeomorphAt I I ∞ (show a ∈ Set.univ from mem_univ a)
  have heq : gInf j = localPullMetric (S.limitMetric gInf hg) (S.toSeqSystem.incl j) hloc := by
    apply SmoothRiemannianMetric.ext_inner
    intro a v w
    rw [localPullMetric_inner, S.limitMetric_pullback]
  rw [heq, metricScalarAt_localPull]

end SmoothSeqSystem

end DifferentialGeometry
