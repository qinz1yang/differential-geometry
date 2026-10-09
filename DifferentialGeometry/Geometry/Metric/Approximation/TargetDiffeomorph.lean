import DifferentialGeometry.Geometry.Metric.Approximation.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.TargetDiffeomorph

open scoped Manifold ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [T2Space P]

theorem metricCkErrorOn_transDiffeomorph
    (Φ : PartialDiffeomorph I I M N ∞) (e : N ≃ₘ⟮I, I⟯ P)
    (K : Set M) (p : ℕ) (g : SmoothRiemannianMetric I M) (k : SmoothRiemannianMetric I P) :
    metricCkErrorOn (transDiffeomorph Φ e) K p g k =
      metricCkErrorOn Φ K p g (Diffeomorph.pullbackMetric k e) := by
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  change CheegerGromovCompactness.metricCkENormOn (Subtype.val ⁻¹' K) p
      (pullbackMetricOn (transDiffeomorph Φ e) U Set.Subset.rfl k)
      (g.restrictOpen U) (g.restrictOpen U) = _
  rw [pullbackMetricOn_transDiffeomorph]
  rfl

theorem isMetricApproximationOn_transDiffeomorph_iff
    (Φ : PartialDiffeomorph I I M N ∞) (e : N ≃ₘ⟮I, I⟯ P)
    (K : Set M) (p : ℕ) (ε : ℝ) (g : SmoothRiemannianMetric I M)
    (k : SmoothRiemannianMetric I P) :
    isMetricApproximationOn (transDiffeomorph Φ e) K p ε g k ↔
      isMetricApproximationOn Φ K p ε g (Diffeomorph.pullbackMetric k e) := by
  unfold isMetricApproximationOn
  rw [metricCkErrorOn_transDiffeomorph]
  rfl

end DifferentialGeometry.PartialDiffeomorph
