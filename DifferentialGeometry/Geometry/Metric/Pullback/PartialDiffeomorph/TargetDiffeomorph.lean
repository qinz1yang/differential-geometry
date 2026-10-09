import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas

open scoped Manifold ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [T2Space P]

theorem pullbackMetricOn_transDiffeomorph
    (Φ : PartialDiffeomorph I I M N ∞) (e : N ≃ₘ⟮I, I⟯ P)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (k : SmoothRiemannianMetric I P) :
    pullbackMetricOn (transDiffeomorph Φ e) U hU k =
      pullbackMetricOn Φ U hU (Diffeomorph.pullbackMetric k e) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [pullbackMetricOn_inner (transDiffeomorph Φ e) U hU k,
    pullbackMetricOn_inner Φ U hU (Diffeomorph.pullbackMetric k e),
    Diffeomorph.pullbackMetric_inner]
  have hΦ : MDifferentiableAt I I (Φ : M → N) (x : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hU x.property))).mdifferentiableAt
      (by simp)
  have he : MDifferentiableAt I I (e : N → P) (Φ x) := e.contMDiff.mdifferentiableAt (by simp)
  change k.inner (e (Φ x))
      (mfderiv I I ((e : N → P) ∘ (Φ : M → N)) (x : M) v)
      (mfderiv I I ((e : N → P) ∘ (Φ : M → N)) (x : M) w) = _
  rw [mfderiv_comp (x : M) he hΦ]
  rfl

end DifferentialGeometry.PartialDiffeomorph
