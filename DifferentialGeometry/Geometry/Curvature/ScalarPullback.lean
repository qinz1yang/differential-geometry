import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold J N]

theorem metricScalarAt_pullback_scaleMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (c : ℝ) (hc : 0 < c) (x : M) :
    metricScalarAt (Diffeomorph.pullbackMetricCross (scaleMetric c hc g) Φ) x =
      metricScalarAt g (Φ x) / c := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F := e.toLinearEquiv.finrank_eq
  let : NeZero (Module.finrank ℝ F) := ⟨by rw [← hdim]; exact NeZero.ne _⟩
  rw [metricScalar_cross, metricScalarAt_scaleMetric, div_eq_mul_inv, mul_comm]

theorem metricScalarAt_pullback_scaleMetric_restrictOpenCross [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric J N) (V : TopologicalSpace.Opens N)
    (Φ : M ≃ₘ⟮I, J⟯ V) (c : ℝ) (hc : 0 < c) (x : M) :
    metricScalarAt
        (Diffeomorph.pullbackMetricCross (scaleMetric c hc (g.restrictOpen V)) Φ) x =
      metricScalarAt g (Φ x : N) / c := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hrange : Set.range Φ = Set.univ := Φ.surjective.range_eq
  let : SigmaCompactSpace V := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range Φ.continuous)
  rw [metricScalarAt_pullback_scaleMetricCross, metricScalarAt_restrictOpen]

end DifferentialGeometry.Geometry.Curvature
