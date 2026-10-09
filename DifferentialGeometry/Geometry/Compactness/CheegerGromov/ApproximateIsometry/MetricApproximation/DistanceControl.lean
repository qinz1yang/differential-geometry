import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import DifferentialGeometry.Geometry.Metric.Comparison.BallImage

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

section BallImage

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [SigmaCompactSpace M] in
theorem MapMetricApproximationOn.image_eball_subset_closedEBall
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [PseudoEMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace I y)]
    [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {O : M} {r r₂ ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hhnorm : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y w w)))
    (hrr₂ : r ≤ r₂) (hε0 : 0 ≤ ε)
    (hdata : MapMetricApproximationOn (I := I)
      (Metric.closedEBall O (ENNReal.ofReal r₂)) ε p (Φ : M → N) g h)
    (hsub : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ Φ.source) :
    (Φ : M → N) '' Metric.eball O (ENNReal.ofReal r) ⊆
      Metric.closedEBall ((Φ : M → N) O)
        (ENNReal.ofReal (Real.sqrt (1 + ε) * r)) := by
  apply DifferentialGeometry.PartialDiffeomorph.image_eball_subset_closedEBall_of_quad_le
    (C := 1 + ε) Φ (by exact_mod_cast le_top) hgnorm hhnorm hrr₂ (by linarith) hsub
  intro x hx v
  have hpull : h.inner ((Φ : M → N) x)
      (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x v) =
      hdata.pullback x (fun _ => v) := by
    rw [hdata.pullback_apply x hx (fun _ => v)]
  rw [hpull]
  exact (tensor_apply_bounds_of_metricTensorErrorNorm_le (I := I) hdata.pullback g
    (hdata.c0_small x hx) v).2

end BallImage

end CheegerGromovCompactness
end DifferentialGeometry
