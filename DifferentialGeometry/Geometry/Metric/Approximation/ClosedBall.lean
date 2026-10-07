import DifferentialGeometry.Geometry.Metric.Approximation.Locality
import DifferentialGeometry.Geometry.Metric.Distance.Closure
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false

namespace DifferentialGeometry.PartialDiffeomorph

open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem metricCkErrorOn_congr_of_eqOn_riemannianBallOf
    (Φ Ψ : PartialDiffeomorph I I M N ∞)
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (h : SmoothRiemannianMetric I N) (x : M) {r : ℝ} (hr : 0 < r)
    (hΦ : riemannianClosedBallOf g x r ⊆ Φ.source)
    (hΨ : riemannianClosedBallOf g x r ⊆ Ψ.source)
    (heq : Set.EqOn (Φ : M → N) (Ψ : M → N) (riemannianBallOf g x r)) (p : ℕ) :
    metricCkErrorOn Φ (riemannianClosedBallOf g x r) p g h =
      metricCkErrorOn Ψ (riemannianClosedBallOf g x r) p g h := by
  let U : TopologicalSpace.Opens M :=
    ⟨riemannianBallOf g x r,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g x) continuous_const⟩
  have hcl : closure (U : Set M) = riemannianClosedBallOf g x r :=
    closure_riemannianBallOf g hg x hr
  have hleft : closure (U : Set M) ⊆ Φ.source := by rwa [hcl]
  have hright : closure (U : Set M) ⊆ Ψ.source := by rwa [hcl]
  simpa only [hcl] using metricCkErrorOn_congr_of_eqOn_open Φ Ψ U hleft hright heq p g h

theorem isMetricApproximationOn_congr_of_eqOn_riemannianBallOf
    (Φ Ψ : PartialDiffeomorph I I M N ∞)
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (h : SmoothRiemannianMetric I N) (x : M) {r : ℝ} (hr : 0 < r)
    (hΦ : riemannianClosedBallOf g x r ⊆ Φ.source)
    (hΨ : riemannianClosedBallOf g x r ⊆ Ψ.source)
    (heq : Set.EqOn (Φ : M → N) (Ψ : M → N) (riemannianBallOf g x r))
    (p : ℕ) (ε : ℝ) :
    isMetricApproximationOn Φ (riemannianClosedBallOf g x r) p ε g h ↔
      isMetricApproximationOn Ψ (riemannianClosedBallOf g x r) p ε g h := by
  simp only [isMetricApproximationOn, hΦ, hΨ, true_and,
    metricCkErrorOn_congr_of_eqOn_riemannianBallOf Φ Ψ g hg h x hr hΦ hΨ heq p]

end DifferentialGeometry.PartialDiffeomorph
