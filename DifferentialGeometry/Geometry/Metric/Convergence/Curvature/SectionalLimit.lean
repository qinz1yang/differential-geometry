import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.TensorConvergence
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem sectionalBoundedBelow_of_tendsto [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (K : ℕ → ℝ) (K0 : ℝ) (hK : Tendsto K atTop (𝓝 K0))
    (hconv : MetricCPConvergenceOn (I := I) Set.univ 2 gSeq h h)
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (K n)) :
    SectionalBoundedBelow h K0 := by
  intro x v w
  have hinner (a b : TangentSpace I x) :
      Tendsto (fun n => (gSeq n).inner x a b) atTop (𝓝 (h.inner x a b)) :=
    hconv.tendsto_inner isCompact_univ (mem_univ x) a b
  have hgram : Tendsto
      (fun n => K n * ((gSeq n).inner x v v * (gSeq n).inner x w w - (gSeq n).inner x v w ^ 2))
      atTop (𝓝 (K0 * (h.inner x v v * h.inner x w w - h.inner x v w ^ 2))) :=
    hK.mul (((hinner v v).mul (hinner w w)).sub ((hinner v w).pow 2))
  have hrm := hconv.tendsto_metricRm04StandardAt isCompact_univ (mem_univ x) v w w v
  exact le_of_tendsto_of_tendsto' hgram hrm (fun n => hsec n x v w)

theorem sectional_nonneg_of_error_tending_zero [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (ε : ℕ → ℝ) (hεlim : Tendsto ε atTop (𝓝 0))
    (hconv : MetricCPConvergenceOn (I := I) Set.univ 2 gSeq h h)
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (-ε n)) :
    SectionalBoundedBelow h 0 := by
  have hK : Tendsto (fun n => -ε n) atTop (𝓝 0) := by
    simpa using hεlim.neg
  exact sectionalBoundedBelow_of_tendsto h gSeq (fun n => -ε n) 0 hK hconv hsec

theorem sectional_nonneg_of_metricCInfConvergenceOnCompacts [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (ε : ℕ → ℝ) (hεlim : Tendsto ε atTop (𝓝 0))
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq h h)
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (-ε n)) :
    SectionalBoundedBelow h 0 :=
  sectional_nonneg_of_error_tending_zero h gSeq ε hεlim (hconv Set.univ isCompact_univ 2) hsec

end DifferentialGeometry.CheegerGromovCompactness

end
