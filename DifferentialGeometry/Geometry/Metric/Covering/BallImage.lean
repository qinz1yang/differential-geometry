import DifferentialGeometry.Geometry.Metric.Quotient
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Distance.Ball

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem image_riemannianBallOf_of_coveringMap_localPullMetric
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {p : M → N} (hp : IsLocalDiffeomorph I J ∞ p) (hcover : IsCoveringMap p)
    (hpull : localPullMetric h p hp = g) (x : M) (r : ℝ) :
    p '' riemannianBallOf g x r = riemannianBallOf h (p x) r := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    have hd := edistOf_le_of_quad_of_localDiffeomorph g h p hp (c := 1) zero_lt_one
      (fun z v => by rw [one_mul, ← hpull, localPullMetric_inner]) x z
    simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hd
    exact hd.trans_lt hz
  · intro y hy
    by_contra hnot
    have hlower (z : M) (hz : p z = y) :
        ENNReal.ofReal r ≤ riemannianEDistOf g x z := by
      by_contra hlt
      exact hnot ⟨z, lt_of_not_ge hlt, hz⟩
    exact (not_lt_of_ge
      (le_edistOf_of_coveringMap_localPullMetric g h hp hcover hpull x y hlower)) hy

end DifferentialGeometry.Geometry.Metric
