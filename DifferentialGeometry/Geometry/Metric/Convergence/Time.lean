import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metric_cp_convergence_at_tendsto_time
    (K : Set M) (p : ℕ) (J : Set ℝ)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M)
    (G : ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    (time : ℕ → ℝ) {s L : ℝ}
    (htime : ∀ n, time n ∈ J) (hlim : Tendsto time atTop (𝓝 s))
    (hconv : ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N,
      ∀ t ∈ J, ∀ j ≤ p, ∀ x ∈ K, metricDerivNorm j (g n t) (G t) R x < epsilon)
    (hcontinuous : ∀ t ∈ J, ∀ j ≤ p, ∀ x ∈ K,
      metricDerivNorm j (G t) (G s) R x ≤ L * |t - s|) :
    MetricCPConvergenceOn K p (fun n => g n (time n)) (G s) R := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hconv (epsilon / 3) (by positivity)
  have hzero : Tendsto (fun n => L * |time n - s|) atTop (𝓝 0) := by
    simpa using (hlim.sub_const s).abs.const_mul L
  obtain ⟨N', hN'⟩ := eventually_atTop.mp
    (hzero.eventually (Iio_mem_nhds (show (0 : ℝ) < epsilon / 3 by positivity)))
  refine ⟨max N N', fun n hn => ?_⟩
  apply lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall K p (g n (time n)) (G s) R
      (2 * epsilon / 3) (by positivity) ?_) (by linarith)
  intro j hj x hx
  have hg := hN n ((le_max_left _ _).trans hn) (time n) (htime n) j hj x hx
  have hG := (hcontinuous (time n) (htime n) j hj x hx).trans_lt
    (hN' n ((le_max_right _ _).trans hn))
  have htri := metricDerivNorm_triangle j (g n (time n)) (G (time n)) (G s) R x
  linarith

end DifferentialGeometry.CheegerGromovCompactness
