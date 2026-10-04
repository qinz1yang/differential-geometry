import DifferentialGeometry.Geometry.Metric.ChartLipschitz.DistanceComparison

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_centered_ambient_bilipschitz_ball_chart
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y, riemannianEDistOf g x y = ENNReal.ofReal (dist x y))
    (p : M) {K : ℝ} (hK : 1 < K) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ φ : Metric.ball p r → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
        φ ⟨p, Metric.mem_ball_self hr⟩ = 0 ∧
        Function.Injective φ ∧
        (∀ x y, K⁻¹ * dist x y ≤ dist (φ x) (φ y)) ∧
        (∀ x y, dist (φ x) (φ y) ≤ K * dist x y) ∧
        ∀ x, φ x = metricChartEuclideanEquiv g p (extChartAt I p x) -
          metricChartEuclideanEquiv g p (extChartAt I p p) := by
  obtain ⟨U, hpU, _, hcomp⟩ := exists_open_riemannianEDistOf_comparison g p hK
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds hpU)
  let A := metricChartEuclideanEquiv g p
  let φ : Metric.ball p r → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun x => A (extChartAt I p x) - A (extChartAt I p p)
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hdist (x y : Metric.ball p r) :
      dist (φ x) (φ y) ≤ K * dist x y ∧ dist x y ≤ K * dist (φ x) (φ y) := by
    have h : edist (A (extChartAt I p x.val)) (A (extChartAt I p y.val)) ≤
          ENNReal.ofReal K * riemannianEDistOf g x.val y.val ∧
        riemannianEDistOf g x.val y.val ≤ ENNReal.ofReal K *
          edist (A (extChartAt I p x.val)) (A (extChartAt I p y.val)) := by
      simpa only [A, edist_metricChartEuclideanEquiv] using
        hcomp x.val (hsub x.property) y.val (hsub y.property)
    simp only [hmetric, edist_dist,
      ← ENNReal.ofReal_mul hKpos.le,
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le dist_nonneg)] at h
    simpa only [φ, dist_sub_right, Subtype.dist_eq] using h
  refine ⟨r, hr, φ, sub_self _, ?_, ?_, fun x y => (hdist x y).1, fun _ => rfl⟩
  · intro x y hxy
    apply dist_eq_zero.mp
    have h := (hdist x y).2
    rw [hxy, dist_self, mul_zero] at h
    exact le_antisymm h dist_nonneg
  · intro x y
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hKpos).mpr (by simpa only [mul_comm] using (hdist x y).2)

theorem exists_centered_ambient_two_bilipschitz_ball_chart
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y, riemannianEDistOf g x y = ENNReal.ofReal (dist x y))
    (p : M) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ φ : Metric.ball p r → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
        φ ⟨p, Metric.mem_ball_self hr⟩ = 0 ∧
        Function.Injective φ ∧
        (∀ x y, (2 : ℝ)⁻¹ * dist x y ≤ dist (φ x) (φ y)) ∧
        (∀ x y, dist (φ x) (φ y) ≤ 2 * dist x y) ∧
        ∀ x, φ x = metricChartEuclideanEquiv g p (extChartAt I p x) -
          metricChartEuclideanEquiv g p (extChartAt I p p) :=
  exists_centered_ambient_bilipschitz_ball_chart g hmetric p (by norm_num)

end DifferentialGeometry.Geometry.Metric
