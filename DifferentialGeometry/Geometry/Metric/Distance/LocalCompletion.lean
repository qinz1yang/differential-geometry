import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

theorem exists_riemannianMetricComplete_eqOn_ball
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y) (p : M) :
    ∃ (g' : SmoothRiemannianMetric I M) (r : ℝ) (U : Set M),
      0 < r ∧ RiemannianMetricComplete g' ∧ IsOpen U ∧
      Metric.closedBall p (4 * r) ⊆ U ∧
      (∀ z ∈ U, g'.inner z = g.inner z) ∧
      (∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) ∧
      ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        riemannianEDistOf g' x y = ENNReal.ofReal (dist x y) := by
  obtain ⟨g', U, hcomplete, hU, hpU, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g (isCompact_singleton (x := p))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hpU (mem_singleton p)))
  let r := R / 8
  have hr : 0 < r := by positivity
  have hKU : Metric.closedBall p (4 * r) ⊆ U := by
    intro z hz
    apply hball
    change dist z p < R
    have hd : dist z p ≤ 4 * r := hz
    dsimp only [r] at hd
    linarith only [hd, hR]
  have hdist (x y : M) : riemannianEDistOf g x y = ENNReal.ofReal (dist x y) :=
    (hmetric x y).symm.trans (edist_dist x y)
  refine ⟨g', r, U, hr, hcomplete, hU, hKU, heq, hle, ?_⟩
  intro x hx y hy
  have hxp : dist x p < r := hx
  have hyp : dist y p < r := hy
  have hxy : dist x y < 2 * r := by
    have htri := dist_triangle x p y
    rw [dist_comm p y] at htri
    linarith only [htri, hxp, hyp]
  have hbuffer : {z : M | riemannianEDistOf g x z ≤ ENNReal.ofReal (2 * r)} ⊆ U := by
    intro z hz
    apply hKU
    change dist z p ≤ 4 * r
    change riemannianEDistOf g x z ≤ ENNReal.ofReal (2 * r) at hz
    rw [hdist] at hz
    have hxz : dist x z ≤ 2 * r :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hz
    have htri := dist_triangle z x p
    rw [dist_comm z x] at htri
    linarith only [htri, hxz, hxp, hr]
  have hyshort : riemannianEDistOf g x y < ENNReal.ofReal (2 * r) := by
    rw [hdist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hxy
  exact (riemannianEDistOf_eq_of_eqOn_ball g g' hbuffer heq hle hyshort).trans (hdist x y)

end DifferentialGeometry.Geometry
