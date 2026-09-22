import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallPairTransport
import DifferentialGeometry.Topology.Manifold.BallChartAffine

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_disjoint_ballCharts_in_chart_ball {M : ClosedOrientedManifold.{u} 3}
    (e : OrientedBallChart M) :
    ∃ c d : OrientedBallChart M,
      Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2) ∧
      c.chart '' Metric.closedBall 0 2 ⊆ e.chart '' Metric.ball 0 1 ∧
      d.chart '' Metric.closedBall 0 2 ⊆ e.chart '' Metric.ball 0 1 := by
  let s : E3 := (1 / 2 : ℝ) • EuclideanSpace.single 0 1
  have hs : ‖s‖ = 1 / 2 := by simp [s, norm_smul]
  have hzero : ‖(0 : E3)‖ + 2 * (1 / 16 : ℝ) ≤ 2 := by norm_num
  have hshift : ‖s‖ + 2 * (1 / 16 : ℝ) ≤ 2 := by rw [hs]; norm_num
  let c := e.affine 0 (1 / 16) (by norm_num) hzero
  let d := e.affine s (1 / 16) (by norm_num) hshift
  have hnorm (x : E3) : ‖(1 / 16 : ℝ) • x‖ = (1 / 16) * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  have hc (x : E3) (hx : x ∈ Metric.closedBall 0 2) : (1 / 16 : ℝ) • x ∈ Metric.ball (0 : E3) 1 := by
    have hx' : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    linarith
  have hd (x : E3) (hx : x ∈ Metric.closedBall 0 2) : s + (1 / 16 : ℝ) • x ∈ Metric.ball (0 : E3) 1 := by
    have hx' : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [Metric.mem_ball, dist_zero_right]
    have h := norm_add_le s ((1 / 16 : ℝ) • x)
    rw [hs, hnorm] at h
    linarith
  refine ⟨c, d, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have heq' : e.chart (s + (1 / 16 : ℝ) • z) = e.chart ((1 / 16 : ℝ) • x) := by
      simpa only [c, d, OrientedBallChart.affine_apply, zero_add] using heq
    have hvec := e.chart.toPartialEquiv.injOn (e.ball_subset_source (hd z hz))
      (e.ball_subset_source (hc x hx)) heq'
    have hsvec : s = (1 / 16 : ℝ) • (x - z) := by
      rw [smul_sub, ← hvec]
      abel
    have hx' : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hz' : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hbound : ‖s‖ ≤ 1 / 4 := by
      rw [hsvec, hnorm]
      have h := norm_sub_le x z
      linarith
    rw [hs] at hbound
    norm_num at hbound
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨(1 / 16 : ℝ) • x, hc x hx, by simp only [c, OrientedBallChart.affine_apply, zero_add]⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨s + (1 / 16 : ℝ) • x, hd x hx, rfl⟩

theorem exists_oriented_diffeomorph_ballPair_into_chart
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (c d e : OrientedBallChart M.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    ∃ (F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier)
      (c' d' : OrientedBallChart M.toClosedOrientedManifold),
      F.preservesOrientation M.orientation M.orientation ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = c'.chart x) ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, F (d.chart x) = d'.chart x) ∧
      Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2) ∧
      c'.chart '' Metric.closedBall 0 2 ⊆ e.chart '' Metric.ball 0 1 ∧
      d'.chart '' Metric.closedBall 0 2 ⊆ e.chart '' Metric.ball 0 1 := by
  obtain ⟨c', d', hdisj, hc', hd'⟩ := exists_disjoint_ballCharts_in_chart_ball e
  obtain ⟨F, hF, hFc, hFd⟩ := exists_oriented_diffeomorph_ballPair c d c' d' hcd hdisj
  exact ⟨F, c', d', hF, hFc, hFd, hdisj, hc', hd'⟩


theorem exists_orientedBallChart_containing_pair
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (c d : OrientedBallChart M.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    ∃ e : OrientedBallChart M.toClosedOrientedManifold,
      c.chart '' Metric.closedBall 0 2 ⊆ e.chart '' Metric.ball 0 1 ∧
      d.chart '' Metric.closedBall 0 2 ⊆ e.chart '' Metric.ball 0 1 := by
  obtain ⟨F, c', d', hF, hc, hd, _, hc', hd'⟩ := exists_oriented_diffeomorph_ballPair_into_chart c d c hcd
  let e := c.pushforward F.symm (Diffeomorph.preservesOrientation_symm hF)
  refine ⟨e, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, heq⟩ := hc' ⟨x, hx, rfl⟩
    refine ⟨z, hz, ?_⟩
    change F.symm (c.chart z) = c.chart x
    rw [heq, ← hc x hx, F.symm_apply_apply]
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, heq⟩ := hd' ⟨x, hx, rfl⟩
    refine ⟨z, hz, ?_⟩
    change F.symm (c.chart z) = d.chart x
    rw [heq, ← hd x hx, F.symm_apply_apply]

end DifferentialGeometry.Topology
