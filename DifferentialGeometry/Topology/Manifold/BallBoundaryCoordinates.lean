import DifferentialGeometry.Topology.Manifold.BallChart.Defs
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.BallChart

variable {n : ℕ}


local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  (c : BallChart (n + 1) (𝓡 (n + 1)) M)

private def angularHeightChart (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ((sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) × ℝ) (EuclideanSpace ℝ (Fin (n + 1))) ∞ :=
  (PartialDiffeomorph.prod (PartialDiffeomorph.extendedChart (I := 𝓡 n) z)
    (translateDiffeomorph (-1 : ℝ)).toPartialDiffeomorph).trans
      (signedNormalFirstDiffeomorph n true).toPartialDiffeomorph

private def unrestrictedRadialBoundaryChart (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) M (EuclideanSpace ℝ (Fin (n + 1))) ∞ :=
  (c.chart.symm.trans (Manifold.spherePolarChart (n := n) z).symm).trans
    (angularHeightChart z)

private theorem unrestrictedRadialBoundaryChart_zero (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (x : M) :
    unrestrictedRadialBoundaryChart c z x 0 = ‖c.chart.symm x‖ - 1 := by
  change signedNormalFirstEquiv n true (_, ‖c.chart.symm x‖ + -1) 0 = _
  rw [signedNormalFirstEquiv_zero]
  rfl

private theorem chart_sphere_mem_unrestrictedRadialBoundaryChart_source (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    c.chart z ∈ (unrestrictedRadialBoundaryChart c z).source := by
  have hz : (z : (EuclideanSpace ℝ (Fin (n + 1)))) ∈ c.chart.source := c.sphere_subset_source z.property
  have hpoint : c.chart.symm (c.chart z) = (z : (EuclideanSpace ℝ (Fin (n + 1)))) := c.chart.left_inv hz
  change (c.chart z ∈ c.chart.target ∧ c.chart.symm (c.chart z) ≠ 0) ∧
    (Manifold.spherePolarChart (n := n) z).symm (c.chart.symm (c.chart z)) ∈
      (angularHeightChart z).source
  rw [hpoint]
  refine ⟨⟨c.chart.map_source hz, ne_zero_of_mem_unit_sphere z⟩, ?_⟩
  change ((Manifold.sphereDirection z z ∈ (extChartAt (𝓡 n) z).source ∧ True) ∧ True)
  have hs : Manifold.sphereDirection z (z : (EuclideanSpace ℝ (Fin (n + 1)))) = z := by
    simpa only [one_smul] using Manifold.sphereDirection_pos_smul z z zero_lt_one
  rw [hs]
  exact ⟨⟨mem_extChartAt_source z, trivial⟩, trivial⟩

def radialBoundaryChart (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) M (EuclideanSpace ℝ (Fin (n + 1))) ∞ :=
  PartialDiffeomorph.restrict (unrestrictedRadialBoundaryChart c z)
    (c.chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 2)
    (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (fun _ hx => c.closedBall_subset_source (ball_subset_closedBall hx)))

theorem chart_sphere_mem_radialBoundaryChart_source (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    c.chart z ∈ (c.radialBoundaryChart z).source := by
  refine ⟨chart_sphere_mem_unrestrictedRadialBoundaryChart_source c z, z, ?_, rfl⟩
  simp only [mem_ball, dist_zero_right, norm_eq_of_mem_sphere]
  norm_num

theorem radialBoundaryChart_zero (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (x : M) :
    c.radialBoundaryChart z x 0 = ‖c.chart.symm x‖ - 1 :=
  unrestrictedRadialBoundaryChart_zero c z x

theorem radialBoundaryChart_source_subset_image_ball (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    (c.radialBoundaryChart z).source ⊆ c.chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 2 :=
  fun _ hx => hx.2

theorem not_mem_ball_iff_radialBoundaryChart_nonneg (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) {x : M}
    (hx : x ∈ (c.radialBoundaryChart z).source) :
    x ∉ c.chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 ↔ 0 ≤ c.radialBoundaryChart z x 0 := by
  have hxt : x ∈ c.chart.target := hx.1.1.1
  rw [radialBoundaryChart_zero]
  constructor
  · intro h
    by_contra hn
    apply h
    refine ⟨c.chart.symm x, ?_, c.chart.right_inv hxt⟩
    rw [mem_ball, dist_zero_right]
    linarith [not_le.mp hn]
  · rintro h ⟨y, hy, rfl⟩
    change 0 ≤ ‖c.chart.symm (c.chart y)‖ - 1 at h
    have hn : ‖c.chart.symm (c.chart y)‖ = ‖y‖ :=
      congrArg norm (c.chart.left_inv (c.ball_subset_source hy))
    have hy1 : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
    linarith [hn]

theorem radialBoundaryChart_zero_iff_mem_sphere (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) {x : M}
    (hx : x ∈ (c.radialBoundaryChart z).source) :
    c.radialBoundaryChart z x 0 = 0 ↔ x ∈ c.chart '' sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 := by
  have hxt : x ∈ c.chart.target := hx.1.1.1
  rw [radialBoundaryChart_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨c.chart.symm x, by simpa only [mem_sphere, dist_zero_right] using h,
      c.chart.right_inv hxt⟩
  · rintro ⟨y, hy, rfl⟩
    change ‖c.chart.symm (c.chart y)‖ = 1
    exact (congrArg norm (c.chart.left_inv (c.sphere_subset_source hy))).trans
      (by simpa only [mem_sphere, dist_zero_right] using hy)

end DifferentialGeometry.Topology.BallChart
