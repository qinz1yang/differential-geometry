import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstaclePullbackSetup
import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstacleInnerObstacle
import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerPreparation

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] {n d p : ℕ}
  {K L : SimplicialComplex ℝ E} {g : C(K.space, M)}
  {X : Set M} {Z : Set E} {b : AdaptedPiecewiseLinearChart K L g X n p} {ε : ℝ}

namespace LocalObstacleChartSetup

variable (S : LocalObstacleChartSetup K L g b Z d ε)
  (m : ObstaclePullbackModel S.approximation)
  (Y : SimplicialComplex ℝ E) (hYK : Y.faces ⊆ m.source.faces) (hYspace : Y.space = Z)

def innerGeometry
    (havoid : ∀ x : K.space, x.val ∈ Z → x.val ∈ L.space → g x ∉ X) :
    NewmanInnerGeometry m.source (S.pullbackFixed m) (S.pullbackMap m) X
      S.approximation.totalRawMap Y.space p := by
  have hZ : Z ⊆ m.source.space :=
    hYspace.symm.subset.trans (subcomplex_space_subset m.source Y hYK)
  have hraw : S.approximation.totalRawMap '' Y.space ⊆
      closedBall b.center (S.radius + 2 * S.gap) := by
    rw [hYspace]
    exact S.active_total_raw m hZ
  have hsmall : S.approximation.totalRawMap '' Y.space ⊆
      ball S.correctedChart.center S.correctedChart.innerRadius :=
    hraw.trans (closedBall_subset_ball (by
      change S.radius + 2 * S.gap < S.radius + 15 * S.gap
      linarith [S.gap_pos]))
  have htarget : S.approximation.totalRawMap '' Y.space ⊆
      S.correctedChart.chart.target :=
    hsmall.trans ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall S.correctedChart.radii_lt.le)).trans
        S.correctedChart.outer_subset)
  have hcore : S.correctedChart.chart.symm ''
      (S.approximation.totalRawMap '' Y.space) ⊆ b.toBufferedChart.core := by
    rintro _ ⟨y, hy, rfl⟩
    apply S.correctedChart_core_subset
    refine ⟨S.correctedChart.chart.map_target (htarget hy), ?_⟩
    change S.correctedChart.chart (S.correctedChart.chart.symm y) ∈
      ball S.correctedChart.center S.correctedChart.innerRadius
    rw [S.correctedChart.chart.right_inv (htarget hy)]
    exact hsmall hy
  have hjoint := S.approximation.jointObstacle_contains_of_corrected_chart
    b.chart X b.toBufferedChart.core Y.space b.obstacle_contains htarget hcore
  have hshared := m.shared_avoids_of_fixed_avoidance b.chart
    (fun x : S.source.space => g ⟨x.val, S.space ▸ x.property⟩) X Y.space
    (fun x _ hx => S.old_source x (by
      rw [subcomplex_inf_space S.source S.region S.fixed S.region_faces S.fixed_faces] at hx
      exact hx.1))
    (fun x _ hx => S.extension_exact x (by
      rw [subcomplex_inf_space S.source S.region S.fixed S.region_faces S.fixed_faces] at hx
      exact hx.1))
    (fun x hxY hx => havoid ⟨x.val, S.space ▸ x.property⟩ (hYspace.subset hxY) (by
      rw [subcomplex_inf_space S.source S.region S.fixed S.region_faces S.fixed_faces] at hx
      exact S.fixed_space.subset hx.2))
  exact {
    gp := m.toFiniteGPFaceModel
    affine := S.total_affine m
    injective := S.total_injective m
    chart := S.correctedChart
    fixed_affine := S.pullback_fixed_affine m
    obstacle := S.approximation.rawObstacleComplex
    obstacle_finite := S.approximation.rawObstacleComplex_finite_faces
    obstacle_dimension := S.approximation.rawObstacleComplex_face_card_le
    obstacle_contains := S.correctedChart_obstacle_contains
    jointObstacle := S.approximation.augmentation.obstacleImage
    jointObstacle_faces := S.approximation.augmentation.obstacleImage_faces
    jointObstacle_dimension := S.approximation.augmentation.obstacleImage_dimension
    jointObstacle_contains := hjoint
    shared_avoids := hshared
  }

@[simp] theorem innerGeometry_chart
    (havoid : ∀ x : K.space, x.val ∈ Z → x.val ∈ L.space → g x ∉ X) :
    (S.innerGeometry m Y hYK hYspace havoid).chart = S.correctedChart := rfl

end LocalObstacleChartSetup

end

end DifferentialGeometry.Topology.Engulfing
