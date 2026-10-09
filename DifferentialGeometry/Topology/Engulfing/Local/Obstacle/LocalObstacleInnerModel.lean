import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerPreparation
import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstaclePullbackSetup
import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanLocalSaturation

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M]
  {n d p : ℕ} {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X : Set M}
  {b : AdaptedPiecewiseLinearChart K L g X n p} {Z : Set E} {ε : ℝ}

theorem LocalObstacleChartSetup.exists_innerModel
    (S : LocalObstacleChartSetup K L g b Z d ε) (m : ObstaclePullbackModel S.approximation)
    (H Y : SimplicialComplex ℝ E) (hHK : H.faces ⊆ m.source.faces)
    (hYK : Y.faces ⊆ m.source.faces) (hYspace : Y.space = Z)
    (a : NewmanInnerGeometry m.source (S.pullbackFixed m) (S.pullbackMap m)
      X S.approximation.totalRawMap Y.space p) (hchart : a.chart = S.correctedChart) :
    Nonempty (NewmanInnerModel m.source (S.pullbackFixed m) H (S.pullbackMap m)
      X S.approximation.totalRawMap Y.space p) := by
  obtain ⟨cut, hcut, hcut_lower, hcut_upper⟩ := exists_finite_complex_between_balls b.center
    (show S.radius + 12 * S.gap < S.radius + 15 * S.gap by linarith [S.gap_pos])
  have hZK : Z ⊆ m.source.space := hYspace ▸ subcomplex_space_subset m.source Y hYK
  have hYD : Y.space ⊆ (S.pullbackRegion m).space := by
    rw [hYspace]
    exact S.active_subset_region m hZK
  have hcenter : a.chart.center = b.center := by rw [hchart]; rfl
  apply exists_newmanInnerModel_of_gap m.source (S.pullbackFixed m) H (S.pullbackRegion m) Y
    m.finite_faces (S.pullbackFixed_faces m) hHK (S.pullbackRegion_faces m) hYK hYD
    (S.pullbackMap m) X S.approximation.totalRawMap a cut hcut
    S.radius S.gap S.gap S.gap_pos le_rfl
    (by rw [hchart]; rfl) (by rw [hchart]; rfl)
    (by simpa only [hcenter] using hcut_lower)
    (by simpa only [hcenter] using hcut_upper)
    (by rw [hcenter, hYspace]; exact S.active_total_raw m hZK)
    (S.total_oscillation m)
  · intro x hx
    rw [hchart]
    exact S.pullback_fixed_coordinates m x hx.1 hx.2
  · intro x hxD hxcut
    rw [hchart]
    exact S.pullback_small_raw_coordinates m x hxD (hcut_upper hxcut)
  · intro x hxsource hxball
    rw [hchart] at hxsource ⊢
    rw [hcenter, hchart] at hxball
    have hx := S.pullback_chart_entry m x
      ⟨S.correctedChart.chart (S.pullbackMap m x), hxball,
        S.correctedChart.chart.left_inv hxsource⟩
    have hxD : x ∈ Subtype.val ⁻¹' (S.pullbackRegion m).space := interior_subset hx.1
    exact ⟨hxD, hx.2⟩

end

end DifferentialGeometry.Topology.Engulfing
