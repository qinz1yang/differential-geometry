import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstacleChartSetup
import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstacleFiniteGPModel
import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstacleFaceOscillation
import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstacleRawComplex
import DifferentialGeometry.Topology.Engulfing.Local.Charts.CorrectedBufferedChart
import DifferentialGeometry.Topology.Engulfing.Local.Charts.FixedChartFromLocalModel
import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanGlobalData

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] {n d p : ℕ}
  {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X Z : Set E}

namespace LocalObstacleChartSetup

variable {X : Set M} {b : AdaptedPiecewiseLinearChart K L g X n p} {Z : Set E} {ε : ℝ}
  (S : LocalObstacleChartSetup K L g b Z d ε)

def correctedChart : BufferedChart M n :=
  b.toBufferedChart.corrected S.approximation.correction
    (show 0 < S.radius + 15 * S.gap by linarith [S.radius_pos, S.gap_pos])
    (show S.radius + 15 * S.gap < S.radius + 18 * S.gap by linarith [S.gap_pos])
    S.approximation.correction_near
    (show S.radius + 18 * S.gap + S.error ≤ b.outerRadius by
      linarith [S.room, S.error_le, S.gap_pos, b.radii_lt])

theorem correctedChart_core_subset : S.correctedChart.core ⊆ b.toBufferedChart.core :=
  b.toBufferedChart.corrected_core_subset S.approximation.correction _ _ _ _
    (by linarith [S.room, S.error_le, S.gap_pos])

theorem correctedChart_obstacle_contains :
    S.correctedChart.chart '' (X ∩ S.correctedChart.core) ⊆
      S.approximation.rawObstacleComplex.space := by
  rw [S.approximation.rawObstacleComplex_space]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨b.chart x, b.obstacle_contains
    ⟨x, ⟨hx.1, S.correctedChart_core_subset hx.2⟩, rfl⟩, rfl⟩

variable (m : ObstaclePullbackModel S.approximation)

def pullbackFixed : SimplicialComplex ℝ E := complexRestriction m.source S.fixed

def pullbackRegion : SimplicialComplex ℝ E := complexRestriction m.source S.region

def pullbackMap : C(m.source.space, M) :=
  S.map.comp ⟨Homeomorph.setCongr m.space, (Homeomorph.setCongr m.space).continuous⟩

theorem pullbackFixed_faces : (S.pullbackFixed m).faces ⊆ m.source.faces :=
  complexRestriction_faces_subset _ _

theorem pullbackRegion_faces : (S.pullbackRegion m).faces ⊆ m.source.faces :=
  complexRestriction_faces_subset _ _

theorem pullbackFixed_space : (S.pullbackFixed m).space = L.space :=
  (complexRestriction_space_of_refines m.source S.source S.fixed m.refines m.space
    S.fixed_faces).trans S.fixed_space

theorem pullbackRegion_space : (S.pullbackRegion m).space = S.region.space :=
  complexRestriction_space_of_refines m.source S.source S.region m.refines m.space S.region_faces

theorem pullbackMap_fixed (x : m.source.space) (hx : x.val ∈ L.space) :
    S.pullbackMap m x = g ⟨x.val, (m.space.trans S.space) ▸ x.property⟩ :=
  S.map_fixed ⟨x.val, m.space ▸ x.property⟩ hx

theorem pullbackMap_near (x : m.source.space) :
    dist (S.pullbackMap m x) (g ⟨x.val, (m.space.trans S.space) ▸ x.property⟩) < ε :=
  S.map_near ⟨x.val, m.space ▸ x.property⟩

theorem pullbackMap_injOn_fixed (hinj : InjOn g (Subtype.val ⁻¹' L.space)) :
    InjOn (S.pullbackMap m) (Subtype.val ⁻¹' (S.pullbackFixed m).space) := by
  intro x hx y hy he
  have hxL := (S.pullbackFixed_space m).subset hx
  have hyL := (S.pullbackFixed_space m).subset hy
  rw [S.pullbackMap_fixed m x hxL, S.pullbackMap_fixed m y hyL] at he
  exact Subtype.ext (congrArg (fun z : K.space => z.val) (hinj hxL hyL he))

theorem pullbackMap_hasAdaptedPiecewiseLinearCharts (h : hasAdaptedPiecewiseLinearCharts K L g X n p) :
    hasAdaptedPiecewiseLinearCharts m.source (S.pullbackFixed m) (S.pullbackMap m) X n p := by
  let gR : C(m.source.space, M) := g.comp
    ⟨Homeomorph.setCongr (m.space.trans S.space),
      (Homeomorph.setCongr (m.space.trans S.space)).continuous⟩
  have hR := h.refine m.source (S.pullbackFixed m) (m.space.trans S.space)
    ((complexRestriction_refines_right m.source S.fixed).trans S.fixed_refines)
    (S.pullbackFixed_space m).subset gR (fun _ => rfl)
  exact hR.withMap (S.pullbackMap m) (fun x hx =>
    S.pullbackMap_fixed m x ((S.pullbackFixed_space m).subset hx))

theorem active_subset_region (hZ : Z ⊆ m.source.space) : Z ⊆ (S.pullbackRegion m).space := by
  intro x hx
  rw [S.pullbackRegion_space m]
  let x' : S.source.space := ⟨x, m.space.subset (hZ hx)⟩
  exact show x' ∈ Subtype.val ⁻¹' S.region.space from
    interior_subset (S.core_region (interior_subset (S.active_core x' hx)))

theorem active_total_raw (hZ : Z ⊆ m.source.space) :
    S.approximation.totalRawMap '' Z ⊆ closedBall b.center (S.radius + 2 * S.gap) := by
  rintro _ ⟨x, hx, rfl⟩
  let x' : S.source.space := ⟨x, m.space.subset (hZ hx)⟩
  rw [show S.approximation.totalRawMap x = S.approximation.rawMap x' from
    S.approximation.totalRawMap_subtype x']
  exact S.active_raw x' hx

theorem total_affine : ∀ s ∈ m.source.faces,
    ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn S.approximation.totalRawMap A (convexHull ℝ (s : Set E)) := by
  intro s hs
  obtain ⟨A, hA, -⟩ := m.affine s hs
  refine ⟨A, fun x hx => ?_⟩
  let x' : S.source.space := ⟨x, m.space.subset (m.source.convexHull_subset_space hs hx)⟩
  exact (S.approximation.totalRawMap_subtype x').trans (hA x' hx)

theorem total_injective : ∀ s ∈ m.source.faces,
    InjOn S.approximation.totalRawMap (convexHull ℝ (s : Set E)) := by
  intro s hs
  obtain ⟨A, hA, hinj⟩ := m.affine s hs
  intro x hx y hy he
  apply hinj hx hy
  let x' : S.source.space := ⟨x, m.space.subset (m.source.convexHull_subset_space hs hx)⟩
  let y' : S.source.space := ⟨y, m.space.subset (m.source.convexHull_subset_space hs hy)⟩
  exact (hA x' hx).symm.trans ((S.approximation.totalRawMap_subtype x').symm.trans
    (he.trans ((S.approximation.totalRawMap_subtype y').trans (hA y' hy))))

theorem total_oscillation : ∀ s ∈ m.source.faces,
    ∀ x ∈ convexHull ℝ (s : Set E), ∀ y ∈ convexHull ℝ (s : Set E),
      dist (S.approximation.totalRawMap x) (S.approximation.totalRawMap y) < 5 * S.gap := by
  intro s hs x hx y hy
  let x' : S.source.space := ⟨x, m.space.subset (m.source.convexHull_subset_space hs hx)⟩
  let y' : S.source.space := ⟨y, m.space.subset (m.source.convexHull_subset_space hs hy)⟩
  rw [show S.approximation.totalRawMap x = S.approximation.rawMap x' from
    S.approximation.totalRawMap_subtype x',
    show S.approximation.totalRawMap y = S.approximation.rawMap y' from
    S.approximation.totalRawMap_subtype y']
  exact (m.raw_oscillation hs x' y' hx hy).trans_le (by linarith [S.error_le])

theorem pullback_fixed_coordinates (x : m.source.space)
    (hxL : x.val ∈ (S.pullbackFixed m).space) (hxD : x.val ∈ (S.pullbackRegion m).space) :
    S.pullbackMap m x ∈ S.correctedChart.chart.source ∧
      S.correctedChart.chart (S.pullbackMap m x) = S.approximation.totalRawMap x.val := by
  let x' : S.source.space := ⟨x.val, m.space ▸ x.property⟩
  have hxL' : x.val ∈ L.space := (S.pullbackFixed_space m).subset hxL
  have hxD' : x.val ∈ S.region.space := (S.pullbackRegion_space m).subset hxD
  refine ⟨S.map_source x' hxD', ?_⟩
  have hxI : x'.val ∈ (S.region ⊓ S.fixed).space := by
    rw [subcomplex_inf_space S.source S.region S.fixed S.region_faces S.fixed_faces]
    exact ⟨hxD', S.fixed_space.symm.subset hxL'⟩
  exact (S.approximation.correctedChart_eq_rawMap_of_relative b.chart
    (fun y => g ⟨y.val, S.space ▸ y.property⟩) S.map hxI
    (S.map_fixed x' hxL') (S.extension_exact x' hxD')).trans
      (S.approximation.totalRawMap_subtype x').symm

theorem pullback_small_raw_coordinates (x : m.source.space)
    (hxD : x.val ∈ (S.pullbackRegion m).space)
    (hxraw : S.approximation.totalRawMap x.val ∈ ball b.center (S.radius + 15 * S.gap)) :
    S.pullbackMap m x ∈ S.correctedChart.chart.source ∧
      S.correctedChart.chart (S.pullbackMap m x) = S.approximation.totalRawMap x.val := by
  let x' : S.source.space := ⟨x.val, m.space ▸ x.property⟩
  have hxD' : x.val ∈ S.region.space := (S.pullbackRegion_space m).subset hxD
  have hxraw' : S.approximation.rawMap x' ∈ ball b.center (S.radius + 15 * S.gap) := by
    rwa [← S.approximation.totalRawMap_subtype x']
  have hxcore : x' ∈ S.core := interior_subset (S.old_core x'
    (S.approximation.original_mem_chart_closedBall_of_rawMap_mem_ball b.chart
      (fun y => g ⟨y.val, S.space ▸ y.property⟩) b.center
      (S.old_source x' hxD') (S.extension_exact x' hxD') hxraw'
      (by linarith [S.error_le, S.gap_pos])))
  refine ⟨S.map_source x' hxD', ?_⟩
  exact (S.approximation.correctedChart_eq_rawMap_of_exact b.chart S.map
    (S.exact_core x' hxcore)).trans (S.approximation.totalRawMap_subtype x').symm

theorem pullback_chart_entry (x : m.source.space)
    (hx : S.pullbackMap m x ∈ S.correctedChart.chart.symm ''
      closedBall b.center (S.radius + 18 * S.gap)) :
    x ∈ interior (Subtype.val ⁻¹' (S.pullbackRegion m).space) ∧
      S.correctedChart.chart (S.pullbackMap m x) = S.approximation.totalRawMap x.val := by
  let e : m.source.space ≃ₜ S.source.space := Homeomorph.setCongr m.space
  have hcore : e x ∈ S.core := interior_subset (S.new_core (e x) hx)
  refine ⟨?_, ?_⟩
  · rw [S.pullbackRegion_space m]
    have hm : x ∈ e ⁻¹' interior (Subtype.val ⁻¹' S.region.space) := S.core_region hcore
    rw [e.preimage_interior] at hm
    exact hm
  · exact (S.approximation.correctedChart_eq_rawMap_of_exact b.chart S.map
      (S.exact_core (e x) hcore)).trans (S.approximation.totalRawMap_subtype (e x)).symm

theorem pullback_fixed_affine : ∀ s ∈ (S.pullbackFixed m).faces,
    ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : m.source.space, x.val ∈ convexHull ℝ (s : Set E) →
        S.pullbackMap m x ∈ S.correctedChart.core →
          S.correctedChart.chart (S.pullbackMap m x) = A x.val := by
  apply fixed_affine_of_local_model m.source (S.pullbackFixed m) (S.pullbackRegion m)
    (S.pullbackFixed_faces m) (S.pullbackRegion_faces m) (S.pullbackMap m)
    S.correctedChart S.approximation.totalRawMap
    (fun s hs => S.total_affine m s (S.pullbackRegion_faces m hs))
    (fun x hxL hxD => (S.pullback_fixed_coordinates m x hxL hxD).2)
  intro x _ hx
  apply (S.pullback_chart_entry m x ?_).1
  exact ⟨S.correctedChart.chart (S.pullbackMap m x),
    closedBall_subset_closedBall (by linarith [S.gap_pos] :
      S.radius + 15 * S.gap ≤ S.radius + 18 * S.gap) (ball_subset_closedBall hx.2),
    S.correctedChart.chart.left_inv hx.1⟩

end LocalObstacleChartSetup

end

end DifferentialGeometry.Topology.Engulfing
