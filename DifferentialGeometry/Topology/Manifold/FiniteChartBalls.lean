import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Defs








open Set
open scoped Topology

namespace DifferentialGeometry.Topology




theorem exists_finite_chart_ball_cover
    {E M : Type*} [PseudoMetricSpace E] [TopologicalSpace M]
    [ChartedSpace E M] [CompactSpace M] {a : ℝ} (ha : 0 < a) :
    ∃ r : M → ℝ, (∀ p, 0 < r p ∧
      Metric.closedBall (chartAt E p p) (a * r p) ⊆ (chartAt E p).target) ∧
      ∃ t : Finset M, ∀ q, ∃ p ∈ t,
        q ∈ (chartAt E p).source ∧ chartAt E p q ∈ Metric.ball (chartAt E p p) (r p) := by
  classical
  have hlocal (p : M) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartAt E p p) (a * r) ⊆ (chartAt E p).target := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((chartAt E p).open_target.mem_nhds (mem_chart_target E p))
    refine ⟨ρ / a, div_pos hρ ha, ?_⟩
    simpa [mul_div_cancel₀ _ ha.ne'] using hsub
  choose r hr hsub using hlocal
  let U : M → Set M := fun p => (chartAt E p).source ∩
    (chartAt E p) ⁻¹' Metric.ball (chartAt E p p) (r p)
  have hU : ∀ p, IsOpen (U p) := fun p =>
    (chartAt E p).isOpen_inter_preimage Metric.isOpen_ball
  have hcover : univ ⊆ ⋃ p, U p := by
    intro p _
    exact mem_iUnion.mpr ⟨p, mem_chart_source E p, Metric.mem_ball_self (hr p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨r, fun p => ⟨hr p, hsub p⟩, t, fun q => ?_⟩
  obtain ⟨p, hp, hq⟩ := mem_iUnion₂.mp (ht (mem_univ q))
  exact ⟨p, hp, hq.1, hq.2⟩

theorem exists_finite_extChartAt_ball_cover
    {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] {a : ℝ} (ha : 0 < a) :
    ∃ r : M → ℝ, (∀ p, 0 < r p ∧
      Metric.closedBall (extChartAt I p p) (a * r p) ⊆ (extChartAt I p).target) ∧
      ∃ t : Finset M, ∀ q, ∃ p ∈ t,
        q ∈ (extChartAt I p).source ∧ extChartAt I p q ∈ Metric.ball (extChartAt I p p) (r p) := by
  let e : M → OpenPartialHomeomorph M E := fun p =>
    { toPartialEquiv := extChartAt I p
      open_source := isOpen_extChartAt_source p
      open_target := isOpen_extChartAt_target p
      continuousOn_toFun := continuousOn_extChartAt p
      continuousOn_invFun := continuousOn_extChartAt_symm p }
  let : ChartedSpace E M :=
    { atlas := range e
      chartAt := e
      mem_chart_source := fun p => mem_extChartAt_source p
      chart_mem_atlas := fun p => mem_range_self p }
  exact exists_finite_chart_ball_cover (E := E) (M := M) ha

theorem exists_finite_extChartAt_cover_with_margin
    {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ t : Finset M, ∃ K : M → Set E,
      (∀ p ∈ t, IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target) ∧
      ∀ q, ∃ p ∈ t, q ∈ (extChartAt I p).source ∧
        Metric.closedBall (extChartAt I p q) ρ ⊆ K p := by
  classical
  obtain ⟨r, hr, t, ht⟩ := exists_finite_extChartAt_ball_cover (I := I) (M := M)
    (a := 3) (by norm_num)
  let K := fun p => Metric.closedBall (extChartAt I p p) (2 * r p)
  have hK (p : M) : IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target :=
    ⟨isCompact_closedBall _ _, (Metric.closedBall_subset_closedBall (by linarith [(hr p).1])).trans
      (hr p).2⟩
  by_cases htn : t.Nonempty
  · let ρ := t.inf' htn r
    have hρ : 0 < ρ := (Finset.lt_inf'_iff _).mpr (fun p _ => (hr p).1)
    refine ⟨ρ, hρ, t, K, fun p _ => hK p, fun q => ?_⟩
    obtain ⟨p, hp, hq, hqr⟩ := ht q
    refine ⟨p, hp, hq, fun y hy => ?_⟩
    have hρr : ρ ≤ r p := Finset.inf'_le _ hp
    have hyρ : dist y (extChartAt I p q) ≤ ρ := hy
    have hqr' : dist (extChartAt I p q) (extChartAt I p p) < r p := hqr
    have hdist := dist_triangle y (extChartAt I p q) (extChartAt I p p)
    change dist y (extChartAt I p p) ≤ 2 * r p
    linarith only [hyρ, hqr', hρr, hdist]
  · refine ⟨1, zero_lt_one, t, K, fun p _ => hK p, fun q => ?_⟩
    obtain ⟨p, hp, _⟩ := ht q
    exact (htn ⟨p, hp⟩).elim


end DifferentialGeometry.Topology
