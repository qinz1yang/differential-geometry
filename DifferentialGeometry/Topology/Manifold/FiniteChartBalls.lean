import Mathlib.Geometry.Manifold.ChartedSpace
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

end DifferentialGeometry.Topology
