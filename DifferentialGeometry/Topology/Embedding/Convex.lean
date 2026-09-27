import DifferentialGeometry.Topology.Diffeomorph.Convex
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Handle.Embedding

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_smooth_convex_sublevel_ball_filling (n : ℕ)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hc : ContDiff ℝ ∞ f)
    (hb : Bornology.IsBounded {x | f x ≤ 0})
    {c : EuclideanSpace ℝ (Fin (n + 1))} (hneg : f c < 0) :
    ∃ b : ClosedCell (n + 1) → EuclideanSpace ℝ (Fin (n + 1)),
      Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace (n + 1))
        (𝓡 (n + 1)) ∞ b ∧
      b (closedCellCenter (n + 1)) = c ∧
      Set.range b = {x | f x ≤ 0} ∧
      Set.range (b ∘ cellBoundaryInclusion (n + 1)) = {x | f x = 0} := by
  obtain ⟨F, hzero, _, hclosed, _, hsphere⟩ :=
    Diffeomorph.exists_diffeomorph_convex_sublevel hf hc hb hneg
  refine ⟨F ∘ Subtype.val,
    (Handle.closedCellInclusion_isSmoothEmbedding n).diffeomorph_comp F,
    hzero, ?_, ?_⟩
  · rw [Set.range_comp, Subtype.range_val_subtype]
    simpa only [Metric.closedBall, dist_zero_right] using hclosed
  · change Set.range (F ∘ (Subtype.val : CellBoundary (n + 1) → _)) = _
    rw [Set.range_comp, Subtype.range_val_subtype]
    simpa only [Metric.sphere, dist_zero_right] using hsphere

end DifferentialGeometry.Topology
