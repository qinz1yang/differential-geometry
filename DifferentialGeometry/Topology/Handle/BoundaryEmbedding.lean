import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.ClosedBall
import Mathlib.Geometry.Manifold.Instances.Sphere

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private local instance (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨by simp⟩

theorem not_surjective_closedCell_of_isSmoothEmbedding (m : ℕ)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M]
    {n : ℕ∞ω} (hn : n ≠ 0) {u : ClosedCell (m + 1) → M}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) I n u) :
    ¬ Function.Surjective u := by
  let x : ClosedCell (m + 1) := ⟨EuclideanSpace.single 0 1, by simp⟩
  apply hu.not_surjective_of_isBoundaryPoint hn (x := x)
  change x ∈ (𝓡∂ (m + 1)).boundary (ClosedCell (m + 1))
  rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere]
  simp [x]

theorem exists_stereographic_source_superset_range_closedCell (m k : ℕ)
    {n : ℕ∞ω} (hn : n ≠ 0)
    {u : ClosedCell (m + 1) → Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 k) n u) :
    ∃ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
      Set.range u ⊆ (stereographic' k p).source := by
  obtain ⟨p, hp⟩ := not_forall.mp (not_surjective_closedCell_of_isSmoothEmbedding m hn hu)
  refine ⟨p, ?_⟩
  rintro y ⟨x, rfl⟩
  simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using
    (show u x ≠ p from fun h => hp ⟨x, h⟩)

end DifferentialGeometry.Topology.Handle
