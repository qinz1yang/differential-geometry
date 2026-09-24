import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.StereographicChart
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Set
open scoped ContDiff Manifold

namespace Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ V H}

theorem IsSmoothEmbedding.stereographic_comp {f : M → Metric.sphere (0 : E) 1}
    (hf : IsSmoothEmbedding I (𝓡 n) ∞ f)
    (p : Metric.sphere (0 : E) 1) (hp : p ∉ range f) :
    IsSmoothEmbedding I (𝓡 n) ∞ ((stereographic' n p) ∘ f) := by
  have hs : ∀ x, f x ∈ (stereographic' n p).source := by
    intro x
    simp only [stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact fun h => hp ⟨x, h⟩
  refine ⟨hf.isImmersion.isLocalDiffeomorphOn_comp ?_, ?_⟩
  · intro x
    exact DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn p
      ⟨x.val, by obtain ⟨y, hy⟩ := x.property; rw [← hy]; exact hs y⟩
  · let g : M → (stereographic' n p).source := fun x => ⟨f x, hs x⟩
    have hg : Topology.IsEmbedding g := hf.isEmbedding.codRestrict _ hs
    have hcomp := (stereographic' n p).isEmbedding_restrict.comp hg
    exact hcomp

end Manifold
