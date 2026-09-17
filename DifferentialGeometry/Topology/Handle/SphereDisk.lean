import DifferentialGeometry.Topology.Embedding.Stereographic
import DifferentialGeometry.Topology.Embedding.FiniteDimension
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.PlanarJordan.SmoothSchoenflies
import DifferentialGeometry.Topology.Handle.SphereComplement

open Set Metric Manifold
open scoped ContDiff Manifold
namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_isSmoothEmbedding_closedCell_sphere_of_circle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    {f : AddCircle (1 : ℝ) → Metric.sphere (0 : E) 1}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ f) :
    ∃ b : ClosedCell 2 → Metric.sphere (0 : E) 1,
      IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
      range (b ∘ cellBoundaryInclusion 2) = range f := by
  obtain ⟨p, hp⟩ := not_forall.mp (hf.not_surjective_of_finrank_ne (by simp)
    (by simp : Module.finrank ℝ ℝ ≠ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))))
  have hpf : p ∉ range f := hp
  let c := stereographic' 2 p
  have hfc := hf.stereographic_comp p hpf
  obtain ⟨Φ, hΦ, _, _⟩ := PlanarJordan.smooth_schoenflies hfc
  let b : ClosedCell 2 → Metric.sphere (0 : E) 1 := fun x => c.symm (Φ x.val)
  have hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b := by
    have hi := (closedCellInclusion_isSmoothEmbedding 1).diffeomorph_comp Φ
    exact ⟨hi.isImmersion.isLocalDiffeomorphOn_comp
      (fun x => DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph p x.val),
      (c.symm.isOpenEmbedding (by simp [c])).isEmbedding.comp hi.isEmbedding⟩
  refine ⟨b, hb, ?_⟩
  have hboundary : range ((Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) ∘
      cellBoundaryInclusion 2) = sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := range_cellBoundary 2
  have hleft : ∀ x, c.symm (c (f x)) = f x := by
    intro x
    apply c.left_inv
    simp only [c, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact fun h => hp ⟨x, h⟩
  change range ((c.symm ∘ Φ) ∘ ((Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) ∘
    cellBoundaryInclusion 2)) = range f
  rw [range_comp, hboundary, image_comp, hΦ, ← range_comp]
  congr 1
  exact funext hleft

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem exists_two_smooth_disks_sphere_of_circle
    {f : AddCircle (1 : ℝ) → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ f) :
    ∃ b₀ b₁ : ClosedCell 2 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₀ ∧ IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₁ ∧
      range (b₀ ∘ cellBoundaryInclusion 2) = range f ∧
      range (b₁ ∘ cellBoundaryInclusion 2) = range f ∧
      range b₀ ∪ range b₁ = univ ∧ range b₀ ∩ range b₁ = range f := by
  obtain ⟨b₀, hb₀, hf₀⟩ := exists_isSmoothEmbedding_closedCell_sphere_of_circle hf
  obtain ⟨b₁, hb₁, himage⟩ := exists_isSmoothEmbedding_closedCell_complement_sphere 1 hb₀
  have hclosed : IsClosed (range b₀) := (isCompact_range hb₀.isEmbedding.continuous).isClosed
  have hfrontier : frontier (range b₀) = range f :=
    (frontier_range_closedCell_sphere 1 hb₀).trans hf₀
  have hfrontier₁ : frontier (range b₁) = frontier (range b₀) := by
    rw [himage, closure_compl, frontier_compl]
    simp only [frontier, closure_interior_range_closedCell_sphere 1 hb₀,
      interior_interior, hclosed.closure_eq]
  refine ⟨b₀, b₁, hb₀, hb₁, hf₀,
    (frontier_range_closedCell_sphere 1 hb₁).symm.trans (hfrontier₁.trans hfrontier), ?_, ?_⟩
  · rw [himage]
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ range b₀
    · exact Or.inl hx
    · exact Or.inr (subset_closure hx)
  · rw [himage, closure_compl, ← hfrontier, frontier, hclosed.closure_eq]
    rfl


end DifferentialGeometry.Topology.Handle
