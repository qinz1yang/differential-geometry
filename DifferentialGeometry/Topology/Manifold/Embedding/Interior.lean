import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInteriorImage
import DifferentialGeometry.Topology.Manifold.InteriorImage
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingRestriction
import DifferentialGeometry.Topology.Embedding.Diffeomorph

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Manifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [BoundarylessManifold J N] {f : M → N}

theorem IsSmoothEmbedding.image_interior_eq_interior_range
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    f '' I.interior M = interior (range f) := by
  apply Subset.antisymm
  · exact interior_maximal (image_subset_range _ _)
      (DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion hf.isImmersion hdim)
  · intro y hy
    obtain ⟨x, rfl⟩ := interior_subset hy
    exact ⟨x, hf.isInteriorPoint_of_mem_interior_range hdim hy
      BoundarylessManifold.isInteriorPoint, rfl⟩

def IsSmoothEmbedding.interiorDiffeomorph
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
    let V : TopologicalSpace.Opens N := ⟨interior (range f), isOpen_interior⟩
    Diffeomorph I J U V ∞ := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let V : TopologicalSpace.Opens N := ⟨interior (range f), isOpen_interior⟩
  let hfU := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen I J f hf U
  refine hfU.diffeomorphOfRangeEq (IsSmoothEmbedding.of_opens (I := J) (n := ∞) V) ?_
  change range (f ∘ (Subtype.val : U → M)) = range (Subtype.val : V → N)
  rw [range_comp, Subtype.range_coe, Subtype.range_coe]
  exact hf.image_interior_eq_interior_range hdim

@[simp] theorem IsSmoothEmbedding.interiorDiffeomorph_apply_val
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (x : DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)) :
    (hf.interiorDiffeomorph hdim x).val = f x.val := by
  exact (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen I J f hf _).comp_diffeomorphOfRangeEq
    (IsSmoothEmbedding.of_opens (I := J) (n := ∞) _) _ x

theorem IsSmoothEmbedding.interiorDiffeomorph_symm_apply
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (y : (⟨interior (range f), isOpen_interior⟩ : TopologicalSpace.Opens N)) :
    f ((hf.interiorDiffeomorph hdim).symm y).val = y.val := by
  rw [← hf.interiorDiffeomorph_apply_val hdim,
    (hf.interiorDiffeomorph hdim).apply_symm_apply]

end Manifold
