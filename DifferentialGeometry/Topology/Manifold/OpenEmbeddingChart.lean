import DifferentialGeometry.Topology.Manifold.OpenCoverLocalDiffeomorph

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold

variable {E F H M X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

private def openEmbeddingCoordinate (L : E ≃L[ℝ] F) (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, F) M F ∞ :=
  let d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ :=
    ⟨L.toEquiv, L.contDiff.contMDiff, L.symm.contDiff.contMDiff⟩
  (interiorChart I ∞ x).trans d.toPartialDiffeomorph

def openEmbeddingChart (f : M → X) (hf : _root_.Topology.IsOpenEmbedding f)
    (L : E ≃L[ℝ] F) (x : M) : OpenPartialHomeomorph X F := by
  let _ : Nonempty M := ⟨x⟩
  exact (hf.toOpenPartialHomeomorph f).symm.trans
    (openEmbeddingCoordinate I L x).toOpenPartialHomeomorph

theorem mem_openEmbeddingChart_source
    (f : M → X) (hf : _root_.Topology.IsOpenEmbedding f)
    (L : E ≃L[ℝ] F) (x : M) (hx : I.IsInteriorPoint x) :
    f x ∈ (openEmbeddingChart I f hf L x).source := by
  let _ : Nonempty M := ⟨x⟩
  change f x ∈ ((hf.toOpenPartialHomeomorph f).symm.trans
    (openEmbeddingCoordinate I L x).toOpenPartialHomeomorph).source
  refine ⟨?_, ?_⟩
  · exact ⟨x, trivial, rfl⟩
  · change (hf.toOpenPartialHomeomorph f).symm (f x) ∈
      (openEmbeddingCoordinate I L x).source
    rw [hf.toOpenPartialHomeomorph_left_inv f]
    exact ⟨(mem_interiorChart_source_iff I ∞ x).mpr hx, trivial⟩

variable {G H' N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H'] [TopologicalSpace N] [ChartedSpace H' N]
  (J : ModelWithCorners ℝ G H')

theorem isLocalDiffeomorphOn_comp_openEmbeddingChart_symm
    (f : M → X) (hf : _root_.Topology.IsOpenEmbedding f)
    (L : E ≃L[ℝ] F) (x : M) (g : X → N)
    (hgf : IsLocalDiffeomorph I J ∞ (g ∘ f)) :
    IsLocalDiffeomorphOn 𝓘(ℝ, F) J ∞ (g ∘ (openEmbeddingChart I f hf L x).symm)
      (openEmbeddingChart I f hf L x).target := by
  let _ : Nonempty M := ⟨x⟩
  intro y
  have hy : y.val ∈ (openEmbeddingCoordinate I L x).target := y.property.1
  have hd := (openEmbeddingCoordinate I L x).symm.isLocalDiffeomorphAt
    𝓘(ℝ, F) I ∞ hy
  have h := hd.comp (K := J) (P := N) (hgf ((openEmbeddingCoordinate I L x).symm y.val))
  exact h

end DifferentialGeometry.Manifold
