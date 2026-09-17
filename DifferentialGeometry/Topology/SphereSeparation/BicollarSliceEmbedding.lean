import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.SphereSeparation.BicollarSliceSeparation

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

theorem isSmoothEmbedding_bicollarSliceMap
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (c : AxialInterval a) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (bicollarSliceMap Φ c) := by
  let ι : SphereTwo → SphereTwo × AxialInterval a := fun z => (z, c)
  have hproj : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞ (Prod.fst ∘ ι) :=
    Manifold.IsSmoothEmbedding.id
  have hι : Manifold.IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ ι :=
    hproj.of_comp (J := (𝓡 2).prod 𝓘(ℝ, ℝ)) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  exact hΦ.comp hι (by simp)

end DifferentialGeometry.Topology.SphereSeparation
