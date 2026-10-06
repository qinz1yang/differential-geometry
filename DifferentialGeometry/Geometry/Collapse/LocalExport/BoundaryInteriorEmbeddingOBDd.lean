import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion
import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.InteriorAtlas

/-!
# A smooth embedding into `W` with values in the interior is one into `W°` (lane S-BD2d, `_OBDd`)

Lane O-BD1 (by S-BD2d), group G10b, kernel. `W° = W.pieceInterior ⊤` carries the interior atlas
(model `𝓡 3`, boundaryless: `interiorCharted_BDRY1`). For a smooth embedding `φ : M → W` (model
`W.model`, boundary or not) with values in `W°`, the same map into `W°` with the interior atlas is a
smooth embedding with model `𝓡 3`: through the diffeomorphism `interiorAtlasDiffeomorph`
(`W.model` to `𝓡 3`); the carrier kinds `closed` (`W.model = 𝓡 3`) and `withBoundary`
(`𝓡∂ 3`, `diffeomorph_comp_fromHalfSpace_OCX`) are treated separately.

* `isSmoothEmbedding_toInterior_OBDd`: the statement.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The target `N₀` of the interior-atlas diffeomorphism as an ARGUMENT (so that the case split on
the carrier kind does not change the instances in the statement). -/
theorem isSmoothEmbedding_toInterior_aux (W : CompactCarrier.{0}) {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace E3 N₀] [IsManifold (𝓡 3) ∞ N₀]
    (D : (W.pieceInterior ⊤) ≃ₘ⟮W.model, 𝓡 3⟯ N₀)
    (φ : M → W.Carrier) (hφ : IsSmoothEmbedding I W.model ∞ φ)
    (hr : ∀ p, φ p ∈ (W.pieceInterior ⊤ : Set W.Carrier)) :
    IsSmoothEmbedding I (𝓡 3) ∞ (fun p => D ⟨φ p, hr p⟩) := by
  have hr' : ∀ p, φ p ∈ (W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) := hr
  have hopen : IsSmoothEmbedding I W.model ∞
      (fun p => (⟨φ p, hr' p⟩ : (W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier))) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen _ _ _ _ hφ
  cases W with
  | mk k C o =>
    cases k
    · exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp I _ _ hopen D
    · exact hopen.diffeomorph_comp_fromHalfSpace_OCX D

/-- **A smooth embedding into `W` with values in the interior is a smooth embedding into `W°`
(interior atlas).** -/
theorem isSmoothEmbedding_toInterior_OBDd (W : CompactCarrier.{0}) {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (φ : M → W.Carrier) (hφ : IsSmoothEmbedding I W.model ∞ φ)
    (hr : ∀ p, φ p ∈ (W.pieceInterior ⊤ : Set W.Carrier)) :
    IsSmoothEmbedding I (𝓡 3) ∞ (fun p => (⟨φ p, hr p⟩ : W.pieceInterior ⊤)) :=
  isSmoothEmbedding_toInterior_aux W (N₀ := W.pieceInterior ⊤)
    (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞) φ hφ hr

end DifferentialGeometry.Geometry.Collapse
