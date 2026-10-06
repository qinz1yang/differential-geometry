import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskCompositionOED
import DifferentialGeometry.Topology.Embedding.CrossModelInstancesOCX
import DifferentialGeometry.Topology.Manifold.ProductSectionCenteredChart
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource

/-!
# The slice of a disk chart into a carrier of either kind (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G8b (hlift, the cut facts `H`: kernel of
`EdgeCutFacts74.fibre_disk`). The tree composes smooth embeddings only into boundaryless targets or
through a boundaryless middle manifold; the slice `z ↦ φ (0, z)` of a disk chart
`φ : ℝ¹ × D² → W` (middle `ℝ¹ × D²` has boundary, target `W` may have boundary) is handled here:

* `isSmoothEmbedding_diskSlice_OBD`: `z ↦ (0, z)` is a smooth embedding `D² → ℝ¹ × D²`
  (`isSmoothEmbedding_const_prodMk_of_centered_chart`);
* `isSmoothEmbedding_slice_halfSpace_OBD` (generic): an `𝓡∂ 3`-manifold `N`, an open set `U` whose
  `𝓡∂ 3`-structure is identified with a boundaryless `𝓡 3`-structure by a diffeomorphism `e`
  followed by a local diffeomorphism embedding `ι` (`ι ∘ e = val`): `φ` with values in `U` has the
  smooth-embedding slice (interior lift by `diffeomorph_comp_fromHalfSpace_OCX`, composition with
  `comp_of_smoothBoundary` into the boundaryless chart manifold, back by
  `localDiffeomorph_comp_toHalfSpace_OED`);
* `isSmoothEmbedding_slice_of_interior_OBD`: the carrier form (`W.kind` closed: the boundaryless
  composition; with boundary: the interior atlas and the generic form), for `φ` with values in
  `W°`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The slice `z ↦ (0, z)` of `ℝ¹ × D²` is a smooth embedding. -/
theorem isSmoothEmbedding_diskSlice_OBD :
    IsSmoothEmbedding (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 2)) ∞ (fun z : ClosedCell 2 => ((0 : ℝ¹), z)) :=
  isSmoothEmbedding_const_prodMk_of_centered_chart (0 : ℝ¹) (chartAt ℝ¹ (0 : ℝ¹))
    (mem_chart_source ℝ¹ (0 : ℝ¹)) (IsManifold.chart_mem_maximalAtlas (0 : ℝ¹)) (by simp)

/-- **The slice of a disk chart into the interior of a half-space manifold** (generic form):
`φ : ℝ¹ × D² → N` a smooth embedding into an `𝓡∂ 3`-manifold with values in an open set `U` whose
`𝓡∂ 3`-structure is identified with a boundaryless `𝓡 3`-structure `cs` by a diffeomorphism `e`
(followed by a local diffeomorphism embedding `ι` into `N`, `ι ∘ e = val`): the slice `z ↦ φ (0, z)`
is a smooth embedding of the closed cell. -/
theorem isSmoothEmbedding_slice_halfSpace_OBD {N N₀ : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold (𝓡∂ 3) ∞ N] [TopologicalSpace N₀]
    (cs : ChartedSpace ℝ³ N₀) (hN₀ : IsManifold (𝓡 3) ∞ N₀) (U : TopologicalSpace.Opens N)
    (e : Diffeomorph (𝓡∂ 3) 𝓘(ℝ, ℝ³) U N₀ ∞) (ι : N₀ → N)
    (hι : IsLocalDiffeomorph 𝓘(ℝ, ℝ³) (𝓡∂ 3) ∞ ι) (hιe : IsEmbedding ι)
    (hιU : ∀ x : U, ι (e x) = (x : N)) (φ : ℝ¹ × ClosedCell 2 → N)
    (hφ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) (𝓡∂ 3) ∞ φ) (hr : ∀ p, φ p ∈ U) :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ (fun z : ClosedCell 2 => φ (0, z)) := by
  let Φ₀ : ℝ¹ × ClosedCell 2 → U := fun p => ⟨φ p, hr p⟩
  have hopen : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) (𝓡∂ 3) ∞ Φ₀ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen _ _ U Φ₀ hφ
  have hΦ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) 𝓘(ℝ, ℝ³) ∞ (e ∘ Φ₀) :=
    hopen.diffeomorph_comp_fromHalfSpace_OCX e
  have hslice : IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, ℝ³) ∞ ((e ∘ Φ₀) ∘ fun z : ClosedCell 2 =>
      ((0 : ℝ¹), z)) :=
    hΦ.comp_of_smoothBoundary isSmoothEmbedding_diskSlice_OBD
  have hfinal : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ (ι ∘ ((e ∘ Φ₀) ∘ fun z : ClosedCell 2 =>
      ((0 : ℝ¹), z))) :=
    isSmoothEmbedding_localDiffeomorph_comp_toHalfSpace_OED (halfSpaceBoundaryShift_OCX 0)
      halfSpaceBoundaryShift_OCX_two.1 halfSpaceBoundaryShift_OCX_two.2 hslice hι hιe
  convert hfinal using 1
  funext z
  exact (hιU (Φ₀ (0, z))).symm

section Carrier

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

/-- **The slice of a disk chart of a carrier of either kind**: a smooth embedding
`φ : ℝ¹ × D² → W` into the interior has the smooth-embedding slice `z ↦ φ (0, z)`. -/
theorem isSmoothEmbedding_slice_of_interior_OBD (W : CompactCarrier.{0})
    (φ : ℝ¹ × ClosedCell 2 → W.Carrier)
    (hφ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) W.model ∞ φ)
    (hr : range φ ⊆ (W.interior : Set W.Carrier)) :
    IsSmoothEmbedding (𝓡∂ 2) W.model ∞ (fun z : ClosedCell 2 => φ (0, z)) := by
  have hr' : ∀ p, φ p ∈ (W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) := fun p =>
    ⟨trivial, hr (mem_range_self p)⟩
  have hloc := isLocalDiffeomorph_pieceInterior_val W ⊤
  obtain ⟨D, hD⟩ : ∃ D : (W.pieceInterior ⊤) ≃ₘ⟮W.model, 𝓡 3⟯ (W.pieceInterior ⊤),
      ∀ x, D x = x :=
    ⟨DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞, fun _ => rfl⟩
  cases W with
  | mk k C o =>
    cases k
    · exact hφ.comp_of_smoothBoundary isSmoothEmbedding_diskSlice_OBD
    · exact isSmoothEmbedding_slice_halfSpace_OBD (interiorCharted_BDRY1 _)
        (interiorManifold_BDRY1 _) _ D Subtype.val hloc IsEmbedding.subtypeVal
        (fun x => congrArg Subtype.val (hD x)) φ hφ hr'

end Carrier

end DifferentialGeometry.Geometry.Collapse
