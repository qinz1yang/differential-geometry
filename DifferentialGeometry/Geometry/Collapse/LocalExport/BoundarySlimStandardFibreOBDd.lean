import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimSurfaceSubmersionOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorEmbeddingOBDd

/-!
# The standard whole slim fibres over `W°` (lane S-BD2d, suffix `_OBDd`), group G10b

Lane O-BD1 (by S-BD2d), hlift, `SlimCutPieces74`. For the slim stage over `W°`
(`exists_slimSubmersion_OBDd`), every point `y` of `B₃` carries a `StandardWholeSurfaceFibre_EFE`
(a smooth embedding of the model surface onto the whole fibre) of the sphere or of the torus, from
the slim product chart of the whole-fibre layer: the slice `z ↦ φ (0, z)` of the smooth embedding
`φ : ℝ × F → W` with values in `W°` (`isSmoothEmbedding_toInterior_OBDd`, then the slice of a
product).

* `BoundaryGaf02ChainE.standardFibre_of_chart_OBDd`: from ONE product chart at `y` (any fibre
  model `F`);
* `BoundaryGaf02ChainE.exists_standardFibre_OBDd`: the sphere or torus fibre at every `y ∈ B₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **A standard whole slim fibre from one product chart** (fibre model `F`). -/
theorem standardFibre_of_chart_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x) {EF HF : Type} [NormedAddCommGroup EF]
    [NormedSpace ℝ EF] [FiniteDimensional ℝ EF] [TopologicalSpace HF]
    {IF : ModelWithCorners ℝ EF HF} [IF.Boundaryless] {F : Type}
    [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hchart : SmoothProductChartAt_BIFc W.model IF (F := F) 1 (C.toChain.stageMap 2)
      (dec.bases.source 2) (dec.bases.base 2) y) :
    Nonempty (StandardWholeSurfaceFibre_EFE P IF F y) := by
  obtain ⟨σ, φ, O, h0, hs, he, hi, hO, hr, hφ, hrφ, hf⟩ := hchart
  have hint : ∀ p : ℝ¹ × F, φ p ∈ (W.pieceInterior ⊤ : Set W.Carrier) := fun p => by
    have h : φ p ∈ range φ := mem_range_self p
    rw [hrφ] at h
    exact C.source_two_subset_pieceInterior_OBDd dec h.1
  have hφ' := isSmoothEmbedding_toInterior_OBDd W φ hφ hint
  have hslice : IsSmoothEmbedding IF ((𝓡 1).prod IF) ∞ (fun z : F => ((0 : ℝ¹), z)) :=
    isSmoothEmbedding_const_prodMk_of_centered_chart (0 : ℝ¹) (chartAt ℝ¹ (0 : ℝ¹))
      (mem_chart_source ℝ¹ (0 : ℝ¹)) (IsManifold.chart_mem_maximalAtlas (0 : ℝ¹)) (by simp)
  have hemb := Manifold.IsSmoothEmbedding.comp hφ' hslice (by simp)
  refine ⟨{ emb := fun z => (⟨φ (0, z), hint (0, z)⟩ : W.pieceInterior ⊤)
            isSmoothEmbedding := hemb
            range_eq := ?_ }⟩
  have hrange : range (fun z : F => φ (0, z)) =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} :=
    range_slice_eq_fibre_BIFc h0 he.injective hrφ hf
  have hyB : y ∈ dec.bases.base 2 := by
    have h : y ∈ range σ := ⟨0, h0⟩
    rw [hr] at h
    exact h.1
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have h1 : φ (0, z) ∈ range (fun z : F => φ (0, z)) := mem_range_self z
    rw [hrange] at h1
    change P.toFun ⟨φ (0, z), hint (0, z)⟩ = y
    rw [hP]
    exact h1.2
  · intro hx
    have hx' : C.toChain.stageMap 2 x.1 = y := by
      have h2 : P.toFun x = y := hx
      rw [hP] at h2
      exact h2
    have hxs : x.1 ∈ dec.bases.source 2 :=
      C.mem_source_of_stageMap_mem_base_OBDd dec (hx' ▸ hyB)
    have hmem : x.1 ∈ range (fun z : F => φ (0, z)) := by
      rw [hrange]
      exact ⟨hxs, hx'⟩
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, Subtype.ext hz⟩

include C in
/-- **Every point of the slim base carries a standard whole fibre**, a sphere or a torus. -/
theorem exists_standardFibre_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ dec.bases.base 2) :
    Nonempty (StandardWholeSurfaceFibre_EFE P (𝓡 2) ClosureSphere.{0} y) ∨
      Nonempty (StandardWholeSurfaceFibre_EFE P torusModel Torus y) := by
  rcases dec.fibres.slim_chart y hy with h | h
  · exact Or.inl (C.standardFibre_of_chart_OBDd dec P hP h)
  · exact Or.inr (C.standardFibre_of_chart_OBDd dec P hP h)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
