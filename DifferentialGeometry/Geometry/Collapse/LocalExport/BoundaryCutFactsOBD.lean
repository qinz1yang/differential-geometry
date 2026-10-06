import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometryOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageProjsOBD

/-!
# Cut facts of the boundary landing that follow from the stage geometry (lane S-BD2)

Lane O-BD1 (by S-BD2, suffix `_OBD`), group G7c (hlift, the cut facts `H`, first part). For ANY
`P : BoundaryStageGeometry74b zc` (the stage geometry of G7b, whatever the good open bases):

* `StageProj74` restricted to an open base: the image of the whole preimage of `K` is
  `src ∩ q⁻¹(ι '' K)` (`image_restrictProj_OBD`);
* `BoundaryStageGeometry74b.circle_proper_OBD` / `edge_proper_OBD`: the `proper` fields of
  `CircleCutFacts74` / `EdgeCutFacts74`, from the properness of the stage maps on the sources
  (`Bs.proper`) and the whole-preimage descriptions of the sources.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

open Set Function Metric Topology

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}


omit [ConnectedSpace W.Carrier] in
/-- **The image of the whole preimage of `K` under the restricted projection.** -/
theorem image_restrictProj_OBD {k : ℕ} {Q : StageProj74 W k} {Bs : Type*} [TopologicalSpace Bs]
    {q : W.Carrier → Bs} {ι : Q.Base → Bs} {src : Set W.Carrier}
    (h : StageIdentSrc_LND74 Q q ι src) (V : TopologicalSpace.Opens Q.Base) (K : Set V) :
    Subtype.val '' (Q.restrictProj V ⁻¹' K) = src ∩ q ⁻¹' (ι '' (Subtype.val '' K)) := by
  rw [← stageSetSrc_LND74 h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyp, hyV⟩ := Q.exists_of_mem_restrictParent y.2
    refine ⟨hyp, ?_⟩
    exact ⟨_, hy, rfl⟩
  · rintro ⟨hx, k, hk, hkx⟩
    refine ⟨⟨x, Q.mem_restrictParent_of hx (hkx ▸ k.2)⟩, ?_, rfl⟩
    have : Q.restrictProj V ⟨x, Q.mem_restrictParent_of hx (hkx ▸ k.2)⟩ = k :=
      Subtype.ext hkx.symm
    rw [mem_preimage, this]
    exact hk

section Proper

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
  {dec : BoundaryActualDecompositionV2b C} {zc : BoundaryZeroCuspExit74b C dec}
  (P : BoundaryStageGeometry74b zc)

/-- **`CircleCutFacts74.proper` for the produced stages**: the restricted circle projection is
proper over the good open base (whole preimages of compact sets are compact). -/
theorem BoundaryStageGeometry74b.circle_proper_OBD :
    ∀ K : Set P.cut.circleBaseOpen, IsCompact K →
      IsCompact (Subtype.val ''
          (P.stageGeometry.circle.restrictProj P.cut.circleBaseOpen ⁻¹' K)) := by
  intro K hK
  rw [image_restrictProj_OBD P.circle_ident]
  have h1 : IsCompact (P.ιcircle '' (Subtype.val '' K)) :=
    (hK.image continuous_subtype_val).image P.circle_ident.emb.continuous
  have h2 : P.ιcircle '' (Subtype.val '' K) ⊆ dec.bases.base 0 := by
    rintro _ ⟨z, -, rfl⟩
    exact P.circle_range ⟨z, rfl⟩
  exact dec.bases.proper 0 _ h2 h1

/-- **`EdgeCutFacts74.proper` for the produced stages**: the restricted edge projection with the
height cut is proper over the good open base. -/
theorem BoundaryStageGeometry74b.edge_proper_OBD :
    ∀ K : Set P.cut.edgeBaseOpen, IsCompact K →
      IsCompact (Subtype.val '' {x : P.cut.edgeSource |
        P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen x ∈ K ∧
          P.cut.edgeHeight x ≤ P.stageGeometry.edge.level}) := by
  intro K hK
  have h1 : IsCompact (P.ιedge '' (Subtype.val '' K)) :=
    (hK.image continuous_subtype_val).image P.edge_ident.emb.continuous
  have h2 : P.ιedge '' (Subtype.val '' K) ⊆ dec.bases.base 1 := by
    rintro _ ⟨z, -, rfl⟩
    exact P.edge_range ⟨z, rfl⟩
  have hc := dec.bases.proper 1 _ h2 h1
  have hcut : dec.bases.source 1 = dec.bases.parent.edgeParent ∩
      {p | C.heightRatio p ≤ 4 * Δ} := dec.bases.parent.edgeParent_cut
  convert hc using 1
  ext x
  constructor
  · rintro ⟨y, ⟨hyK, hyh⟩, rfl⟩
    have hy : y.1 ∈ Subtype.val '' (P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen ⁻¹' K) :=
      ⟨y, hyK, rfl⟩
    rw [image_restrictProj_OBD P.edge_ident] at hy
    refine ⟨?_, hy.2⟩
    rw [hcut]
    refine ⟨hy.1, ?_⟩
    have h3 : P.cut.edgeHeight y = C.heightRatio y.1 := P.edge_height _
    have h4 : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
    change C.heightRatio y.1 ≤ 4 * Δ
    rw [← h3, ← h4]
    exact hyh
  · rintro ⟨hx1, hf⟩
    rw [hcut] at hx1
    have hx : x ∈ dec.bases.parent.edgeParent ∩
        C.stageMap 1 ⁻¹' (P.ιedge '' (Subtype.val '' K)) := ⟨hx1.1, hf⟩
    rw [← image_restrictProj_OBD P.edge_ident] at hx
    obtain ⟨y, hyK, rfl⟩ := hx
    refine ⟨y, ⟨hyK, ?_⟩, rfl⟩
    have h3 : P.cut.edgeHeight y = C.heightRatio y.1 := P.edge_height _
    have h4 : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
    rw [h3, h4]
    exact hx1.2

end Proper

section Compact

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}


namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}

include C in
/-- **`CircleCutFacts74.cbase_compact` for the produced stages** (`R_c` is compact). -/
theorem circle_cbase_compact_OBD (P : BoundaryStageGeometry74b zc)
    (geom : BoundaryGeometricExports74b C.toChain dec) :
    IsCompact (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen) := by
  have h1 : IsCompact P.cut.C₁ := by
    refine P.circle_ident.emb.isInducing.isCompact_iff.2 ?_
    rw [P.cut_C₁]
    exact geom.pieces.2.1.image (C.contMDiff_stageMap_OBD 0).continuous
  refine Topology.IsEmbedding.subtypeVal.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset (by rw [Subtype.range_coe_subtype]; exact P.cut.C₁_sub)]
  exact h1

include C in
/-- **`EdgeCutFacts74.cbase_compact` for the produced stages** (the edge piece is compact). -/
theorem edge_cbase_compact_OBD (P : BoundaryStageGeometry74b zc)
    (geom : BoundaryGeometricExports74b C.toChain dec) :
    IsCompact (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen) := by
  have h1 : IsCompact P.cut.C₂ := by
    refine P.edge_ident.emb.isInducing.isCompact_iff.2 ?_
    rw [P.cut_C₂]
    exact geom.pieces.1.image (C.contMDiff_stageMap_OBD 1).continuous
  refine Topology.IsEmbedding.subtypeVal.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset (by rw [Subtype.range_coe_subtype]; exact P.cut.C₂_sub)]
  exact h1

end BoundaryGaf02ChainE

end Compact

end DifferentialGeometry.Geometry.Collapse
