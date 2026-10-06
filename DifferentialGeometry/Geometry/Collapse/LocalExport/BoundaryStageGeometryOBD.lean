import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageProjsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRestrictOCL

/-!
# The stage geometry of the boundary landing without the cut facts (lane S-BD2)

Lane O-BD1 (by S-BD2, suffix `_OBD`), group G7b (stage lift of `hlift`, part 2). On the three stages
of G7a: the slim stage with its base sets `C₃`, slab image and face points (`ι⁻¹` of the
decomposition's sets), the cut choice `StageCutChoice74` (`K₃ = ι⁻¹ dec.slim.K₃`, `D₃`, `C₂`, `C₁`
the preimages of the images of the edge piece and the remainder), and the identification fields of
`BoundaryStageGeometry74b zc`: **`exists_stageGeometry74b_OBD`**
`Nonempty (BoundaryStageGeometry74b zc)` for EVERY zero / cusp exit `zc`.
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

/-- **Preimage of a relative interior under an embedding onto a set**. -/
theorem preimage_subset_interior_of_relInterior_OBD {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {ι : Y → Z} (hι : IsEmbedding ι) {R T K : Set Z} (hr : range ι = R)
    (hT : T ⊆ relInterior_BIF R K) : ι ⁻¹' T ⊆ interior (ι ⁻¹' K) := by
  let e : Y ≃ₜ R := hι.toHomeomorph.trans (Homeomorph.setCongr hr)
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hT hx
  have hyx' : y = e x := Subtype.ext hyx
  have h1 : e x ∈ interior (Subtype.val ⁻¹' K : Set R) := hyx' ▸ hy
  have h2 : x ∈ e ⁻¹' interior (Subtype.val ⁻¹' K : Set R) := h1
  rw [e.preimage_interior] at h2
  exact h2

/-- Compactness of the preimage of a compact subset of the range of an embedding. -/
theorem isCompact_preimage_of_subset_range_OBD {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {ι : Y → Z} (hι : IsEmbedding ι) {K : Set Z} (hK : IsCompact K)
    (hKr : K ⊆ range ι) : IsCompact (ι ⁻¹' K) :=
  hι.isInducing.isCompact_iff.2 (by rwa [image_preimage_eq_of_subset hKr])

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
/-- **The stage geometry of the boundary landing, without the cut facts** (G7b): for every
zero / cusp exit `zc`, the three stages of G7a, the slim base sets, the cut choice and all the
identification fields of `BoundaryStageGeometry74b zc`. -/
theorem exists_stageGeometry74b_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) : Nonempty (BoundaryStageGeometry74b zc) := by
  classical
  obtain ⟨Qc, ιc, hc, hrc⟩ := C.exists_circleStage_OBD dec
  obtain ⟨Qs, ιs, hs, hrs⟩ := C.exists_slimStage_OBD dec
  obtain ⟨E, ιe, he, hre, hh, hl⟩ := C.exists_edgeStage_OBD dec hint
  have hK₃sub : dec.slim.K₃ ⊆ range ιs := by
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    rw [hrs]
    exact dec.slim.arc_subset_base k hk
  have hpe : dec.slim.edgePiece ⊆ dec.bases.source 1 := inter_subset_right
  have hP₂ : C.toChain.stageMap 1 '' dec.slim.edgePiece ⊆ range ιe := by
    rw [hre, ← dec.bases.image_eq 1]
    exact image_mono hpe
  have hP₀ : C.toChain.stageMap 0 '' dec.slim.remainder ⊆ range ιc := by
    rw [hrc, ← dec.bases.image_eq 0]
    exact image_mono geom.pieces.2.2.2.1
  have hD₃ : IsCompact (dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc) := by
    have hKc : IsCompact dec.slim.K₃ := dec.slim.isCompact_K₃_BIFc
    have hcl : IsClosed C.toChain.M₁_BIFc := isOpen_interior.isClosed_compl
    have hKb : dec.slim.K₃ ⊆ dec.bases.base 2 := hrs ▸ hK₃sub
    have h1 : IsCompact (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' dec.slim.K₃) :=
      dec.bases.proper 2 _ hKb hKc
    have h2 : IsCompact (C.toChain.M₁_BIFc ∩ (dec.bases.source 2 ∩
        C.toChain.stageMap 2 ⁻¹' dec.slim.K₃)) := h1.inter_left hcl
    have h3 := h2.image (C.contMDiff_stageMap_OBD 2).continuous
    have h4 : C.toChain.stageMap 2 '' (C.toChain.M₁_BIFc ∩ (dec.bases.source 2 ∩
        C.toChain.stageMap 2 ⁻¹' dec.slim.K₃)) =
        dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc := by
      rw [← inter_assoc, image_inter_preimage, inter_comm]
      rfl
    rwa [h4] at h3
  let slim : SlimStage74 W :=
    { toStageProj74 := Qs
      C₃ := ιs ⁻¹' dec.bases.slimBaseDomain_BIFc
      slabImage := ιs ⁻¹' (C.toChain.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF))
      facePoints := ιs ⁻¹' (C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) }
  have hreq : slim.slabImage ∪ slim.facePoints ⊆ interior (ιs ⁻¹' dec.slim.K₃) :=
    union_subset
      (preimage_subset_interior_of_relInterior_OBD hs.emb hrs dec.slim.slabs_subset)
      (preimage_subset_interior_of_relInterior_OBD hs.emb hrs dec.slim.faces_subset)
  let cut : StageCutChoice74 (assembleBoundaryStages74 zc.zero zc.cusp slim E Qc) :=
    { K₃ := ιs ⁻¹' dec.slim.K₃
      D₃ := ιs ⁻¹' (dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc)
      C₂ := ιe ⁻¹' (C.toChain.stageMap 1 '' dec.slim.edgePiece)
      C₁ := ιc ⁻¹' (C.toChain.stageMap 0 '' dec.slim.remainder)
      edgeBaseOpen := if ιe ⁻¹' (C.toChain.stageMap 1 '' dec.slim.edgePiece) = ∅ then ⊥ else ⊤
      circleBaseOpen := ⊤
      K₃_compact := isCompact_preimage_of_subset_range_OBD hs.emb dec.slim.isCompact_K₃_BIFc hK₃sub
      D₃_compact := isCompact_preimage_of_subset_range_OBD hs.emb hD₃
        (inter_subset_left.trans hK₃sub)
      D₃_eq := rfl
      K₃_req := hreq
      K₃_faces := disjoint_left.2 fun x hx hf => hx.2 (hreq (Or.inr hf))
      C₂_sub := by
        intro x hx
        by_cases h : ιe ⁻¹' (C.toChain.stageMap 1 '' dec.slim.edgePiece) = ∅
        · exact absurd (h ▸ hx) (notMem_empty x)
        · simp only [h, ite_false]
          exact trivial
      C₁_sub := fun _ _ => trivial
      edgeBaseOpen_empty := fun h => by simp only [h, ite_true] }
  have hDimg : ιs '' cut.D₃ = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc :=
    image_preimage_eq_of_subset (inter_subset_left.trans hK₃sub)
  have hC₂img : ιe '' cut.C₂ = C.toChain.stageMap 1 '' dec.slim.edgePiece :=
    image_preimage_eq_of_subset hP₂
  have hC₁img : ιc '' cut.C₁ = C.toChain.stageMap 0 '' dec.slim.remainder :=
    image_preimage_eq_of_subset hP₀
  have hep : dec.slim.edgePiece = dec.bases.edgeParent ∩
      C.toChain.stageMap 1 ⁻¹' (ιe '' cut.C₂) ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} := by
    have h1 : dec.slim.edgePiece = dec.bases.source 1 ∩
        C.toChain.stageMap 1 ⁻¹' (C.toChain.stageMap 1 '' dec.slim.edgePiece) :=
      dec.edge.saturated
    have h2 : dec.bases.source 1 =
        dec.bases.parent.edgeParent ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} :=
      dec.bases.parent.edgeParent_cut
    rw [hC₂img]
    ext x
    have hx2 : x ∈ dec.bases.source 1 ↔
        x ∈ dec.bases.parent.edgeParent ∧ C.toChain.heightRatio x ≤ 4 * Δ := by
      rw [h2]
      rfl
    have hx1 := Set.ext_iff.1 h1 x
    simp only [mem_inter_iff, mem_preimage, Set.mem_ofPred_eq] at hx1 ⊢
    tauto
  let G : BoundaryStageGeometry74b zc :=
    { slim := slim
      edge := E
      circle := Qc
      ιslim := ιs
      ιedge := ιe
      ιcircle := ιc
      slim_ident := hs
      edge_ident := he
      circle_ident := hc
      edge_range := hre.subset
      circle_range := hrc.subset
      edge_height := hh
      edge_level := hl
      cut := cut
      cut_D₃ := hDimg
      cut_C₂ := hC₂img
      cut_C₁ := hC₁img
      comp := (actualComponentEquiv_OCL ιs hs.emb cut.D₃).trans
        (actualComponentEquivOfEq_OCL hDimg)
      comp_eq := fun c => by simp
      edgePiece_eq := hep }
  exact ⟨G⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
