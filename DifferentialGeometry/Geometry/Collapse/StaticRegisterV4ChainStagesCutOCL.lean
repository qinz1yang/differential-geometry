import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainStagesOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCutBases74

/-!
# Draft 74 CL0, G3a: the closed stage geometry record at the produced cut choice `D_R`

Lane O-CL1 (`_OCL`, successor of O-CL0), group G3a. On the three actual stages of O-CL0 G2a
(`slimStage_OCL`, `edgeStage74`, `circleStage_OCL`) and the produced cut choice
`D_R = S.goodCut_OCL B hT hεr` (O-CL0 G1):

* **`cutAt_OCL`**: the cut choice on the stages carried from `D_R` (`K₃, D₃, C₂, C₁` pulled back
  along the base inclusions, `edgeBaseOpen = B₂` (or `⊥` when `C₂ = ∅`), `circleBaseOpen` the
  whole restricted base `W₁ ∩ R₁`), with the `K₃` contract read on `W₃ ∩ R₃`;
* **`closedStagesAt_OCL S B hT hεr A zero : ClosedStageGeometryU74 (S.goodCut_OCL B hT hεr) zero`**:
  the revised stage-geometry record (S-LANDING G2d) with all its identification fields
  (whole-fibre identifications, `C₃`, slab, faces, height `A/s`, level `4Δ`, the cut sets, the
  open bases, the components of `D₃`), for ANY zero exit `zero`.

Universe: `W : CompactCarrier.{0}` (as the edge / circle stage records).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-! ## The cut choice on the stages, carried from `D_R` -/

section Cut

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- The slim base sets of `D_R` lie in `W₃ ∩ R₃`. -/
theorem goodCut_slim_subset_OCL :
    (S.goodCut_OCL B hT hεr).K₃.carrier ⊆ range S.slimι_OCL ∧
      (S.goodCut_OCL B hT hεr).D₃.carrier ⊆ range S.slimι_OCL ∧
      S.chain.slimC3_ZSP35 ⊆ range S.slimι_OCL ∧
      S.chain.toChain.slimSlabImage_ZSP35 ∪ S.chain.slimFacePoints_ZSP35 ⊆ range S.slimι_OCL := by
  rw [S.range_slimι_OCL]
  refine ⟨(S.goodCut_OCL B hT hεr).K₃.subset_base, (S.goodCut_OCL B hT hεr).D₃.subset_base, ?_,
    ?_⟩
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact hx
  · intro w hw
    obtain ⟨y, -, rfl⟩ := (S.goodCut_OCL B hT hεr).K₃_req hw
    exact y.2

/-- The map from the stage base `W₃ ∩ R₃` to the subtype `slimBs_ZSP35` of the block space. -/
def slimBsMap_OCL : S.slimBsOpens_OCL → S.chain.slimBs_ZSP35 :=
  fun b => ⟨S.slimι_OCL b, by
    rw [← S.range_slimι_OCL]
    exact mem_range_self b⟩

theorem continuous_slimBsMap_OCL : Continuous S.slimBsMap_OCL :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

/-- From the block space's relative interior to the interior on the stage base `W₃ ∩ R₃`. -/
theorem slim_mem_interior_OCL {Kc : Set S.blockSpace_R74} {x : S.slimBsOpens_OCL}
    (hx : S.slimι_OCL x ∈ Subtype.val '' interior (Subtype.val ⁻¹' Kc : Set S.chain.slimBs_ZSP35)) :
    x ∈ interior (S.slimι_OCL ⁻¹' Kc) := by
  obtain ⟨y, hy, hyx⟩ := hx
  have hex : S.slimBsMap_OCL x = y := Subtype.ext hyx.symm
  have h1 : x ∈ S.slimBsMap_OCL ⁻¹' interior (Subtype.val ⁻¹' Kc : Set S.chain.slimBs_ZSP35) := by
    rw [mem_preimage, hex]
    exact hy
  exact preimage_interior_subset_interior_preimage S.continuous_slimBsMap_OCL h1

/-- The slim `K₃` contract on the stage base: `slab ∪ F₃ ⊆ int K₃`. -/
theorem cut_K₃_req_OCL :
    S.slimι_OCL ⁻¹' S.chain.toChain.slimSlabImage_ZSP35 ∪
        S.slimι_OCL ⁻¹' S.chain.slimFacePoints_ZSP35 ⊆
      interior (S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier) := by
  intro x hx
  rw [← preimage_union] at hx
  exact S.slim_mem_interior_OCL ((S.goodCut_OCL B hT hεr).K₃_req hx)

/-- The slim `K₃` contract on the stage base: `∂K₃ ∩ F₃ = ∅`. -/
theorem cut_K₃_faces_OCL :
    Disjoint (frontier (S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier))
      (S.slimι_OCL ⁻¹' S.chain.slimFacePoints_ZSP35) := by
  rw [Set.disjoint_left]
  intro x hxf hxF
  have hcl : IsClosed (S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier) :=
    (S.goodCut_OCL B hT hεr).K₃.isCompact_carrier_BCF.isClosed.preimage
      S.slimι_isEmbedding_OCL.continuous
  have hxK : x ∈ S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier :=
    hcl.closure_subset (frontier_subset_closure hxf)
  have hint : S.slimι_OCL x ∈ Subtype.val '' interior (Subtype.val ⁻¹'
      (S.goodCut_OCL B hT hεr).K₃.carrier : Set S.chain.slimBs_ZSP35) := by
    by_contra hn
    exact Set.disjoint_left.mp (S.goodCut_OCL B hT hεr).K₃_faces ⟨hxK, hn⟩ hxF
  exact hxf.2 (S.slim_mem_interior_OCL hint)

/-- The edge base of `D_R` as an open of `W₂` is `⊥` when its `C₂` (read on `W₂`) is empty. -/
theorem cut_edgeBaseOpen_empty_OCL
    (h : (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).C₂ : Set ↥(S.chain.toChain.finalBase_BAS 1)) =
      ∅) : (S.goodCut_OCL B hT hεr).edgeBaseOpens_R74 = ⊥ := by
  have hC : (S.goodCut_OCL B hT hεr).C₂ = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    have hwW : w ∈ S.chain.toChain.finalBase_BAS 1 :=
      (S.chain.toGaf02ChainE.cutC2_subset_R74 _ hw).1
    have hmem : (⟨w, hwW⟩ : ↥(S.chain.toChain.finalBase_BAS 1)) ∈
        (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).C₂ : Set ↥(S.chain.toChain.finalBase_BAS 1)) :=
      hw
    rw [h] at hmem
    exact hmem
  have hE := (S.goodCut_OCL B hT hεr).edgeBaseOpen_empty hC
  apply TopologicalSpace.Opens.ext
  ext w
  change w.1 ∈ (S.goodCut_OCL B hT hεr).edgeBaseOpen ↔ w ∈ (∅ : Set _)
  rw [hE]
  exact ⟨fun hw => absurd hw (notMem_empty _), fun hw => absurd hw (notMem_empty _)⟩

/-- **The cut choice on the actual stages**, carried from `D_R` (for any zero domains `Zr`). -/
def cutAt_OCL (A : SmoothStageBases74 S) (Zr : ZeroDomains W) :
    StageCutChoice74 (assembleStages74 M Zr (S.slimStage_OCL A) (S.edgeStage74 A)
      (S.circleStage_OCL A)) where
  K₃ := S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier
  D₃ := S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier
  C₂ := (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).C₂ : Set ↥(S.chain.toChain.finalBase_BAS 1))
  C₁ := S.circleι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).C₁
  edgeBaseOpen := (S.goodCut_OCL B hT hεr).edgeBaseOpens_R74
  circleBaseOpen := ⊤
  K₃_compact := (S.slimι_isEmbedding_OCL.isInducing.isCompact_preimage_iff
    (S.goodCut_slim_subset_OCL B hT hεr).1).2 (S.goodCut_OCL B hT hεr).K₃.isCompact_carrier_BCF
  D₃_compact := (S.slimι_isEmbedding_OCL.isInducing.isCompact_preimage_iff
    (S.goodCut_slim_subset_OCL B hT hεr).2.1).2 (S.goodCut_OCL B hT hεr).D₃.isCompact_carrier_BCF
  D₃_eq := by
    change S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier =
      S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier ∩
        S.slimι_OCL ⁻¹' S.chain.slimC3_ZSP35
    rw [(S.goodCut_OCL B hT hεr).D₃_eq, preimage_inter]
  K₃_req := S.cut_K₃_req_OCL B hT hεr
  K₃_faces := S.cut_K₃_faces_OCL B hT hεr
  C₂_sub := fun _ hw => (S.goodCut_OCL B hT hεr).edgeBaseOpen_sub hw
  C₁_sub := fun _ _ => trivial
  edgeBaseOpen_empty := S.cut_edgeBaseOpen_empty_OCL B hT hεr

/-! ## The stage geometry record at `D_R` -/

/-- `C₂` of `D_R`, read back from `W₂`. -/
theorem cut_C₂_image_OCL :
    Subtype.val '' (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).C₂ :
      Set ↥(S.chain.toChain.finalBase_BAS 1)) = (S.goodCut_OCL B hT hεr).C₂ := by
  rw [Subtype.image_preimage_coe]
  exact inter_eq_right.mpr fun w hw => (S.chain.toGaf02ChainE.cutC2_subset_R74 _ hw).1

/-- `C₁` of `D_R` lies in the circle stage base `W₁ ∩ R₁`. -/
theorem cut_C₁_subset_OCL : (S.goodCut_OCL B hT hεr).C₁ ⊆ range S.circleι_OCL := by
  rw [S.range_circleι_OCL, ← (S.goodCut_bases_OCL B hT hεr).2.2]
  exact (S.goodCut_OCL B hT hεr).circleBaseOpen_sub

/-- The circle stage base is the whole circle base of `D_R`. -/
theorem cut_circleOpen_OCL :
    S.circleι_OCL '' ((⊤ : TopologicalSpace.Opens S.circleBsOpens_OCL) : Set _) =
      (S.goodCut_OCL B hT hεr).circleBaseOpen := by
  rw [TopologicalSpace.Opens.coe_top, image_univ, S.range_circleι_OCL,
    (S.goodCut_bases_OCL B hT hεr).2.2]

/-- The slim `D₃` of the carried cut is read back as the `D₃` of `D_R`. -/
theorem cut_D₃_image_OCL :
    S.slimι_OCL '' (S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier) =
      (S.goodCut_OCL B hT hεr).D₃.carrier :=
  image_preimage_eq_of_subset (S.goodCut_slim_subset_OCL B hT hεr).2.1

/-- **The revised stage-geometry record at the produced cut choice `D_R`** (S-LANDING G2d
`ClosedStageGeometryU74`), for any zero exit: the three actual stages (O-CL0 G2a), their
whole-fibre identifications, `C₃` / slab / faces, height `A/s`, level `4Δ`, the carried cut
`cutAt_OCL` identified set by set with `D_R`, and the components of `D₃`. -/
def closedStagesAt_OCL (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S) :
    ClosedStageGeometryU74 (S.goodCut_OCL B hT hεr) zero where
  slim := S.slimStage_OCL A
  edge := S.edgeStage74 A
  circle := S.circleStage_OCL A
  ιslim := S.slimι_OCL
  ιedge := fun b : ↥(S.chain.toChain.finalBase_BAS 1) => (b : S.blockSpace_R74)
  ιcircle := S.circleι_OCL
  slim_ident := S.slimStage_ident_OCL A
  edge_ident := S.edgeStage_ident_OCL A
  circle_ident := S.circleStage_ident_OCL A B hT hεr
  slim_C₃ := image_preimage_eq_of_subset (S.goodCut_slim_subset_OCL B hT hεr).2.2.1
  slim_slab := image_preimage_eq_of_subset
    (subset_union_left.trans (S.goodCut_slim_subset_OCL B hT hεr).2.2.2)
  slim_faces := image_preimage_eq_of_subset
    (subset_union_right.trans (S.goodCut_slim_subset_OCL B hT hεr).2.2.2)
  edge_height := fun _ => rfl
  edge_level := rfl
  cut := S.cutAt_OCL B hT hεr A zero.rows
  cut_K₃ := image_preimage_eq_of_subset (S.goodCut_slim_subset_OCL B hT hεr).1
  cut_D₃ := S.cut_D₃_image_OCL B hT hεr
  cut_C₂ := S.cut_C₂_image_OCL B hT hεr
  cut_C₁ := image_preimage_eq_of_subset (S.cut_C₁_subset_OCL B hT hεr)
  cut_edgeOpen := (S.goodCut_OCL B hT hεr).edgeBaseOpens_val_R74
  cut_circleOpen := S.cut_circleOpen_OCL B hT hεr
  comp := (actualComponentEquiv_OCL S.slimι_OCL S.slimι_isEmbedding_OCL
      (S.slimι_OCL ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier)).trans
    (actualComponentEquivOfEq_OCL (S.cut_D₃_image_OCL B hT hεr))
  comp_eq := fun c => (actualComponentEquivOfEq_OCL_val (S.cut_D₃_image_OCL B hT hεr)
    (actualComponentEquiv_OCL S.slimι_OCL S.slimι_isEmbedding_OCL _ c)).symm

/-- The record's stage geometry is the assembled one on the zero exit's domains. -/
theorem closedStagesAt_A_OCL (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S) :
    (S.closedStagesAt_OCL B hT hεr A zero).A =
      assembleStages74 M zero.rows (S.slimStage_OCL A) (S.edgeStage74 A) (S.circleStage_OCL A) :=
  rfl

end Cut

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
