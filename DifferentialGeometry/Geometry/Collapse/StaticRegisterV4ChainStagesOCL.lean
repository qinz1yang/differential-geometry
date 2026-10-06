import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimStageOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGoodCutOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeStageRecord74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCircleStageRecord74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExportsU74

/-!
# Draft 74 CL0, G2: the closed stage geometry at the produced cut choice `D_R`

Lane O-CL0 (`_OCL`), G2. The binding of draft 74 §4.1 (`A`, `D`) to the closed source `S` at the
produced cut choice `D_R = S.goodCut_OCL B hT hεr` (G1), in the revised landing's vocabulary
(S-LANDING G2d, `ClosedStageGeometryU74`):

* the three ACTUAL stages, each the final map `q_j = π_j ∘ E` through the ONE `M.ψ`:
  - slim: `slimStage_OCL S A` = this lane's slim stage `f₃ : M.ψ(U₃) → W₃` restricted to the
    good open base `W₃ ∩ R₃` (whole `f₃`-preimage; every fibre lies in `U₃`, ZSP35's chart
    localization), with `C₃`, the slab image and `F₃` read on the chain;
  - edge: lane S-REG-CHAIN2's `edgeStage74 S A` (`q₁ : M.ψ(U₂) → W₂`, height `A/s`, level `4Δ`),
    identified on the open ambient parent `U₂` (`StageIdentU_LND74`);
  - circle: lane S-REG-CHAIN2's `circleStage74 S A` restricted to the good open base `W₁ ∩ R₁`
    (whole circles; every fibre lies in `U₀`, GAF07's localization);
* the whole-fibre identifications `slimStage_ident_OCL`, `edgeStage_ident_OCL` (on `U₂`),
  `circleStage_ident_OCL` — the `slim_ident / edge_ident / circle_ident` fields of
  `ClosedStageGeometryU74`.

NOT here (parked, build-logs/scratch/O-CL0/StagesOCL-full-parked.lean): the cut choice on these
stages carried from `D_R` (`cutAt_OCL`) and the record `ClosedStageGeometryU74` at `D_R`.
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-! ## The good open bases and the restricted stages -/

/-- The good open slim base `W₃ ∩ R₃` (`slimBs_ZSP35`) as an open subset of `W₃`. -/
def slimBsOpens_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    TopologicalSpace.Opens ↥(S.chain.toChain.finalBase_BAS 2) :=
  ⟨Subtype.val ⁻¹' gaf07SlimRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets,
    (isOpen_gaf07SlimRatio_ZSP35 _).preimage continuous_subtype_val⟩

/-- The good open circle base `W₁ ∩ R₁` as an open subset of `W₁`. -/
def circleBsOpens_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    TopologicalSpace.Opens ↥(S.chain.toChain.finalBase_BAS 0) :=
  ⟨Subtype.val ⁻¹' gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets,
    (isOpen_gaf07CircleRatio_GAFC _).preimage continuous_subtype_val⟩

/-- The inclusion of the slim base `W₃ ∩ R₃` into the block space. -/
def slimι_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    S.slimBsOpens_OCL → S.blockSpace_R74 :=
  fun b => ((b : ↥(S.chain.toChain.finalBase_BAS 2)) : S.blockSpace_R74)

/-- The inclusion of the circle base `W₁ ∩ R₁` into the block space. -/
def circleι_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    S.circleBsOpens_OCL → S.blockSpace_R74 :=
  fun b => ((b : ↥(S.chain.toChain.finalBase_BAS 0)) : S.blockSpace_R74)

theorem slimι_isEmbedding_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    Topology.IsEmbedding S.slimι_OCL :=
  Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

theorem circleι_isEmbedding_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    Topology.IsEmbedding S.circleι_OCL :=
  Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

/-- The slim base inclusion has range `W₃ ∩ R₃`. -/
theorem range_slimι_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    range S.slimι_OCL = S.chain.slimBs_ZSP35 := by
  ext w
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.1.2, b.2⟩
  · rintro ⟨hW, hR⟩
    exact ⟨⟨⟨w, hW⟩, hR⟩, rfl⟩

/-- The circle base inclusion has range `R₁ ∩ W₁` (the circle base of `D_R`). -/
theorem range_circleι_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    range S.circleι_OCL =
      gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets ∩
      S.chain.toChain.finalBase_BAS 0 := by
  ext w
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.2, b.1.2⟩
  · rintro ⟨hR, hW⟩
    exact ⟨⟨⟨w, hW⟩, hR⟩, rfl⟩

/-- **The slim stage of the rows**: `f₃ ∘ M.ψ⁻¹` restricted to the good open base `W₃ ∩ R₃`, with
the chain's `C₃`, slab image and face points `F₃` read on the base. -/
def slimStage_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (A : SmoothStageBases74 S) :
    SlimStage74 W :=
  { (S.slimStageProj_OCL A).restrictStage_OCL S.slimBsOpens_OCL with
    C₃ := S.slimι_OCL ⁻¹' S.chain.slimC3_ZSP35
    slabImage := S.slimι_OCL ⁻¹' S.chain.toChain.slimSlabImage_ZSP35
    facePoints := S.slimι_OCL ⁻¹' S.chain.slimFacePoints_ZSP35 }

/-- **The circle stage of the rows**: `q₀ ∘ M.ψ⁻¹` restricted to the good open base `W₁ ∩ R₁`. -/
def circleStage_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (A : SmoothStageBases74 S) :
    StageProj74 W 2 :=
  (S.circleStage74 A).restrictStage_OCL S.circleBsOpens_OCL

/-! ## The whole-fibre identifications -/

/-- **The slim stage IS `f₃` with whole fibres** (`f₃ p ∈ W₃ ∩ R₃` puts `p` in `U₃`: ZSP35's chart
localization `slim_chart_local_ZSP35`). -/
theorem slimStage_ident_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) :
    StageIdent_LND74 M.ψ.toEquiv (S.slimStage_OCL A).toStageProj74 S.chain.slimMap_ZSP35
      S.slimι_OCL := by
  refine stageIdent_restrict_OCL (S.slimStageProj_ident_OCL A) S.slimBsOpens_OCL ?_
  rintro p ⟨b, hb, hbp⟩
  have hp : S.chain.slimMap_ZSP35 p ∈ S.chain.slimBs_ZSP35 := by
    rw [← hbp]
    exact ⟨b.2, hb⟩
  obtain ⟨i, hY, -⟩ := S.chain.slim_chart_local_ZSP35 hp
  exact ⟨i, hY⟩

/-- **The edge stage IS `q₁` on the open ambient parent `U₂`** (`StageIdentU_LND74`). -/
theorem edgeStage_ident_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) :
    StageIdentU_LND74 M.ψ.toEquiv (S.edgeStage74 A).toStageProj74
      (S.chain.toGaf02ChainE.cutQ_R74 1)
      (fun b : ↥(S.chain.toChain.finalBase_BAS 1) => (b : S.blockSpace_R74))
      (gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1) where
  emb := Topology.IsEmbedding.subtypeVal
  proj_eq := fun _ => rfl
  parent_eq := rfl

/-- The (unrestricted) circle stage is `q₀` on its parent `M.ψ(U₀)`. -/
theorem circleStage74_identU_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) :
    StageIdentU_LND74 M.ψ.toEquiv (S.circleStage74 A) (S.chain.toGaf02ChainE.cutQ_R74 0)
      (fun b : ↥(S.chain.toChain.finalBase_BAS 0) => (b : S.blockSpace_R74))
      (gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 0) where
  emb := Topology.IsEmbedding.subtypeVal
  proj_eq := fun _ => rfl
  parent_eq := rfl

/-- **The circle stage IS `q₀` with whole fibres** (`q₀ p ∈ W₁ ∩ R₁` puts `p` in `U₀`: GAF07's
circle localization, through `goodCut_circleSource_OCL`). -/
theorem circleStage_ident_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) :
    StageIdent_LND74 M.ψ.toEquiv (S.circleStage_OCL A) (S.chain.toGaf02ChainE.cutQ_R74 0)
      S.circleι_OCL := by
  refine stageIdent_restrict_OCL (S.circleStage74_identU_OCL A) S.circleBsOpens_OCL ?_
  rintro p ⟨b, hb, hbp⟩
  refine (S.goodCut_circleSource_OCL B hT hεr).2 ?_
  change S.chain.toGaf02ChainE.cutQ_R74 0 p ∈ (S.goodCut_OCL B hT hεr).circleBaseOpen
  rw [(S.goodCut_bases_OCL B hT hεr).2.2, ← hbp]
  exact ⟨hb, b.2⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
