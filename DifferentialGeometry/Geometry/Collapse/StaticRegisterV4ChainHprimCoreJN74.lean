import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesAssembleJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageHprimJN74

/-!
# Draft 74, the endpoint primitives at `D_R`: the edge coordinate, the disks and `C₂`

Lane S-JUNCTIONS (by S-JUNCTIONS5), G32 (suffix `_JN74`). On the stage geometry at `D_R`:

* `edgeBlockProj_of_proj_JN74`: `ι(q₁ x) = π₂E(ψ⁻¹ x)` on the edge source of the rows;
* `disk_eq_image_JN74`: the end disk is `ψ` of the chain's `{q₁ = ι c, T ≤ level}`;
* `mem_cbase_iff_disk_JN74`: a point of the edge base is in `C₂` iff its disk meets `M₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- **`ι(q₁ x) = π₂E(ψ⁻¹ x)` on the edge source of the rows.** -/
theorem edgeBlockProj_of_proj_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (x : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).source) :
    S.chain.toGaf02ChainE.edgeValB_EFE
      (TopologicalSpace.Opens.inclusion (S.edgeBaseOpen_le_JN74 B hT hεr)
        ((edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).proj x)) =
      S.chain.toGaf02ChainE.edgeBlockProj_EFE (M.ψ.symm x.1) :=
  (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.proj_eq
    ⟨x.1, (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictParent_le _ x.2⟩

/-- **A point over the good edge base below the level lies in the chain's edge source and region
`X₂`** (`T ≤ 4Δ`). -/
theorem edgeSource_of_fibre_JN74
    (c : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) {y : M.X}
    (hq : S.chain.toGaf02ChainE.cutQ_R74 1 y = (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1)
    (hH : S.toE_RGC.toRowsSource_RGC.height y ≤
      (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level) :
    y ∈ S.chain.edgeSource_EFE ∧ S.chain.edgeHeightGlobal_EFE y ≤ 4 * R.later.excl.Δ ∧
      y ∈ S.chain.toGaf02ChainE.edgeRegion_R74 := by
  have hyT : S.chain.edgeHeightGlobal_EFE y ≤ 4 * R.later.excl.Δ := by
    have h1 : S.toE_RGC.toRowsSource_RGC.height y ≤ R.edgeLevel_R74 := by
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).edge_level]
      exact hH
    rw [S.height_eq_OCL, ClosedRegisterV4.edgeLevel_R74] at h1
    exact h1
  have hcB : (c.1 : S.chain.toChain.finalBase_BAS 1) ∈
      S.chain.toGaf02ChainE.edgeBaseOpens_EFE := S.edgeBaseOpen_le_JN74 B hT hεr c.2
  have hR : S.chain.toGaf02ChainE.cutQ_R74 1 y ∈
      edgeRatio_R74 S.F.family.toLocalChartPacketsC14 := by
    rw [hq]
    exact hcB
  have hysrc : y ∈ S.chain.edgeSource_EFE :=
    S.chain.toGaf02ChainE.mem_edgeSource_EFE R.two_le_Δ_EDP23 hR hyT
  exact ⟨hysrc, hyT, S.chain.mem_edgeRegion_of_source_JN74 hysrc hyT⟩

/-- **The end disk is `ψ` of the chain's `{q₁ = ι c, T ≤ level}`.** -/
theorem disk_eq_image_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (c : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base) :
    (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).disk c =
      M.ψ.toEquiv '' {y | S.chain.toGaf02ChainE.cutQ_R74 1 y =
          (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 ∧
        S.toE_RGC.toRowsSource_RGC.height y ≤
          (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level} :=
  edgeBundle74_disk_eq_JN74 (S.closedStagesAt_OCL B hT hεr A zero).cut M.ψ.toEquiv
    (S.chain.toGaf02ChainE.cutQ_R74 1) (S.closedStagesAt_OCL B hT hεr A zero).ιedge
    S.toE_RGC.toRowsSource_RGC.height F
    (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.proj_eq
    (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.emb.injective
    (S.edge_parent_of_below_JN74 B hT hεr A zero)
    (S.closedStagesAt_OCL B hT hεr A zero).edge_height c

variable {S B hT hεr A zero} in
/-- **A point of the edge base lies in `C₂` iff its disk meets `M₂`.** -/
theorem mem_cbase_iff_disk_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    {Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut} {c : Rw.edge.Base} :
    c ∈ Rw.edge.cbase ↔
      ∃ x ∈ Rw.edge.disk c, x ∈ (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ := by
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := Rw.disk_nonempty_JN74 c
    refine ⟨x, hx, ?_⟩
    obtain ⟨z, ⟨hzc, hzh⟩, rfl⟩ := hx
    have hedge : (z : W.Carrier) ∈ Rw.edge.edgePiece := ⟨z, ⟨hzc ▸ hc, hzh⟩, rfl⟩
    rw [Rw.edgePiece_eq] at hedge
    exact (S.cover_at_OCL B hT hεr A zero
      (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)).edgeSet_subset_M₂ hedge
  · rintro ⟨x, hx, hxM⟩
    have hx' := hx
    rw [S.disk_eq_image_JN74 B hT hεr A zero Rw.edgeFacts c] at hx'
    obtain ⟨y, ⟨hq, hH⟩, rfl⟩ := hx'
    have hx2 := hx
    obtain ⟨-, -, hyR⟩ := S.edgeSource_of_fibre_JN74 B hT hεr A zero c hq hH
    have hyM : y ∈ (S.goodCut_OCL B hT hεr).M₂ := by
      rw [S.M₂_at_OCL B hT hεr A zero] at hxM
      obtain ⟨y', hy', hyy'⟩ := hxM
      rwa [← M.ψ.injective hyy']
    have hyE : y ∈ (S.goodCut_OCL B hT hεr).edgeSet := ⟨hyM, hyR⟩
    have hxE : M.ψ.toEquiv y ∈ (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet := by
      rw [S.edgeSet_at_OCL B hT hεr A zero (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)]
      exact ⟨y, hyE, rfl⟩
    rw [← Rw.edgePiece_eq] at hxE
    obtain ⟨z, ⟨hzc, -⟩, hzx⟩ := hxE
    obtain ⟨z', ⟨hz'c, -⟩, hz'x⟩ := hx2
    have hzz : z = z' := Subtype.ext (hzx.trans hz'x.symm)
    rw [hzz, hz'c] at hzc
    exact hzc

/-- **The edge coordinate on the good edge base**: `c ↦ ι c` into the block space. -/
def edgeVal_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base → S.blockSpace_R74 :=
  fun c => S.chain.toGaf02ChainE.edgeValB_EFE
    (TopologicalSpace.Opens.inclusion (S.edgeBaseOpen_le_JN74 B hT hεr) c)

/-- **The edge coordinate is smooth.** -/
theorem contMDiff_edgeVal_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    let _ := A.edgeChartedSpace1
    ContMDiff (𝓡 1) 𝓘(ℝ, S.blockSpace_R74) ∞ (S.edgeVal_JN74 B hT hεr A zero F) := by
  intro _
  have := A.edge_isManifold1.1
  exact (S.chain.toGaf02ChainE.contMDiff_edgeValB_EFE A).comp
    (contMDiff_inclusion (n := ∞) (S.edgeBaseOpen_le_JN74 B hT hεr))

/-- **`ι(q₁ x) = π₂E(ψ⁻¹ x)`** for the edge coordinate. -/
theorem edgeVal_proj_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (x : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).source) :
    S.edgeVal_JN74 B hT hεr A zero F ((edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).proj x) =
      S.chain.toGaf02ChainE.edgeBlockProj_EFE (M.ψ.symm x.1) :=
  S.edgeBlockProj_of_proj_JN74 B hT hεr A zero F x

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
