import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesM2JN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHorizontalDisksJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRimSmoothJN74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCornersEFE

/-!
# Draft 74, the faces over the endpoints of `C₂` at `D_R` (labels g1, g2 and the disk cover)

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 (suffix `_JN74`). For an endpoint `e` of the edge base of
the rows at `D_R`:

* `edgeEnd_frontier_JN74`: `j e ∈ ∂C₂` (chain);
* `edgeEnd_cases_JN74`: the whole disk lies over `e` in ONE face: a zero face `∂Z_k` with
  `f₃ ∉ K₃`, or a free slim end `f₃⁻¹(arc k (iccEnd b))`, in `W`-terms (`edge_disk_in_face_EFE`).
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

/-- **An endpoint of the edge base of the rows is an endpoint of the chain's `C₂`**
(`j e ∈ ∂C₂` for the inclusion `j` of the good edge base into `B₂`). -/
theorem edgeEnd_frontier_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (c : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base)
    (hc : c ∈ frontier (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase) :
    (TopologicalSpace.Opens.inclusion (S.edgeBaseOpen_le_JN74 B hT hεr) c :
      S.chain.toGaf02ChainE.edgeBaseOpens_EFE) ∈
        frontier (S.chain.edgeC2_EFE (S.goodCut_OCL B hT hεr).K₃) := by
  let j : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base →
      S.chain.toGaf02ChainE.edgeBaseOpens_EFE :=
    TopologicalSpace.Opens.inclusion (S.edgeBaseOpen_le_JN74 B hT hεr)
  have hjo : Topology.IsOpenEmbedding j :=
    TopologicalSpace.Opens.isOpenEmbedding_of_le (S.edgeBaseOpen_le_JN74 B hT hεr)
  have hcb : j '' (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase =
      S.chain.edgeC2_EFE (S.goodCut_OCL B hT hεr).K₃ := by
    ext cc
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine (mem_edgeC2_iff_JN74 (S := S) (B := B) (hT := hT) (hεr := hεr) (cc := j c)).2 ?_
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_C₂]
      exact ⟨c.1, hc, rfl⟩
    · intro hcc
      have h := (mem_edgeC2_iff_JN74 (S := S) (B := B) (hT := hT) (hεr := hεr) (cc := cc)).1 hcc
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_C₂] at h
      obtain ⟨b, hb, hbq⟩ := h
      exact ⟨⟨b, (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂_sub hb⟩, hb,
        Subtype.ext (Subtype.ext hbq)⟩
  have hcl : IsClosed (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase := F.cbase_compact.isClosed
  have hjcl : IsClosed (j '' (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase) :=
    (F.cbase_compact.image hjo.continuous).isClosed
  rw [← hcb]
  exact (frontier_image_openEmbedding_JN74 hjo hcl hjcl (a := c)).2 hc

variable {S B hT hεr} in
/-- **The compactness hypothesis of the EDP05 row at `D_R`** (from `Htail`). -/
theorem edge_hcpt_JN74 (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    IsCompact (S.chain.edgeM2_EFE (S.goodCut_OCL B hT hεr).K₃ ∩
      Subtype.val '' {x : S.chain.edgeSource_EFE | S.chain.edgeHeight_EFE x ≤
        4 * R.later.excl.Δ}) := by
  have h := Htail.edge_compact
  convert h using 1
  ext y
  constructor
  · rintro ⟨hyM, x, hxT, rfl⟩
    exact ⟨hyM, S.chain.mem_edgeRegion_of_source_JN74 x.2 hxT⟩
  · intro hyE
    obtain ⟨hyT, hysrc⟩ := S.chain.cutEdgeSet_height_le_JN74 R.two_le_Δ_EDP23
      (S.goodCut_OCL B hT hεr).K₃ hyE
    exact ⟨hyE.1, ⟨y, hysrc⟩, hyT, rfl⟩

/-- **Over an endpoint of the edge base the whole disk lies in one face, in `W`-terms**: a zero
face `∂Z_k` with `f₃ ∉ K₃`, or the fibre of a free slim end value (an arc end of `D₃`, in the
relative interior of `C₃`). -/
theorem edgeEnd_cases_JN74 (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (c : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base)
    (hc : c ∈ frontier (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase) :
    (∃ k : S.ZeroIdx74, ∀ y : M.X, S.chain.toGaf02ChainE.cutQ_R74 1 y =
        (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 →
      S.toE_RGC.toRowsSource_RGC.height y ≤
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      y ∈ frontier (S.zeroDom74 k) ∧
        S.chain.slimMap_ZSP35 y ∉ (S.goodCut_OCL B hT hεr).K₃.carrier) ∨
    (∃ (k : Fin (S.chain.slimD₃_OCL hεr).m) (b : Bool),
      (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∈ Subtype.val '' interior
        (Subtype.val ⁻¹' S.chain.slimC3_ZSP35 : Set S.chain.slimBs_ZSP35) ∧
      ∀ y : M.X, S.chain.toGaf02ChainE.cutQ_R74 1 y =
          (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 →
        S.toE_RGC.toRowsSource_RGC.height y ≤
          (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
        S.chain.slimMap_ZSP35 y = (S.chain.slimD₃_OCL hεr).arc k (iccEnd b)) := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
  let _ := A.edgeChartedSpace1
  have := A.edge_isManifold1.1
  have hcpt := edge_hcpt_JN74 (S := S) (B := B) (hT := hT) (hεr := hεr) Htail
  have hD := (S.goodCut_OCL B hT hεr).D₃_eq
  have hKs := (S.goodCut_OCL B hT hεr).K₃_req
  have hKF := (S.goodCut_OCL B hT hεr).K₃_faces
  have hDreg := S.goodCut_D₃_reg_OCL B hT hεr
  have hdD := S.goodCut_D₃_bdry_OCL B hT hεr
  have hc₀ := S.edgeEnd_frontier_JN74 B hT hεr A zero F c hc
  have hdisk := S.chain.edge_disk_in_face_EFE A hεr R.two_le_Δ_EDP23 hE.2.2.1 hE.2.2.2.1
    hE.2.2.2.2.1 hE.2.2.2.2.2.1 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
    R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT) hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1
    hE.2.2.2.2.2.2.2.2 (S.goodCut_OCL B hT hεr).K₃ (S.goodCut_OCL B hT hεr).D₃ hD hKs hKF hDreg
    hdD hcpt hc₀
  have hconv : ∀ y : M.X, S.chain.toGaf02ChainE.cutQ_R74 1 y =
        (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 →
      S.toE_RGC.toRowsSource_RGC.height y ≤
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      ∃ hysrc : y ∈ S.chain.edgeSource_EFE,
        S.chain.edgeProj_EFE ⟨y, hysrc⟩ =
          TopologicalSpace.Opens.inclusion (S.edgeBaseOpen_le_JN74 B hT hεr) c ∧
        S.chain.edgeHeight_EFE ⟨y, hysrc⟩ ≤ 4 * R.later.excl.Δ := by
    intro y hq hH
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
    refine ⟨hysrc, ?_, hyT⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hq
  obtain ⟨hcase, -⟩ := hdisk
  rcases hcase with ⟨k, hk⟩ | ⟨y, ⟨k, hy01⟩, hyC, hxy⟩
  · left
    refine ⟨k, fun y hq hH => ?_⟩
    obtain ⟨hysrc, hxj, hyT⟩ := hconv y hq hH
    exact hk ⟨y, hysrc⟩ hxj hyT
  · right
    have hb : ∃ b : Bool, y = (S.goodCut_OCL B hT hεr).D₃.arc k (iccEnd b) := by
      rcases hy01 with h | h
      · exact ⟨false, by simpa [iccEnd] using h⟩
      · exact ⟨true, by simpa [iccEnd] using h⟩
    obtain ⟨b, hyb⟩ := hb
    refine ⟨k, b, hyb ▸ hyC, fun y' hq hH => ?_⟩
    obtain ⟨hysrc, hxj, hyT⟩ := hconv y' hq hH
    exact (hxy ⟨y', hysrc⟩ hxj hyT).trans hyb

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
