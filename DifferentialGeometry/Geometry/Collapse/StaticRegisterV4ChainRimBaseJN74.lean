import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeRegionJN74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimFibreEFE
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRimBaseJN74

/-!
# Draft 74, the rim base at `D_R` (fields `rimBase`, `rim_fibre` of `JunctionRimFacts74`)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G13 (suffix `_JN74`). On the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` at `D_R`:

* `rim_whole_fibre_at_JN74` (chain, in block-space terms): over every `w ∈ C₂(D_R)` the rim
  `{q₁ = w, H = level}` is a whole fibre `q₀⁻¹(w₀)` with `w₀ ∈ W₁ ∩ R₁`. A rim point over `w`
  exists (`edge_rim_point_EFE`), lies in `M₂` (`goodCut_edge_saturated_OCL`), in `M^edge`, hence in
  `M₃` (`rim_mem_cutM3_JN74`, G8), hence in `X₁` (`goodCut_facts_OCL`): so EDP06's
  `edp06_rim_eq_whole_fibre_EFE` applies with no separate `X₁` input;
* **`exists_rimBase_at_JN74`**: the maps `rimBase` of the rows' bundles with
  `rim c = fibre (rimBase c)` on `cbase` (`exists_rimBase_JN74` applied to the identifications of
  the stage record).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **Over every point of `C₂(D_R)` the rim is a whole `q₀`-fibre over a point of `W₁ ∩ R₁`.** -/
theorem rim_whole_fibre_at_JN74 (A : SmoothStageBases74 S) (hNb : T.Nb = maxNb_V4C)
    (hcw : T.cw = maxCw_V4C) {w : S.blockSpace_R74} (hw : w ∈ (S.goodCut_OCL B hT hεr).C₂) :
    ∃ w₀ : S.blockSpace_R74, w₀ ∈ range S.circleι_OCL ∧
      {y | S.chain.toGaf02ChainE.cutQ_R74 1 y = w ∧
          S.toE_RGC.toRowsSource_RGC.height y = R.edgeLevel_R74} =
        S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' {w₀} := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
  have hg7 := R.gaf07_numerics_OCL hT
  have hfacts := (S.goodCut_facts_OCL B hT hεr).2.2.2
  obtain ⟨x', hx'E, hx'w⟩ := hw
  have hx'reg : x' ∈ S.chain.toGaf02ChainE.edgeRegion_R74 := hx'E.2
  rw [S.chain.edgeRegion_eq_JN74] at hx'reg
  obtain ⟨⟨hW, hrat⟩, -⟩ := hx'reg
  let cc : S.chain.toGaf02ChainE.edgeBaseOpens_EFE := ⟨⟨_, hW⟩, hrat⟩
  obtain ⟨xs, hxs1, hxs2⟩ := S.chain.toGaf02ChainE.edge_rim_point_EFE R.two_le_Δ_EDP23 hE.2.2.1
    hE.2.2.2.1 hE.2.2.2.2.1 hE.2.2.2.2.2.1 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
    R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT) hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1
    hE.2.2.2.2.2.2.2.2 cc
  have hq1 : S.chain.toGaf02ChainE.cutQ_R74 1 xs.1 = S.chain.toGaf02ChainE.cutQ_R74 1 x' :=
    congrArg (fun v : S.chain.toGaf02ChainE.edgeBaseOpens_EFE =>
      ((v : S.chain.toChain.finalBase_BAS 1) : S.blockSpace_R74)) hxs1
  have hxT : S.chain.edgeHeightGlobal_EFE xs.1 = 4 * R.later.excl.Δ := hxs2
  have hhx : S.toE_RGC.toRowsSource_RGC.height xs.1 = R.edgeLevel_R74 := by
    rw [S.height_eq_OCL, ClosedRegisterV4.edgeLevel_R74]
    exact hxT
  have hM2 : xs.1 ∈ (S.goodCut_OCL B hT hεr).M₂ :=
    S.goodCut_edge_saturated_OCL B hT hεr hNb hcw hx'E hq1 (le_of_eq hhx)
  have hxE : xs.1 ∈ S.chain.toGaf02ChainE.cutEdgeSet_R74 (S.goodCut_OCL B hT hεr).K₃.carrier :=
    ⟨hM2, S.chain.mem_edgeRegion_of_source_JN74 xs.2 (le_of_eq hxT)⟩
  have hx3 : xs.1 ∈ (S.goodCut_OCL B hT hεr).M₃ :=
    S.chain.rim_mem_cutM3_JN74 A hεr R.two_le_Δ_EDP23 hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1
      hE.2.2.2.2.2.1 hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2
      (S.goodCut_OCL B hT hεr).K₃ (S.goodCut_OCL B hT hεr).D₃ (S.goodCut_OCL B hT hεr).D₃_eq
      (S.goodCut_OCL B hT hεr).K₃_req (S.goodCut_OCL B hT hεr).K₃_faces
      (S.goodCut_D₃_reg_OCL B hT hεr) (S.goodCut_D₃_bdry_OCL B hT hεr) hxE hxT
  have hxX : xs.1 ∈ S.chain.circleDomain_EFE :=
    S.chain.mem_circleDomain_of_EFE (hfacts hx3).1 (hfacts hx3).2
  have hX₁ : (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero 0).starProjection (S.chain.toChain.E xs.1) ∈
      S.chain.toChain.circleBase_BAS := by
    have h := S.chain.circleDomain_eq_EFE hg7.1 hg7.2
    have hq : xs.1 ∈ (S.chain.circleDomain_EFE : Set M.X) := hxX
    rw [h] at hq
    exact hq
  have hrim := S.chain.edp06_rim_eq_whole_fibre_EFE hg7.1 hg7.2 R.two_le_Δ_EDP23 hE.2.2.1
    hE.2.2.2.1 hE.2.2.2.2.1 hE.2.2.2.2.2.1 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
    R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT) hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1
    hE.2.2.2.2.2.2.2.2 (q₀ := xs.1) (S.chain.toGaf02ChainE.edgeSource_mem_EFE xs.2).2 hxT hX₁
  refine ⟨S.chain.toGaf02ChainE.cutQ_R74 0 xs.1, ?_, ?_⟩
  · rw [S.range_circleι_OCL]
    exact ⟨(hfacts hx3).2, (hfacts hx3).1⟩
  · ext y
    have hy := Set.ext_iff.1 hrim y
    rw [← hx'w, ← hq1]
    change (S.chain.toGaf02ChainE.cutQ_R74 1 y = S.chain.toGaf02ChainE.cutQ_R74 1 xs.1 ∧
      S.toE_RGC.toRowsSource_RGC.height y = R.edgeLevel_R74) ↔ _
    rw [S.height_eq_OCL, ClosedRegisterV4.edgeLevel_R74]
    exact hy

/-- **The rim base of the rows' bundles at `D_R`**: a map `rimBase` with
`rim c = fibre (rimBase c)` for every `c ∈ cbase` (fields `rimBase`, `rim_fibre` of
`JunctionRimFacts74`, before smoothness). -/
theorem exists_rimBase_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (G : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    ∃ rimBase : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base →
      (circleBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut G).Base,
      ∀ c ∈ (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase,
        (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).rim c =
        (circleBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut G).fibre (rimBase c) := by
  refine exists_rimBase_JN74 (S.closedStagesAt_OCL B hT hεr A zero).cut M.ψ.toEquiv
    (S.chain.toGaf02ChainE.cutQ_R74 1) (S.chain.toGaf02ChainE.cutQ_R74 0)
    (S.closedStagesAt_OCL B hT hεr A zero).ιedge (S.closedStagesAt_OCL B hT hεr A zero).ιcircle
    S.toE_RGC.toRowsSource_RGC.height F G
    (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.proj_eq
    (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.emb.injective ?_
    (S.closedStagesAt_OCL B hT hεr A zero).edge_height
    (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.proj_eq
    (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.emb.injective
    (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.parent_pre ?_
  · intro y hy hH
    rw [(S.closedStagesAt_OCL B hT hεr A zero).cut_edgeOpen] at hy
    have hH' : S.toE_RGC.toRowsSource_RGC.height y ≤ R.edgeLevel_R74 := by
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).edge_level]
      exact hH
    have hU := S.goodCut_edge_local_OCL B hT hεr hy hH'
    change M.ψ.toEquiv y ∈ ((S.closedStagesAt_OCL B hT hεr A zero).edge.parent : Set W.Carrier)
    rw [(S.closedStagesAt_OCL B hT hεr A zero).edge_ident.parent_eq]
    exact ⟨y, hU, rfl⟩
  · intro c hc
    have hw : (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 ∈ (S.goodCut_OCL B hT hεr).C₂ := by
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_C₂]
      exact ⟨c.1, hc, rfl⟩
    obtain ⟨w₀, ⟨b', hb'⟩, hset⟩ := S.rim_whole_fibre_at_JN74 B hT hεr A hNb hcw hw
    refine ⟨⟨b', trivial⟩, ?_⟩
    have hb'' : (S.closedStagesAt_OCL B hT hεr A zero).ιcircle b' = w₀ := hb'
    rw [(S.closedStagesAt_OCL B hT hεr A zero).edge_level]
    change {y | S.chain.toGaf02ChainE.cutQ_R74 1 y =
        (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 ∧
      S.toE_RGC.toRowsSource_RGC.height y = R.edgeLevel_R74} =
      S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' {(S.closedStagesAt_OCL B hT hεr A zero).ιcircle b'}
    rw [hb'']
    exact hset

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
