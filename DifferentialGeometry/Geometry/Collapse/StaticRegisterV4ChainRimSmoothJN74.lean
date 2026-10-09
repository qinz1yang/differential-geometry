import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimSmoothGenJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRimBaseJN74

/-!
# Draft 74, the rim base is smooth at `D_R` (field `rimBase_smooth` of `JunctionRimFacts74`)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G15 (suffix `_JN74`). On the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero`: **every** map `rimBase` of the rows' edge base into the
rows' circle base with `rim c = fibre (rimBase c)` on `cbase` is smooth on `cbase`
(`rimBase_contMDiffOn_at_JN74`: `rimBase_contMDiffOn_gen_JN74` for `Y = ↥edgeBaseOpen`,
`j` its inclusion into `B₂`, `rb = opensTop ∘ rimBase`; the rim point over `c ∈ C₂` is in `X₁` by
`rim_whole_fibre_at_JN74`'s construction); with `exists_rimBase_at_JN74` this gives
`exists_rimBase_smooth_at_JN74`: a `rimBase` with `rim_fibre` AND `rimBase_smooth`.
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

/-- **A rim point in `X₁` over every point of `C₂(D_R)`** (the first half of
`rim_whole_fibre_at_JN74`). -/
theorem exists_rimPoint_at_JN74 (A : SmoothStageBases74 S) (hNb : T.Nb = maxNb_V4C)
    (hcw : T.cw = maxCw_V4C) {w : S.blockSpace_R74} (hw : w ∈ (S.goodCut_OCL B hT hεr).C₂) :
    ∃ xs : S.chain.toGaf02ChainE.edgeSource_EFE,
      S.chain.toGaf02ChainE.cutQ_R74 1 xs.1 = w ∧
        S.chain.edgeHeightGlobal_EFE xs.1 = 4 * R.later.excl.Δ ∧
        xs.1 ∈ S.chain.circleDomain_EFE := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
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
  exact ⟨xs, hq1.trans hx'w, hxT, S.chain.mem_circleDomain_of_EFE (hfacts hx3).1 (hfacts hx3).2⟩

/-- **Points below the level over the edge base of `D_R` lie in the edge parent** (the
identification input `hparE` of `exists_rimBase_JN74`). -/
theorem edge_parent_of_below_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S) :
    ∀ y, S.chain.toGaf02ChainE.cutQ_R74 1 y ∈
        (S.closedStagesAt_OCL B hT hεr A zero).ιedge ''
          ((S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen : Set _) →
      S.toE_RGC.toRowsSource_RGC.height y ≤ (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      (M.ψ.toEquiv y) ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.edge.parent := by
  intro y hy hH
  rw [(S.closedStagesAt_OCL B hT hεr A zero).cut_edgeOpen] at hy
  have hH' : S.toE_RGC.toRowsSource_RGC.height y ≤ R.edgeLevel_R74 := by
    rw [← (S.closedStagesAt_OCL B hT hεr A zero).edge_level]
    exact hH
  have hU := S.goodCut_edge_local_OCL B hT hεr hy hH'
  change M.ψ.toEquiv y ∈ ((S.closedStagesAt_OCL B hT hεr A zero).edge.parent : Set W.Carrier)
  rw [(S.closedStagesAt_OCL B hT hεr A zero).edge_ident.parent_eq]
  exact ⟨y, hU, rfl⟩

/-- **Any `rimBase` with `rim = fibre ∘ rimBase` on `cbase` is smooth on `cbase`.** -/
theorem rimBase_contMDiffOn_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (G : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (rimBase : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base →
      (circleBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut G).Base)
    (hrim : ∀ c ∈ (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase,
        (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).rim c =
        (circleBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut G).fibre (rimBase c)) :
    ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
  have hg7 := R.gaf07_numerics_OCL hT
  let _ := A.edgeChartedSpace1
  let _ := A.circleChartedSpace
  have := A.edge_isManifold1.1
  have hle : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen ≤
      S.chain.toGaf02ChainE.edgeBaseOpens_EFE := fun b hb =>
    ((S.goodCut_bases_OCL B hT hεr).1 hb).2
  let j : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base →
      S.chain.toGaf02ChainE.edgeBaseOpens_EFE := TopologicalSpace.Opens.inclusion hle
  let τ := Diffeomorph.opensTop_OCL (I := 𝓡 2)
    (N := (S.closedStagesAt_OCL B hT hεr A zero).A.circle.Base)
  have hj : ContMDiff (𝓡 1) (𝓡 1) ∞ j := contMDiff_inclusion (n := ∞) hle
  let rb : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base → S.chain.circleBaseOpens_EFE :=
    fun c => τ (rimBase c)
  have hX₁ : ∀ cc ∈ (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase,
      ∃ y : S.chain.toGaf02ChainE.edgeSource_EFE, S.chain.toGaf02ChainE.edgeProj_EFE y = j cc ∧
        S.chain.toGaf02ChainE.edgeHeight_EFE y = 4 * R.later.excl.Δ ∧
          (y : M.X) ∈ S.chain.circleDomain_EFE := by
    intro cc hcc
    have hw : (S.closedStagesAt_OCL B hT hεr A zero).ιedge cc.1 ∈ (S.goodCut_OCL B hT hεr).C₂ := by
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_C₂]
      exact ⟨cc.1, hcc, rfl⟩
    obtain ⟨xs, hq, hT', hX⟩ := S.exists_rimPoint_at_JN74 B hT hεr A hNb hcw hw
    refine ⟨xs, ?_, hT', hX⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hq
  have hrb : ∀ cc ∈ (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase,
      ∀ y : S.chain.toGaf02ChainE.edgeSource_EFE, S.chain.toGaf02ChainE.edgeProj_EFE y = j cc →
        S.chain.toGaf02ChainE.edgeHeight_EFE y = 4 * R.later.excl.Δ →
        ∀ hy : (y : M.X) ∈ S.chain.circleDomain_EFE,
          S.chain.circleProj_EFE ⟨y.1, hy⟩ = rb cc := by
    intro cc hcc y hyj hyT hy
    have hq1 : S.chain.toGaf02ChainE.cutQ_R74 1 y.1 =
        (S.closedStagesAt_OCL B hT hεr A zero).ιedge cc.1 :=
      congrArg (fun v : S.chain.toGaf02ChainE.edgeBaseOpens_EFE =>
        ((v : S.chain.toChain.finalBase_BAS 1) : S.blockSpace_R74)) hyj
    have hhy : S.toE_RGC.toRowsSource_RGC.height y.1 =
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level := by
      rw [S.height_eq_OCL, (S.closedStagesAt_OCL B hT hεr A zero).edge_level,
        ClosedRegisterV4.edgeLevel_R74]
      exact hyT
    have hmem : M.ψ.toEquiv y.1 ∈ (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).rim cc := by
      rw [edgeBundle74_rim_eq_JN74 (S.closedStagesAt_OCL B hT hεr A zero).cut M.ψ.toEquiv
        (S.chain.toGaf02ChainE.cutQ_R74 1) (S.closedStagesAt_OCL B hT hεr A zero).ιedge
        S.toE_RGC.toRowsSource_RGC.height F
        (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.proj_eq
        (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.emb.injective
        (S.edge_parent_of_below_JN74 B hT hεr A zero)
        (S.closedStagesAt_OCL B hT hεr A zero).edge_height cc]
      exact ⟨y.1, ⟨hq1, hhy⟩, rfl⟩
    rw [hrim cc hcc, circleBundle74_fibre_eq_JN74 (S.closedStagesAt_OCL B hT hεr A zero).cut
      M.ψ.toEquiv (S.chain.toGaf02ChainE.cutQ_R74 0)
      (S.closedStagesAt_OCL B hT hεr A zero).ιcircle G
      (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.proj_eq
      (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.emb.injective
      (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.parent_pre (rimBase cc)] at hmem
    obtain ⟨y', hy', hψ⟩ := hmem
    have hyy : y' = y.1 := M.ψ.toEquiv.injective hψ
    rw [hyy] at hy'
    apply Subtype.ext
    apply Subtype.ext
    exact hy'
  have hsm := S.chain.rimBase_contMDiffOn_gen_JN74 A hg7.1 hg7.2 R.two_le_Δ_EDP23 hE.2.2.1
    hE.2.2.2.1 hE.2.2.2.2.1 hE.2.2.2.2.2.1 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
    R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT) hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1
    hE.2.2.2.2.2.2.2.2 j hj _ rb hrb hX₁
  have h2 : ContMDiffOn (𝓡 1) (𝓡 2) ∞ (fun c => τ.symm (rb c))
      (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase :=
    τ.symm.contMDiff.comp_contMDiffOn hsm
  exact h2.congr fun c _ => (τ.symm_apply_apply (rimBase c)).symm

/-- **The rim base with `rim_fibre` AND smoothness** (fields `rimBase`, `rimBase_smooth`,
`rim_fibre` of `JunctionRimFacts74`): `exists_rimBase_at_JN74` with
`rimBase_contMDiffOn_at_JN74`. -/
theorem exists_rimBase_smooth_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (G : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    ∃ rimBase : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base →
      (circleBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut G).Base,
      ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase (edgeBundle74
        (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase ∧
      ∀ c ∈ (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase,
        (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).rim c =
        (circleBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut G).fibre (rimBase c) := by
  obtain ⟨rimBase, hrim⟩ := S.exists_rimBase_at_JN74 B hT hεr A zero hNb hcw F G
  exact ⟨rimBase, S.rimBase_contMDiffOn_at_JN74 B hT hεr A zero hNb hcw F G rimBase hrim, hrim⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
