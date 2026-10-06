import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCoverAtOCL
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierCrossKind74

/-!
# Draft 74 CL0, G5a: the edge facts of the produced stage geometry at `D_R`

Lane O-CL1 (`_OCL`), group G5a. On `P = S.closedStagesAt_OCL B hT hεr A zero` (G3a) at
`D_R = S.goodCut_OCL B hT hεr`, three of the five fields of `EdgeCutFacts74 P.A P.cut` are
PRODUCED; `rank_two` (EDP05 rim rank in abstract form) and `cbase_domain` (FDC02's frontier data
on the good base) stay explicit arguments of `edgeCutFactsAt_OCL`:

* kernel `edgeSublevelSet_OCL`: for a stage identified with `q` on an open ambient parent
  (`StageIdentU_LND74`), the restricted sublevel set over `Kc ⊆ V` is
  `ψ(U ∩ {q ∈ ι(Kc), H ≤ lvl})`;
* `isSmoothEmbedding_comp_closedModel_OCL`: a smooth embedding of the closed disk into the
  boundaryless model `X` followed by the carrier diffeomorphism `M.ψ` (either carrier kind: O-CROSS'
  `diffeomorph_comp_toHalfSpace_OCX` for a carrier with boundary);
* at `D_R`: `edgeSublevel_at_OCL` (the parent `U₂` drops out: O-CL0 G1's
  `goodCut_edge_local_OCL`), **`edge_proper_at_OCL`** (`proper`), **`edge_fibre_disk_at_OCL`**
  (`fibre_disk`: EDP04's whole disk `goodCut_edge_disk_OCL` carried by `M.ψ`),
  **`edge_cbase_compact_at_OCL`** (`cbase_compact`, from FDC04's `edge_compact` in `Htail`);
* **`edgeCutFactsAt_OCL`**: `EdgeCutFacts74 P.A P.cut` from `rank_two` and `cbase_domain` only.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

universe u v w

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace GC.GraphManifold.Assembly.FC39P0

variable {X : Type v} {Bs : Type w} [TopologicalSpace Bs] {W : CompactCarrier.{u}} {n : ℕ}
  {E : BoundaryTori W n}

/-- **The restricted sublevel set over `Kc`** of a stage identified with `q` on the open ambient
parent `U`: `val '' {x ∈ q⁻¹(V) | proj x ∈ Kc, H x ≤ lvl} = ψ(U ∩ {q ∈ ι(Kc), Hs ≤ lvl})`. -/
theorem edgeSublevelSet_OCL {ψ : X ≃ W.Carrier} {A : SmoothStageGeometry74 W E}
    {D : StageCutChoice74 A} {q : X → Bs} {ι : A.edge.Base → Bs} {U : Set X} {Hs : X → ℝ}
    {lvl : ℝ} (hid : StageIdentU_LND74 ψ A.edge.toStageProj74 q ι U)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs (ψ.symm x)) (hlvl : A.edge.level = lvl)
    (Kc : Set D.edgeBaseOpen) :
    Subtype.val '' {x : D.edgeSource | A.edge.restrictProj D.edgeBaseOpen x ∈ Kc ∧
        D.edgeHeight x ≤ A.edge.level} =
      ψ '' (U ∩ {p | q p ∈ ι '' (Subtype.val '' Kc) ∧ Hs p ≤ lvl}) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hK, hh⟩, rfl⟩
    obtain ⟨hx, -⟩ := A.edge.exists_of_mem_restrictParent x.2
    have hxU : (x : W.Carrier) ∈ ψ '' U := hid.parent_eq ▸ hx
    obtain ⟨u, hu, hux⟩ := hxU
    have hq : ι (A.edge.proj (A.edge.restrictIncl D.edgeBaseOpen x)) = q u := by
      rw [hid.proj_eq]
      change q (ψ.symm (x : W.Carrier)) = q u
      rw [← hux, ψ.symm_apply_apply]
    have hHu : Hs u ≤ lvl := by
      have h1 := hH (A.edge.restrictIncl D.edgeBaseOpen x)
      change A.edge.height (A.edge.restrictIncl D.edgeBaseOpen x) ≤ A.edge.level at hh
      rw [h1, hlvl] at hh
      change Hs (ψ.symm (x : W.Carrier)) ≤ lvl at hh
      rwa [← hux, ψ.symm_apply_apply] at hh
    exact ⟨u, ⟨hu, ⟨_, ⟨_, hK, rfl⟩, hq⟩, hHu⟩, hux⟩
  · rintro ⟨u, ⟨hu, ⟨b, ⟨c, hc, rfl⟩, hb⟩, hHs⟩, rfl⟩
    have hx : ψ u ∈ A.edge.parent := by
      rw [← SetLike.mem_coe, hid.parent_eq]
      exact mem_image_of_mem ψ hu
    have hp : A.edge.proj ⟨ψ u, hx⟩ = c.1 := by
      apply hid.emb.injective
      rw [hid.proj_eq]
      change q (ψ.symm (ψ u)) = ι c.1
      rw [ψ.symm_apply_apply]
      exact hb.symm
    have hsrc : ψ u ∈ D.edgeSource := by
      refine A.edge.mem_restrictParent_of hx ?_
      rw [hp]
      exact c.2
    refine ⟨⟨ψ u, hsrc⟩, ⟨?_, ?_⟩, rfl⟩
    · have he : A.edge.restrictProj D.edgeBaseOpen ⟨ψ u, hsrc⟩ = c := Subtype.ext hp
      rw [he]
      exact hc
    · change A.edge.height (A.edge.restrictIncl D.edgeBaseOpen ⟨ψ u, hsrc⟩) ≤ A.edge.level
      rw [hH, hlvl]
      change Hs (ψ.symm (ψ u)) ≤ lvl
      rwa [ψ.symm_apply_apply]

end GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

/-- **A smooth embedding of the closed disk into the boundaryless model, followed by a carrier
diffeomorphism of either kind** (the closed-route `M.ψ`). -/
theorem isSmoothEmbedding_comp_closedModel_OCL {W : CompactCarrier.{u}} {N₀ : Type*}
    [TopologicalSpace N₀] [ChartedSpace E3 N₀]
    (e : N₀ ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier) {φ : ClosedCell 2 → N₀}
    (hφ : IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ) :
    IsSmoothEmbedding (𝓡∂ 2) W.model ∞ (e ∘ φ) := by
  have hs₀ : (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    simp at h1
  have hs₀I : ∀ v : EuclideanSpace ℝ (Fin 2),
      v + EuclideanSpace.single 1 1 ∈ range (𝓡∂ 2) ↔ v ∈ range (𝓡∂ 2) := by
    intro v
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp
  cases W with
  | mk k C o =>
    cases k
    · exact hφ.diffeomorph_comp e
    · exact hφ.diffeomorph_comp_toHalfSpace_OCX _ hs₀ hs₀I e

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The final edge projection `q₁` is continuous on `X`. -/
theorem continuous_cutQ1_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    Continuous (S.chain.toGaf02ChainE.cutQ_R74 1) :=
  (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
    S.F.family.toLocalChartPacketsC14.zero 1).starProjection.continuous.comp
    S.chain.toChain.stage_smooth.2.2.continuous

/-- The rows' height `A/s` is continuous on `X`. -/
theorem continuous_height_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    Continuous S.toE_RGC.toRowsSource_RGC.height := by
  have h : S.toE_RGC.toRowsSource_RGC.height = S.edgeHeightW_R74 ∘ M.ψ := by
    funext p
    change _ = S.toE_RGC.toRowsSource_RGC.height (M.ψ.symm (M.ψ p))
    rw [M.ψ.symm_apply_apply]
  rw [h]
  exact S.edgeHeightW_smooth_R74.continuous.comp M.ψ.continuous

/-- The sublevel set of `A/s` over a compact base set is compact. -/
theorem isCompact_edgeSublevel_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    {Kb : Set S.blockSpace_R74} (hK : IsCompact Kb) :
    IsCompact {p : M.X | S.chain.toGaf02ChainE.cutQ_R74 1 p ∈ Kb ∧
      S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74} :=
  ((hK.isClosed.preimage S.continuous_cutQ1_OCL).inter
    (isClosed_le S.continuous_height_OCL continuous_const)).isCompact

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- **The restricted sublevel set of the produced edge stage over `Kc`**: the parent `U₂` drops
out (O-CL0 G1: the whole low part of a fibre over the edge base of `D_R` lies in `U₂`). -/
theorem edgeSublevel_at_OCL (Kc : Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) :
    Subtype.val '' {x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource |
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
          (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen x ∈ Kc ∧
        (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x ≤
          (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level} =
      M.ψ '' {p | S.chain.toGaf02ChainE.cutQ_R74 1 p ∈
          (S.closedStagesAt_OCL B hT hεr A zero).ιedge '' (Subtype.val '' Kc) ∧
        S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74} := by
  rw [edgeSublevelSet_OCL (S.closedStagesAt_OCL B hT hεr A zero).edge_ident
    (S.closedStagesAt_OCL B hT hεr A zero).edge_height
    (S.closedStagesAt_OCL B hT hεr A zero).edge_level Kc]
  congr 1
  refine inter_eq_right.mpr fun p hp => S.goodCut_edge_local_OCL B hT hεr ?_ hp.2
  rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_edgeOpen]
  obtain ⟨b, ⟨c, -, rfl⟩, hb⟩ := hp.1
  exact ⟨c.1, c.2, hb⟩

/-- **`proper`** of the edge facts at `D_R`. -/
theorem edge_proper_at_OCL (Kc : Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen)
    (hK : IsCompact Kc) :
    IsCompact (Subtype.val '' {x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource |
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
          (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen x ∈ Kc ∧
        (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x ≤
          (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level}) := by
  rw [S.edgeSublevel_at_OCL B hT hεr A zero Kc]
  exact (S.isCompact_edgeSublevel_OCL ((hK.image continuous_subtype_val).image
    (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.emb.continuous)).image M.ψ.continuous

/-- **`fibre_disk`** of the edge facts at `D_R`: EDP04's whole smooth disk over every point of the
good edge base, carried to `W` by `M.ψ`. -/
theorem edge_fibre_disk_at_OCL (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (c : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) :
    ∃ φ : ClosedCell 2 → W.Carrier, IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ ∧
      range φ = Subtype.val '' {x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource |
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
          (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen x = c ∧
        (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x ≤
          (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level} := by
  have hc : (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 ∈
      (S.goodCut_OCL B hT hεr).edgeBaseOpen := by
    rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_edgeOpen]
    exact mem_image_of_mem _ c.2
  obtain ⟨φ, hφ, hr, -⟩ := S.goodCut_edge_disk_OCL B hT hNb hcw hεr hc
  refine ⟨M.ψ ∘ φ, isSmoothEmbedding_comp_closedModel_OCL M.ψ hφ, ?_⟩
  have h := S.edgeSublevel_at_OCL B hT hεr A zero {c}
  simp only [image_singleton] at h
  change _ = Subtype.val '' {x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource |
    (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen x ∈ ({c} : Set _) ∧
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x ≤
      (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level}
  rw [h, range_comp, hr]
  rfl

/-- `C₂` of `D_R` is compact (FDC04's `edge_compact` and the continuity of `q₁`). -/
theorem goodCut_C₂_compact_OCL (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    IsCompact (S.goodCut_OCL B hT hεr).C₂ :=
  Htail.edge_compact.image S.continuous_cutQ1_OCL

/-- **`cbase_compact`** of the edge facts at `D_R`. -/
theorem edge_cbase_compact_at_OCL (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    IsCompact (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂ :
      Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) := by
  let ι : (S.goodCut_OCL B hT hεr).edgeBaseOpens_R74 → S.blockSpace_R74 := fun c => c.1.1
  have hι : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hsub : (S.goodCut_OCL B hT hεr).C₂ ⊆ range ι := by
    intro w hw
    have hw' : w ∈ Subtype.val '' ((S.goodCut_OCL B hT hεr).edgeBaseOpens_R74 :
        Set (S.chain.toChain.finalBase_BAS 1)) := by
      rw [(S.goodCut_OCL B hT hεr).edgeBaseOpens_val_R74]
      exact (S.goodCut_OCL B hT hεr).edgeBaseOpen_sub hw
    obtain ⟨b, hb, rfl⟩ := hw'
    exact ⟨⟨b, hb⟩, rfl⟩
  exact (hι.isInducing.isCompact_preimage_iff hsub).2 (S.goodCut_C₂_compact_OCL B hT hεr Htail)

/-- **The edge facts at `D_R`** from the two remaining fields (EDP05's rim rank two and FDC02's
frontier data on the good base); `proper`, `fibre_disk` and `cbase_compact` are produced. -/
theorem edgeCutFactsAt_OCL (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (rank_two : ∀ x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource,
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x =
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
        (mfderiv W.model (𝓡 1) ((S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
            (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) x v,
          mfderiv W.model 𝓘(ℝ, ℝ) (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x v))
    (cbase_domain : ∀ c ∈ frontier (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂ :
        Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen),
      ∃ U : TopologicalSpace.Opens (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen, c ∈ U ∧
        ∃ φ : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen → ℝ,
          ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
          (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂ :
            Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) ∩ U =
            {c' | c' ∈ U ∧ 0 ≤ φ c'}) :
    EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut where
  rank_two := rank_two
  proper := S.edge_proper_at_OCL B hT hεr A zero
  fibre_disk := S.edge_fibre_disk_at_OCL B hT hεr A zero hNb hcw
  cbase_compact := S.edge_cbase_compact_at_OCL B hT hεr A zero Htail
  cbase_domain := cbase_domain

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
