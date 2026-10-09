import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCbaseDomainOCL

/-!
# Draft 74 CL0, G8a: the circle facts of the produced stage geometry at `D_R`, partly produced

Lane O-CL1 (`_OCL`), group G8a. Of the seven fields of `CircleCutFacts74 P.A P.cut` for the
produced stage geometry `P` at `D_R` (clause (f) of the gate-1A table), two are PRODUCED here:

* **`circle_proper_at_OCL`** (`proper`): the whole restricted preimage of a compact base set is
  `M.ψ(q₀⁻¹(ι K))` (whole fibres: `circleStage_ident_OCL`), closed in the compact `X`;
* **`circle_cbase_compact_at_OCL`** (`cbase_compact`): `C₁ = q₀(M₃)` with `M₃` compact (FDC04's
  `remainder_compact` in `Htail`);
* **`circleCutFactsAt_OCL`**: the record from the remaining fields — the local trivializations
  (`neighborhood`, `mem_neighborhood`, `trivialization`, `projection_trivialization`: S-EDP-FDC2's
  `circleProj_trivial_EFE` carried by `M.ψ`, not yet transported) and FDC03's saturation
  `M₃ = q₀⁻¹(C₁)` (EDP06 (3), open).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The final circle projection `q₀` is continuous on `X`. -/
theorem continuous_cutQ0_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    Continuous (S.chain.toGaf02ChainE.cutQ_R74 0) :=
  (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
    S.F.family.toLocalChartPacketsC14.zero 0).starProjection.continuous.comp
    S.chain.toChain.stage_smooth.2.2.continuous

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- **`proper`** of the circle facts at `D_R`. -/
theorem circle_proper_at_OCL
    (Kc : Set (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen) (hK : IsCompact Kc) :
    IsCompact (Subtype.val '' ((S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictProj
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen ⁻¹' Kc)) := by
  have hset : Subtype.val '' ((S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictProj
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen ⁻¹' Kc) =
      {x | ∃ hx : x ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.circle.parent,
        (S.closedStagesAt_OCL B hT hεr A zero).A.circle.proj ⟨x, hx⟩ ∈ Subtype.val '' Kc} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hx, -⟩ := (S.closedStagesAt_OCL B hT hεr A zero).A.circle.exists_of_mem_restrictParent
        y.2
      exact ⟨hx, _, hy, rfl⟩
    · rintro ⟨hx, c, hc, hcx⟩
      have hsrc : x ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictParent
          (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen := by
        refine (S.closedStagesAt_OCL B hT hεr A zero).A.circle.mem_restrictParent_of hx ?_
        rw [← hcx]
        exact c.2
      refine ⟨⟨x, hsrc⟩, ?_, rfl⟩
      have he : (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictProj
          (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen ⟨x, hsrc⟩ = c :=
        Subtype.ext hcx.symm
      rw [mem_preimage, he]
      exact hc
  rw [hset, stageSet_LND74 (S.closedStagesAt_OCL B hT hεr A zero).circle_ident]
  have hKι : IsCompact ((S.closedStagesAt_OCL B hT hεr A zero).ιcircle '' (Subtype.val '' Kc)) :=
    (hK.image continuous_subtype_val).image
      (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.emb.continuous
  exact (hKι.isClosed.preimage S.continuous_cutQ0_OCL).isCompact.image M.ψ.continuous

/-- **`cbase_compact`** of the circle facts at `D_R` (`C₁ = q₀(M₃)`, `M₃` compact). -/
theorem circle_cbase_compact_at_OCL (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    IsCompact (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₁ :
      Set (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen) := by
  have hC : IsCompact (S.goodCut_OCL B hT hεr).C₁ :=
    Htail.remainder_compact.image S.continuous_cutQ0_OCL
  let ι : (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen → S.blockSpace_R74 :=
    fun c => S.circleι_OCL c.1
  have hι : Topology.IsEmbedding ι :=
    S.circleι_isEmbedding_OCL.comp Topology.IsEmbedding.subtypeVal
  have hsub : (S.goodCut_OCL B hT hεr).C₁ ⊆ range ι := by
    intro w hw
    obtain ⟨b, rfl⟩ := S.cut_C₁_subset_OCL B hT hεr hw
    exact ⟨⟨b, trivial⟩, rfl⟩
  exact (hι.isInducing.isCompact_preimage_iff hsub).2 hC

/-- **The circle facts at `D_R` from the trivializations and the saturation** (`proper` and
`cbase_compact` produced). -/
def circleCutFactsAt_OCL (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (nb : (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen →
      TopologicalSpace.Opens (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen)
    (hmem : ∀ c, c ∈ nb c)
    (tr : (c : (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen) →
      (TopologicalSpace.Opens.comap ((S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictProj
          (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen) (nb c))
        ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ ((nb c) × Circle))
    (hpt : ∀ c x, ((tr c x).1).val =
      (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictProj
        (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen x.val)
    (hsat : (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ =
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleRegion) :
    CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut where
  neighborhood := nb
  mem_neighborhood := hmem
  trivialization := tr
  projection_trivialization := hpt
  proper := S.circle_proper_at_OCL B hT hεr A zero
  cbase_compact := S.circle_cbase_compact_at_OCL B hT hεr A zero Htail
  saturation := hsat

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
