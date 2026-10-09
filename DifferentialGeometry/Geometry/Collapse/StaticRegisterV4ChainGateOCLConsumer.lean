import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGateOCL

/-!
# Consumer of O-CL1 G5: the edge exit at `D_R` from two fields

Lane O-CL1 (`_OCL`), G5 consumer. The edge exit `EDP04WholeDiskExitU74 P` of the produced stage
geometry at `D_R` exists as soon as EDP05's rim rank two and FDC02's frontier data on the good base
(the two non-produced fields of `EdgeCutFacts74`) and FDC02's set equality are given: `proper`,
`fibre_disk`, `cbase_compact` (G5a) and the component models (S-EDGE-INT2 E2 + E3 + E4c) are
produced.
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

/-- **The edge exit at `D_R` from the two remaining edge fields and FDC02's set equality.** -/
theorem exists_edgeExitAt_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
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
            {c' | c' ∈ U ∧ 0 ≤ φ c'})
    (hE : (S.goodCut_OCL B hT hεr).edgeSet =
      gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
        (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹' (S.goodCut_OCL B hT hεr).C₂ ∩
          {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74})) :
    Nonempty (EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero)) :=
  ⟨S.edgeExitAt_OCL B hT hεr A zero
    (S.edgeCutFactsAt_OCL B hT hεr A zero hNb hcw Htail rank_two cbase_domain) hE⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
