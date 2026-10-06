import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate3OCL

/-!
# Consumer of O-CL1 G7: the edge exit at `D_R` from the rim rank alone

Lane O-CL1 (`_OCL`), G7 consumer. The edge exit `EDP04WholeDiskExitU74 P` of the produced stage
geometry at `D_R` exists as soon as EDP05's rim rank two holds on the carried edge source: proper,
whole disks, compact base (G5a), FDC02's frontier data (G7a), FDC02's set equality (G6a) and the
component models (S-EDGE-INT2) are produced.
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

/-- **The edge exit at `D_R` from the rim rank alone.** -/
theorem exists_edgeExitAt3_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
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
          mfderiv W.model 𝓘(ℝ, ℝ) (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x v)) :
    Nonempty (EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero)) :=
  ⟨S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
    (S.edgeCutFactsAt2_OCL B hT hεr A zero hNb hcw Htail rank_two)⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
