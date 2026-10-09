import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate2OCL

/-!
# Consumer of O-CL1 G6: the produced stage geometry's edge set and cover, unconditionally

Lane O-CL1 (`_OCL`), G6 consumer. With FDC02's set equality produced (G6a), the edge set of the
carried cut is `M.ψ(M^edge)` and FDC04's cover of the produced stage geometry holds with no input
other than the zero exit (register values `T.Nb`, `T.cw`).
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

/-- **The carried edge set is `M.ψ(M^edge)`** and **FDC04's cover holds** for the produced stage
geometry at `D_R`, unconditionally on the register values. -/
theorem stagesAt_edgeSet_cover_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet =
        M.ψ '' (S.goodCut_OCL B hT hεr).edgeSet ∧
      CutCoverFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut :=
  ⟨S.edgeSet_at_OCL B hT hεr A zero (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw),
    S.cover_at_OCL B hT hεr A zero (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
