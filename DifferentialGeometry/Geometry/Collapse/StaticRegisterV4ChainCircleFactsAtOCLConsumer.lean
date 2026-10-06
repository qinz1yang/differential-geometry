import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCircleFactsAtOCL

/-!
# Consumer of O-CL1 G8: the circle region over the compact base is compact

Lane O-CL1 (`_OCL`), G8 consumer. For the produced stage geometry `P` at `D_R`, the whole restricted
circle preimage of the compact remaining base `C₁` (the circle region `q₀⁻¹(C₁)` carried to `W`)
is compact: `circle_cbase_compact_at_OCL` fed into `circle_proper_at_OCL`.
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

/-- **The carried circle region over `C₁` is compact** at `D_R`. -/
theorem stagesAt_circleRegion_compact_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    IsCompact (Subtype.val '' ((S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictProj
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen ⁻¹'
        (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₁))) :=
  S.circle_proper_at_OCL B hT hεr A zero _
    (S.circle_cbase_compact_at_OCL B hT hεr A zero Htail)

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
