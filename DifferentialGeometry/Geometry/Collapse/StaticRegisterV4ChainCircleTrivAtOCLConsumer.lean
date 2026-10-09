import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCircleTrivAtOCL

/-!
# Consumer of O-CL1 G8b: the circle facts at `D_R` from the saturation alone

Lane O-CL1 (`_OCL`), G8b consumer. The circle exit `FDC03ActualRemainderU74 P` of the produced stage
geometry at `D_R` exists as soon as FDC03's saturation `M₃ = q₀⁻¹(C₁)` holds and the edge exit is
given: local trivializations (S-EDP-FDC2 through `M.ψ`), properness, compact base (G8a/G8b) and
FDC04's cover (G4a) are produced.
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

/-- **The remainder exit at `D_R` from the saturation and the edge exit.** -/
theorem exists_fdc03RemainderAt_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (hsat : (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ =
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleRegion) :
    Nonempty (FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero)) :=
  ⟨S.fdc03RemainderAt_OCL B hT hεr A zero edge
    (S.circleCutFactsAt2_OCL B hT hεr A zero Htail hsat)⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
