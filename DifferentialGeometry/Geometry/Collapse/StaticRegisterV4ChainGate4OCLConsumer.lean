import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate4OCL

/-!
# Consumer of O-CL1 G9: the zero, edge and remainder exits at `D_R`, produced

Lane O-CL1 (`_OCL`), G9 consumer. On the produced stage geometry at `D_R` over the produced zero
exit (S-REG-CHAIN3), the edge exit exists from FDC04's member facts alone and the remainder exit
from FDC03's saturation alone; the zero exit's domains are the `M.ψ`-images of the actual `Z_k`.
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

/-- **The produced exits at `D_R`**: the carried regions cover `W` with the zero exit's domains,
the edge exit exists, and the remainder exit exists once FDC03's saturation holds. -/
theorem exitsAtZ_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (A : SmoothStageBases74 S) (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    (⋃ i, range ((S.zsp02SmoothExit74 hεr).rows.piece i).map = M.ψ '' S.chain.zeroUnion_ZSP35) ∧
      Nonempty (EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A)) ∧
      ((S.stagesAtZ_OCL B hT hεr A).cut.M₃ = (S.stagesAtZ_OCL B hT hεr A).cut.circleRegion →
        Nonempty (FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))) :=
  ⟨S.zeroRanges_at_OCL (S.zsp02SmoothExit74 hεr),
    ⟨S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail⟩,
    fun hsat => ⟨S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail hsat⟩⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
