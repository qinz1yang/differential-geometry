import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate5OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeRegionJN74

/-!
# Draft 74, FC39 gate 1A at `D_R`, sixth form: the saturation (f') produced

Lane S-JUNCTIONS (by S-JUNCTIONS3), G9 consumer (suffix `_JN74`). `closed_rows_gate5_OCL` with its
input `hsat` discharged by `cut_M₃_eq_circleRegion_JN74` (G8): the residual inputs of the gate are
now only the junction face facts (g), the rim facts (h) and the corner descent and rank data (i).
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

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
  (A : SmoothStageBases74 S) (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))

/-- **FC39 gate 1A at `D_R`, sixth form**: `closed_rows_gate5_OCL` with the saturation (f')
produced by `cut_M₃_eq_circleRegion_JN74`; the residual inputs are faces (g), rims (h) and the
corner data (i). -/
theorem closed_rows_gate6_JN74 (hK : 5 ≤ K)
    (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt_OCL B hT hεr A hK))
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
        (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw)))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      ((S.stagesAtZ_OCL B hT hεr A).rows
        (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
          (S.slimExitAt_OCL B hT hεr A hK))
        (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
        (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
          (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw))))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate5_OCL B hT hNb hcw hεr A Htail hK
    (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw) faces rims hdesc
    hrank

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
