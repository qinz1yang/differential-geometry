import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitAt2OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSaturationJN74

/-!
# Draft 74, FC39 gate 1A at `D_R`, sixth form with the slim exit that carries the end coordinates

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G2 consumer (suffix `_JN74`, the gate of S-JUNCTIONS3's
`closed_rows_gate6_JN74`). The same gate with the slim exit `X` plugged in REPLACED by
`slimExitAt2_OCL` (G2: the choice from `exists_slimExit_rel2_OCL`, whose free end functions are
`e ∘ f₃ ∘ ψ⁻¹`): the saturation (f') is produced by `cut_M₃_eq_circleRegion_JN74`, the residual
inputs are the faces (g), the rims (h) and the corner data (i), now stated on the NEW exit.
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

/-- **FC39 gate 1A at `D_R`, sixth form, with the slim exit `slimExitAt2_OCL`**: as
`closed_rows_gate6_JN74` with `slimExitAt_OCL` replaced by `slimExitAt2_OCL`. The residual
inputs are faces (g), rims (h) and the corner data (i). -/
theorem closed_rows_gate6b_JN74 (hK : 5 ≤ K)
    (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK))
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
        (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw)))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      ((S.stagesAtZ_OCL B hT hεr A).rows
        (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
          (S.slimExitAt2_OCL B hT hεr A hK))
        (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
        (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
          (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw))))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate4_OCL B hT hNb hcw hεr A Htail (S.slimExitAt2_OCL B hT hεr A hK)
    (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw) faces rims
    hdesc hrank

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
