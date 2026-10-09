import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitAtOCL

/-!
# Draft 74, FC39 gate 1A at `D_R`, fifth form: the slim exit (b) plugged in

Lane C14-REG-CHAIN (by S-REG-CHAIN5), G40 consumer. `closed_rows_gate4_OCL` with the clause (b)
input `X : SlimExit74 P.A P.cut` produced by `nonempty_slimExit_OCL` (G40): the residual inputs
of the gate are now only FDC03's saturation (f'), the junction face facts (g), the rim facts (h)
and the corner descent and rank data (i), stated on the produced exit `slimExitAt_OCL`.
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

/-- **The produced slim exit at `D_R`** (clause (b)): a choice from G40's
`nonempty_slimExit_OCL`; its component / arc / loop relations are `exists_slimExit_rel_OCL`. -/
def slimExitAt_OCL (hK : 5 ≤ K) :
    SlimExit74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut :=
  Classical.choice (S.nonempty_slimExit_OCL B hT hεr (S.zsp02SmoothExit74 hεr)
    (S.stagesAtZ_OCL B hT hεr A) hK)

/-- **FC39 gate 1A at `D_R`, fifth form** (zero, edge, circle exits and the slim exit produced):
the residual inputs are saturation (f'), faces (g), rims (h) and corner data (i). -/
theorem closed_rows_gate5_OCL (hK : 5 ≤ K)
    (hsat : (S.stagesAtZ_OCL B hT hεr A).cut.M₃ = (S.stagesAtZ_OCL B hT hεr A).cut.circleRegion)
    (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt_OCL B hT hεr A hK))
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail hsat))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      ((S.stagesAtZ_OCL B hT hεr A).rows
        (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
          (S.slimExitAt_OCL B hT hεr A hK))
        (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
        (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail hsat)))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate4_OCL B hT hNb hcw hεr A Htail (S.slimExitAt_OCL B hT hεr A hK) hsat faces
    rims hdesc hrank

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
