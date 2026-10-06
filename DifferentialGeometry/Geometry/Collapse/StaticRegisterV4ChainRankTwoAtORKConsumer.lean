import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRankTwoAtORK
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate3OCL

/-!
# Consumer of O-RANK2 G1/G2: the edge exit and gate 1A at `D_R` without `rank_two`

Lane O-RANK2 (`_ORK`), consumer. With clause (c) produced (`edgeCutFacts_rank_two_at_OCL_ORK`):

* **`exists_edgeExitAt4_ORK`**: the edge exit `EDP04WholeDiskExitU74 P` of the produced stage
  geometry at `D_R` from FDC04's member facts `Htail` alone;
* **`closed_rows_gate4_ORK`**: O-CL1's `closed_rows_gate3_OCL` with the input `rank_two`
  discharged: rows linked at `D_R` and GROUP G's certificate from `Htail`, the zero exit (a),
  `SlimExit74` (b), the circle facts (f), the face facts (g), the rim facts (h) and the corner data
  (i).
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

/-- **The edge exit at `D_R` from FDC04's member facts alone.** -/
theorem exists_edgeExitAt4_ORK (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    Nonempty (EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero)) :=
  ⟨S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
    (S.edgeCutFactsAt3_ORK B hT hεr A zero hNb hcw Htail)⟩

/-- **FC39 gate 1A at `D_R`, fourth form**: `closed_rows_gate3_OCL` with `rank_two` produced. -/
theorem closed_rows_gate4_ORK (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (X : SlimExit74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (cf : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X)
      (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
        (S.edgeCutFactsAt3_ORK B hT hεr A zero hNb hcw Htail))
      (S.fdc03RemainderAt_OCL B hT hεr A zero
        (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
          (S.edgeCutFactsAt3_ORK B hT hεr A zero hNb hcw Htail)) cf))
    (rims : JunctionRimFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut
      ((S.closedStagesAt_OCL B hT hεr A zero).rows (S.zsp04ExitAt_OCL B hT hεr A zero X)
        (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
          (S.edgeCutFactsAt3_ORK B hT hεr A zero hNb hcw Htail))
        (S.fdc03RemainderAt_OCL B hT hεr A zero
          (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
            (S.edgeCutFactsAt3_ORK B hT hεr A zero hNb hcw Htail)) cf)))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate3_OCL B hT hNb hcw hεr A zero Htail X
    (S.edgeCutFacts_rank_two_at_OCL_ORK B hT hεr A zero hNb hcw) cf faces rims hdesc hrank

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
