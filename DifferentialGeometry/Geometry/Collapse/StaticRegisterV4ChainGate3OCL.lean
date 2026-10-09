import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate2OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCbaseDomainOCL

/-!
# Draft 74, FC39 gate 1A at `D_R`, third form: the edge facts from `rank_two` alone

Lane O-CL1 (`_OCL`), group G7b. The gate head of G6 with the clauses (d) (FDC02's frontier data,
G7a) and (e) (FDC02's set equality, G6a) PRODUCED: the only edge input left is EDP05's rim rank
two (`rank_two`, clause (c)).

**`closed_rows_gate3_OCL`**: rows `Rw : FC39RowsV2 W ∅` linked at `D_R` and GROUP G's certificate
from: FDC04's member facts `Htail` at `D_R` (S-REG-NUM), the zero exit (a), `SlimExit74` on `P`
(b), `rank_two` (c), the circle facts (f), the junction face facts (g), the rim facts (h) with the
corner descent and rank data (i).
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

/-- **FC39 gate 1A at `D_R`, third form**: the edge facts from `rank_two` alone. -/
theorem closed_rows_gate3_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (X : SlimExit74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (rank_two : ∀ x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource,
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x =
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
        (mfderiv W.model (𝓡 1) ((S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
            (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) x v,
          mfderiv W.model 𝓘(ℝ, ℝ) (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x v))
    (cf : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X)
      (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
        (S.edgeCutFactsAt2_OCL B hT hεr A zero hNb hcw Htail rank_two))
      (S.fdc03RemainderAt_OCL B hT hεr A zero
        (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
          (S.edgeCutFactsAt2_OCL B hT hεr A zero hNb hcw Htail rank_two)) cf))
    (rims : JunctionRimFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut
      ((S.closedStagesAt_OCL B hT hεr A zero).rows (S.zsp04ExitAt_OCL B hT hεr A zero X)
        (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
          (S.edgeCutFactsAt2_OCL B hT hεr A zero hNb hcw Htail rank_two))
        (S.fdc03RemainderAt_OCL B hT hεr A zero
          (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero
            (S.edgeCutFactsAt2_OCL B hT hεr A zero hNb hcw Htail rank_two)) cf)))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate2_OCL B hT hNb hcw hεr A zero X _ cf faces rims hdesc hrank

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
