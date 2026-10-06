import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate3OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCircleTrivAtOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRankTwoAtORK
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainZeroExit74

/-!
# Draft 74, FC39 gate 1A at `D_R`, fourth form: zero exit, edge facts, circle facts plugged in

Lane O-CL1 (`_OCL`), group G9. The gate head with every produced exit plugged in:

* the zero exit (a): S-REG-CHAIN3 G32 `zsp02SmoothExit74 S hεr`;
* the edge facts (c)(d)(e): O-RANK2's `edgeCutFactsAt3_ORK` (G5a / G6a / G7a + the rim rank), with
  the component models (S-EDGE-INT2) inside `edgeExitAt2_OCL`;
* the circle facts (f): G8 / G8b `circleCutFactsAt2_OCL` (only FDC03's saturation left).

**`closed_rows_gate4_OCL`**: rows `Rw : FC39RowsV2 W ∅` linked at `D_R` and GROUP G's certificate
from: FDC04's member facts `Htail` at `D_R` (S-REG-NUM), `SlimExit74` on `P` (b), FDC03's saturation
`M₃ = q₀⁻¹(C₁)` (f, EDP06 (3)), the junction face facts (g), the rim facts (h) with the corner
descent and rank data (i). **`register_yields_closed_rows_gate4_OCL`**: the same on the register's
sources (`Htail` from S-REG-NUM's member facts, `T.Nb`, `T.cw` from the numerics record).
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

/-- The produced stage geometry at `D_R` on the produced zero exit. -/
abbrev stagesAtZ_OCL : ClosedStageGeometryU74 (S.goodCut_OCL B hT hεr) (S.zsp02SmoothExit74 hεr) :=
  S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)

/-- The produced edge exit at `D_R` (zero exit of S-REG-CHAIN3, edge facts of O-RANK2). -/
def edgeExitAtZ_OCL : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A) :=
  S.edgeExitAt2_OCL B hT hNb hcw hεr A (S.zsp02SmoothExit74 hεr)
    (S.edgeCutFactsAt3_ORK B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw Htail)

/-- The produced remainder exit at `D_R` from FDC03's saturation. -/
def finalExitAtZ_OCL
    (hsat : (S.stagesAtZ_OCL B hT hεr A).cut.M₃ = (S.stagesAtZ_OCL B hT hεr A).cut.circleRegion) :
    FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A) :=
  S.fdc03RemainderAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
    (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
    (S.circleCutFactsAt2_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) Htail hsat)

/-- **FC39 gate 1A at `D_R`, fourth form** (zero, edge and circle exits produced). -/
theorem closed_rows_gate4_OCL
    (X : SlimExit74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut)
    (hsat : (S.stagesAtZ_OCL B hT hεr A).cut.M₃ = (S.stagesAtZ_OCL B hT hεr A).cut.circleRegion)
    (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) X)
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail hsat))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      ((S.stagesAtZ_OCL B hT hεr A).rows
        (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) X)
        (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
        (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail hsat)))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) := by
  obtain ⟨Rw, L⟩ := S.closed_rows_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) _ _ _ faces
    (EDP06CircleAgreementU74.ofCornerData faces rims hdesc hrank)
  exact ⟨Rw, L, exists_strongCertificate_of_rows_GFIN Rw⟩

end At

end ClosedChainEZRowsSource_RGC

/-- **FC39 gate 1A on the register's sources, fourth form**: on every member of the tail, at every
base point, with S-REG-NUM's numerics record `N` and member facts `Hm`, for every bases object `B`
and every `Ab`, the residual inputs (b) slim exit, (f) saturation, (g) faces, (h) rims, (i) corner
data on the produced stage geometry at `D_R` give rows linked at `D_R` and GROUP G's certificate. -/
theorem register_yields_closed_rows_gate4_OCL (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∃ Hm : ∀ B : ClosedBases74 S,
              ClosedFdcMemberFacts74 S B, ∀ (B : ClosedBases74 S) (Ab : SmoothStageBases74 S)
              (X : SlimExit74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).A
                (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut)
              (hsat : (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut.M₃ =
                (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut.circleRegion)
              (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab)
                (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab
                  (S.zsp02SmoothExit74 N.eps_lt) X)
                (S.edgeExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab
                  ((Hm B).facts _))
                (S.finalExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab
                  ((Hm B).facts _) hsat))
              (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).A
                (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut
                ((S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).rows
                  (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab
                    (S.zsp02SmoothExit74 N.eps_lt) X)
                  (S.edgeExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab
                    ((Hm B).facts _))
                  (S.finalExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab
                    ((Hm B).facts _) hsat))),
              (∀ e, CornerDescent74 faces.facts rims e) →
              (∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) →
              ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
                Nonempty (StrongCertificate (Wseq m) (BoundaryTori.empty (Wseq m))) := by
  obtain ⟨T, -, -, -, hR⟩ := register_yields_fdcFacts_RNUM K hK A hA Wseq gseq hf hg
  refine ⟨T, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, h0, h14, n, hn⟩ := hR R
  refine ⟨εr, δ, Λz, h0, h14, n, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := hn m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hx, ⟨N⟩, hB⟩ := hS x₀
  exact ⟨S, hx, N, hB, fun B Ab X hsat faces rims hdesc hrank =>
    S.closed_rows_gate4_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab ((hB B).facts _) X hsat
      faces rims hdesc hrank⟩

end DifferentialGeometry.Geometry.Collapse
