import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeFactsAtOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsAtOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCornersU74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeComponentModelsEIMExits

/-!
# Draft 74, FC39 gate 1A at `D_R`: the certificate on the actual chain outputs, residual inputs

Lane O-CL1 (`_OCL`), group G5b. FC39 gate 1A (`exists_strongCertificate_of_rows_GFIN` on the rows of
the ACTUAL chain at the produced cut choice `D_R`), with everything produced so far plugged in:
the cut choice `D_R` (O-CL0 G1), the stage geometry `P` (G3a), FDC04's cover (G4a), the edge facts'
`proper / fibre_disk / cbase_compact` (G5a, through `edgeCutFactsAt_OCL`), the EDP06 corner exit
from S-JUNCTIONS2 G6 (`EDP06CircleAgreementU74.ofCornerData`), the slim exit from S-JUNCTIONS G4.

* `edgeExitAt_OCL`: the edge exit from the edge facts and FDC02's set equality (the component
  models are S-EDGE-INT2's `edgeBundle74_models_EIM`: E2 + E3 + E4c, no input);
* **`closed_rows_gate_OCL`**: rows linked at `D_R` and GROUP G's certificate from the RESIDUAL
  inputs: zero exit; `SlimExit74` on `P`; edge facts (= `rank_two` + `cbase_domain` by G5a);
  FDC02's set equality; `CircleCutFacts74`; the junction face
  facts; the rim facts with the corner descent and rank data;
* **`register_yields_closed_rows_gate_OCL`**: the same on the register's sources (every member of
  the tail, every base point, every bases object).
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
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- The edge exit at `D_R` from the edge facts and FDC02's set equality (component models:
`edgeBundle74_models_EIM`). -/
def edgeExitAt_OCL
    (facts : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (hE : (S.goodCut_OCL B hT hεr).edgeSet =
      gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
        (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹' (S.goodCut_OCL B hT hεr).C₂ ∩
          {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74})) :
    EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero) :=
  ⟨facts, (edgeBundle74_models_EIM _ _ facts).some, hE⟩

/-- **FC39 gate 1A at `D_R` from the residual inputs**: rows `Rw : FC39RowsV2 W ∅` linked to the
actual chain at `D_R` and GROUP G's strong certificate. -/
theorem closed_rows_gate_OCL
    (X : SlimExit74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (facts : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (hE : (S.goodCut_OCL B hT hεr).edgeSet =
      gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
        (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹' (S.goodCut_OCL B hT hεr).C₂ ∩
          {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74}))
    (cf : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X) (S.edgeExitAt_OCL B hT hεr A zero facts hE)
      (S.fdc03RemainderAt_OCL B hT hεr A zero (S.edgeExitAt_OCL B hT hεr A zero facts hE)
        cf))
    (rims : JunctionRimFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut
      ((S.closedStagesAt_OCL B hT hεr A zero).rows (S.zsp04ExitAt_OCL B hT hεr A zero X)
        (S.edgeExitAt_OCL B hT hεr A zero facts hE)
        (S.fdc03RemainderAt_OCL B hT hεr A zero
          (S.edgeExitAt_OCL B hT hεr A zero facts hE) cf)))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) := by
  obtain ⟨Rw, L⟩ := S.closed_rows_at_OCL B hT hεr A zero _ _ _ faces
    (EDP06CircleAgreementU74.ofCornerData faces rims hdesc hrank)
  exact ⟨Rw, L, exists_strongCertificate_of_rows_GFIN Rw⟩

end At

end ClosedChainEZRowsSource_RGC

/-- **FC39 gate 1A on the register's sources** (S-REG-NUM's numerics record `N` and member facts,
S-LANDING2 G5's plumbing): on every member of the tail, at every base point, for every bases object
`B` and every `Ab`, the residual inputs on the produced stage geometry at `D_R` give rows linked at
`D_R` and GROUP G's certificate. -/
theorem register_yields_closed_rows_gate_OCL (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∀ (B : ClosedBases74 S) (Ab : SmoothStageBases74 S)
              (zero : ZSP02SmoothExit74 S)
              (X : SlimExit74 (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).A
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).cut)
              (facts : EdgeCutFacts74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).A
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).cut)
              (hE : (S.goodCut_OCL B N.strategy_below N.eps_lt).edgeSet =
                gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
                  (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹'
                      (S.goodCut_OCL B N.strategy_below N.eps_lt).C₂ ∩
                    {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74}))
              (cf : CircleCutFacts74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).A
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).cut)
              (faces : EDP05HorizontalExitU74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero)
                (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab zero X)
                (S.edgeExitAt_OCL B N.strategy_below N.eps_lt Ab zero facts hE)
                (S.fdc03RemainderAt_OCL B N.strategy_below N.eps_lt Ab zero
                  (S.edgeExitAt_OCL B N.strategy_below N.eps_lt Ab zero facts hE) cf))
              (rims : JunctionRimFacts74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).A
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).cut
                ((S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).rows
                  (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab zero X)
                  (S.edgeExitAt_OCL B N.strategy_below N.eps_lt Ab zero facts hE)
                  (S.fdc03RemainderAt_OCL B N.strategy_below N.eps_lt Ab zero
                    (S.edgeExitAt_OCL B N.strategy_below N.eps_lt Ab zero facts hE) cf))),
              (∀ e, CornerDescent74 faces.facts rims e) →
              (∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) →
              ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
                Nonempty (StrongCertificate (Wseq m) (BoundaryTori.empty (Wseq m))) := by
  obtain ⟨T, hR⟩ := register_yields_closed_rows_at_OCL K hK A hA Wseq gseq hf hg
  refine ⟨T, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, h0, h14, n, hn⟩ := hR R
  refine ⟨εr, δ, Λz, h0, h14, n, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := hn m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hx, N, hB⟩ := hS x₀
  exact ⟨S, hx, N, fun B Ab zero X facts hE cf faces rims hdesc hrank =>
    hB B Ab zero X _ cf faces (EDP06CircleAgreementU74.ofCornerData faces rims hdesc hrank)⟩

end DifferentialGeometry.Geometry.Collapse
