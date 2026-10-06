import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGateOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeSetEqOCL

/-!
# Draft 74, FC39 gate 1A at `D_R`, second form: FDC02's set equality produced

Lane O-CL1 (`_OCL`), group G6b. The gate heads of G5 with the clause (e) (FDC02's set equality
`M^edge = U₂ ∩ q₁⁻¹(C₂) ∩ {A/s ≤ 4Δ}`) PRODUCED by G6a's `goodCut_edgeSet_eq_OCL`:

* `edgeExitAt2_OCL`: the edge exit from the edge facts alone;
* **`closed_rows_gate2_OCL`**: rows linked at `D_R` + GROUP G's certificate from: zero exit,
  `SlimExit74` on `P`, the edge facts (= `rank_two` + `cbase_domain` by G5a), the circle facts, the
  junction face facts, the rim facts with the corner descent and rank data;
* **`register_yields_closed_rows_gate2_OCL`**: the same on the register's sources (the numerics
  record `N` supplies `T.Nb`, `T.cw`).
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
  (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- The edge exit at `D_R` from the edge facts alone (FDC02's set equality: G6a). -/
def edgeExitAt2_OCL
    (facts : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero) :=
  S.edgeExitAt_OCL B hT hεr A zero facts (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)

/-- **FC39 gate 1A at `D_R`, second form** (FDC02's set equality produced). -/
theorem closed_rows_gate2_OCL
    (X : SlimExit74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (facts : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (cf : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X) (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero facts)
      (S.fdc03RemainderAt_OCL B hT hεr A zero (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero facts)
        cf))
    (rims : JunctionRimFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut
      ((S.closedStagesAt_OCL B hT hεr A zero).rows (S.zsp04ExitAt_OCL B hT hεr A zero X)
        (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero facts)
        (S.fdc03RemainderAt_OCL B hT hεr A zero
          (S.edgeExitAt2_OCL B hT hNb hcw hεr A zero facts) cf)))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate_OCL B hT hεr A zero X facts (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw) cf
    faces rims hdesc hrank

end At

end ClosedChainEZRowsSource_RGC

/-- **FC39 gate 1A on the register's sources, second form** (FDC02's set equality produced; the
numerics record `N` supplies `T.Nb` and `T.cw`). -/
theorem register_yields_closed_rows_gate2_OCL (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
              (cf : CircleCutFacts74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).A
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).cut)
              (faces : EDP05HorizontalExitU74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero)
                (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab zero X)
                (S.edgeExitAt2_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab zero facts)
                (S.fdc03RemainderAt_OCL B N.strategy_below N.eps_lt Ab zero
                  (S.edgeExitAt2_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab zero facts)
                  cf))
              (rims : JunctionRimFacts74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).A
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).cut
                ((S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).rows
                  (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab zero X)
                  (S.edgeExitAt2_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab zero facts)
                  (S.fdc03RemainderAt_OCL B N.strategy_below N.eps_lt Ab zero
                    (S.edgeExitAt2_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab zero facts)
                    cf))),
              (∀ e, CornerDescent74 faces.facts rims e) →
              (∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) →
              ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
                Nonempty (StrongCertificate (Wseq m) (BoundaryTori.empty (Wseq m))) := by
  obtain ⟨T, hR⟩ := register_yields_closed_rows_gate_OCL K hK A hA Wseq gseq hf hg
  refine ⟨T, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, h0, h14, n, hn⟩ := hR R
  refine ⟨εr, δ, Λz, h0, h14, n, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := hn m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hx, N, hB⟩ := hS x₀
  exact ⟨S, hx, N, fun B Ab zero X facts cf faces rims hdesc hrank =>
    hB B Ab zero X facts (S.goodCut_edgeSet_eq_OCL B N.strategy_below N.eps_lt N.nb_eq N.cw_eq) cf
      faces rims hdesc hrank⟩

end DifferentialGeometry.Geometry.Collapse
