import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdcFactsHeadFCW
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate4OCL

/-!
# The same-source sequence head of the closed rows producer (review 78 Q12, D78-12)

Lane S-FC-WRAP5 (suffix `_FCW`), group G15. Two layers, as prescribed by D78-12:

* the LOCAL layer `hrowsAt`: at ONE cut choice `D_R = S.goodCut_OCL B N.strategy_below N.eps_lt`,
  `ClosedFdcFacts74 D_R → ∃ Rw : FC39RowsV2 W ∅, ClosedRowsLinkAtU74 S B D_R Rw`, for every source
  `S` with its numerics record `N` and every bases object `B`. FC39 gate 1A at `D_R`
  (`closed_rows_gate4_OCL`, O-CL1) gives it from the residual inputs (b) slim exit `X`, (f)
  saturation `hsat`, (g) faces, (h) rims, (i) corner descent and rank data, which enter as the
  explicit hypothesis `hres` of `closed_rows_sequence_head_FCW` (the data are produced once the
  producers arrive: then `hres` is replaced by a proof and the head is unconditional).
  `closed_rowsAt_of_residuals_FCW` is that step at one source.
* the SAME-SOURCE sequence head (`closed_rows_sequence_head_of_rowsAt_FCW`): ONE strategy `T`
  refining the complete one with validity, `T.Nb = maxNb`, `T.cw = maxCw`, a nonempty register
  (`register_yields_fdcFacts_head_FCW`); at every register `R`: `ε_r ∈ (0, 1/4)`, `δ`, `Λ_z` and
  `n ≥ R.later.tail` (the actual `n_good`, before any member); on every member `m ≥ n` the model
  with its identification, nonempty `M.X`, and at EVERY base point `x₀` a source `S` with
  `S.chain.x₀ = x₀`, numerics `N`, a bases object `B`, the FDC facts at `D_R` AND rows linked at
  `D_R`. Quantifier order: strategy ≺
  register ≺ parameters and common tail ≺ member ≺ base point; `n` does not depend on `x₀`; `Rw`
  may depend on `x₀`.

Universes: the local layer and the head are stated at `CompactCarrier.{u}`; the gate
`closed_rows_gate4_OCL` is at `CompactCarrier.{0}`, so `closed_rows_sequence_head_FCW` (residual
inputs as hypotheses) is at universe 0 and `closed_rows_sequence_head_of_rowsAt_FCW` is
universe polymorphic.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The local layer at one source, universe 0**: the residual inputs of the gate at `D_R` give
rows linked at `D_R` (`closed_rows_gate4_OCL`; the strong certificate is not needed here). -/
theorem closed_rowsAt_of_residuals_FCW {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (N : ClosedRowsNumericsAt74 S)
    (B : ClosedBases74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt))
    (hres : ∃ (Ab : SmoothStageBases74 S)
      (X : SlimExit74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).A
        (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut)
      (hsat : (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut.M₃ =
        (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut.circleRegion)
      (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab)
        (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab (S.zsp02SmoothExit74 N.eps_lt) X)
        (S.edgeExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail)
        (S.finalExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail hsat))
      (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).A
        (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut
        ((S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).rows
          (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab (S.zsp02SmoothExit74 N.eps_lt) X)
          (S.edgeExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail)
          (S.finalExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail hsat))),
      Nonempty (∀ e, CornerDescent74 faces.facts rims e) ∧
        ∀ e, ∃ Kr : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 Kr)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw := by
  obtain ⟨Ab, X, hsat, faces, rims, ⟨hdesc⟩, hrank⟩ := hres
  obtain ⟨Rw, L, -⟩ := S.closed_rows_gate4_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab
    Htail X hsat faces rims hdesc hrank
  exact ⟨Rw, L⟩

/-- **The same-source sequence head** (review 78 Q12 / D78-12) from the local layer `hrowsAt`
(module header). -/
theorem closed_rows_sequence_head_of_rowsAt_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    (hrowsAt : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (W : CompactCarrier.{u})
      (g : SmoothRiemannianMetric W.model W.Carrier) (M : ClosedModel W g) (δ εr Λz : ℝ)
      (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (N : ClosedRowsNumericsAt74 S)
      (B : ClosedBases74 S),
      ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
        ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, R.later.tail ≤ n ∧ ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
          M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧ Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∃ B : ClosedBases74 S,
              ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) ∧
              ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw := by
  obtain ⟨T, hTU, hv, hNb, hcw, hreg, hR⟩ := register_yields_fdcFacts_head_FCW K hK A hA Wseq gseq
    hf hg
  refine ⟨T, hTU, hv, hNb, hcw, hreg, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, h0, h14, n, hnt, hn⟩ := hR R
  refine ⟨εr, δ, Λz, h0, h14, n, hnt, fun m hm => ?_⟩
  obtain ⟨M, hM, hne, hS⟩ := hn m hm
  refine ⟨M, hM, hne, fun x₀ => ?_⟩
  obtain ⟨S, hx, ⟨N⟩, hH⟩ := hS x₀
  exact ⟨S, hx, N, S.bases74, (hH S.bases74).facts _,
    hrowsAt T R (Wseq m) (gseq m) M δ εr Λz S N S.bases74 ((hH S.bases74).facts _)⟩

/-- **The same-source sequence head with the gate's residual inputs as the explicit hypothesis
`hres`** (universe 0): at every source `S` with numerics `N`, bases `B` and the FDC facts at `D_R`,
the slim exit, the saturation, the faces, the rims and the corner descent / rank data of FC39 gate
1A exist (the producers are not yet delivered; once they are, `hres` is replaced by a proof). -/
theorem closed_rows_sequence_head_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    (hres : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (W : CompactCarrier.{0})
      (g : SmoothRiemannianMetric W.model W.Carrier) (M : ClosedModel W g) (δ εr Λz : ℝ)
      (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (N : ClosedRowsNumericsAt74 S)
      (B : ClosedBases74 S)
      (Htail : ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt)),
      ∃ (Ab : SmoothStageBases74 S)
        (X : SlimExit74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).A
          (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut)
        (hsat : (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut.M₃ =
          (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut.circleRegion)
        (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab)
          (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab (S.zsp02SmoothExit74 N.eps_lt) X)
          (S.edgeExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail)
          (S.finalExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail hsat))
        (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).A
          (S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).cut
          ((S.stagesAtZ_OCL B N.strategy_below N.eps_lt Ab).rows
            (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab (S.zsp02SmoothExit74 N.eps_lt) X)
            (S.edgeExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail)
            (S.finalExitAtZ_OCL B N.strategy_below N.nb_eq N.cw_eq N.eps_lt Ab Htail hsat))),
        Nonempty (∀ e, CornerDescent74 faces.facts rims e) ∧
          ∀ e, ∃ Kr : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 Kr)) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, R.later.tail ≤ n ∧ ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
          M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧ Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∃ B : ClosedBases74 S,
              ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) ∧
              ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw :=
  closed_rows_sequence_head_of_rowsAt_FCW K hK A hA Wseq gseq hf hg
    fun T R W g M δ εr Λz S N B Htail =>
      closed_rowsAt_of_residuals_FCW S N B Htail (hres T R W g M δ εr Λz S N B Htail)

end DifferentialGeometry.Geometry.Collapse
