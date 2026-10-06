import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdc04CompleteRegisterFD4
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGateFinalJN74

/-!
# Draft 74, FDC04's complete row WITH the FC39 fields (B:7367–7435, clause (1)) at `D_R`

Lane S-JUNCTIONS (by S-JUNCTIONS5), G34 consumer (suffix `_JN74`). The clause table of
`thm:fibration-actual-closed-decomposition` (B:7367–7435): clauses (2)–(5) (finite compact pieces,
cover with disjoint interiors, common faces, horizontal disks and rims) are
`fdc04_row_complete_at_OCL_FD4` (S-FDC04b G7); clause (1) ("the domains supply every geometric
field of FC39 on the ORIGINAL closed carrier") is the FC39 gate 1A at the produced cut choice,
`closed_rows_gate_final_OCL` (G32): the face facts g1–g7, the rim facts, the corner descent and
rank data, rows linked at `D_R` and a strong certificate (the FC39 certificate of the carrier).

* `fdc04_fc39_final_at_OCL_JN74`: both rows at one source, for any bases object `B`, stage bases
  `Ab`, FDC facts `Htail` and `5 ≤ K`;
* `register_yields_fdc04_fc39_final_JN74`: the register consumer, as
  `register_yields_fdc04_complete_FD4` with the FC39 fields added (hypotheses of the register
  only).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **FDC04's complete row and the FC39 fields at one source at `D_R`.** -/
theorem fdc04_fc39_final_at_OCL_JN74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S) (N : ClosedRowsNumericsAt74 S) (hK : 5 ≤ K) (A : SmoothStageBases74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt)) :
    type_of% (S.fdc04_row_complete_at_OCL_FD4 B N hK A Htail) ∧
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
        ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
        Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  ⟨S.fdc04_row_complete_at_OCL_FD4 B N hK A Htail,
    S.closed_rows_gate_final_OCL B N.strategy_below N.eps_lt A hK N.nb_eq N.cw_eq Htail⟩

end ClosedChainEZRowsSource_RGC

/-- **Consumer: the register yields FDC04's complete row and the FC39 fields at `D_R`**. -/
theorem register_yields_fdc04_fc39_final_JN74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∃ Hm : ∀ B : ClosedBases74 S,
              ClosedFdcMemberFacts74 S B, ∀ (B : ClosedBases74 S) (Ab : SmoothStageBases74 S),
              type_of% (S.fdc04_row_complete_at_OCL_FD4 B N (le_trans (by norm_num) hK) Ab
                ((Hm B).facts _)) ∧
              ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
                Nonempty (StrongCertificate (Wseq m) (BoundaryTori.empty (Wseq m))) :=
  (register_yields_fdcFacts_RNUM K hK A hA Wseq gseq hf hg).imp fun T hT R =>
    (hT.2.2.2 R).imp fun εr h1 => h1.imp fun δ h2 => h2.imp fun Λz h3 =>
      ⟨h3.1, h3.2.1, h3.2.2.imp fun n hn m hm => (hn m hm).imp fun M h4 =>
        ⟨h4.1, fun x₀ => (h4.2 x₀).imp fun S h5 =>
          ⟨h5.1, h5.2.1.elim fun N => ⟨N, h5.2.2, fun B Ab =>
            S.fdc04_fc39_final_at_OCL_JN74 B N (le_trans (by norm_num) hK) Ab
              ((h5.2.2 B).facts _)⟩⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
