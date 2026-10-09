import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCoverAtOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsAtDRU74LND

/-!
# Draft 74 CL1, G4b: rows of the chain outputs at `D_R`, with the value rows and the register

Lane O-CL1 (`_OCL`), group G4b. CL1 (`closed_rows_of_chain_outputs74`, revised) at the produced
cut choice `D_R = S.goodCut_OCL B hT hεr`, on the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` (G3a), with the remainder exit's cover produced (G4a):

* **`remainingActualRowExitsU74_of_parts_OCL`**: `Hrows` at `D_R` from the RESIDUAL inputs only —
  the zero exit, S-JUNCTIONS' slim exits `SlimExit74` on `P`, the edge exit, the circle facts,
  the junction face and rim / corner facts (FDC04's cover is produced);
* **`closed_rows_values_at_OCL`**: S-LANDING2 G5's `closed_rows_values_atDR_U74` fed with it:
  `Rw : FC39RowsV2 W ∅` linked at `D_R` (revised table), G14's value rows on `W`, the
  `transport_R74` identities, and GROUP G's certificate;
* **`register_yields_closed_rows_at_OCL`**: on the register's sources (S-REG-NUM's numerics
  record `N` and member facts), for every bases object, the residual inputs on the produced
  stage geometry give the linked rows at `D_R` and the certificate.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
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

/-- **`Hrows` at `D_R` from the residual inputs** (FDC04's cover produced by G4a). -/
theorem remainingActualRowExitsU74_of_parts_OCL
    (X : SlimExit74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (cf : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X) edge (S.fdc03RemainderAt_OCL B hT hεr A zero edge cf))
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X) edge (S.fdc03RemainderAt_OCL B hT hεr A zero edge cf)
      faces) :
    RemainingActualRowExitsU74 S B (S.goodCut_OCL B hT hεr) :=
  S.remainingActualRowExitsU74_at_OCL B hT hεr A zero _ edge _ faces rims

/-- **CL1 at `D_R` with the value rows** (S-LANDING2 G5 `closed_rows_values_atDR_U74`): the rows
linked at `D_R`, G14's value rows on `W`, the transport identities and the certificate. -/
theorem closed_rows_values_at_OCL (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (X : SlimExit74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (cf : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X) edge (S.fdc03RemainderAt_OCL B hT hεr A zero edge cf))
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero)
      (S.zsp04ExitAt_OCL B hT hεr A zero X) edge (S.fdc03RemainderAt_OCL B hT hεr A zero edge cf)
      faces) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      (M.ψ '' (S.goodCut_OCL B hT hεr).edgeSet = M.ψ '' (S.goodCut_OCL B hT hεr).M₂ ∩
          (S.stageProjW_R74 1 ⁻¹' (S.chain.toChain.finalBase_BAS 1 ∩
            edgeRatio_R74 S.F.family.toLocalChartPacketsC14) ∩
          {x | S.edgeHeightW_R74 x ≤ R.edgeLevel_R74}) ∧
        M.ψ '' (S.goodCut_OCL B hT hεr).M₃ ⊆ S.stageProjW_R74 0 ⁻¹'
          (S.chain.toChain.finalBase_BAS 0 ∩
            gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets) ∧
        M.ψ '' S.chain.zeroUnion_ZSP35 ∪ M.ψ '' (S.goodCut_OCL B hT hεr).slimSet ∪
          M.ψ '' (S.goodCut_OCL B hT hεr).M₂ = univ ∧
        ∀ j x, S.stageProjW_R74 j x =
          S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j (M.ψ.symm x))) ∧
      (M.ψ '' (S.goodCut_OCL B hT hεr).M₃ = M.ψ '' (S.goodCut_OCL B hT hεr).M₂ \
          relInt (M.ψ '' (S.goodCut_OCL B hT hεr).M₂)
            (M.ψ '' (S.goodCut_OCL B hT hεr).edgeSet) ∧
        M.ψ '' frontier (S.goodCut_OCL B hT hεr).slimSet =
          frontier (M.ψ '' (S.goodCut_OCL B hT hεr).slimSet) ∧
        (∀ j (T' : Set (BlockSpace (fun _ : CGPTag
            S.F.family.toLocalChartPacketsC14.toLocalChartFamily
            S.F.family.toLocalChartPacketsC14.zero => EuclideanSpace ℝ (Fin 2)))),
          (S.chain.toGaf02ChainE.cutQ_R74 j ∘ M.ψ.symm) ⁻¹' T' =
            M.ψ '' (S.chain.toGaf02ChainE.cutQ_R74 j ⁻¹' T')) ∧
        M.ψ '' (S.goodCut_OCL B hT hεr).edgeSource =
          (S.chain.toGaf02ChainE.cutQ_R74 1 ∘ M.ψ.symm) ⁻¹'
            (S.goodCut_OCL B hT hεr).edgeBaseOpen ∧
        M.ψ '' (S.goodCut_OCL B hT hεr).circleSource =
          (S.chain.toGaf02ChainE.cutQ_R74 0 ∘ M.ψ.symm) ⁻¹'
            (S.goodCut_OCL B hT hεr).circleBaseOpen) ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  closed_rows_values_atDR_U74 S B hT hεr Htail
    (S.remainingActualRowExitsU74_of_parts_OCL B hT hεr A zero X edge cf faces rims)

end At

end ClosedChainEZRowsSource_RGC

/-- **CL1 / gate 1A on the register's sources** (S-REG-NUM's numerics record `N` and member facts;
S-LANDING2 G5's register plumbing): for every bases object `B` and every `A`, the residual inputs
on the produced stage geometry at `D_R` give rows linked at `D_R` and GROUP G's certificate. -/
theorem register_yields_closed_rows_at_OCL (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
              (edge : EDP04WholeDiskExitU74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero))
              (cf : CircleCutFacts74 (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).A
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero).cut)
              (faces : EDP05HorizontalExitU74
                (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero)
                (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab zero X) edge
                (S.fdc03RemainderAt_OCL B N.strategy_below N.eps_lt Ab zero edge cf)),
              EDP06CircleAgreementU74 (S.closedStagesAt_OCL B N.strategy_below N.eps_lt Ab zero)
                (S.zsp04ExitAt_OCL B N.strategy_below N.eps_lt Ab zero X) edge
                (S.fdc03RemainderAt_OCL B N.strategy_below N.eps_lt Ab zero edge cf) faces →
              ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
                Nonempty (StrongCertificate (Wseq m) (BoundaryTori.empty (Wseq m))) := by
  obtain ⟨T, hR⟩ := register_yields_closed_rows_atDR_of_rows_U74 K hK A hA Wseq gseq hf hg
  refine ⟨T, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, h0, h14, n, hn⟩ := hR R
  refine ⟨εr, δ, Λz, h0, h14, n, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := hn m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hx, N, hB⟩ := hS x₀
  exact ⟨S, hx, N, fun B Ab zero X edge cf faces rims => hB B
    (S.remainingActualRowExitsU74_of_parts_OCL B N.strategy_below N.eps_lt Ab zero X edge cf
      faces rims)⟩

end DifferentialGeometry.Geometry.Collapse
