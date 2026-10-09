import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSequenceHeadFCW
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFc44
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42SequenceBindings
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# PBR02 certificate part, PBR03 threshold and FC44 closed binding on the same-source head

Lane S-FC-WRAP5 (suffix `_FCW`), group G16. Review 78 Q12 (D78-12): the consumers of
`StaticRegisterV4CertificateFCW` (`pbr02_certificate_FCW`, `closedSeq_of_rows_FCW`,
`pbr03_threshold_FCW`) took a global `hrows` over ALL `T R`; the head of
`closed_rows_sequence_head_of_rowsAt_FCW` instead produces ONE strategy, ONE register-indexed
parameter record with the common late tail `n ≥ R.later.tail`, and at every member and base point a
source with the FDC facts and rows linked at `D_R`. The consumers `_atDR_FCW` take the LOCAL layer
`hrowsAt` only (`ClosedFdcFacts74 D_R → ∃ Rw, ClosedRowsLinkAtU74 S B D_R Rw`), choose `x₀` from the
nonempty `M.X` AFTER `n` and forget `∃ Rw, link` to the rows `Rw` only at the final call of
`exists_strongCertificate_of_rows_GFIN`. They return and consume the actual `n` (not
`R.later.tail`).

* `pbr02_certificate_atDR_FCW`: PBR02 in full (static fields, FC42 form (b)) on the head.
* `closedSeq_atDR_FCW`: the per-sequence closed binding (tail `n`).
* `pbr03_threshold_atDR_FCW`: PBR03 (closed threshold, nonnegative branch included).
* `fc44_closed_binding_atDR_FCW`: FC44's closed binding: the stage part of
  `fc44_closed_binding_RGC` at the head's strategy (only `T.Nb`, `T.cw` are read) and, at every
  register, the head's member part (every consumer reads the SAME assignment).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace


/-- **PBR02, certificate part, on the same-source head** (B:10257–10275): the static data of
`pbr02_staticEZ_RGC` AND, at every register on every member from the common tail `n ≥ R.later.tail`
on, a closed strong certificate `Dc` (rim-product clause) and, by FC42 form (b), a raw graph
presentation or a closed auxiliary `sec ≥ 0` metric. Only the local layer `hrowsAt` is assumed. -/
theorem pbr02_certificate_atDR_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
        ∃ n : ℕ, R.later.tail ≤ n ∧ ∀ m, n ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m),
            M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧ Nonempty M.X ∧
            (∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀) ∧
            ∃ Dc : ClosedDecompositionCertificate (Wseq m), Dc.cert.RimProduct ∧
              (Nonempty (RawGraphPresentation (Wseq m)) ∨
                ((Wseq m).model.boundary (Wseq m).Carrier = ∅ ∧
                  ∃ g' : SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier,
                    SectionalBoundedBelow g' 0)) := by
  obtain ⟨T, hTU, hv, hNb, hcw, hreg, hR⟩ := closed_rows_sequence_head_of_rowsAt_FCW K hK A hA
    Wseq gseq hf hg hrowsAt
  refine ⟨T, hTU, hv, hNb, hcw, hreg, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, h0, h14, n, hnt, hn⟩ := hR R
  refine ⟨εr, δ, Λz, h0, h14, n, hnt, fun m hm => ?_⟩
  obtain ⟨M, hM, hne, hS⟩ := hn m hm
  obtain ⟨x₀⟩ := hne
  obtain ⟨S, -, N, B, -, Rw, -⟩ := hS x₀
  obtain ⟨D⟩ := exists_strongCertificate_of_rows_GFIN Rw
  have := (hf m).connected
  exact ⟨M, hM, ⟨x₀⟩, fun y => (hS y).imp fun S' h => h.1, D.toClosed.toClosedCertificate,
    D.toClosed.rimProduct, D.raw_or_aux_nonneg (Wseq m)⟩

/-- **The per-sequence closed binding on the same-source head**: on every closed standing sequence
there is a tail `n` (the head's actual `n_good`) on which every member has a closed strong
certificate (the `closedSeq` input of the common static threshold). -/
theorem closedSeq_atDR_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x)
    (hrowsAt : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (W : CompactCarrier.{u})
      (g : SmoothRiemannianMetric W.model W.Carrier) (M : ClosedModel W g) (δ εr Λz : ℝ)
      (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (N : ClosedRowsNumericsAt74 S)
      (B : ClosedBases74 S),
      ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
        ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw)
    (W : ℕ → CompactCarrier.{u}) [hW : ∀ m, ConnectedSpace (W m).Carrier]
    (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier)
    (hseq : ∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
      closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ Dc : ClosedDecompositionCertificate (W m), Dc.cert.RimProduct := by
  obtain ⟨T, -, -, -, -, ⟨R⟩, hR⟩ := pbr02_certificate_atDR_FCW K hK A hA W g
    (fun m => ⟨(hseq m).2.1, hW m⟩) (fun m => (hseq m).2) hrowsAt
  obtain ⟨εr, δ, Λz, -, -, n, -, ht⟩ := hR R
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨-, -, -, -, Dc, hDc, -⟩ := ht m hm
  exact ⟨Dc, hDc⟩

/-- **PBR03, the closed static threshold, on the same-source head** (B:10277–10333, the
nonnegative branch included, form (b)): there is `w₀ < ω₃` such that every closed connected member
with finite curvature scales at volume ratio `w₀` and the whole-ball derivative bounds is a graph
manifold (raw presentation) or carries a closed auxiliary `sec ≥ 0` metric. -/
theorem pbr03_threshold_atDR_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x)
    (hrowsAt : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (W : CompactCarrier.{u})
      (g : SmoothRiemannianMetric W.model W.Carrier) (M : ClosedModel W g) (δ εr Λz : ℝ)
      (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (N : ClosedRowsNumericsAt74 S)
      (B : ClosedBases74 S),
      ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
        ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            SectionalBoundedBelow g' 0) :=
  closed_graph_threshold_of_sequence_binding_rimProduct_BQ K A
    (fun W _ g hseq => closedSeq_atDR_FCW K hK A hA hrowsAt W g hseq)
    fun W _ _ _ D hp =>
      exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct W D hp

/-- **FC44's closed binding on the same-source head** (B:9998–10024, B:10336): ONE strategy `T`
(the head's), the register inhabited, the validity record, and at EVERY register `R` the stage part
of `fc44_closed_binding_RGC` (the chain's numbers are `R`'s stage values chosen first, PR10's `C_ρ`
dominates every constant, `C_ρ Δ Λ < 10⁻⁶`; read from `T.Nb`, `T.cw` only) together with the head's
member part at the SAME `ε_r, δ, Λ_z` and the common tail `n ≥ R.later.tail`: on every member the
model with its identification and, at every base point, the source with its FDC facts and rows at
`D_R`. -/
theorem fc44_closed_binding_atDR_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        ((∀ j, 0 < (earlyDataSharedV4 K).Ξ j (R.stage.Γ j) ∧ 0 < R.stage.Sig j ∧
            128 * ((earlyDataSharedV4 K).Ξ j (R.stage.Γ j))⁻¹ * R.stage.Sig j ≤ 1 / 5 ∧
            0 ≤ R.stage.e j) ∧
          5 / 3 * (earlyDataSharedV4 K).Ξ 0 (R.stage.Γ 0) * R.stage.Sig 0 < R.stage.c 0 ∧
          R.stage.c 0 ≤ 1 / 512 ∧
          (5 / 3 * (earlyDataSharedV4 K).Ξ 0 (R.stage.Γ 0) * R.stage.Sig 0 * gafCutoffConstant *
              gafDerivativeBound + (earlyDataSharedV4 K).Ξ 0 (R.stage.Γ 0) * gafDerivativeBound +
              R.stage.e 0) < R.stage.c 0 ∧
          R.stage.c 0 ≤ 4 * gafKappa / 5 ∧ R.stage.c 0 ≤ 3 * R.stage.Sig 1 / 10 ∧
          (R.stage.c 0 + (5 / 3 * (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1) * R.stage.Sig 1 +
              (1 + (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1)) * R.stage.c 0)) < R.stage.c 1 ∧
          R.stage.c 1 ≤ 1 / 512 ∧
          ((5 / 3 * (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1) * R.stage.Sig 1 +
              (1 + (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1)) * R.stage.c 0) * gafCutoffConstant *
              (gafDerivativeBound + R.stage.c 0) +
              (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1) * (gafDerivativeBound + R.stage.c 0) +
              R.stage.e 1 + 2 * R.stage.c 0) < R.stage.c 1 ∧
          R.stage.c 1 ≤ 4 * gafKappa / 5 ∧ R.stage.c 1 ≤ 3 * R.stage.Sig 2 / 10 ∧
          (R.stage.c 1 + (5 / 3 * (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2) * R.stage.Sig 2 +
              (1 + (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2)) * R.stage.c 1)) < R.stage.c 2 ∧
          R.stage.c 2 ≤ 1 / 512 ∧
          ((5 / 3 * (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2) * R.stage.Sig 2 +
              (1 + (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2)) * R.stage.c 1) * gafCutoffConstant *
              (gafDerivativeBound + R.stage.c 1) +
              (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2) * (gafDerivativeBound + R.stage.c 1) +
              R.stage.e 2 + 2 * R.stage.c 1) < R.stage.c 2) ∧
        100 * (gafDerivativeBound + 1) *
            (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage ∧
        (∀ j, 2 * stageCwAt_V4C R.stage j / R.stage.Sig j ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage / 100) ∧
        closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.excl.Δ *
          R.later.scale.Λ < 1 / 10 ^ 6 ∧
        ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
          ∃ n : ℕ, R.later.tail ≤ n ∧ ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
            M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧ Nonempty M.X ∧
            ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
              ∃ N : ClosedRowsNumericsAt74 S, ∃ B : ClosedBases74 S,
                ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) ∧
                ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                  ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw := by
  obtain ⟨T, hTU, hv, hNb, hcw, hreg, hR⟩ := closed_rows_sequence_head_of_rowsAt_FCW K hK A hA
    Wseq gseq hf hg hrowsAt
  exact ⟨T, hTU, hv, hNb, hcw, hreg, fun R => ⟨R.stage.chain_numbers_RGC,
    R.stage.chain_scaleConstant_le_RGC hNb hcw, R.stage.smv_le_scaleConstant_RGC hNb hcw,
    R.later.regScale_Cρ, hR R⟩⟩

end DifferentialGeometry.Geometry.Collapse
