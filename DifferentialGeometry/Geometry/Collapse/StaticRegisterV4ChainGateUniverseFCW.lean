import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainConsumersAtDRFCW

/-!
# The universe-0 gate: FC39 gate 1A's residual inputs feed PBR02, PBR03, FC44 at `D_R`

Lane S-FC-WRAP5 (suffix `_FCW`), group G17 (review 78 Q12, last paragraph of §12.3: universe).
The tree's gate `closed_rows_gate4_OCL` (O-CL1) is stated at `CompactCarrier.{0}` (its stage
geometry, the zero exit, the edge exits and the corner records live over `Type 0` carriers), while
the FCW layer of groups G15 / G16 (`closed_rows_sequence_head_of_rowsAt_FCW`, `_atDR_FCW`) is
universe polymorphic: it consumes the local layer `hrowsAt` at `CompactCarrier.{u}`. Generalising
the gate (about forty modules of the closed-landing chain) is not needed for the closed route: the
standing sequences of the closed threshold are over `CompactCarrier.{0}`, and `hrowsAt` at universe
`0` is exactly what the gate delivers from its residual inputs. So the bridge is a universe-0
instantiation:

* `closed_rowsAt_all_of_residuals_FCW`: the residual inputs (b) slim exit, (f) saturation, (g)
  faces, (h) rims, (i) corner descent and rank data of FC39 gate 1A at every source, numerics
  record, bases object and FDC facts at `D_R` give `hrowsAt` at universe 0
  (`closed_rows_gate4_OCL`);
* `pbr02_certificate_gate_FCW`, `closedSeq_gate_FCW`, `pbr03_threshold_gate_FCW`,
  `fc44_closed_binding_gate_FCW`: the consumers of G16 at universe 0 with `hres` as the only
  explicit hypothesis (the residual inputs of the gate; once the producers deliver them, `hres` is
  replaced by a proof and the four statements are unconditional).

No lowering of a universe-`u` carrier to universe `0` is claimed; for `u > 0` only the `hrowsAt`
forms of G16 apply.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Gate

variable (K : ℕ) (hres : ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
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
          ∀ e, ∃ Kr : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 Kr))

include hres

/-- **The local layer at universe 0 from the gate's residual inputs**: `hrowsAt` for every source,
numerics record, bases object and FDC facts at `D_R`. -/
theorem closed_rowsAt_all_of_residuals_FCW :
    ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (W : CompactCarrier.{0})
      (g : SmoothRiemannianMetric W.model W.Carrier) (M : ClosedModel W g) (δ εr Λz : ℝ)
      (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (N : ClosedRowsNumericsAt74 S)
      (B : ClosedBases74 S),
      ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
        ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw :=
  fun T R W g M δ εr Λz S N B Htail =>
    closed_rowsAt_of_residuals_FCW S N B Htail (hres T R W g M δ εr Λz S N B Htail)


/-- **PBR02, certificate part, on the same-source head** (B:10257–10275): the static data of
`pbr02_staticEZ_RGC` AND, at every register on every member from the common tail `n ≥ R.later.tail`
on, a closed strong certificate `Dc` (rim-product clause) and, by FC42 form (b), a raw graph
presentation or a closed auxiliary `sec ≥ 0` metric. Only the local layer `hrowsAt` is assumed.
Universe 0: the gate's residual inputs `hres` replace `hrowsAt`
(`closed_rowsAt_all_of_residuals_FCW`). -/
theorem pbr02_certificate_gate_FCW (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
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
                    SectionalBoundedBelow g' 0)) :=
  pbr02_certificate_atDR_FCW K hK A hA Wseq gseq hf hg
    (closed_rowsAt_all_of_residuals_FCW K hres)

/-- **The per-sequence closed binding on the same-source head**: on every closed standing sequence
there is a tail `n` (the head's actual `n_good`) on which every member has a closed strong
certificate (the `closedSeq` input of the common static threshold).
Universe 0: the gate's residual inputs `hres` replace `hrowsAt`
(`closed_rowsAt_all_of_residuals_FCW`). -/
theorem closedSeq_gate_FCW (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x)
    (W : ℕ → CompactCarrier.{0}) [hW : ∀ m, ConnectedSpace (W m).Carrier]
    (g : ∀ m, SmoothRiemannianMetric (W m).model (W m).Carrier)
    (hseq : ∀ m, (∀ p, curvatureRadius (g m) p ≠ ⊤) ∧
      closedCollapseHypotheses (W m) (g m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ Dc : ClosedDecompositionCertificate (W m), Dc.cert.RimProduct :=
  closedSeq_atDR_FCW K hK A hA (closed_rowsAt_all_of_residuals_FCW K hres) W g hseq

/-- **PBR03, the closed static threshold, on the same-source head** (B:10277–10333, the
nonnegative branch included, form (b)): there is `w₀ < ω₃` such that every closed connected member
with finite curvature scales at volume ratio `w₀` and the whole-ball derivative bounds is a graph
manifold (raw presentation) or carries a closed auxiliary `sec ≥ 0` metric.
Universe 0: the gate's residual inputs `hres` replace `hrowsAt`
(`closed_rowsAt_all_of_residuals_FCW`). -/
theorem pbr03_threshold_gate_FCW (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            SectionalBoundedBelow g' 0) :=
  pbr03_threshold_atDR_FCW K hK A hA (closed_rowsAt_all_of_residuals_FCW K hres)

/-- **FC44's closed binding on the same-source head** (B:9998–10024, B:10336): ONE strategy `T`
(the head's), the register inhabited, the validity record, and at EVERY register `R` the stage part
of `fc44_closed_binding_RGC` (the chain's numbers are `R`'s stage values chosen first, PR10's `C_ρ`
dominates every constant, `C_ρ Δ Λ < 10⁻⁶`; read from `T.Nb`, `T.cw` only) together with the head's
member part at the SAME `ε_r, δ, Λ_z` and the common tail `n ≥ R.later.tail`: on every member the
model with its identification and, at every base point, the source with its FDC facts and rows at
`D_R`.
Universe 0: the gate's residual inputs `hres` replace `hrowsAt`
(`closed_rowsAt_all_of_residuals_FCW`). -/
theorem fc44_closed_binding_gate_FCW (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
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
                  ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw :=
  fc44_closed_binding_atDR_FCW K hK A hA Wseq gseq hf hg
    (closed_rowsAt_all_of_residuals_FCW K hres)

end Gate

end DifferentialGeometry.Geometry.Collapse
