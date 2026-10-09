import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Chain
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Complete
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp01

/-!
# Register V4 yields the chain: the final consumer (lane C14-REG-CHAIN, G2)

`register_yields_chain_RGC` is lane FC39-V4C(b)'s final consumer `exists_closed_complete_V4C` with
ONE more cap layer (`exists_chainStrategy_RGC` at `closedStrategyCompleteV4C`: FC27's three test
thresholds in the register's slots) and ONE more exit on every member of every register's tail:
at the SAME instance `F` of the final family (C14D, projected to `LocalChartPacketsC14`), every
selection `sel` of original preimages carries a chain

`C : Gaf02Chain F.family.toLocalChartPackets K (Ξ_j(Γ_j)) Γ Σ e c (stageCwAt_V4C R.stage)`,
`C.sel = sel`,

whose numbers are the register's stage values field by field (they index its type), and whose
scale `s = C.scale = ℓ_ρ(C.E)` satisfies EDP01's (SD) with the REGISTER'S
`C_ρ = closedScaleConstantV4 D T R.stage` (D66-5: the chain constant
`100(L_gaf+1)(1 + b_gaf + c_w^{(0)}/Σ₀)` of `Gaf02Chain.edp01_GAF8` is dominated by the register's
`C_ρ`, fixed at the stage, before `Δ, Λ`, with `C_ρΔΛ < 10⁻⁶` at every register). `T` still
refines `closedStrategyCompleteV4C` (the chain caps keep `N_b, c_w, I₁, LmaxLow, endpointUp`), so
every register-level request and every native exit of `exists_closed_complete_V4C` holds verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **Register V4 yields the chain** (G2, see the module header): every conclusion of
`exists_closed_complete_V4C` at a strategy refining `closedStrategyCompleteV4C`, and on every member
of every register's tail, at the same instance of the final family, the chain object on the
register's own stage data for every selection, with EDP01's (SD) at the register's `C_ρ`. -/
theorem register_yields_chain_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      ClosedFamilyAtC14DV4 K Wseq gseq T ∧ T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        (3 * R.later.circle.βc < R.later.excl.β₂ ∧
          R.later.excl.β₂ < R.later.circle.γc / 1000 ∧
          3 * R.later.excl.β₂ < R.later.circle.δ ∧
          Lfr29NumericV4C R.later.excl.Δ R.later.err.bd.τ R.later.err.wk.b' R.later.err.wk.s'
            R.later.err.s R.later.scale.Λ R.later.split.b ∧
          (0 < R.later.circle.γ ∧ R.later.circle.γ < 1 / 100 ∧ R.β 2 ≤ R.later.circle.γ / 2 ∧
            R.β 2 ≤ 1 / 10 ^ 7) ∧
          (∀ j, stageNbAt_V4C R.stage j ≤ T.Nb R.stage ∧ stageCwAt_V4C R.stage j ≤ T.cw R.stage) ∧
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.excl.Δ *
            R.later.scale.Λ < 1 / 10 ^ 6) ∧
        ∃ εr δ'cone Λz : ℝ, ∃ δcone : ℝ, 0 < δcone ∧ δcone < δ'cone ∧ ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m),
            ∃ F : ClosedFamilyInstanceC14DV4 K R M δcone εr Λz,
              Tcp02RawBufferOutV4C F.family.toLocalChartPackets R.later.circle.δ ∧
              Tcp01GramQuadOutV4C F.family.toLocalChartPackets (3 * R.later.circle.γ) ∧
              (∀ p : M.X, 0 < closedVStarV4 T R.later.scale ∧
                closedVStarV4 T R.later.scale ≤ (ballVolume M.gX p (F.ρ p)).toReal / F.ρ p ^ 3) ∧
              tcp01SupportBound + 1 ≤ (earlyDataSharedV4 K).N ∧
              (∀ i : M.X,
                (tcp01CircleList F.family.toLocalChartFamily i).ncard +
                    (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
                    (tcp01SlimList F.family.toLocalChartFamily i).ncard ≤ tcp01SupportBound ∧
                  (zeroMeetingList F.family.zero i 10).ncard ≤ 1 ∧
                  (tcp01CircleList F.family.toLocalChartFamily i).ncard +
                      (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
                      (tcp01SlimList F.family.toLocalChartFamily i).ncard +
                      (zeroMeetingList F.family.zero i 10).ncard ≤ (earlyDataSharedV4 K).N) ∧
              (∀ j ∈ F.family.edge.centres,
                ∃ (Y : Type) (mY : MetricSpace Y) (q : Y) (C : ℝ) (hC : 0 ≤ C),
                  200 * R.later.excl.Δ < C ∧
                  ∃ (Fj : @KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
                      (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j
                      (WithLp.toLp 2 ((0 : ℝ), q)) R.later.split.b)
                    (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩
                      R.later.err.s),
                    Lfr32OutV4C hC F.ρ F.ρ_pos Fj Gj R.later.excl.Δ R.later.err.bd.τ
                      R.later.err.wk.b' R.later.err.wk.s' ∧
                    ∀ a : M.X, dist a j ≤ 101 * R.later.excl.Δ * F.ρ j →
                      dist (@KleinerLottApprox.toFun M.X (WithLp 2 (ℝ × Y))
                        (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j _
                        R.later.split.b Fj a).snd q < 2 * R.later.split.b →
                      @Lfr31OutV4C M.X (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) Y mY
                        j q C R.later.split.b R.later.err.s hC Fj Gj a (F.ρ a / F.ρ j)⁻¹
                        (inv_pos.mpr (div_pos (F.ρ_pos a) (F.ρ_pos j))) R.later.excl.Δ
                        R.later.err.wk.b' R.later.err.wk.s') ∧
              ∀ sel : Fin 3 → BlockSpace (fun _ : CGPTag F.family.toLocalChartFamily
                  F.family.zero => ℝ²) → M.X,
                (∀ st, ∀ x ∈ gafCloudEnlarged F.family.toLocalChartFamily F.family.zero st,
                  cgpProjMap F.family.toLocalChartFamily F.family.zero
                    (gafStageTags F.family.toLocalChartFamily F.family.zero st) (sel st x) = x) →
                ∃ C : Gaf02Chain F.family.toLocalChartPackets K
                    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
                    R.stage.e R.stage.c (stageCwAt_V4C R.stage),
                  C.sel = sel ∧ ∀ p : M.X,
                    MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.scale p ∧
                    |C.scale p - F.ρ p| ≤
                      closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ *
                        F.ρ p ∧
                    (∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) C.scale p v| ≤
                      closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ *
                        Real.sqrt (M.gX.inner p v v)) ∧
                    0 < C.scale p := by
  obtain ⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hC⟩ := earlyDataSharedV4_fields_VAL6 K
  obtain ⟨U', hU'U, hchain⟩ :=
    exists_chainStrategy_RGC K (closedStrategyCompleteV4C (earlyDataSharedV4 K))
  obtain ⟨T, hTU', hH, hlc, hfam⟩ :=
    exists_closed_realization_C14D_VAL6 K hK A hA Wseq gseq hf hg U'
  have hTU := hTU'.trans_RGC hU'U
  have hbU' : ClosedStrategyBelowV4 T U' := hTU'.below_VAL6
  have hb : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) :=
    hTU.below_VAL6
  obtain ⟨hraw, hlfr, hgram, hrows⟩ := hb.complete_caps_V4C
  have hsc : ClosedStrategyBelowV4 T (scaleStrategyV4 (earlyDataSharedV4 K)) :=
    hrows.trans_VAL6 ((ClosedThresholdsV4.inf_below_left_VAL6 _ _).trans_VAL6
      (ClosedThresholdsV4.inf_below_left_VAL6 _ _))
  have hv : PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T :=
    ⟨⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hlc, hTU.I₁_eq, fun m p => by
      rw [hH m]
      exact closed_standing_clauses_VAL K A Wseq gseq hg m p, fun _ => hfam.toC14_VAL6⟩,
      hC, closedScaleBudgetV4_of_below_VAL6 hsc,
      fun _ _ _ _ hεr hΛz _ _ F => closedRowOuts_of_below_VAL6 hC hrows F hεr hΛz⟩
  have hNb : T.Nb = maxNb_V4C := hTU.Nb_eq
  have hcw : T.cw = maxCw_V4C := hTU.cw_eq
  refine ⟨T, hv, hTU, hfam, hNb, hcw, fun R => ⟨?_, ?_⟩⟩
  · obtain ⟨-, hst, hCρ⟩ := R.scaleConstant_maxNb_V4C hNb hcw
    have hCeq := (R.scaleConstant_maxNb_V4C hNb hcw).1
    refine ⟨R.later.three_mul_βc_lt_β₂_VAL6, R.β₂_lt_γc_of_below_VAL6 hb,
      R.three_mul_β₂_lt_δ_of_below_V4C hraw, R.lfr29_numeric_of_below_V4C hlfr,
      R.gram_request_of_below_V4C hgram, hst, ?_⟩
    rw [hCeq]
    exact hCρ
  · obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
    obtain ⟨hεr0, -, hεrε₀, -, -, hΛz, δc, hδc0, hδc, ht⟩ := hF R
    refine ⟨εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
      R.later.split.β₁, δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁, ΛzF R.stage R.later.circle R.later.excl R.later.err
      R.later.scale R.later.split.b R.later.split.β₁, δc, hδc0, hδc, fun m hm => ?_⟩
    obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
    have hcount := F.wholeSupportCounts_CNTb hN hrows.below_partialRows_CNTb
    refine ⟨M, F, F.tcp02_raw_buffer_V4C hraw, (F.gram_V4C hgram).1,
      fun p => F.volume_exit_V4C hv.toPartialClosedThresholdValidityV4 p, hcount.1, hcount.2.1,
      fun j hj => F.edge_maps_V4C hlfr j hj, fun sel hsel => ?_⟩
    obtain ⟨C, hCsel⟩ := hchain T hbU' R F.family.toLocalChartPacketsC14 hεr0.le hεrε₀ hΛz sel hsel
    obtain ⟨-, hed⟩ := C.edp01_GAF8 (stageCwAt_nonneg_V4C R.stage 0) R.stage.sig_zero_le_RGC
    have hdom := R.stage.chain_scaleConstant_le_RGC hNb hcw
    have hΛ : 0 ≤ R.later.scale.Λ := R.later.Λ_pos.le
    refine ⟨C, hCsel, fun p => ?_⟩
    obtain ⟨hdiff, hval, hder, hpos⟩ := hed p
    have hρp := F.ρ_pos p
    refine ⟨hdiff, hval.trans ?_, fun v => (hder v).trans ?_, hpos⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdom hΛ) hρp.le
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdom hΛ) (Real.sqrt_nonneg _)


end DifferentialGeometry.Geometry.Collapse
