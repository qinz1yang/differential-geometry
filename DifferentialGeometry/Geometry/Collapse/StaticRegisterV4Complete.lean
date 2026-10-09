import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4RawDelta
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Endpoint
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Gram
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4VolumeExit
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4WholeSupportCountInstance

/-!
# Register V4: ONE strategy carrying every native exit of lane FC39-V4C(b) on ONE strong C14D
realization (review 57, §7.1–§7.3; dispositions items 3, 4, 6, 7)

`closedStrategyCompleteV4C D` = the rows strategy with PR10's maxima `N_b, c_w` (G3), with the
pre-`β_c` `β₂` caps of TCP02's raw buffer (`β₂ < δ_raw/3`, G2), TCP01's Gram request
(`β₂ ≤ min (γ/2) 10⁻⁷`, `γ < 1/100`, G6), TCP04's `β₂ < γ_c/1000` (lane FC39-VAL6), and the LFR29.1
cap (`lfr29W ≤ W(Δ, τ)`, `splitUp ≤ s/10⁵`, G4). All `β₂` requests sit in `β₂Up` (read at the circle
prefix and `β₃`), so the merge order of G1 holds for it.

`exists_closed_complete_V4C` (the final consumer): at the early data `earlyDataSharedV4 K`, on every
closed standing sequence, ONE strategy `T` refining it with
* the record `PartialClosedThresholdValidityV4Rows` (the same realization's family projected),
* the STRONG package `ClosedFamilyAtC14DV4` (final family with LFR44 item 2, one LPA02 witness),
* `T.Nb = maxNb_V4C`, `T.cw = maxCw_V4C` (ONE cloud-cover `N_b`, G3),
and at EVERY register: `3β_c < β₂`, `β₂ < γ_c/1000`, `3β₂ < δ_raw`, LFR29.1, the Gram request,
`C_ρ ΔΛ < 10⁻⁶` with `C_ρ` from that `N_b` dominating every stage; and ONE cone error
`δ_cone < δ'_cone` with, on every member of the tail, ONE instance `F` of the final family carrying
TCP02's raw buffer at `δ_raw` (G2), TCP01's Gram form at `3γ` (G6), the volume exit
`v_* ≤ vol B(p, ρ(p))/ρ(p)³` (G7), TCP01's whole support-list counts `≤ N` (lane C14-COUNTb's
`ClosedFamilyInstanceC14DV4.wholeSupportCounts_CNTb`, called, not re-proved; `N` is the early whole
count, distinct from the cloud-cover `N_b`), and at every edge centre ONE pair of actual strong
maps carrying LFR32's output (G4) and LFR31's explicit recentering (G5).

The name of the record stays `Partial…` (review 57 §7: `RowsAt`, the Δ-stage short-buffer radii and
the boundary validity are not part of this lane).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The combined strategy**: PR10's maxima, then the raw, LFR29.1, Gram and TCP04 caps. -/
def closedStrategyCompleteV4C (D : ClosedEarlyData) : ClosedThresholdsV4 D :=
  ((((rowsStrategyNbMaxV4C D).withRawβ₂_V4C).withLfr29_V4C).withGram_V4C).withCollarβ₂_VAL6

/-- A strategy below the combined one is below each cap in the form its lemmas read, and below the
11-row strategy. -/
theorem ClosedStrategyBelowV4.complete_caps_V4C {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (h : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D)) :
    ClosedStrategyBelowV4 T ((rowsStrategyNbMaxV4C D).withRawβ₂_V4C) ∧
      ClosedStrategyBelowV4 T (((rowsStrategyNbMaxV4C D).withRawβ₂_V4C).withLfr29_V4C) ∧
      ClosedStrategyBelowV4 T
        ((((rowsStrategyNbMaxV4C D).withRawβ₂_V4C).withLfr29_V4C).withGram_V4C) ∧
      ClosedStrategyBelowV4 T (rowsStrategyV4 D) := by
  have h3 := h.trans_VAL6 (ClosedThresholdsV4.withCollarβ₂_below_VAL6 _)
  have h2 := h3.trans_VAL6 (ClosedThresholdsV4.withGram_below_V4C _)
  have h1 := h2.trans_VAL6 (ClosedThresholdsV4.withLfr29_below_V4C _)
  exact ⟨h1, h2, h3, (h1.trans_VAL6 (ClosedThresholdsV4.withRawβ₂_below_V4C _)).trans_VAL6
    (rowsStrategyNbMaxV4C_below_V4C D)⟩

/-- `Δ ≥ 1` at every register. -/
theorem ClosedRegisterV4.one_le_Δ_V4C {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) : 1 ≤ R.later.excl.Δ := by
  have h1 := R.later.Δ_gt
  have h2 := le_max_left (10 ^ 6 : ℝ)
    (max (100 / R.later.excl.β₂) (T.ΔLow R.stage R.later.circle R.later.excl.β₃ R.later.excl.β₂))
  have h3 : (1 : ℝ) ≤ 10 ^ 6 := by norm_num
  linarith

/-- **ONE pair of actual strong maps at an edge centre carrying LFR32 and LFR31 together**: at a
register below the LFR29.1 cap, every edge centre of every C14D instance has actual strong maps
(`edge.strong j`, `C > 200Δ`) satisfying LFR32's output and, at every `a` with
`d(a, j) ≤ 101Δρ(j)`, `d(v(a), y₀) < 2b`, LFR31's explicit own-scale recentering. -/
theorem ClosedFamilyInstanceC14DV4.edge_maps_V4C {K : ℕ} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withLfr29_V4C)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz) (j : M.X) (hj : j ∈ F.family.edge.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y) (q : Y) (C : ℝ) (hC : 0 ≤ C),
      200 * R.later.excl.Δ < C ∧
      ∃ (Fj : @KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
          (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j (WithLp.toLp 2 ((0 : ℝ), q))
          R.later.split.b)
        (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩ R.later.err.s),
        Lfr32OutV4C hC F.ρ F.ρ_pos Fj Gj R.later.excl.Δ R.later.err.bd.τ R.later.err.wk.b'
          R.later.err.wk.s' ∧
        ∀ a : M.X, dist a j ≤ 101 * R.later.excl.Δ * F.ρ j →
          dist (@KleinerLottApprox.toFun M.X (WithLp 2 (ℝ × Y))
            (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j _ R.later.split.b Fj a).snd q <
              2 * R.later.split.b →
          @Lfr31OutV4C M.X (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) Y mY j q C
            R.later.split.b R.later.err.s hC Fj Gj a (F.ρ a / F.ρ j)⁻¹
            (inv_pos.mpr (div_pos (F.ρ_pos a) (F.ρ_pos j))) R.later.excl.Δ R.later.err.wk.b'
            R.later.err.wk.s' := by
  obtain ⟨Y, mY, q, C, hC, hCl, ⟨Fj⟩, ⟨Gj⟩⟩ := F.family.edge.strong j hj
  exact ⟨Y, mY, q, C, hC, hCl, Fj, Gj,
    R.lfr32_of_below_V4C h F.family.lipschitz_scale F.ρ_pos Fj Gj hCl.le, fun a ha hqa =>
    (@lfr31Out_physical_V4C M.X M.mX Y mY j a q _ _ _ _ _ _ _ _ F.ρ (R.lfr29_numeric_of_below_V4C h)
      F.family.lipschitz_scale F.ρ_pos R.one_le_Δ_V4C hC Fj Gj hCl.le ha hqa).1⟩

/-- **The final consumer of lane FC39-V4C(b)** (see the module header): ONE strategy, the record,
the strong C14D package, ONE `N_b`, every register-level request and, on every member of every
register's tail, ONE instance of the final family carrying every native exit of this lane and
lane C14-COUNTb's whole support-list counts. -/
theorem exists_closed_complete_V4C (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
              ∀ j ∈ F.family.edge.centres,
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
                        R.later.err.wk.b' R.later.err.wk.s' := by
  obtain ⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hC⟩ := earlyDataSharedV4_fields_VAL6 K
  obtain ⟨T, hTU, hH, hlc, hfam⟩ := exists_closed_realization_C14D_VAL6 K hK A hA Wseq gseq hf hg
    (closedStrategyCompleteV4C (earlyDataSharedV4 K))
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
    obtain ⟨-, -, -, -, -, -, δc, hδc0, hδc, ht⟩ := hF R
    refine ⟨εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
      R.later.split.β₁, δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁, ΛzF R.stage R.later.circle R.later.excl R.later.err
      R.later.scale R.later.split.b R.later.split.β₁, δc, hδc0, hδc, fun m hm => ?_⟩
    obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
    have hcount := F.wholeSupportCounts_CNTb hN hrows.below_partialRows_CNTb
    exact ⟨M, F, F.tcp02_raw_buffer_V4C hraw, (F.gram_V4C hgram).1,
      fun p => F.volume_exit_V4C hv.toPartialClosedThresholdValidityV4 p, hcount.1, hcount.2.1,
      fun j hj => F.edge_maps_V4C hlfr j hj⟩

end DifferentialGeometry.Geometry.Collapse
