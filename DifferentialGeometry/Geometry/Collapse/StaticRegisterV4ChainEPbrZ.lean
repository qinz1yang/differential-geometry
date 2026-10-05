import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsEZ
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples

/-!
# PBR02, PBR03 and FC44's closed binding on the ENHANCED chain with (JA), on the FINAL family C14Z

Lane C14-REG-CHAIN, G9 (re-base of G8 on `LocalChartPacketsC14Z`, review 71 D71-3: the rows' source
`ClosedChainEZRowsSource_RGC` keeps the realization's `P_Z`). G8 was: the successors of G3
    (`pbr02_static_RGC`, `pbr03_reduction_RGC`) and
G4 (`fc44_closed_binding_RGC`) on the chain object of review 66 D66-2, built on the register's own
stage data (`exists_chainEStrategy_RGC`, G6): the static data of PBR02 (B:10257–10275) on the tail
of a closed standing sequence is ONE register choice and, on every member, ONE instance of the
final family together with the rows' source `ClosedChainEZRowsSource_RGC` (enhanced planes, native
outputs on the planes' slots, rough data, (JA)) for every base point.

* `pbr02_staticEZ_RGC`: PBR02's STATIC-DATA part on the enhanced chain (same carrier:
  `M.gX = ψ^*g_m`);
* `pbr03_reductionEZ_RGC`: PBR03's reduction (B:10277–10333 up to its last line) with that static
  data on the counterexample tail;
* `fc44_closed_bindingEZ_RGC`: FC44's closed half (B:9998–10024) with the enhanced chain: at every
  register, GAF01's CHOICE in the chain's form AND its evidence (`ClosedStage.choice_RGC`) at the
  stage values, (JA) and every downstream bound on `c₃` (`ClosedStage.c_two_bounds_RGC`), PR10's
  `C_ρ` dominating EDP01's chain constant, `C_ρΔΛ < 10⁻⁶`, EDP-E's numerics
  (`ClosedRegisterV4.edpE_numerics_RGC`), and every consumer reading the SAME assignment.

NOT claimed (as in G3): PBR02's certificate part (FC39 decomposition / KL graph presentation from
the static data: GAF02 BASES on the chain, FC39's certificate producer, FC42).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **PBR02, static-data part, on the enhanced chain** (see the module header). -/
theorem pbr02_staticEZ_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m),
          M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧ Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ := by
  obtain ⟨T, hTU, hv, hNb, hcw, hR⟩ :=
    exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, hNb, hcw, exists_closedRegisterV4 _ T, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := ht m hm
  exact ⟨M, M.metric_eq, hne, hS⟩

/-- **PBR03's reduction on the enhanced chain** (B:10293–10333, up to the last line): for every
certificate `Good`, either the closed finite-scale threshold exists, or there is a closed standing
sequence of counterexamples without `Good` on whose tail register V4 yields ONE assignment and, on
every member, the rows' source on the enhanced chain with (JA) for every base point. -/
theorem pbr03_reductionEZ_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x)
    (Good : CompactCarrier.{u} → Prop) :
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ → Good W) ∨
    ∃ (Wseq : ℕ → CompactCarrier.{u})
      (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier),
      (∀ m, ClosedMemberFacts (Wseq m) ∧ (∀ p, curvatureRadius (gseq m) p ≠ ⊤) ∧
        closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)) ∧
        ¬ Good (Wseq m)) ∧
      ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
        ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
        PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
        Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
        ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
            ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ := by
  by_cases h : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ → Good W
  · exact Or.inl h
  right
  obtain ⟨W, hW, g, hseq⟩ := exists_closed_standing_sequence_of_no_threshold K A Good h
  have hf : ∀ m, ClosedMemberFacts (W m) := fun m => ⟨(hseq m).2.1.1, hW m⟩
  obtain ⟨T, hTU, hv, -, -, hreg, hR⟩ :=
    pbr02_staticEZ_RGC K hK A hA W g hf (fun m => (hseq m).2.1)
  refine ⟨W, g, fun m => ⟨hf m, (hseq m).1, (hseq m).2.1, (hseq m).2.2.1⟩, T, hTU, hv, hreg,
    fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, -, hne, hS⟩ := ht m hm
  exact ⟨M, hne, hS⟩

/-- **FC44's closed binding on the enhanced chain** (see the module header). -/
theorem fc44_closed_bindingEZ_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        (∀ j, R.stage.Sig j < (earlyDataSharedV4 K).Ξ j (R.stage.Γ j) / 10000 ∧
          0 ≤ stageCwAt_V4C R.stage j) ∧
        R.stage.c 2 < registerCadj_RGC K ∧ R.stage.c 2 < 1 / 1000 ∧ R.stage.c 2 < 1 / 100000 ∧
        (1 + 2 * cgpProfileBound) * (5 / 4 * R.stage.c 2) < 1 / 1000 ∧
        100 * (gafDerivativeBound + 1) *
            (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage ∧
        (∀ j, 2 * stageCwAt_V4C R.stage j / R.stage.Sig j ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage / 100) ∧
        closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.excl.Δ *
          R.later.scale.Λ < 1 / 10 ^ 6 ∧
        R.later.err.co.ε < 1 ∧ R.later.circle.γc < 1 / 100 ∧ R.later.circle.βc < 1 / 100000 ∧
        ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
            ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ := by
  obtain ⟨T, hTU, hv, hNb, hcw, hreg, hR⟩ := pbr02_staticEZ_RGC K hK A hA Wseq gseq hf hg
  have hb := hTU.below_VAL6
  refine ⟨T, hTU, hv, hreg, fun R => ?_⟩
  obtain ⟨-, -, -, hsig, hcwn⟩ := R.stage.choice_RGC
  obtain ⟨hc1, hc2, hc3, hc4⟩ := R.stage.c_two_bounds_RGC
  obtain ⟨-, hγc, hβc⟩ := R.collar_le_RGC hb
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨fun j => ⟨hsig j, hcwn j⟩, hc1, hc2, hc3, hc4,
    R.stage.chain_scaleConstant_le_RGC hNb hcw, R.stage.smv_le_scaleConstant_RGC hNb hcw,
    R.later.regScale_Cρ, (R.eps_lt_RGC hb).2, hγc, hβc, εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, -, hne, hS⟩ := ht m hm
  exact ⟨M, hne, hS⟩

end DifferentialGeometry.Geometry.Collapse
