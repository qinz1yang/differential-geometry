import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterPacket

/-!
# Register V4's enhanced chain with (JA) on the flat torus: the first NON-EMPTY circle stage
# (O-FIXTURE-C1, G7 file 2)

Review 71 D71-7 / review 75 D75-1 (ii): every stage theorem of the chapter was so far instantiated
only on empty families. Here register V4's chain producer — the layer of
`register_yields_chainEJAZ_RGC` (C14-REG-CHAIN G9) that builds the chain,
`exists_chainEStrategy_RGC` at the combined strategy `closedStrategyCompleteV4C`, which quantifies
over EVERY `LocalChartPacketsC14` at a register's values — is applied to the explicit flat torus
packet `torRegPacketsZ_OFC` at the register's own numbers (one legal register, D75-10):

`exists_torus_register_chainEJA_OFC K`: there are a strategy `T` below the combined strategy (with
LC18's slot capped by the rank-exclusion threshold, so `β₃ < 1/10`) such that at EVERY register `R`
at `T`, for every `K_f, δ, ε_r ∈ [0, ε₀), Λ_z` with `20 Λ_z ≤ T₀Low` and every base point `x₀`,
there is
`Ĉ : Gaf02ChainEJA P K (Ξ_j(Γ_j)) Γ Σ e c (stageCwAt_V4C R.stage) (registerCadj_RGC K)` on the
torus packet `P = torRegPackets_OFC R …` (no orientation involved) with `Ĉ.x₀ = x₀`, the origin
`j₀` a circle centre with `η_{j₀}(j₀) = 0`, `j₀` in the first stage core, the stage-0 cloud
non-empty and the stage-0 slot of `Ĉ` ACTIVE (D75-6 records: the centre, the point, the cloud).

Registers exist at `T` (`exists_closedRegisterV4`): the consumer `torC1_register_chain_OFC`
(`TorusRegisterChainExamples`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **Register V4's enhanced chain with (JA) on the flat torus packet, with an ACTIVE first stage**
(see the module header). -/
theorem exists_torus_register_chainEJA_OFC (K : ℕ) :
    ∃ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
      (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}),
      ∀ (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (Kf : ℕ) (δ εr Λz : ℝ),
        0 ≤ εr → εr < R.later.err.co.ε₀ →
        20 * Λz ≤ T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
          R.later.split.b R.later.split.β₁ →
        ∀ x₀ : torRegTorus_OFC R,
          ∃ C : Gaf02ChainEJA (torRegPackets_OFC R hT hlc Kf δ εr Λz)
              K (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
              R.stage.e R.stage.c (stageCwAt_V4C R.stage) (registerCadj_RGC K),
            C.x₀ = x₀ ∧
            torRegOrigin_OFC R ∈ (torRegPackets_OFC R hT hlc Kf δ εr Λz).circle.centres ∧
            torRegOrigin_OFC R ∈ gafStageCore
              (torRegPackets_OFC R hT hlc Kf δ εr Λz).toLocalChartFamily
              (torRegPackets_OFC R hT hlc Kf δ εr Λz).zero 0 ∧
            (gafCloud (torRegPackets_OFC R hT hlc Kf δ εr Λz).toLocalChartFamily
              (torRegPackets_OFC R hT hlc Kf δ εr Λz).zero 0).Nonempty ∧
            ∃ O, C.toChain.slot 0 = Gaf02StageSlot.active O := by
  -- (`obtain` on the whole conjunction times out at `isDefEq`; destructure in two steps)
  have h := exists_chainEStrategy_RGC K (closedStrategyCompleteV4C (earlyDataSharedV4 K))
  obtain ⟨U', h2⟩ := h
  have hb := U'.withTorusCap_below_OFC
  have hbU := hb.trans_VAL6 h2.1.below_VAL6
  refine ⟨U'.withTorusCap_OFC, hbU, U'.withTorusCap_lc18_OFC, ?_⟩
  intro R Kf δ εr Λz hεr hεr' hΛz x₀
  have hC := h2.2 _ hb R (torRegPackets_OFC R hbU U'.withTorusCap_lc18_OFC Kf δ εr Λz)
    hεr hεr' hΛz x₀
  obtain ⟨C, hCx⟩ := hC
  have hj := torRegPackets_origin_mem_OFC R hbU U'.withTorusCap_lc18_OFC (Kf := Kf) (δ := δ)
    (εr := εr) (Λz := Λz)
  have hcore := gafCloud_zero_nonempty_FXC1
    (torRegPackets_OFC R hbU U'.withTorusCap_lc18_OFC Kf δ εr Λz).toLocalChartFamily
    (torRegPackets_OFC R hbU U'.withTorusCap_lc18_OFC Kf δ εr Λz).zero hj (by
      rw [torRegPackets_origin_coord_OFC, norm_zero]
      norm_num)
  have hO := slot_zero_active_FXC1 C.toChain hj
  exact ⟨C, hCx, hj, hcore.1, hcore.2, hO⟩

end DifferentialGeometry.Geometry.Collapse
