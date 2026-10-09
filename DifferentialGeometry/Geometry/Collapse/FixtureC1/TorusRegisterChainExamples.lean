import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterChain

/-!
# Consumer of G7: the register chain on the flat torus exists (O-FIXTURE-C1, G7 file 3)

`torC1_register_chain_OFC K`: a strategy below the combined one, a register at it (they exist:
`exists_closedRegisterV4`) and register V4's enhanced chain with (JA) on the flat torus packet of
that register based at the origin centre, with an ACTIVE stage-0 slot.
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

/-- **Consumer, non-empty form**: a register exists at the strategy, so the chain of
`exists_torus_register_chainEJA_OFC` exists (`K_f = 5`, `δ = γ`, `ε_r = 0`, `Λ_z = T₀Low / 20`). -/
theorem torC1_register_chain_OFC (K : ℕ) :
    ∃ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
      (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0})
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T),
        ∃ C : Gaf02ChainEJA (torRegPackets_OFC R hT hlc 5 R.later.circle.γ 0
              (T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
                R.later.split.b R.later.split.β₁ / 20))
              K (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
              R.stage.e R.stage.c (stageCwAt_V4C R.stage) (registerCadj_RGC K),
            C.x₀ = torRegOrigin_OFC R ∧ ∃ O, C.toChain.slot 0 = Gaf02StageSlot.active O := by
  have h0 := exists_torus_register_chainEJA_OFC K
  obtain ⟨T, h1⟩ := h0
  obtain ⟨hT, h2⟩ := h1
  obtain ⟨hlc, h⟩ := h2
  -- (`obtain ⟨R⟩` on the `Nonempty` times out at `whnf`; use `Classical.choice`)
  have R : ClosedRegisterV4 (earlyDataSharedV4 K) T :=
    Classical.choice (exists_closedRegisterV4 (earlyDataSharedV4 K) T)
  refine ⟨T, hT, hlc, R, ?_⟩
  have hΛz : 20 * (T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁ / 20) ≤ T.T₀Low R.stage R.later.circle R.later.excl
      R.later.err R.later.scale R.later.split.b R.later.split.β₁ := le_of_eq (by ring)
  have hR := h R 5 R.later.circle.γ 0 _ le_rfl R.later.ε₀_pos hΛz (torRegOrigin_OFC R)
  obtain ⟨C, hC, hrest⟩ := hR
  exact ⟨C, hC, hrest.2.2.2⟩

end DifferentialGeometry.Geometry.Collapse
