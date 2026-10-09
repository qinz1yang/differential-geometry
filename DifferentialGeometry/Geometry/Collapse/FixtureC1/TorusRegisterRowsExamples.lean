import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterRows

/-!
# Consumer of G8: the counted rows run on an EXISTING register chain over the flat torus
# (O-FIXTURE-C1, G8 file 3)

`torC1_register_rows_OFC K`: a strategy below the combined one, a register at it, and register
V4's chain with (JA) on the torus packet of that register (`K_f = 5`, `δ = γ`, `ε_r = 0`,
`Λ_z = T₀Low / 20`) based at the origin centre `j₀`, on which the D75-6 records at `j₀`, GAF07's
circle row with the strong circle clauses at `j₀`, GAF07's circle bundle, GAF06, EDP01, and, for
every orientation parameter, GAF07's whole strong row and ZSP02's strong row all hold.
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

/-- **Consumer: the counted rows on an existing register chain over the torus** (see the module
header). -/
theorem torC1_register_rows_OFC (K : ℕ) :
    ∃ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
      (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0})
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T),
        ∃ C : Gaf02ChainEJA (torRegPackets_OFC R hT hlc 5 R.later.circle.γ 0
              (T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
                R.later.split.b R.later.split.β₁ / 20))
              K (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
              R.stage.e R.stage.c (stageCwAt_V4C R.stage) (registerCadj_RGC K),
            C.x₀ = torRegOrigin_OFC R ∧
            type_of% (torRegChain_records_OFC R hT hlc C) ∧
            type_of% (torRegChain_gaf07_circle_OFC R hT hlc C) ∧
            type_of% (torRegChain_edp01_OFC R hT hlc C) ∧
            ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (torRegTorus_OFC R) 3,
              type_of% (torRegChain_gaf07_strong_OFC R hT hlc C le_rfl oM) ∧
              type_of% (torRegChain_zsp02_strong_OFC R hT hlc C (by norm_num) oM) := by
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
  obtain ⟨C, hC, -⟩ := hR
  exact ⟨C, hC, torRegChain_records_OFC R hT hlc C, torRegChain_gaf07_circle_OFC R hT hlc C,
    torRegChain_edp01_OFC R hT hlc C, fun oM =>
      ⟨torRegChain_gaf07_strong_OFC R hT hlc C le_rfl oM,
        torRegChain_zsp02_strong_OFC R hT hlc C (by norm_num) oM⟩⟩

end DifferentialGeometry.Geometry.Collapse
