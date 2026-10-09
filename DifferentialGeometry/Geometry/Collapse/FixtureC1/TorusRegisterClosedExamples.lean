import DifferentialGeometry.Geometry.Collapse.FixtureC1.ChainCirclePatch
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusOrientation
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterRowsExamples
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusPacketsExamples

/-!
# Consumers of G9: the CLOSED C1 packets and the rows at the actual orientation
# (O-FIXTURE-C1, G9 file 3)

* `torC1_packets_closed_OFC`, `torRegPacketsZ_closed_OFC`: the closed families
  `LocalChartPacketsC14Z` of S-FIXTURE-C1b's C1 example torus and of the register torus at the
  orientation `torOrientation_OFC` (no orientation parameter left).
* `torC1_register_closed_OFC K`: a strategy below the combined one, a register at it, register V4's
  chain with (JA) on the register torus packet based at the origin centre `j₀`, its D75-6 records,
  the NON-EMPTY circle patch of `j₀` with its centre, and GAF07's whole strong row and ZSP02's
  strong row at the ACTUAL orientation of the torus.
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

/-- **The closed C1 example packet** (S-FIXTURE-C1b's `torC1_packets_FXC1`) at the orientation of
the torus. -/
def torC1_packets_closed_OFC :
    LocalChartPacketsC14Z (Tor_FXC1 torPeriodsC1_FXC1) (torMetric_FXC1 torPeriodsC1_FXC1)
      (torMS_hmetric_FXC1 torPeriodsC1_FXC1) (fun _ => (1 : ℝ)) (fun _ => one_pos) 0
      torBetaC1_FXC1 1 0 0 0 0 (1 / 1000) (1 / 1000) 0 0 0 0 0 0 0 (1 / 10) 0 0 0 0 0 0 0 0
      (torOrientation_OFC torPeriodsC1_FXC1) :=
  torC1_packets_FXC1 (torOrientation_OFC torPeriodsC1_FXC1)

/-- **The closed register packet** at the orientation of the torus. -/
def torRegPacketsZ_closed_OFC {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
    (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) (Kf : ℕ) (δ εr Λz : ℝ) :=
  torRegPacketsZ_OFC R hT hlc Kf δ εr Λz
    (torOrientation_OFC (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))

/-- **Consumer: register chain over the torus, records, non-empty circle patch, and the
orientation-dependent strong rows at the actual orientation** (see the module header). -/
theorem torC1_register_closed_OFC (K : ℕ) :
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
            type_of% (torRegChain_patch_OFC R hT hlc C) ∧
            type_of% (torRegChain_gaf07_strong_OFC R hT hlc C le_rfl
              (torOrientation_OFC (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))) ∧
            type_of% (torRegChain_zsp02_strong_OFC R hT hlc C (by norm_num)
              (torOrientation_OFC (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))) := by
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
  exact ⟨C, hC, torRegChain_records_OFC R hT hlc C, torRegChain_patch_OFC R hT hlc C,
    torRegChain_gaf07_strong_OFC R hT hlc C le_rfl
      (torOrientation_OFC (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos)),
    torRegChain_zsp02_strong_OFC R hT hlc C (by norm_num)
      (torOrientation_OFC (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))⟩

end DifferentialGeometry.Geometry.Collapse
