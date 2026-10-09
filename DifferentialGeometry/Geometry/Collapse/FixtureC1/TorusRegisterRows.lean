import DifferentialGeometry.Geometry.Collapse.FixtureC1.ChainCentreRecords
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowStrong
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf06Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroFacesStandard
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJARealization

/-!
# The counted rows on register V4's chain over the flat torus (O-FIXTURE-C1, G8 file 2)

For EVERY chain with (JA) on the register torus packet `torRegPackets_OFC R …` with register V4's
own chain data (such chains exist: `exists_torus_register_chainEJA_OFC`, G7), the counted rows run
with their hypotheses discharged by the register (no new hypothesis):

* `torRegChain_records_OFC`: the D75-6 records at the origin centre `j₀`
  (`Gaf02ChainEJA.circle_centre_records_OFC`: plateau, `U_{j₀}⁵`, cloud, active slot, native output,
  `g₁`, final map `E`, FC30 cutoff, BASES object and circle patch, all at the ACTUAL centre);
* `torRegChain_gaf07_circle_OFC`: GAF07's circle row and the circle clauses of the STRONG row
  (D1 base piece / chart map as a proper surjective submersion / local trivializations) at `j₀`
  (no orientation needed), GAF07's circle bundle, GAF06's row;
* `torRegChain_gaf07_strong_OFC`: the whole STRONG row `gaf07_row_strong_GAFD` for every
  orientation parameter (its slim part is about the empty slim family of C1);
* `torRegChain_edp01_OFC`: EDP01's (SD) on the chain (`ρ ≡ 1`);
* `torRegChain_zsp02_strong_OFC`: ZSP02's strong row on the closed family `torRegPacketsZ_OFC`
  (every clause quantifies over zero centres; on C1 the zero family is EMPTY, recorded alongside —
  C1 gives the circle stage only, D75-4).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **The row numbers at the register**: GAF07's `β₂ ≤ 10⁻⁷` and `γ + β₂ < 1/10`. -/
theorem ClosedRegisterV4.torus_row_numbers_OFC {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D)) :
    R.β 2 ≤ 1 / 10000000 ∧ R.later.circle.γ + R.β 2 < 1 / 10 := by
  obtain ⟨-, hγ1, hβγ, hβ2⟩ := R.gram_request_of_below_V4C hT.complete_caps_V4C.2.2.1
  refine ⟨by norm_num at hβ2 ⊢; exact hβ2, by linarith⟩

section Rows

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  (R : ClosedRegisterV4 (earlyDataSharedV4 K) T)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) {Kf : ℕ} {δ εr Λz : ℝ}
  (C : Gaf02ChainEJA (torRegPackets_OFC R hT hlc Kf δ εr Λz) K
    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig R.stage.e R.stage.c
    (stageCwAt_V4C R.stage) (registerCadj_RGC K))

/-- **D75-6 records of the register chain over the torus at the origin centre `j₀`.** -/
theorem torRegChain_records_OFC :
    type_of% (C.circle_centre_records_OFC (R.stage.Sig_pos 0)
      (torRegPackets_origin_mem_OFC R hT hlc) (torRegPackets_origin_coord_OFC R hT hlc)) :=
  C.circle_centre_records_OFC (R.stage.Sig_pos 0) (torRegPackets_origin_mem_OFC R hT hlc)
    (torRegPackets_origin_coord_OFC R hT hlc)

/-- **GAF07's circle row, the circle clauses of the STRONG row at `j₀`, the circle bundle, and
GAF06's row** on the register chain over the torus (no orientation involved). -/
theorem torRegChain_gaf07_circle_OFC :
    type_of% (C.gaf07_circle_row_GAFD (R.torus_row_numbers_OFC hT).1
      (R.torus_row_numbers_OFC hT).2) ∧
    type_of% (C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt (R.torus_row_numbers_OFC hT).1
      (R.torus_row_numbers_OFC hT).2
      ⟨torRegOrigin_OFC R, (Set.Finite.mem_toFinset _).mpr
        (torRegPackets_origin_mem_OFC R hT hlc)⟩) ∧
    type_of% (C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt (R.torus_row_numbers_OFC hT).1
      (R.torus_row_numbers_OFC hT).2
      ⟨torRegOrigin_OFC R, (Set.Finite.mem_toFinset _).mpr
        (torRegPackets_origin_mem_OFC R hT hlc)⟩) ∧
    type_of% (C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt
      (R.torus_row_numbers_OFC hT).1 (R.torus_row_numbers_OFC hT).2
      ⟨torRegOrigin_OFC R, (Set.Finite.mem_toFinset _).mpr
        (torRegPackets_origin_mem_OFC R hT hlc)⟩) ∧
    type_of% (C.gaf07_circle_bundle_GAFC (R.torus_row_numbers_OFC hT).1
      (R.torus_row_numbers_OFC hT).2) ∧
    type_of% C.gaf06_row_GAFD := by
  have h := R.torus_row_numbers_OFC hT
  have hj := (Set.Finite.mem_toFinset (torRegPackets_OFC R hT hlc Kf δ εr Λz).circle.finite_centres
    (a := torRegOrigin_OFC R)).mpr (torRegPackets_origin_mem_OFC R hT hlc)
  exact ⟨C.gaf07_circle_row_GAFD h.1 h.2,
    C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt h.1 h.2 ⟨_, hj⟩,
    C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt h.1 h.2 ⟨_, hj⟩,
    C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt h.1 h.2 ⟨_, hj⟩,
    C.gaf07_circle_bundle_GAFC h.1 h.2, C.gaf06_row_GAFD⟩

/-- **GAF07, the whole STRONG row** on the register chain over the torus (`K_f ≥ 5`), for every
orientation parameter. -/
theorem torRegChain_gaf07_strong_OFC (hK : 5 ≤ Kf)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (torRegTorus_OFC R) 3) :
    type_of% (C.gaf07_row_strong_GAFD (R.torus_row_numbers_OFC hT).1
      (R.torus_row_numbers_OFC hT).2 hK oM) :=
  C.gaf07_row_strong_GAFD (R.torus_row_numbers_OFC hT).1 (R.torus_row_numbers_OFC hT).2 hK oM

/-- **EDP01's (SD)** on the register chain over the torus (`ρ ≡ 1`). -/
theorem torRegChain_edp01_OFC : type_of% C.toGaf02ChainE.edp01_GAFC :=
  C.toGaf02ChainE.edp01_GAFC

/-- **ZSP02, the STRONG row** on the closed family of the register torus, for every orientation
parameter; the zero family of C1 is empty (every clause of the row quantifies over its centres). -/
theorem torRegChain_zsp02_strong_OFC (hεr : εr < 1 / 2)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (torRegTorus_OFC R) 3) :
    (torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM).zero.centres = ∅ ∧
    type_of% (Gaf02ChainE.zsp02_row_strong_ZSP35
      (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM) C.toGaf02ChainE hεr) :=
  ⟨rfl, Gaf02ChainE.zsp02_row_strong_ZSP35 (P := torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM)
    C.toGaf02ChainE hεr⟩

end Rows

end DifferentialGeometry.Geometry.Collapse
