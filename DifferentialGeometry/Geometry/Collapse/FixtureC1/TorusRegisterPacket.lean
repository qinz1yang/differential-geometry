import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusStageSlot
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEZComplete

/-!
# The flat torus packet at a register V4 (O-FIXTURE-C1, G7 file 1)

* `ClosedThresholdsV4.withTorusCap_OFC U`: `U` with LC18's slot capped by the rank-exclusion
  threshold (`threeSplittingExclusionThreshold < 1/10`, review 75 D75-9 addendum: the fixture takes
  `β₃` from the register cap); below `U`.
* `ClosedRegisterV4.torus_numbers_OFC`: at every register of a strategy below the combined strategy
  `closedStrategyCompleteV4C` with that cap, `0 < β₂ ≤ 10⁻⁷`, `β₃ ≤ 3/20`, `0 < γ`, `b ≤ 1/6`,
  `s ≤ 1/7`, `b + s ≤ 1/100` — every numeric hypothesis of the flat torus packet.
* `torRegPeriods_OFC β₂`: the periods `(N, N, β₂)`, `N = ⌈8/β₂⌉₊` (scale `R = 1`: `L₂ ≤ R β₂`,
  `8R/β₂ ≤ N R`).
* `torRegPackets_OFC R hT hlc Kf δ εr Λz : LocalChartPacketsC14 …` at EXACTLY the register's
  values (the parameter list of `exists_chainEStrategy_RGC`), with the origin node a circle centre
  (`torRegPackets_origin_mem_OFC`) of vanishing coordinate; its closed extension
  `torRegPacketsZ_OFC … oM : LocalChartPacketsC14Z …` (`oM` a parameter, zero family empty).
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

/-! ### The torus cap of a strategy -/

/-- LC18's slot capped by the rank-exclusion threshold (`< 1/10`). -/
def ClosedThresholdsV4.withTorusCap_OFC {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedThresholdsV4 D :=
  { U with
    lc18 := min U.lc18 threeSplittingExclusionThreshold.{0, 0}
    lc18_pos := lt_min U.lc18_pos threeSplittingExclusionThreshold_pos }

/-- The torus cap only lowers LC18's slot. -/
theorem ClosedThresholdsV4.withTorusCap_below_OFC {D : ClosedEarlyData}
    (U : ClosedThresholdsV4 D) : ClosedStrategyBelowV4 U.withTorusCap_OFC U where
  lc18_le := min_le_left _ _
  circleUp_le := fun _ _ _ _ _ => le_rfl
  β₂Up_le := fun _ _ _ => le_rfl
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => le_rfl
  sectionUp_le := fun _ _ _ _ => le_rfl
  lfr29W_le := fun _ _ _ _ _ => le_rfl
  endpointUp_le := fun _ _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => le_rfl
  splitUp_le := fun _ _ _ _ _ => le_rfl
  β₁Up_le := fun _ _ _ _ _ _ => le_rfl
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_rfl
  LmaxLow_ge := fun _ _ _ _ _ _ => le_rfl
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

theorem ClosedThresholdsV4.withTorusCap_lc18_OFC {D : ClosedEarlyData}
    (U : ClosedThresholdsV4 D) :
    U.withTorusCap_OFC.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} :=
  min_le_right _ _

/-! ### The numbers of the torus packet at a register -/

/-- **Every numeric hypothesis of the flat torus packet holds at the register** (below the
combined strategy, LC18 capped by the rank-exclusion threshold). -/
theorem ClosedRegisterV4.torus_numbers_OFC {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
    (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) :
    0 < R.β 2 ∧ R.β 2 ≤ 1 / 10 ^ 7 ∧ R.β 3 ≤ 3 / 20 ∧ 0 < R.later.circle.γ ∧
      R.later.split.b ≤ 1 / 6 ∧ R.later.err.s ≤ 1 / 7 ∧
      R.later.split.b + R.later.err.s ≤ 1 / 100 := by
  obtain ⟨hγ, -, -, hβ2⟩ := R.gram_request_of_below_V4C hT.complete_caps_V4C.2.2.1
  have hb := R.later.b_lt_audit_VAL6
  have hs := R.later.s_lt_b'_VAL6
  have hb' := R.later.b'_lt_VAL6
  have h3 : R.later.excl.β₃ < 1 / 10 :=
    (R.later.β₃_lt.trans_le hlc).trans threeSplittingExclusionThreshold_lt
  have h2 := R.later.β₂_pos
  rw [R.β_two_VAL6] at hβ2
  rw [R.β_two_VAL6, R.β_three_VAL6]
  refine ⟨h2, hβ2, by linarith, hγ, by linarith, by linarith, by linarith⟩

/-! ### The torus of a register -/

/-- The plane side `N = ⌈8/β₂⌉₊` of the torus of `β₂`. -/
def torRegSide_OFC (β₂ : ℝ) : ℕ := ⌈8 / β₂⌉₊

theorem torRegSide_pos_OFC {β₂ : ℝ} (hβ₂ : 0 < β₂) : 0 < torRegSide_OFC β₂ :=
  Nat.ceil_pos.mpr (by positivity)

/-- **The flat torus of `β₂`**: periods `(N, N, β₂)`, `N = ⌈8/β₂⌉₊`. -/
def torRegPeriods_OFC (β₂ : ℝ) (hβ₂ : 0 < β₂) : TorusPeriods_FXC1 where
  L := ![(torRegSide_OFC β₂ : ℝ), (torRegSide_OFC β₂ : ℝ), β₂]
  pos := by
    have hN : (0 : ℝ) < torRegSide_OFC β₂ := Nat.cast_pos.mpr (torRegSide_pos_OFC hβ₂)
    intro i
    fin_cases i
    · exact hN
    · exact hN
    · exact hβ₂

section Periods

variable {β₂ : ℝ} (hβ₂ : 0 < β₂)

theorem torRegPeriods_L0_OFC :
    (torRegPeriods_OFC β₂ hβ₂).L 0 = (torRegSide_OFC β₂ : ℝ) * 1 := by
  simp [torRegPeriods_OFC]

theorem torRegPeriods_L1_OFC :
    (torRegPeriods_OFC β₂ hβ₂).L 1 = (torRegSide_OFC β₂ : ℝ) * 1 := by
  simp [torRegPeriods_OFC]

theorem torRegPeriods_L2_OFC : (torRegPeriods_OFC β₂ hβ₂).L 2 ≤ 1 * β₂ := by
  simp [torRegPeriods_OFC]

theorem torRegPeriods_plane_OFC : 8 * 1 / β₂ ≤ planePeriod_FXC1 (torRegPeriods_OFC β₂ hβ₂) := by
  simp only [planePeriod_FXC1, torRegPeriods_OFC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, min_self, mul_one]
  exact Nat.le_ceil _

end Periods

/-! ### The packet at the register -/

section Packet

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D} (R : ClosedRegisterV4 D T)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
  (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0})

/-- The flat torus of the register: `torRegPeriods_OFC β₂`. -/
abbrev torRegTorus_OFC : Type := Tor_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos)

/-- **The flat torus packet at the register** (scale `ρ ≡ 1`): `LocalChartPacketsC14` at exactly
the register's values in the order of `exists_chainEStrategy_RGC` (free `K_f, δ, ε_r, Λ_z`);
non-empty circle family, empty slim / edge / zero families. No orientation is involved. -/
def torRegPackets_OFC (Kf : ℕ) (δ εr Λz : ℝ) :
    LocalChartPacketsC14 (torRegTorus_OFC R)
      (torMetric_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))
      (torMS_hmetric_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))
      (fun _ => (1 : ℝ)) (fun _ => one_pos) R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
      R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr
      R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ
      Λz :=
  torPacketsC14_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos) (R := 1) one_pos
    (R.torus_numbers_OFC hT hlc).1 (R.torus_numbers_OFC hT hlc).2.1
    (by rw [R.β_two_VAL6]; exact torRegPeriods_L2_OFC R.later.β₂_pos)
    (by rw [R.β_two_VAL6]; exact torRegPeriods_plane_OFC R.later.β₂_pos)
    (torRegSide_OFC R.later.excl.β₂) (torRegPeriods_L0_OFC R.later.β₂_pos)
    (torRegPeriods_L1_OFC R.later.β₂_pos) (R.torus_numbers_OFC hT hlc).2.2.1
    (R.torus_numbers_OFC hT hlc).2.2.2.1 (R.torus_numbers_OFC hT hlc).2.2.2.2.1
    (R.torus_numbers_OFC hT hlc).2.2.2.2.2.1 (R.torus_numbers_OFC hT hlc).2.2.2.2.2.2

/-- **The closed family `LocalChartPacketsC14Z` on the register torus** (`o_M` a parameter: the
zero family is empty); its `LocalChartPacketsC14` is `torRegPackets_OFC` (by `rfl`,
`torRegPacketsZ_toC14_OFC`). -/
def torRegPacketsZ_OFC (Kf : ℕ) (δ εr Λz : ℝ)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (torRegTorus_OFC R) 3) :
    LocalChartPacketsC14Z (torRegTorus_OFC R)
      (torMetric_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))
      (torMS_hmetric_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))
      (fun _ => (1 : ℝ)) (fun _ => one_pos) R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
      R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr
      R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ
      Λz oM where
  toLocalChartPacketsC14 := torRegPackets_OFC R hT hlc Kf δ εr Λz
  weak_edge_density := fun p hp => absurd hp
    (torNotMemStratum_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos) one_pos
      (R.torus_numbers_OFC hT hlc).1 (R.torus_numbers_OFC hT hlc).2.1
      (by rw [R.β_two_VAL6]; exact torRegPeriods_L2_OFC R.later.β₂_pos)
      (by rw [R.β_two_VAL6]; exact torRegPeriods_plane_OFC R.later.β₂_pos)
      (R.torus_numbers_OFC hT hlc).2.2.1 (by decide) p)
  zero_sublevel_types := fun c hc => absurd hc (notMem_empty c)

theorem torRegPacketsZ_toC14_OFC {Kf : ℕ} {δ εr Λz : ℝ}
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (torRegTorus_OFC R) 3) :
    (torRegPacketsZ_OFC R hT hlc Kf δ εr Λz oM).toLocalChartPacketsC14D.toLocalChartPacketsC14 =
      torRegPackets_OFC R hT hlc Kf δ εr Λz :=
  rfl

/-- The origin node of the register torus. -/
def torRegOrigin_OFC : torRegTorus_OFC R :=
  torPi_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos) (torNode_FXC1 1 0 0)

variable {Kf : ℕ} {δ εr Λz : ℝ}

/-- **The origin node is a circle centre of the register packet.** -/
theorem torRegPackets_origin_mem_OFC :
    torRegOrigin_OFC R ∈ (torRegPackets_OFC R hT hlc Kf δ εr Λz).circle.centres := by
  have hN : (0 : ℤ) < (torRegSide_OFC R.later.excl.β₂ : ℤ) :=
    Int.natCast_pos.mpr (torRegSide_pos_OFC R.later.β₂_pos)
  exact ⟨(0, 0), ⟨⟨le_rfl, hN⟩, ⟨le_rfl, hN⟩⟩, by simp [torRegOrigin_OFC]⟩

/-- The circle coordinate of the origin centre vanishes at the origin. -/
theorem torRegPackets_origin_coord_OFC :
    cgpCircleCoord (torRegPackets_OFC R hT hlc Kf δ εr Λz).toLocalChartFamily
      (torRegOrigin_OFC R) (torRegPackets_origin_mem_OFC R hT hlc) (torRegOrigin_OFC R) = 0 := by
  change torEta_FXC1 _ 1 _ _ = 0
  exact torEta_center_FXC1 _ _ _

end Packet

end DifferentialGeometry.Geometry.Collapse
