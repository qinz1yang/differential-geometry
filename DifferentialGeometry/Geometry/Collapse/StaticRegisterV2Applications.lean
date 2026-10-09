import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterV2
import DifferentialGeometry.Geometry.Collapse.StaticRegisterApplications

/-!
# A concrete inhabitant of the staged closed register (lane FC39-VAL2)

Review 52 (R-a) and the inhabitant rule (a structure that lanes build on needs a compiled
nontrivial inhabitant): a concrete threshold record `unitClosedThresholdsV2` on the concrete early
datum `unitClosedEarlyData` (`StaticRegisterApplications`), the existence of a staged register at
these concrete data, and the consumer facts at that register (CAA01's edge error, `β₁ < ζ`,
`σ_col < 1`, `400V < L_max`); the same for the boundary register on the staged closed register
(`unitBoundaryEarlyDataV2`, `unitBoundaryThresholdsV2`).
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace DifferentialGeometry.Geometry.Collapse

/-- A concrete staged threshold record on `unitClosedEarlyData` (every upper slot `1`, LPA02
output `V = T₀`, every lower slot `0`, test radius `H_α = α`). -/
def unitClosedThresholdsV2 : ClosedThresholdsV2 unitClosedEarlyData where
  Nb := fun _ => 0
  Nb_nonneg := fun _ => le_rfl
  cw := fun _ => 0
  cw_nonneg := fun _ => le_rfl
  circleUp := fun _ _ _ _ => 1
  circleUp_pos := fun _ _ _ _ => one_pos
  lc18 := 1
  lc18_pos := one_pos
  β₂Up := fun _ _ _ => 1
  β₂Up_pos := fun _ _ _ => one_pos
  ΔLow := fun _ _ _ _ => 0
  errorsUp := fun _ _ _ => 1
  errorsUp_pos := fun _ _ _ => one_pos
  sectionUp := fun _ _ _ _ => 1
  sectionUp_pos := fun _ _ _ _ => one_pos
  lfr29W := fun _ _ _ _ _ => 1
  lfr29W_pos := fun _ _ _ _ _ => one_pos
  endpointUp := fun _ _ _ _ _ _ => 1
  endpointUp_pos := fun _ _ _ _ _ _ => one_pos
  σcolUp := fun _ _ _ _ _ _ _ => 1
  σcolUp_pos := fun _ _ _ _ _ _ _ => one_pos
  I₁ := 1
  I₁_pos := one_pos
  scaleUp := fun _ _ _ _ => 1
  scaleUp_pos := fun _ _ _ _ => one_pos
  wUp := fun _ _ _ _ _ => 1
  wUp_pos := fun _ _ _ _ _ => one_pos
  splitUp := fun _ _ _ _ _ => 1
  splitUp_pos := fun _ _ _ _ _ => one_pos
  β₁Up := fun _ _ _ _ _ _ => 1
  β₁Up_pos := fun _ _ _ _ _ _ => one_pos
  T₀Low := fun _ _ _ _ _ _ _ => 0
  lpa02V := fun _ _ _ _ _ _ _ T₀ => T₀
  T₀_le_lpa02V := fun _ _ _ _ _ _ _ _ => le_rfl
  LmaxLow := fun _ _ _ _ _ _ => 0
  tailLow := fun _ _ _ _ _ _ _ => 0
  H := fun α => (α : ℝ)
  H_tendsto := tendsto_natCast_atTop_atTop

/-- **The inhabitant**: a staged closed register exists at the concrete data. -/
theorem nonempty_unit_closedRegisterV2_VAL2 :
    Nonempty (ClosedRegisterV2 unitClosedEarlyData unitClosedThresholdsV2) :=
  exists_closedRegisterV2 unitClosedEarlyData unitClosedThresholdsV2

/-- **Consumer at the concrete register**: CAA01's edge error is below `10⁻³`, the splitting
quality `β₁` is below LC73's slim quality, the collapsed-model error is below `1` and the upper
test range is above `400 V`. -/
theorem unit_closedRegisterV2_facts_VAL2 :
    ∃ R : ClosedRegisterV2 unitClosedEarlyData unitClosedThresholdsV2,
      5 * R.later.excl.β₂ + R.later.split.b + R.later.err.s < 1 / 1000 ∧
      R.β 1 < R.later.err.co.ζ ∧ R.later.err.σcol < 1 ∧
      400 * R.later.split.V < R.later.Lmax := by
  obtain ⟨R⟩ := nonempty_unit_closedRegisterV2_VAL2
  refine ⟨R, R.later.edgeError_lt_obstruction_VAL2, ?_, R.later.σcol_lt_one_VAL2,
    R.later.Lmax_gt_VAL2⟩
  rw [ClosedRegisterV2.β_one_VAL2]
  exact R.later.β₁_lt_ζ_VAL2

/-- A concrete augmented early datum: `unitClosedEarlyData` with `δ_* = C₀ = 1`. -/
def unitBoundaryEarlyDataV2 : BoundaryEarlyData where
  toClosedEarlyData := unitClosedEarlyData
  δStar := 1
  δStar_pos := one_pos
  C₀ := 1
  C₀_pos := one_pos

/-- A concrete boundary threshold record on the staged closed register (every upper slot `1`,
every lower slot `0`, interior slots `unitClosedThresholdsV2`, no fixed constants). -/
def unitBoundaryThresholdsV2 : BoundaryThresholdsV2 unitBoundaryEarlyDataV2 where
  ϑUp := fun _ => 1
  ϑUp_pos := fun _ => one_pos
  shortUp := fun _ _ => 1
  shortUp_pos := fun _ _ => one_pos
  bcgUp := fun _ _ => 1
  bcgUp_pos := fun _ _ => one_pos
  interior := fun _ _ _ => unitClosedThresholdsV2
  cuspUp := fun _ _ _ _ _ => 1
  cuspUp_pos := fun _ _ _ _ _ => one_pos
  cuspRadii := fun _ _ _ _ _ _ => 0
  productUp := fun _ _ _ _ _ _ _ => 1
  productUp_pos := fun _ _ _ _ _ _ _ => one_pos
  tailLow := fun _ _ _ _ _ _ _ _ => 0
  fixedConstants := ∅

/-- **The boundary inhabitant**: a boundary register on the staged closed register exists at the
concrete data; its volume parameter is below `w_cap` and its cusp quality below `β₁`. -/
theorem unit_boundaryRegisterV2_facts_VAL2 :
    ∃ R : BoundaryRegisterV2 unitBoundaryEarlyDataV2 unitBoundaryThresholdsV2,
      R.later.scale.w < boundaryVolumeCap ∧ R.cuspQuality < R.later.split.β₁ := by
  obtain ⟨R⟩ := exists_boundaryRegisterV2 unitBoundaryEarlyDataV2 unitBoundaryThresholdsV2
  exact ⟨R, R.w_lt_cap_VAL2, R.cuspQuality_lt_β₁_VAL2⟩

end DifferentialGeometry.Geometry.Collapse
