import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterV2
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2Realization
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2RowsStrategy

/-!
# The boundary validity record for the PER-SEQUENCE supply (lane FC39-BQ; review 52 R-c, route 2)

User decision 2026-10-05: the boundary supply takes the blueprint's per-sequence form (BBR01,
B:10356–10367: ONE assignment independent of the member, point and boundary component; BR20–BR23,
B:10452–10455: the joint producer outputs `V` and the tail ON THE SEQUENCE; BR25, B:10489–10490:
the tail includes `H_n = n/4 > 400V`). As on the closed side (`exists_closed_realization_VAL3`),
the STRATEGY `T : BoundaryThresholdsV2 D` may depend on the standing sequence; the register
`BoundaryRegisterV2` is unchanged. The uniform `BoundaryThresholdValidity`
(`BoundaryRegisterValidity.lean`, field `family` for EVERY member) is superseded and kept as
history.

This file holds the member-free part:

* `PartialBoundaryThresholdValidityV2_BQ K D T` — the early sources on `D.toClosedEarlyData`
  (PR01–PR03 as in `PartialClosedThresholdValidityV2`) and the constant interior slots `lc18`, `I₁`
  for EVERY boundary request `(ϑ, shortErr, bcgErr)` (BR04–BR23). The member part (T3B's per-member
  conclusion on the final family on the tail of ONE sequence) is the per-sequence supply, stated
  in a later file on the sequence hypothesis at the top of `build-logs/resume/sheet-FC39-BQ.md`.
  PARTIAL: no boundary-slot `Out`s yet (BCG02–03 square sum, short comparisons, cusp/product slots).
* `BoundaryStrategyRefinesV2_BQ T U` — `T` refines `U` slot by slot (upper slots below, lower slots
  above, the interior closed strategies refine), the shape a per-sequence strategy takes.
* Consumers: `β₃_le_BQ`, `toClosed_lc18_I₁_BQ`, `ϑ_lt_BQ`, `tailLow_le_BQ`, `cuspQuality_lt_BQ`;
  inhabitant `nonempty_partialBoundaryThresholdValidityV2_BQ` (early data `closedEarlyDataV3 K`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology
open GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

/-- **The member-free part of the boundary validity on the staged register** (PARTIAL). -/
structure PartialBoundaryThresholdValidityV2_BQ (K : ℕ) (D : BoundaryEarlyData)
    (T : BoundaryThresholdsV2 D) : Prop where
  /-- PR01 `N` on the augmented constants (BR00–BR03). -/
  N_ge : gafMultiplicity ≤ D.N
  /-- PR01 `P`: CGP02's profile bound. -/
  P_ge : cgpProfileBound ≤ D.P
  /-- PR01 `P`: the slim/edge/circle graph-model profile bound. -/
  P_ge_sgp : sgpProfileBound ≤ D.P
  /-- PR01 `P`: the zero graph-model profile bound. -/
  P_ge_zero : zeroProfileBound ≤ D.P
  /-- PR02 `L₀`: CGP02's global derivative bound of the initial map. -/
  L₀_ge : gafDerivativeBound ≤ D.L₀
  /-- PR03 `Ξ_j`: CFS15's conclusion at the stage dimension, jet order `K`, ratio `5/3`. -/
  Ξ_cfs15 : ∀ j, Cfs15ModulusOut (gafStageDim j) K (5 / 3) (D.Ξ j)
  /-- PR03: every actual `Γ_j` of every stage choice lies in CFS15's native range. -/
  Ξ_range : ∀ (st : ClosedStage D.toClosedEarlyData) j,
    Cfs15ModulusAtV2 (gafStageDim j) K (5 / 3) (D.Ξ j) (st.Γ j)
  /-- BR04–BR23, PR12: LC18's obstruction for every boundary request. -/
  lc18_le : ∀ ϑ sh bc, (T.interior ϑ sh bc).lc18 ≤ threeSplittingExclusionThreshold.{0, 0}
  /-- BR04–BR23, PR20: the comparison constant `I(1)` for every boundary request. -/
  I₁_eq : ∀ ϑ sh bc, (T.interior ϑ sh bc).I₁ = ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2

/-- **`T` refines `U`** (boundary strategies): every upper slot of `T` is below `U`'s, every lower
slot above it, the fixed constants of `U` are among `T`'s, and the interior closed strategies refine
(`ClosedStrategyRefinesV2`, which leaves `V` and `H` free — they are the sequence's). -/
structure BoundaryStrategyRefinesV2_BQ {D : BoundaryEarlyData} (T U : BoundaryThresholdsV2 D) :
    Prop where
  ϑUp_le : ∀ st, T.ϑUp st ≤ U.ϑUp st
  shortUp_le : ∀ st ϑ, T.shortUp st ϑ ≤ U.shortUp st ϑ
  bcgUp_le : ∀ st ϑ, T.bcgUp st ϑ ≤ U.bcgUp st ϑ
  interior_refines : ∀ ϑ sh bc, ClosedStrategyRefinesV2 (T.interior ϑ sh bc) (U.interior ϑ sh bc)
  cuspUp_le : ∀ st ϑ sh bc v, T.cuspUp st ϑ sh bc v ≤ U.cuspUp st ϑ sh bc v
  cuspRadii_ge : ∀ st ϑ sh bc v q, U.cuspRadii st ϑ sh bc v q ≤ T.cuspRadii st ϑ sh bc v q
  productUp_le : ∀ st ϑ sh bc v q H, T.productUp st ϑ sh bc v q H ≤ U.productUp st ϑ sh bc v q H
  tailLow_ge : ∀ st ϑ sh bc v q H r, U.tailLow st ϑ sh bc v q H r ≤ T.tailLow st ϑ sh bc v q H r
  fixed_subset : U.fixedConstants ⊆ T.fixedConstants

namespace PartialBoundaryThresholdValidityV2_BQ

variable {K : ℕ} {D : BoundaryEarlyData} {T : BoundaryThresholdsV2 D}

/-- **Consumer**: the exclusion quality `β₃` of every boundary register is below LC18's
obstruction (the producers' `β 3 ≤ thr`). -/
theorem β₃_le_BQ (hv : PartialBoundaryThresholdValidityV2_BQ K D T) (R : BoundaryRegisterV2 D T) :
    R.later.excl.β₃ ≤ threeSplittingExclusionThreshold.{0, 0} :=
  (R.later.β₃_lt.trans_le (hv.lc18_le R.ϑ R.shortErr R.bcgErr)).le

/-- **Consumer**: the closed strategy actually used by the boundary register (`T.toClosed`, with
`w ∩ w_cap` and `H n = n/4`) carries LC18's obstruction and the constant `I(1)`. -/
theorem toClosed_lc18_I₁_BQ (hv : PartialBoundaryThresholdValidityV2_BQ K D T)
    (ϑ : Fin 3 → ℝ) (sh bc : ℝ) :
    (T.toClosed ϑ sh bc).lc18 ≤ threeSplittingExclusionThreshold.{0, 0} ∧
      (T.toClosed ϑ sh bc).I₁ = ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 :=
  ⟨hv.lc18_le ϑ sh bc, hv.I₁_eq ϑ sh bc⟩

end PartialBoundaryThresholdValidityV2_BQ

namespace BoundaryStrategyRefinesV2_BQ

variable {D : BoundaryEarlyData} {T U : BoundaryThresholdsV2 D}

/-- **Consumer**: a register at the refining strategy meets `U`'s `ϑ` request. -/
theorem ϑ_lt_BQ (h : BoundaryStrategyRefinesV2_BQ T U) (R : BoundaryRegisterV2 D T) (j : Fin 3) :
    R.ϑ j < U.ϑUp R.stage :=
  ((R.ϑ_lt j).trans_le (min_le_right _ _)).trans_le (h.ϑUp_le R.stage)

/-- **Consumer**: a register at the refining strategy has its tail above `U`'s tail request. -/
theorem tailLow_le_BQ (h : BoundaryStrategyRefinesV2_BQ T U) (R : BoundaryRegisterV2 D T) :
    U.tailLow R.stage R.ϑ R.shortErr R.bcgErr R.later.values R.cuspQuality R.cuspRadius
      R.physicalScale ≤ R.tail :=
  (h.tailLow_ge _ _ _ _ _ _ _ _).trans R.tail_ge

/-- **Consumer**: a register at the refining strategy meets `U`'s cusp request. -/
theorem cuspQuality_lt_BQ (h : BoundaryStrategyRefinesV2_BQ T U) (R : BoundaryRegisterV2 D T) :
    R.cuspQuality < U.cuspUp R.stage R.ϑ R.shortErr R.bcgErr R.later.values :=
  (R.cuspQuality_lt.trans_le (min_le_left _ _)).trans_le (h.cuspUp_le _ _ _ _ _)

end BoundaryStrategyRefinesV2_BQ

/-- `I(1) = ∫₀¹ sinh² > 0`. -/
theorem integral_sinh_sq_pos_BQ : 0 < ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Real.continuous_sinh.pow 2).intervalIntegrable 0 1) (fun x hx => ?_) one_pos
  exact pow_pos (Real.sinh_pos_iff.mpr hx.1) 2

/-- The boundary early data on the closed constant provenance `closedEarlyDataV3 K`. -/
def boundaryEarlyDataV3_BQ (K : ℕ) : BoundaryEarlyData :=
  { closedEarlyDataV3 K with δStar := 1, δStar_pos := one_pos, C₀ := 1, C₀_pos := one_pos }

/-- A boundary strategy whose interior is the rows' total strategy with LC18's obstruction and the
actual `I(1)`. -/
def boundaryThresholdsV3_BQ (K : ℕ) : BoundaryThresholdsV2 (boundaryEarlyDataV3_BQ K) where
  ϑUp := fun _ => 1
  ϑUp_pos := fun _ => one_pos
  shortUp := fun _ _ => 1
  shortUp_pos := fun _ _ => one_pos
  bcgUp := fun _ _ => 1
  bcgUp_pos := fun _ _ => one_pos
  interior := fun _ _ _ =>
    { partialRowsStrategyV2 (boundaryEarlyDataV3_BQ K).toClosedEarlyData with
      lc18 := threeSplittingExclusionThreshold.{0, 0}
      lc18_pos := threeSplittingExclusionThreshold_pos
      I₁ := ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2
      I₁_pos := integral_sinh_sq_pos_BQ }
  cuspUp := fun _ _ _ _ _ => 1
  cuspUp_pos := fun _ _ _ _ _ => one_pos
  cuspRadii := fun _ _ _ _ _ _ => 0
  productUp := fun _ _ _ _ _ _ _ => 1
  productUp_pos := fun _ _ _ _ _ _ _ => one_pos
  tailLow := fun _ _ _ _ _ _ _ _ => 0
  fixedConstants := ∅

/-- **Inhabitant**: the member-free boundary validity holds at concrete data, and a boundary
register exists there (with `β₃` below LC18's obstruction). -/
theorem nonempty_partialBoundaryThresholdValidityV2_BQ (K : ℕ) :
    PartialBoundaryThresholdValidityV2_BQ K (boundaryEarlyDataV3_BQ K) (boundaryThresholdsV3_BQ K) ∧
      ∃ R : BoundaryRegisterV2 (boundaryEarlyDataV3_BQ K) (boundaryThresholdsV3_BQ K),
        R.later.excl.β₃ ≤ threeSplittingExclusionThreshold.{0, 0} := by
  obtain ⟨hN, hP, hPs, hPz, hL, hΞ, hΞr, -⟩ := closedEarlyDataV3_fields_VAL3 K
  have hv : PartialBoundaryThresholdValidityV2_BQ K (boundaryEarlyDataV3_BQ K)
      (boundaryThresholdsV3_BQ K) :=
    ⟨hN, hP, hPs, hPz, hL, hΞ, hΞr, fun _ _ _ => le_rfl, fun _ _ _ => rfl⟩
  obtain ⟨R⟩ := exists_boundaryRegisterV2 (boundaryEarlyDataV3_BQ K) (boundaryThresholdsV3_BQ K)
  exact ⟨hv, R, hv.β₃_le_BQ R⟩

/-- **Consumer (refinement is reflexive on the inhabitant's interior shape)**: every strategy
refines itself. -/
theorem BoundaryStrategyRefinesV2_BQ.refl_BQ {D : BoundaryEarlyData} (T : BoundaryThresholdsV2 D) :
    BoundaryStrategyRefinesV2_BQ T T where
  ϑUp_le := fun _ => le_rfl
  shortUp_le := fun _ _ => le_rfl
  bcgUp_le := fun _ _ => le_rfl
  interior_refines := fun _ _ _ =>
    { Nb_eq := rfl, cw_eq := rfl, I₁_eq := rfl, LmaxLow_eq := rfl, endpointUp_eq := rfl,
      circleUp_le := fun _ _ _ _ => le_rfl, lc18_le := le_rfl, β₂Up_le := fun _ _ _ => le_rfl,
      ΔLow_ge := fun _ _ _ _ => le_rfl, errorsUp_le := fun _ _ _ => le_rfl,
      sectionUp_le := fun _ _ _ _ => le_rfl, lfr29W_le := fun _ _ _ _ _ => le_rfl,
      σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl, scaleUp_le := fun _ _ _ _ => le_rfl,
      wUp_le := fun _ _ _ _ _ => le_rfl, splitUp_le := fun _ _ _ _ _ => le_rfl,
      β₁Up_le := fun _ _ _ _ _ _ => le_rfl, T₀Low_ge := fun _ _ _ _ _ _ _ => le_rfl,
      tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl }
  cuspUp_le := fun _ _ _ _ _ => le_rfl
  cuspRadii_ge := fun _ _ _ _ _ _ => le_rfl
  productUp_le := fun _ _ _ _ _ _ _ => le_rfl
  tailLow_ge := fun _ _ _ _ _ _ _ _ => le_rfl
  fixed_subset := subset_rfl

end DifferentialGeometry.Geometry.Collapse
