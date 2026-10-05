import DifferentialGeometry.Geometry.Collapse.BoundarySequenceValidityBridge
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterV2SequenceSupplyTied

/-!
# Stage order of the per-sequence boundary supply: `V` and `δ` are producer outputs (FC39-BQ2)

External review 54, §6.3 (dispositions row 6): positivity and the stage order must be explicit —
`0 < δ < δ'`; `εr, δ', Λ'` before `T₀` with `20Λ' ≤ T₀`; `V` and `δ` are OUTPUTS of the joint
producer (BR20–BR23, B:10436–10456; `lpa02V` is LPA02's finite output, not a free lower-bound
slot, `StaticRegisterV2.lean:184–187`). A refinement relation must not enlarge `V`.

* `BoundaryStrategyRefinesV3_BQ2 T U` — `BoundaryStrategyRefinesV2_BQ` plus `lpa02V_eq`: `T` keeps
  `U`'s `V` slot. It is a GENUINE refinement: `BoundaryRegisterV2.ofRefinesV3_BQ2` turns every
  register at `T` into a register at `U` with the same stage, requests and values (in particular the
  same `V`), `exists_register_same_values_BQ2`. No monotonicity of the family in `V` is claimed (the
  per-member `Out` has the `g`-ball clause at radius `(… + 400V + …)ρ`, not monotone in `V`).
* `BoundaryProducerOutputs_BQ2 D` — the producer's Skolem outputs on ONE sequence, fixed before
  any request strategy: `εr, δ', Λz` as functions of the values read before `T₀`
  (`st, ci, ex, er, sc, b, β₁`), and `V`, `δ` as functions of those and `T₀` (before `L_max`, the
  cusp requests and the tail), with `T₀ ≤ V`.
* `BoundaryThresholdsV2.withV_BQ2 U VF` — the request strategy `U` with its `V` slot set to the
  producer's `VF`; a strategy `T` refining `U.withV_BQ2 VF` (V3) has `V = VF` at every register
  (`BoundaryStrategyRefinesV3_BQ2.V_eq_VF_BQ2`) and still refines `U` on every request
  (`BoundaryStrategyRefinesV3_BQ2.toV2_withV_BQ2`), so the validity bridge applies
  (`PartialBoundaryThresholdValidityV3_BQ2.of_withV_refines_BQ2`).
* `PartialBoundaryFamilyOnSeqV3_BQ2 … R εr δ' Λz δ` — on the boundary standing sequence at
  `D.δStar` (member `n` at `δ_{n+1}`): `0 < εr < 1/4`, `εr < ε₀`, `0 < δ'`, `0 < Λz`,
  `20Λz ≤ T₀Low` (hence `≤ T₀`), `0 < δ < δ'`, and T3B-R's per-member conclusion on every member of
  the register's tail at the register's values, cusp requests `βd = εN = R.cuspQuality` (BR24).
  `PartialBoundaryFamilyAtSeqV3_BQ2 … T P` — the record at every register, with the witnesses read
  from `P` at the register's prefix (`δ` at the prefix and `T₀`).
* Consumers: `twenty_Λz_le_T₀_BQ2`, `toOnSeqV2_BQ2`, `PartialBoundaryFamilyAtSeqV3_BQ2.toTied_BQ2`
  (the V3 record implies FC39-BQ's tied record), `PartialBoundaryFamilyAtSeqV3_BQ2.exists_tail_BQ2`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

/-! ### A genuine refinement: registers at `T` are registers at `U` -/

/-- The closed slots used by the boundary register refine when the interior strategies do. -/
theorem ClosedStrategyRefinesV2.toClosed_BQ2 {D : BoundaryEarlyData} {T U : BoundaryThresholdsV2 D}
    {ϑ : Fin 3 → ℝ} {sh bc : ℝ}
    (h : ClosedStrategyRefinesV2 (T.interior ϑ sh bc) (U.interior ϑ sh bc)) :
    ClosedStrategyRefinesV2 (T.toClosed ϑ sh bc) (U.toClosed ϑ sh bc) where
  Nb_eq := h.Nb_eq
  cw_eq := h.cw_eq
  I₁_eq := h.I₁_eq
  LmaxLow_eq := h.LmaxLow_eq
  endpointUp_eq := h.endpointUp_eq
  circleUp_le := h.circleUp_le
  lc18_le := h.lc18_le
  β₂Up_le := h.β₂Up_le
  ΔLow_ge := h.ΔLow_ge
  errorsUp_le := h.errorsUp_le
  sectionUp_le := h.sectionUp_le
  lfr29W_le := h.lfr29W_le
  σcolUp_le := h.σcolUp_le
  scaleUp_le := h.scaleUp_le
  wUp_le := fun st ci ex er Λ => min_le_min_right _ (h.wUp_le st ci ex er Λ)
  splitUp_le := h.splitUp_le
  β₁Up_le := h.β₁Up_le
  T₀Low_ge := h.T₀Low_ge
  tailLow_ge := h.tailLow_ge

/-- **A staged later choice at `T` is one at `U`** with the same values, when `T` refines `U` and
keeps `U`'s `V` slot and test radii. -/
def ClosedLaterV2.ofRefines_BQ2 {D : ClosedEarlyData} {T U : ClosedThresholdsV2 D}
    {st : ClosedStage D} (h : ClosedStrategyRefinesV2 T U) (hV : T.lpa02V = U.lpa02V)
    (hH : T.H = U.H) (la : ClosedLaterV2 D T st) : ClosedLaterV2 D U st :=
  { la with
    γ_lt := la.γ_lt.trans_le (min_le_min_left _ (h.circleUp_le _ _ _ _))
    E_lt := la.E_lt.trans_le (min_le_min_left _ (h.circleUp_le _ _ _ _))
    δ_lt := la.δ_lt.trans_le (min_le_min_left _ (h.circleUp_le _ _ _ _))
    γc_lt := la.γc_lt.trans_le (h.circleUp_le _ _ _ _)
    βc_lt := la.βc_lt.trans_le (min_le_min_left _ (h.circleUp_le _ _ _ _))
    β₃_lt := la.β₃_lt.trans_le h.lc18_le
    β₂_lt := la.β₂_lt.trans_le (min_le_min_right _ (h.β₂Up_le _ _ _))
    Δ_gt := (max_le_max le_rfl (max_le_max le_rfl (h.ΔLow_ge _ _ _ _))).trans_lt la.Δ_gt
    qe_lt := la.qe_lt.trans_le (min_le_min_left _ (h.errorsUp_le _ _ _))
    qs_lt := la.qs_lt.trans_le (min_le_min_left _ (h.errorsUp_le _ _ _))
    ve_lt := la.ve_lt.trans_le (min_le_min_left _ (h.errorsUp_le _ _ _))
    ε_lt := la.ε_lt.trans_le (h.errorsUp_le _ _ _)
    ζ_lt := la.ζ_lt.trans_le (h.errorsUp_le _ _ _)
    e₀_lt := la.e₀_lt.trans_le (min_le_min_left _ (h.errorsUp_le _ _ _))
    ε₀_lt := la.ε₀_lt.trans_le (min_le_min_left _ (h.errorsUp_le _ _ _))
    τ_lt := la.τ_lt.trans_le (min_le_min_left _ (h.sectionUp_le _ _ _ _))
    μ_lt := la.μ_lt.trans_le (min_le_min_left _ (h.sectionUp_le _ _ _ _))
    b'_lt := la.b'_lt.trans_le (min_le_min_right _ (h.lfr29W_le _ _ _ _ _))
    s'_lt := la.s'_lt.trans_le (min_le_min_right _ (h.lfr29W_le _ _ _ _ _))
    s_lt := by rw [← h.endpointUp_eq]; exact la.s_lt
    σcol_lt := la.σcol_lt.trans_le (min_le_min_right _ (h.σcolUp_le _ _ _ _ _ _ _))
    Λ_lt := la.Λ_lt.trans_le (h.scaleUp_le _ _ _ _)
    regScale_Cρ := by
      have e : closedScaleConstantV2 D U st = closedScaleConstantV2 D T st := by
        simp only [closedScaleConstantV2, h.Nb_eq, h.cw_eq]
      rw [e]
      exact la.regScale_Cρ
    w_lt := la.w_lt.trans_le (min_le_min_right _ (h.wUp_le _ _ _ _ _))
    b_lt := la.b_lt.trans_le (min_le_min_right _ (h.splitUp_le _ _ _ _ _))
    β₁_lt := la.β₁_lt.trans_le (min_le_min_right _ (h.β₁Up_le _ _ _ _ _ _))
    T₀_ge := (max_le_max le_rfl (h.T₀Low_ge _ _ _ _ _ _ _)).trans la.T₀_ge
    V_eq := by rw [← hV]; exact la.V_eq
    Lmax_gt := by rw [← h.LmaxLow_eq]; exact la.Lmax_gt
    tail_ge := (h.tailLow_ge _ _ _ _ _ _ _).trans la.tail_ge
    H_gt := by rw [← hH]; exact la.H_gt }

/-- **`T` refines `U` without touching `V`** (review 54 §6.3): every request of `U` is met at `T`
(`BoundaryStrategyRefinesV2_BQ`) and `T` keeps `U`'s `V` slot (`lpa02V`, LPA02's output). -/
structure BoundaryStrategyRefinesV3_BQ2 {D : BoundaryEarlyData} (T U : BoundaryThresholdsV2 D) :
    Prop extends BoundaryStrategyRefinesV2_BQ T U where
  /-- The `V` slot is not touched. -/
  lpa02V_eq : ∀ ϑ sh bc, (T.interior ϑ sh bc).lpa02V = (U.interior ϑ sh bc).lpa02V

/-- **A register at a refining strategy is a register at `U`** with the same stage, requests,
later values, cusp choices and tail (so with the same `V`). -/
def BoundaryRegisterV2.ofRefinesV3_BQ2 {D : BoundaryEarlyData} {T U : BoundaryThresholdsV2 D}
    (h : BoundaryStrategyRefinesV3_BQ2 T U) (R : BoundaryRegisterV2 D T) : BoundaryRegisterV2 D U
    where
  stage := R.stage
  ϑ := R.ϑ
  shortErr := R.shortErr
  bcgErr := R.bcgErr
  later := R.later.ofRefines_BQ2 (h.interior_refines R.ϑ R.shortErr R.bcgErr).toClosed_BQ2
    (h.lpa02V_eq R.ϑ R.shortErr R.bcgErr) rfl
  cuspQuality := R.cuspQuality
  cuspRadius := R.cuspRadius
  physicalScale := R.physicalScale
  tail := R.tail
  ϑ_pos := R.ϑ_pos
  ϑ_lt := fun j => (R.ϑ_lt j).trans_le (min_le_min_left _ (h.ϑUp_le _))
  ϑ_e := R.ϑ_e
  shortErr_pos := R.shortErr_pos
  shortErr_lt := R.shortErr_lt.trans_le (min_le_min_left _ (h.shortUp_le _ _))
  bcgErr_pos := R.bcgErr_pos
  bcgErr_lt := R.bcgErr_lt.trans_le (min_le_min_left _ (h.bcgUp_le _ _))
  cuspQuality_pos := R.cuspQuality_pos
  cuspQuality_lt := R.cuspQuality_lt.trans_le (min_le_min_right _ (h.cuspUp_le _ _ _ _ _))
  cuspRadius_ge := (max_le_max le_rfl (h.cuspRadii_ge _ _ _ _ _ _)).trans R.cuspRadius_ge
  physicalScale_pos := R.physicalScale_pos
  physicalScale_lt := R.physicalScale_lt.trans_le
    (min_le_min_left _ (h.productUp_le _ _ _ _ _ _ _))
  tail_ge_later := R.tail_ge_later
  tail_ge := (h.tailLow_ge _ _ _ _ _ _ _ _).trans R.tail_ge
  tail_wPrime := R.tail_wPrime
  tail_testRadius := R.tail_testRadius
  tail_fixed := fun n hn C hC => R.tail_fixed n hn C (h.fixed_subset hC)
  tail_edgeCollar := R.tail_edgeCollar
  tail_Δ := R.tail_Δ

/-- **Consumer (genuine refinement)**: every register at a strategy refining `U` without touching
`V` is a register at `U` with the same stage, requests, later values (including `V`), cusp choices
and tail. -/
theorem exists_register_same_values_BQ2 {D : BoundaryEarlyData} {T U : BoundaryThresholdsV2 D}
    (h : BoundaryStrategyRefinesV3_BQ2 T U) (R : BoundaryRegisterV2 D T) :
    ∃ R' : BoundaryRegisterV2 D U, R'.stage = R.stage ∧ R'.ϑ = R.ϑ ∧ R'.shortErr = R.shortErr ∧
      R'.bcgErr = R.bcgErr ∧ R'.later.values = R.later.values ∧
      R'.later.split.V = R.later.split.V ∧ R'.cuspQuality = R.cuspQuality ∧
      R'.cuspRadius = R.cuspRadius ∧ R'.physicalScale = R.physicalScale ∧ R'.tail = R.tail :=
  ⟨R.ofRefinesV3_BQ2 h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The producer's outputs and the request strategy with the producer's `V` -/

/-- **The producer's Skolem outputs on ONE standing sequence** (BR20–BR23), fixed before any
request strategy: `εr, δ', Λz` read the values chosen before `T₀`, and `V, δ` read those and `T₀`
(not `L_max`, the cusp requests or the tail); `T₀ ≤ V`. -/
structure BoundaryProducerOutputs_BQ2 (D : BoundaryEarlyData) where
  εrF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
    ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ
  δ'F : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
    ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ
  ΛzF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
    ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ
  VF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
    ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ → ℝ
  δF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
    ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ → ℝ
  T₀_le_VF : ∀ st ci ex er sc b β₁ T₀, T₀ ≤ VF st ci ex er sc b β₁ T₀

/-- The request strategy `U` with its `V` slot set to the producer's output `VF`. -/
def BoundaryThresholdsV2.withV_BQ2 {D : BoundaryEarlyData} (U : BoundaryThresholdsV2 D)
    (VF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
      ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ → ℝ)
    (hVF : ∀ st ci ex er sc b β₁ T₀, T₀ ≤ VF st ci ex er sc b β₁ T₀) : BoundaryThresholdsV2 D :=
  { U with
    interior := fun ϑ sh bc =>
      { U.interior ϑ sh bc with lpa02V := VF, T₀_le_lpa02V := hVF } }

namespace BoundaryStrategyRefinesV3_BQ2

variable {D : BoundaryEarlyData} {T U : BoundaryThresholdsV2 D}
  {VF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
    ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ → ℝ}
  {hVF : ∀ st ci ex er sc b β₁ T₀, T₀ ≤ VF st ci ex er sc b β₁ T₀}

/-- **`V` is the producer's output**: at every register of a strategy refining `U.withV_BQ2 VF`,
`V = VF` at the register's prefix and `T₀`. -/
theorem V_eq_VF_BQ2 (h : BoundaryStrategyRefinesV3_BQ2 T (U.withV_BQ2 VF hVF))
    (R : BoundaryRegisterV2 D T) :
    R.later.split.V = VF R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁ R.later.split.T₀ := by
  rw [R.later.V_eq]
  exact congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun
    (h.lpa02V_eq R.ϑ R.shortErr R.bcgErr) _) _) _) _) _) _) _) _

/-- **The requests of `U` are met**: a strategy refining `U.withV_BQ2 VF` refines `U` on every
request slot (the V2 relation does not read `V`). -/
theorem toV2_withV_BQ2 (h : BoundaryStrategyRefinesV3_BQ2 T (U.withV_BQ2 VF hVF)) :
    BoundaryStrategyRefinesV2_BQ T U where
  ϑUp_le := h.ϑUp_le
  shortUp_le := h.shortUp_le
  bcgUp_le := h.bcgUp_le
  interior_refines := fun ϑ sh bc =>
    have hi := h.interior_refines ϑ sh bc
    { Nb_eq := hi.Nb_eq, cw_eq := hi.cw_eq, I₁_eq := hi.I₁_eq, LmaxLow_eq := hi.LmaxLow_eq
      endpointUp_eq := hi.endpointUp_eq, circleUp_le := hi.circleUp_le, lc18_le := hi.lc18_le
      β₂Up_le := hi.β₂Up_le, ΔLow_ge := hi.ΔLow_ge, errorsUp_le := hi.errorsUp_le
      sectionUp_le := hi.sectionUp_le, lfr29W_le := hi.lfr29W_le, σcolUp_le := hi.σcolUp_le
      scaleUp_le := hi.scaleUp_le, wUp_le := hi.wUp_le, splitUp_le := hi.splitUp_le
      β₁Up_le := hi.β₁Up_le, T₀Low_ge := hi.T₀Low_ge, tailLow_ge := hi.tailLow_ge }
  cuspUp_le := h.cuspUp_le
  cuspRadii_ge := h.cuspRadii_ge
  productUp_le := h.productUp_le
  tailLow_ge := h.tailLow_ge
  fixed_subset := h.fixed_subset

end BoundaryStrategyRefinesV3_BQ2

/-- **The validity bridge through the producer's `V`** (review 54 §6.2–§6.3): for the SAME early
data, a strategy refining `U.withV_BQ2 VF` is valid when `U` is. -/
theorem PartialBoundaryThresholdValidityV3_BQ2.of_withV_refines_BQ2 {K : ℕ} {D : BoundaryEarlyData}
    {T U : BoundaryThresholdsV2 D}
    {VF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
      ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ → ℝ}
    {hVF : ∀ st ci ex er sc b β₁ T₀, T₀ ≤ VF st ci ex er sc b β₁ T₀}
    (hv : PartialBoundaryThresholdValidityV3_BQ2 K D U)
    (h : BoundaryStrategyRefinesV3_BQ2 T (U.withV_BQ2 VF hVF)) :
    PartialBoundaryThresholdValidityV3_BQ2 K D T :=
  hv.of_refines_BQ2 h.toV2_withV_BQ2

/-! ### The per-sequence family with the stage order explicit -/

/-- **The per-sequence boundary family at one register, stage order explicit** (PARTIAL: universe
lift and LPA02's joint witness not included): positivity `0 < εr < 1/4`, `εr < ε₀`, `0 < δ'`,
`0 < Λz`, `20Λz ≤ T₀Low` (the order `Λz` before `T₀`), `0 < δ < δ'`, and T3B-R's per-member
conclusion on every member `n ≥ R.tail` of the sequence at `D.δStar` (ratio `δ_{n+1}`, BCP04.a
index `n + 1`) at the register's values, `V = R.later.split.V`, cusp requests `R.cuspQuality`. -/
def PartialBoundaryFamilyOnSeqV3_BQ2 (K : ℕ) (A : ℝ → ℝ) {D : BoundaryEarlyData}
    (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
    (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio D.δStar (n + 1)))
    {T : BoundaryThresholdsV2 D} (R : BoundaryRegisterV2 D T) (εr δ' Λz δ : ℝ) : Prop :=
  0 < εr ∧ εr < 1 / 4 ∧ εr < R.later.err.co.ε₀ ∧ 0 < δ' ∧ 0 < Λz ∧
    20 * Λz ≤ (T.toClosed R.ϑ R.shortErr R.bcgErr).T₀Low R.stage R.later.circle R.later.excl
      R.later.err R.later.scale R.later.split.b R.later.split.β₁ ∧
    0 < δ ∧ δ < δ' ∧ ∀ n : ℕ, R.tail ≤ n →
      BoundaryPacketsOutBFR_BQ (W n) (g n) K A (boundaryCounterexampleRatio D.δStar (n + 1)) (B n)
        ((n + 1 : ℕ) : ℝ) R.later.scale.Λ R.later.scale.w
        (closedβV3 R.later.split.β₁ R.later.excl) R.later.excl.Δ R.later.err.co.qs
        R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s R.later.err.wk.b'
        R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc R.later.Lmax
        R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
        R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz R.cuspQuality R.cuspQuality

/-- **The per-sequence boundary family on every register at `T`, witnesses from the producer's
outputs** (PARTIAL): `εr, δ', Λz` at the register's prefix, `δ` at the prefix and `T₀`. -/
def PartialBoundaryFamilyAtSeqV3_BQ2 (K : ℕ) (A : ℝ → ℝ) {D : BoundaryEarlyData}
    (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
    (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio D.δStar (n + 1)))
    (T : BoundaryThresholdsV2 D) (P : BoundaryProducerOutputs_BQ2 D) : Prop :=
  ∀ R : BoundaryRegisterV2 D T,
    PartialBoundaryFamilyOnSeqV3_BQ2 K A W g B R
      (P.εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
        R.later.split.β₁)
      (P.δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
        R.later.split.β₁)
      (P.ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
        R.later.split.β₁)
      (P.δF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
        R.later.split.β₁ R.later.split.T₀)

namespace PartialBoundaryFamilyOnSeqV3_BQ2

variable {K : ℕ} {A : ℝ → ℝ} {D : BoundaryEarlyData} {W : ℕ → CompactCarrier.{0}}
  [∀ n, ConnectedSpace (W n).Carrier] {g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier}
  {B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio D.δStar (n + 1))}
  {T : BoundaryThresholdsV2 D} {R : BoundaryRegisterV2 D T} {εr δ' Λz δ : ℝ}

/-- **Consumer (order)**: `20 Λz ≤ T₀` at the register. -/
theorem twenty_Λz_le_T₀_BQ2 (h : PartialBoundaryFamilyOnSeqV3_BQ2 K A W g B R εr δ' Λz δ) :
    20 * Λz ≤ R.later.split.T₀ := by
  obtain ⟨-, -, -, -, -, hT, -⟩ := h
  exact hT.trans ((le_max_right _ _).trans R.later.T₀_ge)

/-- **Consumer**: forgetting the explicit `δ` gives FC39-BQ's record (cusp requests
`R.cuspQuality`). -/
theorem toOnSeqV2_BQ2 (h : PartialBoundaryFamilyOnSeqV3_BQ2 K A W g B R εr δ' Λz δ) :
    PartialBoundaryFamilyOnSeqV2_BQ K A W g B R R.cuspQuality R.cuspQuality εr δ' Λz := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, δ, h7, h8, h9⟩

end PartialBoundaryFamilyOnSeqV3_BQ2

namespace PartialBoundaryFamilyAtSeqV3_BQ2

variable {K : ℕ} {A : ℝ → ℝ} {D : BoundaryEarlyData} {W : ℕ → CompactCarrier.{0}}
  [∀ n, ConnectedSpace (W n).Carrier] {g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier}
  {B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio D.δStar (n + 1))}
  {T : BoundaryThresholdsV2 D} {P : BoundaryProducerOutputs_BQ2 D}

/-- **Consumer**: the V3 record implies FC39-BQ's tied record on the same sequence. -/
theorem toTied_BQ2 (h : PartialBoundaryFamilyAtSeqV3_BQ2 K A W g B T P) :
    PartialBoundaryFamilyAtSeqTied_BQ K A W g B T :=
  ⟨P.εrF, P.δ'F, P.ΛzF, fun R => (h R).toOnSeqV2_BQ2⟩

/-- **Consumer (wrapper (6) shape)**: at every register one tail `N ≥ R.tail`, with `δ` the
producer's output at the register's prefix and `T₀`, positive and below `δ'`, and T3B-R's
conclusion on every member `n ≥ N`. -/
theorem exists_tail_BQ2 (h : PartialBoundaryFamilyAtSeqV3_BQ2 K A W g B T P)
    (R : BoundaryRegisterV2 D T) :
    ∃ N : ℕ, R.tail ≤ N ∧
      0 < P.δF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
        R.later.split.β₁ R.later.split.T₀ ∧ ∀ n : ℕ, N ≤ n →
      ∃ Pk : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio D.δStar (n + 1))
        (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) R.cuspQuality
          R.cuspQuality), Pk.cusp = B n := by
  obtain ⟨-, -, -, -, -, -, hδ, -, hn⟩ := h R
  exact ⟨R.tail, le_rfl, hδ, fun n hN => by
    obtain ⟨Pk, hPk, -⟩ := hn n hN
    exact ⟨Pk, hPk⟩⟩

end PartialBoundaryFamilyAtSeqV3_BQ2

end DifferentialGeometry.Geometry.Collapse
