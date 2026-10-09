import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainNumerics74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdpE
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFc33Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp02RowEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp03RowEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactApplicationsEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroDomainsFc35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc36Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc37Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38Row

/-!
# The register-level numerics of tonight's rows at `ClosedChainEZRowsSource_RGC`

Lane S-REG-NUM (`_RNUM`), G3 (D74-18). Rows delivered tonight carry their numeric premises as
explicit hypotheses (D74-18: the assembler is qualitative; numerics stay in the register layer).
They are ALL values read before the member, so the rows hold on the closed rows' source with NO
numeric hypothesis left, given the record `N` of G1 (`strategy_below`, `nb_eq`, `cw_eq`, `eps_lt`,
`qe_le`, `gamma_*`, `e_le`) and PR10's `K ≥ 10`.

## Audit table: row → premise → choice node → supplier

* EDP02 (`edp02_row_EDP23`): `Δ ≥ 2` ← PR13 `Δ > 10⁶` (`two_le_Δ_EDP23`).
* EDP03 whole row (`edp03_row_EDP23`; also FC37's `fc37_row_FCW`, the same twelve): `Δ ≥ 2`; `c₃ <
  10⁻⁵` ← early `c₃` bound (`c_two_bounds_RGC`); `hϑ` (`C_ρΛΔ < 10⁻⁶`) ← PR19 `regScale_Cρ`
  (`chain_scale_small_RGC`, needs PR10's `N_b, c_w` equalities); `0 ≤ ε`, `ε < 1` ← PR14 and the
  scale budget (`eps_lt_RGC`); `μ, τ ≤ 10⁻⁸` ← PR18 `μ_lt`, `τ_lt`; **`σ_c ≤ 1/1000`** ← PR14 slot
  `qe_lt` (`q_e < θ_e²/10⁸`, `θ_e < 1/100`: `qe_le_thousandth_RNUM`); **`b·1000Δ ≤ 1`** ← LFR29.1's
  cap (`b < 10⁻⁵ b'`, `b' < 1/(10⁶Δ)`: `b_mul_le_RNUM`); `0 < γ_c ≤ 1/100`, `β_c ≤ 10⁻⁵` ← TCP01's
  Gram cap in `circleUp` and `3β_c < β₂ < 10⁻⁶` (`collar_le_RGC`).
* FC33 (`fc33_row_BAS`): no numeric premise (`c₃ < c_adjust` is a field of the chain).
* FC35 / ZSP02 (`fc35_row_RWS`, `zsp02_row_strong_ZSP35`): `ε_r < 1/2` ← FAMZ; `e ≤ 1/1000` ← PR14
  `e₀_lt` (fields of `N`).
* FC36 / ZSP04–ZSP05 (`fc36_row_FCW`, `zsp0405_row_ZSP35`): `ε_r < 1/2`, `K ≥ 5` ← `K ≥ 10`.
* FC38 (`fc38_row_FCW`): `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`, `0 ≤ γ ≤ 3/4` ← Gram request
  (`gram_request_of_below_V4C`); `ε_r < 1/2`, `σ_c ≤ 1/2` ← fields of `N`.

* `ClosedRegisterV4.qe_le_thousandth_RNUM`, `b_mul_le_RNUM`, `beta_two_le_RNUM`,
  `gamma_add_beta_lt_RNUM`: the four register facts not already in the tree;
* `ClosedChainEZRowsSource_RGC.{edp02, edp03, fc35, fc36, fc37, fc38, zsp0405}_row_RNUM`: each row
  on the source, no numeric hypothesis other than `N` (and `5 ≤ K` for FC36);
NOT here: a single production-path theorem over the register tail carrying the `type_of%` rows (each
attempt exhausts the heartbeats of the declaration in the statement / `obtain`; the S-level
consumers above combine with `register_yields_numerics_RNUM` by `obtain ⟨S, hS, ⟨N⟩⟩`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedRegisterV4

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}

/-- `σ_c = q_e ≤ 1/1000` at every register (PR14: `q_e < θ_e²/10⁸`, `θ_e < 1/100`). -/
theorem qe_le_thousandth_RNUM (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.later.err.co.qe ≤ 1 / 1000 := by
  have h1 : R.later.err.co.qe < R.later.circle.θe ^ 2 / 10 ^ 8 :=
    R.later.qe_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 := R.later.θe_lt_hundredth_VAL6
  have h3 := R.later.θe_pos
  have h4 : R.later.circle.θe ^ 2 / 10 ^ 8 ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- `b · (1000 Δ) ≤ 1` at a register below the complete strategy (LFR29.1's cap:
`b < 10⁻⁵ b'`, `b' < W(Δ, τ) ≤ 1/(10⁶ Δ)`). -/
theorem b_mul_le_RNUM
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.later.split.b * (1000 * R.later.excl.Δ) ≤ 1 := by
  obtain ⟨-, hlf, -, -⟩ := hT.complete_caps_V4C
  obtain ⟨⟨-, hb'W, -, -⟩, -, -, -, hb⟩ := R.lfr29_numeric_of_below_V4C hlf
  have hΔ := R.later.Δ_pos_VAL6
  have hW : lfr29WV4C R.later.excl.Δ R.later.err.bd.τ ≤ 1 / (10 ^ 6 * R.later.excl.Δ) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hb1 : R.later.split.b < 1 / 10 ^ 5 * R.later.err.wk.b' :=
    hb.trans_le (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _))
      (by norm_num))
  have hb2 : R.later.split.b < 1 / 10 ^ 5 * (1 / (10 ^ 6 * R.later.excl.Δ)) :=
    hb1.trans_le (mul_le_mul_of_nonneg_left (hb'W.le.trans hW) (by norm_num))
  have e : 1 / 10 ^ 5 * (1 / (10 ^ 6 * R.later.excl.Δ)) * (1000 * R.later.excl.Δ) =
      1 / 10 ^ 8 := by
    field_simp
    norm_num
  have h := mul_lt_mul_of_pos_right hb2 (by positivity : 0 < 1000 * R.later.excl.Δ)
  rw [e] at h
  linarith

/-- `β₂ ≤ 10⁻⁷` at a register below the complete strategy (Gram request). -/
theorem beta_two_le_RNUM
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) : R.β 2 ≤ 1 / 10000000 := by
  obtain ⟨-, -, hgram, -⟩ := hT.complete_caps_V4C
  obtain ⟨-, -, -, h⟩ := R.gram_request_of_below_V4C hgram
  norm_num at h ⊢
  exact h

/-- `γ + β₂ < 1/10` at a register below the complete strategy (Gram request). -/
theorem gamma_add_beta_lt_RNUM
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.later.circle.γ + R.β 2 < 1 / 10 := by
  obtain ⟨-, -, hgram, -⟩ := hT.complete_caps_V4C
  obtain ⟨hγ0, hγ1, h2, -⟩ := R.gram_request_of_below_V4C hgram
  linarith

end ClosedRegisterV4

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz}

/-- **EDP02's row on the source** (`Δ ≥ 2` from the register). -/
theorem edp02_row_RNUM (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    type_of% (S.chain.toGaf02ChainE.edp02_row_EDP23 R.two_le_Δ_EDP23) :=
  S.chain.toGaf02ChainE.edp02_row_EDP23 R.two_le_Δ_EDP23

/-- **EDP03's whole row on the source**: all twelve premises (the nine numeric ones among them)
are register facts; `N` supplies the strategy and PR10's equalities. -/
theorem edp03_row_RNUM (N : ClosedRowsNumericsAt74 S) :
    type_of% (S.chain.toGaf02ChainE.edp03_row_EDP23 R.two_le_Δ_EDP23
      R.stage.c_two_bounds_RGC.2.2.1 (R.chain_scale_small_RGC N.nb_eq N.cw_eq) R.later.ε_pos.le
      (R.eps_lt_RGC N.strategy_below).2 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
      R.qe_le_thousandth_RNUM (R.b_mul_le_RNUM N.strategy_below)
      (R.collar_le_RGC N.strategy_below).1 (R.collar_le_RGC N.strategy_below).2.1.le
      (R.collar_le_RGC N.strategy_below).2.2.le) :=
  S.chain.toGaf02ChainE.edp03_row_EDP23 R.two_le_Δ_EDP23
    R.stage.c_two_bounds_RGC.2.2.1 (R.chain_scale_small_RGC N.nb_eq N.cw_eq) R.later.ε_pos.le
    (R.eps_lt_RGC N.strategy_below).2 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
    R.qe_le_thousandth_RNUM (R.b_mul_le_RNUM N.strategy_below)
    (R.collar_le_RGC N.strategy_below).1 (R.collar_le_RGC N.strategy_below).2.1.le
    (R.collar_le_RGC N.strategy_below).2.2.le

/-- **FC37's row on the source** (EDP-E's nine premises, `Δ ≥ 2`, `σ_c ≤ 1/1000`,
`b·1000Δ ≤ 1`, all register facts). -/
theorem fc37_row_RNUM (N : ClosedRowsNumericsAt74 S) :
    type_of% (S.chain.fc37_row_FCW R.two_le_Δ_EDP23
      R.stage.c_two_bounds_RGC.2.2.1 (R.chain_scale_small_RGC N.nb_eq N.cw_eq) R.later.ε_pos.le
      (R.eps_lt_RGC N.strategy_below).2 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
      R.qe_le_thousandth_RNUM (R.b_mul_le_RNUM N.strategy_below)
      (R.collar_le_RGC N.strategy_below).1 (R.collar_le_RGC N.strategy_below).2.1.le
      (R.collar_le_RGC N.strategy_below).2.2.le) :=
  S.chain.fc37_row_FCW R.two_le_Δ_EDP23
    R.stage.c_two_bounds_RGC.2.2.1 (R.chain_scale_small_RGC N.nb_eq N.cw_eq) R.later.ε_pos.le
    (R.eps_lt_RGC N.strategy_below).2 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
    R.qe_le_thousandth_RNUM (R.b_mul_le_RNUM N.strategy_below)
    (R.collar_le_RGC N.strategy_below).1 (R.collar_le_RGC N.strategy_below).2.1.le
    (R.collar_le_RGC N.strategy_below).2.2.le

/-- **FC38's row on the source** (Gram request and the fields of `N`). -/
theorem fc38_row_RNUM (N : ClosedRowsNumericsAt74 S) :
    type_of% (S.chain.fc38_row_FCW (R.beta_two_le_RNUM N.strategy_below)
      (R.gamma_add_beta_lt_RNUM N.strategy_below) N.eps_lt N.qe_le N.gamma_nonneg N.gamma_le) :=
  S.chain.fc38_row_FCW (R.beta_two_le_RNUM N.strategy_below)
    (R.gamma_add_beta_lt_RNUM N.strategy_below) N.eps_lt N.qe_le N.gamma_nonneg N.gamma_le

/-- **FC36's row on the source** (`ε_r < 1/2` from `N`, `K ≥ 5` from `K ≥ 10`). -/
theorem fc36_row_RNUM (N : ClosedRowsNumericsAt74 S) (hK : 5 ≤ K) :
    type_of% (S.chain.fc36_row_FCW N.eps_lt hK) :=
  S.chain.fc36_row_FCW N.eps_lt hK

/-- **FC35's row on the source** (`ε_r < 1/2`, `e ≤ 1/1000`: fields of `N`), at every zero index. -/
theorem fc35_row_RNUM (N : ClosedRowsNumericsAt74 S) :
    ∀ k, type_of% (S.chain.toGaf02ChainE.fc35_row_RWS N.eps_lt N.e_le k) := fun k =>
  S.chain.toGaf02ChainE.fc35_row_RWS N.eps_lt N.e_le k

/-- **ZSP04–ZSP05's row on the source** (`ε_r < 1/2`: a field of `N`). -/
theorem zsp0405_row_RNUM (N : ClosedRowsNumericsAt74 S) :
    type_of% (S.chain.zsp0405_row_ZSP35 N.eps_lt) :=
  S.chain.zsp0405_row_ZSP35 N.eps_lt

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
