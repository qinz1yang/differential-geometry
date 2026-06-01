import DifferentialGeometry.Integral.Connection.TensorRSIntrinsicChartCLMOpNorm
import DifferentialGeometry.Integral.Connection.SlotChristoffelCorrectionOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartLeviCivitaParallelCLMOpNorm

/-!
# Pointwise op-norm bound for `chartTensorRSCovariantDerivative`

The chart-frame covariant derivative
`chartTensorRSCovariantDerivative r s g α T X b ∈ TensorRSSpace r s I b`
is, by definition, the difference of three pieces:

* the intrinsic Fréchet-derivative piece
  `tensorRSIntrinsicChartCLM r s α T b (X b)`,
* the sum over upper slots `k : Fin r` of
  `chartTensorRSInputSlotCorrection r s g α T X b k`,
* the sum over lower slots `l : Fin s` of
  `chartTensorRSOutputSlotCorrection r s g α T X b l`.

The triangle inequality together with the previously shipped op-norm bounds
delivers a uniform pointwise bound of the form

  `‖chartTensorRSCovariantDerivative r s g α T X b‖ ≤
      C * (max (1 + ‖X b‖) 1) ^ (max r s) *
        (‖fderiv ℝ (chart-pulled repr of T) (extChartAt I α b)‖ * ‖X b‖
         + ‖T b‖)`

valid for every `b` in the closed support of the canonical chart-atlas
partition-of-unity weight at `α`. The constant `C` depends only on the chart
at `α`, the locality hypothesis, and the metric `g`; it is independent of
`T`, `X`, and `b`. The polynomial factor `(max (1+‖X b‖) 1) ^ (max r s)`
absorbs the slot-Christoffel product.

## Strategy

1. Triangle inequality on the three-term decomposition.
2. The intrinsic piece is bounded by
   `C_I * ‖fderiv ℝ (chart-pulled repr of T) (extChartAt I α b)‖ * ‖X b‖`
   via `tensorRSIntrinsicChartCLM_opNorm_isBounded_on_compact`.
3. Each slot correction is bounded by
   `(max ‖chartLeviCivitaParallelCLM g α b X‖ 1) ^ n * ‖T b‖`
   pointwise (`chartTensorRSInputSlotCorrection_opNorm_le`,
   `chartTensorRSOutputSlotCorrection_opNorm_le`).
4. The slot CLM op-norm itself is bounded by `C_LC * ‖X b‖` on the POU
   tsupport via `chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport`,
   so `(max ‖Φ‖ 1) ^ n ≤ ((max C_LC 1 + 1) * (1 + ‖X b‖)) ^ n`.
5. Combining yields the headline bound. The `‖X b‖`-polynomial absorbs into
   the polynomial factor `(max (1+‖X b‖) 1) ^ (max r s)`.

Note: the slot bound is `O(‖T b‖)`, not `O(‖T b‖ · ‖X b‖)`. The factor
`max ‖Φ‖ 1 ≥ 1` retains a constant term even when `X = 0`. The headline
RHS therefore presents the natural decomposition
`(Fréchet derivative term) · ‖X b‖ + (slot Christoffel term)`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Core slot-Christoffel bound: `max ‖Φ‖ 1 ≤ (max C_LC 1 + 1) * (1 + ‖X b‖)`,
valid whenever `‖Φ‖ ≤ C_LC * ‖X b‖` and `C_LC, ‖X b‖ ≥ 0`. -/
private lemma slot_factor_le_const_mul_one_plus_X
    {Φ_norm : ℝ}
    {C_LC X_b_norm : ℝ} (_hC_LC_nn : 0 ≤ C_LC) (hX_nn : 0 ≤ X_b_norm)
    (hΦ : Φ_norm ≤ C_LC * X_b_norm) :
    max Φ_norm 1 ≤ (max C_LC 1 + 1) * (1 + X_b_norm) := by
  have hmaxC_nn : 0 ≤ max C_LC 1 := le_trans zero_le_one (le_max_right _ _)
  have hmaxC_ge_one : (1 : ℝ) ≤ max C_LC 1 := le_max_right _ _
  have h_1X_nn : (0 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_1X_ge_one : (1 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_Φ_le_step :
      Φ_norm ≤ max C_LC 1 * (1 + X_b_norm) := by
    have h_a : C_LC * X_b_norm ≤ max C_LC 1 * X_b_norm :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX_nn
    have h_b : max C_LC 1 * X_b_norm ≤ max C_LC 1 * (1 + X_b_norm) := by
      have : X_b_norm ≤ 1 + X_b_norm := by linarith
      exact mul_le_mul_of_nonneg_left this hmaxC_nn
    linarith
  have h_one_le_step :
      (1 : ℝ) ≤ max C_LC 1 * (1 + X_b_norm) := by
    have h_a : (1 : ℝ) * 1 ≤ max C_LC 1 * (1 + X_b_norm) :=
      mul_le_mul hmaxC_ge_one h_1X_ge_one (by norm_num) hmaxC_nn
    linarith
  have h_max_step : max Φ_norm 1 ≤ max C_LC 1 * (1 + X_b_norm) :=
    max_le h_Φ_le_step h_one_le_step
  have h_expand : max C_LC 1 * (1 + X_b_norm) ≤
      (max C_LC 1 + 1) * (1 + X_b_norm) := by
    have h1 : max C_LC 1 ≤ max C_LC 1 + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h1 h_1X_nn
  linarith

/-- Raise the previous bound to the `n`-th power and split the product. -/
private lemma slot_factor_pow_le_const_mul_one_plus_X_pow (n : ℕ)
    {Φ_norm : ℝ}
    {C_LC X_b_norm : ℝ} (hC_LC_nn : 0 ≤ C_LC) (hX_nn : 0 ≤ X_b_norm)
    (hΦ : Φ_norm ≤ C_LC * X_b_norm) :
    (max Φ_norm 1) ^ n ≤
      (max C_LC 1 + 1) ^ n * (1 + X_b_norm) ^ n := by
  have h_max_nn : 0 ≤ max Φ_norm 1 := le_trans zero_le_one (le_max_right _ _)
  have h_step :=
    slot_factor_le_const_mul_one_plus_X (Φ_norm := Φ_norm)
      (C_LC := C_LC) (X_b_norm := X_b_norm) hC_LC_nn hX_nn hΦ
  have h_pow :
      (max Φ_norm 1) ^ n ≤ ((max C_LC 1 + 1) * (1 + X_b_norm)) ^ n :=
    pow_le_pow_left₀ h_max_nn h_step n
  rw [mul_pow] at h_pow
  exact h_pow

/-- Monotonic absorption of `(1 + X_b_norm) ^ n` into `(max (1+X_b_norm) 1) ^ N`
when `n ≤ N`. -/
private lemma one_plus_X_pow_le_max_pow
    {X_b_norm : ℝ} (hX_nn : 0 ≤ X_b_norm) {n N : ℕ} (hn : n ≤ N) :
    (1 + X_b_norm) ^ n ≤ (max (1 + X_b_norm) 1) ^ N := by
  have h_1X_nn : (0 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_1X_le_max : (1 + X_b_norm) ≤ max (1 + X_b_norm) 1 := le_max_left _ _
  have h_max_ge_one : (1 : ℝ) ≤ max (1 + X_b_norm) 1 := by
    have h_1X_ge_one : (1 : ℝ) ≤ 1 + X_b_norm := by linarith
    exact le_trans h_1X_ge_one h_1X_le_max
  have h_step1 :
      (1 + X_b_norm) ^ n ≤ (max (1 + X_b_norm) 1) ^ n :=
    pow_le_pow_left₀ h_1X_nn h_1X_le_max n
  have h_step2 :
      (max (1 + X_b_norm) 1) ^ n ≤ (max (1 + X_b_norm) 1) ^ N :=
    pow_le_pow_right₀ h_max_ge_one hn
  linarith

/-- Monotonic absorption of `(max C_LC 1 + 1) ^ n` into `(max C_LC 1 + 1) ^ N`
when `n ≤ N`. -/
private lemma const_pow_le_max_pow
    {C_LC : ℝ} (_hC_LC_nn : 0 ≤ C_LC) {n N : ℕ} (hn : n ≤ N) :
    (max C_LC 1 + 1) ^ n ≤ (max C_LC 1 + 1) ^ N := by
  have h_one_le : (1 : ℝ) ≤ max C_LC 1 + 1 := by
    have : (1 : ℝ) ≤ max C_LC 1 := le_max_right _ _
    linarith
  exact pow_le_pow_right₀ h_one_le hn

end Connection
end Integral
end DifferentialGeometry

end
