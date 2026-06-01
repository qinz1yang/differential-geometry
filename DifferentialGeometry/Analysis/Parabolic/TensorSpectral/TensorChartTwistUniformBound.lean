import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerLowerBound
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Uniform operator-norm bounds on the chart `(r, s)`-tensor twist over a compact base set

For a smooth manifold `M` modelled on `(E, H)` with model `I`, and a fixed base
point `α : M`, this file proves pointwise operator-norm bounds on the chart
`(r, s)`-tensor twist `chartRSTwist α b r s` and its inverse
`chartRSTwistInv α b r s`, viewed as continuous linear maps on
`TensorRSModel r s ℝ E`, in terms of the operator norms of `chartJ`/`chartJinv`
at the base point `b`.

## Strategy

The chart `(r, s)`-tensor twist `chartRSTwist α b r s T` is defined as the
composition `(post-compose with `chartJ α b` on `s` output slots) ∘ T ∘
(pre-compose with `chartJinv α b` on `r` input slots)`. Mathlib's
`norm_compContinuousLinearMap_le` gives, for each `α' : Tensor0SModel r ℝ E`:

* `‖α'.compCLM (chartJinv α b)‖ ≤ ‖α'‖ * ‖chartJinv α b‖^r`
* `‖T (α'.compCLM (chartJinv α b))‖ ≤ ‖T‖ * ‖α'.compCLM (chartJinv α b)‖`
* `‖(T (α'.compCLM (chartJinv α b))).compCLM (chartJ α b)‖
    ≤ ‖T (α'.compCLM (chartJinv α b))‖ * ‖chartJ α b‖^s`

Chaining these,
`‖chartRSTwist α b r s T α'‖ ≤ ‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖ * ‖α'‖`.
Hence `‖chartRSTwist α b r s T‖ ≤ ‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖`.

## Main results

* `chartRSTwist_opNorm_le` — pointwise op-norm bound on `chartRSTwist α b r s T`
  in terms of `‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖`.
* `chartRSTwistInv_opNorm_le` — analogous bound for the inverse twist.

Both bounds are predicate-free and require no Riemannian-metric structure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap ContinuousMultilinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

set_option linter.unusedSectionVars false in
/-- Pointwise operator-norm bound on `chartRSTwist α b r s T`, as a continuous
linear map `Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E`:
`‖chartRSTwist α b r s T‖ ≤ ‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖`. -/
lemma chartRSTwist_opNorm_le
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    ‖chartRSTwist (I := I) (M := M) α b r s T‖ ≤
      ‖chartJ (I := I) (M := M) α b‖ ^ s *
        ‖chartJinv (I := I) (M := M) α b‖ ^ r * ‖T‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · have : (0 : ℝ) ≤ ‖chartJ (I := I) (M := M) α b‖ ^ s *
        ‖chartJinv (I := I) (M := M) α b‖ ^ r * ‖T‖ := by positivity
    exact this
  intro α'
  rw [chartRSTwist_apply]
  have hA :
      ‖α'.compContinuousLinearMap
          (fun _ : Fin r => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      α' (fun _ : Fin r => chartJinv (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  set u : Tensor0SModel r ℝ E :=
    α'.compContinuousLinearMap
      (fun _ : Fin r => chartJinv (I := I) (M := M) α b) with hu_def
  have hB : ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
  have hC :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖ ≤
        ‖T u‖ * ‖chartJ (I := I) (M := M) α b‖ ^ s := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (T u) (fun _ : Fin s => chartJ (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hCsorted :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖ ≤
        ‖chartJ (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by
    calc
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖
          ≤ ‖T u‖ * ‖chartJ (I := I) (M := M) α b‖ ^ s := hC
      _ = ‖chartJ (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by ring
  have h_pow_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ ^ s := by positivity
  have h_T_le : ‖T u‖ ≤ ‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r) := by
    calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := hB
      _ ≤ ‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r) := by
            have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_left hA h_T_nn
  have h_combined :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖ ≤
        ‖chartJ (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r)) :=
    hCsorted.trans <| mul_le_mul_of_nonneg_left h_T_le h_pow_nn
  have h_final :
      ‖chartJ (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r)) =
        ‖chartJ (I := I) (M := M) α b‖ ^ s *
          ‖chartJinv (I := I) (M := M) α b‖ ^ r * ‖T‖ * ‖α'‖ := by ring
  rw [h_final] at h_combined
  exact h_combined

set_option linter.unusedSectionVars false in
/-- Pointwise operator-norm bound on `chartRSTwistInv α b r s T`:
`‖chartRSTwistInv α b r s T‖ ≤ ‖chartJinv α b‖^s * ‖chartJ α b‖^r * ‖T‖`. -/
lemma chartRSTwistInv_opNorm_le
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    ‖chartRSTwistInv (I := I) (M := M) α b r s T‖ ≤
      ‖chartJinv (I := I) (M := M) α b‖ ^ s *
        ‖chartJ (I := I) (M := M) α b‖ ^ r * ‖T‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · have : (0 : ℝ) ≤ ‖chartJinv (I := I) (M := M) α b‖ ^ s *
        ‖chartJ (I := I) (M := M) α b‖ ^ r * ‖T‖ := by positivity
    exact this
  intro α'
  rw [chartRSTwistInv_apply]
  have hA :
      ‖α'.compContinuousLinearMap
          (fun _ : Fin r => chartJ (I := I) (M := M) α b)‖ ≤
        ‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      α' (fun _ : Fin r => chartJ (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  set u : Tensor0SModel r ℝ E :=
    α'.compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b) with hu_def
  have hB : ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
  have hC :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖T u‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ s := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (T u) (fun _ : Fin s => chartJinv (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hCsorted :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖chartJinv (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by
    calc
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖
          ≤ ‖T u‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ s := hC
      _ = ‖chartJinv (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by ring
  have h_pow_nn : 0 ≤ ‖chartJinv (I := I) (M := M) α b‖ ^ s := by positivity
  have h_T_le : ‖T u‖ ≤ ‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r) := by
    calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := hB
      _ ≤ ‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r) := by
            have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_left hA h_T_nn
  have h_combined :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r)) :=
    hCsorted.trans <| mul_le_mul_of_nonneg_left h_T_le h_pow_nn
  have h_final :
      ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r)) =
        ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          ‖chartJ (I := I) (M := M) α b‖ ^ r * ‖T‖ * ‖α'‖ := by ring
  rw [h_final] at h_combined
  exact h_combined

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
