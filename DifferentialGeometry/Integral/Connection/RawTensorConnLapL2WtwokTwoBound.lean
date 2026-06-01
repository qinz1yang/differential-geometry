import DifferentialGeometry.Integral.Connection.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Integral.Connection.IteratedFDerivTensorReprChartCompBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartTargetSqBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartL2PouBridge
import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.FderivToWkpNormBridge
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedFderivToWkpNormBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartTransition
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound

/-!
# Order-zero bound: chart-target POU-weighted L² of the chart-pulled
# tensor representation by the sum of chart-component L² norms

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, and a
chart base point `α : M`, this file ships a uniform bound for the
chart-α-target partition-of-unity-weighted L² norm-squared of the chart-pulled
model-fibre representation `tensorRSChartE_section_repr r s α T.toSection ∘
(extChartAt I α).symm ∘ toEuclidean.symm` of a smooth compactly-supported
`(r, s)`-tensor section `T`, in terms of the L² (= `wkpNorm 0 2`) norms of the
chart-frame scalar components `tensorChartComp g r s T α Idx Jdx` over the
chart-target image `chartTargetEuclid α`.

Concretely:

```
∫⁻ y in chartTargetEuclid α,
    ENNReal.ofReal (POU(symm y)² · ‖repr T (symm y)‖²) dvol ≤
  ENNReal.ofReal K *
    ∑ Idx, Σ Jdx,
      (wkpNorm 0 2 (tensorChartComp g r s T α Idx Jdx) (chartTargetEuclid α))²
```

with `K = (cardinality of (Idx, Jdx)) · basisNormConstant²` depending only on
`(g, r, s)` and the model space; in particular `K` is independent of `T`.

## Strategy

1. Pointwise on `M`: `‖tensorRSChartE_section_repr r s α T.toSection b‖² ≤
   K_basis · Σ Idx Σ Jdx |tensorChartComponentRaw α Idx Jdx b|²` via
   `reprNorm_le_sum_components` squared (Cauchy-Schwarz finite sum).

2. Multiply both sides by `POU(b)²` and rewrite `POU(b)² · |raw α Idx Jdx b|² =
   |POU(b) · raw α Idx Jdx b|² = |tensorChartComponentPou α Idx Jdx b|²`.

3. Pull through `ENNReal.ofReal` (LHS argument is non-negative) and integrate
   over `chartTargetEuclid α`.

4. For `y ∈ chartTargetEuclid α`, `tensorChartComp α Idx Jdx y =
   tensorChartComponentPou α Idx Jdx ((extChartAt I α).symm (toEuclidean.symm y))`.

5. The integral `∫⁻ y in chartTargetEuclid α, ENNReal.ofReal (|tensorChartComp y|²) dvol`
   equals `(eLpNorm tensorChartComp 2 (volume.restrict (chartTargetEuclid α)))² =
   (wkpNorm 0 2 tensorChartComp (chartTargetEuclid α))²` via
   `eLpNorm_eq_lintegral_rpow_enorm_toReal` and `wkpNorm_zero`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Pointwise squared bound: the squared model-fibre norm of the
chart-α-trivialised representation of `T.toSection` is bounded by a uniform
constant `K_basis` times the finite double sum of the squares of the raw
chart-frame scalar components. The constant `K_basis` depends only on the
ranks `(r, s)` and the model space. -/
theorem reprNormSq_le_sum_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M) :
    ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  have h_lin := reprNorm_le_sum_components (I := I) (M := M) g r s T α b
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_rhs_rewrite : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          |tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b| * Bnorm) =
      (∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) * Bnorm := by
    rw [Finset.sum_mul, hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b| * Bnorm)]
  rw [hBnorm_def.symm] at h_lin
  rw [h_rhs_rewrite] at h_lin
  have h_sum_nn : 0 ≤ (∑ p ∈ V,
      |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_sq : ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ ^ 2 ≤
      ((∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) *
        Bnorm) ^ 2 := by
    have := mul_le_mul h_lin h_lin (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  have hCS : (∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p => |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by
      simp
    rw [show (∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b| ^ 2) =
        ∑ p ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2 from
      Finset.sum_congr rfl (fun _ _ => by rw [sq_abs]), h_sum_one] at hbase
    exact hbase
  set sumSq : ℝ := ∑ p ∈ V,
    (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2
  have h_sumSq_nn : 0 ≤ sumSq :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_combined : ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 * sumSq := by
    have h_sq_eq : ((∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) *
        Bnorm) ^ 2 = (∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    have h_bound : (∑ p ∈ V,
            |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
          Bnorm ^ 2 ≤ (V.card : ℝ) * sumSq * Bnorm ^ 2 := h_mul
    calc ‖tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) b‖ ^ 2
        ≤ (∑ p ∈ V,
            |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * sumSq * Bnorm ^ 2 := h_bound
      _ = (V.card : ℝ) * Bnorm ^ 2 * sumSq := by ring
  have h_sumSq_eq : sumSq = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
    change (∑ p ∈ V, _) = _
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2)]
  rw [h_sumSq_eq] at h_combined
  exact h_combined

/-- For a real-valued function `f` and a measure `μ`, the square of `eLpNorm f 2 μ`
equals the lintegral of `‖f x‖ₑ ^ 2`. -/
private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  classical
  have h_rpow : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
      (1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have h_two_toReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [h_rpow, h_two_toReal]
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hI_def
  have hI_eq : I = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr ?_
    intro x
    rw [show ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) from by norm_num,
      ENNReal.rpow_natCast]
  have h_step1 : (I ^ ((1 : ℝ) / 2)) ^ 2 = (I ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
  rw [h_step1]
  rw [← ENNReal.rpow_mul]
  have h_eq : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_eq, ENNReal.rpow_one, hI_eq]

/-- **Order-0 chart-target POU-weighted L² bound for the chart-pulled tensor
representation by the sum of chart-component L² norms.** For a smooth closed
Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, and a chart base point
`α : M`, there is a non-negative constant `K` (depending only on `(g, r, s)`
and the model space; independent of `T`) such that for every smooth
compactly-supported `(r, s)`-tensor section `T`, the chart-target Lebesgue
integral of the partition-of-unity-weighted squared model-fibre norm of the
chart-pulled representation of `T.toSection` is bounded by `K` times the
finite double sum of the squared `L²`-norms (= `wkpNorm 0 2`) of the
chart-frame scalar components `tensorChartComp g r s T α Idx Jdx` over the
chart target. -/
theorem chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm
                      ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                (wkpNorm (d := Module.finrank ℝ E) 0 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  set N : ℝ := (V.card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨N * Bnorm ^ 2, mul_nonneg hN_nn (sq_nonneg _), ?_⟩
  intro T
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) (sym y)‖ ^ 2) with hlhs_def
  set rhsIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2)
    with hrhs_def
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal (N * Bnorm ^ 2) *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rhsIntegrand Idx Jdx y := by
    intro y _hy
    set b : M := sym y
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) b
    set V_norm : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) b‖
    have hρ_nn : 0 ≤ ρ :=
      (chartAtlasPOU I M).nonneg α b
    have hV_norm_nn : 0 ≤ V_norm := norm_nonneg _
    have h_sq := reprNormSq_le_sum_components_sq (I := I) (M := M) g r s T α b
    have h_scaled : ρ ^ 2 * V_norm ^ 2 ≤ ρ ^ 2 *
        (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) :=
      mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
    have h_distrib : ρ ^ 2 *
        (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
        N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
      rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
          ρ ^ 2 * (∑ Idx, ∑ Jdx,
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [Finset.mul_sum]]
      ring
    rw [h_distrib] at h_scaled
    have hLHS_eq : lhsIntegrand y = ENNReal.ofReal (ρ ^ 2 * V_norm ^ 2) := by
      change ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (V_norm ^ 2) = _
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [hLHS_eq]
    have h_ennreal :
        ENNReal.ofReal (ρ ^ 2 * V_norm ^ 2) ≤
        ENNReal.ofReal (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) :=
      ENNReal.ofReal_le_ofReal h_scaled
    refine le_trans h_ennreal ?_
    rw [ENNReal.ofReal_mul (mul_nonneg hN_nn (sq_nonneg _))]
    have h_ofReal_double_sum :
        ENNReal.ofReal
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (ρ ^ 2 *
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg
          (fun Jdx _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Jdx _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [h_ofReal_double_sum]
    have h_sum_eq :
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (ρ ^ 2 *
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2)) =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y := by
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      change ENNReal.ofReal
          (ρ ^ 2 *
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
        ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2)
      have h_apply := tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx _hy
      rw [h_apply]
      have h_pou_eq : tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx b =
          ρ * tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
        unfold tensorChartComponentPou
        rfl
      rw [h_pou_eq]
      congr 1
      ring
    rw [h_sum_eq]
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal (N * Bnorm ^ 2) *
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  rhsIntegrand Idx Jdx y
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' (chartTargetEuclid_measurableSet (I := I) (M := M) α)
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  rw [show (fun y : EuclN =>
      ENNReal.ofReal (N * Bnorm ^ 2) *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rhsIntegrand Idx Jdx y) =
      (fun y : EuclN =>
        ENNReal.ofReal (N * Bnorm ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y) from rfl] at h_int_mono
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h_int_mono
  have h_rhsIntegrand_meas : ∀ Idx Jdx,
      Measurable (fun y : EuclN => rhsIntegrand Idx Jdx y) := by
    intro Idx Jdx
    refine ENNReal.measurable_ofReal.comp ?_
    refine (continuous_pow 2).measurable.comp ?_
    exact (tensorChartComp_continuous (I := I) (M := M) g r s T α Idx Jdx).measurable
  have h_int_double_sum :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y) ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rhsIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    rw [MeasureTheory.lintegral_finset_sum _
      (fun Idx _ => by
        exact Finset.measurable_sum _ (fun Jdx _ => h_rhsIntegrand_meas Idx Jdx))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact MeasureTheory.lintegral_finset_sum _
      (fun Jdx _ => h_rhsIntegrand_meas Idx Jdx)
  rw [h_int_double_sum] at h_int_mono
  have h_per_idx_jdx : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          rhsIntegrand Idx Jdx y ∂(volume : Measure EuclN) ≤
        (wkpNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    intro Idx Jdx
    have h_rhs_eq_enorm :
        (fun y : EuclN => rhsIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2) := by
      funext y
      change ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2) =
        ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
      rw [show ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2) =
          ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
      rw [show ENNReal.ofReal
          (‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ ^ 2) =
            (ENNReal.ofReal
              ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖) ^ 2 from
        ENNReal.ofReal_pow (norm_nonneg _) 2]
      rw [ofReal_norm_eq_enorm]
    rw [h_rhs_eq_enorm]
    have h_sq_eLp :=
      sq_eLpNorm_two_eq_lintegral_enorm_sq
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
    rw [show ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
            ∂(volume : Measure EuclN) =
          ∫⁻ y,
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
            ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) from rfl]
    rw [← h_sq_eLp]
    rw [show wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) =
          eLpNorm (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) from
      wkpNorm_zero (d := Module.finrank ℝ E) 2 _ _]
  refine le_trans h_int_mono ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  refine Finset.sum_le_sum (fun Idx _ => ?_)
  refine Finset.sum_le_sum (fun Jdx _ => ?_)
  exact h_per_idx_jdx Idx Jdx

/-- The chart-pushed POU weight: the EuclN-side function
`y ↦ POU(extChartAt.symm (toEuclidean.symm y))`, extended by `0` off
`chartTargetEuclid α`. -/
private noncomputable def chartPouEucl (α : M) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

private lemma chartPouEucl_apply_of_mem (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPouEucl (I := I) (M := M) α y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold chartPouEucl; exact if_pos hy

private lemma chartPouEucl_apply_of_notMem (α : M) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPouEucl (I := I) (M := M) α y = 0 := by
  classical
  unfold chartPouEucl; exact if_neg hy

/-- The chart-pushed POU weight is `ContDiff ℝ ∞` on EuclN. The proof mirrors
`tensorChartComponent_contMDiff`: inside chartTargetEuclid the formula gives
smoothness, and outside, the function vanishes on an open neighborhood. -/
private lemma chartPouEucl_contDiff (α : M) :
    ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hf_def
  have hf_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞ f :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_target : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_target
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target :
      y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hformula_smooth :
        ContDiffOn ℝ ∞
          (fun z : EuclN =>
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hscalar : ContDiffOn ℝ ∞
          (fun z : E => f ((extChartAt I α).symm z))
          (extChartAt I α).target :=
        DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hf_smooth
      have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
        ContinuousLinearEquiv.contDiff _
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
          (chartTargetEuclid (I := I) (M := M) α)
          (extChartAt I α).target := by
        intro z hz
        rcases hz with ⟨w, hw_target, hwz⟩
        have h_eq : (toEuclidean (E := E)).symm z = w := by
          rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun z : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (chartTargetEuclid (I := I) (M := M) α) y := hformula_smooth y hy_target
    have hformula_at : ContDiffAt ℝ ∞
        (fun z : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y :=
      hwithin.contDiffAt (hOpen.mem_nhds hy_target)
    refine hformula_at.congr_of_eventuallyEq ?_
    filter_upwards [hOpen.mem_nhds hy_target] with z hz
    exact (chartPouEucl_apply_of_mem (I := I) (M := M) α hz)
  · have hcarrier_subset_target :
        K ⊆ chartTargetEuclid (I := I) (M := M) α := by
      intro z hz_carrier
      rcases hz_carrier with ⟨w, ⟨x, hx_supp, hxw⟩, hwz⟩
      have hx_src : x ∈ (extChartAt I α).source := hsub_target hx_supp
      have hw_target : w ∈ (extChartAt I α).target := by
        rw [← hxw]; exact (extChartAt I α).map_source hx_src
      exact ⟨w, hw_target, hwz⟩
    have hy_off : y ∉ K := fun hy_in =>
      hy_target (hcarrier_subset_target hy_in)
    have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off] with z hz
    by_cases hz_target :
        z ∈ chartTargetEuclid (I := I) (M := M) α
    · obtain ⟨w, hw_target, hwz⟩ := hz_target
      have hz_target' :
          z ∈ chartTargetEuclid (I := I) (M := M) α := ⟨w, hw_target, hwz⟩
      have h_eq : (toEuclidean (E := E)).symm z = w := by
        rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [chartPouEucl_apply_of_mem (I := I) (M := M) α hz_target']
      by_contra hne_f
      apply hz
      have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈
          tsupport f := subset_tsupport _ hne_f
      rw [h_eq] at hin_supp
      have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      refine ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwz⟩
    · exact chartPouEucl_apply_of_notMem (I := I) (M := M) α hz_target

/-- The chart-pushed POU weight has compact support. -/
private lemma chartPouEucl_hasCompactSupport (α : M) :
    HasCompactSupport (chartPouEucl (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hf_def
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_target : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_target
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  apply HasCompactSupport.intro (K := K) hK_compact
  intro y hy_notK
  by_cases hy_target :
      y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨w, hw_target, hwy⟩ := hy_target
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    rw [chartPouEucl_apply_of_mem (I := I) (M := M) α
        ⟨w, hw_target, hwy⟩]
    by_contra hne_f
    apply hy_notK
    have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        tsupport f := subset_tsupport _ hne_f
    rw [h_eq] at hin_supp
    have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
      (extChartAt I α).right_inv hw_target
    refine ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwy⟩
  · exact chartPouEucl_apply_of_notMem (I := I) (M := M) α hy_target

/-- The Fréchet derivative of the chart-pushed POU weight is bounded on EuclN. -/
private lemma exists_chartPouEucl_fderiv_uniform_bound (α : M) :
    ∃ K_pou : ℝ, 0 ≤ K_pou ∧
      ∀ y : EuclN, ‖fderiv ℝ (chartPouEucl (I := I) (M := M) α) y‖ ≤ K_pou := by
  classical
  have hCD : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have hHCS : HasCompactSupport (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_hasCompactSupport (I := I) (M := M) α
  have h_fderiv_cont : Continuous (fun y : EuclN =>
      fderiv ℝ (chartPouEucl (I := I) (M := M) α) y) :=
    hCD.continuous_fderiv (by norm_num)
  have h_fderiv_compactSupport : HasCompactSupport (fun y : EuclN =>
      fderiv ℝ (chartPouEucl (I := I) (M := M) α) y) :=
    hHCS.fderiv ℝ
  obtain ⟨K_raw, hK_bound⟩ := h_fderiv_cont.bounded_above_of_compact_support
    h_fderiv_compactSupport
  refine ⟨max K_raw 0, le_max_right _ _, ?_⟩
  intro y
  exact le_trans (hK_bound y) (le_max_left _ _)

/-- The chart-pulled raw component is `ContDiffOn ℝ ∞` on the chart target. -/
private lemma tensorChartComponentRaw_symm_contDiffOn_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) := by
  classical
  have hsmooth_on := tensorChartComponentRaw_contMDiffOn_chart_source
    (I := I) (M := M) g r s T α Idx Jdx
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (chartAt H α).source := by
    intro e he_tgt
    have hsrc : (extChartAt I α).symm e ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target he_tgt
    rwa [extChartAt_source] at hsrc
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hsmooth_on.comp hsymm hmaps
  exact hcomp.contDiffOn

/-- The chart-pulled POU is `ContDiffOn ℝ ∞` on the chart target. -/
private lemma chartAtlasPOU_symm_contDiffOn_target (α : M) :
    ContDiffOn ℝ ∞
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) ((extChartAt I α).target) := by
  classical
  have hf_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  exact DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
    (I := I) α hf_smooth

/-- Differentiability of the chart-pulled POU function at any chart-target point. -/
private lemma chartAtlasPOU_symm_differentiableAt
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) e := by
  have hcd := chartAtlasPOU_symm_contDiffOn_target (I := I) (M := M) α
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hwithin : DifferentiableWithinAt ℝ
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) ((extChartAt I α).target) e :=
    (hcd _ he).differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open.mem_nhds he)

/-- Differentiability of the chart-pulled raw component at any chart-target point. -/
private lemma tensorChartComponentRaw_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e := by
  have hcd := tensorChartComponentRaw_symm_contDiffOn_target
    (I := I) (M := M) g r s T α Idx Jdx
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hwithin : DifferentiableWithinAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) e :=
    (hcd _ he).differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open.mem_nhds he)

/-- For `y ∈ chartTargetEuclid α`, the chart component on EuclN equals the
chart-pulled POU-weighted raw scalar on M, pulled back via `extChartAt.symm` and
`toEuclidean.symm`. -/
private lemma tensorChartComp_eq_pou_mul_raw_pulled
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx hy]
  unfold tensorChartComponentPou
  rfl

/-- For `e ∈ (extChartAt I α).target`, the chart component on EuclN evaluated at
`toEuclidean e` equals the chart-pulled POU-weighted raw scalar evaluated at the
manifold point. -/
private lemma tensorChartComp_toEuclidean_eq_pou_mul_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e) := by
  have hy : (toEuclidean (E := E)) e ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨e, he, rfl⟩
  have h_eq : (toEuclidean (E := E)).symm ((toEuclidean (E := E)) e) = e :=
    (toEuclidean (E := E)).symm_apply_apply e
  rw [tensorChartComp_eq_pou_mul_raw_pulled
    (I := I) (M := M) g r s T α Idx Jdx hy, h_eq]

/-- For `e ∈ (extChartAt I α).target`, the chart-pulled POU-weighted raw
component, expressed via the EuclN-side `tensorChartComp` and `toEuclidean`. -/
private lemma pou_mul_raw_eq_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e) =
      tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e) :=
  (tensorChartComp_toEuclidean_eq_pou_mul_raw
    (I := I) (M := M) g r s T α Idx Jdx he).symm

/-- For `e ∈ (extChartAt I α).target`, the chart-pulled POU function equals the
EuclN-side chartPouEucl at `toEuclidean e`. -/
private lemma chartPouEucl_toEuclidean_eq_pou_symm
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    chartPouEucl (I := I) (M := M) α ((toEuclidean (E := E)) e) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) := by
  have hy : (toEuclidean (E := E)) e ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨e, he, rfl⟩
  have h_eq : (toEuclidean (E := E)).symm ((toEuclidean (E := E)) e) = e :=
    (toEuclidean (E := E)).symm_apply_apply e
  rw [chartPouEucl_apply_of_mem (I := I) (M := M) α hy, h_eq]

/-- The pointwise pre-product identity, lifted from the chart-target to a
function-level eventual equality near a target point. -/
private lemma pou_mul_raw_symm_eventuallyEq_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (fun e' : E =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e') *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e'))
      =ᶠ[𝓝 e]
      (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e')) := by
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  filter_upwards [h_open.mem_nhds he] with e' he'
  exact pou_mul_raw_eq_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he'

/-- The pointwise pre-product fderiv identity, on the chart target. -/
private lemma fderiv_pou_mul_raw_symm_eq_fderiv_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      fderiv ℝ
        (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
          ((toEuclidean (E := E)) e')) e :=
  (pou_mul_raw_symm_eventuallyEq_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he).fderiv_eq

/-- The Fréchet derivative of `tensorChartComp ∘ toEuclidean` on E equals the
composition of the EuclN-side Fréchet derivative with `toEuclidean`. -/
private lemma fderiv_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (e : E) :
    fderiv ℝ
        (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
          ((toEuclidean (E := E)) e')) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  classical
  have htoE_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)) : E → EuclN) :=
    ContinuousLinearEquiv.contDiff _
  have hcomp_smooth : ContDiff ℝ ∞
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
  have h_chain : fderiv ℝ
      ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ∘
        ((toEuclidean (E := E)) : E → EuclN)) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (((toEuclidean (E := E)) : E → EuclN) e)).comp
        (fderiv ℝ ((toEuclidean (E := E)) : E → EuclN) e) := by
    apply fderiv_comp e
    · exact (hcomp_smooth.differentiable (by norm_num)).differentiableAt
    · exact (htoE_smooth.differentiable (by norm_num)).differentiableAt
  rw [show (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e')) =
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ∘
        ((toEuclidean (E := E)) : E → EuclN) from rfl]
  rw [h_chain]
  congr 1
  exact (toEuclidean (E := E)).fderiv

/-- Similarly, the Fréchet derivative of `chartPouEucl ∘ toEuclidean` on E. -/
private lemma fderiv_chartPouEucl_toEuclidean (α : M) (e : E) :
    fderiv ℝ
        (fun e' : E => chartPouEucl (I := I) (M := M) α
          ((toEuclidean (E := E)) e')) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  classical
  have htoE_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)) : E → EuclN) :=
    ContinuousLinearEquiv.contDiff _
  have hpou_smooth : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have h_chain : fderiv ℝ
      ((chartPouEucl (I := I) (M := M) α) ∘
        ((toEuclidean (E := E)) : E → EuclN)) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          (((toEuclidean (E := E)) : E → EuclN) e)).comp
        (fderiv ℝ ((toEuclidean (E := E)) : E → EuclN) e) := by
    apply fderiv_comp e
    · exact (hpou_smooth.differentiable (by norm_num)).differentiableAt
    · exact (htoE_smooth.differentiable (by norm_num)).differentiableAt
  rw [show (fun e' : E => chartPouEucl (I := I) (M := M) α
        ((toEuclidean (E := E)) e')) =
      (chartPouEucl (I := I) (M := M) α) ∘
        ((toEuclidean (E := E)) : E → EuclN) from rfl]
  rw [h_chain]
  congr 1
  exact (toEuclidean (E := E)).fderiv

/-- The chart-pulled POU function equals `chartPouEucl ∘ toEuclidean` on the
chart target. -/
private lemma pou_symm_eventuallyEq_chartPouEucl_toEuclidean
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e'))
      =ᶠ[𝓝 e]
      (fun e' : E => chartPouEucl (I := I) (M := M) α
        ((toEuclidean (E := E)) e')) := by
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  filter_upwards [h_open.mem_nhds he] with e' he'
  exact (chartPouEucl_toEuclidean_eq_pou_symm (I := I) (M := M) α he').symm

/-- The Fréchet derivative of the chart-pulled POU function equals
`fderiv chartPouEucl (toEuclidean e) ∘ toEuclidean` on the chart target. -/
private lemma fderiv_pou_symm_eq
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  rw [(pou_symm_eventuallyEq_chartPouEucl_toEuclidean
    (I := I) (M := M) α he).fderiv_eq]
  exact fderiv_chartPouEucl_toEuclidean (I := I) (M := M) α e

/-- The chart-pulled POU Fréchet derivative is uniformly bounded on
`(extChartAt I α).target`. -/
private lemma exists_pou_symm_fderiv_uniform_bound (α : M) :
    ∃ K_pou : ℝ, 0 ≤ K_pou ∧
      ∀ e ∈ (extChartAt I α).target,
        ‖fderiv ℝ
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ≤ K_pou := by
  classical
  obtain ⟨K_eucl, hK_nn, hK_bound⟩ :=
    exists_chartPouEucl_fderiv_uniform_bound (I := I) (M := M) α
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  refine ⟨K_eucl * NtoE, mul_nonneg hK_nn hNtoE_nn, ?_⟩
  intro e he
  rw [fderiv_pou_symm_eq (I := I) (M := M) α he]
  have hbound : ‖(fderiv ℝ (chartPouEucl (I := I) (M := M) α)
        ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ≤
      ‖fderiv ℝ (chartPouEucl (I := I) (M := M) α)
        ((toEuclidean (E := E)) e)‖ *
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  refine le_trans hbound ?_
  exact mul_le_mul_of_nonneg_right (hK_bound _) hNtoE_nn

/-- The topological support of `tensorChartComp g r s T α Idx Jdx` is contained in
`chartTargetEuclid α`. Since `tensorChartComp` equals `0` outside the chart target
and is identified with the chart-Euclidean push of `tensorChartComponentPou`,
whose carrier is contained in the compact `toEuclidean`-image of the chart of
`tsupport (POU * raw)` — itself a subset of `chartTargetEuclid α`. -/
lemma tensorChartComp_tsupport_subset_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  set f : M → ℝ := tensorChartComponentPou (I := I) (M := M)
    g r s T α Idx Jdx with hf_def
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
  set K : Set EuclN :=
    (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_src : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_src
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_subset_target : K ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro z hz_carrier
    rcases hz_carrier with ⟨w, ⟨x, hx_supp, hxw⟩, hwz⟩
    have hx_src : x ∈ (extChartAt I α).source := hsub_src hx_supp
    have hw_target : w ∈ (extChartAt I α).target := by
      rw [← hxw]; exact (extChartAt I α).map_source hx_src
    exact ⟨w, hw_target, hwz⟩
  have h_supp_K : Function.support
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ⊆ K := by
    intro y hy_supp
    by_contra hyK
    apply hy_supp
    by_cases hy_target :
        y ∈ chartTargetEuclid (I := I) (M := M) α
    · rcases hy_target with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [tensorChartComp_def, tensorChartComponent_def,
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) α f ⟨w, hw_target, hwy⟩]
      by_contra hne_f
      apply hyK
      have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
          tsupport f := by
        apply subset_tsupport
        exact hne_f
      rw [h_eq] at hin_supp
      have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      exact ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwy⟩
    · rw [tensorChartComp_def, tensorChartComponent_def]
      exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) α f hy_target
  refine (closure_minimal h_supp_K hK_closed).trans hK_subset_target

/-- The squared `eLpNorm` identity: for a real-valued function `f` and a measure `μ`,
`(eLpNorm f 2 μ)² = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ`. -/
private lemma sq_eLpNorm_two_eq_lintegral_ofReal_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq f μ]
  refine lintegral_congr ?_
  intro x
  rw [show ((f x) ^ 2 : ℝ) = ‖f x‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs],
    ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm_eq_enorm]

/-- The chart-α-pulled `repr T` is differentiable at any chart-target point. -/
lemma repr_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e := by
  classical
  set b : M := (extChartAt I α).symm e
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target he
  have hb_chart : b ∈ (chartAt H α).source := by
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  have he_eq : extChartAt I α b = e := (extChartAt I α).right_inv he
  have hψ_eq :
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) =
        fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx := by
    funext y
    set bb := (extChartAt I α).symm y
    set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
      r s α (fun z : M => T.toSection z) bb
    have hR_recover : R =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx R •
              tensorChartBasisElement (E := E) r s Idx Jdx :=
      tensorRSModel_eq_sum_basis (E := E) r s R
    have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s Idx Jdx R =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx bb := by
      intro Idx Jdx
      rw [tensorChartComponentRaw_def]
      rfl
    change R = _
    rw [hR_recover]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [hcomp_eq Idx Jdx]
    rfl
  rw [hψ_eq]
  refine DifferentiableAt.fun_sum (fun Idx _ => ?_)
  refine DifferentiableAt.fun_sum (fun Jdx _ => ?_)
  refine DifferentiableAt.smul_const ?_ _
  have hdiff := chart_pulled_component_differentiableAt
    (I := I) (M := M) g r s T α Idx Jdx hb_chart
  rwa [he_eq] at hdiff

/-- The chart-pulled `tensorChartComponentRaw α Idx Jdx ∘ symm` is differentiable at
any chart-target point. (A renaming of an existing helper for ergonomic reuse.) -/
private lemma raw_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e :=
  tensorChartComponentRaw_symm_differentiableAt
    (I := I) (M := M) g r s T α Idx Jdx he

/-- The fderiv of `(POU · raw_IJ) ∘ symm` at a chart-target point factors via
the EuclN-side `tensorChartComp`: it equals `fderiv tensorChartComp_IJ (toEucl e)
∘ toEucl`. -/
private lemma fderiv_pou_raw_symm_eq_chain
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  rw [fderiv_pou_mul_raw_symm_eq_fderiv_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he]
  exact fderiv_tensorChartComp_toEuclidean (I := I) (M := M) g r s T α Idx Jdx e

/-- The Leibniz expansion of `fderiv (POU · raw_IJ ∘ symm)` at a chart-target
point. -/
private lemma fderiv_pou_raw_symm_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e) •
          fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e +
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e) •
          fderiv ℝ
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e := by
  classical
  have hP_diff : DifferentiableAt ℝ
      (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e')) e :=
    chartAtlasPOU_symm_differentiableAt (I := I) (M := M) α he
  have hR_diff : DifferentiableAt ℝ
      (fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e')) e :=
    raw_symm_differentiableAt (I := I) (M := M) g r s T α Idx Jdx he
  exact fderiv_fun_mul hP_diff hR_diff

/-- Pointwise (squared) bound: at any chart-target point, the squared operator
norm of `fderiv (repr T ∘ symm)` is bounded by `N · Bnorm²` times the finite
double sum of `‖fderiv (raw_IJ ∘ symm)‖²`. -/
lemma fderiv_repr_opNormSq_le_sum_fderiv_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {e : E}
    (he : e ∈ (extChartAt I α).target) :
    ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        e‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) e‖ ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  set b : M := (extChartAt I α).symm e with hb_def
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target he
  have hb_chart : b ∈ (chartAt H α).source := by
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  have he_eq : extChartAt I α b = e := (extChartAt I α).right_inv he
  have hbasis_le : ∀ Idx Jdx, ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ ≤ Bnorm := by
    intro Idx Jdx
    exact tensorChartBasisElement_norm_le (E := E) r s Idx Jdx
  have h_lin :=
    fderiv_repr_opNorm_le_sum_fderiv_components
      (I := I) (M := M) g r s T α (b := b) hb_chart
  rw [he_eq] at h_lin
  have h_rhs_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ *
              ‖tensorChartBasisElement (E := E) r s Idx Jdx‖) ≤
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact mul_le_mul_of_nonneg_left (hbasis_le Idx Jdx) (norm_nonneg _)
  have h_norm_le : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ Idx, ∑ Jdx,
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := h_lin.trans h_rhs_le
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_sum_pair_eq :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)]
  have h_sum_nn :
      0 ≤ (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
          p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_le' : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [← h_sum_pair_eq] at h_norm_le; exact h_norm_le
  have h_norm_sq : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ((∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 := by
    have := mul_le_mul h_norm_le' h_norm_le' (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  have hCS :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by simp
    rw [h_sum_one] at hbase
    exact hbase
  have h_combined : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 *
        ∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have h_sq_eq : ((∑ p ∈ V,
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 = (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    calc ‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ (∑ p ∈ V,
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * (∑ p ∈ V,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) * Bnorm ^ 2 := h_mul
      _ = (V.card : ℝ) * Bnorm ^ 2 *
            ∑ p ∈ V,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by ring
  have h_pair_to_nest :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2)]
  rw [h_pair_to_nest] at h_combined
  exact h_combined

/-- **Pointwise scaled bound.** On the chart target, the POU²-scaled squared
chart-pulled-repr Fréchet-derivative norm is bounded by `C1` times the sum of
squared Fréchet-derivative norms of `tensorChartComp_IJ` at `toEuclidean e`,
plus `C2` times the sum of squared raw component values at
`(extChartAt I α).symm e`, with explicit constants:

```
C1 = 2 * N * Bnorm² * ‖toEuclidean‖²
C2 = 2 * N * Bnorm² * K_pou²
```

where `N` is the cardinality of the `(Idx, Jdx)` pair set, `Bnorm` is the
chart-basis norm constant, and `K_pou` is a uniform upper bound on the
operator norm of the Fréchet derivative of the chart-pulled
partition-of-unity. This is the pointwise core of the order-`1` chart-target
POU-weighted `L²` bound on the chart-pulled repr Fréchet derivative. -/
lemma pou_sq_fderiv_repr_sq_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (K_pou : ℝ) (hK_pou_nn : 0 ≤ K_pou)
    (hK_pou_bound : ∀ e ∈ (extChartAt I α).target,
      ‖fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ≤ K_pou)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm e)) ^ 2) *
      (‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (2 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ ^ 2 +
        (2 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
          (tensorChartBasisNormConstant (E := E) r s) ^ 2 * K_pou ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ)
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e)
  have hρ_nn : 0 ≤ ρ := by
    have := (chartAtlasPOU I M).nonneg α ((extChartAt I α).symm e); exact this
  have h_sq := fderiv_repr_opNormSq_le_sum_fderiv_components_sq
    (I := I) (M := M) g r s T α (e := e) he
  have h_scaled : ρ ^ 2 *
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
  have h_per_IJ : ∀ Idx Jdx,
      ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
        2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
        2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2 := by
    intro Idx Jdx
    set raw_val : ℝ := tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e)
    set FR : E →L[ℝ] ℝ := fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
          (extChartAt I α).symm) e
    set FP : E →L[ℝ] ℝ := fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e
    set L : E →L[ℝ] ℝ := fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e
    have hleibniz : L = ρ • FR + raw_val • FP := by
      simpa [L, FR, FP, raw_val, ρ] using
        fderiv_pou_raw_symm_leibniz (I := I) (M := M) g r s T α Idx Jdx he
    have h_eq : ρ • FR = L - raw_val • FP := by
      rw [hleibniz]; abel
    have hnorm : ‖ρ • FR‖ ≤ ‖L‖ + |raw_val| * ‖FP‖ := by
      rw [h_eq]
      refine le_trans (norm_sub_le _ _) ?_
      refine add_le_add le_rfl ?_
      rw [norm_smul, Real.norm_eq_abs]
    have hρFR : ‖ρ • FR‖ = ρ * ‖FR‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ_nn]
    rw [hρFR] at hnorm
    have hρFR_nn : 0 ≤ ρ * ‖FR‖ := mul_nonneg hρ_nn (norm_nonneg _)
    have hLraw_nn : 0 ≤ ‖L‖ + |raw_val| * ‖FP‖ :=
      add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    have hsq : (ρ * ‖FR‖) ^ 2 ≤ (‖L‖ + |raw_val| * ‖FP‖) ^ 2 := by
      exact pow_le_pow_left₀ hρFR_nn hnorm 2
    have hexp : (‖L‖ + |raw_val| * ‖FP‖) ^ 2 ≤ 2 * ‖L‖ ^ 2 + 2 * (|raw_val| * ‖FP‖) ^ 2 := by
      have h := sq_nonneg (‖L‖ - |raw_val| * ‖FP‖)
      nlinarith [h]
    have hρ_sq_FR_sq : ρ ^ 2 * ‖FR‖ ^ 2 = (ρ * ‖FR‖) ^ 2 := by ring
    rw [hρ_sq_FR_sq]
    refine le_trans hsq (le_trans hexp ?_)
    have hL_eq := fderiv_pou_raw_symm_eq_chain (I := I) (M := M)
      g r s T α Idx Jdx he
    have hL_bound : ‖L‖ ≤
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ * NtoE := by
      change ‖fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e‖ ≤ _
      rw [hL_eq]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    have hL_nn : 0 ≤ ‖L‖ := norm_nonneg _
    have hLsq : ‖L‖ ^ 2 ≤
        (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 :=
      pow_le_pow_left₀ hL_nn hL_bound 2
    have hFP_bound : ‖FP‖ ≤ K_pou := hK_pou_bound e he
    have hFP_nn : 0 ≤ ‖FP‖ := norm_nonneg _
    have hraw_abs_nn : 0 ≤ |raw_val| := abs_nonneg _
    have h_raw_fp_nn : 0 ≤ |raw_val| * ‖FP‖ := mul_nonneg hraw_abs_nn hFP_nn
    have h_raw_K_nn : 0 ≤ |raw_val| * K_pou := mul_nonneg hraw_abs_nn hK_pou_nn
    have h_raw_fp_le : |raw_val| * ‖FP‖ ≤ |raw_val| * K_pou :=
      mul_le_mul_of_nonneg_left hFP_bound hraw_abs_nn
    have h_raw_fp_sq_le : (|raw_val| * ‖FP‖) ^ 2 ≤ (|raw_val| * K_pou) ^ 2 :=
      pow_le_pow_left₀ h_raw_fp_nn h_raw_fp_le 2
    have h_raw_K_sq : (|raw_val| * K_pou) ^ 2 = raw_val ^ 2 * K_pou ^ 2 := by
      rw [mul_pow]; rw [sq_abs]
    have hL_NtoE_sq : (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 =
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by ring
    have h_total : 2 * ‖L‖ ^ 2 + 2 * (|raw_val| * ‖FP‖) ^ 2 ≤
        2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
        2 * raw_val ^ 2 * K_pou ^ 2 := by
      have h1 : 2 * ‖L‖ ^ 2 ≤ 2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by
        calc 2 * ‖L‖ ^ 2 ≤ 2 * (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left hLsq (by norm_num)
            _ = 2 *
                ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by
              rw [hL_NtoE_sq]; ring
      have h2 : 2 * (|raw_val| * ‖FP‖) ^ 2 ≤ 2 * raw_val ^ 2 * K_pou ^ 2 := by
        calc 2 * (|raw_val| * ‖FP‖) ^ 2 ≤ 2 * (|raw_val| * K_pou) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left h_raw_fp_sq_le (by norm_num)
            _ = 2 * raw_val ^ 2 * K_pou ^ 2 := by
              rw [h_raw_K_sq]; ring
      linarith
    exact h_total
  have h_sum_per :
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (2 * N * Bnorm ^ 2 * NtoE ^ 2) *
          ∑ Idx, ∑ Jdx,
            ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              ((toEuclidean (E := E)) e)‖ ^ 2 +
        (2 * N * Bnorm ^ 2 * K_pou ^ 2) *
          ∑ Idx, ∑ Jdx,
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 := by
    rw [show ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) = (N * Bnorm ^ 2) *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
      rw [show (∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) =
            ρ ^ 2 * ∑ Idx, ∑ Jdx,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [Finset.mul_sum]]
      ring]
    have hNBsq_nn : 0 ≤ N * Bnorm ^ 2 :=
      mul_nonneg hN_nn (sq_nonneg _)
    calc N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ N * Bnorm ^ 2 *
            (∑ Idx, ∑ Jdx,
              (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
              2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNBsq_nn
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = (2 * N * Bnorm ^ 2 * NtoE ^ 2) *
            ∑ Idx, ∑ Jdx,
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ ^ 2 +
          (2 * N * Bnorm ^ 2 * K_pou ^ 2) *
            ∑ Idx, ∑ Jdx,
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 := by
          have h_inner_sum : ∀ Idx,
              (∑ Jdx,
                (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) =
              (∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) +
              (∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) := fun Idx => by
            rw [Finset.sum_add_distrib]
          have h_outer_sum :
              (∑ Idx, ∑ Jdx,
                (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) =
              (∑ Idx, ∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) +
              (∑ Idx, ∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) := by
            rw [Finset.sum_congr rfl (fun Idx _ => h_inner_sum Idx)]
            rw [Finset.sum_add_distrib]
          rw [h_outer_sum]
          rw [show (∑ Idx, ∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) =
            2 * NtoE ^ 2 *
              ∑ Idx, ∑ Jdx,
                ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Idx _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Jdx _ => ?_)
            ring]
          rw [show (∑ Idx, ∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) =
            2 * K_pou ^ 2 *
              ∑ Idx, ∑ Jdx,
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e)) ^ 2 from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Idx _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Jdx _ => ?_)
            ring]
          ring
  exact le_trans h_scaled h_sum_per

/-- AEMeasurability of `y ↦ ofReal((raw α Idx Jdx (sym y))^2)` on the chart-
target restriction. The composition `(raw α Idx Jdx) ∘ (extChartAt I α).symm ∘
toEuclidean.symm` is continuous on `chartTargetEuclid α` (a chain of two
continuous-on-target maps and one CLE), so by `ContinuousOn.aemeasurable` it is
AEMeasurable w.r.t. `volume.restrict chartTargetEuclid α`. -/
private lemma raw_sym_sq_ofReal_aeMeasurable_restrict
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclN =>
        ENNReal.ofReal
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_raw_symm_contDiffOn : ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) :=
    tensorChartComponentRaw_symm_contDiffOn_target
      (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_symm_cont : ContinuousOn
      (fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e')) (extChartAt I α).target :=
    h_raw_symm_contDiffOn.continuousOn
  have h_toEucl_symm_cont : Continuous ((toEuclidean (E := E)).symm) :=
    (toEuclidean (E := E)).symm.continuous
  have h_raw_sym_cont : ContinuousOn
      (fun y : EuclN => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine h_raw_symm_cont.comp h_toEucl_symm_cont.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_raw_sym_ae :
      AEMeasurable
        (fun y : EuclN => tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    h_raw_sym_cont.aemeasurable h_chartTarget_meas
  have h_sq_ae : AEMeasurable
      (fun y : EuclN => (tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    h_raw_sym_ae.pow_const 2
  exact ENNReal.measurable_ofReal.comp_aemeasurable h_sq_ae

/-- AEMeasurability of `y ↦ ofReal(‖fderiv tensorChartComp_IJ y‖^2)`. Since
`tensorChartComp_IJ` is `ContDiff ℝ ∞`, `fderiv tensorChartComp_IJ` is continuous,
so the entire integrand is continuous, hence measurable on the whole space (and
a fortiori AEMeasurable on any restriction). -/
private lemma fderiv_tensorChartComp_sq_ofReal_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (fun y : EuclN =>
        ENNReal.ofReal
          (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  refine (continuous_pow 2).measurable.comp ?_
  have h_fderiv_cont : Continuous
      (fun y : EuclN =>
        fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) := by
    have := (tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx)
    exact this.continuous_fderiv (by simp)
  exact h_fderiv_cont.norm.measurable

/-- **Order-1 chart-target POU-weighted L² bound for the Fréchet derivative of
the chart-pulled tensor representation.** For a smooth closed Riemannian
manifold `(M, g)`, fixed ranks `(r, s)`, and a chart base point `α : M`, there
is a non-negative constant `K` (depending only on `(g, r, s, α)` and the model
space; independent of `T`) such that for every smooth compactly-supported
`(r, s)`-tensor section `T`, the chart-target Lebesgue integral of the
partition-of-unity-weighted squared operator norm of the Fréchet derivative
`fderiv (tensorRSChartE_section_repr r s α T.toSection ∘ (extChartAt I α).symm)`
is bounded by `K` times the sum of two pieces:

* the sum of the squared `wkpNorm 1 2`-norms of the chart-frame scalar
  components `tensorChartComp g r s T α Idx Jdx`, and
* the sum of the squared `L²`-norms (over the chart target) of the chart-pulled
  raw components `raw_IJ ∘ (extChartAt I α).symm ∘ toEuclidean.symm`.

The first term packages the gradient contribution into Sobolev-style norms via
the order-`1` chart-target Fréchet-derivative `L²`-bound. The second term, the
unweighted `L²` of the raw components, is the controlled correction coming
from the partition-of-unity multiplier. -/
theorem chartTargetPouWeightedL2NormSq_fderiv_repr_le_sum_chartComp_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖fderiv ℝ
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) 1 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    (chartTargetEuclid (I := I) (M := M) α) ^ 2 +
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  eLpNorm
                      (fun y : EuclN =>
                        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
                      ((volume : Measure EuclN).restrict
                        (chartTargetEuclid (I := I) (M := M) α)) ^ 2) := by
  classical
  obtain ⟨K_pou, hK_pou_nn, hK_pou_bound⟩ :=
    exists_pou_symm_fderiv_uniform_bound (I := I) (M := M) α
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set C1 : ℝ := 2 * N * Bnorm ^ 2 * NtoE ^ 2 with hC1_def
  set C2 : ℝ := 2 * N * Bnorm ^ 2 * K_pou ^ 2 with hC2_def
  have hC1_nn : 0 ≤ C1 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    exact by norm_num
  have hC2_nn : 0 ≤ C2 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    exact by norm_num
  refine ⟨C1 + C2, add_nonneg hC1_nn hC2_nn, ?_⟩
  intro T
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2) with hlhs_def
  set fIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)
    with hfInt_def
  set rIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
    with hrInt_def
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal C1 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fIntegrand Idx Jdx y) +
        ENNReal.ofReal C2 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rIntegrand Idx Jdx y) := by
    intro y hy
    set e : E := (toEuclidean (E := E)).symm y with he_def
    have he_target : e ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_real := pou_sq_fderiv_repr_sq_pointwise
      (I := I) (M := M) g r s T α K_pou hK_pou_nn hK_pou_bound (e := e) he_target
    have h_toEucl_e : (toEuclidean (E := E)) e = y := by
      simp [he_def, (toEuclidean (E := E)).apply_symm_apply]
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e) with hρ_def
    have hρ_sym : ρ = (chartAtlasPOU I M α : M → ℝ) (sym y) := by
      simp [hρ_def, hsym_def, he_def]
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    set FRsq : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 with hFRsq_def
    have hFRsq_nn : 0 ≤ FRsq := sq_nonneg _
    set fSum : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ ^ 2 with hfSum_def
    have hfSum_nn : 0 ≤ fSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    set rSum : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e)) ^ 2 with hrSum_def
    have hrSum_nn : 0 ≤ rSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have h_real' : ρ ^ 2 * FRsq ≤ C1 * fSum + C2 * rSum := by
      simpa [ρ, FRsq, fSum, rSum, C1, C2, Bnorm, NtoE, N, hC1_def, hC2_def,
        hBnorm_def, hNtoE_def, hN_def] using h_real
    have h_LHS_eq : lhsIntegrand y =
        ENNReal.ofReal (ρ ^ 2 * FRsq) := by
      simp only [hlhs_def, ← hρ_sym, FRsq]
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_LHS_eq]
    refine le_trans (ENNReal.ofReal_le_ofReal h_real') ?_
    have h_C1fSum_nn : 0 ≤ C1 * fSum := mul_nonneg hC1_nn hfSum_nn
    have h_C2rSum_nn : 0 ≤ C2 * rSum := mul_nonneg hC2_nn hrSum_nn
    rw [ENNReal.ofReal_add h_C1fSum_nn h_C2rSum_nn]
    rw [ENNReal.ofReal_mul hC1_nn, ENNReal.ofReal_mul hC2_nn]
    have h_fSum_eq :
        ENNReal.ofReal fSum =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y := by
      simp only [hfSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg (fun Jdx _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun Jdx _ => sq_nonneg _)]
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      change ENNReal.ofReal
          (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2) =
        fIntegrand Idx Jdx y
      rw [h_toEucl_e]
    have h_rSum_eq :
        ENNReal.ofReal rSum =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y := by
      simp only [hrSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg (fun Jdx _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun Jdx _ => sq_nonneg _)]
    rw [h_fSum_eq, h_rSum_eq]
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (ENNReal.ofReal C1 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  fIntegrand Idx Jdx y) +
              ENNReal.ofReal C2 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  rIntegrand Idx Jdx y))
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  have h_fInt_meas : ∀ Idx Jdx, Measurable (fIntegrand Idx Jdx) := fun Idx Jdx =>
    fderiv_tensorChartComp_sq_ofReal_measurable
      (I := I) (M := M) g r s T α Idx Jdx
  have h_rInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (rIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    have := raw_sym_sq_ofReal_aeMeasurable_restrict
      (I := I) (M := M) g r s T α Idx Jdx
    simpa [hrInt_def, hsym_def] using this
  have h_fInt_sum_aeMeas :
      AEMeasurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    have : Measurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y) := by
      refine Finset.measurable_sum _ (fun Idx _ => ?_)
      refine Finset.measurable_sum _ (fun Jdx _ => ?_)
      exact h_fInt_meas Idx Jdx
    exact this.aemeasurable
  have h_rInt_sum_aeMeas :
      AEMeasurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_inner_ae : ∀ Idx,
        AEMeasurable
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
      have h_eq : (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
        funext y
        simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    have h_funsum_ae : AEMeasurable
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      Finset.aemeasurable_sum _ (fun Idx _ => h_inner_ae Idx)
    have h_eq : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) =
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
      funext y
      simp [Finset.sum_apply]
    rwa [h_eq] at h_funsum_ae
  have h_split :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y) +
            ENNReal.ofReal C2 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y))
          ∂(volume : Measure EuclN) =
        (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal C1 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  fIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN)) +
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal C2 *
                (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                  ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                    rIntegrand Idx Jdx y)
              ∂(volume : Measure EuclN)) := by
    have h_lhs_aeMeas : AEMeasurable
        (fun y : EuclN =>
          ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      exact AEMeasurable.const_mul h_fInt_sum_aeMeas _
    exact lintegral_add_left' h_lhs_aeMeas _
  rw [h_split] at h_int_mono
  have h_const_C1 :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C1 *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h_const_C2 :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal C2 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C2 *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [h_const_C1, h_const_C2] at h_int_mono
  have h_dist_f :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                fIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    rw [lintegral_finset_sum _ (fun Idx _ => by
      refine Finset.measurable_sum _ (fun Jdx _ => ?_)
      exact h_fInt_meas Idx Jdx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum _ (fun Jdx _ => h_fInt_meas Idx Jdx)
  have h_dist_r :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    have h_inner_ae : ∀ Idx,
        AEMeasurable
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
      have h_eq : (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
        funext y
        simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    rw [lintegral_finset_sum' _ (fun Idx _ => h_inner_ae Idx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum' _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
  rw [h_dist_f, h_dist_r] at h_int_mono
  have h_per_f : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          fIntegrand Idx Jdx y ∂(volume : Measure EuclN) ≤
        wkpNorm (d := Module.finrank ℝ E) 1 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
    intro Idx Jdx
    have h_chartTarget_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α
    have h_tcc_smooth : ContDiff ℝ ∞
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
      tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
    have h_tcc_compactSupport : HasCompactSupport
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
      tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
    have h_tcc_supp : tsupport (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        ⊆ chartTargetEuclid (I := I) (M := M) α :=
      tensorChartComp_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) g r s T α Idx Jdx
    have h_brg :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chartTarget_fderiv_eLpNorm_le_wkpNorm_one_two
        (d := Module.finrank ℝ E) h_chartTarget_open
        (h_tcc_smooth.of_le (by simp)) h_tcc_compactSupport h_tcc_supp
    have h_lp_sq :
        (eLpNorm
            (fun y : EuclN =>
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 =
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              fIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
      have h_eLp_sq := sq_eLpNorm_two_eq_lintegral_ofReal_sq
        (fun y : EuclN =>
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      rw [h_eLp_sq]
    have h_sq_le :
        (eLpNorm
            (fun y : EuclN =>
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
          wkpNorm (d := Module.finrank ℝ E) 1 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
      exact pow_le_pow_left' h_brg 2
    rw [← h_lp_sq]; exact h_sq_le
  have h_per_r : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          rIntegrand Idx Jdx y ∂(volume : Measure EuclN) =
        eLpNorm
            (fun y : EuclN =>
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    intro Idx Jdx
    have h_eLp_sq := sq_eLpNorm_two_eq_lintegral_ofReal_sq
      (fun y : EuclN =>
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
    have h_eq_lhs :
        ∫⁻ y,
            ENNReal.ofReal
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
            ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) =
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            rIntegrand Idx Jdx y ∂(volume : Measure EuclN) := rfl
    rw [h_eq_lhs] at h_eLp_sq
    exact h_eLp_sq.symm
  refine h_int_mono.trans ?_
  have h_f_total_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) ≤
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) 1 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact h_per_f Idx Jdx
  have h_r_total_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rIntegrand Idx Jdx y ∂(volume : Measure EuclN)) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            eLpNorm
                (fun y : EuclN =>
                  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    exact h_per_r Idx Jdx
  set Xf : ℝ≥0∞ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) 1 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ^ 2 with hXf_def
  set Xr : ℝ≥0∞ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      eLpNorm
          (fun y : EuclN =>
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 with hXr_def
  have h_C1_le : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C1 + C2) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hC2_nn)
  have h_C2_le : ENNReal.ofReal C2 ≤ ENNReal.ofReal (C1 + C2) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hC1_nn)
  calc
    ENNReal.ofReal C1 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) +
      ENNReal.ofReal C2 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  rIntegrand Idx Jdx y ∂(volume : Measure EuclN))
        ≤ ENNReal.ofReal C1 * Xf + ENNReal.ofReal C2 * Xr := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_right h_f_total_le (ENNReal.ofReal C1)
          · exact le_of_eq (by rw [h_r_total_eq])
      _ ≤ ENNReal.ofReal (C1 + C2) * Xf + ENNReal.ofReal (C1 + C2) * Xr := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_left h_C1_le Xf
          · exact mul_le_mul_left h_C2_le Xr
      _ = ENNReal.ofReal (C1 + C2) * (Xf + Xr) := by
          rw [mul_add]

/-- **Order-2 Leibniz inequality.** For two real-valued functions
`f, g : E → ℝ` that are `ContDiffAt ℝ 2` at a point `x`, the iterated
Fréchet derivative satisfies the triangle bound
`|f x| · ‖∇²g x‖ ≤ ‖∇²(f·g) x‖ + |g x| · ‖∇²f x‖ + 2 · ‖∇f x‖ · ‖∇g x‖`.

The proof works at the `fderiv (fderiv ·)` level, using the order-1
Leibniz equality (`fderiv_fun_mul`) twice. We unfold both `iteratedFDeriv 2 f`
and `iteratedFDeriv 2 (fg)` to `fderiv (fderiv ·)` via
`iteratedFDeriv_two_apply`. -/
private lemma scalar_iteratedFDeriv_two_mul_norm_le
    (f g : E → ℝ) {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    |f x| * ‖iteratedFDeriv ℝ 2 g x‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun y : E => f y * g y) x‖ +
        |g x| * ‖iteratedFDeriv ℝ 2 f x‖ +
        2 * ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
  classical
  have h1_ne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have h2_ne : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hf_diffAt : DifferentiableAt ℝ f x :=
    hf.differentiableAt h2_ne
  have hg_diffAt : DifferentiableAt ℝ g x :=
    hg.differentiableAt h2_ne
  have h2_ne_top : (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
  have hf_diff_at_eventually : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually h2_ne_top] with y hy
    exact hy.differentiableAt h2_ne
  have hg_diff_at_eventually : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually h2_ne_top] with y hy
    exact hy.differentiableAt h2_ne
  have hf_fderiv_contDiffAt : ContDiffAt ℝ 1 (fderiv ℝ f) x := by
    have := hf.fderiv_right
      (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    simpa using this
  have hg_fderiv_contDiffAt : ContDiffAt ℝ 1 (fderiv ℝ g) x := by
    have := hg.fderiv_right
      (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    simpa using this
  have hf_fderiv_diffAt : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hf_fderiv_contDiffAt.differentiableAt h1_ne
  have hg_fderiv_diffAt : DifferentiableAt ℝ (fderiv ℝ g) x :=
    hg_fderiv_contDiffAt.differentiableAt h1_ne
  have h_fderiv_fg_eventually :
      (fun y : E => fderiv ℝ (fun z : E => f z * g z) y) =ᶠ[nhds x]
        (fun y : E => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    filter_upwards [hf_diff_at_eventually, hg_diff_at_eventually]
      with y hfy hgy
    exact fderiv_fun_mul hfy hgy
  have h_step3 :
      fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x =
        fderiv ℝ (fun y : E => f y • fderiv ℝ g y + g y • fderiv ℝ f y) x :=
    h_fderiv_fg_eventually.fderiv_eq
  have h_split :
      fderiv ℝ (fun y : E => f y • fderiv ℝ g y + g y • fderiv ℝ f y) x =
        fderiv ℝ (fun y : E => f y • fderiv ℝ g y) x +
        fderiv ℝ (fun y : E => g y • fderiv ℝ f y) x := by
    apply fderiv_fun_add
    · exact hf_diffAt.smul hg_fderiv_diffAt
    · exact hg_diffAt.smul hf_fderiv_diffAt
  have h_f_smul : fderiv ℝ (fun y : E => f y • fderiv ℝ g y) x =
      f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x) :=
    fderiv_fun_smul hf_diffAt hg_fderiv_diffAt
  have h_g_smul : fderiv ℝ (fun y : E => g y • fderiv ℝ f y) x =
      g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x) :=
    fderiv_fun_smul hg_diffAt hf_fderiv_diffAt
  have h_total :
      fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x =
        f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x) +
        (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
    rw [h_step3, h_split, h_f_smul, h_g_smul]
  have h_norm_iter_f : ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
    rw [show ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ f) x‖ from
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ f) (x := x)).symm]
    rw [norm_iteratedFDeriv_fderiv]
  have h_norm_iter_g : ‖iteratedFDeriv ℝ 2 g x‖ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by
    rw [show ‖fderiv ℝ (fderiv ℝ g) x‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) x‖ from
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ g) (x := x)).symm]
    rw [norm_iteratedFDeriv_fderiv]
  have h_norm_iter_fg :
      ‖iteratedFDeriv ℝ 2 (fun y : E => f y * g y) x‖ =
        ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ := by
    rw [show ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun y : E => f y * g y)) x‖ from
      (norm_iteratedFDeriv_one (𝕜 := ℝ)
        (fderiv ℝ (fun y : E => f y * g y)) (x := x)).symm]
    rw [norm_iteratedFDeriv_fderiv]
  have h_iso :
      f x • fderiv ℝ (fderiv ℝ g) x =
        fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x -
        ((fderiv ℝ f x).smulRight (fderiv ℝ g x) +
         (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))) := by
    rw [h_total]
    abel
  have h_fx_smul_norm :
      ‖f x • fderiv ℝ (fderiv ℝ g) x‖ =
        |f x| * ‖fderiv ℝ (fderiv ℝ g) x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h_gx_smul_norm :
      ‖g x • fderiv ℝ (fderiv ℝ f) x‖ =
        |g x| * ‖fderiv ℝ (fderiv ℝ f) x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h_smulRight_norm_fg :
      ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ =
        ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
  have h_smulRight_norm_gf :
      ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ =
        ‖fderiv ℝ g x‖ * ‖fderiv ℝ f x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
  have h_tri :
      ‖f x • fderiv ℝ (fderiv ℝ g) x‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ +
          ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x) +
           (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))‖ := by
    rw [h_iso]
    exact norm_sub_le _ _
  have h_tri2 :
      ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x) +
       (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))‖ ≤
        ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ +
          ‖g x • fderiv ℝ (fderiv ℝ f) x +
           (fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ :=
    norm_add_le _ _
  have h_tri3 :
      ‖g x • fderiv ℝ (fderiv ℝ f) x +
       (fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ ≤
        ‖g x • fderiv ℝ (fderiv ℝ f) x‖ +
          ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ :=
    norm_add_le _ _
  have h_combined :
      ‖f x • fderiv ℝ (fderiv ℝ g) x‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ +
          (‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ +
           (‖g x • fderiv ℝ (fderiv ℝ f) x‖ +
            ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖)) :=
    h_tri.trans
      (add_le_add le_rfl
        (h_tri2.trans (add_le_add le_rfl h_tri3)))
  rw [h_fx_smul_norm] at h_combined
  rw [h_gx_smul_norm] at h_combined
  rw [h_smulRight_norm_fg] at h_combined
  rw [h_smulRight_norm_gf] at h_combined
  rw [← h_norm_iter_g, ← h_norm_iter_f, ← h_norm_iter_fg] at h_combined
  nlinarith [h_combined,
    mul_nonneg (norm_nonneg (fderiv ℝ f x)) (norm_nonneg (fderiv ℝ g x)),
    mul_nonneg (norm_nonneg (fderiv ℝ g x)) (norm_nonneg (fderiv ℝ f x))]

/-- **Order-2 squared basis decomposition.** Pointwise (squared) bound: at any
chart-target point, the squared operator norm of `iteratedFDeriv 2 (repr T ∘
symm) e` is bounded by `N · Bnorm²` times the finite double sum of
`‖iteratedFDeriv 2 (raw_IJ ∘ symm) e‖²`. -/
lemma iteratedFDeriv_two_repr_opNormSq_le_sum_iteratedFDeriv_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {e : E}
    (he : e ∈ (extChartAt I α).target) :
    ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        e‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) e‖ ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  set b : M := (extChartAt I α).symm e with hb_def
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target he
  have hb_chart : b ∈ (chartAt H α).source := by
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  have he_eq : extChartAt I α b = e := (extChartAt I α).right_inv he
  have hbasis_le : ∀ Idx Jdx, ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ ≤ Bnorm := by
    intro Idx Jdx
    exact tensorChartBasisElement_norm_le (E := E) r s Idx Jdx
  have h_lin :=
    iteratedFDeriv_two_tensorRepr_opNorm_le_sum_iteratedFDeriv_components
      (I := I) (M := M) g r s T α (b := b) hb_chart
  rw [he_eq] at h_lin
  have h_rhs_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ *
              ‖tensorChartBasisElement (E := E) r s Idx Jdx‖) ≤
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact mul_le_mul_of_nonneg_left (hbasis_le Idx Jdx) (norm_nonneg _)
  have h_norm_le : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ Idx, ∑ Jdx,
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := h_lin.trans h_rhs_le
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_sum_pair_eq :
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)]
  have h_sum_nn :
      0 ≤ (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      ‖iteratedFDeriv ℝ 2
        (tensorChartComponentRaw (I := I) (M := M) g r s T α
          p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_le' : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [← h_sum_pair_eq] at h_norm_le; exact h_norm_le
  have h_norm_sq : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ((∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 := by
    have := mul_le_mul h_norm_le' h_norm_le' (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  have hCS :
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p =>
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by simp
    rw [h_sum_one] at hbase
    exact hbase
  have h_combined : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 *
        ∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have h_sq_eq : ((∑ p ∈ V,
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 = (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    calc ‖iteratedFDeriv ℝ 2
            (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ (∑ p ∈ V,
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * (∑ p ∈ V,
              ‖iteratedFDeriv ℝ 2
                (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) * Bnorm ^ 2 := h_mul
      _ = (V.card : ℝ) * Bnorm ^ 2 *
            ∑ p ∈ V,
              ‖iteratedFDeriv ℝ 2
                (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by ring
  have h_pair_to_nest :
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2)]
  rw [h_pair_to_nest] at h_combined
  exact h_combined

/-- The chart-pulled POU iterated-Fréchet-derivative (order 2) is uniformly
bounded on `(extChartAt I α).target` (and globally on `E`, since the
chart-pushed POU `chartPouEucl` is `ContDiff ℝ ∞` with compact support).

We use the chain-rule decomposition `iteratedFDeriv 2 (chartPouEucl ∘ toEucl)
e = (composition with toEucl twice)` to transfer the bound from EuclN to E. -/
private lemma exists_chartPouEucl_iteratedFDeriv_two_uniform_bound (α : M) :
    ∃ K_pou2 : ℝ, 0 ≤ K_pou2 ∧
      ∀ y : EuclN, ‖iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) y‖ ≤ K_pou2 := by
  classical
  have hCD : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have hHCS : HasCompactSupport (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_hasCompactSupport (I := I) (M := M) α
  have h_iter_cont : Continuous (fun y : EuclN =>
      iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) y) := by
    have hm : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact hCD.continuous_iteratedFDeriv hm
  have h_iter_compactSupport : HasCompactSupport (fun y : EuclN =>
      iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) y) :=
    hHCS.iteratedFDeriv 2
  obtain ⟨K_raw, hK_bound⟩ := h_iter_cont.bounded_above_of_compact_support
    h_iter_compactSupport
  refine ⟨max K_raw 0, le_max_right _ _, ?_⟩
  intro y
  exact le_trans (hK_bound y) (le_max_left _ _)

/-- The chart-pulled POU function (composed with `(extChartAt I α).symm`) has a
uniformly bounded `iteratedFDeriv 2` on `(extChartAt I α).target`.

The proof: the function equals `chartPouEucl ∘ toEucl` on the chart target
(via `chartPouEucl_toEuclidean_eq_pou_symm`). Since `chartPouEucl` is `ContDiff
ℝ ∞` and `toEucl` is a continuous linear equivalence (in particular `ContDiff
ℝ ∞`), the chain rule gives `‖iteratedFDeriv 2 (chartPouEucl ∘ toEucl) e‖ ≤
‖iteratedFDeriv 2 chartPouEucl (toEucl e)‖ · NtoE²` (since `toEucl` is linear,
so `iteratedFDeriv toEucl` is `toEucl` itself at order 1 and 0 at higher
orders). We use `ContinuousLinearMap.iteratedFDeriv_comp_left` (composition
with a CLM) to derive this bound. -/
private lemma exists_pou_symm_iteratedFDeriv_two_uniform_bound (α : M) :
    ∃ K_pou2 : ℝ, 0 ≤ K_pou2 ∧
      ∀ e ∈ (extChartAt I α).target,
        ‖iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ≤ K_pou2 := by
  classical
  obtain ⟨K_eucl, hK_nn, hK_bound⟩ :=
    exists_chartPouEucl_iteratedFDeriv_two_uniform_bound (I := I) (M := M) α
  let toEucl_CLM : E →L[ℝ] EuclN := (toEuclidean (E := E) : E →L[ℝ] EuclN)
  set NtoE : ℝ := ‖toEucl_CLM‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  have hCD_pou : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  refine ⟨K_eucl * NtoE ^ 2, mul_nonneg hK_nn (sq_nonneg _), ?_⟩
  intro e he
  have h_eventuallyEq :
      (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e')) =ᶠ[nhds e]
        (fun e' : E => chartPouEucl (I := I) (M := M) α (toEucl_CLM e')) :=
    pou_symm_eventuallyEq_chartPouEucl_toEuclidean (I := I) (M := M) α he
  have h_iter_eq : iteratedFDeriv ℝ 2
      (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e')) e =
        iteratedFDeriv ℝ 2
          (fun e' : E => chartPouEucl (I := I) (M := M) α (toEucl_CLM e')) e :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ h_eventuallyEq 2).eq_of_nhds
  rw [h_iter_eq]
  have h_comp_eq :
      iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α ∘ toEucl_CLM) e =
        ContinuousMultilinearMap.compContinuousLinearMap
          (iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) (toEucl_CLM e))
          (fun _ : Fin 2 => toEucl_CLM) :=
    toEucl_CLM.iteratedFDeriv_comp_right hCD_pou e h2_le
  have h_fn_eq : (fun e' : E => chartPouEucl (I := I) (M := M) α (toEucl_CLM e')) =
      chartPouEucl (I := I) (M := M) α ∘ toEucl_CLM := rfl
  rw [h_fn_eq, h_comp_eq]
  have h_norm_bound :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (g := iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) (toEucl_CLM e))
      (fun _ : Fin 2 => toEucl_CLM)
  have h_prod_eq : ∏ _i : Fin 2, ‖toEucl_CLM‖ = ‖toEucl_CLM‖ ^ 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_prod_eq] at h_norm_bound
  refine h_norm_bound.trans ?_
  have hK_eval : ‖iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α)
      (toEucl_CLM e)‖ ≤ K_eucl := hK_bound _
  calc ‖iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α)
            (toEucl_CLM e)‖ * NtoE ^ 2
      ≤ K_eucl * NtoE ^ 2 :=
        mul_le_mul_of_nonneg_right hK_eval (sq_nonneg _)

/-- **Order-2 pointwise scaled bound.** On the chart target, the POU²-scaled
squared chart-pulled-repr iterated-Fréchet-derivative norm (order 2) is bounded
by `C1` times the sum of squared `iteratedFDeriv 2` norms of `(POU·raw_IJ) ∘
symm`, plus `C2` times the sum of squared raw component values at
`(extChartAt I α).symm e`, plus `C3` times the sum of `‖fderiv POU∘symm‖² ·
‖fderiv raw_IJ∘symm‖²`. -/
lemma pou_sq_iteratedFDeriv_two_repr_sq_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (K_pou2 : ℝ) (_hK_pou2_nn : 0 ≤ K_pou2)
    (hK_pou2_bound : ∀ e ∈ (extChartAt I α).target,
      ‖iteratedFDeriv ℝ 2
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ≤ K_pou2)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm e)) ^ 2) *
      (‖iteratedFDeriv ℝ 2
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (3 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖iteratedFDeriv ℝ 2
                (fun e' : E =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                    ((extChartAt I α).symm e') *
                  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e')) e‖ ^ 2 +
        (3 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
          (tensorChartBasisNormConstant (E := E) r s) ^ 2 * K_pou2 ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 +
        (12 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
          (tensorChartBasisNormConstant (E := E) r s) ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖fderiv ℝ
                (fun e' : E =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                    ((extChartAt I α).symm e')) e‖ ^ 2 *
              ‖fderiv ℝ
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) e‖ ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ)
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e)
  have hρ_nn : 0 ≤ ρ := by
    have := (chartAtlasPOU I M).nonneg α ((extChartAt I α).symm e); exact this
  have hρ_abs : |ρ| = ρ := abs_of_nonneg hρ_nn
  have h_sq := iteratedFDeriv_two_repr_opNormSq_le_sum_iteratedFDeriv_components_sq
    (I := I) (M := M) g r s T α (e := e) he
  have h_scaled : ρ ^ 2 *
      ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
  have h_per_IJ : ∀ Idx Jdx,
      ρ ^ 2 * ‖iteratedFDeriv ℝ 2
        (tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
        3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2 := by
    intro Idx Jdx
    have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
    have hP_cd : ContDiffAt ℝ 2 (fun e' : E =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e := by
      have hcd_on := chartAtlasPOU_symm_contDiffOn_target (I := I) (M := M) α
      have hcd_at_inf : ContDiffAt ℝ ∞ (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e :=
        (hcd_on _ he).contDiffAt (h_open.mem_nhds he)
      have h2_le_inf : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
        exact (WithTop.coe_le_coe.mpr h1 : _)
      exact hcd_at_inf.of_le (by exact_mod_cast h2_le_inf)
    have hR_cd : ContDiffAt ℝ 2 (fun e' : E =>
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e')) e := by
      have hcd_on := tensorChartComponentRaw_symm_contDiffOn_target
        (I := I) (M := M) g r s T α Idx Jdx
      have hcd_at_inf : ContDiffAt ℝ ∞ (fun e' : E =>
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e :=
        (hcd_on _ he).contDiffAt (h_open.mem_nhds he)
      have h2_le_inf : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
        exact (WithTop.coe_le_coe.mpr h1 : _)
      exact hcd_at_inf.of_le (by exact_mod_cast h2_le_inf)
    set P := fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e') with hP_def
    set R := fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e') with hR_def
    have h_leibniz := scalar_iteratedFDeriv_two_mul_norm_le P R hP_cd hR_cd
    have hPe : P e = ρ := rfl
    set raw_val : ℝ := R e with hraw_def
    have hraw_eq : raw_val = tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e) := rfl
    rw [hPe] at h_leibniz
    rw [hρ_abs] at h_leibniz
    have h_sq_ineq : (ρ * ‖iteratedFDeriv ℝ 2 R e‖) ^ 2 ≤
        3 * (‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ ^ 2 +
            (|raw_val| * ‖iteratedFDeriv ℝ 2 P e‖) ^ 2 +
            (2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖) ^ 2) := by
      set a : ℝ := ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖
      set b : ℝ := |raw_val| * ‖iteratedFDeriv ℝ 2 P e‖
      set c : ℝ := 2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hb_nn : 0 ≤ b := mul_nonneg (abs_nonneg _) (norm_nonneg _)
      have hc_nn : 0 ≤ c := by positivity
      have hρR_nn : 0 ≤ ρ * ‖iteratedFDeriv ℝ 2 R e‖ :=
        mul_nonneg hρ_nn (norm_nonneg _)
      have h_lhs_le : ρ * ‖iteratedFDeriv ℝ 2 R e‖ ≤ a + b + c := by
        change ρ * ‖iteratedFDeriv ℝ 2 R e‖ ≤
          ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ +
            |raw_val| * ‖iteratedFDeriv ℝ 2 P e‖ + 2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖
        have h_temp : ρ * ‖iteratedFDeriv ℝ 2 R e‖ ≤
          ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ +
            |raw_val| * ‖iteratedFDeriv ℝ 2 P e‖ +
            2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖ := h_leibniz
        exact h_temp
      have h_sq_le : (ρ * ‖iteratedFDeriv ℝ 2 R e‖) ^ 2 ≤ (a + b + c) ^ 2 :=
        pow_le_pow_left₀ hρR_nn h_lhs_le 2
      have h_expand : (a + b + c) ^ 2 ≤ 3 * (a^2 + b^2 + c^2) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a+b-c)]
      exact le_trans h_sq_le h_expand
    have hρ_R_sq : ρ ^ 2 * ‖iteratedFDeriv ℝ 2 R e‖ ^ 2 =
        (ρ * ‖iteratedFDeriv ℝ 2 R e‖) ^ 2 := by ring
    change ρ ^ 2 * ‖iteratedFDeriv ℝ 2 R e‖ ^ 2 ≤ _
    rw [hρ_R_sq]
    refine h_sq_ineq.trans ?_
    have h_a_sq : ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ ^ 2 =
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e')) e‖ ^ 2 := by rfl
    have h_b_sq : (|raw_val| * ‖iteratedFDeriv ℝ 2 P e‖) ^ 2 =
        raw_val ^ 2 * ‖iteratedFDeriv ℝ 2 P e‖ ^ 2 := by
      rw [mul_pow, sq_abs]
    have h_c_sq : (2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖) ^ 2 =
        4 * ‖fderiv ℝ P e‖ ^ 2 * ‖fderiv ℝ R e‖ ^ 2 := by ring
    rw [h_a_sq, h_b_sq, h_c_sq]
    have h_P_def : ‖iteratedFDeriv ℝ 2 P e‖ ^ 2 =
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 := by rfl
    have h_P_fderiv_def : ‖fderiv ℝ P e‖ ^ 2 =
        ‖fderiv ℝ
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 := by rfl
    have h_R_fderiv_def : ‖fderiv ℝ R e‖ ^ 2 =
        ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 := by rfl
    have h_raw_def : raw_val ^ 2 = (tensorChartComponentRaw (I := I) (M := M)
        g r s T α Idx Jdx ((extChartAt I α).symm e)) ^ 2 := by rw [hraw_eq]
    rw [h_P_def, h_P_fderiv_def, h_R_fderiv_def, h_raw_def]
    linarith
  refine le_trans h_scaled ?_
  have h_distrib : ρ ^ 2 * (N * Bnorm ^ 2 *
      ∑ Idx, ∑ Jdx,
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) =
      (N * Bnorm ^ 2) *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    rw [show (∑ Idx, ∑ Jdx,
        ρ ^ 2 * ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) =
          ρ ^ 2 * ∑ Idx, ∑ Jdx,
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [Finset.mul_sum]]
    ring
  rw [h_distrib]
  have hNBsq_nn : 0 ≤ N * Bnorm ^ 2 :=
    mul_nonneg hN_nn (sq_nonneg _)
  have h_sum_bound :
      ∑ Idx, ∑ Jdx,
        ρ ^ 2 * ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ∑ Idx, ∑ Jdx,
        (3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) := by
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact h_per_IJ Idx Jdx
  have h_mul_le : (N * Bnorm ^ 2) *
      ∑ Idx, ∑ Jdx,
        ρ ^ 2 * ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      (N * Bnorm ^ 2) * ∑ Idx, ∑ Jdx,
        (3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_sum_bound hNBsq_nn
  refine le_trans h_mul_le ?_
  have hP_fderiv2_bound :
      ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 ≤ K_pou2 ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hK_pou2_bound e he) 2
  have h_sum_split :
      ∑ Idx, ∑ Jdx,
        (3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) =
      (∑ Idx, ∑ Jdx,
        3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2) +
      (∑ Idx, ∑ Jdx,
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2) +
      (∑ Idx, ∑ Jdx,
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) := by
    rw [Finset.sum_congr rfl (fun Idx _ =>
      show (∑ Jdx, _) = _ from by rw [Finset.sum_add_distrib, Finset.sum_add_distrib])]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [h_sum_split]
  have h_factor3_a : (∑ Idx, ∑ Jdx,
      3 * ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e') *
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e')) e‖ ^ 2) =
      3 * ∑ Idx, ∑ Jdx,
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e')) e‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    rw [Finset.mul_sum]
  have h_factor3_b_inner : (∑ Idx, ∑ Jdx,
      3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e)) ^ 2 *
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2) ≤
      3 * K_pou2 ^ 2 * ∑ Idx, ∑ Jdx,
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e)) ^ 2 := by
    rw [show (3 : ℝ) * K_pou2 ^ 2 = 3 * K_pou2 ^ 2 from rfl]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    have hsq_raw_nn : 0 ≤ (tensorChartComponentRaw (I := I) (M := M)
        g r s T α Idx Jdx ((extChartAt I α).symm e)) ^ 2 := sq_nonneg _
    have hbound :
      3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e)) ^ 2 *
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 ≤
      3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e)) ^ 2 * K_pou2 ^ 2 := by
      have h3raw_nn : 0 ≤ 3 * (tensorChartComponentRaw (I := I) (M := M)
          g r s T α Idx Jdx ((extChartAt I α).symm e)) ^ 2 :=
        mul_nonneg (by norm_num) hsq_raw_nn
      exact mul_le_mul_of_nonneg_left hP_fderiv2_bound h3raw_nn
    linarith [hbound]
  have h_factor3_c : (∑ Idx, ∑ Jdx,
      12 * ‖fderiv ℝ
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 *
        ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2) =
      12 * ∑ Idx, ∑ Jdx,
        ‖fderiv ℝ
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 *
        ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    ring
  rw [h_factor3_a, h_factor3_c]
  set A := ∑ Idx, ∑ Jdx,
    ‖iteratedFDeriv ℝ 2
      (fun e' : E =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e') *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e')) e‖ ^ 2 with hA_def
  set B_old := ∑ Idx, ∑ Jdx,
    3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e)) ^ 2 *
      ‖iteratedFDeriv ℝ 2
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ^ 2 with hB_def
  set RawSum := ∑ Idx, ∑ Jdx,
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
      ((extChartAt I α).symm e)) ^ 2 with hRawSum_def
  set C := ∑ Idx, ∑ Jdx,
    ‖fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ^ 2 *
    ‖fderiv ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e‖ ^ 2 with hC_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hB_nn : 0 ≤ B_old := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)))
  have hRawSum_nn : 0 ≤ RawSum := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hB_le : B_old ≤ 3 * K_pou2 ^ 2 * RawSum := h_factor3_b_inner
  have hgoal : (N * Bnorm ^ 2) * (3 * A + B_old + 12 * C) ≤
      (3 * N * Bnorm ^ 2) * A +
      (3 * N * Bnorm ^ 2 * K_pou2 ^ 2) * RawSum +
      (12 * N * Bnorm ^ 2) * C := by
    have h1 : (N * Bnorm ^ 2) * (3 * A + B_old + 12 * C) =
        (N * Bnorm ^ 2) * (3 * A) + (N * Bnorm ^ 2) * B_old +
        (N * Bnorm ^ 2) * (12 * C) := by ring
    rw [h1]
    have hnb_nn : 0 ≤ N * Bnorm ^ 2 := hNBsq_nn
    have h_b_mul : (N * Bnorm ^ 2) * B_old ≤
        (N * Bnorm ^ 2) * (3 * K_pou2 ^ 2 * RawSum) :=
      mul_le_mul_of_nonneg_left hB_le hnb_nn
    have h_eq1 : (N * Bnorm ^ 2) * (3 * A) = (3 * N * Bnorm ^ 2) * A := by ring
    have h_eq2 : (N * Bnorm ^ 2) * (3 * K_pou2 ^ 2 * RawSum) =
        (3 * N * Bnorm ^ 2 * K_pou2 ^ 2) * RawSum := by ring
    have h_eq3 : (N * Bnorm ^ 2) * (12 * C) = (12 * N * Bnorm ^ 2) * C := by ring
    linarith [h_b_mul]
  have h_final :
    (N * Bnorm ^ 2) *
      ((3 : ℝ) * (∑ Idx, ∑ Jdx,
            ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2) +
        (∑ Idx, ∑ Jdx,
          (3 : ℝ) * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 *
            ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2) +
        (12 : ℝ) * (∑ Idx, ∑ Jdx,
            ‖fderiv ℝ
                (fun e' : E =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                    ((extChartAt I α).symm e')) e‖ ^ 2 *
            ‖fderiv ℝ
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) e‖ ^ 2)) ≤
      ((3 : ℝ) * N * Bnorm ^ 2) * A +
      ((3 : ℝ) * N * Bnorm ^ 2 * K_pou2 ^ 2) * RawSum +
      ((12 : ℝ) * N * Bnorm ^ 2) * C := by
    convert hgoal using 2
  exact h_final

/-- **Order-2 chart-target POU-weighted L² bound for the second iterated
Fréchet derivative of the chart-pulled tensor representation by chart-component
data.** For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`,
and a chart base point `α : M`, there is a non-negative constant `K` (depending
only on `(g, r, s, α)` and the model space; independent of `T`) such that for
every smooth compactly-supported `(r, s)`-tensor section `T`, the chart-target
Lebesgue integral of the partition-of-unity-weighted squared operator norm of
`iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr r s α T.toSection ∘
(extChartAt I α).symm)` is bounded by `K` times the sum of three pieces:

* the sum of the chart-target Lebesgue integrals of the squared iterated
  Fréchet-derivative norms of the POU-weighted chart-frame scalar components
  (this piece is the principal contribution; it is bounded above by the
  squared `wkpNorm 2 2` of `tensorChartComp_IJ` modulo a constant factor that
  is absorbed into `K`),
* the sum of the squared `L²`-norms over the chart target of the chart-pulled
  Fréchet derivatives of the raw scalar components (first Leibniz correction),
* the sum of the squared `L²`-norms over the chart target of the chart-pulled
  raw scalar components themselves (second Leibniz correction).

The two correction terms are deferred to cross-chart aggregation. The proof
combines the order-2 squared basis decomposition, the order-2 scalar Leibniz
inequality, the uniform bound on the chart-pulled POU iteratedFDeriv 2, and
the `(a+b+c)² ≤ 3(a²+b²+c²)` algebraic inequality, integrated against the
chart-target restriction measure. -/
theorem chartTargetPouWeightedL2NormSq_iteratedFDeriv_two_repr_le_sum_chartComp_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖iteratedFDeriv ℝ 2
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                      ENNReal.ofReal
                        (‖iteratedFDeriv ℝ 2
                          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                              ((extChartAt I α).symm e') *
                            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                              ((extChartAt I α).symm e'))
                          ((toEuclidean (E := E)).symm y)‖ ^ 2)
                      ∂(volume : Measure EuclN)) +
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                      ENNReal.ofReal
                        (‖fderiv ℝ
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2)
                      ∂(volume : Measure EuclN)) +
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                      ENNReal.ofReal
                        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
                      ∂(volume : Measure EuclN))) := by
  classical
  obtain ⟨K_pou2, hK_pou2_nn, hK_pou2_bound⟩ :=
    exists_pou_symm_iteratedFDeriv_two_uniform_bound (I := I) (M := M) α
  obtain ⟨K_pou1, hK_pou1_nn, hK_pou1_bound⟩ :=
    exists_pou_symm_fderiv_uniform_bound (I := I) (M := M) α
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set C1 : ℝ := 3 * N * Bnorm ^ 2 with hC1_def
  set C2 : ℝ := 3 * N * Bnorm ^ 2 * K_pou2 ^ 2 with hC2_def
  set C3 : ℝ := 12 * N * Bnorm ^ 2 * K_pou1 ^ 2 with hC3_def
  have hC1_nn : 0 ≤ C1 := by
    refine mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _); norm_num
  have hC2_nn : 0 ≤ C2 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    norm_num
  have hC3_nn : 0 ≤ C3 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    norm_num
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro T
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖iteratedFDeriv ℝ 2
            (tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2) with hlhs_def
  set wIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        (‖iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'))
          ((toEuclidean (E := E)).symm y)‖ ^ 2)
  set fIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        (‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2)
  set rIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
        ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) +
        ENNReal.ofReal C3 * (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y) := by
    intro y hy
    set e : E := (toEuclidean (E := E)).symm y with he_def
    have he_target : e ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_real := pou_sq_iteratedFDeriv_two_repr_sq_pointwise
      (I := I) (M := M) g r s T α K_pou2 hK_pou2_nn hK_pou2_bound (e := e) he_target
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e) with hρ_def
    have hρ_sym : ρ = (chartAtlasPOU I M α : M → ℝ) (sym y) := by
      simp [hρ_def, hsym_def, he_def]
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    set FRsq : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 with hFRsq_def
    set wSum : ℝ := ∑ Idx, ∑ Jdx,
      ‖iteratedFDeriv ℝ 2
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e‖ ^ 2 with hwSum_def
    have hwSum_nn : 0 ≤ wSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    set rSum : ℝ := ∑ Idx, ∑ Jdx,
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm e)) ^ 2 with hrSum_def
    have hrSum_nn : 0 ≤ rSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    set fSum_raw : ℝ := ∑ Idx, ∑ Jdx,
      ‖fderiv ℝ
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 *
      ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 with hfSum_raw_def
    have hfSum_raw_nn : 0 ≤ fSum_raw :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
        (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    have h_real' : ρ ^ 2 * FRsq ≤ C1 * wSum + C2 * rSum + (12 * N * Bnorm ^ 2) * fSum_raw := by
      simpa [ρ, FRsq, wSum, rSum, fSum_raw, C1, C2, Bnorm, N,
        hC1_def, hC2_def, hBnorm_def, hN_def] using h_real
    have hK_pou1_e : ‖fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ≤ K_pou1 := hK_pou1_bound e he_target
    have hK_pou1_e_sq : ‖fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ^ 2 ≤ K_pou1 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hK_pou1_e 2
    have h_fSum_raw_le : fSum_raw ≤ K_pou1 ^ 2 *
        (∑ Idx, ∑ Jdx,
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun Idx _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun Jdx _ => ?_)
      have hsq_raw_nn : 0 ≤ ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hK_pou1_e_sq hsq_raw_nn
    set fdSum : ℝ := ∑ Idx, ∑ Jdx,
      ‖fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
          (extChartAt I α).symm) e‖ ^ 2 with hfdSum_def
    have hfdSum_nn : 0 ≤ fdSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have h_NB12_nn : 0 ≤ 12 * N * Bnorm ^ 2 := by
      refine mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _); norm_num
    have h_real'' : ρ ^ 2 * FRsq ≤ C1 * wSum + C2 * rSum + C3 * fdSum := by
      have h := h_real'
      have h_step : (12 * N * Bnorm ^ 2) * fSum_raw ≤
          (12 * N * Bnorm ^ 2) * (K_pou1 ^ 2 * fdSum) :=
        mul_le_mul_of_nonneg_left h_fSum_raw_le h_NB12_nn
      have h_eq : (12 * N * Bnorm ^ 2) * (K_pou1 ^ 2 * fdSum) = C3 * fdSum := by
        rw [hC3_def]; ring
      linarith
    have h_LHS_eq : lhsIntegrand y = ENNReal.ofReal (ρ ^ 2 * FRsq) := by
      simp only [hlhs_def, ← hρ_sym, FRsq]
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_LHS_eq]
    have h_C1w_nn : 0 ≤ C1 * wSum := mul_nonneg hC1_nn hwSum_nn
    have h_C2r_nn : 0 ≤ C2 * rSum := mul_nonneg hC2_nn hrSum_nn
    have h_C3fd_nn : 0 ≤ C3 * fdSum := mul_nonneg hC3_nn hfdSum_nn
    have h_step1 :
        ENNReal.ofReal (ρ ^ 2 * FRsq) ≤
          ENNReal.ofReal (C1 * wSum + C2 * rSum + C3 * fdSum) :=
      ENNReal.ofReal_le_ofReal h_real''
    refine le_trans h_step1 ?_
    rw [ENNReal.ofReal_add (add_nonneg h_C1w_nn h_C2r_nn) h_C3fd_nn]
    rw [ENNReal.ofReal_add h_C1w_nn h_C2r_nn]
    rw [ENNReal.ofReal_mul hC1_nn, ENNReal.ofReal_mul hC2_nn,
      ENNReal.ofReal_mul hC3_nn]
    have h_wSum_eq :
        ENNReal.ofReal wSum =
          ∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y := by
      simp only [hwSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    have h_rSum_eq :
        ENNReal.ofReal rSum =
          ∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y := by
      simp only [hrSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    have h_fdSum_eq :
        ENNReal.ofReal fdSum =
          ∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y := by
      simp only [hfdSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [h_wSum_eq, h_rSum_eq, h_fdSum_eq]
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have h_toEucl_symm_cont : Continuous ((toEuclidean (E := E)).symm) :=
    (toEuclidean (E := E)).symm.continuous
  have h_2le_inf : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have h_wInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (wIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    have hP_cd := chartAtlasPOU_symm_contDiffOn_target (I := I) (M := M) α
    have hR_cd := tensorChartComponentRaw_symm_contDiffOn_target
      (I := I) (M := M) g r s T α Idx Jdx
    have h_prod_cd : ContDiffOn ℝ ∞
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) (extChartAt I α).target :=
      hP_cd.mul hR_cd
    have h_iter_contOn : ContinuousOn
        (fun e' : E => iteratedFDeriv ℝ 2
          (fun e'' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e'') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'')) e') (extChartAt I α).target := by
      intro e' he'
      have h_cd_at : ContDiffAt ℝ 2
          (fun e'' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e'') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'')) e' :=
        ((h_prod_cd _ he').contDiffAt (h_open.mem_nhds he')).of_le
          (by exact_mod_cast h_2le_inf)
      exact (h_cd_at.continuousAt_iteratedFDeriv (k := 2) le_rfl).continuousWithinAt
    have h_iter_sym_contOn : ContinuousOn
        (fun y : EuclN => iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'))
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine h_iter_contOn.comp h_toEucl_symm_cont.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_norm_sym_ae : AEMeasurable
        (fun y : EuclN => ‖iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'))
          ((toEuclidean (E := E)).symm y)‖)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_iter_sym_contOn.norm.aemeasurable h_chartTarget_meas
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h_norm_sym_ae.pow_const 2)
  have h_fInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (fIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    have hR_cd := tensorChartComponentRaw_symm_contDiffOn_target
      (I := I) (M := M) g r s T α Idx Jdx
    have h_fderiv_contOn : ContinuousOn
        (fun e' : E => fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e') (extChartAt I α).target := by
      intro e' he'
      have h_cd_at : ContDiffAt ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e' :=
        ((hR_cd _ he').contDiffAt (h_open.mem_nhds he')).of_le
          (by exact_mod_cast h_2le_inf)
      exact (h_cd_at.continuousAt_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).continuousWithinAt
    have h_fderiv_sym_contOn : ContinuousOn
        (fun y : EuclN => fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine h_fderiv_contOn.comp h_toEucl_symm_cont.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_norm_sym_ae : AEMeasurable
        (fun y : EuclN => ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_fderiv_sym_contOn.norm.aemeasurable h_chartTarget_meas
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h_norm_sym_ae.pow_const 2)
  have h_rInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (rIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    exact raw_sym_sq_ofReal_aeMeasurable_restrict
      (I := I) (M := M) g r s T α Idx Jdx
  have h_innersum_aeMeas : ∀ (f : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞),
      (∀ Idx Jdx, AEMeasurable (f Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) →
      AEMeasurable (fun y : EuclN => ∑ Idx, ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro f hf
    have h_inner_ae : ∀ Idx, AEMeasurable
        (fun y : EuclN => ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx, fun y : EuclN => f Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => hf Idx Jdx)
      have h_eq : (∑ Jdx, fun y : EuclN => f Idx Jdx y) =
          (fun y : EuclN => ∑ Jdx, f Idx Jdx y) := by
        funext y; simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    have h_funsum_ae : AEMeasurable
        (∑ Idx, fun y : EuclN => ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      Finset.aemeasurable_sum _ (fun Idx _ => h_inner_ae Idx)
    have h_eq : (∑ Idx, fun y : EuclN => ∑ Jdx, f Idx Jdx y) =
        (fun y : EuclN => ∑ Idx, ∑ Jdx, f Idx Jdx y) := by
      funext y; simp [Finset.sum_apply]
    rwa [h_eq] at h_funsum_ae
  have h_wSum_aeMeas := h_innersum_aeMeas wIntegrand h_wInt_aeMeas
  have h_fSum_aeMeas := h_innersum_aeMeas fIntegrand h_fInt_aeMeas
  have h_rSum_aeMeas := h_innersum_aeMeas rIntegrand h_rInt_aeMeas
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
              ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) +
              ENNReal.ofReal C3 * (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y))
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  have h_split :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
            ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) +
            ENNReal.ofReal C3 * (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y))
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C1 *
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) ∂(volume : Measure EuclN)) +
        ENNReal.ofReal C2 *
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) ∂(volume : Measure EuclN)) +
        ENNReal.ofReal C3 *
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y) ∂(volume : Measure EuclN)) := by
    have h_C1_ae : AEMeasurable
        (fun y : EuclN => ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      AEMeasurable.const_mul h_wSum_aeMeas _
    have h_C2_ae : AEMeasurable
        (fun y : EuclN => ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      AEMeasurable.const_mul h_rSum_aeMeas _
    have h_C12_ae : AEMeasurable
        (fun y : EuclN =>
          ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
          ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_C1_ae.add h_C2_ae
    rw [lintegral_add_left' h_C12_ae]
    rw [lintegral_add_left' h_C1_ae]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [h_split] at h_int_mono
  have h_dist : ∀ (f : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞),
      (∀ Idx Jdx, AEMeasurable (f Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) →
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx, ∑ Jdx, f Idx Jdx y) ∂(volume : Measure EuclN) =
        ∑ Idx, ∑ Jdx,
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              f Idx Jdx y ∂(volume : Measure EuclN) := by
    intro f hf
    have h_inner_ae : ∀ Idx, AEMeasurable
        (fun y : EuclN => ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx, fun y : EuclN => f Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => hf Idx Jdx)
      have h_eq : (∑ Jdx, fun y : EuclN => f Idx Jdx y) =
          (fun y : EuclN => ∑ Jdx, f Idx Jdx y) := by
        funext y; simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    rw [lintegral_finset_sum' _ (fun Idx _ => h_inner_ae Idx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum' _ (fun Jdx _ => hf Idx Jdx)
  rw [h_dist wIntegrand h_wInt_aeMeas,
      h_dist rIntegrand h_rInt_aeMeas,
      h_dist fIntegrand h_fInt_aeMeas] at h_int_mono
  refine h_int_mono.trans ?_
  set Sw : ℝ≥0∞ := ∑ Idx, ∑ Jdx,
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        wIntegrand Idx Jdx y ∂(volume : Measure EuclN)
  set Sr : ℝ≥0∞ := ∑ Idx, ∑ Jdx,
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        rIntegrand Idx Jdx y ∂(volume : Measure EuclN)
  set Sf : ℝ≥0∞ := ∑ Idx, ∑ Jdx,
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        fIntegrand Idx Jdx y ∂(volume : Measure EuclN)
  have hC1_le : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C1 + C2 + C3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hC2_le : ENNReal.ofReal C2 ≤ ENNReal.ofReal (C1 + C2 + C3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hC3_le : ENNReal.ofReal C3 ≤ ENNReal.ofReal (C1 + C2 + C3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal C1 * Sw + ENNReal.ofReal C2 * Sr + ENNReal.ofReal C3 * Sf
      ≤ ENNReal.ofReal (C1 + C2 + C3) * Sw +
        ENNReal.ofReal (C1 + C2 + C3) * Sr +
        ENNReal.ofReal (C1 + C2 + C3) * Sf := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_left hC1_le Sw
        · exact mul_le_mul_left hC2_le Sr
        · exact mul_le_mul_left hC3_le Sf
    _ = ENNReal.ofReal (C1 + C2 + C3) * (Sw + Sf + Sr) := by ring
    _ = ENNReal.ofReal (C1 + C2 + C3) *
          ((∑ Idx, ∑ Jdx,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  wIntegrand Idx Jdx y ∂(volume : Measure EuclN)) +
            (∑ Idx, ∑ Jdx,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) +
            (∑ Idx, ∑ Jdx,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  rIntegrand Idx Jdx y ∂(volume : Measure EuclN))) := by rfl

/-- If `chartAt H α = chartAt H β`, the extended charts coincide. -/
private lemma extChartAt_eq_of_chartAt_eq
    {α β : M} (h_eq : chartAt H α = chartAt H β) :
    extChartAt I α = extChartAt I β := by
  simp only [extChartAt, h_eq]

/-- If `chartAt H α = chartAt H β`, then
`chartTargetEuclid α = chartTargetEuclid β`. -/
private lemma chartTargetEuclid_eq_of_chartAt_eq
    {α β : M} (h_eq : chartAt H α = chartAt H β) :
    chartTargetEuclid (I := I) (M := M) α =
      chartTargetEuclid (I := I) (M := M) β := by
  unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
  rw [extChartAt_eq_of_chartAt_eq (I := I) (M := M) h_eq]

/-- For a finite family of non-negative extended reals, `∑ a_i² ≤ (∑ a_i)²`. -/
private lemma sum_sq_le_sq_sum_finset
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ i ∈ s, (f i) ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  set S : ℝ≥0∞ := ∑ i ∈ s, f i with hS_def
  have hS_sq : S ^ 2 = S * S := sq S
  have hineq : ∀ i ∈ s, (f i) ^ 2 ≤ f i * S := by
    intro i hi
    have hi_le_S : f i ≤ S := Finset.single_le_sum
      (f := f) (fun _ _ => zero_le _) hi
    have hsq_eq : (f i) ^ 2 = f i * f i := sq (f i)
    rw [hsq_eq]
    exact mul_le_mul_of_nonneg_left hi_le_S (zero_le _)
  calc ∑ i ∈ s, (f i) ^ 2
      ≤ ∑ i ∈ s, f i * S := Finset.sum_le_sum hineq
    _ = (∑ i ∈ s, f i) * S := by rw [← Finset.sum_mul]
    _ = S * S := by rw [← hS_def]
    _ = S ^ 2 := hS_sq.symm

/-- For a countable family of non-negative extended reals, `∑' a_i² ≤ (∑' a_i)²`. -/
private lemma tsum_sq_le_sq_tsum_ennreal
    {ι : Type*} (f : ι → ℝ≥0∞) :
    ∑' i, (f i) ^ 2 ≤ (∑' i, f i) ^ 2 := by
  classical
  set S : ℝ≥0∞ := ∑' i, f i with hS_def
  have h_le : ∀ i, f i ≤ S := fun i => ENNReal.le_tsum i
  have h_pointwise : ∀ i, (f i) ^ 2 ≤ f i * S := by
    intro i
    have hsq : (f i) ^ 2 = f i * f i := sq (f i)
    rw [hsq]
    exact mul_le_mul_of_nonneg_left (h_le i) (zero_le _)
  calc ∑' i, (f i) ^ 2
      ≤ ∑' i, f i * S :=
        ENNReal.tsum_le_tsum h_pointwise
    _ = (∑' i, f i) * S := by rw [ENNReal.tsum_mul_right]
    _ = S * S := by rw [← hS_def]
    _ = S ^ 2 := (sq S).symm

/-- For each `α` in a finset of charts and each component multi-index `(Idx, Jdx)`,
the square of `wkpNorm 0 2 (tensorChartComp α Idx Jdx)` (on the chart target) is
bounded by `(wtwokTwoNorm g 1 T)^2`. This is the per-chart contribution to the
overall `wtwokTwoNorm` square bound. -/
private lemma wkpNorm_zero_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (wkpNorm (d := Module.finrank ℝ E) 0 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  have h01 : wkpNorm (d := Module.finrank ℝ E) 0 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have : (0 : ℕ) ≤ 2 * 1 := by norm_num
    simpa using wkpNorm_mono_order (d := Module.finrank ℝ E)
      this
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α)
  have h_α : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := by
    unfold wtwokTwoNorm
    have h_term : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
              (chartTargetEuclid (I := I) (M := M) α) := by
      calc wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)
          ≤ ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Jdx' : Fin s → Fin (Module.finrank ℝ E) =>
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                  (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
        _ ≤ ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                  (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Idx' : Fin r → Fin (Module.finrank ℝ E) =>
                ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                    (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Idx)
    refine h_term.trans ?_
    exact ENNReal.le_tsum α
  have h_combined : wkpNorm (d := Module.finrank ℝ E) 0 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := h01.trans h_α
  exact pow_le_pow_left' h_combined 2

/-- The finset sum `∑_α ∑_IJ (wkpNorm 0 2 of tensorChartComp α IJ)²` over
`chartAtlasPOU_finset` is bounded by `|finset| · cardIdx · cardJdx ·
(wtwokTwoNorm g 1 T)²`. -/
private lemma finset_sum_wkpNorm_zero_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
        ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  have h_bound : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        ∀ Jdx ∈ (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤ W := by
    intro α _ Idx _ Jdx _
    exact wkpNorm_zero_sq_le_wtwokTwoNorm_sq (I := I) (M := M)
      g r s T α Idx Jdx
  have h_step1 :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (wkpNorm (d := Module.finrank ℝ E) 0 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W := by
    refine Finset.sum_le_sum (fun α hα => ?_)
    refine Finset.sum_le_sum (fun Idx hIdx => ?_)
    refine Finset.sum_le_sum (fun Jdx hJdx => ?_)
    exact h_bound α hα Idx hIdx Jdx hJdx
  refine h_step1.trans ?_
  have h_inner_eq : ∀ _α : M,
      (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
        ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          (((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
              W) := by
    intro _α
    have h_inner :
        (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
        ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
            W := by
      refine Finset.sum_congr rfl (fun _ _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h_inner, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr (rfl :
    chartAtlasPOU_finset (I := I) (M := M) = chartAtlasPOU_finset (I := I) (M := M))
    (fun α _ => h_inner_eq α)]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
        (((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          (((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
              W)) =
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
        ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
            W from by ring]

/-- Same as `wkpNorm_zero_sq_le_wtwokTwoNorm_sq` but for `wkpNorm 1 2`. -/
private lemma wkpNorm_one_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (wkpNorm (d := Module.finrank ℝ E) 1 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  have h12 : wkpNorm (d := Module.finrank ℝ E) 1 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have : (1 : ℕ) ≤ 2 * 1 := by norm_num
    exact wkpNorm_mono_order (d := Module.finrank ℝ E) this _ _
  have h_α : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := by
    unfold wtwokTwoNorm
    have h_term : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
              (chartTargetEuclid (I := I) (M := M) α) := by
      calc wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)
          ≤ ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Jdx' : Fin s → Fin (Module.finrank ℝ E) =>
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                  (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
        _ ≤ ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                  (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Idx' : Fin r → Fin (Module.finrank ℝ E) =>
                ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                    (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Idx)
    refine h_term.trans ?_
    exact ENNReal.le_tsum α
  exact pow_le_pow_left' (h12.trans h_α) 2

/-- Same as `wkpNorm_zero_sq_le_wtwokTwoNorm_sq` but for `wkpNorm 2 2`. -/
private lemma wkpNorm_two_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (wkpNorm (d := Module.finrank ℝ E) 2 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  have h_eq : (2 : ℕ) = 2 * 1 := by norm_num
  rw [h_eq]
  have h_α : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := by
    unfold wtwokTwoNorm
    have h_term : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
              (chartTargetEuclid (I := I) (M := M) α) := by
      calc wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)
          ≤ ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Jdx' : Fin s → Fin (Module.finrank ℝ E) =>
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                  (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
        _ ≤ ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                  (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Idx' : Fin r → Fin (Module.finrank ℝ E) =>
                ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                    (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Idx)
    refine h_term.trans ?_
    exact ENNReal.le_tsum α
  exact pow_le_pow_left' h_α 2

/-- When `chartAt H α = chartAt H β`, the tangent trivialisations at `α` and `β`
applied at `b` coincide. -/
private lemma tangent_continuousLinearMapAt_eq_of_chartAt_eq
    {α β : M} (h_chart : chartAt H α = chartAt H β) (b : M)
    (hb_α : b ∈ (chartAt H α).source) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b =
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b := by
  classical
  have hb_β : b ∈ (chartAt H β).source := by rw [← h_chart]; exact hb_α
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ) (I := I) hb_α]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ) (I := I) hb_β]
  congr 1
  exact Subtype.ext h_chart

/-- Cauchy-Schwarz for a finset sum of reals: `(Σ f i)² ≤ #s · Σ (f i)²`. -/
private lemma finset_sum_sq_le_card_mul_sum_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  classical
  have hbase := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun _ : ι => (1 : ℝ)) f
  simp only [one_mul, one_pow] at hbase
  have h_sum_one : (∑ _i ∈ s, (1 : ℝ)) = (s.card : ℝ) := by simp
  rw [h_sum_one] at hbase
  exact hbase

/-- **Chart-transition law via POU tsupport.** For any two chart base points
`α, β : M` whose POU `tsupport`s both contain a point `b`, the raw chart-frame
scalar component of a smooth compactly-supported tensor section `T` at `α` and
multi-index `(Idx, Jdx)` equals the finite sum over component multi-indices `Q`
of `transitionCoeff r s β α ⟨Idx, Jdx⟩ Q b · raw component of T at β, Q b`. -/
private lemma tensorChartComponentRaw_chartTransition_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β b : M)
    (hb_α_pou : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb_β_pou : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b =
      ∑ Q : TensorCompIdx (E := E) r s,
        transitionCoeff (E := E) (I := I) (M := M) r s β α ⟨Idx, Jdx⟩ Q b *
          tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b := by
  classical
  have hsupp_α :
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
        (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  have hsupp_β :
      tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
        (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β
  have hb_α_src : b ∈ (chartAt H α).source := hsupp_α hb_α_pou
  have hb_β_src : b ∈ (chartAt H β).source := hsupp_β hb_β_pou
  exact tensorChartComponentRaw_eq_transitionCoeff_sum
    (E := E) (I := I) (M := M) g r s T β α ⟨Idx, Jdx⟩ ⟨hb_β_src, hb_α_src⟩

/-- **Squared chart-transition bound via POU tsupport.** Under the same POU
`tsupport` overlap, the squared raw chart-frame scalar component at `α` is
bounded by `N_idx · K² · Σ_Q (raw β Q b)²`, where `N_idx` is the cardinality
of the component multi-index type and `K` is any uniform `transitionCoeff`
bound on the relevant POU-`tsupport` overlap (in particular, the universal
constant from `transitionCoeff_le_uniform_on_pouTsupport`). The Cauchy-Schwarz
factor `N_idx` is the squared-finset cost of distributing the sum over `Q`. -/
private lemma tensorChartComponentRaw_sq_chartTransition_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (K : ℝ)
    (hK_bound :
      ∀ γ α : M,
        ∀ P₀ Q : TensorCompIdx (E := E) r s,
        ∀ b : M,
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ K)
    (α β b : M)
    (hb_α_pou : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb_β_pou : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 ≤
      ((Finset.univ : Finset (TensorCompIdx (E := E) r s)).card : ℝ) *
        K ^ 2 *
        ∑ Q : TensorCompIdx (E := E) r s,
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by
  classical
  rw [tensorChartComponentRaw_chartTransition_eq
    (I := I) (M := M) g r s T α β b hb_α_pou hb_β_pou Idx Jdx]
  set f : TensorCompIdx (E := E) r s → ℝ :=
    fun Q =>
      transitionCoeff (E := E) (I := I) (M := M) r s β α ⟨Idx, Jdx⟩ Q b *
        tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b
    with hf_def
  have h_per_Q : ∀ Q : TensorCompIdx (E := E) r s,
      (f Q) ^ 2 ≤ K ^ 2 *
        (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by
    intro Q
    rw [hf_def, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hK_Q :
        |transitionCoeff (E := E) (I := I) (M := M) r s β α ⟨Idx, Jdx⟩ Q b| ≤ K :=
      hK_bound β α ⟨Idx, Jdx⟩ Q b ⟨hb_β_pou, hb_α_pou⟩
    have h_sq_abs := sq_abs
      (transitionCoeff (E := E) (I := I) (M := M) r s β α ⟨Idx, Jdx⟩ Q b)
    calc (transitionCoeff (E := E) (I := I) (M := M) r s β α ⟨Idx, Jdx⟩ Q b) ^ 2
        = |transitionCoeff (E := E) (I := I) (M := M) r s β α ⟨Idx, Jdx⟩ Q b| ^ 2 :=
            h_sq_abs.symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hK_Q 2
  have hCS : (∑ Q, f Q) ^ 2 ≤
      ((Finset.univ : Finset (TensorCompIdx (E := E) r s)).card : ℝ) *
        ∑ Q, (f Q) ^ 2 :=
    finset_sum_sq_le_card_mul_sum_sq
      (Finset.univ : Finset (TensorCompIdx (E := E) r s)) f
  refine hCS.trans ?_
  have h_sum_bound :
      (∑ Q : TensorCompIdx (E := E) r s, (f Q) ^ 2) ≤
      ∑ Q : TensorCompIdx (E := E) r s, K ^ 2 *
        (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 :=
    Finset.sum_le_sum (fun Q _ => h_per_Q Q)
  have h_factor_out :
      (∑ Q : TensorCompIdx (E := E) r s, K ^ 2 *
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2) =
        K ^ 2 *
          ∑ Q : TensorCompIdx (E := E) r s,
            (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by
    rw [← Finset.mul_sum]
  have h_card_nn :
      0 ≤ ((Finset.univ : Finset (TensorCompIdx (E := E) r s)).card : ℝ) :=
    Nat.cast_nonneg _
  calc ((Finset.univ : Finset (TensorCompIdx (E := E) r s)).card : ℝ) *
            ∑ Q, (f Q) ^ 2
      ≤ ((Finset.univ : Finset (TensorCompIdx (E := E) r s)).card : ℝ) *
              ∑ Q : TensorCompIdx (E := E) r s, K ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 :=
        mul_le_mul_of_nonneg_left h_sum_bound h_card_nn
    _ = ((Finset.univ : Finset (TensorCompIdx (E := E) r s)).card : ℝ) *
              (K ^ 2 *
                ∑ Q : TensorCompIdx (E := E) r s,
                  (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2) := by
            rw [h_factor_out]
    _ = ((Finset.univ : Finset (TensorCompIdx (E := E) r s)).card : ℝ) *
              K ^ 2 *
              ∑ Q : TensorCompIdx (E := E) r s,
                (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by
            ring

/-- Chain rule transformation: for `y ∈ chartTarget α`, the squared model-space
iterated Fréchet 2-derivative of the POU-weighted raw chart-frame scalar pulled
back through the chart symm is bounded by a multiple of the squared Euclidean
iterated Fréchet 2-derivative of the chart-component function. -/
private lemma iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclN) (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ 2
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e'))
        ((toEuclidean (E := E)).symm y)‖ ^ 2 ≤
      (‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) ^ 2 *
        ‖iteratedFDeriv ℝ 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2 := by
  classical
  set L : E →L[ℝ] EuclN := (toEuclidean (E := E) : E ≃L[ℝ] EuclN).toContinuousLinearMap
  set f : EuclN → ℝ := tensorChartComp (I := I) (M := M) g r s T α Idx Jdx with hf_def
  set u : E → ℝ := fun e' =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e') *
      tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm e') with hu_def
  have he : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_open : IsOpen ((extChartAt I α).target) := isOpen_extChartAt_target (I := I) α
  have h_agree_on : Set.EqOn u (f ∘ L) ((extChartAt I α).target) := by
    intro e' he'
    have hL_e' : L e' = toEuclidean e' := rfl
    have h_L_e'_target : L e' ∈ chartTargetEuclid (I := I) (M := M) α :=
      ⟨e', he', rfl⟩
    have h_f_apply :
        f (L e') =
          tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm (L e'))) := by
      rw [hf_def]
      exact tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx h_L_e'_target
    have h_symL_e' : (toEuclidean (E := E)).symm (L e') = e' := by
      change (toEuclidean (E := E)).symm (toEuclidean e') = e'
      exact (toEuclidean (E := E)).symm_apply_apply e'
    rw [h_symL_e'] at h_f_apply
    change u e' = f (L e')
    rw [h_f_apply]
    unfold tensorChartComponentPou
    rfl
  have h_iter_eq :
      iteratedFDeriv ℝ 2 u ((toEuclidean (E := E)).symm y) =
        iteratedFDeriv ℝ 2 (f ∘ L) ((toEuclidean (E := E)).symm y) := by
    have h_evEq : u =ᶠ[𝓝 ((toEuclidean (E := E)).symm y)] (f ∘ L) :=
      Filter.eventuallyEq_of_mem (h_open.mem_nhds he) h_agree_on
    exact (Filter.EventuallyEq.iteratedFDeriv ℝ h_evEq 2).eq_of_nhds
  rw [h_iter_eq]
  have h_f_cd : ContDiff ℝ ∞ f :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
  have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  rw [L.iteratedFDeriv_comp_right (n := (⊤ : ℕ∞)) h_f_cd _ h2_le]
  have h_L_sym : L ((toEuclidean (E := E)).symm y) = y :=
    (toEuclidean (E := E)).apply_symm_apply y
  rw [h_L_sym]
  have h_norm_le : ‖(iteratedFDeriv ℝ 2 f y).compContinuousLinearMap
        (fun _ : Fin 2 => L)‖ ≤
      ‖iteratedFDeriv ℝ 2 f y‖ * ∏ _i : Fin 2, ‖L‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
  rw [show (∏ _i : Fin 2, ‖L‖) = ‖L‖ ^ 2 from by
    rw [Finset.prod_const]; simp] at h_norm_le
  have hLHS_nn : 0 ≤ ‖(iteratedFDeriv ℝ 2 f y).compContinuousLinearMap
      (fun _ : Fin 2 => L)‖ := norm_nonneg _
  have h_sq_le : ‖(iteratedFDeriv ℝ 2 f y).compContinuousLinearMap
        (fun _ : Fin 2 => L)‖ ^ 2 ≤
      (‖iteratedFDeriv ℝ 2 f y‖ * ‖L‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hLHS_nn h_norm_le 2
  have hL_norm : ‖L‖ = ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ := rfl
  rw [hL_norm] at h_sq_le
  refine h_sq_le.trans (le_of_eq ?_)
  ring

/-- For `y ∈ chartTargetEuclid α` and `POU(α at symm y) ≠ 0`, the inverse-chart
preimage `symm y` lies in `tsupport POU(α) ∩ chartLeviCivitaGoodSet`. Under
`[I.Boundaryless]`, the good set equals the chart source, and `tsupport POU(α)
⊆ chart source α` (subordinate), so the intersection equals `tsupport POU(α)`. -/
private lemma symm_mem_pou_inter_goodSet
    (α : M) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (h_pou_pos :
      (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≠ 0) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∩
        chartLeviCivitaGoodSet (I := I) α := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source := by
    rw [hb_def]
    exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_supp : b ∈ Function.support ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    simp only [Function.mem_support, ne_eq]
    exact h_pou_pos
  have hb_tsupp : b ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    subset_tsupport _ hb_supp
  have h_goodSet_eq : chartLeviCivitaGoodSet (I := I) α = (extChartAt I α).source :=
    chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
  have hb_extSrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [h_goodSet_eq]; exact hb_extSrc
  exact ⟨hb_tsupp, hb_good⟩

/-- For `y ∈ chartTargetEuclid α` and `POU(α at symm y) ≠ 0`, `y` lies in the
`toEuclidean` image of `extChartAt α` image of `tsupport POU(α) ∩ goodSet`. -/
private lemma mem_pouImage_of_pou_pos
    (α : M) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (h_pou_pos :
      (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≠ 0) :
    y ∈ (toEuclidean : E ≃L[ℝ] EuclN) ''
          ((extChartAt I α) ''
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              chartLeviCivitaGoodSet (I := I) α)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_in : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        chartLeviCivitaGoodSet (I := I) α :=
    symm_mem_pou_inter_goodSet (I := I) (M := M) α hy h_pou_pos
  refine ⟨(toEuclidean (E := E)).symm y, ⟨b, hb_in, ?_⟩, ?_⟩
  · rw [hb_def]
    exact (extChartAt I α).right_inv hb_target
  · exact (toEuclidean (E := E)).apply_symm_apply y

/-- For each `α` and `IJ`, the integral over `chartTargetEuclid α` of
`ofReal(‖fderiv (chartComp β IJ) y‖²)` is bounded by `(wkpNorm 2 2 chartComp
β IJ chartTarget β)²`. Domain enlargement: extend the integral from
`chartTarget α` to the whole space (since the integrand vanishes outside
`tsupport (chartComp β IJ) ⊆ chartTarget β`), then apply the Sobolev bridge
`chartTarget_fderiv_eLpNorm_le_wkpNorm_two`. -/
private lemma int_fderiv_tensorChartComp_β_sq_le_wkpNorm_two_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (‖fderiv ℝ
            (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      (wkpNorm (d := Module.finrank ℝ E) 2 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β)) ^ 2 := by
  classical
  set fd : EuclN → ℝ := fun y => ‖fderiv ℝ
    (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ with hfd_def
  have h_le_full :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) ≤
        ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) :=
    setLIntegral_le_lintegral _ _
  refine h_le_full.trans ?_
  have h_supp : tsupport (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_fd_supp : tsupport fd ⊆ chartTargetEuclid (I := I) (M := M) β := by
    have h_norm_subset : tsupport fd ⊆
        tsupport (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)) := by
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq, hfd_def] at hy
      simp only [Function.mem_support, ne_eq]
      intro hzero
      apply hy
      rw [hzero, norm_zero]
    refine (h_norm_subset.trans (tsupport_fderiv_subset _)).trans h_supp
  have h_chartTarget_β_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) β
  have h_full_eq_β :
      ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
            ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    have h_indicator_eq : (fun y => ENNReal.ofReal (fd y ^ 2)) =
        (chartTargetEuclid (I := I) (M := M) β).indicator
          (fun y => ENNReal.ofReal (fd y ^ 2)) := by
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) β
      · rw [Set.indicator_of_mem hy]
      · have hy_notin_supp : y ∉ tsupport fd := fun hin => hy (h_fd_supp hin)
        have hy_zero : fd y = 0 := by
          by_contra hne
          have hy_in_supp : y ∈ Function.support fd := by
            simp only [Function.mem_support, ne_eq]; exact hne
          exact hy_notin_supp (subset_tsupport _ hy_in_supp)
        rw [hy_zero, Set.indicator_of_notMem hy]
        simp
    conv_lhs => rw [h_indicator_eq]
    rw [MeasureTheory.lintegral_indicator h_chartTarget_β_meas]
  rw [h_full_eq_β]
  have h_sq_eLp_eq : (eLpNorm fd 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β))) ^ 2 =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq]
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    change ‖fd y‖ₑ ^ 2 = ENNReal.ofReal (fd y ^ 2)
    rw [show (fd y ^ 2) = ‖fd y‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show ENNReal.ofReal (‖fd y‖ ^ 2) = (ENNReal.ofReal ‖fd y‖) ^ 2 from
      ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [ofReal_norm_eq_enorm]
  rw [← h_sq_eLp_eq]
  have h_β_open : IsOpen (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T β Idx Jdx
  have h_cc :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T β Idx Jdx
  have h_supp_β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chartTarget_fderiv_eLpNorm_le_wkpNorm_two
      (d := Module.finrank ℝ E) (Ω := chartTargetEuclid (I := I) (M := M) β)
      h_β_open h_smooth h_cc h_supp_β
  exact pow_le_pow_left' h_bridge 2

/-- The per-α-(Idx, Jdx) `chartTarget α` integral of
`‖iteratedFDeriv 2 (chartComp β IJ) y‖²` is bounded by
`(wkpNorm 2 2 chartComp β IJ chartTarget β)²`. The structure mirrors
`int_fderiv_tensorChartComp_β_sq_le_wkpNorm_two_sq`. -/
private lemma int_iteratedFDeriv_two_tensorChartComp_β_sq_le_wkpNorm_two_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2
            (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      (wkpNorm (d := Module.finrank ℝ E) 2 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β)) ^ 2 := by
  classical
  set fd : EuclN → ℝ := fun y => ‖iteratedFDeriv ℝ 2
    (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ with hfd_def
  have h_le_full :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) ≤
        ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) :=
    setLIntegral_le_lintegral _ _
  refine h_le_full.trans ?_
  have h_supp : tsupport (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_fd_supp : tsupport fd ⊆ chartTargetEuclid (I := I) (M := M) β := by
    have h_norm_subset : tsupport fd ⊆
        tsupport (iteratedFDeriv ℝ 2
          (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)) := by
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq, hfd_def] at hy
      simp only [Function.mem_support, ne_eq]
      intro hzero
      apply hy
      rw [hzero, norm_zero]
    refine (h_norm_subset.trans (tsupport_iteratedFDeriv_subset 2)).trans h_supp
  have h_chartTarget_β_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) β
  have h_full_eq_β :
      ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
            ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    have h_indicator_eq : (fun y => ENNReal.ofReal (fd y ^ 2)) =
        (chartTargetEuclid (I := I) (M := M) β).indicator
          (fun y => ENNReal.ofReal (fd y ^ 2)) := by
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) β
      · rw [Set.indicator_of_mem hy]
      · have hy_notin_supp : y ∉ tsupport fd := fun hin => hy (h_fd_supp hin)
        have hy_zero : fd y = 0 := by
          by_contra hne
          have hy_in_supp : y ∈ Function.support fd := by
            simp only [Function.mem_support, ne_eq]; exact hne
          exact hy_notin_supp (subset_tsupport _ hy_in_supp)
        rw [hy_zero, Set.indicator_of_notMem hy]
        simp
    conv_lhs => rw [h_indicator_eq]
    rw [MeasureTheory.lintegral_indicator h_chartTarget_β_meas]
  rw [h_full_eq_β]
  have h_sq_eLp_eq : (eLpNorm fd 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β))) ^ 2 =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq]
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    change ‖fd y‖ₑ ^ 2 = ENNReal.ofReal (fd y ^ 2)
    rw [show (fd y ^ 2) = ‖fd y‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show ENNReal.ofReal (‖fd y‖ ^ 2) = (ENNReal.ofReal ‖fd y‖) ^ 2 from
      ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [ofReal_norm_eq_enorm]
  rw [← h_sq_eLp_eq]
  have h_β_open : IsOpen (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_smooth : ContDiff ℝ ∞
      (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T β Idx Jdx
  have h_cc :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T β Idx Jdx
  have h_supp_β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chartTarget_iteratedFDeriv_two_eLpNorm_le_wkpNorm_two
      (d := Module.finrank ℝ E) (Ω := chartTargetEuclid (I := I) (M := M) β)
      h_β_open h_smooth h_cc h_supp_β
  exact pow_le_pow_left' h_bridge 2

/-- The per-(α, IJ) `chartTarget α` integral of the squared norm of the
iterated 2-derivative of `POU(α) · raw α IJ ∘ symm_α` is bounded by
`‖toEuclidean‖⁴ · (wkpNorm 2 2 chartComp α IJ chartTarget α)²`. This combines
the chain rule lemma `iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq`
with `int_iteratedFDeriv_two_tensorChartComp_β_sq_le_wkpNorm_two_sq`. -/
private lemma int_iteratedFDeriv_two_pou_raw_α_symm_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e') *
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e'))
            ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      ENNReal.ofReal ((‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) ^ 2) *
        (wkpNorm (d := Module.finrank ℝ E) 2 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
  classical
  set NtoE_sq2 : ℝ := (‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) ^ 2 with hNtoE_sq2_def
  have hNtoE_sq2_nn : 0 ≤ NtoE_sq2 := sq_nonneg _
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e') *
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e'))
            ((toEuclidean (E := E)).symm y)‖ ^ 2) ≤
        ENNReal.ofReal NtoE_sq2 *
          ENNReal.ofReal
            (‖iteratedFDeriv ℝ 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2) := by
    intro y hy
    have h_real := iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq
      (I := I) (M := M) g r s T α Idx Jdx y hy
    have h_step :=
      ENNReal.ofReal_le_ofReal h_real
    refine h_step.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hNtoE_sq2_nn]
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (‖iteratedFDeriv ℝ 2
              (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e'))
              ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal NtoE_sq2 *
              ENNReal.ofReal
                (‖iteratedFDeriv ℝ 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  refine h_int_mono.trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  exact int_iteratedFDeriv_two_tensorChartComp_β_sq_le_wkpNorm_two_sq
    (I := I) (M := M) g r s T α α Idx Jdx

/-- The per-α B'.3a bound aggregated: the V-integral
`∫_α ofReal(POU² · ‖repr‖²)` is bounded by `K_a · cardIdx · cardJdx · W` for an
explicit `K_a` from `chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq`. -/
private lemma per_alpha_V_int_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  obtain ⟨K_a, hK_a_nn, hK_a_bound⟩ :=
    chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
      (I := I) (M := M) g r s α
  set cIcJ : ℝ :=
    ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ) *
      ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ)
    with hcIcJ_def
  have hcIcJ_nn : 0 ≤ cIcJ := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨K_a * cIcJ, mul_nonneg hK_a_nn hcIcJ_nn, ?_⟩
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  refine (hK_a_bound T).trans ?_
  rw [ENNReal.ofReal_mul hK_a_nn]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  have h_per_IJ : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      (wkpNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤ W :=
    fun Idx Jdx => wkpNorm_zero_sq_le_wtwokTwoNorm_sq (I := I) (M := M) g r s T α Idx Jdx
  calc ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2
      ≤ ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W := by
        refine Finset.sum_le_sum (fun Idx _ => ?_)
        refine Finset.sum_le_sum (fun Jdx _ => ?_)
        exact h_per_IJ Idx Jdx
    _ = ENNReal.ofReal cIcJ * W := by
        rw [show (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
            ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
              (((Finset.univ : Finset
                  (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) * W) from by
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]]
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [show ENNReal.ofReal cIcJ =
            ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
              ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞)
          from by
          rw [hcIcJ_def, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
        ring

end Connection
end Integral
end DifferentialGeometry

end
