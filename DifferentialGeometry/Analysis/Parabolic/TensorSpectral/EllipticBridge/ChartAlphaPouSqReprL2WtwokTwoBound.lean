import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.ChartAlphaPouAlphaPouBetaCovBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapL2WtwokTwoBound

/-!
# Chart-`α` POU(α)²-weighted L² bound for the chart-pulled representation by the
# order-`0` tensor Sobolev norm

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner-product space `E`, fixed tensor ranks `(r, s)`, and a chart base point
`α : M`, this file ships the headline bound

```
∫⁻ y in chartTargetEuclid α,
    ENNReal.ofReal
      ((POU(α)((extChartAt α).symm (toEuclidean.symm y)))^2 *
        ‖tensorRSChartE_section_repr r s α T.toSection
            ((extChartAt α).symm (toEuclidean.symm y))‖^2)
    ∂(volume : Measure EuclN) ≤
  ENNReal.ofReal K * (wtwokTwoNorm g 0 T) ^ 2
```

with `K ≥ 0` depending only on the manifold, the metric, and the ranks —
independent of the chart base point `α` and the tensor section `T`.

## Strategy

The bound chains the order-0 chart-target POU-weighted L² bound
`chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq` (which bounds
the LHS by a constant times the finite double sum
`Σ_(Idx, Jdx) (wkpNorm 0 2 α Idx Jdx)²`) with the elementary
`ℝ≥0∞`-Cauchy–Schwarz double bound and an `ENNReal.le_tsum` step to package the
finite double sum into the squared aggregated norm `(wtwokTwoNorm g 0 T)²`.

The headline LHS shape `ENNReal.ofReal (POU² · ‖repr‖²)` is identified with the
existing `ENNReal.ofReal POU² · ENNReal.ofReal ‖repr‖²` factorisation via
`ENNReal.ofReal_mul`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
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
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- For any fixed chart base point `α : M`, the finite double sum of squared
chart-component `wkpNorm 0 2` is bounded by the squared aggregated tensor
Sobolev norm `(wtwokTwoNorm g 0 T)²`. -/
private lemma sum_wkpNorm_sq_α_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2) ≤
      (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
  classical
  set w : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α' Idx Jdx => wkpNorm (d := Module.finrank ℝ E) 0 2
      (tensorChartComp (I := I) (M := M) g r s T α' Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α') with hw_def
  set S : M → ℝ≥0∞ := fun α' =>
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        w α' Idx Jdx with hS_def
  have h_inner :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E), (w α Idx Jdx) ^ 2) ≤
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx) ^ 2 := by
    intro Idx
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun Jdx _ => zero_le _)
  set u : (Fin r → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun Idx => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx with hu_def
  have h_outer : (∑ Idx : Fin r → Fin (Module.finrank ℝ E), (u Idx) ^ 2) ≤
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E), u Idx) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun Idx _ => zero_le _)
  have h_double :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), (w α Idx Jdx) ^ 2) ≤
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx) ^ 2 := by
    refine le_trans ?_ h_outer
    refine Finset.sum_le_sum ?_
    intro Idx _
    exact h_inner Idx
  have hSα_eq : S α =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx := rfl
  have h_tsum_le : S α ≤ ∑' β : M, S β := ENNReal.le_tsum α
  have h_tsum_eq : (∑' β : M, S β) = wtwokTwoNorm (I := I) (M := M) g 0 T := by
    unfold wtwokTwoNorm
    refine tsum_congr ?_
    intro β
    change (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w β Idx Jdx) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
              (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) β)
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    change wkpNorm (d := Module.finrank ℝ E) 0 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β) =
      wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β)
    congr 1
  have h_Sα_le_wt : S α ≤ wtwokTwoNorm (I := I) (M := M) g 0 T := by
    rw [← h_tsum_eq]
    exact h_tsum_le
  have h_Sα_sq_le_wt_sq :
      (S α) ^ 2 ≤ (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
    have := h_Sα_le_wt
    exact pow_le_pow_left' this 2
  calc (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (wkpNorm (d := Module.finrank ℝ E) 0 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2)
      = (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), (w α Idx Jdx) ^ 2) := by
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rfl
    _ ≤ (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx) ^ 2 := h_double
    _ = (S α) ^ 2 := by rw [hSα_eq]
    _ ≤ (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := h_Sα_sq_le_wt_sq

/-- **Chart-`α` POU(α)²-weighted L² bound for the chart-pulled representation
by the order-`0` tensor Sobolev norm.**

For any closed Riemannian manifold `(M, g)`, fixed tensor ranks `(r, s)`, and
chart base point `α : M`, there exists a non-negative real constant `K`
(depending only on the manifold, the metric, and the ranks; independent of the
tensor section `T`) such that for every smooth compactly-supported
`(r, s)`-tensor section `T : SmoothCcTensor g r s`,

```
∫⁻ y in chartTargetEuclid α,
    ENNReal.ofReal
      ((POU(α)((extChartAt α).symm (toEuclidean.symm y)))^2 *
        ‖tensorRSChartE_section_repr r s α T.toSection
            ((extChartAt α).symm (toEuclidean.symm y))‖^2)
    ∂(volume : Measure EuclN) ≤
  ENNReal.ofReal K * (wtwokTwoNorm g 0 T) ^ 2.
```

The bound applies the order-`0` chart-target POU-weighted L² bound
`chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq` to obtain the
finite double sum `Σ_(Idx, Jdx) (wkpNorm 0 2 α Idx Jdx)²` on the right, then
bounds this finite double sum by the squared aggregated tensor Sobolev norm
`(wtwokTwoNorm g 0 T)²` via the elementary `ℝ≥0∞`-Cauchy–Schwarz double bound
and the `ENNReal.le_tsum` chart-aggregation step. -/
theorem chart_α_pou_sq_repr_L2_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
  classical
  obtain ⟨K_up, hK_up_nn, hK_up_le⟩ :=
    chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
      (E := E) (I := I) (M := M) g r s α
  refine ⟨K_up, hK_up_nn, ?_⟩
  intro T
  have h_LHS_eq :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm
                      ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    exact ENNReal.ofReal_mul (sq_nonneg _)
  rw [h_LHS_eq]
  refine le_trans (hK_up_le T) ?_
  have h_sum_le := sum_wkpNorm_sq_α_le_wtwokTwoNorm_sq
    (I := I) (M := M) g r s α T
  exact mul_le_mul_of_nonneg_left h_sum_le (zero_le _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
