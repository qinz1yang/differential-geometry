import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.WeightedCoeffMulENormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.ChartComponentCutoffENormBound

/-!
# Explicit-norm `eLpNorm` bounds for three eigenvector chart limit objects

The chart-Euclidean right-hand side of the connection-Laplacian eigenvector's
weak-solution assembly is built from `C^∞`-coefficient-weighted limit objects.
Three of them are treated here:

* `crossLeftLimitComponent g r s i α P` — the cutoff Euclidean chart
  component, at `(α, P)`, of the completion-extended covariant gradient
  `tensorCovGradL2Compl g r s` applied to the eigenvector resolvent;
* `crossRightLimitComponent g r s i α P` — the cutoff Euclidean chart
  component, at `(α, P)`, of the `L²`-coercion `TensorH1ComplToTensorL2 g r s`
  of the eigenvector resolvent;
* `covPrincipalRotationCoeffLimit g r s i α P₀` — a four-fold finite
  sum, over component multi-index pairs and chart directions, of the
  `chartPouKernel α`-indicator-cut `C^∞` factor `principalRotationFactor`
  against the chart-partial atom `partialLpLimit`.

This file records, for each, an explicit-constant `eLpNorm` bound for the
chart-pulled weighted measure
`μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

## Strategy

The two cross-Leibniz limits are, by definition, single cutoff Euclidean chart
components of abstract `L²` elements; their weighted `eLpNorm` bound is the
corresponding instance of the foundational
`eLpNorm_tensorL2ChartComponentCutoff_le` — the cutoff confines the component to
a compact kernel, on which the chart-density is bounded above, so the weighted
`eLpNorm` is controlled by a constant times the abstract element's norm `‖u‖`.

The principal rotation coefficient limit is a four-fold finite sum whose
summands carry an `indicator (chartPouKernel α)` cut of the `C^∞`-on-the-chart-
target factor `principalRotationFactor`; the accompanying chart-partial atom
`partialLpLimit` vanishes almost everywhere — for the weighted measure — off the
compact partition-of-unity kernel `chartPouKernel α`, so the indicator-cut
summand agrees almost everywhere with the uncut `C^∞`-factor product. The
explicit-norm bound `eLpNorm_weighted_contDiffOn_mul_le` controls that product's
`eLpNorm` by an explicit constant — the `C^∞` factor's sup over the compact
kernel — times the atom's `eLpNorm`. The triangle inequality `eLpNorm_sum_le`
over the four-fold finite sum assembles the per-summand bounds; every summation
multiplicity and every per-coefficient sup constant is folded into a single
headline constant.

## Main results

* `eLpNorm_crossLeftLimitComponent_le_uniform`
* `eLpNorm_crossRightLimitComponent_le_uniform`
* `eLpNorm_covPrincipalRotationCoeffLimit_le_uniform`

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section CrossRotationENormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- For a `C^∞`-on-the-chart-target coefficient `c` and a function `G` that is
weighted-`MemLp` and vanishes almost everywhere — for the chart-pulled weighted
measure restricted to the chart target — off the compact partition-of-unity
kernel, the indicator-cut summand `(chartPouKernel α).indicator c · G` is
weighted-`MemLp` and its `eLpNorm` is bounded by an explicit nonnegative constant
times the `eLpNorm` of `G`. -/
private lemma eLpNorm_indicatorFactor_mul_atom_le
    (g : SmoothRiemannianMetric I M) (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (G : EuclN → ℝ)
    (hG : MemLp G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)))
    (hG_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) :
    MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
            G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_prod_eq : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        c y * G y) =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)] (fun y => c y * G y) := by
    filter_upwards [hG_zero] with y hy
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK, mul_zero, mul_zero]
  have h_mul_memLp : MemLp (fun y => c y * G y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_weighted_contDiffOn_mul (I := I) (M := M) g α hc
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      hG hG_zero
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le
    (I := I) (M := M) g α hc
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    hG hG_zero
  refine ⟨h_mul_memLp.ae_eq h_prod_eq.symm, C, hC_nn, ?_⟩
  rw [eLpNorm_congr_ae h_prod_eq]
  exact hC_bd

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- Triangle inequality for `eLpNorm` over a finite sum, with each summand
weighted-`MemLp`. -/
private lemma eLpNorm_finsetSum_le
    {ι : Type*} (g : SmoothRiemannianMetric I M) (α : M)
    (s : Finset ι) (F : ι → EuclN → ℝ)
    (hF : ∀ j ∈ s, MemLp (F j) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :
    eLpNorm (fun y => ∑ j ∈ s, F j y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ∑ j ∈ s, eLpNorm (F j) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_fun : (fun y => ∑ j ∈ s, F j y) = ∑ j ∈ s, F j := by
    funext y
    exact (Finset.sum_apply y s F).symm
  rw [h_fun]
  exact eLpNorm_sum_le (fun j hj => (hF j hj).1) (by norm_num)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- A finite indexed family of summands, each weighted-`MemLp` and each
`eLpNorm`-bounded by `ENNReal.ofReal C` times the `eLpNorm` of an atom selected
by a projection `proj`, has its summed `eLpNorm` bounded by `ENNReal.ofReal` of
an explicit constant times the sum, over the distinct atoms, of the atoms'
`eLpNorm`. -/
private lemma eLpNorm_finsetSum_le_const_mul_atomSum
    {ι κ : Type*} (g : SmoothRiemannianMetric I M) (α : M)
    (s : Finset ι) (t : Finset κ) (F : ι → EuclN → ℝ) (atom : κ → EuclN → ℝ)
    (proj : ι → κ) (hproj : ∀ j ∈ s, proj j ∈ t)
    (C : ℝ)
    (hF : ∀ j ∈ s, MemLp (F j) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (h_bd : ∀ j ∈ s, eLpNorm (F j) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal C * eLpNorm (atom (proj j)) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) :
    eLpNorm (fun y => ∑ j ∈ s, F j y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal (C * s.card)
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_tri := eLpNorm_finsetSum_le (I := I) (M := M) g α s F hF
  have h_step : ∑ j ∈ s, eLpNorm (F j) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ∑ _j ∈ s, ENNReal.ofReal C
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    refine (h_bd j hj).trans ?_
    gcongr
    exact Finset.single_le_sum
      (f := fun p => eLpNorm (atom p) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      (fun p _ => zero_le _) (hproj j hj)
  have h_const : ∑ _j ∈ s, ENNReal.ofReal C
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
      = (s.card : ℝ≥0∞) * (ENNReal.ofReal C
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h_cast : (s.card : ℝ≥0∞) * ENNReal.ofReal C
      = ENNReal.ofReal (C * s.card) := by
    rw [mul_comm C, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  calc
    eLpNorm (fun y => ∑ j ∈ s, F j y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ∑ j ∈ s, eLpNorm (F j) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := h_tri
    _ ≤ ∑ _j ∈ s, ENNReal.ofReal C
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := h_step
    _ = (s.card : ℝ≥0∞) * (ENNReal.ofReal C
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) := h_const
    _ = ((s.card : ℝ≥0∞) * ENNReal.ofReal C)
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by rw [mul_assoc]
    _ = ENNReal.ofReal (C * s.card)
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by rw [h_cast]

end CrossRotationENormBounds

section CrossRotationENormBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- A constant-uniform form of the per-summand bound: for a `C^∞`-on-the-chart-
target coefficient `c`, a single nonnegative constant `C` controls the
`eLpNorm` of the indicator-cut product `(chartPouKernel α).indicator c · G` for
*every* weighted-`MemLp` function `G` that vanishes almost everywhere (weighted)
off the compact partition-of-unity kernel. The constant is the coefficient's
sup over the kernel, independent of `G`. -/
private lemma eLpNorm_indicatorFactor_mul_atom_le_uniform
    (g : SmoothRiemannianMetric I M) (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ G : EuclN → ℝ,
        MemLp G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) →
        (∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
            G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ∧
          eLpNorm (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              c y * G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
            ≤ ENNReal.ofReal C *
              eLpNorm G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α hc
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  refine ⟨C, hC_nn, fun G hG hG_zero => ?_⟩
  have h_prod_eq : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        c y * G y) =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)] (fun y => c y * G y) := by
    filter_upwards [hG_zero] with y hy
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK, mul_zero, mul_zero]
  have h_mul_memLp : MemLp (fun y => c y * G y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_weighted_contDiffOn_mul (I := I) (M := M) g α hc
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      hG hG_zero
  refine ⟨h_mul_memLp.ae_eq h_prod_eq.symm, ?_⟩
  rw [eLpNorm_congr_ae h_prod_eq]
  exact hC_bd G hG hG_zero

end CrossRotationENormBoundsUniform

section CrossRotationENormBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- **Chart-locality-free uniform-constant `eLpNorm` bound for the cross-left
limit object.** Chart-locality-free twin of
`eLpNorm_crossLeftLimitComponent_le_uniform`: a single nonnegative constant `C`
serves every eigenbasis index `i`, with no chart-selection hypothesis. The
limit object `crossLeftLimitComponent` is by definition the cutoff
Euclidean chart component, at `(α, P)`, of the abstract `L²` element
`tensorCovGradL2Compl g r s (eigenvectorResolvent g r s i)`, so the
per-`i` bound delegates to the atlas-free uniform delegator
`eLpNorm_tensorL2ChartComponentCutoff_le_uniform`, whose constant depends only on
`g, r, s, α, P` and not on the abstract `L²` element it is applied to. -/
theorem eLpNorm_crossLeftLimitComponent_le_uniform
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal ‖tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i)‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponentCutoff_le_uniform
    (I := I) (M := M) g r (s + 1) α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [crossLeftLimitComponent]
  exact hC_bd (tensorCovGradL2Compl (I := I) (M := M) g r s
    (eigenvectorResolvent (I := I) (M := M) g r s i))

/-- **Chart-locality-free uniform-constant `eLpNorm` bound for the cross-right
limit object.** Chart-locality-free twin of
`eLpNorm_crossRightLimitComponent_le_uniform`: a single nonnegative constant `C`
serves every eigenbasis index `i`, with no chart-selection hypothesis. The
limit object `crossRightLimitComponent` is by definition the cutoff
Euclidean chart component, at `(α, P)`, of the abstract `L²` element
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s i)`, so
the per-`i` bound delegates to the atlas-free uniform delegator
`eLpNorm_tensorL2ChartComponentCutoff_le_uniform`, whose constant depends only on
`g, r, s, α, P` and not on the abstract `L²` element it is applied to. -/
theorem eLpNorm_crossRightLimitComponent_le_uniform
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i)‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponentCutoff_le_uniform
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [crossRightLimitComponent]
  exact hC_bd (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
    (eigenvectorResolvent (I := I) (M := M) g r s i))

/-- **Chart-locality-free twin of
`partialLpLimit_ae_zero_off_chartPouKernel_weighted`.** The chart-partial atom
`partialLpLimit g r s i α P k` vanishes almost everywhere — for the
chart-pulled weighted measure restricted to the chart target — off the compact
partition-of-unity kernel `chartPouKernel α`, with no chart-selection
hypothesis. -/
private lemma partialLpLimit_ae_zero_off_chartPouKernel_weighted
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  have h_weak_sdiff :=
    eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P k
  have hKc_meas : MeasurableSet
      (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_measurableSet (I := I) (M := M) α).compl
  have h_weak_impl : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y = 0 := by
    refine (ae_restrict_iff' hKc_meas).mp ?_
    rw [Measure.restrict_restrict hKc_meas]
    have h_inter : (chartPouKernel (I := I) (M := M) α)ᶜ ∩
        chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := by
      rw [Set.diff_eq, Set.inter_comm]
    rw [h_inter]
    filter_upwards [h_weak_sdiff] with y hy using hy
  have h_weak_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y = 0 :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le h_weak_impl
  have h_smul_w : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y) :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le h_smul
  filter_upwards [h_smul_w, h_weak_w] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-- **Chart-locality-free twin of `partialLpLimit_memLp_weighted`.** The
chart-partial atom `partialLpLimit g r s i α P k` is `MemLp 2` for
the chart-pulled weighted measure restricted to the chart target, with no
chart-selection hypothesis. -/
private lemma partialLpLimit_memLp_weighted
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (fun y => ((partialLpLimit (I := I) (M := M)
      g r s i α P k :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      (chartL2Measure (I := I) (M := M) α) := Lp.memLp _
  have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  have h_weak_sdiff :=
    eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P k
  have hKc_meas : MeasurableSet
      (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_measurableSet (I := I) (M := M) α).compl
  have h_weak_impl : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y = 0 := by
    refine (ae_restrict_iff' hKc_meas).mp ?_
    rw [Measure.restrict_restrict hKc_meas]
    have h_inter : (chartPouKernel (I := I) (M := M) α)ᶜ ∩
        chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := by
      rw [Set.diff_eq, Set.inter_comm]
    rw [h_inter]
    filter_upwards [h_weak_sdiff] with y hy using hy
  have h_atom_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    filter_upwards [h_smul, h_weak_impl] with y hy hy_zero hyK
    · rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    h_atom_zero h_plain

/-- **Chart-locality-free uniform-constant `eLpNorm` bound for the principal
rotation coefficient limit.** Chart-locality-free twin of
`eLpNorm_covPrincipalRotationCoeffLimit_le_uniform`: a single nonnegative
constant `C` serves every eigenbasis index `i`, with no chart-selection
hypothesis. The limit object `covPrincipalRotationCoeffLimit` is a
four-fold finite sum over `(P, Q, k, l)` whose summands carry an
`indicator (chartPouKernel α)` cut of the `C^∞` factor `principalRotationFactor`
against the chart-partial atom `partialLpLimit P k`; the atom
vanishes almost everywhere (weighted) off the compact partition-of-unity kernel,
so the indicator-cut summand agrees almost everywhere with the uncut `C^∞`-factor
product, and `eLpNorm_indicatorFactor_mul_atom_le_uniform` controls its
`eLpNorm`. The per-`i` bound's constant is a finite sum, over the four-fold
summation index, of the per-summand sup constants of the `i`-free `C^∞` factor
`principalRotationFactor` over the kernel; that constant does not depend on `i`
and is hoisted before the `∀ i`. -/
theorem eLpNorm_covPrincipalRotationCoeffLimit_le_uniform
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            (∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have h_factor_data : ∀ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), ∃ C : ℝ, 0 ≤ C ∧
      ∀ G : EuclN → ℝ, MemLp G 2 μw →
        (∀ᵐ y ∂μw, y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M)
              g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) 2 μw ∧
          eLpNorm (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) 2 μw
            ≤ ENNReal.ofReal C * eLpNorm G 2 μw := by
    intro x
    rw [hμw_def]
    exact eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)
  choose CF hCF_nn hCF using h_factor_data
  refine ⟨(∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CF x)
    * (Finset.univ : Finset (TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E))).card,
    mul_nonneg (Finset.sum_nonneg (fun x _ => hCF_nn x))
      (by positivity), fun i => ?_⟩
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set F : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (principalRotationFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemLp (F x) 2 μw ∧
      eLpNorm (F x) 2 μw ≤ ENNReal.ofReal (CF x) *
        eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    intro x
    exact hCF x _ (partialLpLimit_memLp_weighted (I := I) (M := M)
        g r s i α x.1 x.2.2.1)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted
        (I := I) (M := M) g r s i α x.1 x.2.2.1)
  have hCsum_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      eLpNorm (F x) 2 μw
      ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), CF x) *
        eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    intro x
    refine (h_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun x _ => hCF_nn x) (Finset.mem_univ x)
  have h_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), F x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), CF x) * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pk) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ F partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CF x)
      (fun x _ => by rw [← hμw_def]; exact (h_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCsum_bd x)
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), F x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hF_def]
    simp only [Fintype.sum_prod_type]
  have h_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pk) 2 μw
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  rw [show (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    EuclN → ℝ) y) from rfl]
  rw [← h_eq, hμw_def, ← h_atom_eq]
  exact h_bound

end CrossRotationENormBoundsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
