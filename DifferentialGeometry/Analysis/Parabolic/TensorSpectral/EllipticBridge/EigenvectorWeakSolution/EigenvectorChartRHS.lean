import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightDiv

/-!
# The chart right-hand side of the eigenvector weak-solution assembly

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, the per-component
elliptic-regularity analysis realises the chart `P₀`-component of the abstract
connection-Laplacian eigenvector as a chart-local weak elliptic solution.

The variational-identity assembly applies the source-free per-approximant chart
bilinear identity to the partition-of-unity-weighted smooth approximants; its
Dirichlet term splits, by the covariant Leibniz rule, into a genuine-gradient
main-Dirichlet term corrected by two cross terms. This file packages the
chart-Euclidean right-hand side of the limiting variational identity.

## The chart right-hand side

`eigenvectorChartRHS g r s i α P₀` is the chart-Euclidean
right-hand side of the limiting per-component variational identity: the explicit
`densityOnEuclid`-and-`C^∞`-coefficient-weighted finite combination of the
chart-component limit objects produced by the companion files of this campaign —

* the canonical eigenvector chart component `u_chart` (the chart `P₀`-component
  of the eigenvector);
* the cross-Leibniz limit objects `crossLeftLimitComponent`,
  `crossRightLimitComponent`;
* the lower-order coefficient limits `covPrincipalRotationCoeffLimit`,
  `covLowerOrderRotationValueCoeffLimit`,
  `weightedGradCoeffDivLimit`.

Each limit object is, by its companion-file lemma, `MemLp 2` with respect to the
chart-pulled weighted measure restricted to `chartTargetEuclid α`; each multiplying
`C^∞` coefficient is bounded on the compact kernel where the limit object is
supported. The chart-Euclidean right-hand side is therefore again `MemLp 2` with
respect to the chart-pulled weighted measure
(`eigenvectorChartRHS_memLp_weighted`) — the `f_chart` membership of
the chart-bilinear divergence-form data structure.

## Main results

* `eigenvectorChartRHS` — the chart-Euclidean right-hand side of the
  limiting per-component variational identity.
* `eigenvectorChartRHS_memLp_weighted` —
  `eigenvectorChartRHS` is `MemLp 2` with respect to the
  chart-pulled weighted measure restricted to `chartTargetEuclid α`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart-Euclidean right-hand side of the eigenvector weak-solution
assembly (chart-locality-free).** Keyed onto the unconditional eigenvector chart
component and the unconditional cross- and lower-order limit objects. -/
noncomputable def eigenvectorChartRHS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (i.fst.val)⁻¹ *
      (
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
        - (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        - covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y
        - covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y
        + (1 / densityOnEuclid (I := I) g α y) *
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y)
        - (1 / densityOnEuclid (I := I) g α y) *
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ y)

/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞`
(`densityOnEuclid_contDiffOn`) and strictly positive (`densityOnEuclid_pos`)
there, so the quotient `1 / densityOnEuclid g α` is `C^∞`. -/
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

/-- The cross-right gradient-divergence limit vanishes pointwise off the compact
partition-of-unity kernel `chartPouKernel α` (chart-locality-free). Every summand
of its explicit finite-sum definition carries an `indicator (chartPouKernel α)`
factor. -/
lemma crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ y = 0 := by
  classical
  rw [crossRightGradCoeffDivLimit,
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    add_zero]

/-- **Weighted-`L²` membership of the cross-right gradient-divergence limit
(chart-locality-free).** The limit is
`MemLp 2 (chartL2Measure α)` by `crossRightGradCoeffDivLimit_memLp`,
vanishes pointwise — hence a.e. — off the compact partition-of-unity kernel, and
the weighted-measure upgrade lemma delivers weighted `MemLp`. -/
private lemma crossRightGradCoeffDivLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Weighted-`L²` membership of the chart-Euclidean right-hand side
(chart-locality-free).** The chart-Euclidean right-hand side
`eigenvectorChartRHS g r s i α P₀` is `MemLp 2` with respect to the
chart-pulled weighted measure `(chartPulledWeightedMeasure g α).restrict
(chartTargetEuclid α)`.

Keyed onto the unconditional eigenvector chart component, the unconditional
cross- and lower-order limit objects, and their chart-locality-free
`…_memLp_weighted_unconditional` lemmas. The product helper
`memLp_weighted_contDiffOn_mul` and finite-sum closure of `MemLp` deliver the
membership. -/
theorem eigenvectorChartRHS_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have h_uchart : MemLp
      (fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    rw [hμw_def]
    exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) α P₀
  have h_crossLeft : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossLeftLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α P)
      h_aezero
  have h_crossRight : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α P)
      h_aezero
  have h_prc : MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
      g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covPrincipalRotationCoeffLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀
  have h_lov : MemLp (covLowerOrderRotationValueCoeffLimit
      (I := I) (M := M) g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covLowerOrderRotationValueCoeffLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀
  have h_gradDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y)) 2 μw := by
    rw [hμw_def]
    have h_div_sum : MemLp
        (fun y => ∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      memLp_finset_sum (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l _ => weightedGradCoeffDivLimit_memLp_weighted_unconditional
          (I := I) (M := M) g r s i α P₀ l)
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        Finset.sum_eq_zero (fun l _ =>
          weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
            (I := I) (M := M) g r s i α P₀ l hy))
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      h_div_sum h_aezero
  have h_crossRightDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y) 2 μw := by
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ y = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ hy)
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
        g r s i α P₀)
      h_aezero
  have h_crossLeft_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
        (fun Q _ => h_crossLeft P Q))
  have h_crossRight_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => h_crossRight P Q))
  have h_total :
      MemLp (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀) 2
        μw := by
    have h_bracket :=
      ((((((h_uchart.sub h_crossLeft_sum).add h_crossRight_sum).sub h_prc).sub
        h_lov).add h_gradDiv).sub h_crossRightDiv)
    have h_assembled := h_bracket.const_mul (i.fst.val)⁻¹
    refine h_assembled.ae_eq ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [eigenvectorChartRHS, Pi.add_apply, Pi.sub_apply]
  rw [hμw_def] at h_total
  exact h_total

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
