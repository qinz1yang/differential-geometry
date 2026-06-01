import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LaplacianDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.WeakPartialOnVolume
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

/-!
# Iterated `H^{2k}` regularity for the iterated Laplacian domain

For a closed Riemannian manifold `(M, g)`, this file establishes the
non-smooth iterated regularity result:

* For `k ≤ 1`, every `u_h ∈ laplacianDomainPow g k` satisfies the chart-Sobolev
  membership `MemWkpChart g (2k) 2 ((H1ComplToLp u_h).coeFn)` with a finite
  chart-based norm.

The `k = 0` case is the trivial `Lp` membership of the canonical
representative. The `k = 1` case is the unconditional single-step `H²`
regularity (`laplacianDomain_memWkpChart_two_unconditional`).

## Strategy

For `k = 0`:
* `MemWkpChart g 0 2` reduces (via `MemWkp_zero`) to `MemLp 2` on each chart
  target.
* The canonical representative `(H1ComplToLp u_h).coeFn` of any `Lp` class is
  in `MemLp 2` globally, hence on every chart target.
* The norm is bounded by the global `Lp` norm.

For `k = 1`:
* `laplacianDomainPow g 1 = laplacianDomain g` by `laplacianDomainPow_one`.
* Apply `laplacianDomain_memWkpChart_two_unconditional`.

## Higher orders

For `k ≥ 2`, the iterated bootstrap requires differentiating the
chart-bilinear identity `k - 1` times in chart directions and re-applying the
single-step difference-quotient regularity at each level. The full bootstrap
is the standard Nirenberg–Schauder bootstrap and constitutes substantial
additional chart-bilinear infrastructure beyond the scope of this module.

The combinator `laplacianDomainPow_memWkpChart_two_k` packages the available
cases under the unified statement `MemWkpChart g (2k) 2 ...` and exposes the
recursive structure so that downstream consumers (in particular, the heat
semigroup `h_iterated_regularity` discharge in
`Analysis/HeatEquation/Smoothing.lean`) can invoke it.

## Main theorems

* `iteratedH2Regularity_zero` — `k = 0` case.
* `iteratedH2Regularity_one` — `k = 1` case.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

/-- The chart-pushed function of a measurable `Lp 2` class function is in
`MemLp 2 (volume.restrict K)` for any compact subset `K` of the chart target.
This is the direct analogue of `chartPushedWeakPartialLp_locally_memLp` for
the chart-pushed function itself (rather than for its weak partial). -/
private lemma chartPushed_lp_class_locally_memLp_volume
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        ((u_lp : M → ℝ))) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  have h_lp_meas : Measurable ((u_lp : M → ℝ)) :=
    (Lp.stronglyMeasurable u_lp).measurable
  have h_lp_memLp_global : MemLp ((u_lp : M → ℝ)) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := Lp.memLp u_lp
  have h_memLp_w := chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
    (I := I) (M := M) g α h_lp_meas h_lp_memLp_global
  exact memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
    h_memLp_w hK_compact hK_compact.isClosed.measurableSet hK_in

/-- The chart-pushed function of any `Lp ℝ 2 μ_g` class is `MemLp 2`-locally
in each chart target. This is the chart-Sobolev `k = 0` regularity.

The chart-pushed function is supported in the compact image of
`tsupport (ρ_α)` and on this compact set the chart-density is bounded
above and below by positive constants. Combined with the existing
`MemLp 2` of the chart-pushed function against the chart-pulled weighted
measure, this gives `MemLp 2` against `volume.restrict (chartTargetEuclid α)`. -/
theorem memWkpChart_zero_of_lp
    (g : SmoothRiemannianMetric I M)
    (u_lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemWkpChart (I := I) (M := M) g 0 2 ((u_lp : M → ℝ)) := by
  intro α
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero]
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_in_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_memLp_K : MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        ((u_lp : M → ℝ))) 2
      ((volume : Measure EuclN).restrict K) :=
    chartPushed_lp_class_locally_memLp_volume (I := I) (M := M) g α u_lp
      hK_compact hK_in_target
  set f : EuclN → ℝ := chartPushed (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α ((u_lp : M → ℝ))
    with hf_def
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_chart_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_zero_off : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, y ∉ K → f y = 0 :=
    fun y hy hy_off => chartPushed_eq_zero_off_chartImagePOUTsupport
      (I := I) (M := M) α ((u_lp : M → ℝ)) hy hy_off
  have h_pointwise_eq : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      f y = Set.indicator K f y := by
    intro y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, h_zero_off y hy hyK]
  have h_ind_memLp_global : MemLp (Set.indicator K f) 2 (volume : Measure EuclN) := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hK_meas]
    exact h_memLp_K
  have h_ind_memLp_chartTarget : MemLp (Set.indicator K f) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    h_ind_memLp_global.restrict _
  have h_ae_eq : (fun y => f y) =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => Set.indicator K f y) :=
    (MeasureTheory.ae_restrict_iff' h_chart_meas).mpr
      (Filter.Eventually.of_forall (fun y hy => h_pointwise_eq y hy))
  exact h_ind_memLp_chartTarget.ae_eq h_ae_eq.symm

/-- **Iterated `H^{2k}` regularity for `laplacianDomainPow g k`** — the
unified headline.

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`,
`k = 0`, and any `u_h ∈ laplacianDomainPow g 0 = ⊤`, the canonical function
representative `((H1ComplToLp u_h) : M → ℝ)` lies in `MemWkpChart g 0 2`
(which is just `MemLp 2` on chart targets). -/
theorem iteratedH2Regularity_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_zero_of_lp (I := I) (M := M) g
    (H1ComplToLp (I := I) (M := M) g u_h)

/-- **Iterated `H²` regularity for `laplacianDomainPow g 1` (= `laplacianDomain g`)**.

For a closed Riemannian manifold `(M, g)` and any
`u_h ∈ laplacianDomainPow g 1`, the canonical function representative
`((H1ComplToLp u_h) : M → ℝ)` lies in `MemWkpChart g 2 2`, with a finite
chart-based norm. -/
theorem iteratedH2Regularity_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  rw [laplacianDomainPow_one] at hu_h
  exact LaplacianDomainPerChartWitness.laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g hu_h

/-- **Iterated `H^{2k}` regularity for `laplacianDomainPow g k`** at the
`k = 0` and `k = 1` boundary.

For a closed Riemannian manifold `(M, g)` and any
`u_h ∈ laplacianDomainPow g k` with `k ≤ 1`, the canonical function
representative `((H1ComplToLp u_h) : M → ℝ)` lies in `MemWkpChart g (2k) 2`. -/
theorem laplacianDomainPow_memWkpChart_two_k_le_one
    (g : SmoothRiemannianMetric I M)
    {k : ℕ} (hk : k ≤ 1)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  interval_cases k
  · simpa using iteratedH2Regularity_zero (I := I) (M := M) g u_h
  · have h_one : 2 * 1 = 2 := by norm_num
    rw [h_one]
    exact (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1

end Laplacian
end Analysis
end DifferentialGeometry

end
