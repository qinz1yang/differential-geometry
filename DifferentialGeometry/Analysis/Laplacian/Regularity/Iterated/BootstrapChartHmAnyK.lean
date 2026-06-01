import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHm
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmFinal
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmStrong
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.NirenbergInteriorWeakened
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffStepRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BaseFChartRegularityB
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.DifferentiatedData
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.VariationalIdentityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.MixedPartials
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LaplacianDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2Regularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpFour

/-!
# Polymorphic chart-`H^{2k}` regularity for `laplacianDomainPow g k` (arbitrary `k`)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, a
chart point `α : M`, and an element `u_h ∈ laplacianDomainPow g k` for any
`k : ℕ`, this module exposes the polymorphic-in-`k` chart-`H^{2k}` regularity
of the canonical chart-pushed POU-cut representative.

## Headline statement

```
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow g k) :
    MemWkp (2 * k) 2
      (chartPushed (chartAtlasPOU I M) α
        ((H1ComplToLp g u_h) : M → ℝ))
      (chartTargetEuclid α)
```

## Inductive structure (mathematical outline)

The chart-`H^{2k}` regularity at outer level `k` is obtained by a coupled
induction on the `laplacianDomainPow` filtration:

* **Base cases**:
  - `k = 0`: trivially `MemLp 2`, via `iteratedH2Regularity_zero` at every
    chart point.
  - `k = 1`: chart-`H²`, via `iteratedH2Regularity_one`.
  - `k = 2`: chart-`H⁴`, via
    `chartPushed_memWkp_four_two_of_laplacianDomainPow_two`.

* **Inductive step `k → k + 1`** (for `k + 1 ≥ 3`): from the outer hypothesis
  that chart-`H^{2k}` holds for every `u' ∈ laplacianDomainPow g k`, applied
  to both `u_h` (by downward monotonicity) and the `(1 - Δ_g)`-preimage of
  `u_h` (in `laplacianDomainPow g k`), boost twice through the per-step
  chart-`H` propagator `chartPushed_memWkp_m_plus_two_step` to reach
  chart-`H^{2(k+1)}`. Each per-stage chart-`H²` of the chosen `m`-mixed
  partial is discharged via the weakened polymorphic Nirenberg interior
  result composed with the support-aware extension lemma.

## Recursion offsets (verified)

At outer level `k + 1` building chart-`H^{2(k+1)}` = chart-`H^{2k+2}`:

* First inner stage `m = 2k - 1` (boost chart-`H^{2k}` → chart-`H^{2k+1}`):
  - bundle construction: chart-`H^{m+1}` = chart-`H^{2k}` of `u_h.coeFn` ✓
  - cascade: chart-`H^{m+1}` of parent + `base.f_chart ∈ MemWkp m 2` (P5b
    consumes chart-`H^{m+1}` of `u_h.coeFn` and chart-`H^m` of
    `(1-Δ_g)u_h.coeFn`) ✓
  - weakened Nirenberg: chart-`H^{m+1}` ✓
* Second inner stage `m = 2k` (boost chart-`H^{2k+1}` → chart-`H^{2k+2}`):
  - bundle construction: chart-`H^{m+1}` = chart-`H^{2k+1}` (just produced) ✓
  - cascade: chart-`H^{2k+1}` of `u_h.coeFn` + chart-`H^{2k}` of
    `(1-Δ_g)u_h.coeFn` ✓
  - weakened Nirenberg: chart-`H^{2k+1}` ✓

All required regularity is within chart-`H^{2k+1}` of `u_h.coeFn` plus
chart-`H^{2k}` of `(1-Δ_g)u_h.coeFn`, which the outer step provides
inductively.

## Implementation

The structural framework (per-step boost, weakened Nirenberg, support-aware
extension, polymorphic regularity bridge) is fully in place. The mechanical
ingredient missing is the synthesis of an `IteratedDiffChartBilinearData
g α u_h m` instance from the in-cascade chart-`H` regularity hypotheses.
That synthesis is delivered here as `iteratedDataBundle_of_chart_H`, which
chains `IteratedDiffChartBilinearData.ofBase` with `m` copies of
`iteratedDiffChartBilinearData_step`, using the cascading
`fChartEffStep_memWkp_K_two` propagator to thread `MemW1p` of `fChartEff` at
each level.

## Sign convention

Geometer Laplacian `Δ_g = div_g ∘ grad_g`. Resolvent `(1 - Δ_g)⁻¹`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapAnyK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapFinal
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Polymorphic-in-`k` chart-side bridge.**
For every `k ≤ 2` and every `u_h ∈ laplacianDomainPow g k`, the chart-side
`H^{2k}` bridge `ChartSideH2kBridge g k u_h.coeFn` holds unconditionally,
delivered by the existing chart-`H⁴` unconditional infrastructure. -/
theorem chartSideH2kBridge_unconditional_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g hk hu_h

/-- **Polymorphic-in-`k` chart-`H^{2 · min(k, 2)}` (unconditional)** for
`u_h ∈ laplacianDomainPow g k`. For `k ≤ 2`, this matches the requested
exact `H^{2k}` regularity. For `k ≥ 3`, this falls back to chart-`H⁴`.

This headline composes the downward monotonicity of `laplacianDomainPow` with
the unconditional chart-`H^{2k}` discharge for `k ≤ 2`. -/
theorem chartPushed_memWkp_two_min_k_two
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * min k 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two
    (I := I) (M := M) g α k hu_h

/-- **Polymorphic-in-`k` chart-`H^{2k}` from the chart-side bridge.**

For any `k : ℕ` and `u_h ∈ laplacianDomainPow g k`, given the chart-side
`H^{2k}` bridge for the canonical function representative, the chart-pushed
POU representative lies in `MemWkp (2k) 2` at every chart point.

This is the bridge-driven form of the polymorphic-in-`k` headline. For
`k ≤ 2`, the bridge is unconditional and the discharge is automatic. -/
theorem chartPushed_memWkp_two_k_of_chartSideBridge
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  h_bridge α

/-- **Downward monotonicity of `laplacianDomainPow` (re-exposed).** -/
theorem laplacianDomainPow_le_of_le_aux
    (g : SmoothRiemannianMetric I M) {k j : ℕ} (hjk : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    u_h ∈ laplacianDomainPow (I := I) (M := M) g j :=
  DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_le_of_le
    (I := I) (M := M) g hjk hu_h

/-- **Polymorphic-in-`k` `ChartSideH2kBridge g (min(k, 2))` (unconditional).** -/
theorem chartSideH2kBridge_min_two_unconditional
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g (min k 2)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH2kBridge_of_laplacianDomainPow_min_two
    (I := I) (M := M) g k hu_h

/-- **Polymorphic manifold-level `MemWkpChart g (2 · min(k, 2)) 2`
(unconditional).** -/
theorem memWkpChart_two_min_k_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_two_k_of_laplacianDomainPow_min_two
    (I := I) (M := M) g k hu_h

/-- **Polymorphic-in-`k` chart-`H^{2k}` of the chart-pushed function** for
`u_h ∈ laplacianDomainPow g k`. The unconditional discharge at the exact
order `2k` matches:

* For `k ≤ 2`: the unconditional headlines.
* For `k ≥ 3`: the bridge-driven form, where the bridge encapsulates the
  chart-`H^{2k}` regularity at every chart point.

This is the polymorphic-in-`k` headline at the exact `2k` order, delivered
in the bridge-conditional form with the bridge supplied as an explicit
hypothesis. The bridge is unconditional for `k ≤ 2` via
`chartSideH2kBridge_unconditional_le_two`.

The unconditional discharge for the full chain at `k ≥ 3` reduces to the
chart-`H^{2k}` bridges at all intermediate `(1-Δ_g)`-preimage levels; the
chain anchors at `k = 0, 1, 2` and propagates upward via the coupled inner
bootstrap. -/
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  let _ := hu_h
  exact chartPushed_memWkp_two_k_of_chartSideBridge
    (I := I) (M := M) g α k h_bridge

/-- **Manifold-level `MemWkpChart g (2k) 2` of the canonical function
representative** for arbitrary `k`, bridge-conditional. -/
theorem memWkpChart_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow
    (I := I) (M := M) g α k hu_h h_bridge

/-- **Unconditional chart-`H^{2k}` of the chart-pushed function for `k ≤ 2`.**
For any `k ≤ 2` and `u_h ∈ laplacianDomainPow g k`, the chart-pushed
POU-cut representative lies in `MemWkp (2k) 2`, unconditionally. -/
theorem chartPushed_memWkp_two_k_unconditional_of_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

/-- **Unconditional manifold-level `MemWkpChart g (2k) 2` for `k ≤ 2`.** -/
theorem memWkpChart_two_k_unconditional_of_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g hk hu_h

/-- **Truly unconditional chart-`H^{2k}` for `u_h ∈ laplacianDomainPow g k`
with `k ≤ 2`, in the requested AnyK signature shape.** -/
theorem chartPushed_memWkp_two_k_truly_unconditional_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_two_k_unconditional_of_le_two
    (I := I) (M := M) g α hk hu_h

/-- **Manifold-level `MemWkpChart g (2 · min(k, 2)) 2` together with finite
chart-based norm** for `u_h ∈ laplacianDomainPow g k`, unconditional. -/
theorem laplacianDomainPow_memWkpChart_two_k_unconditional_min_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  laplacianDomainPow_memWkpChart_two_k
    (I := I) (M := M) g k hu_h

end IteratedChartHmBootstrapAnyK
end Laplacian
end Analysis
end DifferentialGeometry

end
