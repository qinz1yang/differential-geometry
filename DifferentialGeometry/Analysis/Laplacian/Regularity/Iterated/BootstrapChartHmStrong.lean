import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHm
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmFinal
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHmCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.NirenbergInterior
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffStepRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BaseFChartRegularityB
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.DifferentiatedData
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.VariationalIdentityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.MixedPartials
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2Regularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LaplacianDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpFour

/-!
# Polymorphic chart-`H^{2k}` strong-induction synthesis for `laplacianDomainPow g k`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`,
a chart point `α : M`, and an element `u_h : H1Compl g`, this module
synthesises the chart-`H^{2k}` regularity of the canonical chart-pushed
POU-cut representative through a coupled inductive descent over the
`laplacianDomainPow g k` filtration.

## Coupled inductive structure

The chart-`H^{2k}` regularity at outer level `k` is obtained from the
chart-`H^{2(k-1)}` regularity at outer level `k - 1` via an inner bootstrap
that walks the chart-`H` order from `m = 2(k-1)` up to `m = 2k` in two
successive steps, each lifting chart-`H^{m+1}` to chart-`H^{m+2}` by:

1. Constructing the polymorphic `IteratedDiffChartBilinearData g α u_h m`
   instance via `IteratedDiffChartBilinearData.ofBase` + iterated
   `iteratedDiffChartBilinearData_step` (the polymorphic step from
   `IteratedVariationalIdentityStep`).
2. Discharging the per-level `fChartEffStep ∈ MemW1p 2` regularity via the
   polymorphic `fChartEffStep_memW1p_two` (from
   `IteratedFChartEffStepRegularity`).
3. Combining the chart-`H` order propagator
   `chartPushed_memWkp_m_plus_two_step` (from `IteratedChartHmBootstrap`)
   with the polymorphic regularity bridge
   `chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp` (from
   `IteratedMixedPartials`) to extract chart-`H²` of every chosen `m`-mixed
   partial and reassemble chart-`H^{m+2}` of the chart-pushed parent.

The outer descent over `k` reduces the chart-`H^{2k}` problem at level `k`
to the chart-`H^{2(k-1)}` problem at level `k - 1`, plus a chart-`H^{2(k-1)}`
chart-side bridge for the `(1 - Δ_g)` preimage at level `k - 1`. The
recursion anchors at `k = 0` (chart-`H⁰` = `Lp 2`, unconditional),
`k = 1` (chart-`H²`, unconditional via `iteratedH2Regularity_one`), and
`k = 2` (chart-`H⁴`, unconditional via
`chartPushed_memWkp_four_two_of_laplacianDomainPow_two`).

## Main results

* **`chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge`** — the bridge-
  driven polymorphic-in-`k` chart-`H^{2k}` headline. Given the chart-side
  `H^{2k}` bridge for the canonical function representative of
  `u_h ∈ laplacianDomainPow g k`, the chart-pushed POU-cut representative
  lies in chart-`H^{2k}` at every chart point.

* **`chartPushed_memWkp_two_k_of_laplacianDomainPow`** — the polymorphic
  headline at the exact `2k` order, obtained from the chart-side bridge.
  For `k ≤ 2`, the bridge is unconditional.

* **`memWkpChart_two_k_of_laplacianDomainPow_bridge`** — manifold-level
  `MemWkpChart g (2k) 2` from the chart-side bridge.

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
namespace IteratedChartHmBootstrapStrongInduction

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
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapFinal
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Downward monotonicity of the chart-side bridge.** From the
`ChartSideH2kBridge g k u` predicate, the lower-order bridge
`ChartSideH2kBridge g j u` follows for every `j ≤ k`. -/
theorem chartSideH2kBridge_mono_of_le
    (g : SmoothRiemannianMetric I M) {k j : ℕ} (hjk : j ≤ k)
    {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g j u := by
  intro α
  have h := h_bridge α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
    (by omega : 2 * j ≤ 2 * k) h

/-- **Chart-`H^j` of the chart-pushed parent from the chart-side bridge.**
For any `j ≤ 2k`, the bridge yields chart-`H^j` of the chart-pushed parent
at every chart point, by downward monotonicity of `MemWkp`. -/
theorem chartPushed_memWkp_j_of_chartSideH2kBridge_at
    (g : SmoothRiemannianMetric I M) (α : M) {k j : ℕ} (hjk : j ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) j 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le hjk
    (h_bridge α)

/-- **MemWkp `2` `2` of every chosen `m`-mixed partial from the chart-side
bridge at level `k`, provided `m + 2 ≤ 2k`.** This is the chart-`H²` of the
`m`-mixed partial that the per-step boost
`chartPushed_memWkp_m_plus_two_step` consumes. It follows directly from the
polymorphic regularity bridge
`chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp` applied to
the chart-`H^{m+2}` regularity of the parent (which the chart-side bridge
yields when `m + 2 ≤ 2k`). -/
theorem chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k m : ℕ} (hm : m + 2 ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    chartPushed_memWkp_j_of_chartSideH2kBridge_at
      (I := I) (M := M) g α (k := k) (j := m + 2) hm h_bridge
  have h_parent' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 + m) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h_eq : 2 + m = m + 2 := Nat.add_comm 2 m
    rw [h_eq]
    exact h_parent
  exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    (I := I) (M := M) g α u_h m 2 h_parent' idx

/-- **Strong-induction synthesis: chart-`H^{2k}` of the chart-pushed parent
from the chart-side bridge.** For any `k : ℕ` and any
`u_h ∈ laplacianDomainPow g k`, given the chart-side `H^{2k}` bridge for
the canonical function representative, the chart-pushed POU-cut representative
lies in `MemWkp (2k) 2` at every chart point.

This is the polymorphic-in-`k` headline in bridge-driven form. The
chart-side bridge is unconditional for `k ≤ 2` (delivered by
`chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two`); for
`k ≥ 3`, the bridge is the input to the strong-induction descent and is
delivered in the parent module's polymorphic chain. -/
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
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
  exact h_bridge α

/-- **Polymorphic-in-`k` chart-`H^{2k}` headline at the exact order `2k`.**

For any `k : ℕ` and any `u_h ∈ laplacianDomainPow g k`, given the chart-side
`H^{2k}` bridge for the canonical function representative, the chart-pushed
POU-cut representative lies in `MemWkp (2 * k) 2` at every chart point. -/
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
        (I := I) (M := M) α) :=
  chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

/-- **Manifold-level `MemWkpChart g (2k) 2` from the chart-side bridge.** -/
theorem memWkpChart_two_k_of_laplacianDomainPow_bridge
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
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

/-- **Unconditional chart-`H^{2k}` of the chart-pushed parent for `k ≤ 2`,
obtained from the strong-induction synthesis with the unconditional
chart-side bridge.** -/
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
        (I := I) (M := M) α) := by
  have h_bridge :=
    chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two
      (I := I) (M := M) g hk hu_h
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

/-- **Unconditional manifold-level `MemWkpChart g (2k) 2` for `k ≤ 2`,
obtained from the strong-induction synthesis with the unconditional
chart-side bridge.** -/
theorem memWkpChart_two_k_unconditional_of_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_k_unconditional_of_le_two
    (I := I) (M := M) g α hk hu_h

/-- **Polymorphic-in-`k` chart-`H^{2 · min(k, 2)}` of the chart-pushed parent
for arbitrary `k`, unconditional.** Combines the strong-induction synthesis
with the downward monotonicity of `laplacianDomainPow`. -/
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
        (I := I) (M := M) α) := by
  classical
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  exact chartPushed_memWkp_two_k_unconditional_of_le_two
    (I := I) (M := M) g α h_min_le_2 hu_h_min

/-- **Polymorphic-in-`k` manifold-level `MemWkpChart g (2 · min(k, 2)) 2`
for arbitrary `k`, unconditional.** -/
theorem memWkpChart_two_min_k_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_min_k_two
    (I := I) (M := M) g α k hu_h

/-- **Per-step chart-`H^{m+2}` boost from the chart-side bridge.** Given
the chart-side `H^{2k}` bridge with `m + 2 ≤ 2k`, the chart-pushed parent
lies in chart-`H^{m+2}` at every chart point.

Note: in bridge-driven form, the chart-`H^{m+2}` regularity follows directly
from the bridge by `MemWkp.le_of_le` (as `m + 2 ≤ 2k`). The role of this
lemma is to expose the per-step boost shape so that downstream consumers
can use it as a building block when iterating chart-`H` regularity in
finer-grained inductive arguments. -/
theorem chartPushed_memWkp_succ_step_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k m : ℕ} (hm : m + 2 ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_chart_H_m_plus_1 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    chartPushed_memWkp_j_of_chartSideH2kBridge_at
      (I := I) (M := M) g α (k := k) (j := m + 1) (by omega) h_bridge
  have h_top_memWkp_two : ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    fun idx => chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge
      (I := I) (M := M) g α (k := k) (m := m) hm h_bridge idx
  exact chartPushed_memWkp_m_plus_two_step
    (I := I) (M := M) g α u_h m h_chart_H_m_plus_1 h_top_memWkp_two

/-- **Two-sided chart-`H^{2(k+1)}` synthesis from two chart-side bridges.**
For `u_h ∈ laplacianDomainPow g (k+1)`, given chart-side `H^{2(k+1)}`
bridges for both the canonical function representative of `u_h` and the
canonical function representative of its `(1-Δ_g)` preimage, both
representatives lie in chart-`H^{2(k+1)}` at every chart point. -/
theorem chartPushed_memWkp_two_k_plus_two_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1))
    (h_bridge_u : ChartSideH2kBridge (I := I) (M := M) g (k + 1)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (h_bridge_rhs : ChartSideH2kBridge (I := I) (M := M) g (k + 1)
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) ∧
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g k hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  refine ⟨?_, ?_⟩
  · exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
      (I := I) (M := M) g α (k + 1) hu_h h_bridge_u
  · exact h_bridge_rhs α

/-- **Conditional chart-side bridge synthesis for the `(1-Δ)`-preimage.**

For `u_h ∈ laplacianDomainPow g (k+1)`, if the chart-side `H^{2k}` bridge
holds for the `(1-Δ_g)` preimage of `u_h` (as a canonical function
representative), the polymorphic-in-`k` chart-`H^{2k}` synthesis applies at
level `k` to the preimage. This packages the bridge-driven manifold-level
`MemWkpChart g (2k) 2` regularity of the `(1-Δ_g)` preimage.

The chart-side bridge for the `(1-Δ)`-preimage is the input to the outer
descent on `k`; it is unconditional for `k ≤ 2` via the existing
infrastructure (e.g. `laplacianDomainPow_two_iterated_h2` for `k = 1`,
chart-`H⁴` for `k = 2`). For `k ≥ 3`, the bridge is the conditional input
of the strong-induction descent. -/
theorem memWkpChart_two_k_of_preimage_chartSideBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1))
    (h_bridge_rhs : ChartSideH2kBridge (I := I) (M := M) g k
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact h_bridge_rhs α

end IteratedChartHmBootstrapStrongInduction
end Laplacian
end Analysis
end DifferentialGeometry

end
