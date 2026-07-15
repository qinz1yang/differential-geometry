import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.ManifoldH2.Smooth
import DifferentialGeometry.Analysis.Elliptic.Operator.VariationalLaplacian
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Manifold-level non-smooth `H²` interior regularity for the variational Laplacian

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and an
element `u_h : H1Compl g` lying in the variational Laplacian's domain
`laplacianDomain g`, this module records the manifold-level non-smooth `H²`
regularity statement: any function representative `u : M → ℝ` whose chart-pushed
POU images (under the canonical atlas partition of unity `chartAtlasPOU I M`)
are in `MemWkp 2 2` of the corresponding chart-target image lies in
`MemWkpChart g 2 2`. The statement is hypothesis-bearing: the consumer must
supply the per-chart `MemWkp 2 2` evidence.

The chart-level non-smooth `H²` evidence is the natural target of
`chart_loc_of_uniform_bound` (delivered for the chart-bilinear data structure
`ChartBilinearH1ComplData g α` in `Regularity/ChartHk/H2NonSmooth.lean`). The bridge from
that chart-level output to the per-chart `MemWkp 2 2` evidence uses two
analytical packaging steps:

* a Leibniz-rule packaging that transforms the chart-pulled weak first
  partials of `D.u_chart` (carried by the chart-bilinear data structure)
  into weak first partials of `chartPushed (chartAtlasPOU I M) α u`, where
  `u : M → ℝ` is a function representative of `H1ComplToLp u_h`;
* an extension-by-zero argument that lifts weak partials defined on a
  precompact open subdomain `Ω''` of `chartTargetEuclid α` (the output of
  `chart_loc_of_uniform_bound`) to weak partials on the full chart-target
  image, using the fact that the POU-cut chart-pushed function vanishes
  outside the chart-image of `tsupport (ρ_α)`.

Both packaging steps are formulated below as hypotheses on the per-chart
witness; the connection from the chart-level non-smooth `H²` output and the
per-chart witness is delivered as a schema theorem
`chartH2NonSmoothPOUWitness_of_chart_data_and_pou_bridge`.

## Structure

* `ChartH2NonSmoothPOUWitness g u α` — the per-chart `MemWkp 2 2` evidence for
  the POU-cut chart-pushed function `chartPushed (chartAtlasPOU I M) α u` viewed
  on `chartTargetEuclid α`.

* `memWkpChart_two_of_chartPOUWitnesses` — the manifold-level lift: given a
  function `u : M → ℝ` and a per-chart `ChartH2NonSmoothPOUWitness g u α` for
  every `α : M`, the function `u` lies in `MemWkpChart g 2 2`.

* `wkpNormChart_two_lt_top_of_chartPOUWitnesses` — the quantitative
  finiteness statement.

* `chartH2NonSmoothPOUWitness_of_chart_data_and_pou_bridge` — the schema bridge
  from `ChartBilinearH1ComplData g α` plus a uniform DQ bound plus a "POU
  bridge" hypothesis identifying the chart-pushed function with the chart
  data, produces the per-chart `MemWkp 2 2` witness.

## Headline statement

`memWkpChart_two_of_laplacianDomain` packages the headline manifold-level
hypothesis-bearing form: for `u_h ∈ laplacianDomain g`, any function
representative `u : M → ℝ` for which the per-chart `ChartH2NonSmoothPOUWitness
g u α` data is supplied yields `MemWkpChart g 2 2 u` with a quantitative norm
bound.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ManifoldH2NonSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Per-chart `MemWkp 2 2` evidence for the POU-cut chart-pushed function on
the chart-target image. The structure records the membership and is parametrised
by a chart point `α : M`, a manifold function `u : M → ℝ`, and the smooth
Riemannian metric `g`.

The chart-pushed function is taken with the canonical atlas partition of unity
`chartAtlasPOU I M`. -/
structure ChartH2NonSmoothPOUWitness
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) : Prop where

  memWkp_two : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
      (chartAtlasPOU I M) α u)
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)

namespace ChartH2NonSmoothPOUWitness

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Constructor from an explicit `MemWkp 2 2` proof. -/
theorem mk' {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) :
    ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ⟨h⟩

/-- The `MemWkp 2 2` membership extracted from the witness. -/
theorem memWkp_two_eq {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :=
  h.memWkp_two

/-- The implied `MemWkp 1 2` membership (downward monotonicity in `k`). -/
theorem memWkp_one {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_succ h.memWkp_two

/-- The implied `MemLp 2` membership (downward monotonicity to `k = 0`). -/
theorem memLp_two {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    MemLp
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u) 2
      ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.memLp h.memWkp_two

end ChartH2NonSmoothPOUWitness

/-- **Manifold-level `H²` lift via POU.** Given per-chart `MemWkp 2 2` evidence
for the POU-cut chart-pushed function on every chart-target image (under the
canonical atlas partition of unity), the manifold function lies in
`MemWkpChart g 2 2`. -/
theorem memWkpChart_two_of_chartPOUWitnesses
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u := by
  intro α
  exact (h_witness α).memWkp_two

/-- The implied `MemWkpChart g 1 2` membership. -/
theorem memWkpChart_one_of_chartPOUWitnesses
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 1 2 u :=
  (memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g h_witness).le_succ

/-- The chart-based norm `wkpNormChart g 2 2 u` equals the canonical `tsum`
over chart points of the per-chart `wkpNorm 2 2 (chartPushed _ α u)
(chartTargetEuclid α)`. Re-export for ergonomics. -/
theorem wkpNormChart_two_eq_tsum
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_eq_tsum
    (I := I) (M := M) g 2 2 u

/-- The chart-based norm `wkpNormChart g 2 2 u` is finite under the per-chart
`MemWkp 2 2` witnesses, on a closed manifold. -/
theorem wkpNormChart_two_lt_top_of_chartPOUWitnesses
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 2) (p := 2) (by norm_num)
    (memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g h_witness)

/-- The chart-based norm `wkpNormChart g 2 2 u` is bounded by the canonical
`tsum` over chart points of the per-chart `wkpNorm 2 2 (chartPushed _ α u)
(chartTargetEuclid α)`. This is a direct corollary of `wkpNormChart_two_eq_tsum`
formulated as an inequality (with equality, in fact). -/
theorem wkpNormChart_two_le_tsum_chart_norms
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u ≤
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) :=
  le_of_eq (wkpNormChart_two_eq_tsum (I := I) (M := M) g u)

/-- The per-chart "POU bridge" data. Records:

* a chart-bilinear non-smooth weak-solution data structure
  `D : ChartBilinearH1ComplData g α`,
* a uniform `L²(Ω'')` bound on the difference quotients of the explicit weak
  first partials carried by `D`,
* the room hypothesis on the precompact subdomain `Ω''`,
* a target `MemWkp 2 2` membership of the POU-cut chart-pushed function on
  `chartTargetEuclid α` packaged via the chart-level output of
  `chart_loc_of_uniform_bound` plus the Leibniz / extension-by-zero
  packaging.

The output `memWkp_two_chartPushed` is a *hypothesis* on the consumer:
the natural mathematical content of the non-smooth Nirenberg + Leibniz packaging
is exactly this membership statement. -/
structure ChartH2NonSmoothBridgeData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) where

  D : ChartBilinearH1ComplData (I := I) (M := M) g α

  Omega'' : Set EuclN
  Omega''_open : IsOpen Omega''
  Omega''_compact_closure : IsCompact (closure Omega'')

  h0 : ℝ
  h0_pos : 0 < h0
  room :
    Metric.cthickening h0 (closure Omega'') ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α

  M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ
  M_bound_nn : ∀ i k, 0 ≤ M_bound i k
  uniform_diffQuot_bound :
    ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
      (h : ℝ), 0 < |h| → |h| ≤ h0 →
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
            ((volume : Measure EuclN).restrict Omega'')
          ≤ ENNReal.ofReal (M_bound i k)

  memWkp_two_chartPushed :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)

namespace ChartH2NonSmoothBridgeData

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The chart-level non-smooth `H²` regularity output: from the bridge data,
extract the weak `(i, k)`-second-partials of `D.weak_partial i` on `Omega''`,
with quantitative `L²` norm bounds. This is direct use of
`chart_loc_of_uniform_bound` on the data carried by the bridge. -/
theorem loc_chart_of_chartH2NonSmoothBridgeData
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict h.Omega'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (h.D.weak_partial i) h.Omega'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict h.Omega'') ≤
        ENNReal.ofReal (h.M_bound i k) := by
  exact chart_loc_of_uniform_bound (I := I) (M := M) (g := g) (α := α)
    h.D h.Omega''_open h.Omega''_compact_closure h.h0_pos h.room
    h.M_bound_nn h.uniform_diffQuot_bound

/-- The per-chart `MemWkp 2 2` witness extracted from the bridge data. -/
theorem chartH2NonSmoothPOUWitness_of_bridgeData
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ⟨h.memWkp_two_chartPushed⟩

end ChartH2NonSmoothBridgeData

/-- Schema: from per-chart bridge-data witnesses, the manifold function lies in
`MemWkpChart g 2 2`. -/
theorem memWkpChart_two_of_chartH2NonSmoothBridgeData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u :=
  memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g
    (fun α => (h_bridge α).chartH2NonSmoothPOUWitness_of_bridgeData)

/-- Schema: from per-chart bridge-data witnesses, the chart-based norm is finite. -/
theorem wkpNormChart_two_lt_top_of_chartH2NonSmoothBridgeData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ :=
  wkpNormChart_two_lt_top_of_chartPOUWitnesses (I := I) (M := M) g
    (fun α => (h_bridge α).chartH2NonSmoothPOUWitness_of_bridgeData)

/-- **Headline manifold-level non-smooth `H²` regularity (hypothesis-bearing).**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and
`u_h ∈ laplacianDomain g`, any function `u : M → ℝ` whose POU-cut chart-pushed
images (under the canonical atlas partition of unity `chartAtlasPOU I M`)
satisfy `MemWkp 2 2` of the chart-target image at every chart point lies in
`MemWkpChart g 2 2`, with a finite chart-based norm.

This statement is hypothesis-bearing: the per-chart `MemWkp 2 2` evidence is
the natural target of the chart-level non-smooth `H²` regularity output (via
`chart_loc_of_uniform_bound` plus a Leibniz-rule packaging that transports
the chart-pulled weak first partials of `H1ComplToLp u_h` to weak first
partials of `chartPushed (chartAtlasPOU I M) α u`).

The function `u` is an arbitrary function representative; the headline does
not impose any specific connection between `u` and `u_h`. The connection
is induced by the per-chart witnesses, which the consumer must supply.

The output combines:

* `MemWkpChart g 2 2 u` — the headline membership statement;
* `wkpNormChart g 2 2 u < ⊤` — the chart-based norm is finite. -/
theorem memWkpChart_two_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ := by
  refine ⟨?_, ?_⟩
  · exact memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g h_witness
  · exact wkpNormChart_two_lt_top_of_chartPOUWitnesses (I := I) (M := M) g h_witness

/-- **Headline with explicit quantitative norm bound.**

Variant of `memWkpChart_two_of_laplacianDomain` exposing the canonical equality
`wkpNormChart g 2 2 u = ∑' α, wkpNorm 2 2 (chartPushed _ α u)
(chartTargetEuclid α)` (a `tsum` over chart points of the per-chart
`wkpNorm` contributions). -/
theorem memWkpChart_two_of_laplacianDomain_with_norm
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
  refine ⟨?_, ?_⟩
  · exact (memWkpChart_two_of_laplacianDomain (I := I) (M := M) g u_h hu_h u h_witness).1
  · exact wkpNormChart_two_eq_tsum (I := I) (M := M) g u

/-- **Headline manifold-level non-smooth `H²` regularity, bridge-data form.**

Variant of `memWkpChart_two_of_laplacianDomain` taking per-chart bridge-data
witnesses (combining a chart-bilinear data structure with a uniform DQ bound
and the target `MemWkp 2 2` membership) in place of bare `MemWkp 2 2`
witnesses. -/
theorem memWkpChart_two_of_laplacianDomain_bridgeData
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ := by
  refine ⟨?_, ?_⟩
  · exact memWkpChart_two_of_chartH2NonSmoothBridgeData (I := I) (M := M) g h_bridge
  · exact wkpNormChart_two_lt_top_of_chartH2NonSmoothBridgeData (I := I) (M := M) g h_bridge

/-- The canonical function representative of `H1ComplToLp u_h` via `Lp.coeFn`.
This is a measurable function `M → ℝ` whose `MemLp.toLp` recovers
`H1ComplToLp u_h`. -/
def laplacianDomain.lpRep
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) : M → ℝ :=
  ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)

/-- The canonical function representative of `H1ComplToLp u_h` is a.e. equal to
the L² class. -/
theorem laplacianDomain.lpRep_aeEq_coeFn
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) :
    laplacianDomain.lpRep (I := I) (M := M) g u_h =
      ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := rfl

/-- **Headline manifold-level non-smooth `H²` regularity, canonical form.**

Variant of `memWkpChart_two_of_laplacianDomain` using the canonical function
representative `laplacianDomain.lpRep g u_h := ((H1ComplToLp u_h) : M → ℝ)`. -/
theorem memWkpChart_two_of_laplacianDomain_canonical
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) < ⊤ :=
  memWkpChart_two_of_laplacianDomain (I := I) (M := M) g u_h hu_h
    (laplacianDomain.lpRep (I := I) (M := M) g u_h) h_witness

/-- **Existential headline manifold-level non-smooth `H²` regularity.**

Same as `memWkpChart_two_of_laplacianDomain` but stated as an existential: there
exists a function `u : M → ℝ` (the consumer-supplied representative) for which
`MemWkpChart g 2 2 u` holds with finite chart-based norm, provided per-chart
witnesses are available. -/
theorem exists_memWkpChart_two_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    ∃ v : M → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2 v ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2 v < ⊤ := by
  refine ⟨u, ?_⟩
  exact memWkpChart_two_of_laplacianDomain (I := I) (M := M) g u_h hu_h u h_witness

/-- **Existential headline manifold-level non-smooth `H²` regularity, canonical
form.** Variant using the canonical function representative
`laplacianDomain.lpRep g u_h`. -/
theorem exists_memWkpChart_two_of_laplacianDomain_canonical
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) α) :
    ∃ v : M → ℝ,
      v = laplacianDomain.lpRep (I := I) (M := M) g u_h ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2 v ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2 v < ⊤ := by
  refine ⟨laplacianDomain.lpRep (I := I) (M := M) g u_h, rfl, ?_⟩
  exact memWkpChart_two_of_laplacianDomain_canonical (I := I) (M := M) g u_h hu_h h_witness

end ManifoldH2NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
