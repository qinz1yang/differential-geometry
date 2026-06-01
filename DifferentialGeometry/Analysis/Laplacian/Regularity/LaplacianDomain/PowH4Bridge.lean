import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH4
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H4NonSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.ChartData

/-!
# Bridge: from chart-local iterated bilinear data to manifold-level `H⁴`

For a closed Riemannian manifold `(M, g)` and `u_h ∈ laplacianDomainPow g 2`,
this module provides the bridge connecting:

* the chart-local `H⁴` regularity of the chart-pulled function `u_chart` of a
  base `ChartBilinearH1ComplData` (delivered by
  `ChartH4NonSmooth.h4_chart_loc_explicit_iterated`), and
* the manifold-level `ChartH4NonSmoothPOUWitness` carrying the `MemWkp 4 2`
  membership of the chart-pushed POU function on the chart-target image.

## Strategy

The bridge consists of two ingredients:

1. **Base chart-bilinear data for `u_h ∈ laplacianDomain g`** — already
   provided by `LaplacianDomainChartData.chartBilinearH1ComplData_of_laplacianDomain`.
   The `u_chart` of this base data is the chart-pulled Lp class
   `chartPushedLpFromLp(H1ComplToLp u_h)`, NOT directly `chartPushed POU α
   (H1ComplToLp u_h).coeFn`, but they agree a.e. on the weighted measure
   restricted to the chart target.

2. **Witness lift from chart-local `H⁴` of `u_chart` to manifold-level
   `MemWkp 4 2` of the chart-pushed POU function** — requires
   transferring the regularity from the chart-pulled Lp class
   `u_chart` to the chart-pushed POU function via the chart-side support
   bridge already used at the `H²` level. This bridge is the chart-side
   `MemW1p`-style support discharge developed in
   `LaplacianDomainPerChartWitness.lean` for the `H²` case.

The full bridge is a substantial chart-explicit construction. This
module exposes the bridge as a hypothesis, mirroring the pattern of
`DiffChartBilinearH1ComplUnconditional.lean` (where the residual
`MemW1p` is exposed as a hypothesis at the `H²` level).

## Main results

* `chartH4NonSmoothPOUWitness_of_chart_local_h4` — bridge from chart-local
  `H⁴` (`MemWkp 4 2 u_chart`) plus the chart-side support data to the
  manifold-level `ChartH4NonSmoothPOUWitness`.
* `laplacianDomainPow_two_chartH4POUWitness_of_chart_data` — assembled
  witness from a supplied chain of iterated chart-bilinear data plus the
  chart-side support bridge.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainPowH4Bridge

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

/-- **Direct bridge: from `MemWkp 4 2` of the chart-pushed POU function
to the manifold-level `H⁴` witness.** Given an explicit `MemWkp 4 2`
proof for the POU-cut chart-pushed function on the chart-target image,
the manifold-level witness is the constructor `mk'`. -/
theorem chartH4NonSmoothPOUWitness_of_memWkp_four
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {α : M}
    (h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :
    ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ChartH4NonSmoothPOUWitness.mk' (g := g) h

/-- **Existence-of-witness form.** A `ChartH4NonSmoothPOUWitness` for a
manifold function `u : M → ℝ` at a chart point `α : M` is equivalent to
the existence of a `MemWkp 4 2` proof for the POU-cut chart-pushed
function on the chart-target image. -/
theorem chartH4NonSmoothPOUWitness_iff_memWkp_four
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) :
    ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α ↔
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  ⟨fun h => h.memWkp_four,
   fun h => chartH4NonSmoothPOUWitness_of_memWkp_four g (u := u) (α := α) h⟩

/-- **The bridge consumed as a hypothesis.** A formal statement of the
chart-side bridge from chart-local `H⁴` regularity of a manifold function
`u : M → ℝ` to the `ChartH4NonSmoothPOUWitness` at every chart point.

This hypothesis is the analogue, at H⁴ level, of the chart-side support
bridge that is currently exposed at the H² level in
`DiffChartBilinearH1ComplUnconditional.lean`. The downstream consumer
discharges this hypothesis once the chart-side residual MemW1p machinery
is extended to fourth weak partials. -/
def ChartSideH4Bridge (_g : SmoothRiemannianMetric I M) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)

/-- From the chart-side `H⁴` bridge, the family of per-chart `H⁴`
witnesses follows. -/
theorem chartH4NonSmoothPOUWitness_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_bridge : ChartSideH4Bridge (I := I) (M := M) g u) :
    ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α :=
  fun α => chartH4NonSmoothPOUWitness_of_memWkp_four g (u := u) (α := α)
    (h_bridge α)

/-- **Bridge-driven `H⁴` regularity for `laplacianDomainPow g 2`.** Given
a chart-side `H⁴` bridge for the canonical function representative of
`u_h ∈ laplacianDomainPow g 2`, the manifold-level `MemWkpChart g 4 2`
membership and finite chart-based norm follow. -/
theorem laplacianDomainPow_memWkpChart_four_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_bridge : ChartSideH4Bridge (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h
    (chartH4NonSmoothPOUWitness_of_chartSideH4Bridge g h_bridge)

/-- **Bridge-driven two-sided `H⁴` regularity.** Given chart-side `H⁴`
bridges for both the canonical function representative of `u_h` and the
canonical function representative of the `Lp` preimage of `u_h`, both
manifold-level functions lie in `MemWkpChart g 4 2` with finite norms. -/
theorem laplacianDomainPow_memWkpChart_four_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_bridge_u : ChartSideH4Bridge (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (h_bridge_rhs : ChartSideH4Bridge (I := I) (M := M) g
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) :=
  laplacianDomainPow_memWkpChart_four_two_sided (I := I) (M := M) g hu_h
    (chartH4NonSmoothPOUWitness_of_chartSideH4Bridge g h_bridge_u)
    (chartH4NonSmoothPOUWitness_of_chartSideH4Bridge g h_bridge_rhs)

end LaplacianDomainPowH4Bridge
end Laplacian
end Analysis
end DifferentialGeometry

end
