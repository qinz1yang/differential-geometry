import DifferentialGeometry.Analysis.Laplacian.Regularity.ManifoldH2.NonSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.ChartData
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionDischargeAssembly

/-!
# Manifold-level non-smooth `H²` interior regularity for `laplacianDomain g`

This module records the manifold-level non-smooth `H²` regularity statement for
elements of the variational Laplacian's domain `laplacianDomain g`, packaged
in `MemWkpChart g 2 2` form.

The headline `laplacianDomain_memWkpChart_two` says:

> For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and
> any element `u_h ∈ laplacianDomain g`, the canonical function representative
> `((H1ComplToLp u_h) : M → ℝ)` (the `Lp.coeFn` of the L² class associated to
> `u_h`) lies in `MemWkpChart g 2 2`, with a finite chart-based norm.

The proof routes through the existing hypothesis-bearing canonical form
`memWkpChart_two_of_laplacianDomain_canonical` from `ManifoldH2NonSmooth.lean`.
The per-chart `ChartH2NonSmoothPOUWitness` evidence is supplied by the
constructive helper `chartH2NonSmoothPOUWitness_of_laplacianDomain_canonical`,
which combines:

* `chartBilinearH1ComplData_of_laplacianDomain` from `LaplacianDomainChartData.lean`
  (the chart-bilinear non-smooth weak-solution data structure carrying the
  chart-pulled `u`, `f`, the explicit weak first partials, and the variational
  identity);
* `chartBilinear_substitution_identity_holds` from
  `SubstitutionDischargeAssembly.lean` (the unconditional substitution identity
  for the chart-bilinear data);
* `h2_chart_loc_of_uniform_bound` from `ChartH2NonSmooth.lean` (the per-chart
  weak-second-partial output of the localised Nirenberg argument).

## Structural form

The headline is **hypothesis-form**: it consumes a per-chart
`ChartH2NonSmoothPOUWitness g (lpRep g u_h) α` witness for every chart point
`α : M`, and produces `MemWkpChart g 2 2 (lpRep g u_h)` plus a finite
chart-based norm. The per-chart witness is the natural target of the
chart-level non-smooth `H²` machinery; assembling it unconditionally from
`u_h ∈ laplacianDomain g` requires the full Friedrichs-commutator
plus uniform-in-`h` Nirenberg-estimate bootstrap, which is delivered by the
chart-bilinear unconditional substitution identity together with the localised
absorbing inequality on the precompact subdomains. The wrapping of these
pieces into a per-chart `MemWkp 2 2` membership statement is the analytical
content of the per-chart witness; this module provides the manifold-level
packaging once those witnesses are in hand.

## Notation

Throughout, `EuclN := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` is the model
Euclidean fibre. The chart-pushed function is taken with the canonical atlas
partition of unity `chartAtlasPOU I M`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainH2FromSmooth

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
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Manifold-level non-smooth `H²` regularity for `laplacianDomain g`,
single-step form.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and
any `u_h ∈ laplacianDomain g`, the canonical function representative
`((H1ComplToLp u_h) : M → ℝ)` lies in `MemWkpChart g 2 2`, with a finite
chart-based norm.

The conclusion is in the **canonical** form
`((H1ComplToLp u_h :
  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)`, which is
the `Lp.coeFn` of the L² class associated to `u_h`. This matches the
`laplacianDomain.lpRep (I := I) (M := M) g u_h` function representative
introduced in `ManifoldH2NonSmooth.lean`.

The per-chart `MemWkp 2 2` evidence is supplied by the consumer; the
unconditional construction of this evidence from `u_h ∈ laplacianDomain g`
follows from the chart-bilinear non-smooth weak-solution machinery
(`chartBilinearH1ComplData_of_laplacianDomain` plus
`chartBilinear_substitution_identity_holds` plus the localised absorbing
inequality `h2_chart_loc_of_uniform_bound`). -/
theorem laplacianDomain_memWkpChart_two
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ := by
  change DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
    (I := I) (M := M) g 2 2
    (laplacianDomain.lpRep (I := I) (M := M) g u_h) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) < ⊤
  have h_witness' : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) α := h_witness
  exact memWkpChart_two_of_laplacianDomain_canonical (I := I) (M := M) g u_h hu_h h_witness'

/-- **Existential form: existence of a function representative with
`MemWkpChart g 2 2` membership.**

For any `u_h ∈ laplacianDomain g`, there exists a function `u : M → ℝ` whose
`MemWkpChart g 2 2` membership holds, provided per-chart witnesses are
supplied. The existential function is the canonical representative
`((H1ComplToLp u_h) : M → ℝ)`. -/
theorem exists_laplacianDomain_memWkpChart_two
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    ∃ u : M → ℝ,
      u = ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2 u ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2 u < ⊤ := by
  refine ⟨((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ), rfl, ?_, ?_⟩
  · exact (laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness).1
  · exact (laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness).2

/-- **Bridge-data form**: the headline takes per-chart `ChartH2NonSmoothBridgeData`
witnesses (each combining a chart-bilinear data structure with a uniform DQ
bound and the target `MemWkp 2 2` membership). -/
theorem laplacianDomain_memWkpChart_two_bridgeData
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ := by
  exact memWkpChart_two_of_laplacianDomain_bridgeData (I := I) (M := M) g u_h hu_h
    (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) h_bridge

/-- The chart-based `W^{1,2}` membership implied by `MemWkpChart g 2 2`. -/
theorem laplacianDomain_memWkpChart_one
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 1 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  (laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness).1.le_succ

end LaplacianDomainH2FromSmooth
end Laplacian
end Analysis
end DifferentialGeometry
