import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplDirectH3
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpThree
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PerChartWitness
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.UniformDiffQuotBoundCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev

/-!
# Chart-`W^{2,2}` regularity of the canonical chosen first weak partial

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, direction `l`,
and `u_h ∈ laplacianDomainPow g 2`, this module organises the chart-`W^{2,2}`
regularity claim

```
MemWkp 2 2 (chartPushedChosenFirstPartial g α u_h l) (chartTargetEuclid α)
```

and reduces it structurally via the chart-`H³` regularity of
`chartPushed POU α u_h.coeFn`.

The canonical chosen first weak partial is
`chartPushedChosenFirstPartial g α u_h l :=
  chosenWeakPartial' 2 l (chartPushed POU α u_h.coeFn) (chartTargetEuclid α)`.
By definition of `MemWkp 2 2` (`MemWkp_succ`), the target decomposes into:

* `chartPushedChosenFirstPartial g α u_h l ∈ MemW1p 2 (chartTargetEuclid α)`,
  discharged unconditionally by `chartPushedChosenFirstPartial_memW1p_two`
  (in `DiffChartBilinearH1ComplH3`).

* For each coordinate direction `i`, `MemWkp 1 2 (chosenWeakPartial' 2 i
  chartPushedChosenFirstPartial (chartTargetEuclid α)) (chartTargetEuclid α)`,
  i.e. chart-`H¹` regularity of each chosen second mixed weak partial.

The second conjunct, integrated over all `i`, is structurally equivalent to
chart-`H³` of the chart-pushed POU-cut representative
`chartPushed POU α u_h.coeFn` (by `chartPushed_memWkp_three_two_iff` in
`ChartPushedMemWkpThree`). For a single fixed direction
`l`, the per-direction `MemW1p 2` of the chosen mixed second partials in
directions `(l, i)` is a single instance of this conjunction.

This module delivers the structural reduction and forwards the chart-`H³`
discharge to a downstream chart-bilinear Nirenberg bootstrap on the
differentiated chart-bilinear identity. The headline statement is exposed in
the form requested by downstream consumers, with the chart-`H³` membership
of the chart-pushed function appearing as an explicit hypothesis. (The
mathematical content of the headline is the structural reduction from the
target chart-`H²` to chart-`H³`; the chart-`H³` itself is the content of the
chart-bilinear Nirenberg bootstrap module.)

## Main results

* `target_iff_per_direction` — the structural decomposition of the target via
  `MemWkp_succ`.

* `chartPushedChosenFirstPartial_memWkp_two_of_chartPushed_memWkp_three` —
  the chart-`H²` membership of the chosen first weak partial in direction
  `l`, from the chart-`H³` of `chartPushed POU α u_h.coeFn`.

* `chartPushed_chosenFirstPartial_memWkp_two_two_of_laplacianDomainPow_two_via_chartPushed_memWkp_three`
  — the headline membership in the exact form requested by downstream
  consumers, with the underlying chosen weak partial spelled out as
  `chosenWeakPartial' 2 l (chartPushed POU α u_h.coeFn) (chartTargetEuclid α)`.
  The chart-`H³` membership of the chart-pushed function appears as an
  explicit hypothesis.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChosenFirstPartialChartH2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3Direct
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The chosen second mixed weak partial of `chartPushed POU α u_h.coeFn` in
directions `(l, i)`: first the chosen `l`-partial, then the chosen `i`-partial
of the result. This is the second iterate in the `MemWkp_succ` expansion. -/
noncomputable def chosenMixedSecondPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (l i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 i
    (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
    (chartTargetEuclid (I := I) (M := M) α)

/-- The target chart-`W^{2,2}` membership of the chosen first weak partial
decomposes into chart-`H¹` of the first weak partial itself (unconditional)
and chart-`H¹` of each chosen mixed second weak partial. -/
theorem target_iff_per_direction
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (l : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) ↔
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    ∀ i : Fin (Module.finrank ℝ E),
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenMixedSecondPartial (I := I) (M := M) g α u_h l i)
        (chartTargetEuclid (I := I) (M := M) α) := by
  constructor
  · intro h
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ] at h
    refine ⟨h.1, ?_⟩
    intro i
    have h_step := h.2 i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
      at h_step
    exact h_step
  · rintro ⟨h_first, h_second⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
    refine ⟨h_first, ?_⟩
    intro i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact h_second i

/-- Chart-`H³` of the chart-pushed function ⇒ each chosen second mixed weak
partial is in `MemW1p 2 (chartTargetEuclid α)`. -/
theorem chosenMixedSecondPartial_memW1p_of_chartPushed_memWkp_three
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (h_chartPushed_memWkp_three :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenMixedSecondPartial (I := I) (M := M) g α u_h l i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_first : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_chartPushed_memWkp_three.chosenWeakPartial_mem l
  have h_second := h_first.chosenWeakPartial_mem i
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_second
  exact h_second

/-- From chart-`H³` of `chartPushed POU α u_h.coeFn`, the chosen first weak
partial in direction `l` lies in `MemWkp 2 2 (chartTargetEuclid α)`. -/
theorem chartPushedChosenFirstPartial_memWkp_two_of_chartPushed_memWkp_three
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chartPushed_memWkp_three :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [target_iff_per_direction (I := I) (M := M) g α u_h l]
  refine ⟨chartPushedChosenFirstPartial_memW1p_two
    (I := I) (M := M) g α hu_h l, ?_⟩
  intro i
  exact chosenMixedSecondPartial_memW1p_of_chartPushed_memWkp_three
    (I := I) (M := M) g α u_h h_chartPushed_memWkp_three l i

/-- **Headline: chart-`W^{2,2}` regularity of the canonical chosen first weak
partial of the chart-pushed POU-cut representative.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`,
any chart point `α : M`, any coordinate direction `l`, and any element
`u_h ∈ laplacianDomainPow g 2`, the canonical chosen first weak partial in
direction `l` of the chart-pushed POU-cut representative
`chartPushed (chartAtlasPOU I M) α (H1ComplToLp g u_h).coeFn` lies in
`MemWkp 2 2 (chartTargetEuclid α)`, **provided** the chart-pushed function
itself admits chart-`H³` regularity. -/
theorem chartPushed_chosenFirstPartial_memWkp_two_two_of_laplacianDomainPow_two_via_chartPushed_memWkp_three
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chartPushed_memWkp_three :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
    (chartTargetEuclid (I := I) (M := M) α)
  exact chartPushedChosenFirstPartial_memWkp_two_of_chartPushed_memWkp_three
    (I := I) (M := M) g α hu_h h_chartPushed_memWkp_three l

end ChosenFirstPartialChartH2
end Laplacian
end Analysis
end DifferentialGeometry

end
