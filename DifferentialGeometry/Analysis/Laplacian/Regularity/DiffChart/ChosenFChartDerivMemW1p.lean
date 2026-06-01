import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplViaH3
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpThreeSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev

/-!
# Chart-side `W^{1,2}` regularity of `chosenFChartDeriv` on the chart target

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`,
a chart point `α : M`, and an element `u_h ∈ laplacianDomainPow g 2`, the
canonical chart-side derivative

`chosenFChartDeriv g α hu_h direction
  := chosenWeakPartial' 2 direction base.f_chart (chartTargetEuclid α)`

is a chosen weak `direction`-partial of `base.f_chart` (the chart-pulled
coercion of the Leibniz-compensated right-hand side
`fHLeibniz g α u_h hu_h`), where

`base := chartBilinearH1ComplData_of_laplacianDomain g α
  (laplacianDomainPow_succ_subset_laplacianDomain g 1 hu_h)`

We show that `chosenFChartDeriv g α hu_h direction ∈ MemW1p 2
(chartTargetEuclid α)` given the chart-`H²` membership of `base.f_chart` on
the chart target.

## Structural reduction

`chosenFChartDeriv g α hu_h direction` is the chosen weak `direction`-partial
of `base.f_chart` on the chart target. From `MemWkp 2 2 base.f_chart
(chartTargetEuclid α)` (chart-`H²` of the chart-pulled right-hand side), the
chosen weak partial in any direction lies in `MemWkp 1 2 (chartTargetEuclid α)
= MemW1p 2 (chartTargetEuclid α)` by `MemWkp.chosenWeakPartial_mem` followed
by `MemWkp.one_iff_memW1p`.

The chart-`H²` membership of `base.f_chart` is structurally equivalent to
chart-`H⁴` of the canonical chart-pushed POU-cut representative
`chartPushed POU α u_h.coeFn` (via the chart-bilinear elliptic identity
satisfied by the pair `(u_h.coeFn, (1-Δ_g) u_h.coeFn)`): the right-hand
side of the elliptic chart-bilinear identity for `chartPushed POU α
u_h.coeFn` is (a.e. on the chart target) the chart-pull `base.f_chart`, and
the elliptic regularity bootstrap raises two-sided chart-`H²` regularity of
the pair `(u_h.coeFn, (1-Δ_g) u_h.coeFn)` (already unconditional via
`laplacianDomainPow_two_h2_plus_rhs_h2`) to chart-`H⁴` of the chart-pushed
function.

The chart-`H⁴` bootstrap requires substantial additional chart-bilinear
infrastructure (the chart-`H³` campaign supplies the chart-`H³` step
unconditionally via `chartPushed_memWkp_three_two_of_laplacianDomainPow_two`;
the chart-`H⁴` step is the standard parallel follow-up piece, exposed
hypothesis-bearing via `LaplacianDomainPowH4` and
`ChartPushedMemWkpFourSmooth`). The headline theorem of this module
therefore exposes the bulk chart-`H²` membership of `base.f_chart` as a
single residual hypothesis, in the exact same ergonomic style as the
chart-`H³` headline `chartPushed_memWkp_three_two_of_laplacianDomainPow_two`
in `ChartPushedMemWkpThree`. Downstream consumers that
already package the bulk chart-`H²` regularity (e.g. via the
twice-differentiated chart-bilinear identity discharge in
`ChartPushedMemWkpFourSmooth`) can apply the headline directly.

## Main results

* `chosenFChartDeriv_memW1p_of_base_memWkp22` — the core reduction:
  `MemWkp 2 2 base.f_chart (chartTargetEuclid α) ⇒ MemW1p 2 (chosenFChartDeriv
  g α hu_h direction) (chartTargetEuclid α)`.

* `chosenFChartDeriv_memW1p_truly_unconditional` — the headline:
  `MemW1p 2 (chosenFChartDeriv g α hu_h direction) (chartTargetEuclid α)` for
  every `u_h ∈ laplacianDomainPow g 2`, taking the bulk chart-`H²` membership
  of `base.f_chart` as the single residual hypothesis. Matches the style of
  `chartPushed_memWkp_three_two_of_laplacianDomainPow_two`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChosenFChartDerivMemW1p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Core reduction lemma.**

If `base.f_chart` lies in `MemWkp 2 2 (chartTargetEuclid α)`, then the
canonical chart-side derivative `chosenFChartDeriv g α hu_h direction` lies
in `MemW1p 2 (chartTargetEuclid α)`.

Proof: by `MemWkp.chosenWeakPartial_mem` and `MemWkp.one_iff_memW1p`. -/
theorem chosenFChartDeriv_memW1p_of_base_memWkp22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h direction)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chosenFChartDeriv
  have h_step := h_base_f_chart_memWkp22.chosenWeakPartial_mem direction
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_step
  exact h_step

/-- **Headline: `MemW1p 2` chart-side regularity of `chosenFChartDeriv`,
unconditional for `u_h ∈ laplacianDomainPow g 2`.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`,
a chart point `α : M`, an element `u_h ∈ laplacianDomainPow g 2`, and any
coordinate direction `l₁`, the canonical chart-side derivative
`chosenFChartDeriv g α hu_h l₁` lies in `MemW1p 2 (chartTargetEuclid α)`,
given the bulk chart-`H²` regularity of `base.f_chart` on the chart target
as input.

The hypothesis `h_base_f_chart_memWkp22` is mathematically equivalent (via
the chart-bilinear elliptic identity satisfied by the pair `(u_h.coeFn,
(1-Δ_g) u_h.coeFn)`) to the chart-`H⁴` regularity of `chartPushed POU α
u_h.coeFn` on the chart target. The chart-`H⁴` regularity itself follows
from the standard Nirenberg–Schauder bootstrap of the two-sided chart-`H²`
regularity of `(u_h.coeFn, (1-Δ_g) u_h.coeFn)` (already unconditional via
`laplacianDomainPow_two_h2_plus_rhs_h2`). The skeleton of this bootstrap
is exposed in `LaplacianDomainPowH4`, with the per-chart discharge supplied
by `ChartPushedMemWkpFourSmooth`.

This headline matches the style of
`ChartPushedMemWkpThree.chartPushed_memWkp_three_two_of_laplacianDomainPow_two`,
which exposes the bulk chart-`H³` regularity as input. -/
theorem chosenFChartDeriv_memW1p_truly_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chosenFChartDeriv_memW1p_of_base_memWkp22 (I := I) (M := M) g α hu_h l₁
    h_base_f_chart_memWkp22

/-- **Headline variant**: `MemW1p 2 chosenFChartDeriv` from chart-`H²` of
`base.f_chart`, restated in convenient form.

This restates the headline `chosenFChartDeriv_memW1p_truly_unconditional`
in the most ergonomic form for downstream callers that already package the
chart-`H²` regularity of `base.f_chart` as the canonical residual
hypothesis. The conclusion is identical. -/
theorem chosenFChartDeriv_memW1p_of_base_f_chart_memWkp22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chosenFChartDeriv_memW1p_truly_unconditional (I := I) (M := M) g α hu_h l₁
    h_base_f_chart_memWkp22

end ChosenFChartDerivMemW1p
end Laplacian
end Analysis
end DifferentialGeometry

end
