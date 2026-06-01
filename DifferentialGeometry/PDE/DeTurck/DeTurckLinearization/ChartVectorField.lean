import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciSymbol
import DifferentialGeometry.Geometry.HessianTrace

/-!
# Chart-coordinate components of the DeTurck vector field

For two smooth Riemannian metrics `g` (the evolving metric) and `g'` (the fixed
background metric) on a smooth manifold `M`, the **DeTurck vector field** of the
pair has, in the chart at a base point `α : M`, the coordinate components
$$W^k(y) = \sum_{a, b} G(g)^{ab}(y)\,
    \bigl(\Gamma^k{}_{ab}(g)(y) - \Gamma^k{}_{ab}(g')(y)\bigr),$$
where `G(g)^{ab}` is the inverse chart Gram matrix of `g` and `Γ^k{}_{ab}(g)` is
the chart Christoffel symbol of `g`.  It is the metric-`g` trace of the
difference of the Christoffel symbols of `g` and the background `g'` — the
standard textbook chart formula for the DeTurck correction term.

This file **defines** the component function `W^k` by this explicit formula and
records its basic chart-coordinate properties: an unfolding lemma, the vanishing
`W^k(g, g) = 0` when the background equals the evolving metric, and the
`C^∞`-smoothness on the chart-target interior.  Everything here is pure
chart-coordinate algebra; no linearization is performed.

This is a chart-coordinate development: like the chart symbol objects built
directly from `chartChristoffel` / `chartRicciTensor`, the component function
`chartDeTurckVFComp` is an independent chart object assembled from
`chartChristoffel` and `chartInvGramOnE`, not transported from a bundled
tangent-bundle section.

## Index convention

`chartChristoffel g α a b k y` is the chart Christoffel symbol
`Γ^k{}_{ab}(g)(y)` of the second kind: the **lower pair `a b` comes first**, the
**upper index `k` second**, and the chart-coordinate point `y ∈ E` last.  The
component `chartDeTurckVFComp g g' α k y` accordingly carries the upper index `k`
and the chart point `y`, summing `chartChristoffel … a b k` over the lower pair
`(a, b)` against the inverse Gram `chartInvGramOnE g α a b`.

## Main definitions

* `chartDeTurckVFComp g g' α k` — the `k`-th chart component `W^k` of the
  DeTurck vector field of `g` against `g'`, as a function `E → ℝ` on the chart
  target.

## Main results

* `chartDeTurckVFComp_def` — the defining sum formula, as a `simp`-unfolding
  lemma.
* `chartDeTurckVFComp_self` — `chartDeTurckVFComp g g α k y = 0`: the component
  vanishes when the background metric equals the evolving metric.
* `chartDeTurckVFComp_contDiffOn_interior` — `chartDeTurckVFComp g g' α k` is
  `C^∞` on `interior (extChartAt I α).target`.
* `chartDeTurckVFComp_differentiableOn_interior` /
  `chartDeTurckVFComp_differentiableAt_interior` — the differentiability
  corollaries on the chart-target interior, in the forms a later linearization
  step consumes when applying `partialDeriv` to `W^k`.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The `k`-th chart-coordinate component of the DeTurck vector field of the
evolving metric `g` against the background metric `g'`, evaluated at the
chart-coordinate point `y ∈ E`:
$$W^k(y) = \sum_{a, b} G(g)^{ab}(y)\,
    \bigl(\Gamma^k{}_{ab}(g)(y) - \Gamma^k{}_{ab}(g')(y)\bigr).$$
Here `G(g)^{ab} = chartInvGramOnE g α a b` is the inverse chart Gram matrix of
`g`, and `Γ^k{}_{ab}(g) = chartChristoffel g α a b k` is the chart Christoffel
symbol of `g` (lower pair `a b`, upper index `k`).  This is the metric-`g` trace
of the difference of the chart Christoffel symbols of `g` and the background
`g'`. -/
def chartDeTurckVFComp (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α a b y *
      (chartChristoffel (I := I) g α a b k y -
        chartChristoffel (I := I) g' α a b k y)

@[simp] lemma chartDeTurckVFComp_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g g' α k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          (chartChristoffel (I := I) g α a b k y -
            chartChristoffel (I := I) g' α a b k y) := rfl

/-- **The DeTurck vector field of a metric against itself has zero chart
components.**  Each summand of `chartDeTurckVFComp g g α k y` contains the factor
`chartChristoffel g α a b k y - chartChristoffel g α a b k y = 0`. -/
@[simp] theorem chartDeTurckVFComp_self
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckVFComp (I := I) g g α k y = 0 := by
  classical
  rw [chartDeTurckVFComp_def]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          (chartChristoffel (I := I) g α a b k y -
            chartChristoffel (I := I) g α a b k y)
        = ∑ a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E),
            (0 : ℝ) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [sub_self, mul_zero]
    _ = 0 := by simp

/-- **Smoothness of the chart DeTurck-vector-field component.**  The function
`chartDeTurckVFComp g g' α k` is `C^∞` on the interior of the chart target
`(extChartAt I α).target ⊆ E`. -/
theorem chartDeTurckVFComp_contDiffOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : chartDeTurckVFComp (I := I) g g' α k =
      fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            (chartChristoffel (I := I) g α a b k y -
              chartChristoffel (I := I) g' α a b k y) := by
    funext y
    rw [chartDeTurckVFComp_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  · have hg : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g α a b k
    have hg' : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g' α a b k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g' α a b k
    exact hg.sub hg'

/-- **The chart DeTurck-vector-field component is differentiable on the
chart-target interior.**  An immediate corollary of
`chartDeTurckVFComp_contDiffOn_interior`. -/
theorem chartDeTurckVFComp_differentiableOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentiableOn ℝ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) :=
  (chartDeTurckVFComp_contDiffOn_interior (I := I) g g' α k).differentiableOn
    (by simp)

/-- **The chart DeTurck-vector-field component is differentiable at each
interior point of the chart target.**  This is the form the
`partialDeriv`-based linearization step consumes. -/
theorem chartDeTurckVFComp_differentiableAt_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartDeTurckVFComp (I := I) g g' α k) y := by
  have hcd : ContDiffOn ℝ ∞ (chartDeTurckVFComp (I := I) g g' α k)
      (interior (extChartAt I α).target) :=
    chartDeTurckVFComp_contDiffOn_interior (I := I) g g' α k
  exact (hcd.differentiableOn (by simp)).differentiableAt
    (isOpen_interior.mem_nhds hy)

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
