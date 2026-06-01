import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ChartVectorField
import DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChristoffelLinearization

/-!
# The principal part of the linearized DeTurck vector field

In the chart at a base point `α : M`, the DeTurck vector field of an evolving
metric `g` against a fixed background metric `g'` has coordinate components
$$W^k(g)(y) = \sum_{a, b} G(g)^{ab}(y)\,
    \bigl(\Gamma^k{}_{ab}(g)(y) - \Gamma^k{}_{ab}(g')(y)\bigr),$$
the metric-`g` trace of the difference of the chart Christoffel symbols of `g`
and `g'` (this is `chartDeTurckVFComp`).

Linearizing `g ↦ W^k(g)` in a metric-perturbation direction `h`, the
perturbation enters through the inverse Gram factor `G(g)^{ab}` and through the
Christoffel symbol `Γ^k{}_{ab}(g)`; the background `Γ^k{}_{ab}(g')` is
`g`-independent and so differentiates to zero.  The derivative splits into:

* the **principal part**, which carries a *derivative* of `h` — it comes
  entirely from linearizing `Γ(g)` and is
  $$(DW)^k_{\mathrm{principal}}[h](y) = \sum_{a, b} G(g)^{ab}(y)\,
      (D\Gamma)^k{}_{ab}[h](y),$$
  where `(DΓ)^k{}_{ab}[h]` is the principal part of the linearized Christoffel
  symbol (`chartLinearizedChristoffelPrincipal`);
* the complementary term `D(G^{ab})[h] · (Γ - Γ̄)`, which carries `h`
  undifferentiated — it is of lower order and is not built here.

This file **defines** the principal part `(DW)^k_{\mathrm{principal}}[h]` by the
explicit metric-`g` trace formula above and records its basic chart-coordinate
properties: an unfolding lemma, the visible independence from the background
metric `g'`, the `ℝ`-linearity in the perturbation direction `h`, and the
`C^∞`-smoothness on the chart-target interior.

The background metric `g'` is kept as a parameter purely for signature
uniformity with `chartDeTurckVFComp` and the downstream linearization API: the
*value* of the principal part does not depend on `g'`, because the background
Christoffel term drops out of the linearization (see
`chartLinearizedDeTurckVFPrincipal_def` and
`chartLinearizedDeTurckVFPrincipal_background_indep`).

## Index convention

`chartLinearizedChristoffelPrincipal g α h a b k y` is the principal linearized
Christoffel symbol with the **lower pair `a b` first**, the **upper index `k`
second**, and the chart-coordinate point `y ∈ E` last.  The principal part
`chartLinearizedDeTurckVFPrincipal g g' α h k y` accordingly carries the upper
index `k` and the chart point `y`, summing
`chartLinearizedChristoffelPrincipal … a b k` over the lower pair `(a, b)`
against the inverse Gram `chartInvGramOnE g α a b`.  This matches the
index layout of `chartDeTurckVFComp`.

## Main definitions

* `chartLinearizedDeTurckVFPrincipal g g' α h k` — the `k`-th chart component of
  the principal part of the linearized DeTurck vector field of `g` against `g'`
  in the perturbation direction `h`, as a function `E → ℝ` on the chart target.

## Main results

* `chartLinearizedDeTurckVFPrincipal_def` — the defining sum formula, as a
  `simp`-unfolding lemma.
* `chartLinearizedDeTurckVFPrincipal_background_indep` — the value is
  independent of the background metric `g'`.
* `chartLinearizedDeTurckVFPrincipal_add` / `_smul` / `_zero` — `ℝ`-linearity in
  the perturbation direction `h`.
* `chartLinearizedDeTurckVFPrincipal_contDiffOn_interior` — the principal part
  is `C^∞` on `interior (extChartAt I α).target`.
* `chartLinearizedDeTurckVFPrincipal_differentiableOn_interior` /
  `chartLinearizedDeTurckVFPrincipal_differentiableAt_interior` — the
  differentiability corollaries on the chart-target interior, the forms a later
  symbol step consumes when applying `partialDeriv` to the principal part.
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

set_option linter.unusedVariables false in
/-- The `k`-th chart-coordinate component of the **principal part of the
linearized DeTurck vector field** of the evolving metric `g` against the
background metric `g'`, in the perturbation direction `h`, evaluated at the
chart-coordinate point `y ∈ E`:
$$(DW)^k_{\mathrm{principal}}[h](y) = \sum_{a, b} G(g)^{ab}(y)\,
    (D\Gamma)^k{}_{ab}[h](y).$$
Here `G(g)^{ab} = chartInvGramOnE g α a b` is the inverse chart Gram matrix of
`g`, and `(DΓ)^k{}_{ab}[h] = chartLinearizedChristoffelPrincipal g α h a b k` is
the principal part of the linearized chart Christoffel symbol of `g` (lower pair
`a b`, upper index `k`).

This is the term of the linearization `D(g ↦ W^k(g))[h]` that carries a
*derivative* of the perturbation `h`: it arises entirely from linearizing the
Christoffel symbol `Γ^k{}_{ab}(g)`.  The background metric `g'` is a parameter
only for signature uniformity with `chartDeTurckVFComp` — the value does not
depend on it, since the background Christoffel term `Γ^k{}_{ab}(g')` is
`g`-independent and so contributes nothing to the linearization.  The
complementary term `D(G^{ab})[h] · (Γ - Γ̄)` carries `h` undifferentiated and is
of lower order; it is not part of this principal-part definition.

The background-metric parameter `g'` is deliberately retained for signature
uniformity with `chartDeTurckVFComp`; it does not appear in the body, so the
unused-variable linter is locally disabled on this declaration only. -/
def chartLinearizedDeTurckVFPrincipal (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α a b y *
      chartLinearizedChristoffelPrincipal (I := I) g α h a b k y

@[simp] lemma chartLinearizedDeTurckVFPrincipal_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := rfl

/-- **The principal part of the linearized DeTurck vector field is independent
of the background metric.**  Replacing the background metric `g'` by any other
metric `g''` leaves the principal part unchanged: the defining sum does not
mention the background metric at all. -/
theorem chartLinearizedDeTurckVFPrincipal_background_indep
    (g g' g'' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y =
      chartLinearizedDeTurckVFPrincipal (I := I) g g'' α h k y := rfl

/-- The principal part of the linearized DeTurck vector field vanishes on the
zero perturbation: every principal linearized Christoffel summand is zero. -/
@[simp] theorem chartLinearizedDeTurckVFPrincipal_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α
      (0 : ChartMetricPerturbation E) k y = 0 := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def]
  calc
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          chartLinearizedChristoffelPrincipal (I := I) g α
            (0 : ChartMetricPerturbation E) a b k y
        = ∑ _a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E),
            (0 : ℝ) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [chartLinearizedChristoffelPrincipal_zero, mul_zero]
    _ = 0 := by simp

/-- **Additivity** of the principal part of the linearized DeTurck vector field
in the perturbation direction: `(DW)_principal[h₁ + h₂] = (DW)_principal[h₁] +
(DW)_principal[h₂]`. -/
theorem chartLinearizedDeTurckVFPrincipal_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y =
      chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y +
        chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def, chartLinearizedDeTurckVFPrincipal_def,
    chartLinearizedDeTurckVFPrincipal_def]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_add]
  ring

/-- **Scalar homogeneity** of the principal part of the linearized DeTurck
vector field in the perturbation direction: `(DW)_principal[c • h] =
c • (DW)_principal[h]`. -/
theorem chartLinearizedDeTurckVFPrincipal_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y =
      c • chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y := by
  classical
  rw [chartLinearizedDeTurckVFPrincipal_def, chartLinearizedDeTurckVFPrincipal_def,
    smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_smul, smul_eq_mul]
  ring

/-- **Smoothness of the principal part of the linearized DeTurck vector field.**
As a function of the chart-coordinate point `y`, `(DW)^k_{\mathrm{principal}}[h]`
is `C^∞` on the interior of the chart target `(extChartAt I α).target ⊆ E`. -/
theorem chartLinearizedDeTurckVFPrincipal_contDiffOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k =
      fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := by
    funext y
    rw [chartLinearizedDeTurckVFPrincipal_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  · exact (chartLinearizedChristoffelPrincipal_contDiffOn (I := I) g α h a b k).mono
      interior_subset

/-- **The principal part of the linearized DeTurck vector field is
differentiable on the chart-target interior.**  An immediate corollary of
`chartLinearizedDeTurckVFPrincipal_contDiffOn_interior`. -/
theorem chartLinearizedDeTurckVFPrincipal_differentiableOn_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) :
    DifferentiableOn ℝ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k)
      (interior (extChartAt I α).target) :=
  (chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g g' α h k).differentiableOn
    (by simp)

/-- **The principal part of the linearized DeTurck vector field is
differentiable at each interior point of the chart target.**  This is the form
the `partialDeriv`-based symbol step consumes. -/
theorem chartLinearizedDeTurckVFPrincipal_differentiableAt_interior
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k) y := by
  have hcd : ContDiffOn ℝ ∞ (chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k)
      (interior (extChartAt I α).target) :=
    chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g g' α h k
  exact (hcd.differentiableOn (by simp)).differentiableAt
    (isOpen_interior.mem_nhds hy)

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
