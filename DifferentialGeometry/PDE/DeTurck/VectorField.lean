import DifferentialGeometry.PDE.DeTurck.VectorFieldSmooth

/-!
# The DeTurck vector field as a smooth tangent-bundle section

Given two smooth Riemannian metrics `g` and `g'` on a smooth manifold `M`, the
preceding files build the **DeTurck vector field** of the pair:

* `ConnectionDifference.lean` constructs the connection-difference `(1,2)`-tensor
  `connDiff g g' = ∇^{LC}(g) − ∇^{LC}(g')`;
* `MetricTrace.lean` defines `deTurckFun g g'` as the metric `g`-trace of that
  tensor — the chart-independent vector field with coordinate components
  `W^i = g^{jk}(Γ^i_{jk}(g) − Γ̄^i_{jk}(g'))`;
* `VectorFieldSmooth.lean` proves `deTurckFun g g'` is `C^∞` as a section of the
  tangent bundle.

This file is the public-facing packaging of that construction.  It bundles the
DeTurck vector field as a `ContMDiffSection` of the tangent bundle — the object
`deTurckVF g g'` — and records its characterizing properties: the evaluation
formula, vanishing for a metric against itself, and the explicit chart-trace
formula transported to the bundled section.

## Main definitions

* `deTurckVF g g'` — the DeTurck vector field of `g` against `g'`, as a bundled
  smooth section `Cₛ^∞⟮I; E, TangentSpace I⟯` of the tangent bundle.

## Main results

* `deTurckVF_apply` — the evaluation formula: `(deTurckVF g g') x = deTurckFun g g' x`.
* `deTurckVF_self` — the DeTurck vector field of a metric against itself is the
  zero section.
* `deTurckVF_apply_eq` — the explicit chart-trace formula
  `(deTurckVF g g') x = ∑_{j,k} G^{jk}(x) • connDiff g g' x (e_j x) (e_k x)`
  stated directly on the bundled section.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The **DeTurck vector field** of two smooth Riemannian metrics `g` and `g'`,
packaged as a bundled smooth section of the tangent bundle.

For an evolving metric `g` and a background metric `g'`, this is the vector
field whose components in any chart coordinate frame `{e_j}` are
$$
  W^i \;=\; g^{jk}\bigl(\Gamma^i_{jk}(g) - \bar\Gamma^i_{jk}(g')\bigr),
$$
i.e. the metric `g`-trace of the connection difference
`∇^{LC}(g) − ∇^{LC}(g')`.  It is the vector field used to convert the
Ricci-flow equation into a strictly parabolic system — the DeTurck vector field.

Concretely it wraps the plain function `deTurckFun g g'` (the metric trace,
constructed in `MetricTrace.lean`) together with its global smoothness
`deTurckFun_contMDiff_total` (proved in `VectorFieldSmooth.lean`), exhibiting it
as an element of `Cₛ^∞⟮I; E, TangentSpace I⟯`. -/
def deTurckVF (g g' : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => deTurckFun (I := I) g g' x, deTurckFun_contMDiff_total (I := I) g g'⟩

/-- **Evaluation formula for the bundled DeTurck vector field.**  As a function,
the bundled section `deTurckVF g g'` is the metric-trace vector field
`deTurckFun g g'`. -/
@[simp]
theorem deTurckVF_apply (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      deTurckFun (I := I) g g' x := rfl

/-- **The DeTurck vector field of a metric against itself is the zero section.**

When `g = g'` the connection-difference tensor `connDiff g g` is the zero
tensor, so its metric trace vanishes at every point; hence the bundled section
`deTurckVF g g` is the zero section of the tangent bundle. -/
theorem deTurckVF_self (g : SmoothRiemannianMetric I M) :
    deTurckVF (I := I) g g = 0 := by
  ext x
  rw [deTurckVF_apply, deTurckFun_self_apply (I := I) g x]
  rw [ContMDiffSection.coe_zero]
  rfl

/-- **Chart-trace formula for the bundled DeTurck vector field.**

In the chart at `x` itself, the value of the bundled DeTurck vector field is the
metric `g`-trace of the connection-difference tensor: the finite double sum
$$
  (deTurckVF\ g\ g')\,x
    \;=\; \sum_{j,k} G^{jk}(x)\; A\bigl(e_j(x), e_k(x)\bigr),
$$
where `G^{jk} = chartInvGramMatrix g x x` is the inverse Gram matrix of `g` in
the chart-`x` coordinate frame `e_j = chartBasisVecFiber x j` and
`A = connDiff g g' x` is the connection-difference tensor.  This is the explicit
`W = g^{jk}(Γ(g) − Γ̄(g'))`-style formula transported to the bundled section.

Chart-independence of the right-hand side is `deTurckChartLocal_eq_deTurckFun`. -/
theorem deTurckVF_apply_eq (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x j k •
          connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) x j x)
            (chartBasisVecFiber (I := I) x k x) := by
  rw [deTurckVF_apply, deTurckFun_def, deTurckChartLocal_def]

end DeTurck
end PDE
end DifferentialGeometry
