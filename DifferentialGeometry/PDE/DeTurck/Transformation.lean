import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric

/-!
# The Ricci–DeTurck operator

For two smooth Riemannian metrics `g` and `g'` on a smooth manifold `M` — an *evolving*
metric `g` and a fixed *background* metric `g'` — the **Ricci–DeTurck operator** is the
right-hand side of the Ricci–DeTurck flow
$$
  \partial_t g \;=\; -2\,\operatorname{Rc}(g) \;+\; \mathcal L_{W} g,
$$
where `W = W(g, g')` is the DeTurck vector field of the pair.  Bare Ricci flow is the
equation `∂_t g = −2 Rc(g)`; the DeTurck modification adds the Lie-derivative term
`𝓛_W g` along the DeTurck vector field `W`, which converts the (only weakly parabolic)
Ricci-flow operator into a strictly parabolic one.

This file assembles that right-hand side as a `(0,2)`-tensor field and records its basic
properties.  The two summands are built in the preceding files:

* `−2 Rc(g)` uses `ricciFun g`, the Ricci tensor of `g` as a pointwise bilinear form
  (`Geometry/Curvature/Riemann.lean`);
* `𝓛_W g` uses `lieDerivMetric g W` with `W := deTurckVF g g'`, the Lie derivative of `g`
  along the DeTurck vector field (`PDE/DeTurck/LieDerivativeMetric.lean`,
  `PDE/DeTurck/VectorField.lean`).

The operator is assembled pointwise: at each `x : M` it is the bilinear-form sum
`(-2) • Rc(g)(x) + 𝓛_W g(x)` on `TangentSpace I x`.

## Main definitions

* `deTurckOp g g'` — the Ricci–DeTurck operator at `g` with background `g'`, as a bundled
  `(0,2)`-tensor field `pointwiseBilin I`.

## Main results

* `deTurckOp_apply` — the pointwise evaluation
  `deTurckOp g g' x v w = -2 * Rc(g)(x)(v, w) + 𝓛_W g(x)(v, w)`.
* `deTurckOp_self` — when the background metric equals the evolving metric, the DeTurck
  term vanishes and the operator reduces to bare `−2 Rc(g)`.
* `deTurckOp_isPointwiseSymm` — the Ricci–DeTurck operator is a symmetric `(0,2)`-tensor.
* `deTurckOp_basis_apply` / `chartDeTurckOpMatrix_eq` — the chart-component formula
  `(deTurckOp g g')_{ij} = -2 · Rc(g)_{ij} + (𝓛_W g)_{ij}` in chart coordinates, the
  input later linearization steps consume.
* `chartDeTurckOpMatrix_contMDiffOn` — chart-source smoothness of the components, given
  the chart-source smoothness of the Ricci components.
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

/-- The **Ricci–DeTurck operator** of an evolving metric `g` against a background metric
`g'`, as a bundled `(0,2)`-tensor field (`pointwiseBilin I`).

This is the right-hand side
$$
  \mathcal D(g, g') \;=\; -2\,\operatorname{Rc}(g) \;+\; \mathcal L_{W(g, g')}\,g
$$
of the Ricci–DeTurck flow `∂_t g = −2 Rc(g) + 𝓛_W g`.  Bare Ricci flow is the equation
`∂_t g = −2 Rc(g)`; the DeTurck modification adds the Lie-derivative term `𝓛_W g` along
the DeTurck vector field `W = deTurckVF g g'`, the modification that turns the
Ricci-flow operator into a strictly parabolic system.

At each point `x`, the value is the bilinear-form sum `(-2) • ricciFun g x +
lieDerivMetric g (deTurckVF g g') x` on `TangentSpace I x`. -/
def deTurckOp (g g' : SmoothRiemannianMetric I M) :
    pointwiseBilin (M := M) I :=
  fun x => (-2 : ℝ) • ricciFun (I := I) g x +
    lieDerivMetric (I := I) g (deTurckVF (I := I) g g') x

/-- Unfolding lemma for `deTurckOp`: at a point `x`, the operator is the bilinear-form
sum `(-2) • Rc(g)(x) + 𝓛_W g(x)`. -/
lemma deTurckOp_def (g g' : SmoothRiemannianMetric I M) (x : M) :
    deTurckOp (I := I) g g' x =
      (-2 : ℝ) • ricciFun (I := I) g x +
        lieDerivMetric (I := I) g (deTurckVF (I := I) g g') x := rfl

/-- **Pointwise evaluation of the Ricci–DeTurck operator.**  Applied to two tangent
vectors `v, w` at `x`, the operator returns
$$
  \mathcal D(g, g')(x)(v, w)
    \;=\; -2\,\operatorname{Rc}(g)(x)(v, w) \;+\; (\mathcal L_W g)(x)(v, w),
$$
the term-by-term sum of `−2` times the Ricci tensor and the metric Lie derivative
along the DeTurck vector field. -/
@[simp] theorem deTurckOp_apply (g g' : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    deTurckOp (I := I) g g' x v w =
      -2 * ricciFun (I := I) g x v w +
        lieDerivMetric (I := I) g (deTurckVF (I := I) g g') x v w := by
  rw [deTurckOp_def, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]

/-- **The Ricci–DeTurck operator against a metric and itself reduces to `−2 Rc(g)`.**

When the background metric equals the evolving metric, the DeTurck vector field
`deTurckVF g g` is the zero section, so the Lie-derivative term `𝓛_{W} g` vanishes; the
operator is then exactly the bare Ricci-flow right-hand side, the pointwise scalar
multiple `(-2) • Rc(g)`. -/
theorem deTurckOp_self [I.Boundaryless] (g : SmoothRiemannianMetric I M) :
    deTurckOp (I := I) g g = fun x => (-2 : ℝ) • ricciFun (I := I) g x := by
  funext x
  rw [deTurckOp_def, deTurckVF_self (I := I) g, lieDerivMetric_zero (I := I) g]
  rw [add_zero]

/-- **Pointwise evaluation of the Ricci–DeTurck operator against a metric and itself.**
Applied to two tangent vectors, the operator returns `−2` times the Ricci tensor of
`g`, the DeTurck term having vanished. -/
@[simp] theorem deTurckOp_self_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    deTurckOp (I := I) g g x v w = -2 * ricciFun (I := I) g x v w := by
  rw [deTurckOp_apply, deTurckVF_self (I := I) g, lieDerivMetric_zero (I := I) g]
  simp

/-- **Symmetry of the Ricci–DeTurck operator as a `(0,2)`-tensor:**
`𝓓(g, g')(v, w) = 𝓓(g, g')(w, v)`.

Both the Ricci tensor of `g` and the metric Lie derivative along the DeTurck vector
field are symmetric bilinear forms, so their combination `−2 Rc(g) + 𝓛_W g` is
symmetric. -/
theorem deTurckOp_isPointwiseSymm [I.Boundaryless]
    (g g' : SmoothRiemannianMetric I M) :
    IsPointwiseSymm (deTurckOp (I := I) (M := M) g g') := by
  intro x v w
  rw [deTurckOp_apply, deTurckOp_apply]
  rw [ricciFun_isPointwiseSymm_of_boundaryless (I := I) g x v w,
    lieDerivMetric_isPointwiseSymm (I := I) g (deTurckVF (I := I) g g') x v w]

/-- The **canonical chart component** `(𝓓(g, g'))_{ij}` of the Ricci–DeTurck operator at
`x`: by definition `−2` times the chart Ricci component plus the chart Lie-derivative
component, both read in the chart at `x` itself.

The Ricci component is `chartRicciTensor g x i j (extChartAt I x x)` — the
chart-coordinate Ricci tensor — and the Lie-derivative component is
`lieDerivMetricMatrix g (deTurckVF g g') i j x`, the canonical metric Lie-derivative
component along the DeTurck vector field. -/
def chartDeTurckOpMatrix (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  -2 * chartRicciTensor (I := I) g x i j (extChartAt I x x) +
    lieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g') i j x

@[simp] lemma chartDeTurckOpMatrix_def (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartDeTurckOpMatrix (I := I) g g' i j x =
      -2 * chartRicciTensor (I := I) g x i j (extChartAt I x x) +
        lieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g') i j x := rfl

/-- **The Ricci–DeTurck operator on the canonical basis vectors returns its chart
component.**  Evaluated on the model-basis vectors `e_i, e_j`, the operator
`deTurckOp g g' x` returns the canonical chart component `chartDeTurckOpMatrix g g' i j
x`, i.e. the explicit coordinate combination `−2 Rc(g)_{ij} + (𝓛_W g)_{ij}`. -/
theorem deTurckOp_basis_apply (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    deTurckOp (I := I) g g' x
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      chartDeTurckOpMatrix (I := I) g g' i j x := by
  rw [deTurckOp_apply, chartDeTurckOpMatrix_def,
    ricciFun_basis_apply (I := I) g x i j,
    lieDerivMetric_basis_apply (I := I) g (deTurckVF (I := I) g g') x i j]

/-- **Explicit chart-component formula for the Ricci–DeTurck operator.**  In the chart at
`x` itself, the canonical component `(𝓓(g, g'))_{ij}` is the textbook coordinate
combination
$$
  \bigl(\mathcal D(g, g')\bigr)_{ij}
    \;=\; -2\,\operatorname{Rc}(g)_{ij}
        \;+\; W^k\,\partial_k g_{ij} + g_{kj}\,\partial_i W^k + g_{ik}\,\partial_j W^k,
$$
where the Ricci component is `chartRicciTensor` and the Lie-derivative component is
expanded by `lieDerivMetricMatrix_def` into its convective and deformation summands
along the DeTurck vector field `W = deTurckVF g g'`. -/
theorem chartDeTurckOpMatrix_eq (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartDeTurckOpMatrix (I := I) g g' i j x =
      -2 * chartRicciTensor (I := I) g x i j (extChartAt I x x)
      + ((∑ k : Fin (Module.finrank ℝ E),
            chartCoeff (I := I) x (deTurckVF (I := I) g g') k x *
              partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
                (extChartAt I x x))
          + (∑ k : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g x x k j *
                partialDeriv (E := E) i
                  (chartCoeffOnE (I := I) x (deTurckVF (I := I) g g') k)
                  (extChartAt I x x))
          + (∑ k : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g x x i k *
                partialDeriv (E := E) j
                  (chartCoeffOnE (I := I) x (deTurckVF (I := I) g g') k)
                  (extChartAt I x x))) := by
  rw [chartDeTurckOpMatrix_def, lieDerivMetricMatrix_def]

/-- **Symmetry of the canonical Ricci–DeTurck chart component** in the index pair
`(i, j)`: the Ricci component is symmetric by `chartRicciTensor_symm_of_boundaryless`
and the Lie-derivative component by `lieDerivMetricMatrix_symm`. -/
theorem chartDeTurckOpMatrix_symm [I.Boundaryless]
    (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartDeTurckOpMatrix (I := I) g g' i j x =
      chartDeTurckOpMatrix (I := I) g g' j i x := by
  rw [chartDeTurckOpMatrix_def, chartDeTurckOpMatrix_def,
    lieDerivMetricMatrix_symm (I := I) g (deTurckVF (I := I) g g') i j,
    chartRicciTensor_symm_of_boundaryless (I := I) g x i j (mem_chart_source H x)]

/-- **Smoothness of the Ricci–DeTurck operator chart components, hypothesis-bearing
form.**  Given the chart-source smoothness of the canonical Ricci component
`fun x => chartRicciTensor g x i j (extChartAt I x x)` and of the canonical metric
Lie-derivative component `lieDerivMetricMatrix g (deTurckVF g g') i j`, the canonical
Ricci–DeTurck chart component `chartDeTurckOpMatrix g g' i j` is `C^∞` on the chart
source.

The Lie-derivative hypothesis is the canonical (chart-at-the-point) component, whose
smoothness is a statement about how the chart at the basepoint varies; the chart-`α`
representative is already known smooth by `chartLieDerivMetricMatrix_contMDiffOn`. -/
theorem chartDeTurckOpMatrix_contMDiffOn (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (α : M)
    (hRic : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => chartRicciTensor (I := I) g x i j (extChartAt I x x))
      (chartAt H α).source)
    (hLie : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (lieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g') i j)
      (chartAt H α).source) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (chartDeTurckOpMatrix (I := I) g g' i j) (chartAt H α).source := by
  refine ContMDiffOn.congr ?_ (fun x _ => chartDeTurckOpMatrix_def
    (I := I) g g' i j x)
  exact ((contMDiffOn_const (c := (-2 : ℝ))).mul hRic).add hLie

end DeTurck
end PDE
end DifferentialGeometry
