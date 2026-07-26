import DifferentialGeometry.Geometry.Flow.DeTurckOperator
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Foundational toolkit for linearizing the chart Ricci tensor

The chart Ricci tensor of a Riemannian metric is, in chart coordinates, a fixed algebraic
expression `Rc = F(G, ∂G, ∂²G, G⁻¹)` in the chart Gram matrix `G`, its first and second
Fréchet partial derivatives, and the chart inverse Gram matrix `G⁻¹`.  Linearizing that
expression in a *metric-perturbation* direction is a purely algebraic computation: it does
not see positive-definiteness of the perturbation, only its symmetry and smoothness.

This file collects the scaffolding that the linearization steps consume.  It contains no
Ricci-specific content.

## Contents

### Partial-derivative algebra

The boundaryless Fréchet partial derivative `partialDeriv i u y = fderiv ℝ u y
(chartModelBasis E i)` from `Analysis/Integration/DivergenceTheorem/LocalFormula.lean` lacks the
elementary algebra lemmas (its with-boundary cousin `partialDerivWithin` has them).  We
supply them here:

* `partialDeriv_add`, `partialDeriv_sub` — additivity / subtractivity;
* `partialDeriv_smul` — the `ℝ`-scalar Leibniz rule for `c • u`;
* `partialDeriv_const_smul`, `partialDeriv_const_mul` — derivative of `c • u` / `c * u`
  for a genuine constant `c`;
* `partialDeriv_mul` — the Leibniz product rule for real-valued functions;
* `partialDeriv_sum` — additivity over a finite sum;
* `partialDeriv_const` — the partial derivative of a constant function vanishes.

Each `partialDeriv` of a non-constant expression carries the `DifferentiableAt ℝ`
hypotheses required by the corresponding `fderiv` lemma.

### The metric-perturbation convention

A *chart-coordinate metric perturbation* is a family of component fields
`H : Fin n → Fin n → (E → ℝ)`, with `H i j` playing the role of `h_{ij}(y)` in chart
coordinates.  It is symmetric and smooth, but **not** required to be positive-definite —
the Ricci symbol is purely algebraic.  We bundle the data in the structure
`ChartMetricPerturbation E`, with a `CoeFun` so that `h i j` denotes the `(i, j)`
component field directly.

### Metric trace and index raising

Given a metric `g` and a perturbation `h`, working in the chart at a point `x`:

* `raisedCovectorComp g x ξ m` — the `m`-th raised component `ξ^m = ∑ₙ g^{mn} ξₙ` of a
  covector `ξ` (the same inverse-Gram contraction used by `metricCovectorNormSq`);
* `metricTrace g x h` — the `g`-trace `tr_g h = ∑_{m,n} g^{mn} h_{mn}` of the
  perturbation at `x`.

### The inverse-Gram perturbation

* `invGramPerturbation g α h y` — the algebraic field
  `D(G^{lm})[h] = −∑_{a,b} G^{la} G^{bm} h_{ab}`, the linearization of `G ↦ G⁻¹`
  obtained by differentiating `G · G⁻¹ = I`.  It is recorded as a closed-form definition
  with its symmetry lemma; the downstream linearization reads the Ricci symbol off the
  `∂²h`-coefficients directly, so `invGramPerturbation` only ever contributes lower-order
  terms.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section PartialDerivAlgebra

variable {i : Fin (Module.finrank ℝ E)} {y : E}

/-- Additivity of the partial derivative. -/
lemma partialDeriv_add (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) i (fun y => u y + v y) y =
      partialDeriv (E := E) i u y + partialDeriv (E := E) i v y := by
  unfold partialDeriv
  rw [fderiv_fun_add hu hv]
  rfl

/-- Subtractivity of the partial derivative. -/
lemma partialDeriv_sub (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) i (fun y => u y - v y) y =
      partialDeriv (E := E) i u y - partialDeriv (E := E) i v y := by
  unfold partialDeriv
  rw [fderiv_fun_sub hu hv]
  rfl

/-- The `ℝ`-scalar Leibniz rule for the partial derivative: here `c` is the scalar
function and `u` the real-valued function being scaled. -/
lemma partialDeriv_smul (c u : E → ℝ)
    (hc : DifferentiableAt ℝ c y) (hu : DifferentiableAt ℝ u y) :
    partialDeriv (E := E) i (fun y => c y • u y) y =
      c y • partialDeriv (E := E) i u y + partialDeriv (E := E) i c y • u y := by
  unfold partialDeriv
  rw [fderiv_fun_smul hc hu]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]

/-- Derivative of a genuine-constant scalar multiple `c • u`. -/
lemma partialDeriv_const_smul (c : ℝ) (u : E → ℝ)
    (hu : DifferentiableAt ℝ u y) :
    partialDeriv (E := E) i (fun y => c • u y) y =
      c • partialDeriv (E := E) i u y := by
  unfold partialDeriv
  rw [fderiv_fun_const_smul hu c]
  rfl

/-- Derivative of a genuine-constant left product `c * u`. -/
lemma partialDeriv_const_mul (c : ℝ) (u : E → ℝ)
    (hu : DifferentiableAt ℝ u y) :
    partialDeriv (E := E) i (fun y => c * u y) y =
      c * partialDeriv (E := E) i u y := by
  unfold partialDeriv
  rw [fderiv_const_mul hu c]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Leibniz product rule for the partial derivative of a product of real-valued
functions. -/
lemma partialDeriv_mul (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) i (fun y => u y * v y) y =
      partialDeriv (E := E) i u y * v y + u y * partialDeriv (E := E) i v y := by
  unfold partialDeriv
  rw [fderiv_fun_mul hu hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Additivity of the partial derivative over a finite sum. -/
lemma partialDeriv_sum {ι : Type*} (s : Finset ι) (A : ι → E → ℝ)
    (hA : ∀ k ∈ s, DifferentiableAt ℝ (A k) y) :
    partialDeriv (E := E) i (fun y => ∑ k ∈ s, A k y) y =
      ∑ k ∈ s, partialDeriv (E := E) i (A k) y := by
  unfold partialDeriv
  rw [fderiv_fun_sum hA]
  rw [ContinuousLinearMap.sum_apply]

/-- The partial derivative of a constant function vanishes. -/
@[simp] lemma partialDeriv_const (c : ℝ) :
    partialDeriv (E := E) i (fun _ : E => c) y = 0 := by
  unfold partialDeriv
  rw [show (fun _ : E => c) = Function.const E c from rfl, fderiv_const]
  rfl

end PartialDerivAlgebra

/-- A **chart-coordinate metric perturbation**: a family `toFun i j : E → ℝ` of component
fields, with `toFun i j` standing for `h_{ij}(y)` in chart coordinates.  It is symmetric
and smooth.  It is deliberately **not** required to be positive-definite — the Ricci
symbol is a purely algebraic object and never uses positivity of the perturbation.

The smoothness field requests `ContDiff ℝ ∞` on all of `E`.  This is the simplest
hypothesis that supports the Schwarz-symmetry and Leibniz manipulations of the later
steps; in practice a chart-supported perturbation is extended smoothly to all of `E`
before being packaged here. -/
structure ChartMetricPerturbation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] where

  toFun : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)

  symm' : ∀ i j y, toFun i j y = toFun j i y

  smooth' : ∀ i j, ContDiff ℝ ∞ (toFun i j)

namespace ChartMetricPerturbation

/-- Apply a perturbation as the family of component fields, so `h i j` denotes the
`(i, j)` component field `h_{ij} : E → ℝ`. -/
instance : CoeFun (ChartMetricPerturbation E)
    (fun _ => Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)) :=
  ⟨ChartMetricPerturbation.toFun⟩

@[simp] lemma coe_mk
    (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ))
    (hsymm : ∀ i j y, f i j y = f j i y) (hsmooth : ∀ i j, ContDiff ℝ ∞ (f i j)) :
    ⇑(ChartMetricPerturbation.mk f hsymm hsmooth) = f := rfl

/-- Symmetry of the perturbation: `h_{ij}(y) = h_{ji}(y)`. -/
lemma symm (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    h i j y = h j i y := h.symm' i j y

/-- Index-swap as a function identity: `h i j = h j i`. -/
lemma symm_fun (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) :
    h i j = h j i := funext (h.symm i j)

/-- Every component field of a perturbation is `C^∞`. -/
lemma smooth (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (h i j) := h.smooth' i j

/-- Every component field of a perturbation is differentiable at every point. -/
lemma differentiableAt (h : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentiableAt ℝ (h i j) y :=
  ((h.smooth i j).differentiable (by simp)).differentiableAt

/-- The zero perturbation. -/
instance : Zero (ChartMetricPerturbation E) :=
  ⟨{ toFun := fun _ _ _ => 0
     symm' := fun _ _ _ => rfl
     smooth' := fun _ _ => contDiff_const }⟩

@[simp] lemma zero_apply (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (0 : ChartMetricPerturbation E) i j y = 0 := rfl

/-- Two perturbations are equal once their component fields agree. -/
@[ext] lemma ext {h h' : ChartMetricPerturbation E}
    (hyp : ∀ i j, (h i j) = (h' i j)) : h = h' := by
  cases h; cases h'; congr 1; funext i j; exact hyp i j

end ChartMetricPerturbation

section TraceAndRaising

/-- The `m`-th **raised component** of a covector `ξ`, in the chart at `x`:
$$\xi^m = \sum_n g^{mn}(x)\, \xi_n,$$
where `g^{mn} = chartInvGramMatrix g x x` is the chart inverse metric and
`ξ_n = (chartModelBasis E).repr ξ n` are the chart components of `ξ`.

Summing `raisedCovectorComp g x ξ m * (chartModelBasis E).repr ξ m` over `m` recovers
`metricCovectorNormSq g x ξ`. -/
def raisedCovectorComp (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (m : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ n : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x m n * (chartModelBasis E).repr ξ n

@[simp] lemma raisedCovectorComp_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (m : Fin (Module.finrank ℝ E)) :
    raisedCovectorComp (I := I) g x ξ m =
      ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x m n * (chartModelBasis E).repr ξ n := rfl

/-- The raised covector of the zero covector vanishes. -/
@[simp] lemma raisedCovectorComp_zero (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin (Module.finrank ℝ E)) :
    raisedCovectorComp (I := I) g x (0 : E) m = 0 := by
  simp [raisedCovectorComp]

/-- Contracting the raised covector against the covariant components recovers the squared
`g`-norm `metricCovectorNormSq`. -/
lemma sum_raisedCovectorComp_mul_repr
    (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    ∑ m : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ m * (chartModelBasis E).repr ξ m =
      metricCovectorNormSq (I := I) g x ξ := by
  rw [metricCovectorNormSq_def]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [raisedCovectorComp_def, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

/-- The **metric trace** of a perturbation `h` at a point `x`, in the chart at `x`:
$$\operatorname{tr}_g h \;=\; \sum_{m,n} g^{mn}(x)\, h_{mn}(\varphi_x(x)),$$
the full contraction of the chart inverse Gram matrix against the perturbation
components, evaluated at the chart image `extChartAt I x x` of `x`. -/
def metricTrace (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    ∑ n : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x m n * h m n (extChartAt I x x)

@[simp] lemma metricTrace_def (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) :
    metricTrace (I := I) g x h =
      ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x m n * h m n (extChartAt I x x) := rfl

/-- The metric trace of the zero perturbation vanishes. -/
@[simp] lemma metricTrace_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricTrace (I := I) g x (0 : ChartMetricPerturbation E) = 0 := by
  simp [metricTrace]

/-- The metric trace depends only on the perturbation's component fields. -/
lemma metricTrace_congr (g : SmoothRiemannianMetric I M) (x : M)
    {h h' : ChartMetricPerturbation E}
    (hyp : ∀ m n, h m n (extChartAt I x x) = h' m n (extChartAt I x x)) :
    metricTrace (I := I) g x h = metricTrace (I := I) g x h' := by
  rw [metricTrace_def, metricTrace_def]
  exact Finset.sum_congr rfl (fun m _ =>
    Finset.sum_congr rfl (fun n _ => by rw [hyp m n]))

/-- The metric trace is a sum of products `g^{mn} · h_{mn}`, additively over the
contraction indices.  This is the explicit form used by linearity computations. -/
lemma metricTrace_eq_sum (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) :
    metricTrace (I := I) g x h =
      ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x p.1 p.2 *
          h p.1 p.2 (extChartAt I x x) := by
  rw [metricTrace_def, ← Finset.sum_product', Finset.univ_product_univ]

end TraceAndRaising

section InvGramPerturbation

/-- The **inverse-Gram perturbation**: the linearization of `G ↦ G⁻¹` at the metric `g`
(in the chart at `α`, pulled back to the chart target) in the perturbation direction
`h`.  The closed form
$$D(G^{lm})[h](y) \;=\; -\sum_{a,b} G^{la}(y)\, G^{bm}(y)\, h_{ab}(y)$$
is obtained by differentiating `G · G⁻¹ = I`, with `G^{··} = chartInvGramOnE g α`. -/
def invGramPerturbation (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  -∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α l a y *
        chartInvGramOnE (I := I) g α b m y * h a b y

@[simp] lemma invGramPerturbation_def (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α h l m y =
      -∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α l a y *
            chartInvGramOnE (I := I) g α b m y * h a b y := rfl

/-- The inverse-Gram perturbation along the zero direction vanishes. -/
@[simp] lemma invGramPerturbation_zero (g : SmoothRiemannianMetric I M) (α : M)
    (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α (0 : ChartMetricPerturbation E) l m y = 0 := by
  simp [invGramPerturbation]

/-- Symmetry of the inverse-Gram perturbation: since `G⁻¹` is symmetric and `h` is
symmetric, so is the linearization `D(G⁻¹)[h]`. -/
lemma invGramPerturbation_symm (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α h l m y =
      invGramPerturbation (I := I) g α h m l y := by
  rw [invGramPerturbation_def, invGramPerturbation_def]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartInvGramOnE_symm (I := I) g α l b y,
    chartInvGramOnE_symm (I := I) g α a m y, h.symm b a y]
  ring

end InvGramPerturbation

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
