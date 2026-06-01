import DifferentialGeometry.Integral.Connection.ConnectionLaplacian
import DifferentialGeometry.Integral.Connection.ChartBridge.Hessian

/-!
# Bridge between the connection Laplacian, the chart Laplacian, and the abstract-Hessian
trace

This file packages two equalities that connect the abstract scalar connection Laplacian
`connLaplacian_function g hf` (defined via the metric divergence of the gradient) with
the chart-coordinate Laplacian `Δ_g g hf` and with the basis-naive trace of the abstract
Hessian carrier `abstractHessianBilin g f`.

## Main theorems

* `connLaplacian_function_eq_chartLaplacian` — the scalar connection Laplacian agrees
  with `Δ_g g hf` pointwise. This is `rfl` because `connLaplacian_function g hf` is
  defined as `Δ_g g hf`. Re-exported under the bridge namespace for downstream callers.

* `traceFun_abstractHessian_eq_laplacian` — the basis-naive trace of the abstract
  Hessian carrier equals `Δ_g g hf` at `x`, conditional on the chart at `x` being
  `g`-orthonormal at `x` itself (i.e. `chartInvGramMatrix g x x i j = δ^{ij}`).
  Without orthonormality, the basis-naive trace `∑ i, abstractHessian g f x e_i e_i`
  differs from the metric trace `∑ ij, G^{ij}(x, x) (abstractHessian g f x e_i e_j)`
  which is the geometric Laplacian.

## Strategy

For `traceFun_abstractHessian_eq_laplacian`, the proof chains through:

1. `traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity`
   (the unconditional matrix identity packaged with the trace).
2. `traceFun_hessFun_eq_chartHessTrace_of_orthonormal` — bridging the basis-naive
   trace of `hessFun g f` to the chart-coordinate trace `chartHessTrace g f x`,
   under the orthonormality hypothesis.
3. `chartHessTrace_eq_laplacian_pointwise_of_boundaryless` — the unconditional
   chart-coordinate trace identity to the Laplacian.

The orthonormality hypothesis is the same one used in
`traceFun_hessFun_eq_chartHessTrace_of_orthonormal` and
`laplacian_sq_le_dim_mul_frobenius_sq_via_chartContracted` already in the codebase.
-/

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **Bridge between the scalar connection Laplacian and the chart Laplacian.**
For every smooth scalar function `f : M → ℝ` on a smooth boundaryless Riemannian
manifold, the scalar connection Laplacian agrees with `Δ_g g hf` pointwise. This is
true definitionally. -/
theorem connLaplacian_function_eq_chartLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = Δ_g (I := I) g hf x := rfl

/-- **Trace of the abstract Hessian carrier equals the Laplacian — orthonormal-chart
form.** Conditional on the chart at `x` being `g`-orthonormal at `x` (i.e. the inverse
Gram matrix at `x` is the identity), the basis-naive trace of the abstract Hessian
carrier `abstractHessianBilin g f` equals the chart Laplacian `Δ_g g hf x`.

The proof chains through: (1) the matrix identity packaged on the trace,
`traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity`, which is
unconditional; (2) the chart-coordinate trace identification
`traceFun_hessFun_eq_chartHessTrace_of_orthonormal`, which collapses the
metric trace `∑ G^{ij} H_{ij}` to the basis-naive trace `∑ H_{ii}` under
orthonormality; (3) the unconditional chart-coordinate trace identity
`chartHessTrace_eq_laplacian_pointwise_of_boundaryless`. -/
theorem traceFun_abstractHessian_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      Δ_g (I := I) g hf x := by
  classical
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h1 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
    traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity
      (I := I) g f x hM
  have h2 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x :=
    traceFun_hessFun_eq_chartHessTrace_of_orthonormal (I := I) g f x h_orth
  have h3 : chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x :=
    chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x
  rw [← h1, h2, h3]

/-- **Connection-Laplacian form** of `traceFun_abstractHessian_eq_laplacian`. With the
same orthonormality hypothesis, the basis-naive trace of the abstract Hessian carrier
equals the scalar connection Laplacian. -/
theorem traceFun_abstractHessian_eq_connLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      connLaplacian_function (I := I) g hf x := by
  rw [connLaplacian_function_eq_chartLaplacian (I := I) g hf x]
  exact traceFun_abstractHessian_eq_laplacian (I := I) g hf x h_orth

end Connection
end Integral
end DifferentialGeometry
