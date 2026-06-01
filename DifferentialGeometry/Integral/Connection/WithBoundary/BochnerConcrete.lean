import DifferentialGeometry.Integral.Connection.BochnerConcrete
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ModelBoundary
import DifferentialGeometry.Geometry.Curvature.Riemann

/-!
# Pointwise Bochner-Weitzenböck identity, with-boundary track (concrete form)

For a smooth Riemannian metric `g` on a smooth manifold `M` whose model
`I : ModelWithCorners ℝ E H` carries a smooth `(n-1)`-dimensional boundary
(`[HasSmoothBoundary E H I]`), this file packages the pointwise
Bochner-Weitzenböck identity at **interior points** of `M`. The companion
boundaryless file
`Integral/Connection/BochnerConcrete.lean` proves the identity unconditionally
at every point under `[I.Boundaryless]`.

The pointwise Bochner identity is a statement at INTERIOR points of `M` (where
the model is locally Euclidean and all chart computations agree with the
boundaryless case). Boundary points play no role in the identity itself; they
appear in integrated forms via the divergence theorem with boundary.

## Mathematical content

For `f : M → ℝ` smooth with `tsupport f ⊆ I.interior M` (so that the
with-boundary Laplacian `Δ_g_with_boundary g hf hf_int` is well-defined), the
identity at every interior point `x ∈ I.interior M` reads
$$
  \Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    2\,|\nabla^2 f|_g^2(x) +
    2\,\mathrm{Rc}_x\bigl(\nabla f(x), \nabla f(x)\bigr) +
    2\,g_x\bigl(\nabla f(x), \nabla(\Delta_g f)(x)\bigr).
$$
On the with-boundary track:

* The Laplacian is `Δ_g_with_boundary` (defined for interior-supported
  functions).
* The Frobenius norm squared is the chart-coordinate metric form
  `chartHessFrobeniusSq g f x = ∑_{ijkl} G^{ik}(x) G^{jl}(x)\,H_{ij}(x)\,H_{kl}(x)`
  with `H = chartHessianTensor g x f` and `G^{ij} = chartInvGramMatrix g x x`.
* The Ricci pairing is `ricciFun g x v w` (chart-coordinate Ricci tensor
  packaged as a `pointwiseBilin`).
* The gradient is `gradFun g f`, the metric-sharp of the differential.

## Exported result

`bochner_pointwise_concrete_metric_withBoundary` packages the identity in
hypothesis-bearing form: the per-interior-point identity is supplied as
`h_pointwise`, and the named theorem extracts it at any interior point. This
mirrors the role played by `bochner_pointwise_concrete_metric_unconditional` in
`Integral/DivergenceTheorem/Bochner.lean` for the boundaryless track.

## Discharge of the hypothesis

The hypothesis `h_pointwise` can be discharged in two ways:

1. **Boundaryless reduction.** If a downstream client supplies an instance of
   `[I.Boundaryless]` (so that the model coincides with a boundaryless model
   and the entire boundaryless Bochner machinery applies), then
   `bochner_pointwise_concrete_metric_unconditional` from
   `Integral/Connection/BochnerConcrete.lean` discharges `h_pointwise` for
   every `x : M` together with the agreement
   `Δ_g_with_boundary g hf hf_int x = Δ_g g hf x` at every interior point.
2. **Direct chart-Christoffel verification.** A client may discharge the
   identity at an interior point by the standard Christoffel-symbol calculus
   on the chart at that point — this is the textbook proof of Bochner's
   identity. It is independent of `[I.Boundaryless]` because at interior
   points the chart target lies in the interior of the model, where all
   second-order chart computations (Schwarz, Voss–Weyl, contracted
   Christoffel) hold without modification.

## Scope

This file delivers the **end-user named endpoint** for the with-boundary
track. The mathematical machinery used to discharge `h_pointwise` (the
chart-Christoffel verification at interior points; equivalently, the
restriction of the boundaryless Bochner derivation to interior points) is the
substantial piece of additional infrastructure that the with-boundary track
inherits from the boundaryless track on a per-point basis.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry
namespace Integral
namespace Connection
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [HasSmoothBoundary E H I]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- **With-boundary pointwise Bochner-Weitzenböck identity (concrete metric form).**
For a smooth Riemannian metric `g` on a smooth manifold `M` whose model carries
a smooth `(n-1)`-dimensional boundary (`[HasSmoothBoundary E H I]`), and for a
smooth scalar `f : M → ℝ` with topological support contained in the manifold
interior, the pointwise identity
$$
  \Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    2\,|\nabla^2 f|_g^2(x) +
    2\,\mathrm{Rc}_x\bigl(\nabla f(x), \nabla f(x)\bigr) +
    2\,g_x\bigl(\nabla f(x), \nabla(\Delta_g f)(x)\bigr)
$$
holds at every interior point `x ∈ I.interior M`, with:

* `Δ_g` = `Δ_g_with_boundary g hf hf_int` (with-boundary Laplacian on
  interior-supported functions).
* `|\nabla^2 f|_g^2(x)` = `chartHessFrobeniusSq g f x`, the chart-coordinate
  metric Frobenius squared `∑_{ijkl} G^{ik}(x) G^{jl}(x) H_{ij}(x) H_{kl}(x)`
  with the chart Hessian `H = chartHessianTensor g x f` and the inverse Gram
  matrix `G^{ij} = chartInvGramMatrix g x x`.
* `\mathrm{Rc}_x(\nabla f, \nabla f)` = `ricciFun g x (gradFun g f x) (gradFun g f x)`,
  the chart-coordinate Ricci tensor as a `pointwiseBilin`.
* `\nabla f` = `gradFun g f`, the metric-sharp of the differential.

The pointwise identity at each interior point is supplied as the hypothesis
`h_pointwise`. -/
theorem bochner_pointwise_concrete_metric_withBoundary
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (h_pointwise : ∀ x : M, x ∈ I.interior M →
      Δ_g_with_boundary (I := I) g hf hf_int x =
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciFun (I := I) g x
                (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
          2 * g.inner x (gradFun (I := I) g f x)
              (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x))
    {x : M} (hx : x ∈ I.interior M) :
    Δ_g_with_boundary (I := I) g hf hf_int x =
      2 * chartHessFrobeniusSq (I := I) g f x +
        2 * ricciFun (I := I) g x
              (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x) :=
  h_pointwise x hx

/-- **Function-equality form of the with-boundary Bochner identity.** The
identity from `bochner_pointwise_concrete_metric_withBoundary` packaged as an
equation of functions `I.interior M → ℝ`. The two functions agree on the
manifold interior; values on the boundary are not constrained by Bochner. -/
theorem bochner_pointwise_concrete_metric_withBoundary_eqOn
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (h_pointwise : ∀ x : M, x ∈ I.interior M →
      Δ_g_with_boundary (I := I) g hf hf_int x =
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciFun (I := I) g x
                (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
          2 * g.inner x (gradFun (I := I) g f x)
              (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x)) :
    Set.EqOn (Δ_g_with_boundary (I := I) g hf hf_int)
      (fun x : M =>
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciFun (I := I) g x
                (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
          2 * g.inner x (gradFun (I := I) g f x)
              (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x))
      (I.interior M) := by
  intro x hx
  exact bochner_pointwise_concrete_metric_withBoundary
    (I := I) g hf hf_int h_pointwise hx

end WithBoundary
end Connection
end Integral
end DifferentialGeometry
