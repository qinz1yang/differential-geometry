import DifferentialGeometry.Integral.Connection.TensorRSNabla
import DifferentialGeometry.Integral.Connection.LeviCivita

/-!
# Locality of the `(r, s)`-tensor bundle Levi-Civita covariant derivative

For a smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, this file establishes the *locality* property of the bundled
Levi-Civita covariant derivative on the `(r, s)`-tensor bundle: two sections
that agree on a neighbourhood of a point `x` have the same covariant
derivative at `x`, provided both are sufficiently differentiable.

The result is a direct specialisation of Mathlib's
`IsCovariantDerivativeOn.congr_of_eventuallyEq` to the `(r, s)`-tensor bundle
covariant derivative `TensorRSNabla.tensorRSCovariantDerivative I M r s
(LeviCivita g)`, which carries a global `IsCovariantDerivativeOn ... Set.univ`
structure via the bundled `CovariantDerivative.isCovariantDerivativeOnUniv`
field.

## Main result

* `tensorRSCovariantDerivative_congr_of_eventuallyEq` — given two sections
  `σ, σ' : Π b, TensorRSSpace r s I b` that agree on a neighbourhood of `x`
  (i.e. `∀ᶠ y in 𝓝 x, σ y = σ' y` — the dependent-type version of an
  eventually-equal hypothesis) and are both `MDifferentiableAt` at `x` (in
  the total-space sense), the pointwise value of the `(r, s)`-tensor
  covariant derivative agrees at `x`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open Bundle CovariantDerivative Filter Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Locality of the `(r, s)`-tensor bundle Levi-Civita covariant derivative.**

Two sections `σ, σ' : Π b : M, TensorRSSpace r s I b` that agree on a
neighbourhood of `x` have equal Levi-Civita-induced covariant derivatives at
`x`, provided both are differentiable at `x` in the total-space sense.

This is a specialisation of Mathlib's
`IsCovariantDerivativeOn.congr_of_eventuallyEq` to the bundled
`(r, s)`-tensor covariant derivative
`TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita g)`. The
neighbourhood-set hypothesis is supplied by the trivial fact
`Set.univ ∈ 𝓝 x`. -/
theorem tensorRSCovariantDerivative_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {σ σ' : Π b : M, TensorRSSpace r s I b}
    {x : M} (hagree : ∀ᶠ y in 𝓝 x, σ y = σ' y)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
            (fun y : M =>
              TotalSpace.mk' (TensorRSModel r s ℝ E) y (σ y)) x)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
            (fun y : M =>
              TotalSpace.mk' (TensorRSModel r s ℝ E) y (σ' y)) x) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun σ x =
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun σ' x := by
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := σ) (σ' := σ') (x := x)
    hσ hσ' Filter.univ_mem hagree

end Connection
end Integral
end DifferentialGeometry

end
