import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifferenceCurvature
import DifferentialGeometry.Geometry.Flow.ConnectionDifference

/-!
# The intrinsic Ricci-difference (Palatini) identity via the connection-difference tensor

For two smooth Riemannian metrics `g₀, g₁` on a closed manifold `M`, the connection-difference
tensor `A := connDiff g₁ g₀ = ∇₁ - ∇₀` (`Geometry/Flow/ConnectionDifference.lean`, the project's
canonical `(1,2)`-tensor packaging of `CovariantDerivative.difference`) controls the difference of
the two Riemann curvature operators by the classical Palatini formula
$$
  R^{∇₁}(X, Y) Z = R^{∇₀}(X, Y) Z
    + (∇₀_X A)(Y, Z) - (∇₀_Y A)(X, Z)
    + A(X, A(Y, Z)) - A(Y, A(X, Z)),
$$
the curvature of a connection plus a tensor.  Tracing the `Z`-slot gives the **intrinsic
Ricci-difference identity**: the difference of the two Ricci tensors is the model-basis trace of the
first-order `(∇₀ A)`-divergence-type term plus the quadratic `A ∧ A` contraction.

This file is the `connDiff`-native restatement of the curvature-difference machinery of
`ConnectionDifferenceCurvature.lean`: that file proves the identity for the raw difference one-form
`CovariantDerivative.difference (LeviCivita g₁) (LeviCivita g₀)`, which is **definitionally**
`connDiff g₁ g₀`; here we re-expose it through the project's primary `connDiff` name as a first-class
reusable engine.  This is the chart-free `C₂` (curvature) content of the Ricci–DeTurck
linearization, with `A = connDiff` the intrinsic Christoffel variation `δΓ`.

## Main definitions

* `covDerivConnDiff g₀ g₁ X Y Z x` — the directional covariant derivative `(∇₀_X A)(Y, Z) (x)` of the
  connection-difference tensor `A = connDiff g₁ g₀` under the `g₀`-Levi-Civita connection (the
  divergence-type / principal `div(∇A)` term of the Palatini identity).

## Main theorems

* `connDiff_eq_difference` — `connDiff g₁ g₀` is the difference one-form
  `CovariantDerivative.difference (LeviCivita g₁) (LeviCivita g₀)`.
* `ricciTensor_sub_eq_connDiff_palatini` — the intrinsic Ricci-difference identity:
  `Ric(g₁)(v, w) - Ric(g₀)(v, w)` equals the model-basis trace of the grouped Palatini terms
  `(∇₀ A)`-divergence minus the swapped slot, plus the quadratic `A(·, A(·, ·))` contraction, with
  `A = connDiff g₁ g₀`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The connection-difference tensor `connDiff g₁ g₀` is the difference one-form
`CovariantDerivative.difference (LeviCivita g₁) (LeviCivita g₀)`, the object the curvature-difference
machinery of `ConnectionDifferenceCurvature.lean` is phrased in.  This is a definitional identity
(`connDiff` unfolds to exactly this `CovariantDerivative.difference`), recorded as a named bridge so
the Palatini identity can be cited in the project's primary `connDiff` vocabulary. -/
theorem connDiff_eq_difference (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiff (I := I) g₁ g₀ =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) := rfl

/-- The **directional covariant derivative of the connection-difference tensor** `A = connDiff g₁ g₀`
under the `g₀`-Levi-Civita connection:
`(∇₀_X A)(Y, Z) (x) = ∇₀_X(A(Y, Z)) (x) - A(∇₀_X Y, Z)(x) - A(Y, ∇₀_X Z)(x)`.

This is the `connDiff`-native packaging of `covDerivDiff (LeviCivita g₀) (LeviCivita g₁)`; it is the
first-order, divergence-type (`div(∇A)`) term of the intrinsic Palatini identity, the part that feeds
the principal symbol of the Ricci–DeTurck `C₂` linearization. -/
def covDerivConnDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x

/-- Unfolding of `covDerivConnDiff` to the underlying `covDerivDiff` of the Levi-Civita pair. -/
theorem covDerivConnDiff_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ X Y Z x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x := rfl

/-- **The intrinsic Ricci-difference (Palatini) identity.**

For two smooth Riemannian metrics `g₀, g₁` and fibre vectors `v, w ∈ T_x M`, the difference of their
Ricci tensors at `x` is the model-basis trace of the grouped Palatini difference-tensor terms built
from the connection-difference tensor `A = connDiff g₁ g₀`:
$$
  \mathrm{Ric}^{g₁}(v, w) - \mathrm{Ric}^{g₀}(v, w)
    = \sum_i \bigl[\,b\bigr]_i\Bigl(
        (∇₀_{B_i} A)(V, W) - (∇₀_V A)(B_i, W)
        + A(B_i, A(V, W)) - A(V, A(B_i, W))
      \Bigr)(x),
$$
where `b = chartModelBasis E`, `B_i = smoothExtensionTangent x (b i)`,
`V = smoothExtensionTangent x v`, `W = smoothExtensionTangent x w`, the first two terms are the
first-order divergence-type `(∇₀ A)` contribution (`covDerivConnDiff`) and the last two are the
quadratic `A ∧ A` contraction (`A = connDiff g₁ g₀` applied via `diffSec`).

This is the `connDiff`-native form of `ricciTensor_sub_eq_basisSum_difference`; it is the chart-free
`C₂` (curvature) core of the Ricci–DeTurck right-hand-side linearization, with `A = connDiff` the
intrinsic Christoffel variation `δΓ`. -/
theorem ricciTensor_sub_eq_connDiff_palatini (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i :=
  ricciTensor_sub_eq_basisSum_difference (I := I) g₀ g₁ x v w

end Connection
end Integral
end DifferentialGeometry
