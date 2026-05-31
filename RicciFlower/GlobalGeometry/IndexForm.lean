import RicciFlower.GlobalGeometry.Lecture07.FirstVariation
import RicciFlower.GlobalGeometry.Lecture07.Jacobi

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Myers index-form scaffolding

This file starts the GSM245 Myers proof stack at the definition layer.  It does
not prove the second-variation theorem or any diameter estimate; it only records
the data shapes consumed by the later index-form and Bonnet-Myers arguments.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Filter intervalIntegral
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The index form integrand data for a single along-field `V`.

`DV` is the selected covariant derivative `D_t V`, and `CurvV` is the selected
curvature field, intended later to be `R(V,T)T`.  This definition deliberately
keeps both fields explicit: the current Lecture 7 along-curve derivative and
curvature APIs are relation-valued, not canonical functions of `V`. -/
def indexForm
    (g : SmoothRiemannianMetric I M) (gamma : Lecture07.Curve M)
    (V DV CurvV : Lecture07.VectorFieldAlong I gamma) (a b : Real) : Real :=
  ∫ t in a..b,
    (g.inner (gamma t) (DV t) (DV t) -
      g.inner (gamma t) (CurvV t) (V t))

/-- A two-parameter variation has a local length minimum at the central
variation parameter `0`.

This is the minimizing-geodesic consumer shape used by the second-variation
layer: the central time curve is locally length-minimizing among nearby
variation curves. -/
def IsLengthLocalMin
    (g : SmoothRiemannianMetric I M) (F : Surface M) (a b : Real) : Prop :=
  ∀ᶠ s in 𝓝 (0 : Real),
    Lecture07.variationLength (I := I) g F a b 0 ≤
      Lecture07.variationLength (I := I) g F a b s

/-- Relation-valued parallelism for a vector field along a curve.

This is the along-field analogue of `Lecture07.IsParallelGlobalAlong`, using
the explicit realized pullback derivative relation already available in the
Lecture 7 geodesic layer. -/
def IsParallelAlong
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Lecture07.Curve M)
    (V : Lecture07.VectorFieldAlong I gamma) : Prop :=
  Lecture07.IsAlongCovDeriv (I := I) cov gamma V
    (Lecture07.zeroAlong I gamma)

/-- A parallel orthonormal frame along a curve, perpendicular to the velocity.

The index type is arbitrary and finite; Myers later uses a type with cardinality
`n - 1`.  The orthonormal and perpendicular conditions are recorded on the
closed time interval used by the index-form comparison, while parallelism is
kept as the current global along-field derivative relation. -/
def IsParallelONFrameAlong
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Lecture07.Curve M)
    (frame : ι -> Lecture07.VectorFieldAlong I gamma)
    (a b : Real) : Prop :=
  (∀ i : ι, IsParallelAlong (I := I) cov gamma (frame i)) ∧
    (∀ t ∈ Set.uIcc a b, ∀ i j : ι,
      g.inner (gamma t) (frame i t) (frame j t) =
        if i = j then 1 else 0) ∧
      (∀ t ∈ Set.uIcc a b, ∀ i : ι,
        g.inner (gamma t) (frame i t)
          (Lecture07.velocityAlong I gamma t) = 0)

end GlobalGeometry
end RicciFlower
