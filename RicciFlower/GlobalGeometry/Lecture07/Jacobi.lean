import RicciFlower.GlobalGeometry.Lecture07.InitialValue
import RicciFlower.Curvature.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: Jacobi field interface

This file records the first realized Jacobi-field predicate.  It uses the
global-extension along-derivative layer from `Geodesics.lean`; it does not yet
construct Jacobi fields from geodesic variations, nor does it define a pullback
connection on `gamma^* TM`.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Curvature term along a geodesic -/

/-- The curvature term `R(J, gamma') gamma'` along a curve, using global
representatives for both `gamma'` and `J`.

The slot order follows `connectionRiemannCurvatureField cov X Y Z = R(X,Y)Z`.
The Jacobi equation below is written as
`D_t^2 J + R(J, gamma') gamma' = 0`. -/
def jacobiCurvatureTerm
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {gamma : Curve M} (X J : GlobalVectorField I M) :
    VectorFieldAlong I gamma :=
  fun t =>
    RicciFlower.Curvature.connectionRiemannCurvatureField (I := I) cov J X X (gamma t)

@[simp] theorem jacobiCurvatureTerm_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {gamma : Curve M} (X J : GlobalVectorField I M) (t : Real) :
    jacobiCurvatureTerm (I := I) cov (gamma := gamma) X J t =
      RicciFlower.Curvature.connectionRiemannCurvatureField (I := I) cov J X X (gamma t) :=
  rfl

/-! ## Jacobi field predicates -/

/-- A Jacobi field along `gamma`, relative to a chosen global velocity
extension `X`.

The equation is relation-valued:
* `X` realizes `gamma'` and is parallel along `gamma`;
* `Jsec` realizes the along-field `J`;
* `A` is a realized second covariant derivative of `J`;
* `A = - R(J, gamma') gamma'`.

This avoids pretending that arbitrary along-fields already have a canonical
pullback covariant derivative. -/
def IsJacobiFieldViaExtension
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (X : GlobalVectorField I M)
    (J : VectorFieldAlong I gamma) : Prop :=
  RealizesVelocity (I := I) gamma X /\
    IsParallelGlobalAlong (I := I) cov gamma X /\
      exists (Jsec : GlobalVectorField I M) (A : VectorFieldAlong I gamma),
        RealizesAlong (I := I) gamma Jsec J /\
          IsSecondAlongCovDeriv (I := I) cov gamma J A /\
            A = fun t =>
              -jacobiCurvatureTerm (I := I) cov (gamma := gamma) X Jsec t

@[simp] theorem isJacobiFieldViaExtension_iff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (X : GlobalVectorField I M)
    (J : VectorFieldAlong I gamma) :
    IsJacobiFieldViaExtension (I := I) cov gamma X J <->
      RealizesVelocity (I := I) gamma X /\
        IsParallelGlobalAlong (I := I) cov gamma X /\
          exists (Jsec : GlobalVectorField I M) (A : VectorFieldAlong I gamma),
            RealizesAlong (I := I) gamma Jsec J /\
              IsSecondAlongCovDeriv (I := I) cov gamma J A /\
                A = fun t =>
                  -jacobiCurvatureTerm (I := I) cov (gamma := gamma) X Jsec t :=
  Iff.rfl

/-- A Jacobi field along a curve, with the geodesic velocity extension included
as a witness. -/
def IsJacobiField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (J : VectorFieldAlong I gamma) : Prop :=
  exists X : GlobalVectorField I M,
    IsJacobiFieldViaExtension (I := I) cov gamma X J

@[simp] theorem isJacobiField_iff_exists_velocity_extension
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (J : VectorFieldAlong I gamma) :
    IsJacobiField (I := I) cov gamma J <->
      exists X : GlobalVectorField I M,
        IsJacobiFieldViaExtension (I := I) cov gamma X J :=
  Iff.rfl

end Lecture07
end GlobalGeometry
end RicciFlower

