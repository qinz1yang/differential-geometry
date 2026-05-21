import RicciFlower.Realized.CurvatureComponents

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci Identity Bridge for Realized Connections

This file exposes the RicciFlower-facing one-form Ricci identity through the
project's realized tensor predicates.  The proof route stays inside
`RicciFlower`; do not import the external geometry namespace here.
-/

noncomputable section

namespace RicciFlower
namespace Connection

open Tensor0SBundle
open Realized
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [Module.Finite Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Raw dual-connection evaluation used by the algebraic one-form Ricci
identity.

This is the RicciFlower-local algebraic replacement for the external
`nabla_dual` calculation: no smooth-section or synthetic realization API is
involved here. -/
def nablaDualEval {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (act : V -> R -> R) (conn : V -> V -> V)
    (X : V) (alpha : V -> R) (Y : V) : R :=
  act X (alpha Y) - alpha (conn X Y)

/-- Raw curvature expression for a connection and bracket. -/
def connectionRmRaw {V : Type*} [Sub V]
    (bracket : V -> V -> V) (conn : V -> V -> V)
    (X Y Z : V) : V :=
  conn X (conn Y Z) - conn Y (conn X Z) - conn (bracket X Y) Z

/-- Algebraic one-form Ricci identity in bracket form.

This is the small calculation previously borrowed from the external
external geometry namespace.  It only uses the commutator rule for the
action and linearity of the one-form. -/
theorem oneFormRicciIdentity_algebra
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (act : V -> R -> R) (bracket : V -> V -> V) (conn : V -> V -> V)
    (hact_sub : ∀ X f g, act X (f - g) = act X f - act X g)
    (hact_bracket : ∀ X Y f,
      act (bracket X Y) f = act X (act Y f) - act Y (act X f))
    (X Y Z : V) (alpha : V →ₗ[R] R) :
    nablaDualEval act conn X
        (fun W => nablaDualEval act conn Y (fun U => alpha U) W) Z -
      nablaDualEval act conn Y
        (fun W => nablaDualEval act conn X (fun U => alpha U) W) Z -
      nablaDualEval act conn (bracket X Y) (fun U => alpha U) Z =
        -alpha (connectionRmRaw bracket conn X Y Z) := by
  unfold nablaDualEval connectionRmRaw
  rw [hact_sub X (act Y (alpha Z)) (alpha (conn Y Z))]
  rw [hact_sub Y (act X (alpha Z)) (alpha (conn X Z))]
  rw [hact_bracket]
  simp only [map_sub]
  abel

/-- Connection-generic one-form Ricci identity in RicciFlower's public tensor
interface.

The proof currently routes through the coordinate Christoffel curvature layer:
`hcoord` is the local coordinate calculation for the one-form commutator, while
`hcurv` identifies the coordinate curvature coefficients with the realized
connection curvature.  This theorem is deliberately independent of any
primitive metric-Christoffel or upstream `LeviCivita g` definition. -/
theorem oneFormRicciIdentity_of_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  one_form_third_comm_coord_of_christoffelCurv (I := I) cov hcov Rm13 x alpha
    nabla2Alpha hRm hcurv hcoord

/-- Smooth-connection version of `oneFormRicciIdentity_of_connection`.

The coordinate curvature hypothesis is now produced in the general
connection-curvature layer.  The one-form coordinate commutator is intentionally
left explicit until the higher-order covariant-derivative API is settled. -/
theorem oneFormRicciIdentity_of_smooth_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov_one : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  oneFormRicciIdentity_of_connection (I := I) cov Rm13 x alpha nabla2Alpha
    hRm hcov_one (connection_curvature_coord_of_christoffel (I := I) cov hcov x) hcoord

/-- Evaluation form of `oneFormRicciIdentity_of_connection`. -/
theorem oneFormRicciIdentity_of_connection_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  one_form_third_covDeriv_comm (I := I) Rm13 alpha nabla2Alpha
    (oneFormRicciIdentity_of_connection (I := I) cov Rm13 x alpha nabla2Alpha
      hRm hcov hcurv hcoord) X Y Z

/-- Evaluation form of `oneFormRicciIdentity_of_smooth_connection`. -/
theorem oneFormRicciIdentity_of_smooth_connection_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov_one : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  one_form_third_covDeriv_comm (I := I) Rm13 alpha nabla2Alpha
    (oneFormRicciIdentity_of_smooth_connection (I := I) cov Rm13 x alpha
      nabla2Alpha hRm hcov hcov_one hcoord) X Y Z

end Connection
end RicciFlower
