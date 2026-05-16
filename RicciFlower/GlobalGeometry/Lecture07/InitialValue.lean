import RicciFlower.GlobalGeometry.Lecture07.Geodesics

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: geodesic initial values

This file adds the initial-value layer needed before exponential-map and normal
coordinate statements.  It is relation-valued on purpose: we do not define an
exponential map as a function until geodesic existence, uniqueness, and smooth
dependence on initial velocity are available.
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

/-! ## Initial velocity -/

/-- The velocity of a curve, packaged as a point of the tangent bundle. -/
def curveVelocityBundle (I : ModelWithCorners Real E H) (gamma : Curve M) (t : Real) :
    TangentBundle I M :=
  ⟨gamma t, curveVelocity I gamma t⟩

/-- The zero tangent vector at `x`, as a tangent-bundle point. -/
def zeroInitialVelocity (I : ModelWithCorners Real E H) (x : M) :
    TangentBundle I M :=
  ⟨x, 0⟩

@[simp] theorem curveVelocityBundle_const (x : M) (t : Real) :
    curveVelocityBundle I (fun _ : Real => x) t = zeroInitialVelocity I x := by
  simp [curveVelocityBundle, zeroInitialVelocity]

/-- A curve has initial velocity `u` at time `0`. -/
def HasInitialVelocity (gamma : Curve M) (u : TangentBundle I M) : Prop :=
  curveVelocityBundle I gamma 0 = u

@[simp] theorem hasInitialVelocity_iff (gamma : Curve M) (u : TangentBundle I M) :
    HasInitialVelocity (I := I) gamma u <->
      curveVelocityBundle I gamma 0 = u :=
  Iff.rfl

/-! ## Geodesic initial-value data -/

/-- A geodesic solving the initial-value problem with initial tangent vector
`u`.  This bundles the current realized geodesic predicate; later geodesic
spray work should produce such data from ODE existence. -/
structure GeodesicIVP
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (u : TangentBundle I M) where
  gamma : Curve M
  is_geodesic : IsGeodesic (I := I) cov gamma
  initial_velocity : HasInitialVelocity (I := I) gamma u

section VectorBundleLemmas

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- The constant curve is the geodesic initial-value solution for the zero
initial velocity at its base point. -/
def constantGeodesicIVP
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    GeodesicIVP (I := I) cov (zeroInitialVelocity I x) where
  gamma := fun _ : Real => x
  is_geodesic := isGeodesic_const (I := I) cov x
  initial_velocity := by
    simp [HasInitialVelocity]

@[simp] theorem constantGeodesicIVP_gamma_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) (t : Real) :
    (constantGeodesicIVP (I := I) cov x).gamma t = x :=
  rfl

end VectorBundleLemmas

/-! ## Exponential-map endpoint relation -/

/-- Relation-level endpoint of a geodesic with initial tangent vector `u`.

This is the safe precursor to an exponential map.  It says that some geodesic
solving the initial-value problem for `u` reaches `y` at time `t`; it does not
assert existence or uniqueness for arbitrary `u`. -/
def ExpEndpointAtTime
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (u : TangentBundle I M) (t : Real) (y : M) : Prop :=
  exists G : GeodesicIVP (I := I) cov u, G.gamma t = y

section VectorBundleLemmas

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- The zero initial velocity endpoint relation is realized by the constant
geodesic, at every time. -/
theorem expEndpointAtTime_zeroInitialVelocity
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) (t : Real) :
    ExpEndpointAtTime (I := I) cov (zeroInitialVelocity I x) t x :=
  ⟨constantGeodesicIVP (I := I) cov x, rfl⟩

end VectorBundleLemmas

end Lecture07
end GlobalGeometry
end RicciFlower

