import RicciFlower.Metric.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: geodesics

This file starts the side-project formalization of GSM245, Lecture 7,
Section 7.3, "Geodesics".  The goal here is to expose the small interface
needed before first variation, Jacobi fields, Hopf-Rinow, and Myers.

The mathematically intended route is:

* a curve `gamma : Real -> M` has velocity `mfderiv% gamma t 1`;
* a vector field along `gamma` is a dependent function
  `t : Real -> T_{gamma t} M`;
* a global vector field `X` differentiates along `gamma` by
  `t ↦ (cov X (gamma t)) (gamma'(t))`;
* a geodesic is a curve whose velocity is realized by a global vector field
  whose covariant derivative along the curve vanishes.

This is still the first realizable layer, not the full pullback connection on
arbitrary vector fields along a curve.  The remaining local frontier is to
replace the global velocity-extension hypothesis by a local-extension or
pullback-bundle construction.
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

/-! ## Curves and vector fields along curves -/

/-- A time-parametrized curve in a manifold. -/
abbrev Curve (M : Type*) := Real -> M

/-- The velocity vector of a curve at time `t`, following mathlib's
`pathELength` convention. -/
def curveVelocity (I : ModelWithCorners Real E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (gamma : Curve M) (t : Real) :
    TangentSpace I (gamma t) :=
  mfderiv% gamma t 1

/-- A vector field along a curve `gamma`. -/
abbrev VectorFieldAlong (I : ModelWithCorners Real E H) (gamma : Curve M) :=
  (t : Real) -> TangentSpace I (gamma t)

/-- A global vector field on `M`. -/
abbrev GlobalVectorField (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :=
  (p : M) -> TangentSpace I p

/-- The zero vector field along a curve. -/
def zeroAlong (I : ModelWithCorners Real E H) (gamma : Curve M) :
    VectorFieldAlong I gamma :=
  fun _t => 0

/-- The velocity field along a curve. -/
def velocityAlong (I : ModelWithCorners Real E H) (gamma : Curve M) :
    VectorFieldAlong I gamma :=
  fun t => curveVelocity I gamma t

@[simp] theorem velocityAlong_apply (gamma : Curve M) (t : Real) :
    velocityAlong I gamma t = curveVelocity I gamma t :=
  rfl

@[simp] theorem zeroAlong_apply (gamma : Curve M) (t : Real) :
    zeroAlong I gamma t = 0 :=
  rfl

@[simp] theorem curveVelocity_const (x : M) (t : Real) :
    curveVelocity I (fun _ : Real => x) t = 0 := by
  simp [curveVelocity]

/-! ## Realized covariant derivative along a curve -/

/-- Covariant derivative of a global vector field along a curve:
`(∇_{gamma'} X)(t) = (cov X (gamma t)) (gamma'(t))`. -/
def alongCovDeriv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (X : GlobalVectorField I M) :
    VectorFieldAlong I gamma :=
  fun t => (cov X (gamma t)) (curveVelocity I gamma t)

@[simp] theorem alongCovDeriv_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (X : GlobalVectorField I M) (t : Real) :
    alongCovDeriv (I := I) cov gamma X t =
      (cov X (gamma t)) (curveVelocity I gamma t) :=
  rfl

/-! ## Locality of extensions -/

section ExtensionLocality

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- The realized covariant derivative along a curve is independent of the
chosen smooth global extension, as long as the two extensions agree on a
neighborhood of the base point `gamma t`.

This is the first local-extension bridge for Lecture 7.3.  It deliberately
uses agreement near `gamma t` in the manifold, not merely agreement along the
image of the curve.  The latter is the future pullback-connection frontier. -/
theorem alongCovDeriv_eq_of_eventuallyEq
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {X Y : GlobalVectorField I M} {t : Real}
    (hX : MDiffAt (T% X) (gamma t))
    (hY : MDiffAt (T% Y) (gamma t))
    (hXY : ∀ᶠ p in 𝓝 (gamma t), X p = Y p) :
    alongCovDeriv (I := I) cov gamma X t =
      alongCovDeriv (I := I) cov gamma Y t := by
  have hcov :
      cov X (gamma t) = cov Y (gamma t) :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (x := gamma t) hX hY (by simp) hXY
  change (cov X (gamma t)) (curveVelocity I gamma t) =
    (cov Y (gamma t)) (curveVelocity I gamma t)
  rw [hcov]

end ExtensionLocality

/-- A global vector field realizes a vector field along a curve if it restricts
to that along-field on the image of the curve. -/
def RealizesAlong (gamma : Curve M) (X : GlobalVectorField I M)
    (V : VectorFieldAlong I gamma) : Prop :=
  forall t : Real, X (gamma t) = V t

/-! ## Realized along-curve derivatives -/

/-- A relation saying that `W` is a realized covariant derivative of the
along-field `V` along `gamma`.

The witness is a global vector field `X` that realizes `V` on the curve.  This
keeps the current global-extension hypothesis explicit; it is not yet the
intrinsic pullback-bundle derivative of an arbitrary along-field. -/
def IsAlongCovDeriv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (V W : VectorFieldAlong I gamma) : Prop :=
  exists X : GlobalVectorField I M,
    RealizesAlong (I := I) gamma X V /\
      alongCovDeriv (I := I) cov gamma X = W

@[simp] theorem isAlongCovDeriv_iff_exists_global_extension
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (V W : VectorFieldAlong I gamma) :
    IsAlongCovDeriv (I := I) cov gamma V W <->
      exists X : GlobalVectorField I M,
        RealizesAlong (I := I) gamma X V /\
          alongCovDeriv (I := I) cov gamma X = W :=
  Iff.rfl

/-- A relation saying that `A` is a realized second covariant derivative of the
along-field `V` along `gamma`.

This is intentionally relation-valued.  Without a pullback connection or a
stronger local representative theory, the intermediate derivative is part of
the data rather than a definitional value. -/
def IsSecondAlongCovDeriv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (V A : VectorFieldAlong I gamma) : Prop :=
  exists W : VectorFieldAlong I gamma,
    IsAlongCovDeriv (I := I) cov gamma V W /\
      IsAlongCovDeriv (I := I) cov gamma W A

@[simp] theorem isSecondAlongCovDeriv_iff_exists_intermediate
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (V A : VectorFieldAlong I gamma) :
    IsSecondAlongCovDeriv (I := I) cov gamma V A <->
      exists W : VectorFieldAlong I gamma,
        IsAlongCovDeriv (I := I) cov gamma V W /\
          IsAlongCovDeriv (I := I) cov gamma W A :=
  Iff.rfl

/-- A global vector field is parallel along a curve if its realized covariant
derivative along that curve vanishes. -/
def IsParallelGlobalAlong
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (X : GlobalVectorField I M) : Prop :=
  alongCovDeriv (I := I) cov gamma X = zeroAlong I gamma

@[simp] theorem isParallelGlobalAlong_iff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (X : GlobalVectorField I M) :
    IsParallelGlobalAlong (I := I) cov gamma X <->
      alongCovDeriv (I := I) cov gamma X = zeroAlong I gamma :=
  Iff.rfl

/-- Pointwise form of parallelism for a global field along a curve. -/
theorem IsParallelGlobalAlong.eq_zero
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {X : GlobalVectorField I M}
    (h : IsParallelGlobalAlong (I := I) cov gamma X) (t : Real) :
    (cov X (gamma t)) (curveVelocity I gamma t) = 0 := by
  exact congrFun h t

section VectorBundleLemmas

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

@[simp] theorem zero_global_parallel_along
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) :
    IsParallelGlobalAlong (I := I) cov gamma (fun _p : M => 0) := by
  funext t
  change (cov (0 : (p : M) -> TangentSpace I p) (gamma t))
      (curveVelocity I gamma t) = 0
  rw [CovariantDerivative.zero cov]
  rfl

end VectorBundleLemmas

/-! ## Geodesics -/

/-- The velocity field of `gamma` is realized by a global vector field. -/
def RealizesVelocity (gamma : Curve M) (X : GlobalVectorField I M) : Prop :=
  RealizesAlong (I := I) gamma X (velocityAlong I gamma)

/-- Realized geodesic predicate: the curve has a global velocity extension
whose covariant derivative along the curve is zero.

This is the first concrete connection-based version of
`∇_{gamma'} gamma' = 0`.  A later pullback-connection layer should remove the
global-extension witness from the public statement.
-/
def IsGeodesic
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) : Prop :=
  exists X : GlobalVectorField I M,
    RealizesVelocity (I := I) gamma X /\
      IsParallelGlobalAlong (I := I) cov gamma X

@[simp] theorem isGeodesic_iff_exists_velocity_extension
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) :
    IsGeodesic (I := I) cov gamma <->
      exists X : GlobalVectorField I M,
        RealizesVelocity (I := I) gamma X /\
          IsParallelGlobalAlong (I := I) cov gamma X :=
  Iff.rfl

/-- Bundled geodesic data for one connection. -/
structure Geodesic
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) where
  gamma : Curve M
  velocityExtension : GlobalVectorField I M
  realizes_velocity : RealizesVelocity (I := I) gamma velocityExtension
  velocity_parallel : IsParallelGlobalAlong (I := I) cov gamma velocityExtension

theorem Geodesic.isGeodesic
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (G : Geodesic (I := I) cov) :
    IsGeodesic (I := I) cov G.gamma :=
  ⟨G.velocityExtension, G.realizes_velocity, G.velocity_parallel⟩

section VectorBundleLemmas

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- Constant curves are geodesics for every connection. -/
theorem isGeodesic_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    IsGeodesic (I := I) cov (fun _ : Real => x) := by
  refine ⟨fun _p : M => 0, ?_, ?_⟩
  · intro t
    simp [velocityAlong]
  · exact zero_global_parallel_along (I := I) cov (fun _ : Real => x)

end VectorBundleLemmas

/-! ## Speed predicates used later by first variation -/

/-- Squared speed of a curve with respect to a RicciFlower smooth Riemannian
metric.  This keeps the sign convention and metric object local to RicciFlower. -/
def speedSq (g : SmoothRiemannianMetric I M) (gamma : Curve M) (t : Real) :
    Real :=
  g.inner (gamma t) (curveVelocity I gamma t) (curveVelocity I gamma t)

/-- Constant-speed curve, stated with squared speed to avoid square roots. -/
def IsConstantSpeed (g : SmoothRiemannianMetric I M) (gamma : Curve M) :
    Prop :=
  exists c : Real, forall t : Real, speedSq (I := I) g gamma t = c

/-- Unit-speed curve, stated with squared speed. -/
def IsUnitSpeed (g : SmoothRiemannianMetric I M) (gamma : Curve M) : Prop :=
  forall t : Real, speedSq (I := I) g gamma t = 1

/-!
Future theorem frontiers for this section:

* replace the global velocity extension in `IsGeodesic` by a local-extension or
  pullback-bundle construction;
* specialize that construction to `LeviCivita.leviCivitaConnectionOfMetric g`;
* prove that affine lines in the model vector space are geodesics for the
  standard flat connection;
* add the coordinate geodesic equation
  `d^2 gamma^k/dt^2 + Gamma^k_ij(gamma) gamma'^i gamma'^j = 0`;
* postpone minimal geodesics to first variation, since Lecture 7 introduces
  that after Section 7.3.
-/

end Lecture07
end GlobalGeometry
end RicciFlower
