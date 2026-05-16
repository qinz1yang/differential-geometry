import RicciFlower.GlobalGeometry.Lecture07.PullbackConnection
import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.CoordinateFrame
import RicciFlower.VectorBundle.LocalFrameRegularity
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: coordinate geodesic equations

This file adds a general-coordinate layer for geodesics.

The invariant object in this file is not tied to one fixed chart.  A
`CoordinateChartData` packages a coordinate-induced local frame on an open
domain, and `HasCoordinateGeodesicEquationAt` says that all coordinate
components of the covariant acceleration vanish.  This is immediately
equivalent to the intrinsic pointwise equation, hence independent of the
coordinate package.

The usual second-order ODE formula

`d v^k / dt + Gamma^k_ij v^i v^j = 0`

is defined as `HasCoordinateGeodesicODEAt`.  It deliberately includes the
covariant-acceleration relation and the scalar component formula, so the ODE
statement is the scalar expression of an actual geometric acceleration rather
than a standalone second-derivative assertion.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle Filter
open scoped BigOperators Manifold ContDiff Topology
open RicciFlower.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- A coordinate-induced local frame on an open domain.

This is deliberately a frame package, not a raw atlas chart.  The intended
instances are coordinate frames, such as `coordinateFrameAt`, and the
`bracket_zero` field records the coordinate-frame property needed by later ODE
and torsion calculations. -/
structure CoordinateChartData where
  domain : Set M
  frame : CoordinateIdx (𝕜 := Real) E -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E 1 frame domain
  isOpen_domain : IsOpen domain
  bracket_zero : ∀ ⦃x : M⦄, x ∈ domain ->
    ∀ i j : CoordinateIdx (𝕜 := Real) E,
      VectorField.mlieBracket I (frame i) (frame j) x = 0

namespace CoordinateChartData

/-- Coefficient of a tangent vector in the coordinate frame. -/
def coeff (C : CoordinateChartData (I := I) (M := M))
    (i : CoordinateIdx (𝕜 := Real) E) {x : M}
    (v : TangentSpace I x) : Real :=
  C.hframe.coeff i x v

@[simp] theorem coeff_apply (C : CoordinateChartData (I := I) (M := M))
    (i : CoordinateIdx (𝕜 := Real) E) {x : M} (v : TangentSpace I x) :
    C.coeff i v = C.hframe.coeff i x v := rfl

/-- Velocity component of a curve in this coordinate frame. -/
def velocityCoeff (C : CoordinateChartData (I := I) (M := M))
    (gamma : Curve M) (i : CoordinateIdx (𝕜 := Real) E) (t : Real) : Real :=
  C.coeff i (curveVelocity I gamma t)

/-- Christoffel coefficient in this coordinate frame. -/
def christoffel (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) (i j k : CoordinateIdx (𝕜 := Real) E) : Real :=
  christoffelSymbolInFrame cov C.frame C.hframe x i j k

@[simp] theorem christoffel_apply (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    C.christoffel cov x i j k =
      christoffelSymbolInFrame cov C.frame C.hframe x i j k := rfl

/-- The quadratic Christoffel term `Gamma^k_ij v^i v^j` along a curve. -/
def christoffelVelocityQuadratic (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) (k : CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ i : CoordinateIdx (𝕜 := Real) E,
    ∑ j : CoordinateIdx (𝕜 := Real) E,
      C.christoffel cov (gamma t) i j k *
        C.velocityCoeff gamma i t * C.velocityCoeff gamma j t

end CoordinateChartData

/-- Expand the first tangent slot of a Christoffel term in coordinate-frame
components. -/
theorem christoffelAlong_eq_sum_coeff
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M} (hx : x ∈ C.domain) (v : TangentSpace I x)
    (j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelAlongInFrame cov C.frame C.hframe x v j k =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        C.coeff i v * C.christoffel cov x i j k := by
  classical
  let b := C.hframe.toBasisAt hx
  have hv : v = ∑ i : CoordinateIdx (𝕜 := Real) E, C.coeff i v • C.frame i x := by
    simpa [b, CoordinateChartData.coeff, IsLocalFrameOn.coeff, hx] using
      (b.sum_repr v).symm
  conv_lhs => rw [hv]
  simp [christoffelAlongInFrame, CoordinateChartData.christoffel,
    CoordinateChartData.coeff]

/-- The quadratic Christoffel term can be written using the arbitrary-direction
Christoffel coefficient `christoffelAlongInFrame` in the first slot. -/
theorem christoffelVelocityQuadratic_eq_sum_velocity_christoffelAlong
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) {t : Real} (hgt : gamma t ∈ C.domain)
    (k : CoordinateIdx (𝕜 := Real) E) :
    C.christoffelVelocityQuadratic cov gamma t k =
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        C.velocityCoeff gamma j t *
          christoffelAlongInFrame cov C.frame C.hframe
            (gamma t) (curveVelocity I gamma t) j k := by
  classical
  calc
    C.christoffelVelocityQuadratic cov gamma t k
        = ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              C.christoffel cov (gamma t) i j k *
                C.velocityCoeff gamma i t * C.velocityCoeff gamma j t := rfl
    _ = ∑ j : CoordinateIdx (𝕜 := Real) E,
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            C.christoffel cov (gamma t) i j k *
              C.velocityCoeff gamma i t * C.velocityCoeff gamma j t := by
          rw [Finset.sum_comm]
    _ = ∑ j : CoordinateIdx (𝕜 := Real) E,
          C.velocityCoeff gamma j t *
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              C.velocityCoeff gamma i t * C.christoffel cov (gamma t) i j k := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    _ = ∑ j : CoordinateIdx (𝕜 := Real) E,
          C.velocityCoeff gamma j t *
            christoffelAlongInFrame cov C.frame C.hframe
              (gamma t) (curveVelocity I gamma t) j k := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [christoffelAlong_eq_sum_coeff (I := I) C cov hgt
            (curveVelocity I gamma t) j k]
          simp [CoordinateChartData.velocityCoeff]

/-- Relation-valued covariant acceleration of a curve at a time.

This is the legacy global-extension producer.  Public geodesic-equation
predicates below use `HasPullbackCovariantAccelerationAt`; this relation is
kept so existing velocity-extension proofs can produce pullback acceleration
witnesses. -/
def HasCovariantAccelerationAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) (A : TangentSpace I (gamma t)) : Prop :=
  ∃ X : GlobalVectorField I M,
    IsVelocityExtensionAt (I := I) gamma t X ∧
      A = (cov X (gamma t)) (curveVelocity I gamma t)

/-- Legacy global-extension acceleration produces the pullback-bundle
acceleration relation. -/
theorem HasCovariantAccelerationAt.toPullback
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {A : TangentSpace I (gamma t)}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hA : HasCovariantAccelerationAt (I := I) cov gamma t A) :
    HasPullbackCovariantAccelerationAt (I := I) cov gamma t A := by
  rcases hA with ⟨X, hX, hAeq⟩
  rw [hAeq]
  exact hasPullbackCovariantAccelerationAt_of_velocityExtensionAt
    (I := I) (cov := cov) (gamma := gamma) (X := X) (t := t) hgamma hX

/-- Pointwise intrinsic geodesic equation, still using the current
pullback-bundle acceleration relation.

This no longer exposes a global velocity extension in the public expression. -/
def HasIntrinsicGeodesicEquationAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) : Prop :=
  HasPullbackCovariantAccelerationAt (I := I) cov gamma t 0

/-- The invariant coordinate-component geodesic equation.

For a chosen coordinate frame, all coordinate components of the
extension-independent covariant acceleration vanish.  This is equivalent to the
intrinsic predicate below, so it is independent of the coordinate package on
whose domain `gamma t` lies. -/
def HasCoordinateGeodesicEquationAt
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) : Prop :=
  ∃ A : TangentSpace I (gamma t),
    HasPullbackCovariantAccelerationAt (I := I) cov gamma t A ∧
      ∀ k : CoordinateIdx (𝕜 := Real) E,
        C.coeff k A = 0

/-- Velocity coordinates at a time, relation-valued for later ODE work. -/
def HasCoordinateVelocityAt
    (C : CoordinateChartData (I := I) (M := M))
    (gamma : Curve M) (t : Real)
    (v : CoordinateIdx (𝕜 := Real) E -> Real) : Prop :=
  ∀ i : CoordinateIdx (𝕜 := Real) E,
    v i = C.velocityCoeff gamma i t

/-- Coordinate acceleration means derivative of the velocity-coordinate
functions.  This is the second-order ODE ingredient, not yet the intrinsic
covariant acceleration. -/
def HasCoordinateAccelerationAt
    (C : CoordinateChartData (I := I) (M := M))
    (gamma : Curve M) (t : Real)
    (a : CoordinateIdx (𝕜 := Real) E -> Real) : Prop :=
  ∀ k : CoordinateIdx (𝕜 := Real) E,
    HasDerivAt (fun s : Real => C.velocityCoeff gamma k s) (a k) t

/-- The Christoffel correction term for the covariant derivative of an
along-curve field `S`.

In coordinates this is `Γ^k_{ij}(γ(t)) γ'^i(t) S^j(t)`. -/
def CoordinateChartData.alongChristoffelTerm
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (S : VectorFieldAlong I gamma) (t : Real)
    (k : CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ i : CoordinateIdx (𝕜 := Real) E,
    ∑ j : CoordinateIdx (𝕜 := Real) E,
      C.christoffel cov (gamma t) i j k *
        C.velocityCoeff gamma i t * C.coeff j (S t)

/-- Coordinate derivative of an along-curve field: each component
`S^k(t)` has ordinary derivative `b^k`. -/
def HasCoordinateAlongDerivativeAt
    (C : CoordinateChartData (I := I) (M := M))
    (gamma : Curve M) (S : VectorFieldAlong I gamma) (t : Real)
    (b : CoordinateIdx (𝕜 := Real) E -> Real) : Prop :=
  ∀ k : CoordinateIdx (𝕜 := Real) E,
    HasDerivAt (fun s : Real => C.coeff k (S s)) (b k) t

/-- Coordinate-defined covariant derivative of an along-curve field.

This is the direct coordinate formula
`(∇_t S)^k = dS^k/dt + Γ^k_{ij} γ'^i S^j`.  It is a coordinate-level
predicate; invariance across coordinate systems is a later theorem. -/
def HasCoordinateAlongCovDerivAt
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (S : VectorFieldAlong I gamma) (t : Real)
    (A : TangentSpace I (gamma t)) : Prop :=
  ∃ b : CoordinateIdx (𝕜 := Real) E -> Real,
    HasCoordinateAlongDerivativeAt (I := I) C gamma S t b ∧
      ∀ k : CoordinateIdx (𝕜 := Real) E,
        C.coeff k A =
          b k + C.alongChristoffelTerm cov gamma S t k

/-- Coordinate-defined pullback acceleration of a curve.  This is the
coordinate along-covariant derivative of the velocity field along the curve. -/
def HasCoordinatePullbackAccelerationAt
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) (A : TangentSpace I (gamma t)) : Prop :=
  HasCoordinateAlongCovDerivAt (I := I) C cov gamma
    (velocityAlong I gamma) t A

/-- For the velocity along the curve, the along-field Christoffel term is the
usual quadratic Christoffel term. -/
theorem alongChristoffelTerm_velocity_eq_christoffelVelocityQuadratic
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real)
    (k : CoordinateIdx (𝕜 := Real) E) :
    C.alongChristoffelTerm cov gamma (velocityAlong I gamma) t k =
      C.christoffelVelocityQuadratic cov gamma t k := by
  simp [CoordinateChartData.alongChristoffelTerm,
    CoordinateChartData.christoffelVelocityQuadratic,
    CoordinateChartData.velocityCoeff, velocityAlong]

/-- Coordinate derivatives of the velocity along the curve are exactly the
coordinate accelerations already used by the scalar geodesic ODE layer. -/
theorem hasCoordinateAlongDerivativeAt_velocity_iff_accelerationAt
    (C : CoordinateChartData (I := I) (M := M))
    (gamma : Curve M) (t : Real)
    (a : CoordinateIdx (𝕜 := Real) E -> Real) :
    HasCoordinateAlongDerivativeAt (I := I) C gamma
        (velocityAlong I gamma) t a ↔
      HasCoordinateAccelerationAt (I := I) C gamma t a := by
  simp [HasCoordinateAlongDerivativeAt, HasCoordinateAccelerationAt,
    CoordinateChartData.velocityCoeff, velocityAlong]

/-- Chain rule for scalar exterior derivatives along a real curve.

This is the bridge from `extDerivFun f (gamma t) gamma'(t)` to the ordinary
time derivative of the scalar function `f ∘ gamma`. -/
theorem extDerivFun_along_curve_eq_deriv
    {f : M -> Real} {gamma : Curve M} {t : Real}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f (gamma t))
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t) :
    HasDerivAt (fun s : Real => f (gamma s))
      (extDerivFun (I := I) f (gamma t) (curveVelocity I gamma t)) t := by
  have hcomp :
      HasMFDerivAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun s : Real => f (gamma s)) t
        ((mfderiv I 𝓘(Real, Real) f (gamma t)).comp
          (mfderiv 𝓘(Real, Real) I gamma t)) := by
    simpa [Function.comp_def] using
      (hf.hasMFDerivAt.comp t hgamma.hasMFDerivAt)
  have hderiv := hcomp.hasFDerivAt.hasDerivAt
  simpa [curveVelocity, extDerivFun, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply, Function.comp_def] using hderiv

/-- The component formula identifying the geometric covariant acceleration
with the usual scalar acceleration plus the Christoffel quadratic term. -/
def HasCoordinateAccelerationFormulaAt
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) (A : TangentSpace I (gamma t)) : Prop :=
  HasPullbackCovariantAccelerationAt (I := I) cov gamma t A ∧
    ∃ a : CoordinateIdx (𝕜 := Real) E -> Real,
      HasCoordinateAccelerationAt (I := I) C gamma t a ∧
        ∀ k : CoordinateIdx (𝕜 := Real) E,
          C.coeff k A =
            a k + C.christoffelVelocityQuadratic cov gamma t k

/-- The usual coordinate ODE form of the geodesic equation.

This is intentionally not a pure scalar predicate: it carries a geometric
covariant acceleration `A` and the scalar formula relating `A` to the coordinate
velocity derivatives. -/
def HasCoordinateGeodesicODEAt
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) : Prop :=
  ∃ A : TangentSpace I (gamma t),
    ∃ a : CoordinateIdx (𝕜 := Real) E -> Real,
      HasPullbackCovariantAccelerationAt (I := I) cov gamma t A ∧
        HasCoordinateAccelerationAt (I := I) C gamma t a ∧
          (∀ k : CoordinateIdx (𝕜 := Real) E,
            C.coeff k A =
              a k + C.christoffelVelocityQuadratic cov gamma t k) ∧
      ∀ k : CoordinateIdx (𝕜 := Real) E,
        a k + C.christoffelVelocityQuadratic cov gamma t k = 0

/-- If every coordinate coefficient of a tangent vector is zero, then the
vector is zero. -/
theorem coeff_zero_iff
    (C : CoordinateChartData (I := I) (M := M))
    {x : M} (hx : x ∈ C.domain) {v : TangentSpace I x} :
    (∀ k : CoordinateIdx (𝕜 := Real) E, C.coeff k v = 0) ↔ v = 0 := by
  constructor
  · intro h
    let b := C.hframe.toBasisAt hx
    apply b.ext_elem
    intro k
    have hk : b.repr v k = 0 := by
      simpa [CoordinateChartData.coeff, IsLocalFrameOn.coeff, hx, b] using h k
    simp [hk]
  · intro hv k
    simp [hv, CoordinateChartData.coeff]

/-- Coordinate-component vanishing is equivalent to the intrinsic pointwise
geodesic equation. -/
theorem hasCoordinateGeodesicEquationAt_iff_intrinsic
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) (hgt : gamma t ∈ C.domain) :
    HasCoordinateGeodesicEquationAt (I := I) C cov gamma t ↔
      HasIntrinsicGeodesicEquationAt (I := I) cov gamma t := by
  constructor
  · rintro ⟨A, hA, hcoeff⟩
    have hA_zero : A = 0 := (coeff_zero_iff (I := I) C hgt).1 hcoeff
    simpa [HasIntrinsicGeodesicEquationAt, hA_zero] using hA
  · intro hzero
    refine ⟨0, hzero, ?_⟩
    intro k
    simp [CoordinateChartData.coeff]

/-- Any two coordinate packages give equivalent coordinate-component geodesic
equations at points where both packages are valid. -/
theorem hasCoordinateGeodesicEquationAt_iff_of_coordinates
    (C D : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real)
    (hC : gamma t ∈ C.domain) (hD : gamma t ∈ D.domain) :
    HasCoordinateGeodesicEquationAt (I := I) C cov gamma t ↔
      HasCoordinateGeodesicEquationAt (I := I) D cov gamma t := by
  rw [hasCoordinateGeodesicEquationAt_iff_intrinsic (I := I) C cov gamma t hC,
    hasCoordinateGeodesicEquationAt_iff_intrinsic (I := I) D cov gamma t hD]

/-- A smooth global velocity representative whose covariant derivative
vanishes along the curve gives the pointwise intrinsic geodesic equation.

The older `IsGeodesic` predicate does not store differentiability of its global
velocity extension, so the differentiability witness is explicit here. -/
theorem hasIntrinsicGeodesicEquationAt_of_velocityExtension
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {X : GlobalVectorField I M} {t : Real}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hvel : RealizesVelocity (I := I) gamma X)
    (hpar : IsParallelGlobalAlong (I := I) cov gamma X)
    (hX : MDiffAt (T% X) (gamma t)) :
    HasIntrinsicGeodesicEquationAt (I := I) cov gamma t := by
  have hacc :
      HasPullbackCovariantAccelerationAt (I := I) cov gamma t
        ((cov X (gamma t)) (curveVelocity I gamma t)) :=
    hasPullbackCovariantAccelerationAt_of_velocityExtensionAt
      (I := I) (cov := cov) (gamma := gamma) (X := X) (t := t) hgamma
      ⟨hX, Filter.Eventually.of_forall fun s => hvel s⟩
  have hzero : (cov X (gamma t)) (curveVelocity I gamma t) = 0 :=
    IsParallelGlobalAlong.eq_zero (I := I) hpar t
  simpa [HasIntrinsicGeodesicEquationAt, hzero] using hacc

/-- A smooth global velocity representative whose covariant derivative
vanishes along the curve satisfies every valid coordinate-component equation. -/
theorem hasCoordinateGeodesicEquationAt_of_velocityExtension
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {X : GlobalVectorField I M} {t : Real}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hvel : RealizesVelocity (I := I) gamma X)
    (hpar : IsParallelGlobalAlong (I := I) cov gamma X)
    (hX : MDiffAt (T% X) (gamma t))
    (C : CoordinateChartData (I := I) (M := M))
    (hgt : gamma t ∈ C.domain) :
    HasCoordinateGeodesicEquationAt (I := I) C cov gamma t := by
  exact (hasCoordinateGeodesicEquationAt_iff_intrinsic
    (I := I) C cov gamma t hgt).2
      (hasIntrinsicGeodesicEquationAt_of_velocityExtension
        (I := I) hgamma hvel hpar hX)

/-!
Once the local scalar component formula is available, the coordinate ODE and
the invariant coordinate-component geodesic equation are the same assertion.
The actual analytic work is therefore isolated in producing
`HasCoordinateAccelerationFormulaAt`.
-/
theorem hasCoordinateGeodesicODEAt_iff_geodesicEquationAt_of_formula
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real)
    (hformula : ∀ A : TangentSpace I (gamma t),
      HasPullbackCovariantAccelerationAt (I := I) cov gamma t A →
        HasCoordinateAccelerationFormulaAt (I := I) C cov gamma t A) :
    HasCoordinateGeodesicODEAt (I := I) C cov gamma t ↔
      HasCoordinateGeodesicEquationAt (I := I) C cov gamma t := by
  constructor
  · rintro ⟨A, a, hA, ha, hcoeff, hode⟩
    refine ⟨A, hA, ?_⟩
    intro k
    rw [hcoeff k, hode k]
  · rintro ⟨A, hA, hzero⟩
    rcases hformula A hA with ⟨hA', a, ha, hcoeff⟩
    refine ⟨A, a, hA', ha, hcoeff, ?_⟩
    intro k
    exact (hcoeff k).symm.trans (hzero k)

/-- The coordinate package coming from mathlib's `extChartAt` tangent
trivialization at `x0`. -/
def extChartAtCoordinateData (x0 : M) : CoordinateChartData (I := I) (M := M) where
  domain := coordinateFrameSet (I := I) x0
  frame := coordinateFrameAt (I := I) x0
  hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  isOpen_domain := coordinateFrameSet_open (I := I) x0
  bracket_zero := by
    intro x hx i j
    exact coordinateFrameAt_bracket_zero_of_mem (I := I) (x₀ := x0) (x := x) hx i j

@[simp] theorem extChartAtCoordinateData_domain (x0 : M) :
    (extChartAtCoordinateData (I := I) x0).domain =
      coordinateFrameSet (I := I) x0 := rfl

@[simp] theorem extChartAtCoordinateData_frame (x0 : M) :
    (extChartAtCoordinateData (I := I) x0).frame =
      coordinateFrameAt (I := I) x0 := rfl

/-- The `extChartAt` coordinate package is valid at its base point. -/
theorem extChartAtCoordinateData_mem (x0 : M) :
    x0 ∈ (extChartAtCoordinateData (I := I) x0).domain := by
  exact coordinateFrameAt_mem (I := I) x0

/-- A smooth velocity extension supplies the ordinary derivative of each
coordinate velocity component in the `extChartAt` coordinate package. -/
theorem coordinateAcceleration_of_velocityExtension_extChartAt
    {gamma : Curve M} {t : Real} {X : GlobalVectorField I M}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hX : IsVelocityExtensionAt (I := I) gamma t X) :
    HasCoordinateAccelerationAt (I := I)
      (extChartAtCoordinateData (I := I) (gamma t)) gamma t
      (fun k : CoordinateIdx (𝕜 := Real) E =>
        extDerivFun (I := I)
          (fun p : M =>
            (extChartAtCoordinateData (I := I) (gamma t)).coeff k (X p))
          (gamma t) (curveVelocity I gamma t)) := by
  intro k
  let C : CoordinateChartData (I := I) (M := M) :=
    extChartAtCoordinateData (I := I) (gamma t)
  let f : M -> Real := fun p => C.coeff k (X p)
  have hx :
      gamma t ∈ (coordinateTrivializationAt (I := I) (gamma t)).baseSet := by
    exact coordinateFrameAt_mem (I := I) (gamma t)
  have hf : MDifferentiableAt I 𝓘(Real, Real) f (gamma t) := by
    simpa [f, C, CoordinateChartData.coeff, extChartAtCoordinateData,
      coordinateFrameAt, coordinateFrameSet, coordinateTrivializationAt] using
      (mdifferentiableAt_localFrame_coeff
        (I := I)
        (e := coordinateTrivializationAt (I := I) (gamma t))
        (b := Module.finBasis Real E)
        hx hX.1 k)
  have hderiv :
      HasDerivAt (fun s : Real => f (gamma s))
        (extDerivFun (I := I) f (gamma t) (curveVelocity I gamma t)) t :=
    extDerivFun_along_curve_eq_deriv (I := I) hf hgamma
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [hX.2] with s hs
  simp [f, C, CoordinateChartData.velocityCoeff, hs.symm]

/-- Component formula for one smooth velocity extension in the `extChartAt`
coordinate package centered at the point `gamma t`.

This is the remaining local-coordinate calculation for Step 1.  The intended
proof is:

* apply `covariantDerivative_localFrame_coeff_eq` in the coordinate
  trivialization at `gamma t`;
* expand the first tangent slot from the coordinate basis to `gamma'(t)`;
* use `extDerivFun_along_curve_eq_deriv` and the eventual velocity-extension
  equality to identify the ordinary derivative of velocity coefficients;
* rewrite the Christoffel contraction as
  `C.christoffelVelocityQuadratic cov gamma t k`. -/
theorem coordinateAccelerationFormula_of_velocityExtension_extChartAt
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {X : GlobalVectorField I M}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hX : IsVelocityExtensionAt (I := I) gamma t X) :
    ∃ a : CoordinateIdx (𝕜 := Real) E -> Real,
      HasCoordinateAccelerationAt (I := I)
        (extChartAtCoordinateData (I := I) (gamma t)) gamma t a ∧
        ∀ k : CoordinateIdx (𝕜 := Real) E,
          (extChartAtCoordinateData (I := I) (gamma t)).coeff k
              ((cov X (gamma t)) (curveVelocity I gamma t)) =
            a k +
              (extChartAtCoordinateData (I := I) (gamma t)).christoffelVelocityQuadratic
                cov gamma t k := by
  let C : CoordinateChartData (I := I) (M := M) :=
    extChartAtCoordinateData (I := I) (gamma t)
  let a : CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k =>
      extDerivFun (I := I) (fun p : M => C.coeff k (X p))
        (gamma t) (curveVelocity I gamma t)
  refine ⟨a, ?_, ?_⟩
  · simpa [a, C] using
      coordinateAcceleration_of_velocityExtension_extChartAt
        (I := I) (gamma := gamma) (t := t) (X := X) hgamma hX
  · intro k
    have hxC : gamma t ∈ C.domain := by
      simpa [C] using extChartAtCoordinateData_mem (I := I) (gamma t)
    let e := coordinateTrivializationAt (I := I) (gamma t)
    let b := Module.finBasis Real E
    have hxE :
        gamma t ∈ e.baseSet := by
      exact coordinateFrameAt_mem (I := I) (gamma t)
    have hcoeff_eq (l : CoordinateIdx (𝕜 := Real) E) :
        e.localFrame_coeff I b l (gamma t) = C.hframe.coeff l (gamma t) := by
      apply (C.hframe.toBasisAt hxC).ext
      intro i
      rw [C.hframe.toBasisAt_coe hxC i]
      have hleft :
          e.localFrame_coeff I b l (gamma t) (C.frame i (gamma t)) =
            (if i = l then 1 else 0) := by
        rw [show C.frame i (gamma t) = e.localFrame b i (gamma t) by
          simp [C, e, b, extChartAtCoordinateData, coordinateFrameAt,
            coordinateTrivializationAt]]
        rw [e.localFrame_coeff_apply_of_mem_baseSet b hxE (e.localFrame b i) l]
        rw [e.localFrame_apply_of_mem_baseSet (b := b) (i := i) hxE]
        rw [(e.basisAt b hxE).repr_self]
        simp [Finsupp.single_apply]
      have hright :
          C.hframe.coeff l (gamma t) (C.frame i (gamma t)) =
            (if i = l then 1 else 0) := by
        unfold IsLocalFrameOn.coeff
        rw [dif_pos hxC]
        rw [← C.hframe.toBasisAt_coe hxC i]
        rw [Module.Basis.coord_apply]
        rw [(C.hframe.toBasisAt hxC).repr_self]
        simp [Finsupp.single_apply]
      rw [hleft, hright]
    have hvel_at : X (gamma t) = curveVelocity I gamma t :=
      hX.2.self_of_nhds
    have hlocal :=
      covariantDerivative_localFrame_coeff_eq_along
        (I := I) cov e b hxE hX.1
        (curveVelocity I gamma t) k
    have hconn :
        C.coeff k ((cov X (gamma t)) (curveVelocity I gamma t)) =
          a k +
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              C.coeff j (X (gamma t)) *
                C.coeff k ((cov (C.frame j) (gamma t))
                  (curveVelocity I gamma t)) := by
      simpa [C, a, CoordinateChartData.coeff, extChartAtCoordinateData,
        coordinateFrameAt, coordinateFrameSet, coordinateTrivializationAt,
        e, b, hcoeff_eq] using hlocal
    have hsum :
        (∑ j : CoordinateIdx (𝕜 := Real) E,
            C.coeff j (X (gamma t)) *
              C.coeff k ((cov (C.frame j) (gamma t))
                (curveVelocity I gamma t))) =
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            C.velocityCoeff gamma j t *
              christoffelAlongInFrame cov C.frame C.hframe
                (gamma t) (curveVelocity I gamma t) j k := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hvel_at]
      simp [CoordinateChartData.velocityCoeff, CoordinateChartData.coeff,
        christoffelAlongInFrame]
    have hquad :=
      christoffelVelocityQuadratic_eq_sum_velocity_christoffelAlong
        (I := I) C cov gamma hxC k
    calc
      C.coeff k ((cov X (gamma t)) (curveVelocity I gamma t))
          = a k +
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                C.coeff j (X (gamma t)) *
                  C.coeff k ((cov (C.frame j) (gamma t))
                    (curveVelocity I gamma t)) := hconn
      _ = a k +
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                C.velocityCoeff gamma j t *
                  christoffelAlongInFrame cov C.frame C.hframe
                    (gamma t) (curveVelocity I gamma t) j k := by
            rw [hsum]
      _ = a k + C.christoffelVelocityQuadratic cov gamma t k := by
            rw [hquad]

/-- The scalar component formula for the extension-independent covariant
acceleration in the `extChartAt` coordinate package. -/
theorem hasCoordinateAccelerationFormulaAt_extChartAt
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {A : TangentSpace I (gamma t)}
    (hA : HasPullbackCovariantAccelerationAt (I := I) cov gamma t A) :
    HasCoordinateAccelerationFormulaAt (I := I)
      (extChartAtCoordinateData (I := I) (gamma t)) cov gamma t A := by
  rcases hA with ⟨hgamma, X, hXrep, hAeq⟩
  have hX : IsVelocityExtensionAt (I := I) gamma t X := by
    refine ⟨mdiffSectionAt_tPercent (I := I) (F := E)
      (V := TangentSpace I) hXrep.1, ?_⟩
    filter_upwards [hXrep.2] with s hs
    simpa [velocityAlong] using hs.symm
  rcases coordinateAccelerationFormula_of_velocityExtension_extChartAt
      (I := I) (cov := cov) (gamma := gamma) (t := t) (X := X)
      hgamma hX with
    ⟨a, ha, hcoeff⟩
  refine ⟨⟨hgamma, X, hXrep, hAeq⟩, a, ha, ?_⟩
  intro k
  have hAeq' : A = (cov X (gamma t)) (curveVelocity I gamma t) := by
    simpa [pullbackCovDerivOfRepresentativeAt, curveVelocity] using hAeq
  simpa [hAeq'] using hcoeff k

/-- The value of the covariant acceleration does not depend on the chosen
smooth local velocity extension.

This removes the raw extension `X` from the public geodesic ODE interface.  The
proof compares the `extChartAt` scalar component formula for two extensions and
uses uniqueness of ordinary derivatives of the same velocity-coordinate
function. -/
theorem covariantAcceleration_eq_of_velocityExtensions
    [CompleteSpace E]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {X Y : GlobalVectorField I M}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hX : IsVelocityExtensionAt (I := I) gamma t X)
    (hY : IsVelocityExtensionAt (I := I) gamma t Y) :
    (cov X (gamma t)) (curveVelocity I gamma t) =
      (cov Y (gamma t)) (curveVelocity I gamma t) := by
  exact HasPullbackCovariantAccelerationAt.unique
    (I := I) (cov := cov) (gamma := gamma) (t := t)
    (hasPullbackCovariantAccelerationAt_of_velocityExtensionAt
      (I := I) (cov := cov) (gamma := gamma) (X := X) (t := t) hgamma hX)
    (hasPullbackCovariantAccelerationAt_of_velocityExtensionAt
      (I := I) (cov := cov) (gamma := gamma) (X := Y) (t := t) hgamma hY)

/-- The covariant acceleration relation is unique whenever the curve is
differentiable at the parameter value. -/
theorem HasCovariantAccelerationAt.unique
    [CompleteSpace E]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {A B : TangentSpace I (gamma t)}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hA : HasCovariantAccelerationAt (I := I) cov gamma t A)
    (hB : HasCovariantAccelerationAt (I := I) cov gamma t B) :
    A = B := by
  rcases hA with ⟨X, hX, hAeq⟩
  rcases hB with ⟨Y, hY, hBeq⟩
  rw [hAeq, hBeq]
  exact covariantAcceleration_eq_of_velocityExtensions
    (I := I) hgamma hX hY

/-- In the `extChartAt` coordinate package centered at `gamma t`, the scalar
geodesic ODE is equivalent to vanishing of the coordinate components of the
covariant acceleration. -/
theorem hasCoordinateGeodesicODEAt_extChartAt_iff_geodesicEquationAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) :
    HasCoordinateGeodesicODEAt (I := I)
        (extChartAtCoordinateData (I := I) (gamma t)) cov gamma t ↔
      HasCoordinateGeodesicEquationAt (I := I)
        (extChartAtCoordinateData (I := I) (gamma t)) cov gamma t := by
  exact hasCoordinateGeodesicODEAt_iff_geodesicEquationAt_of_formula
    (I := I) (extChartAtCoordinateData (I := I) (gamma t)) cov gamma t
    (fun A hA =>
      hasCoordinateAccelerationFormulaAt_extChartAt
        (I := I) (cov := cov) (gamma := gamma) (t := t)
        (A := A) hA)

/-- The invariant coordinate equation in the `extChartAt` package is exactly
the intrinsic pointwise geodesic equation. -/
theorem hasCoordinateGeodesicEquationAt_extChartAt_iff_intrinsic
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (gamma : Curve M) (t : Real)
    (hgt : gamma t ∈ coordinateFrameSet (I := I) x0) :
    HasCoordinateGeodesicEquationAt (I := I)
        (extChartAtCoordinateData (I := I) x0) cov gamma t ↔
      HasIntrinsicGeodesicEquationAt (I := I) cov gamma t := by
  exact hasCoordinateGeodesicEquationAt_iff_intrinsic
    (I := I) (extChartAtCoordinateData (I := I) x0) cov gamma t hgt

/-- At the base point of the `extChartAt` package, the coordinate equation is
again the intrinsic pointwise geodesic equation. -/
theorem hasCoordinateGeodesicEquationAt_extChartAt_base_iff_intrinsic
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (gamma : Curve M) (t : Real) (hbase : gamma t = x0) :
    HasCoordinateGeodesicEquationAt (I := I)
        (extChartAtCoordinateData (I := I) x0) cov gamma t ↔
      HasIntrinsicGeodesicEquationAt (I := I) cov gamma t := by
  exact hasCoordinateGeodesicEquationAt_extChartAt_iff_intrinsic
    (I := I) cov x0 gamma t (by
      simpa [hbase] using coordinateFrameAt_mem (I := I) x0)

end Lecture07
end GlobalGeometry
end RicciFlower
