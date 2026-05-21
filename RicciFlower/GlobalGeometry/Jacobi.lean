import RicciFlower.GlobalGeometry.Lecture07.PullbackConnection
import RicciFlower.GlobalGeometry.Lecture07.SurfaceCalculus
import RicciFlower.LeviCivita.Smooth
import RicciFlower.Riemann.Basic
import RicciFlower.Curvature.Components.Christoffel
import RicciFlower.Tensor.Auxiliary.SlotAlgebra

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pullback Jacobi fields

This file is the canonical global-geometry layer for Jacobi fields.  It uses
the pullback covariant-derivative relation from Lecture 7.3 rather than the
older global-extension predicate.

The curvature term is stated in the pointwise `(1,3)` tensor API:
`riemannCurvatureAt cov hcov x`.  Since RicciFlower does not yet expose a
general vector-valued public action `R(X,Y)Z`, the Jacobi equation is tested
against all cotangent vectors.  This keeps the statement intrinsic and avoids
returning to ambient vector-field representatives.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Filter Tensor0SBundle RicciFlower.Curvature
open scoped Manifold ContDiff Topology

open Lecture07
open RicciFlower.Tensor.SlotAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-! ## Two-parameter variations -/

/-- A two-parameter surface used for geodesic variations.  The first parameter
is the variation parameter and the second is the curve time. -/
abbrev Surface (M : Type*) := Real × Real -> M

/-- The time curve `t ↦ F (s,t)` in a variation. -/
def timeCurve (F : Surface M) (s : Real) : Curve M :=
  fun t => F (s, t)

/-- The parameter curve `s ↦ F (s,t)` through a fixed time. -/
def paramCurve (F : Surface M) (t : Real) : Curve M :=
  fun s => F (s, t)

/-- Velocity in the time direction of a two-parameter surface. -/
def timeField (I : ModelWithCorners Real E H) (F : Surface M) :
    (p : Real × Real) -> TangentSpace I (F p) :=
  fun p => curveVelocity I (timeCurve F p.1) p.2

/-- Velocity in the variation-parameter direction of a two-parameter surface. -/
def paramField (I : ModelWithCorners Real E H) (F : Surface M) :
    (p : Real × Real) -> TangentSpace I (F p) :=
  fun p => curveVelocity I (paramCurve F p.2) p.1

/-- The variation field along the base curve `t ↦ F (s0,t)`. -/
def variationField (I : ModelWithCorners Real E H) (F : Surface M)
    (s0 : Real) : VectorFieldAlong I (timeCurve F s0) :=
  fun t => curveVelocity I (paramCurve F t) s0

/-- Smoothness of a two-parameter variation as a map from the standard product
model.  The implementation lives in the Lecture 7 surface-calculus layer. -/
abbrev SmoothSurface (I : ModelWithCorners Real E H) (F : Surface M) : Prop :=
  Lecture07.SmoothSurface (I := I) F

/-! ## Surface fields and curve restrictions -/

/-- A tangent field along a two-parameter surface. -/
abbrev SurfaceField (I : ModelWithCorners Real E H) (F : Surface M) :=
  (p : Real × Real) -> TangentSpace I (F p)

/-- Restrict a surface field to the time curve `t ↦ F (s,t)`. -/
def timeRestrictField (I : ModelWithCorners Real E H) (F : Surface M)
    (V : SurfaceField I F) (s : Real) :
    VectorFieldAlong I (timeCurve F s) :=
  fun t => V (s, t)

/-- Restrict a surface field to the parameter curve `s ↦ F (s,t)`. -/
def paramRestrictField (I : ModelWithCorners Real E H) (F : Surface M)
    (V : SurfaceField I F) (t : Real) :
    VectorFieldAlong I (paramCurve F t) :=
  fun s => V (s, t)

/-- An ambient field realizes a surface field near a parameter point. -/
def SurfaceFieldRealizedByAt (F : Surface M) (V : SurfaceField I F)
    (X : GlobalVectorField I M) (p : Real × Real) : Prop :=
  ∀ᶠ q in 𝓝 p, V q = X (F q)

/-- A surface-field representative restricts to a pullback derivative along a
time curve. -/
theorem surfTime_rep
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s0 t : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (timeCurve F s0) t)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s0, t)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s0, t)) :
    HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov (timeCurve F s0)
      (timeRestrictField I F V s0) t
      ((cov X (F (s0, t))) (curveVelocity I (timeCurve F s0) t)) := by
  have hmap :
      Tendsto (fun τ : Real => (s0, τ)) (𝓝 t) (𝓝 (s0, t)) :=
    (ContinuousAt.prodMk continuousAt_const continuousAt_id).tendsto
  refine ⟨hγ, X, ⟨hX, ?_⟩, rfl⟩
  filter_upwards [hmap.eventually hVX] with τ hτ
  simpa [timeRestrictField, timeCurve] using hτ

/-- A surface-field representative restricts to a pullback derivative along a
parameter curve. -/
theorem surfParam_rep
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s t0 : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (paramCurve F t0) s)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s, t0)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s, t0)) :
    HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov (paramCurve F t0)
      (paramRestrictField I F V t0) s
      ((cov X (F (s, t0))) (curveVelocity I (paramCurve F t0) s)) := by
  have hmap :
      Tendsto (fun σ : Real => (σ, t0)) (𝓝 s) (𝓝 (s, t0)) :=
    (ContinuousAt.prodMk continuousAt_id continuousAt_const).tendsto
  refine ⟨hγ, X, ⟨hX, ?_⟩, rfl⟩
  filter_upwards [hmap.eventually hVX] with σ hσ
  simpa [paramRestrictField, paramCurve] using hσ

/-- A surface-field representative restricts to the canonical frame-defined
pullback derivative along a time curve. -/
private theorem surfTime_frame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s0 t : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (timeCurve F s0) t)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s0, t)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s0, t)) :
    HasPBCovAlongAt (I := I) cov (timeCurve F s0)
      (timeRestrictField I F V s0) t
      ((cov X (F (s0, t))) (curveVelocity I (timeCurve F s0) t)) := by
  exact (surfTime_rep (I := I) (cov := cov) hγ hX hVX).toPBCov

/-- A surface-field representative restricts to the canonical frame-defined
pullback derivative along a parameter curve. -/
private theorem surfParam_frame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s t0 : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (paramCurve F t0) s)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s, t0)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s, t0)) :
    HasPBCovAlongAt (I := I) cov (paramCurve F t0)
      (paramRestrictField I F V t0) s
      ((cov X (F (s, t0))) (curveVelocity I (paramCurve F t0) s)) := by
  exact (surfParam_rep (I := I) (cov := cov) hγ hX hVX).toPBCov

/-! ## Pullback Jacobi equation -/

/-- A second covariant derivative along a curve, using the canonical
frame-defined pullback derivative relation. -/
def HasSecondPullbackDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (t : Real)
    (A : TangentSpace I (gamma t)) : Prop :=
  ∃ W : VectorFieldAlong I gamma,
    HasPBCovAlongAt (I := I) cov gamma J t (W t) ∧
      HasPBCovAlongAt (I := I) cov gamma W t A

/-- The pointwise curvature scalar `α (R(J,γ')γ')`.

This is the public curvature term for the current Jacobi API.  It is
cotangent-tested because the available pointwise curvature object is the
RicciFlower `(1,3)` tensor `riemannCurvatureAt`. -/
def curvatureAlongScalarAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (t : Real)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) : Real :=
  Riemann.CovariantDerivative.riemannCurvatureAt (I := I) cov hcov (gamma t) α
    (vec3 (I := I) (J t) (curveVelocity I gamma t) (curveVelocity I gamma t))

/-- Coordinate expansion of the Jacobi curvature scalar in the centered
coordinate frame at the curve point. -/
theorem curvScalar_coord_expand
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) :
    curvatureAlongScalarAt (I := I) cov hcov gamma J t α =
      ∑ r : Fin 3 -> Coordinates.CoordinateIdx (𝕜 := Real) E,
        (∏ q : Fin 3,
          (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
            (vec3 (I := I) (J t) (curveVelocity I gamma t)
              (curveVelocity I gamma t) q) (r q)) *
          (∑ m : Coordinates.CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCurvCoeffAt (I := I) cov (gamma t)
              (r 0) (r 1) (r 2) m *
              α (fun _ : Fin 1 =>
                Coordinates.coordinateFrameAt (I := I) (gamma t) m (gamma t))) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    Riemann.CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  have hRm : Realized.Rm13RealizesConnection (I := I) cov Rm13 := by
    intro X Y Z x β
    exact Riemann.CovariantDerivative.rm13Section_apply_smooth
      (I := I) (M := M) cov hcov X Y Z β
  have hcurv : Realized.ConnectionCurvatureCoordAt (I := I) cov (gamma t) :=
    Realized.connection_curvature_coord_of_christoffel (I := I) cov hcov (gamma t)
  have h :=
    Realized.rm13_coord_expand (I := I) cov hcov1 Rm13 (gamma t) α hRm hcurv
      (J t) (curveVelocity I gamma t) (curveVelocity I gamma t)
  simpa [curvatureAlongScalarAt, Rm13] using h

/-- Algebraic bridge from the fixed-frame curvature vector to the intrinsic
Jacobi curvature scalar, after the coordinate coefficients of the fixed-frame
curvature matrix have been identified with the coordinate curvature tensor. -/
theorem curvVec_scalar_of_coeff
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (Γs Γt dΓt_s dΓs_t :
      Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
        (Coordinates.CoordinateIdx (𝕜 := Real) E) Real)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t))
    (hcoeff :
      ∀ m : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Lecture07.frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec
            (Lecture07.frameVec (I := I)
              (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
              (Module.finBasis Real E) (curveVelocity I gamma t)) m =
          ∑ r : Fin 3 -> Coordinates.CoordinateIdx (𝕜 := Real) E,
            (∏ q : Fin 3,
              (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                (vec3 (I := I) (J t) (curveVelocity I gamma t)
                  (curveVelocity I gamma t) q) (r q)) *
              Realized.christoffelCurvCoeffAt (I := I) cov (gamma t)
                (r 0) (r 1) (r 2) m) :
    cotangentToDual (I := I) α
        (Lecture07.frameCurvVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
          (Module.finBasis Real E) Γs Γt dΓt_s dΓs_t
          (curveVelocity I gamma t)) =
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α := by
  classical
  let e := Coordinates.coordinateTrivializationAt (I := I) (gamma t)
  let b := Module.finBasis Real E
  have hscalar :=
    curvScalar_coord_expand (I := I) (cov := cov) (hcov := hcov)
      hcov1 (gamma := gamma) (J := J) (t := t) α
  rw [hscalar]
  calc
    cotangentToDual (I := I) α
        (Lecture07.frameCurvVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
          (Module.finBasis Real E) Γs Γt dΓt_s dΓs_t
          (curveVelocity I gamma t))
        =
      ∑ m : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ((Lecture07.frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec
          (Lecture07.frameVec (I := I)
            (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
            (Module.finBasis Real E) (curveVelocity I gamma t)) m) *
          α (fun _ : Fin 1 =>
            Coordinates.coordinateFrameAt (I := I) (gamma t) m (gamma t)) := by
        simp [Lecture07.frameCurvVec, Lecture07.frameSum, cotangentToDual_apply,
          Coordinates.coordinateFrameAt, Coordinates.coordinateTrivializationAt]
    _ =
      ∑ m : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (∑ r : Fin 3 -> Coordinates.CoordinateIdx (𝕜 := Real) E,
            (∏ q : Fin 3,
              (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                (vec3 (I := I) (J t) (curveVelocity I gamma t)
                  (curveVelocity I gamma t) q) (r q)) *
              Realized.christoffelCurvCoeffAt (I := I) cov (gamma t)
                (r 0) (r 1) (r 2) m) *
          α (fun _ : Fin 1 =>
            Coordinates.coordinateFrameAt (I := I) (gamma t) m (gamma t)) := by
        refine Finset.sum_congr rfl ?_
        intro m _hm
        rw [hcoeff m]
    _ =
      ∑ r : Fin 3 -> Coordinates.CoordinateIdx (𝕜 := Real) E,
        (∏ q : Fin 3,
          (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
            (vec3 (I := I) (J t) (curveVelocity I gamma t)
              (curveVelocity I gamma t) q) (r q)) *
          (∑ m : Coordinates.CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCurvCoeffAt (I := I) cov (gamma t)
              (r 0) (r 1) (r 2) m *
              α (fun _ : Fin 1 =>
                Coordinates.coordinateFrameAt (I := I) (gamma t) m (gamma t))) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- In the centered coordinate frame, the local-frame connection matrix in a
curve direction is the velocity-coordinate contraction of Christoffel
coefficients. -/
theorem frameGammaMat_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real)
    (j k : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
        (Module.finBasis Real E) gamma t
        (1 : TangentSpace 𝓘(Real, Real) t) k j =
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
            (curveVelocity I gamma t) i *
          Realized.christoffelCoordAt (I := I) cov (gamma t) i j k := by
  classical
  let x : M := gamma t
  let frame := Coordinates.coordinateFrameAt (I := I) x
  let hframe := Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x
  have hx : x ∈ Coordinates.coordinateFrameSet (I := I) x :=
    Coordinates.coordinateFrameAt_mem (I := I) x
  have h :=
    Coordinates.christoffelAlongInFrame_eq_sum_coeff
      (I := I) (Idx := Coordinates.CoordinateIdx (𝕜 := Real) E)
      cov frame hframe hx (curveVelocity I gamma t) j k
  simpa [Lecture07.frameGammaMat, Lecture07.frameGamma,
    Coordinates.christoffelAlongInFrame, Realized.christoffelCoordAt,
    Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord,
    Bundle.Trivialization.localFrame_coeff, IsLocalFrameOn.coeff, hx,
    Coordinates.coordinateFrameAt_toBasis, Coordinates.coordinateFrameAt_basis,
    IsLocalFrameOn.toBasisAt_coe,
    Coordinates.coordinateFrameAt, Coordinates.coordinateTrivializationAt,
    curveVelocity, x, frame, hframe] using h

/-- In a fixed coordinate frame centered at `x₀`, the local-frame connection
matrix in a curve direction is the velocity-coordinate contraction of the
fixed-center Christoffel coefficient function. -/
theorem frameGammaMat_fixed
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (gamma : Curve M) (t : Real)
    (hgt : gamma t ∈ Coordinates.coordinateFrameSet (I := I) x₀)
    (j k : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (Coordinates.coordinateTrivializationAt (I := I) x₀)
        (Module.finBasis Real E) gamma t
        (1 : TangentSpace 𝓘(Real, Real) t) k j =
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
            i (gamma t) (curveVelocity I gamma t) *
          Realized.christoffelCoordFun (I := I) cov x₀ i j k (gamma t) := by
  classical
  let frame := Coordinates.coordinateFrameAt (I := I) x₀
  let hframe := Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have h :=
    Coordinates.christoffelAlongInFrame_eq_sum_coeff
      (I := I) (Idx := Coordinates.CoordinateIdx (𝕜 := Real) E)
      cov frame hframe hgt (curveVelocity I gamma t) j k
  simpa [Lecture07.frameGammaMat, Lecture07.frameGamma,
    Coordinates.christoffelAlongInFrame, Realized.christoffelCoordFun,
    Coordinates.coordinateFrameAt, Coordinates.coordinateTrivializationAt,
    curveVelocity, frame, hframe] using h

/-- Fixed-coordinate expansion of the connection matrix in the time direction
of a two-parameter surface. -/
theorem frameGammaMat_time
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (F : Surface M) (s t : Real)
    (hst : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x₀)
    (j k : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (Coordinates.coordinateTrivializationAt (I := I) x₀)
        (Module.finBasis Real E) (timeCurve F s) t
        (1 : TangentSpace 𝓘(Real, Real) t) k j =
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
            i (F (s, t)) (timeField I F (s, t)) *
          Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) := by
  simpa [timeCurve, timeField] using
    frameGammaMat_fixed (I := I) cov x₀ (timeCurve F s) t hst j k

/-- Fixed-coordinate expansion of the connection matrix in the variation
parameter direction of a two-parameter surface. -/
theorem frameGammaMat_param
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (F : Surface M) (s t : Real)
    (hst : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x₀)
    (j k : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (Coordinates.coordinateTrivializationAt (I := I) x₀)
        (Module.finBasis Real E) (paramCurve F t) s
        (1 : TangentSpace 𝓘(Real, Real) s) k j =
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
            i (F (s, t)) (paramField I F (s, t)) *
          Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) := by
  simpa [paramCurve, paramField] using
    frameGammaMat_fixed (I := I) cov x₀ (paramCurve F t) s hst j k

/-- Product rule for the fixed-coordinate time-direction connection matrix
when the variation parameter changes.  The derivative of the Christoffel
coefficient along the surface is supplied separately, so this lemma is only
finite-sum calculus. -/
private theorem gammaT_deriv_s
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (F : Surface M) (s t : Real)
    (hmem : ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ Coordinates.coordinateFrameSet (I := I) x₀)
    (T S Ts : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (hT :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
            i (F (s, t)) (timeField I F (s, t)) = T i)
    (hTderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
              i (F (σ, t)) (timeField I F (σ, t)))
          (Ts i) s)
    (hCderiv :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (σ, t)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k) s)
    (j k : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun σ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (timeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t) k j)
      (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Ts i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
          T i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              S a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
      s := by
  classical
  let coeff :
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real -> Real :=
    fun i σ =>
      (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
        i (F (σ, t)) (timeField I F (σ, t))
  let C :
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real -> Real :=
    fun i σ => Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (σ, t))
  have hrhs :
      HasDerivAt
        (fun σ : Real =>
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E, coeff i σ * C i σ)
        (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
          (Ts i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
            T i *
              (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
                S a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
        s := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hmul := (hTderiv i).mul (hCderiv i j k)
    simpa [coeff, C, hT i, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hline :
      (fun σ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (timeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t) k j) =ᶠ[𝓝 s]
        (fun σ : Real =>
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E, coeff i σ * C i σ) := by
    filter_upwards [hmem] with σ hσ
    simpa [coeff, C] using
      (frameGammaMat_time (I := I) cov x₀ F σ t hσ j k)
  exact hrhs.congr_of_eventuallyEq hline

/-- Product rule for the fixed-coordinate parameter-direction connection matrix
when the time parameter changes. -/
private theorem gammaS_deriv_t
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (F : Surface M) (s t : Real)
    (hmem : ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ Coordinates.coordinateFrameSet (I := I) x₀)
    (S T St : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (hS :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
            i (F (s, t)) (paramField I F (s, t)) = S i)
    (hSderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
              i (F (s, τ)) (paramField I F (s, τ)))
          (St i) t)
    (hCderiv :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, τ)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            T a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k) t)
    (j k : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (paramCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s) k j)
      (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (St i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
          S i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              T a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
      t := by
  classical
  let coeff :
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real -> Real :=
    fun i τ =>
      (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
        i (F (s, τ)) (paramField I F (s, τ))
  let C :
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real -> Real :=
    fun i τ => Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, τ))
  have hrhs :
      HasDerivAt
        (fun τ : Real =>
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E, coeff i τ * C i τ)
        (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
          (St i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
            S i *
              (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
                T a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
        t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hmul := (hSderiv i).mul (hCderiv i j k)
    simpa [coeff, C, hS i, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hline :
      (fun τ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (paramCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s) k j) =ᶠ[𝓝 t]
        (fun τ : Real =>
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E, coeff i τ * C i τ) := by
    filter_upwards [hmem] with τ hτ
    simpa [coeff, C] using
      (frameGammaMat_param (I := I) cov x₀ F s τ hτ j k)
  exact hrhs.congr_of_eventuallyEq hline

/-- Matrix-valued version of `gammaT_deriv_s`. -/
private theorem gammaT_deriv_s_mat
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (F : Surface M) (s t : Real)
    (hmem : ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ Coordinates.coordinateFrameSet (I := I) x₀)
    (T S Ts : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (hT :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
            i (F (s, t)) (timeField I F (s, t)) = T i)
    (hTderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
              i (F (σ, t)) (timeField I F (σ, t)))
          (Ts i) s)
    (hCderiv :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (σ, t)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k) s) :
    HasDerivAt
      (fun σ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (timeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t))
      (fun k j =>
        ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
          (Ts i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
            T i *
              (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
                S a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
      s := by
  change HasDerivAt
    (fun σ : Real => fun k j =>
      Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (Coordinates.coordinateTrivializationAt (I := I) x₀)
        (Module.finBasis Real E) (timeCurve F σ) t
        (1 : TangentSpace 𝓘(Real, Real) t) k j)
    (fun k j =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Ts i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
          T i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              S a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
    s
  rw [hasDerivAt_pi]
  intro k
  rw [hasDerivAt_pi]
  intro j
  exact gammaT_deriv_s (I := I) cov x₀ F s t hmem T S Ts hT hTderiv hCderiv j k

/-- Matrix-valued version of `gammaS_deriv_t`. -/
private theorem gammaS_deriv_t_mat
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (F : Surface M) (s t : Real)
    (hmem : ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ Coordinates.coordinateFrameSet (I := I) x₀)
    (S T St : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (hS :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
            i (F (s, t)) (paramField I F (s, t)) = S i)
    (hSderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff
              i (F (s, τ)) (paramField I F (s, τ)))
          (St i) t)
    (hCderiv :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, τ)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            T a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k) t) :
    HasDerivAt
      (fun τ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (paramCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s))
      (fun k j =>
        ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
          (St i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
            S i *
              (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
                T a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
      t := by
  change HasDerivAt
    (fun τ : Real => fun k j =>
      Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (Coordinates.coordinateTrivializationAt (I := I) x₀)
        (Module.finBasis Real E) (paramCurve F τ) s
        (1 : TangentSpace 𝓘(Real, Real) s) k j)
    (fun k j =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (St i * Realized.christoffelCoordFun (I := I) cov x₀ i j k (F (s, t)) +
          S i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              T a * Realized.christoffelCoordDerivAt (I := I) cov x₀ a i j k)))
    t
  rw [hasDerivAt_pi]
  intro k
  rw [hasDerivAt_pi]
  intro j
  exact gammaS_deriv_t (I := I) cov x₀ F s t hmem S T St hS hSderiv hCderiv j k

/-- Pure algebra for the antisymmetric derivative part of the curvature
matrix.  After the product-rule expansions of `∂s Γt` and `∂t Γs`, equal
mixed velocity derivatives cancel, leaving only the antisymmetrized
Christoffel-coordinate derivative. -/
private theorem gammaDeriv_skew
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T Ts St : ι -> Real)
    (C : ι -> ι -> ι -> Real) (dC : ι -> ι -> ι -> ι -> Real)
    (dΓt_s dΓs_t : Matrix ι ι Real)
    (hΓt : ∀ m j : ι,
      dΓt_s m j =
        ∑ k : ι, (Ts k * C k j m +
          T k * (∑ i : ι, S i * dC i k j m)))
    (hΓs : ∀ m j : ι,
      dΓs_t m j =
        ∑ i : ι, (St i * C i j m +
          S i * (∑ k : ι, T k * dC k i j m)))
    (hmix : Ts = St) :
    ∀ m j : ι,
      dΓt_s m j - dΓs_t m j =
        ∑ i : ι, ∑ k : ι,
          S i * T k * (dC i k j m - dC k i j m) := by
  classical
  intro m j
  have hfirst :
      (∑ k : ι, Ts k * C k j m) =
        (∑ i : ι, St i * C i j m) := by
    subst hmix
    rfl
  have hsecond :
      (∑ k : ι, T k * (∑ i : ι, S i * dC i k j m)) =
        ∑ i : ι, ∑ k : ι, S i * T k * dC i k j m := by
    calc
      (∑ k : ι, T k * (∑ i : ι, S i * dC i k j m))
          = ∑ k : ι, ∑ i : ι, T k * (S i * dC i k j m) := by
            simp [Finset.mul_sum]
      _ = ∑ i : ι, ∑ k : ι, T k * (S i * dC i k j m) := by
            rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ k : ι, S i * T k * dC i k j m := by
            simp [mul_left_comm, mul_comm]
  have hthird :
      (∑ i : ι, S i * (∑ k : ι, T k * dC k i j m)) =
        ∑ i : ι, ∑ k : ι, S i * T k * dC k i j m := by
    simp [Finset.mul_sum, mul_assoc]
  rw [hΓt, hΓs]
  simp_rw [Finset.sum_add_distrib]
  rw [hfirst, hsecond, hthird]
  have hdiff :
      (∑ i : ι, ∑ k : ι,
          S i * T k * (dC i k j m - dC k i j m)) =
        (∑ i : ι, ∑ k : ι, S i * T k * dC i k j m) -
          (∑ i : ι, ∑ k : ι, S i * T k * dC k i j m) := by
    simp [Finset.sum_sub_distrib, mul_sub]
  rw [hdiff]
  abel

private theorem curvMat_contract
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T V : ι -> Real)
    (Γs Γt dΓt_s dΓs_t : Matrix ι ι Real)
    (C : ι -> ι -> ι -> Real) (dC : ι -> ι -> ι -> ι -> Real)
    (hΓs : ∀ m j : ι, Γs m j = ∑ i : ι, S i * C i j m)
    (hΓt : ∀ m j : ι, Γt m j = ∑ k : ι, T k * C k j m)
    (hdΓ : ∀ m j : ι,
      dΓt_s m j - dΓs_t m j =
        ∑ i : ι, ∑ k : ι, S i * T k * (dC i k j m - dC k i j m))
    (m : ι) :
    (dΓt_s - dΓs_t + Γs * Γt - Γt * Γs).mulVec V m =
      ∑ i : ι, ∑ k : ι, ∑ j : ι,
        S i * T k * V j *
          (dC i k j m - dC k i j m +
            (∑ a : ι, C k j a * C i a m) -
            (∑ a : ι, C i j a * C k a m)) := by
  classical
  have hsplit (A B C D V : ι -> Real) :
      (∑ j : ι, (A j + (-D j + (B j + -C j))) * V j) =
        (∑ j : ι, B j * V j) - (∑ j : ι, C j * V j) +
          (∑ j : ι, (A j - D j) * V j) := by
    simp [Finset.sum_add_distrib, sub_eq_add_neg, add_mul]
    abel
  have hD :
      (∑ j : ι,
        (∑ i : ι, ∑ k : ι,
          S i * T k * (dC i k j m - dC k i j m)) * V j) =
        ∑ i : ι, ∑ k : ι, ∑ j : ι,
          S i * T k * V j * (dC i k j m - dC k i j m) := by
    calc
      (∑ j : ι,
        (∑ i : ι, ∑ k : ι,
          S i * T k * (dC i k j m - dC k i j m)) * V j)
          =
        ∑ i : ι, ∑ k : ι, ∑ j : ι,
          (S i * T k * (dC i k j m - dC k i j m)) * V j := by
          rw [sum_mul_right3]
      _ = ∑ i : ι, ∑ k : ι, ∑ j : ι,
          S i * T k * V j * (dC i k j m - dC k i j m) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
  have hP :
      (∑ j : ι,
        (∑ a : ι,
          (∑ i : ι, S i * C i a m) *
            (∑ k : ι, T k * C k j a)) * V j) =
        ∑ i : ι, ∑ k : ι, ∑ j : ι,
          S i * T k * V j * (∑ a : ι, C k j a * C i a m) := by
    calc
      (∑ j : ι,
        (∑ a : ι,
          (∑ i : ι, S i * C i a m) *
            (∑ k : ι, T k * C k j a)) * V j)
          =
        ∑ j : ι, ∑ a : ι, ∑ k : ι, ∑ i : ι,
          (S i * C i a m) * (T k * C k j a) * V j := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ =
        ∑ k : ι, ∑ i : ι, ∑ j : ι, ∑ a : ι,
          (S i * C i a m) * (T k * C k j a) * V j := by
          rw [sum_rotate4_two]
      _ =
        ∑ i : ι, ∑ k : ι, ∑ j : ι, ∑ a : ι,
          (S i * C i a m) * (T k * C k j a) * V j := by
          rw [Finset.sum_comm]
      _ =
        ∑ i : ι, ∑ k : ι, ∑ j : ι,
          S i * T k * V j * (∑ a : ι, C k j a * C i a m) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
  have hQ :
      (∑ j : ι,
        (∑ a : ι,
          (∑ k : ι, T k * C k a m) *
            (∑ i : ι, S i * C i j a)) * V j) =
        ∑ i : ι, ∑ k : ι, ∑ j : ι,
          S i * T k * V j * (∑ a : ι, C i j a * C k a m) := by
    calc
      (∑ j : ι,
        (∑ a : ι,
          (∑ k : ι, T k * C k a m) *
            (∑ i : ι, S i * C i j a)) * V j)
          =
        ∑ j : ι, ∑ a : ι, ∑ i : ι, ∑ k : ι,
          (T k * C k a m) * (S i * C i j a) * V j := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ =
        ∑ i : ι, ∑ k : ι, ∑ j : ι, ∑ a : ι,
          (T k * C k a m) * (S i * C i j a) * V j := by
          rw [sum_rotate4_two]
      _ =
        ∑ i : ι, ∑ k : ι, ∑ j : ι,
          S i * T k * V j * (∑ a : ι, C i j a * C k a m) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
  calc
    (dΓt_s - dΓs_t + Γs * Γt - Γt * Γs).mulVec V m =
        (∑ j : ι, (Γs * Γt) m j * V j) -
          (∑ j : ι, (Γt * Γs) m j * V j) +
          (∑ j : ι, (dΓt_s m j - dΓs_t m j) * V j) := by
          simpa [Matrix.mulVec, dotProduct, sub_eq_add_neg, add_assoc] using
            hsplit (fun j => dΓt_s m j) (fun j => (Γs * Γt) m j)
              (fun j => (Γt * Γs) m j) (fun j => dΓs_t m j) V
    _ =
        (∑ j : ι,
          (∑ a : ι,
            (∑ i : ι, S i * C i a m) *
              (∑ k : ι, T k * C k j a)) * V j) -
          (∑ j : ι,
            (∑ a : ι,
              (∑ k : ι, T k * C k a m) *
                (∑ i : ι, S i * C i j a)) * V j) +
          (∑ j : ι,
            (∑ i : ι, ∑ k : ι,
              S i * T k * (dC i k j m - dC k i j m)) * V j) := by
          simp [Matrix.mul_apply, hΓs, hΓt, hdΓ]
    _ =
        ∑ i : ι, ∑ k : ι, ∑ j : ι,
          S i * T k * V j *
            (dC i k j m - dC k i j m +
              (∑ a : ι, C k j a * C i a m) -
              (∑ a : ι, C i j a * C k a m)) := by
          rw [hP, hQ, hD]
          simp [Finset.sum_add_distrib, mul_add, sub_eq_add_neg, mul_assoc,
            mul_left_comm, mul_comm]
          abel_nf

/-- Coordinate expansion of the fixed-frame curvature matrix expression.

This is the finite-sum algebra core of the surface-commutator curvature
bridge.  The geometric producer still has to supply the three hypotheses:
`Γs`, `Γt`, and the antisymmetric derivative term in coordinates. -/
theorem frameCurvMat_coord
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {x : M}
    (S T V : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (Γs Γt dΓt_s dΓs_t :
      Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
        (Coordinates.CoordinateIdx (𝕜 := Real) E) Real)
    (hΓs :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γs m j =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S i * Realized.christoffelCoordAt (I := I) cov x i j m)
    (hΓt :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γt m j =
          ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
            T k * Realized.christoffelCoordAt (I := I) cov x k j m)
    (hdΓ :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        dΓt_s m j - dΓs_t m j =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
              S i * T k *
                (Realized.christoffelCoordDerivAt (I := I) cov x i k j m -
                  Realized.christoffelCoordDerivAt (I := I) cov x k i j m))
    (m : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    (Lecture07.frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec V m =
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S i * T k * V j *
              Realized.christoffelCurvCoeffAt (I := I) cov x i k j m := by
  classical
  have h :=
    curvMat_contract
      (S := S) (T := T) (V := V)
      (Γs := Γs) (Γt := Γt) (dΓt_s := dΓt_s) (dΓs_t := dΓs_t)
      (C := fun i j m =>
        Realized.christoffelCoordAt (I := I) cov x i j m)
      (dC := fun i k j m =>
        Realized.christoffelCoordDerivAt (I := I) cov x i k j m)
      hΓs hΓt hdΓ m
  simpa [Lecture07.frameCurvMat, Realized.christoffelCurvCoeffAt, add_assoc,
    sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using h

/-- Coordinate expansion of the fixed-frame curvature matrix after the
product-rule derivatives of `Γs` and `Γt` have been supplied.  The equal mixed
velocity derivative terms are cancelled by `gammaDeriv_skew`. -/
theorem frameCurvMat_deriv
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {x : M}
    (S T V Ts St : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (Γs Γt dΓt_s dΓs_t :
      Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
        (Coordinates.CoordinateIdx (𝕜 := Real) E) Real)
    (hΓs :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γs m j =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S i * Realized.christoffelCoordAt (I := I) cov x i j m)
    (hΓt :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γt m j =
          ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
            T k * Realized.christoffelCoordAt (I := I) cov x k j m)
    (hDΓt :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        dΓt_s m j =
          ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Ts k * Realized.christoffelCoordAt (I := I) cov x k j m +
              T k *
                (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                  S i * Realized.christoffelCoordDerivAt (I := I) cov x i k j m)))
    (hDΓs :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        dΓs_t m j =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (St i * Realized.christoffelCoordAt (I := I) cov x i j m +
              S i *
                (∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                  T k * Realized.christoffelCoordDerivAt (I := I) cov x k i j m)))
    (hmix : Ts = St)
    (m : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    (Lecture07.frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec V m =
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S i * T k * V j *
              Realized.christoffelCurvCoeffAt (I := I) cov x i k j m := by
  classical
  exact frameCurvMat_coord (I := I)
    (S := S) (T := T) (V := V)
    (Γs := Γs) (Γt := Γt) (dΓt_s := dΓt_s) (dΓs_t := dΓs_t)
    hΓs hΓt
    (gammaDeriv_skew
      (S := S) (T := T) (Ts := Ts) (St := St)
      (C := fun i j m => Realized.christoffelCoordAt (I := I) cov x i j m)
      (dC := fun i k j m =>
        Realized.christoffelCoordDerivAt (I := I) cov x i k j m)
      (dΓt_s := dΓt_s) (dΓs_t := dΓs_t) hDΓt hDΓs hmix)
    m

/-- Cotangent-tested curvature bridge after the fixed-coordinate `Γ` matrices
and their product-rule derivatives have been identified. -/
theorem curvVec_scalar_deriv
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (Γs Γt dΓt_s dΓs_t :
      Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
        (Coordinates.CoordinateIdx (𝕜 := Real) E) Real)
    (Ts St : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t))
    (hΓs :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γs m j =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                (J t) i *
              Realized.christoffelCoordAt (I := I) cov (gamma t) i j m)
    (hΓt :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γt m j =
          ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                (curveVelocity I gamma t) k *
              Realized.christoffelCoordAt (I := I) cov (gamma t) k j m)
    (hDΓt :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        dΓt_s m j =
          ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Ts k * Realized.christoffelCoordAt (I := I) cov (gamma t) k j m +
              (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                (curveVelocity I gamma t) k *
                (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                  (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                    (J t) i *
                    Realized.christoffelCoordDerivAt (I := I) cov
                      (gamma t) i k j m)))
    (hDΓs :
      ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        dΓs_t m j =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (St i * Realized.christoffelCoordAt (I := I) cov (gamma t) i j m +
              (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                (J t) i *
                (∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                  (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
                    (curveVelocity I gamma t) k *
                    Realized.christoffelCoordDerivAt (I := I) cov
                      (gamma t) k i j m)))
    (hmix : Ts = St) :
    cotangentToDual (I := I) α
        (Lecture07.frameCurvVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
          (Module.finBasis Real E) Γs Γt dΓt_s dΓs_t
          (curveVelocity I gamma t)) =
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α := by
  classical
  let S : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i => (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr (J t) i
  let T : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i =>
      (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
        (curveVelocity I gamma t) i
  refine curvVec_scalar_of_coeff (I := I) (cov := cov) (hcov := hcov)
    hcov1 (gamma := gamma) (J := J) (t := t)
    Γs Γt dΓt_s dΓs_t α ?_
  intro m
  have htriple :=
    frameCurvMat_deriv (I := I) (cov := cov) (x := gamma t)
      (S := S) (T := T) (V := T) (Ts := Ts) (St := St)
      (Γs := Γs) (Γt := Γt) (dΓt_s := dΓt_s) (dΓs_t := dΓs_t)
      (by simpa [S] using hΓs)
      (by simpa [T] using hΓt)
      (by simpa [S, T] using hDΓt)
      (by simpa [S, T] using hDΓs)
      hmix m
  have hframeVec :
      Lecture07.frameVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
          (Module.finBasis Real E) (curveVelocity I gamma t) = T := by
    ext i
    simp [T, Lecture07.frameVec,
      Bundle.Trivialization.localFrame_coeff, IsLocalFrameOn.coeff,
      Coordinates.coordinateFrameAt_toBasis, Coordinates.coordinateFrameAt_basis,
      Coordinates.coordinateFrameAt, Coordinates.coordinateTrivializationAt]
    rfl
  calc
    (Lecture07.frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec
        (Lecture07.frameVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (gamma t))
          (Module.finBasis Real E) (curveVelocity I gamma t)) m =
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S i * T k * T j *
              Realized.christoffelCurvCoeffAt (I := I) cov (gamma t) i k j m := by
        rw [hframeVec]
        exact htriple
    _ =
      ∑ r : Fin 3 -> Coordinates.CoordinateIdx (𝕜 := Real) E,
        (∏ q : Fin 3,
          (Coordinates.coordinateFrameAt_toBasis (I := I) (gamma t)).repr
            (vec3 (I := I) (J t) (curveVelocity I gamma t)
              (curveVelocity I gamma t) q) (r q)) *
          Realized.christoffelCurvCoeffAt (I := I) cov (gamma t)
            (r 0) (r 1) (r 2) m := by
        rw [← RicciFlower.Tensor.SlotAlgebra.sum_fin3_fun_eq_triple
          (A := S) (B := T) (C := T)
          (K := fun i k j =>
            Realized.christoffelCurvCoeffAt (I := I) cov (gamma t) i k j m)]
        simp [S, T, RicciFlower.Curvature.vec3, Fin.prod_univ_three,
          mul_assoc]

/-- Pointwise Jacobi equation along a curve.

The equation is
`D_t^2 J + R(J,γ')γ' = 0`, tested against every cotangent vector at the point. -/
def IsJacobiFieldAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (t : Real) : Prop :=
  ∃ A : TangentSpace I (gamma t),
    HasSecondPullbackDerivAt (I := I) cov gamma J t A ∧
      ∀ α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 (gamma t),
        cotangentToDual (I := I) α A +
            curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0

/-- Jacobi equation on a set of parameter values. -/
def IsJacobiFieldOn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (T : Set Real) : Prop :=
  ∀ t ∈ T, IsJacobiFieldAt (I := I) cov hcov gamma J t

/-! ## Formal geodesic-variation identities -/

/-- A geodesic variation on a rectangle of parameter values. -/
def IsGeodesicVariationOn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (S T : Set Real) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T,
    HasPBCovAccelAt (I := I) cov (timeCurve F s) t 0

/-- Torsion/mixed-derivative swap data at one point of a variation.

`W` is both the time covariant derivative of the variation field and the
parameter covariant derivative of the time field.  This is the canonical
pullback version of `D_t S = D_s T`. -/
def VariationTorsionSwapAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 t : Real)
    (W : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  HasPBCovAlongAt (I := I) cov (timeCurve F s0)
      (variationField I F s0) t (W t) ∧
    HasPBCovAlongAt (I := I) cov (paramCurve F t)
      (paramRestrictField I F (timeField I F) t) s0 (W t)

/-- Curvature commutator data after differentiating the geodesic equation.

Together with `VariationTorsionSwapAt`, this supplies the second derivative of
the variation field and the curvature term in the Jacobi equation. -/
def VariationCurvCommAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (F : Surface M) (s0 t : Real)
    (W : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  ∃ A : TangentSpace I (timeCurve F s0 t),
    HasPBCovAlongAt (I := I) cov (timeCurve F s0) W t A ∧
      ∀ α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 (timeCurve F s0 t),
        cotangentToDual (I := I) α A +
            curvatureAlongScalarAt (I := I) cov hcov
              (timeCurve F s0) (variationField I F s0) t α = 0

/-- Surface-jet curvature commutator in the centered coordinate frame.

This is the checked bridge from the fixed-frame surface commutator to the
Jacobi-facing `VariationCurvCommAt`.  The remaining producer work is exactly
the scalar surface calculus supplied here as hypotheses: derivatives of the
time/parameter velocity coefficients, derivatives of Christoffel coefficients
along the surface, and mixed-partial equality. -/
private theorem curvComm_surface
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {s t : Real}
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F (timeField I F) Vs
      (fun _ => 0) s t (0 : TangentSpace I (F (s, t))) DtsV)
    (hmem_s : ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ Coordinates.coordinateFrameSet (I := I) (F (s, t)))
    (hmem_t : ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ Coordinates.coordinateFrameSet (I := I) (F (s, t)))
    (S T Ts St : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (hS :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
            i (F (s, t)) (paramField I F (s, t)) = S i)
    (hT :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
            i (F (s, t)) (timeField I F (s, t)) = T i)
    (hTderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
              i (F (σ, t)) (timeField I F (σ, t)))
          (Ts i) s)
    (hSderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
              i (F (s, τ)) (paramField I F (s, τ)))
          (St i) t)
    (hCs :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (σ, t)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S a * Realized.christoffelCoordDerivAt (I := I) cov
              (F (s, t)) a i j k) s)
    (hCt :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (s, τ)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            T a * Realized.christoffelCoordDerivAt (I := I) cov
              (F (s, t)) a i j k) t)
    {vt vst vts : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real}
    (hvt_s : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (timeCurve F σ)
          (fun τ => timeField I F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s)
    (hvs : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (timeField I F (σ, t))) Ts s)
    (hvs_t : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (paramCurve F τ)
          (fun σ => timeField I F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t)
    (hvt : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (timeField I F (s, τ))) vt t)
    (hmix_raw : vst = vts)
    (hmix : Ts = St) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Vs (s, τ)) := by
  classical
  let x : M := F (s, t)
  let e := Coordinates.coordinateTrivializationAt (I := I) x
  let b := Module.finBasis Real E
  let Γs : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
      (paramCurve F t) s (1 : TangentSpace 𝓘(Real, Real) s)
  let Γt : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
      (timeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t)
  let dΓt_s : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    fun k j =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Ts i * Realized.christoffelCoordAt (I := I) cov x i j k +
          T i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              S a * Realized.christoffelCoordDerivAt (I := I) cov x a i j k))
  let dΓs_t : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    fun k j =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (St i * Realized.christoffelCoordAt (I := I) cov x i j k +
          S i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              T a * Realized.christoffelCoordDerivAt (I := I) cov x a i j k))
  have hmem_s_e : ∀ᶠ σ : Real in 𝓝 s, F (σ, t) ∈ e.baseSet := by
    simpa [e, x, Coordinates.coordinateTrivializationAt] using hmem_s
  have hmem_t_e : ∀ᶠ τ : Real in 𝓝 t, F (s, τ) ∈ e.baseSet := by
    simpa [e, x, Coordinates.coordinateTrivializationAt] using hmem_t
  have hΓt_deriv : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t (1 : TangentSpace 𝓘(Real, Real) t))
      dΓt_s s := by
    have h := gammaT_deriv_s_mat (I := I) cov x F s t hmem_s T S Ts
      (by simpa [x] using hT) (by simpa [x] using hTderiv)
      (by simpa [x, Realized.christoffelCoordAt, Realized.christoffelCoordFun] using hCs)
    simpa [dΓt_s, e, b, x, surfaceTimeCurve, timeCurve,
      Realized.christoffelCoordAt, Realized.christoffelCoordFun] using h
  have hΓs_deriv : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s (1 : TangentSpace 𝓘(Real, Real) s))
      dΓs_t t := by
    have h := gammaS_deriv_t_mat (I := I) cov x F s t hmem_t S T St
      (by simpa [x] using hS) (by simpa [x] using hSderiv)
      (by simpa [x, Realized.christoffelCoordAt, Realized.christoffelCoordFun] using hCt)
    simpa [dΓs_t, e, b, x, surfaceParamCurve, paramCurve,
      Realized.christoffelCoordAt, Realized.christoffelCoordFun] using h
  have hvt_s' : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => timeField I F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s := by
    simpa [e, b, x, surfaceTimeCurve, timeCurve] using hvt_s
  have hvs_t' : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => timeField I F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t := by
    simpa [e, b, x, surfaceParamCurve, paramCurve] using hvs_t
  have hvs' : HasDerivAt
      (fun σ : Real => Lecture07.frameVec (I := I) e b (timeField I F (σ, t)))
      Ts s := by
    simpa [e, b, x] using hvs
  have hvt' : HasDerivAt
      (fun τ : Real => Lecture07.frameVec (I := I) e b (timeField I F (s, τ)))
      vt t := by
    simpa [e, b, x] using hvt
  have hvec_raw := hjet.frame_dts_neg_vec (I := I) (cov := cov)
    (hDst := by rfl) (e := e) (b := b) hmem_s_e hmem_t_e
    hΓt_deriv hvt_s' hvs' hΓs_deriv hvs_t' hvt' hmix_raw
  have hvec : DtsV =
      -Lecture07.frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
        (timeField I F (s, t)) := by
    simpa [Γs, Γt, e, b, x, surfaceParamCurve, surfaceTimeCurve,
      paramCurve, timeCurve] using hvec_raw
  refine ⟨DtsV, ?_, ?_⟩
  · simpa [HasPBTimeCovDerivAt, surfaceTimeCurve, timeCurve] using
      hjet.has_time_param
  · intro α
    have hcurv : cotangentToDual (I := I) α
          (Lecture07.frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
            (timeField I F (s, t))) =
        curvatureAlongScalarAt (I := I) cov hcov
          (timeCurve F s) (variationField I F s) t α := by
      have hΓs_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            Γs m j =
              ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (variationField I F s t) i *
                  Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) i j m := by
        intro m j
        have h := frameGammaMat_coord (I := I) cov (paramCurve F t) s j m
        simpa [Γs, e, b, x, timeCurve, paramCurve, variationField] using h
      have hΓt_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            Γt m j =
              ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (curveVelocity I (timeCurve F s) t) k *
                  Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) k j m := by
        intro m j
        have h := frameGammaMat_coord (I := I) cov (timeCurve F s) t j m
        simpa [Γt, e, b, x, timeCurve] using h
      have hSrepr :
          ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                (variationField I F s t) i = S i := by
        intro i
        rw [← hS i]
        have hcoeff :=
          Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord (I := I)
            (F (s, t)) (paramField I F (s, t)) i
        simpa [timeCurve, variationField, paramField] using hcoeff.symm
      have hTrepr :
          ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                (curveVelocity I (timeCurve F s) t) i = T i := by
        intro i
        rw [← hT i]
        have hcoeff :=
          Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord (I := I)
            (F (s, t)) (timeField I F (s, t)) i
        simpa [timeCurve, timeField] using hcoeff.symm
      have hDΓt_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              dΓt_s m j =
              ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (Ts k * Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) k j m +
                  (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (curveVelocity I (timeCurve F s) t) k *
                    (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                      (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                        (variationField I F s t) i *
                        Realized.christoffelCoordDerivAt (I := I) cov
                          (timeCurve F s t) i k j m)) := by
        intro m j
        dsimp [dΓt_s, x]
        simp_rw [← hTrepr, ← hSrepr]
        simp [timeCurve]
      have hDΓs_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            dΓs_t m j =
              ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (St i * Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) i j m +
                  (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (variationField I F s t) i *
                    (∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                      (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                        (curveVelocity I (timeCurve F s) t) k *
                        Realized.christoffelCoordDerivAt (I := I) cov
                          (timeCurve F s t) k i j m)) := by
        intro m j
        dsimp [dΓs_t, x]
        simp_rw [← hTrepr, ← hSrepr]
        simp [timeCurve]
      have hmain := curvVec_scalar_deriv (I := I) (cov := cov) (hcov := hcov)
        hcov1 (gamma := timeCurve F s) (J := variationField I F s) (t := t)
        Γs Γt dΓt_s dΓs_t Ts St α
        hΓs_val hΓt_val hDΓt_val hDΓs_val hmix
      simpa [e, b, Γs, Γt, x, timeCurve, timeField] using hmain
    let R : TangentSpace I (timeCurve F s t) :=
      Lecture07.frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
        (timeField I F (s, t))
    have hdual :
        cotangentToDual (I := I) α (-R) + cotangentToDual (I := I) α R = 0 := by
      rw [map_neg]
      exact neg_add_cancel _
    have hcurvR :
        cotangentToDual (I := I) α R =
          curvatureAlongScalarAt (I := I) cov hcov
            (timeCurve F s) (variationField I F s) t α := by
      simpa [R] using hcurv
    rw [hvec]
    change cotangentToDual (I := I) α (-R) +
        curvatureAlongScalarAt (I := I) cov hcov
          (timeCurve F s) (variationField I F s) t α = 0
    rw [← hcurvR]
    exact hdual

/-- Smooth-surface producer for the Jacobi curvature commutator.

All fixed-coordinate scalar data required by `curvComm_surface` is produced in
`Lecture07.SurfaceCalculus`; this theorem keeps `VariationCurvCommAt` free of
coordinate-calculus hypotheses. -/
private theorem curvComm_smooth
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F (timeField I F) Vs
      (fun _ => 0) s t (0 : TangentSpace I (F (s, t))) DtsV) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Vs (s, τ)) := by
  let jet := Lecture07.SmoothSurface.coordSurfJet
    (I := I) (cov := cov) hcov1 hF s t
  exact curvComm_surface (I := I) (cov := cov) (hcov := hcov) hcov1
    (F := F) (s := s) (t := t) (Vs := Vs) (DtsV := DtsV)
    hjet
    (by simpa [jet] using jet.hmem_s)
    (by simpa [jet] using jet.hmem_t)
    jet.S jet.T jet.Ts jet.St
    (by
      intro i
      simpa [jet, paramField, Lecture07.surfaceParamField] using jet.hS i)
    (by
      intro i
      simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hT i)
    (by
      intro i
      simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hTderiv i)
    (by
      intro i
      simpa [jet, paramField, Lecture07.surfaceParamField] using jet.hSderiv i)
    (by
      intro i j k
      simpa [jet] using jet.hCs i j k)
    (by
      intro i j k
      simpa [jet] using jet.hCt i j k)
    (by simpa [jet, timeCurve, Lecture07.surfaceTimeCurve,
      timeField, Lecture07.surfaceTimeField] using jet.hvt_s)
    (by simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hvs)
    (by simpa [jet, paramCurve, Lecture07.surfaceParamCurve,
      timeField, Lecture07.surfaceTimeField] using jet.hvs_t)
    (by simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hvt)
    (by simpa [jet] using jet.hmix_raw)
    (by simpa [jet] using jet.hmix)

/-- A set-level geodesic variation gives the corresponding time-acceleration
germ at any interior point of the parameter rectangle. -/
theorem IsGeodesicVariationOn.geoGerm
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {S T : Set Real} {s t : Real}
    (hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hS : S ∈ 𝓝 s) (hT : T ∈ 𝓝 t) :
    ∀ᶠ q : Real × Real in 𝓝 (s, t),
      HasPBCovAccelAt (I := I) cov (timeCurve F q.1) q.2
        (0 : TangentSpace I (F q)) := by
  have hfst : Tendsto Prod.fst (𝓝 ((s, t) : Real × Real)) (𝓝 s) :=
    continuousAt_fst.tendsto
  have hsnd : Tendsto Prod.snd (𝓝 ((s, t) : Real × Real)) (𝓝 t) :=
    continuousAt_snd.tendsto
  filter_upwards [hfst.eventually hS, hsnd.eventually hT] with q hqS hqT
  simpa [timeCurve] using hgeo q.1 hqS q.2 hqT

/-- The time part of the surface 2-jet produced by a geodesic variation.

The remaining inputs specify the parameter derivative field `Vs = D_s T` and
its time derivative at the point. -/
private theorem timeJet_of_geo
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hgeo :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBCovAccelAt (I := I) cov (timeCurve F q.1) q.2
          (0 : TangentSpace I (F q)))
    (hVs :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBParamCovDerivAt (I := I) cov F (timeField I F)
          q.1 q.2 (Vs q))
    (hDts : HasPBTimeCovDerivAt (I := I) cov F Vs s t DtsV) :
    HasPBSurfaceCovDeriv2At (I := I) cov F (timeField I F) Vs
      (fun _ => 0) s t (0 : TangentSpace I (F (s, t))) DtsV := by
  refine
    { has_param_germ := ?_
      has_time_germ := ?_
      has_param_time := ?_
      has_time_param := hDts }
  · exact hVs
  · filter_upwards [hgeo] with q hq
    simpa [HasPBTimeCovDerivAt, HasPBCovAccelAt, timeField,
      Lecture07.surfaceTimeCurve, timeCurve, velocityAlong] using hq
  · have hparam : MDifferentiableAt 𝓘(Real, Real) I
        (Lecture07.surfaceParamCurve F t) s := by
      simpa [SmoothSurface] using hF.mdiffAt_param (I := I) s t
    exact HasPBParamCovDerivAt.zero (I := I) (cov := cov) hparam

/-- Smooth geodesic-variation curvature commutator from a parameter-derivative
surface field. -/
private theorem curvComm_geo
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hgeo :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBCovAccelAt (I := I) cov (timeCurve F q.1) q.2
          (0 : TangentSpace I (F q)))
    (hVs :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBParamCovDerivAt (I := I) cov F (timeField I F)
          q.1 q.2 (Vs q))
    (hDts : HasPBTimeCovDerivAt (I := I) cov F Vs s t DtsV) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Vs (s, τ)) :=
  curvComm_smooth (I := I) (cov := cov) (hcov := hcov) hcov1 hF
    (timeJet_of_geo (I := I) (cov := cov) hF hgeo hVs hDts)

/-- Smooth-surface torsion swap for a torsion-free connection.

The field is the canonical coordinate/frame-defined `D_s T` field supplied by
the surface-calculus producer. -/
private theorem torsionSwap_smooth
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F) :
    VariationTorsionSwapAt (I := I) cov F s t
      (fun τ => Lecture07.dsTimeField (I := I) cov F (s, τ)) := by
  constructor
  · have h := Lecture07.SmoothSurface.hasTime_param_eq_dsTime
      (I := I) (cov := cov) htf hF s t
    simpa [HasPBTimeCovDerivAt, timeCurve, variationField, paramField,
      Lecture07.surfaceTimeCurve, Lecture07.surfaceParamField] using h
  · have h := Lecture07.SmoothSurface.hasParam_dsTime
      (I := I) (cov := cov) hF s t
    simpa [HasPBParamCovDerivAt, paramCurve, paramRestrictField, timeField,
      Lecture07.surfaceParamCurve, Lecture07.surfaceTimeField] using h

/-- Smooth geodesic-variation curvature commutator with the canonical
`D_s T` field. -/
private theorem curvComm_geodesic
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {S T : Set Real} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hS : S ∈ 𝓝 s) (hT : T ∈ 𝓝 t) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Lecture07.dsTimeField (I := I) cov F (s, τ)) := by
  refine curvComm_geo (I := I) (cov := cov) (hcov := hcov)
    (DtsV := Lecture07.dtdsTimeFieldIn (I := I) cov (F (s, t)) F s t) hcov1
    hF (hgeo.geoGerm (I := I) hS hT) ?_ ?_
  · filter_upwards with q
    simpa [timeField, Lecture07.surfaceTimeField] using
      Lecture07.SmoothSurface.hasParam_dsTime
        (I := I) (cov := cov) hF q.1 q.2
  · simpa [Lecture07.HasPBTimeCovDerivAt] using
      Lecture07.SmoothSurface.hasTime_dsTime
        (I := I) (cov := cov) hcov1 hF s t

/-! ## Representative-level identities -/

/-- Representative-level torsion swap.

For a torsion-free pair with zero Lie bracket at the point, the two first
covariant derivatives agree.  This is the algebraic core of
`D_t S = D_s T`. -/
private theorem torsionSwap_rep
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {X Y : GlobalVectorField I M} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (htor : cov.torsion x (X x) (Y x) = 0)
    (hbracket : VectorField.mlieBracket I X Y x = 0) :
    (cov Y x) (X x) = (cov X x) (Y x) := by
  have htor_apply := cov.torsion_apply (I := I) (x := x) hX hY
  rw [htor_apply] at htor
  have hsub : (cov Y x) (X x) - (cov X x) (Y x) = 0 := by
    simpa [hbracket, sub_eq_add_neg] using htor
  exact sub_eq_zero.mp hsub

/-- Representative-level producer for the canonical pullback torsion swap.

If ambient fields realize the time and parameter velocity fields near the
surface point, and the torsion and bracket terms vanish there, then
`D_t S = D_s T` in the frame-defined pullback derivative API. -/
theorem torsionSwap_frame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 t : Real} {X Y : GlobalVectorField I M}
    (hγt : MDifferentiableAt 𝓘(Real, Real) I (timeCurve F s0) t)
    (hγs : MDifferentiableAt 𝓘(Real, Real) I (paramCurve F t) s0)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s0, t)))
    (hY : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) Y (F (s0, t)))
    (hTX : SurfaceFieldRealizedByAt (I := I) F (timeField I F) X (s0, t))
    (hSY : SurfaceFieldRealizedByAt (I := I) F (paramField I F) Y (s0, t))
    (htor : cov.torsion (F (s0, t)) (X (F (s0, t))) (Y (F (s0, t))) = 0)
    (hbracket : VectorField.mlieBracket I X Y (F (s0, t)) = 0) :
    VariationTorsionSwapAt (I := I) cov F s0 t
      (fun τ => (cov X (F (s0, τ))) (curveVelocity I (paramCurve F τ) s0)) := by
  let W : VectorFieldAlong I (timeCurve F s0) :=
    fun τ => (cov X (F (s0, τ))) (curveVelocity I (paramCurve F τ) s0)
  have hTX₀ : timeField I F (s0, t) = X (F (s0, t)) :=
    hTX.self_of_nhds
  have hSY₀ : paramField I F (s0, t) = Y (F (s0, t)) :=
    hSY.self_of_nhds
  have hswap_raw :
      (cov Y (F (s0, t))) (X (F (s0, t))) =
        (cov X (F (s0, t))) (Y (F (s0, t))) :=
    torsionSwap_rep (I := I) (cov := cov)
      (X := X) (Y := Y) (x := F (s0, t))
      (mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hX)
      (mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hY)
      htor hbracket
  have hswap :
      (cov Y (F (s0, t))) (curveVelocity I (timeCurve F s0) t) = W t := by
    have h := hswap_raw
    rw [← hTX₀, ← hSY₀] at h
    simpa [W, timeField, paramField, timeCurve, paramCurve] using h
  have htime :
      HasPBCovAlongAt (I := I) cov (timeCurve F s0)
        (variationField I F s0) t (W t) := by
    have hrep :=
      surfTime_frame (I := I) (cov := cov)
        (F := F) (V := paramField I F) (X := Y)
        (s0 := s0) (t := t) hγt hY hSY
    rw [← hswap]
    simpa [timeRestrictField, variationField, paramField] using hrep
  have hparam :
      HasPBCovAlongAt (I := I) cov (paramCurve F t)
        (paramRestrictField I F (timeField I F) t) s0 (W t) := by
    have hrep :=
      surfParam_frame (I := I) (cov := cov)
        (F := F) (V := timeField I F) (X := X)
        (s := s0) (t0 := t) hγs hX hTX
    simpa [W, paramRestrictField, timeField, paramCurve] using hrep
  exact ⟨htime, hparam⟩

/-- Curvature along a curve computed by smooth ambient representatives. -/
private theorem curvScalar_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hX : X (gamma t) = J t)
    (hY : Y (gamma t) = curveVelocity I gamma t)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) :
    curvatureAlongScalarAt (I := I) cov hcov gamma J t α =
      cotangentToDual (I := I) α
        (connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
          (gamma t)) := by
  simpa [curvatureAlongScalarAt, hX, hY] using
    (Riemann.CovariantDerivative.riemannCurvatureAt_apply_smooth
      (I := I) cov hcov X Y Y α)

/-- The cotangent-tested Jacobi scalar equation for the negative curvature
representative. -/
private theorem jacobiScalar_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hX : X (gamma t) = J t)
    (hY : Y (gamma t) = curveVelocity I gamma t)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) :
    cotangentToDual (I := I) α
        (-(connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
          (gamma t))) +
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0 := by
  let R : TangentSpace I (gamma t) :=
    connectionRiemannCurvatureField (I := I) cov
      (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
      (gamma t)
  change cotangentToDual (I := I) α (-R) +
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0
  rw [curvScalar_rep (I := I) (cov := cov) (hcov := hcov)
    (gamma := gamma) (J := J) (t := t) X Y hX hY α]
  have hdual :
      cotangentToDual (I := I) α (-R) + cotangentToDual (I := I) α R = 0 := by
    rw [map_neg]
    exact neg_add_cancel _
  simpa [cotangentToDual_apply] using hdual

/-- A frame-defined curvature commutator value supplies
`VariationCurvCommAt`.

The derivative witness is already in the canonical pullback API; smooth ambient
representatives are used only to identify the pointwise curvature scalar with
RicciFlower's current `riemannCurvatureAt` tensor API. -/
private theorem curvComm_frame
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {s0 t : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    {A : TangentSpace I (timeCurve F s0 t)}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hWA : HasPBCovAlongAt (I := I) cov (timeCurve F s0) W t A)
    (hA : A =
      -(connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
        (timeCurve F s0 t)))
    (hX : X (timeCurve F s0 t) = variationField I F s0 t)
    (hY : Y (timeCurve F s0 t) = curveVelocity I (timeCurve F s0) t) :
    VariationCurvCommAt (I := I) cov hcov F s0 t W := by
  refine ⟨A, hWA, ?_⟩
  intro α
  rw [hA]
  exact jacobiScalar_rep (I := I) (cov := cov) (hcov := hcov)
    (gamma := timeCurve F s0) (J := variationField I F s0) (t := t)
    X Y hX hY α

/-- A representative-level curvature commutator value supplies
`VariationCurvCommAt`. -/
private theorem curvComm_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {s0 t : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    {A : TangentSpace I (timeCurve F s0 t)}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hWA : HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov
      (timeCurve F s0) W t A)
    (hA : A =
      -(connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
        (timeCurve F s0 t)))
    (hX : X (timeCurve F s0 t) = variationField I F s0 t)
    (hY : Y (timeCurve F s0 t) = curveVelocity I (timeCurve F s0) t) :
    VariationCurvCommAt (I := I) cov hcov F s0 t W :=
  curvComm_frame (I := I) (cov := cov) (hcov := hcov)
    (F := F) (s0 := s0) (t := t) (W := W) (A := A)
    X Y hWA.toPBCov hA hX hY

/-- The formal Jacobi-field theorem for a geodesic variation.

The geometric producer of `hswap` and `hcomm` is intentionally kept separate.
For the current representative-based pullback derivative, smooth surface data
alone is not enough; see the note below. -/
theorem jacobi_of_variation
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {S T : Set Real} {s0 : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    (_hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hswap : ∀ t ∈ T, VariationTorsionSwapAt (I := I) cov F s0 t W)
    (hcomm : ∀ t ∈ T, VariationCurvCommAt (I := I) cov hcov F s0 t W) :
    IsJacobiFieldOn (I := I) cov hcov (timeCurve F s0)
      (variationField I F s0) T := by
  intro t ht
  rcases hcomm t ht with ⟨A, hWA, hscalar⟩
  refine ⟨A, ?_, hscalar⟩
  exact ⟨W, (hswap t ht).1, hWA⟩

/-- A smooth torsion-free geodesic variation has a Jacobi variation field. -/
theorem jacobi_of_smooth_geodesic_variation
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {S T : Set Real} {s0 : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hS : S ∈ 𝓝 s0) (hTopen : IsOpen T) :
    IsJacobiFieldOn (I := I) cov hcov
      (timeCurve F s0) (variationField I F s0) T := by
  let W : VectorFieldAlong I (timeCurve F s0) :=
    fun τ => Lecture07.dsTimeField (I := I) cov F (s0, τ)
  refine jacobi_of_variation (I := I) (cov := cov) (hcov := hcov)
    (F := F) (S := S) (T := T) (s0 := s0) (W := W)
    hgeo ?_ ?_
  · intro t _ht
    exact torsionSwap_smooth (I := I) (cov := cov) htf hF
  · intro t ht
    exact curvComm_geodesic (I := I) (cov := cov) (hcov := hcov)
      hcov1 hF hgeo hS (hTopen.mem_nhds ht)

/-- Levi-Civita specialization of the smooth geodesic-variation Jacobi theorem. -/
theorem jacobi_of_lc_variation
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} {S T : Set Real} {s0 : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F S T)
    (hS : S ∈ 𝓝 s0) (hTopen : IsOpen T) :
    IsJacobiFieldOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) g)
      (timeCurve F s0) (variationField I F s0) T := by
  let cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov ∞ :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g
  have hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (1 : WithTop ℕ∞) :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) g
  have htf : LeviCivita.IsTorsionFree (I := I) cov :=
    LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree (I := I) g
  exact jacobi_of_smooth_geodesic_variation (I := I)
    (cov := cov) (hcov := hcov) hcov1 htf hF hgeo hS hTopen

/-!
The smooth-surface producer above is the canonical route for Jacobi fields.
The representative-level lemmas below are retained as compatibility tools for
older arguments that already provide ambient section representatives.
-/

end GlobalGeometry
end RicciFlower
