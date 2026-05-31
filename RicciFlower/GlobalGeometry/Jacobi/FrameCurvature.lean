import RicciFlower.GlobalGeometry.Jacobi.Surface

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Frame curvature algebra for Jacobi fields

Fixed-frame curvature-coordinate expansion and pointwise Jacobi-field predicates.
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
theorem gammaT_deriv_s_mat
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
theorem gammaS_deriv_t_mat
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
    {ι : Type*} [Fintype ι]
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
    {ι : Type*} [Fintype ι]
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

end GlobalGeometry
end RicciFlower
