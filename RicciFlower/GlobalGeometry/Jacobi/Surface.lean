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
# Two-parameter variation surfaces

Surface, variation-field, and pullback representative adapters used by Jacobi-field proofs.
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
theorem surfTime_frame
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
theorem surfParam_frame
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

end GlobalGeometry
end RicciFlower
