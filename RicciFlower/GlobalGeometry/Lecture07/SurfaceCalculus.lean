import RicciFlower.GlobalGeometry.Lecture07.CoordinateEquation
import RicciFlower.Curvature.Components.Christoffel
import RicciFlower.LeviCivita.Torsion
import RicciFlower.VectorBundle.PartialMfderiv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Surface calculus in fixed coordinates

This file is the producer layer for two-parameter coordinate calculations used
by Jacobi fields.  It keeps the public Jacobi predicates intrinsic and proves
the scalar fixed-coordinate data they consume from smooth surfaces.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Filter RicciFlower.Coordinates
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-! ## Smooth surfaces and fixed-coordinate source control -/

/-- A smooth two-parameter surface.  The first coordinate is the variation
parameter and the second coordinate is curve time. -/
def SmoothSurface (I : ModelWithCorners Real E H) (F : Surface M) : Prop :=
  ContMDiff 𝓘(Real, Real × Real) I ∞ F

/-- A smooth surface is continuous at each parameter pair. -/
theorem SmoothSurface.continuousAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (p : Real × Real) :
    ContinuousAt F p := by
  exact hF.continuous.continuousAt

/-- Restricting a smooth surface to a fixed-time parameter line is smooth at
the selected parameter. -/
theorem SmoothSurface.contMDiffAt_param {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContMDiffAt 𝓘(Real, Real) I ∞ (surfaceParamCurve F t) s := by
  have hline :
      ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real × Real) ∞
        (fun σ : Real => (σ, t)) s := by
    simpa using
      ((contDiffAt_id.prodMk contDiffAt_const :
        ContDiffAt Real ∞ (fun σ : Real => (σ, t)) s).contMDiffAt)
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞
      F ((fun σ : Real => (σ, t)) s) := by
    simpa using hF.contMDiffAt (x := (s, t))
  simpa [surfaceParamCurve] using
    (hFat.comp s hline)

/-- Restricting a smooth surface to a fixed-parameter time line is smooth at
the selected time. -/
theorem SmoothSurface.contMDiffAt_time {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContMDiffAt 𝓘(Real, Real) I ∞ (surfaceTimeCurve F s) t := by
  have hline :
      ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real × Real) ∞
        (fun τ : Real => (s, τ)) t := by
    simpa using
      ((contDiffAt_const.prodMk contDiffAt_id :
        ContDiffAt Real ∞ (fun τ : Real => (s, τ)) t).contMDiffAt)
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞
      F ((fun τ : Real => (s, τ)) t) := by
    simpa using hF.contMDiffAt (x := (s, t))
  simpa [surfaceTimeCurve] using
    (hFat.comp t hline)

/-- A smooth surface is differentiable along each fixed-time parameter line. -/
theorem SmoothSurface.mdiffAt_param {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    MDifferentiableAt 𝓘(Real, Real) I (surfaceParamCurve F t) s :=
  (hF.contMDiffAt_param s t).mdifferentiableAt (by simp)

/-- A smooth surface is differentiable along each fixed-parameter time line. -/
theorem SmoothSurface.mdiffAt_time {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
  (hF.contMDiffAt_time s t).mdifferentiableAt (by simp)

/-! ## Fixed-coordinate velocity coefficients -/

/-- Fixed-center coordinate expression of a surface. -/
def surfaceCoord (x₀ : M) (F : Surface M) (p : Real × Real) : E :=
  extChartAt I x₀ (F p)

/-- Fixed-center coordinate component of a surface. -/
def surfaceCoordComp (x₀ : M) (F : Surface M) (p : Real × Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (Module.finBasis Real E).repr (surfaceCoord (I := I) x₀ F p) i

/-- The fixed-center coordinate expression of a smooth surface is smooth at
the center parameter pair. -/
theorem SmoothSurface.surfaceCoord_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContMDiffAt 𝓘(Real, Real × Real) 𝓘(Real, E) ∞
      (surfaceCoord (I := I) (F (s, t)) F) (s, t) := by
  have hchart : ContMDiffAt I 𝓘(Real, E) ∞
      (extChartAt I (F (s, t))) (F (s, t)) :=
    contMDiffAt_extChartAt (I := I) (x := F (s, t))
  simpa [surfaceCoord] using
    (hchart.comp (s, t) (hF.contMDiffAt (x := (s, t))))

/-- Fixed-center coordinate components of a smooth surface are smooth at the
center parameter pair. -/
theorem SmoothSurface.surfaceCoordComp_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt 𝓘(Real, Real × Real) 𝓘(Real, Real) ∞
      (fun p : Real × Real =>
        surfaceCoordComp (I := I) (F (s, t)) F p i) (s, t) := by
  have hcoord := hF.surfaceCoord_contMDiffAt (I := I) s t
  have hlin : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun y : E => (Module.finBasis Real E).repr y i) :=
    (LinearMap.toContinuousLinearMap
      ((Module.finBasis Real E).coord i)).contMDiff
  simpa [surfaceCoordComp] using
    hlin.contMDiffAt.comp (s, t) hcoord

/-- Fixed-center coordinate expression of a smooth surface is smooth at
`(s,t)` whenever the surface point lies in the fixed coordinate frame. -/
theorem SmoothSurface.coordAt_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    ContMDiffAt 𝓘(Real, Real × Real) 𝓘(Real, E) ∞
      (surfaceCoord (I := I) x₀ F) (s, t) := by
  have hx_chart : F (s, t) ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hchart : ContMDiffAt I 𝓘(Real, E) ∞
      (extChartAt I x₀) (F (s, t)) :=
    contMDiffAt_extChartAt' (I := I) hx_chart
  simpa [surfaceCoord] using
    hchart.comp (s, t) (hF.contMDiffAt (x := (s, t)))

/-- Fixed-center coordinate components of a smooth surface are smooth at
`(s,t)` whenever the surface point lies in the fixed coordinate frame. -/
theorem SmoothSurface.coordCompAt_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    ContDiffAt Real ∞
      (fun p : Real × Real => surfaceCoordComp (I := I) x₀ F p i) (s, t) := by
  have hcoord := hF.coordAt_contMDiffAt (I := I) hx
  have hlin : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun y : E => (Module.finBasis Real E).repr y i) :=
    (LinearMap.toContinuousLinearMap
      ((Module.finBasis Real E).coord i)).contMDiff
  simpa [surfaceCoordComp] using
    (hlin.contMDiffAt.comp (s, t) hcoord).contDiffAt

/-- The fixed-center coordinate expression of a smooth surface is smooth along
a fixed-time parameter line through the chart center. -/
theorem SmoothSurface.surfaceCoord_param_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
      (fun σ : Real => surfaceCoord (I := I) (F (s, t)) F (σ, t)) s := by
  have hchart : ContMDiffAt I 𝓘(Real, E) ∞
      (extChartAt I (F (s, t))) (F (s, t)) :=
    contMDiffAt_extChartAt (I := I) (x := F (s, t))
  simpa [surfaceCoord, surfaceParamCurve] using
    (hchart.comp s (hF.contMDiffAt_param s t))

/-- The fixed-center coordinate expression of a smooth surface is smooth along
a fixed-parameter time line through the chart center. -/
theorem SmoothSurface.surfaceCoord_time_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
      (fun τ : Real => surfaceCoord (I := I) (F (s, t)) F (s, τ)) t := by
  have hchart : ContMDiffAt I 𝓘(Real, E) ∞
      (extChartAt I (F (s, t))) (F (s, t)) :=
    contMDiffAt_extChartAt (I := I) (x := F (s, t))
  simpa [surfaceCoord, surfaceTimeCurve] using
    (hchart.comp t (hF.contMDiffAt_time s t))

/-- Fixed-center coordinate components of a smooth surface are smooth along a
fixed-time parameter line. -/
theorem SmoothSurface.surfaceCoordComp_param_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞
      (fun σ : Real => surfaceCoordComp (I := I) (F (s, t)) F (σ, t) i) s := by
  have hcoord := hF.surfaceCoord_param_contMDiffAt (I := I) s t
  have hlin : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun y : E => (Module.finBasis Real E).repr y i) :=
    (LinearMap.toContinuousLinearMap
      ((Module.finBasis Real E).coord i)).contMDiff
  simpa [surfaceCoordComp] using hlin.contMDiffAt.comp s hcoord

/-- Fixed-center coordinate components of a smooth surface are smooth along a
fixed-parameter time line. -/
theorem SmoothSurface.surfaceCoordComp_time_contMDiffAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞
      (fun τ : Real => surfaceCoordComp (I := I) (F (s, t)) F (s, τ) i) t := by
  have hcoord := hF.surfaceCoord_time_contMDiffAt (I := I) s t
  have hlin : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun y : E => (Module.finBasis Real E).repr y i) :=
    (LinearMap.toContinuousLinearMap
      ((Module.finBasis Real E).coord i)).contMDiff
  simpa [surfaceCoordComp] using hlin.contMDiffAt.comp t hcoord

/-- The time-direction velocity field of a two-parameter surface. -/
def surfaceTimeField (I : ModelWithCorners Real E H) (F : Surface M) :
    SurfaceFieldAlong I F :=
  fun p => curveVelocity I (surfaceTimeCurve F p.1) p.2

/-- The parameter-direction velocity field of a two-parameter surface. -/
def surfaceParamField (I : ModelWithCorners Real E H) (F : Surface M) :
    SurfaceFieldAlong I F :=
  fun p => curveVelocity I (surfaceParamCurve F p.2) p.1

/-- Fixed-coordinate coefficient of the time-direction velocity. -/
def timeCoeff (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (coordinateFrameAt_toBasis (I := I) x₀).repr
    (surfaceTimeField (I := I) F (s, t)) i

/-- Fixed-coordinate coefficient of the parameter-direction velocity. -/
def paramCoeff (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (coordinateFrameAt_toBasis (I := I) x₀).repr
    (surfaceParamField (I := I) F (s, t)) i

/-- Fixed-frame coefficient of the time-direction velocity, evaluated at a
surface point.  This is the coefficient function used by the surface
commutator producer. -/
def timeFrameCoeff (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i (F (s, t))
    (surfaceTimeField (I := I) F (s, t))

/-- Fixed-frame coefficient of the parameter-direction velocity, evaluated at a
surface point. -/
def paramFrameCoeff (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i (F (s, t))
    (surfaceParamField (I := I) F (s, t))

/-- Time partial of one scalar fixed-coordinate surface component. -/
def coordTimeDeriv (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (fderiv Real (fun p : Real × Real =>
    surfaceCoordComp (I := I) x₀ F p i) (s, t)) (0, (1 : Real))

/-- Parameter partial of one scalar fixed-coordinate surface component. -/
def coordParamDeriv (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (fderiv Real (fun p : Real × Real =>
    surfaceCoordComp (I := I) x₀ F p i) (s, t)) ((1 : Real), 0)

/-- Parameter derivative of the time partial of one scalar coordinate
component. -/
def coordTs (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (fderiv Real
    (fun p : Real × Real => coordTimeDeriv (I := I) x₀ F p.1 p.2 i)
    (s, t)) ((1 : Real), 0)

/-- Time derivative of the parameter partial of one scalar coordinate
component. -/
def coordSt (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (fderiv Real
    (fun p : Real × Real => coordParamDeriv (I := I) x₀ F p.1 p.2 i)
    (s, t)) (0, (1 : Real))

/-- Time derivative of the time partial of one scalar coordinate component. -/
def coordTt (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (fderiv Real
    (fun p : Real × Real => coordTimeDeriv (I := I) x₀ F p.1 p.2 i)
    (s, t)) (0, (1 : Real))

/-- Parameter derivative of the time-time partial of one scalar coordinate
component. -/
def coordVst (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (fderiv Real
    (fun p : Real × Real => coordTt (I := I) x₀ F p.1 p.2 i)
    (s, t)) ((1 : Real), 0)

/-- Time derivative of the parameter-time partial of one scalar coordinate
component. -/
def coordVts (x₀ : M) (F : Surface M) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  (fderiv Real
    (fun p : Real × Real => coordTs (I := I) x₀ F p.1 p.2 i)
    (s, t)) (0, (1 : Real))

/-- At the coordinate center, the local-frame coefficient of the time field is
the coordinate-basis coefficient. -/
theorem timeFrameCoeff_self
    (F : Surface M) (s t : Real) (i : CoordinateIdx (𝕜 := Real) E) :
    timeFrameCoeff (I := I) (F (s, t)) F s t i =
      timeCoeff (I := I) (F (s, t)) F s t i := by
  rw [timeFrameCoeff, timeCoeff]
  simpa using
    coordinateFrameAt_coeff_eq_toBasis_coord (I := I) (F (s, t))
      (surfaceTimeField (I := I) F (s, t)) i

/-- At the coordinate center, the local-frame coefficient of the parameter
field is the coordinate-basis coefficient. -/
theorem paramFrameCoeff_self
    (F : Surface M) (s t : Real) (i : CoordinateIdx (𝕜 := Real) E) :
    paramFrameCoeff (I := I) (F (s, t)) F s t i =
      paramCoeff (I := I) (F (s, t)) F s t i := by
  rw [paramFrameCoeff, paramCoeff]
  simpa using
    coordinateFrameAt_coeff_eq_toBasis_coord (I := I) (F (s, t))
      (surfaceParamField (I := I) F (s, t)) i

/-- In a fixed coordinate frame, the time-velocity coefficient is the
corresponding model coordinate of the derivative of the fixed chart expression
of the surface along the time line. -/
theorem SmoothSurface.timeFrameCoeff_eq_coordDeriv {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    timeFrameCoeff (I := I) x₀ F s t i =
      (Module.finBasis Real E).repr
        ((mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (fun τ : Real => surfaceCoord (I := I) x₀ F (s, τ)) t)
          (1 : TangentSpace 𝓘(Real, Real) t)) i := by
  have hx_chart : F (s, t) ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hchart : MDifferentiableAt I 𝓘(Real, E) (extChartAt I x₀) (F (s, t)) :=
    mdifferentiableAt_extChartAt (I := I) (x := x₀) hx_chart
  have hline : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    hF.mdiffAt_time s t
  have hchain :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          ((extChartAt I x₀) ∘ surfaceTimeCurve F s) t =
        (mfderiv I 𝓘(Real, E) (extChartAt I x₀) (F (s, t))).comp
          (mfderiv 𝓘(Real, Real) I (surfaceTimeCurve F s) t) := by
    simpa [surfaceTimeCurve] using
      (mfderiv_comp (I := 𝓘(Real, Real)) (I' := I) (I'' := 𝓘(Real, E))
        (x := t) hchart hline)
  rw [timeFrameCoeff, surfaceTimeField, curveVelocity]
  rw [coordCoeff_eq_chart (I := I) hx]
  change
    (Module.finBasis Real E).repr
        ((mfderiv I 𝓘(Real, E) (extChartAt I x₀) (F (s, t)))
          ((mfderiv 𝓘(Real, Real) I (surfaceTimeCurve F s) t)
            (1 : TangentSpace 𝓘(Real, Real) t))) i =
      (Module.finBasis Real E).repr
        ((mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          ((extChartAt I x₀) ∘ surfaceTimeCurve F s) t)
          (1 : TangentSpace 𝓘(Real, Real) t)) i
  rw [hchain]
  rfl

/-- In a fixed coordinate frame, the parameter-velocity coefficient is the
corresponding model coordinate of the derivative of the fixed chart expression
of the surface along the parameter line. -/
theorem SmoothSurface.paramFrameCoeff_eq_coordDeriv {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    paramFrameCoeff (I := I) x₀ F s t i =
      (Module.finBasis Real E).repr
        ((mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (fun σ : Real => surfaceCoord (I := I) x₀ F (σ, t)) s)
          (1 : TangentSpace 𝓘(Real, Real) s)) i := by
  have hx_chart : F (s, t) ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hchart : MDifferentiableAt I 𝓘(Real, E) (extChartAt I x₀) (F (s, t)) :=
    mdifferentiableAt_extChartAt (I := I) (x := x₀) hx_chart
  have hline : MDifferentiableAt 𝓘(Real, Real) I (surfaceParamCurve F t) s :=
    hF.mdiffAt_param s t
  have hchain :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          ((extChartAt I x₀) ∘ surfaceParamCurve F t) s =
        (mfderiv I 𝓘(Real, E) (extChartAt I x₀) (F (s, t))).comp
          (mfderiv 𝓘(Real, Real) I (surfaceParamCurve F t) s) := by
    simpa [surfaceParamCurve] using
      (mfderiv_comp (I := 𝓘(Real, Real)) (I' := I) (I'' := 𝓘(Real, E))
        (x := s) hchart hline)
  rw [paramFrameCoeff, surfaceParamField, curveVelocity]
  rw [coordCoeff_eq_chart (I := I) hx]
  change
    (Module.finBasis Real E).repr
        ((mfderiv I 𝓘(Real, E) (extChartAt I x₀) (F (s, t)))
          ((mfderiv 𝓘(Real, Real) I (surfaceParamCurve F t) s)
            (1 : TangentSpace 𝓘(Real, Real) s))) i =
      (Module.finBasis Real E).repr
        ((mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          ((extChartAt I x₀) ∘ surfaceParamCurve F t) s)
          (1 : TangentSpace 𝓘(Real, Real) s)) i
  rw [hchain]
  rfl

/-- In a fixed coordinate frame, the time-velocity coefficient is the vertical
partial derivative of the fixed-center coordinate component. -/
theorem SmoothSurface.timeFrameCoeff_eq_coordTimeDeriv {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    timeFrameCoeff (I := I) x₀ F s t i =
      coordTimeDeriv (I := I) x₀ F s t i := by
  let L : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i)
  let g : Real -> E := fun τ => surfaceCoord (I := I) x₀ F (s, τ)
  have hL_smooth : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun y : E => L y) :=
    L.contMDiff
  have hL : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
      (fun y : E => L y) (g t) :=
    hL_smooth.contMDiffAt.mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hline : ContMDiffAt 𝓘(Real, Real)
      𝓘(Real, Real × Real) ∞
      (fun τ : Real => (s, τ)) t := by
    simpa using
      ((contDiffAt_const.prodMk contDiffAt_id :
        ContDiffAt Real ∞ (fun τ : Real => (s, τ)) t).contMDiffAt)
  have hg : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) g t :=
    ((hF.coordAt_contMDiffAt (I := I) hx).comp t hline).mdifferentiableAt
      (by simp)
  have hscalar : HasDerivAt
      (fun τ : Real => surfaceCoordComp (I := I) x₀ F (s, τ) i)
      (coordTimeDeriv (I := I) x₀ F s t i) t := by
    have hdiff : DifferentiableAt Real
        (fun p : Real × Real => surfaceCoordComp (I := I) x₀ F p i) (s, t) :=
      (hF.coordCompAt_contMDiffAt (I := I) hx i).differentiableAt
        (by simp)
    exact modelLine_snd_hasDerivAt (A := fun p : Real × Real =>
      surfaceCoordComp (I := I) x₀ F p i) hdiff
  have hmf := hscalar.hasFDerivAt.hasMFDerivAt.mfderiv
  have hmf_apply :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun τ : Real => surfaceCoordComp (I := I) x₀ F (s, τ) i) t)
          (1 : TangentSpace 𝓘(Real, Real) t) =
        coordTimeDeriv (I := I) x₀ F s t i := by
    rw [hmf]
    exact ContinuousLinearMap.toSpanSingleton_apply_one
      (R₁ := Real) (x := coordTimeDeriv (I := I) x₀ F s t i)
  have hcomp :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun τ : Real => surfaceCoordComp (I := I) x₀ F (s, τ) i) t)
          (1 : TangentSpace 𝓘(Real, Real) t) =
        (Module.finBasis Real E).repr
          ((mfderiv 𝓘(Real, Real) 𝓘(Real, E) g t)
            (1 : TangentSpace 𝓘(Real, Real) t)) i := by
    have h :=
      mfderiv_comp_apply
        (I := 𝓘(Real, Real)) (I' := 𝓘(Real, E))
        (I'' := 𝓘(Real, Real))
        (g := fun y : E => L y) (f := g)
        (x := t) (v := (1 : TangentSpace 𝓘(Real, Real) t))
        hL hg
    have heq :
        (fun τ : Real => surfaceCoordComp (I := I) x₀ F (s, τ) i) =
          (fun y : E => L y) ∘ g := by
      funext τ
      simp [L, g, surfaceCoordComp]
    rw [heq]
    have hLmf :
        mfderiv 𝓘(Real, E) 𝓘(Real, Real) (fun y : E => L y) (g t) = L := by
      rw [mfderiv_eq_fderiv (𝕜 := Real) (f := fun y : E => L y) (x := g t)]
      exact ContinuousLinearMap.fderiv L
    rw [hLmf] at h
    simpa [L] using h
  rw [hF.timeFrameCoeff_eq_coordDeriv (I := I) hx i]
  rw [← hcomp]
  exact hmf_apply

/-- In a fixed coordinate frame, the parameter-velocity coefficient is the
horizontal partial derivative of the fixed-center coordinate component. -/
theorem SmoothSurface.paramFrameCoeff_eq_coordParamDeriv {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    paramFrameCoeff (I := I) x₀ F s t i =
      coordParamDeriv (I := I) x₀ F s t i := by
  let L : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i)
  let g : Real -> E := fun σ => surfaceCoord (I := I) x₀ F (σ, t)
  have hL_smooth : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun y : E => L y) :=
    L.contMDiff
  have hL : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
      (fun y : E => L y) (g s) :=
    hL_smooth.contMDiffAt.mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hline : ContMDiffAt 𝓘(Real, Real)
      𝓘(Real, Real × Real) ∞
      (fun σ : Real => (σ, t)) s := by
    simpa using
      ((contDiffAt_id.prodMk contDiffAt_const :
        ContDiffAt Real ∞ (fun σ : Real => (σ, t)) s).contMDiffAt)
  have hg : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) g s :=
    ((hF.coordAt_contMDiffAt (I := I) hx).comp s hline).mdifferentiableAt
      (by simp)
  have hscalar : HasDerivAt
      (fun σ : Real => surfaceCoordComp (I := I) x₀ F (σ, t) i)
      (coordParamDeriv (I := I) x₀ F s t i) s := by
    have hdiff : DifferentiableAt Real
        (fun p : Real × Real => surfaceCoordComp (I := I) x₀ F p i) (s, t) :=
      (hF.coordCompAt_contMDiffAt (I := I) hx i).differentiableAt
        (by simp)
    exact modelLine_fst_hasDerivAt (A := fun p : Real × Real =>
      surfaceCoordComp (I := I) x₀ F p i) hdiff
  have hmf := hscalar.hasFDerivAt.hasMFDerivAt.mfderiv
  have hmf_apply :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun σ : Real => surfaceCoordComp (I := I) x₀ F (σ, t) i) s)
          (1 : TangentSpace 𝓘(Real, Real) s) =
        coordParamDeriv (I := I) x₀ F s t i := by
    rw [hmf]
    exact ContinuousLinearMap.toSpanSingleton_apply_one
      (R₁ := Real) (x := coordParamDeriv (I := I) x₀ F s t i)
  have hcomp :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun σ : Real => surfaceCoordComp (I := I) x₀ F (σ, t) i) s)
          (1 : TangentSpace 𝓘(Real, Real) s) =
        (Module.finBasis Real E).repr
          ((mfderiv 𝓘(Real, Real) 𝓘(Real, E) g s)
            (1 : TangentSpace 𝓘(Real, Real) s)) i := by
    have h :=
      mfderiv_comp_apply
        (I := 𝓘(Real, Real)) (I' := 𝓘(Real, E))
        (I'' := 𝓘(Real, Real))
        (g := fun y : E => L y) (f := g)
        (x := s) (v := (1 : TangentSpace 𝓘(Real, Real) s))
        hL hg
    have heq :
        (fun σ : Real => surfaceCoordComp (I := I) x₀ F (σ, t) i) =
          (fun y : E => L y) ∘ g := by
      funext σ
      simp [L, g, surfaceCoordComp]
    rw [heq]
    have hLmf :
        mfderiv 𝓘(Real, E) 𝓘(Real, Real) (fun y : E => L y) (g s) = L := by
      rw [mfderiv_eq_fderiv (𝕜 := Real) (f := fun y : E => L y) (x := g s)]
      exact ContinuousLinearMap.fderiv L
    rw [hLmf] at h
    simpa [L] using h
  rw [hF.paramFrameCoeff_eq_coordDeriv (I := I) hx i]
  rw [← hcomp]
  exact hmf_apply

section ChristoffelChain

variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Chain rule for a coordinate Christoffel coefficient along the
surface-parameter line.  The derivative is expressed by contracting the
coordinate derivative with the parameter-direction velocity coefficients. -/
theorem SmoothSurface.christoffel_param_hasDerivAt
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real)
    (S : CoordinateIdx (𝕜 := Real) E -> Real)
    (hS : ∀ a : CoordinateIdx (𝕜 := Real) E,
      paramFrameCoeff (I := I) (F (s, t)) F s t a = S a)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun σ : Real =>
        Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (σ, t)))
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        S a * Realized.christoffelCoordDerivAt (I := I) cov
          (F (s, t)) a i j k) s := by
  classical
  let x : M := F (s, t)
  let f : M -> Real :=
    Realized.christoffelCoordFun (I := I) cov x i j k
  let v : TangentSpace I x := curveVelocity I (surfaceParamCurve F t) s
  let b := coordinateFrameAt_toBasis (I := I) x
  have hf : MDifferentiableAt I 𝓘(Real, Real) f x := by
    simpa [f, x] using
      Realized.christoffelCoordFun_mdiffAt_one (I := I) cov hcov x i j k
  have hcurve : MDifferentiableAt 𝓘(Real, Real) I
      (surfaceParamCurve F t) s :=
    hF.mdiffAt_param s t
  have hderiv :
      HasDerivAt (fun σ : Real => f (surfaceParamCurve F t σ))
        (extDerivFun (I := I) f x v) s := by
    simpa [f, x, v, surfaceParamCurve] using
      extDerivFun_along_curve_eq_deriv (I := I) (f := f)
        (gamma := surfaceParamCurve F t) (t := s) hf hcurve
  have hrepr : ∀ a : CoordinateIdx (𝕜 := Real) E, b.repr v a = S a := by
    intro a
    rw [← hS a]
    simpa [b, v, x, paramFrameCoeff, surfaceParamField, surfaceParamCurve] using
      (coordinateFrameAt_coeff_eq_toBasis_coord (I := I) x v a).symm
  have hv :
      v = ∑ a : CoordinateIdx (𝕜 := Real) E,
        S a • coordinateFrameAt (I := I) x a x := by
    calc
      v = ∑ a : CoordinateIdx (𝕜 := Real) E, b.repr v a • b a := by
        exact (b.sum_repr v).symm
      _ = ∑ a : CoordinateIdx (𝕜 := Real) E,
          S a • coordinateFrameAt (I := I) x a x := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hrepr a]
        simp [b, coordinateFrameAt_toBasis_apply]
  have hvalue :
      extDerivFun (I := I) f x v =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          S a * Realized.christoffelCoordDerivAt (I := I) cov x a i j k := by
    rw [hv]
    simp [f, Realized.christoffelCoordDerivAt, extDerivFun, map_sum,
      map_smul, smul_eq_mul]
  simpa [f, x, surfaceParamCurve, hvalue] using hderiv

/-- Chain rule for a coordinate Christoffel coefficient along the
surface-time line. -/
theorem SmoothSurface.christoffel_time_hasDerivAt
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real)
    (T : CoordinateIdx (𝕜 := Real) E -> Real)
    (hT : ∀ a : CoordinateIdx (𝕜 := Real) E,
      timeFrameCoeff (I := I) (F (s, t)) F s t a = T a)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real =>
        Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (s, τ)))
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        T a * Realized.christoffelCoordDerivAt (I := I) cov
          (F (s, t)) a i j k) t := by
  classical
  let x : M := F (s, t)
  let f : M -> Real :=
    Realized.christoffelCoordFun (I := I) cov x i j k
  let v : TangentSpace I x := curveVelocity I (surfaceTimeCurve F s) t
  let b := coordinateFrameAt_toBasis (I := I) x
  have hf : MDifferentiableAt I 𝓘(Real, Real) f x := by
    simpa [f, x] using
      Realized.christoffelCoordFun_mdiffAt_one (I := I) cov hcov x i j k
  have hcurve : MDifferentiableAt 𝓘(Real, Real) I
      (surfaceTimeCurve F s) t :=
    hF.mdiffAt_time s t
  have hderiv :
      HasDerivAt (fun τ : Real => f (surfaceTimeCurve F s τ))
        (extDerivFun (I := I) f x v) t := by
    simpa [f, x, v, surfaceTimeCurve] using
      extDerivFun_along_curve_eq_deriv (I := I) (f := f)
        (gamma := surfaceTimeCurve F s) (t := t) hf hcurve
  have hrepr : ∀ a : CoordinateIdx (𝕜 := Real) E, b.repr v a = T a := by
    intro a
    rw [← hT a]
    simpa [b, v, x, timeFrameCoeff, surfaceTimeField, surfaceTimeCurve] using
      (coordinateFrameAt_coeff_eq_toBasis_coord (I := I) x v a).symm
  have hv :
      v = ∑ a : CoordinateIdx (𝕜 := Real) E,
        T a • coordinateFrameAt (I := I) x a x := by
    calc
      v = ∑ a : CoordinateIdx (𝕜 := Real) E, b.repr v a • b a := by
        exact (b.sum_repr v).symm
      _ = ∑ a : CoordinateIdx (𝕜 := Real) E,
          T a • coordinateFrameAt (I := I) x a x := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hrepr a]
        simp [b, coordinateFrameAt_toBasis_apply]
  have hvalue :
      extDerivFun (I := I) f x v =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          T a * Realized.christoffelCoordDerivAt (I := I) cov x a i j k := by
    rw [hv]
    simp [f, Realized.christoffelCoordDerivAt, extDerivFun, map_sum,
      map_smul, smul_eq_mul]
  simpa [f, x, surfaceTimeCurve, hvalue] using hderiv

end ChristoffelChain

/-- If a surface point is in a fixed coordinate-frame domain, nearby points on
the parameter line remain in that domain. -/
theorem SmoothSurface.coordMem_param_of_mem {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ coordinateFrameSet (I := I) x₀ := by
  have hU : IsOpen (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameSet_open (I := I) x₀
  have hline : ContinuousAt (fun σ : Real => (σ, t)) s :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hFst : ContinuousAt F ((fun σ : Real => (σ, t)) s) := by
    simpa using SmoothSurface.continuousAt (I := I) hF (s, t)
  have hcomp : ContinuousAt (fun σ : Real => F (σ, t)) s :=
    ContinuousAt.comp (x := s) (f := fun σ : Real => (σ, t)) hFst hline
  exact hcomp.eventually_mem (hU.mem_nhds hx)

/-- If a surface point is in a fixed coordinate-frame domain, nearby points on
the time line remain in that domain. -/
theorem SmoothSurface.coordMem_time_of_mem {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ coordinateFrameSet (I := I) x₀ := by
  have hU : IsOpen (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameSet_open (I := I) x₀
  have hline : ContinuousAt (fun τ : Real => (s, τ)) t :=
    ContinuousAt.prodMk continuousAt_const continuousAt_id
  have hFst : ContinuousAt F ((fun τ : Real => (s, τ)) t) := by
    simpa using SmoothSurface.continuousAt (I := I) hF (s, t)
  have hcomp : ContinuousAt (fun τ : Real => F (s, τ)) t :=
    ContinuousAt.comp (x := t) (f := fun τ : Real => (s, τ)) hFst hline
  exact hcomp.eventually_mem (hU.mem_nhds hx)

/-- Along a fixed-time parameter line, a smooth surface eventually remains in
the coordinate frame centered at the base point. -/
theorem SmoothSurface.coordMem_param {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ coordinateFrameSet (I := I) (F (s, t)) := by
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  exact hF.coordMem_param_of_mem (I := I) hx

/-- Along a fixed-parameter time line, a smooth surface eventually remains in
the coordinate frame centered at the base point. -/
theorem SmoothSurface.coordMem_time {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ coordinateFrameSet (I := I) (F (s, t)) := by
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  exact hF.coordMem_time_of_mem (I := I) hx

/-- Both coordinate-source germs needed for the fixed-coordinate surface
calculus at `(s,t)`. -/
theorem SmoothSurface.coord_mem {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    (∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ coordinateFrameSet (I := I) (F (s, t))) ∧
    (∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ coordinateFrameSet (I := I) (F (s, t))) :=
  ⟨hF.coordMem_param s t, hF.coordMem_time s t⟩

/-! ## Velocity coefficient derivative producers -/

/-- Parameter derivative of the time-velocity frame coefficient. -/
theorem SmoothSurface.timeFrameCoeff_param_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun σ : Real => timeFrameCoeff (I := I) (F (s, t)) F σ t i)
      (coordTs (I := I) (F (s, t)) F s t i) s := by
  let x₀ : M := F (s, t)
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordTimeDeriv (I := I) x₀ F p.1 p.2 i
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ, x₀] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) (0, (1 : Real))) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordTimeDeriv, x₀] using hD
  have hderiv :
      HasDerivAt (fun σ : Real => A (σ, t))
        (coordTs (I := I) x₀ F s t i) s := by
    have hdiff : DifferentiableAt Real A (s, t) :=
      hA.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    simpa [A, coordTs, x₀] using
      modelLine_fst_hasDerivAt (A := A) (s := s) (t := t) hdiff
  have heq :
      (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ t i)
        =ᶠ[𝓝 s] fun σ : Real => A (σ, t) := by
    filter_upwards [hF.coordMem_param (I := I) s t] with σ hσ
    simpa [A, x₀] using
      hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hσ i
  simpa [x₀] using hderiv.congr_of_eventuallyEq heq

/-- Time derivative of the parameter-velocity frame coefficient. -/
theorem SmoothSurface.paramFrameCoeff_time_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real => paramFrameCoeff (I := I) (F (s, t)) F s τ i)
      (coordSt (I := I) (F (s, t)) F s t i) t := by
  let x₀ : M := F (s, t)
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordParamDeriv (I := I) x₀ F p.1 p.2 i
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ, x₀] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) ((1 : Real), 0)) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordParamDeriv, x₀] using hD
  have hderiv :
      HasDerivAt (fun τ : Real => A (s, τ))
        (coordSt (I := I) x₀ F s t i) t := by
    have hdiff : DifferentiableAt Real A (s, t) :=
      hA.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    simpa [A, coordSt, x₀] using
      modelLine_snd_hasDerivAt (A := A) (s := s) (t := t) hdiff
  have heq :
      (fun τ : Real => paramFrameCoeff (I := I) x₀ F s τ i)
        =ᶠ[𝓝 t] fun τ : Real => A (s, τ) := by
    filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
    simpa [A, x₀] using
      hF.paramFrameCoeff_eq_coordParamDeriv (I := I) hτ i
  simpa [x₀] using hderiv.congr_of_eventuallyEq heq

/-- Parameter derivative of the time-velocity frame coefficient in any fixed
coordinate frame containing the base point. -/
theorem SmoothSurface.timeFrameCoeff_param_hasDerivAt_of_mem {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ t i)
      (coordTs (I := I) x₀ F s t i) s := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordTimeDeriv (I := I) x₀ F p.1 p.2 i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) (0, (1 : Real))) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordTimeDeriv] using hD
  have hderiv :
      HasDerivAt (fun σ : Real => A (σ, t))
        (coordTs (I := I) x₀ F s t i) s := by
    have hdiff : DifferentiableAt Real A (s, t) :=
      hA.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    simpa [A, coordTs] using
      modelLine_fst_hasDerivAt (A := A) (s := s) (t := t) hdiff
  have heq :
      (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ t i)
        =ᶠ[𝓝 s] fun σ : Real => A (σ, t) := by
    filter_upwards [hF.coordMem_param_of_mem (I := I) hx] with σ hσ
    simpa [A] using hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hσ i
  exact hderiv.congr_of_eventuallyEq heq

/-- Time derivative of the time-velocity frame coefficient in any fixed
coordinate frame containing the base point. -/
theorem SmoothSurface.timeFrameCoeff_time_hasDerivAt_of_mem {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real => timeFrameCoeff (I := I) x₀ F s τ i)
      (coordTt (I := I) x₀ F s t i) t := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordTimeDeriv (I := I) x₀ F p.1 p.2 i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) (0, (1 : Real))) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordTimeDeriv] using hD
  have hderiv :
      HasDerivAt (fun τ : Real => A (s, τ))
        (coordTt (I := I) x₀ F s t i) t := by
    have hdiff : DifferentiableAt Real A (s, t) :=
      hA.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    simpa [A, coordTt] using
      modelLine_snd_hasDerivAt (A := A) (s := s) (t := t) hdiff
  have heq :
      (fun τ : Real => timeFrameCoeff (I := I) x₀ F s τ i)
        =ᶠ[𝓝 t] fun τ : Real => A (s, τ) := by
    filter_upwards [hF.coordMem_time_of_mem (I := I) hx] with τ hτ
    simpa [A] using hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hτ i
  exact hderiv.congr_of_eventuallyEq heq

/-- Time derivative of the time-velocity frame coefficient in the centered
coordinate frame. -/
theorem SmoothSurface.timeFrameCoeff_time_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real => timeFrameCoeff (I := I) (F (s, t)) F s τ i)
      (coordTt (I := I) (F (s, t)) F s t i) t := by
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  exact hF.timeFrameCoeff_time_hasDerivAt_of_mem (I := I) hx i

/-! ## Mixed coordinate partial producers -/

/-- Equality of the two mixed second partials of a fixed coordinate component
of a smooth surface. -/
theorem SmoothSurface.coordTs_eq_coordSt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordTs (I := I) (F (s, t)) F s t i =
      coordSt (I := I) (F (s, t)) F s t i := by
  let x₀ : M := F (s, t)
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hφTop : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ, x₀] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hφ2 : ContDiffAt Real 2 φ (s, t) :=
    hφTop.of_le (by
      show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2
        (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  simpa [φ, x₀, coordTs, coordSt, coordTimeDeriv, coordParamDeriv] using
    modelMix2 (φ := φ) (s := s) (t := t) hφ2

/-- Equality of the raw third-order mixed partials needed by the surface
commutator. -/
theorem SmoothSurface.coordVst_eq_coordVts {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordVst (I := I) (F (s, t)) F s t i =
      coordVts (I := I) (F (s, t)) F s t i := by
  let x₀ : M := F (s, t)
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hφTop : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ, x₀] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hφ3 : ContDiffAt Real 3 φ (s, t) :=
    hφTop.of_le (by
      show ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2
        (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  simpa [φ, x₀, coordVst, coordVts, coordTt, coordTs, coordTimeDeriv] using
    modelMix3 (φ := φ) (s := s) (t := t) hφ3

/-! ## Frame-vector coefficient bridges -/

/-- In the fixed coordinate trivialization, `frameVec` of the time field is
the coordinate-frame coefficient function. -/
theorem frameVec_timeField_eq
    (x₀ : M) {F : Surface M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    frameVec (I := I) (coordinateTrivializationAt (I := I) x₀)
        (Module.finBasis Real E) (surfaceTimeField (I := I) F (s, t)) =
      fun i : CoordinateIdx (𝕜 := Real) E =>
        timeFrameCoeff (I := I) x₀ F s t i := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hxE : F (s, t) ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  ext i
  rw [frameVec, timeFrameCoeff]
  change e.localFrame_coeff I (Module.finBasis Real E) i (F (s, t))
      (surfaceTimeField (I := I) F (s, t)) =
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i (F (s, t))
      (surfaceTimeField (I := I) F (s, t))
  rw [localFrame_coeff_eq_basis_repr (I := I) e (Module.finBasis Real E) hxE i]
  unfold IsLocalFrameOn.coeff
  rw [dif_pos hx]
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx =
        e.basisAt (Module.finBasis Real E) hxE := by
    ext j
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [← e.localFrame_apply_of_mem_baseSet
      (b := Module.finBasis Real E) (i := j) hxE]
    simp [e, coordinateFrameAt, coordinateTrivializationAt]
  rw [hbasis]
  rfl

/-- In the fixed coordinate trivialization, `frameVec` of the parameter field is
the coordinate-frame coefficient function. -/
theorem frameVec_paramField_eq
    (x₀ : M) {F : Surface M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    frameVec (I := I) (coordinateTrivializationAt (I := I) x₀)
        (Module.finBasis Real E) (surfaceParamField (I := I) F (s, t)) =
      fun i : CoordinateIdx (𝕜 := Real) E =>
        paramFrameCoeff (I := I) x₀ F s t i := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hxE : F (s, t) ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  ext i
  rw [frameVec, paramFrameCoeff]
  change e.localFrame_coeff I (Module.finBasis Real E) i (F (s, t))
      (surfaceParamField (I := I) F (s, t)) =
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i (F (s, t))
      (surfaceParamField (I := I) F (s, t))
  rw [localFrame_coeff_eq_basis_repr (I := I) e (Module.finBasis Real E) hxE i]
  unfold IsLocalFrameOn.coeff
  rw [dif_pos hx]
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx =
        e.basisAt (Module.finBasis Real E) hxE := by
    ext j
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [← e.localFrame_apply_of_mem_baseSet
      (b := Module.finBasis Real E) (i := j) hxE]
    simp [e, coordinateFrameAt, coordinateTrivializationAt]
  rw [hbasis]
  rfl

/-- In a fixed coordinate frame centered at `x0`, the local-frame connection
matrix in a curve direction is the velocity-coordinate contraction of the
fixed-center Christoffel coefficient function. -/
theorem frameGammaMat_fixed
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (gamma : Curve M) (t : Real)
    (hgt : gamma t ∈ coordinateFrameSet (I := I) x0)
    (j k : CoordinateIdx (𝕜 := Real) E) :
    frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (coordinateTrivializationAt (I := I) x0)
        (Module.finBasis Real E) gamma t
        (1 : TangentSpace 𝓘(Real, Real) t) k j =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff
            i (gamma t) (curveVelocity I gamma t) *
          Realized.christoffelCoordFun (I := I) cov x0 i j k (gamma t) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have h :=
    christoffelAlongInFrame_eq_sum_coeff
      (I := I) (Idx := CoordinateIdx (𝕜 := Real) E)
      cov frame hframe hgt (curveVelocity I gamma t) j k
  simpa [frameGammaMat, frameGamma, christoffelAlongInFrame,
    Realized.christoffelCoordFun, coordinateFrameAt, coordinateTrivializationAt,
    curveVelocity, frame, hframe] using h

/-- Fixed-coordinate expansion of the connection matrix in the time direction
of a two-parameter surface. -/
theorem frameGammaMat_time
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real)
    (hst : F (s, t) ∈ coordinateFrameSet (I := I) x0)
    (j k : CoordinateIdx (𝕜 := Real) E) :
    frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (coordinateTrivializationAt (I := I) x0)
        (Module.finBasis Real E) (surfaceTimeCurve F s) t
        (1 : TangentSpace 𝓘(Real, Real) t) k j =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff
            i (F (s, t)) (surfaceTimeField (I := I) F (s, t)) *
          Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, t)) := by
  simpa [surfaceTimeCurve, surfaceTimeField] using
    frameGammaMat_fixed (I := I) cov x0 (surfaceTimeCurve F s) t hst j k

/-- Fixed-coordinate expansion of the connection matrix in the variation
parameter direction of a two-parameter surface. -/
theorem frameGammaMat_param
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real)
    (hst : F (s, t) ∈ coordinateFrameSet (I := I) x0)
    (j k : CoordinateIdx (𝕜 := Real) E) :
    frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (coordinateTrivializationAt (I := I) x0)
        (Module.finBasis Real E) (surfaceParamCurve F t) s
        (1 : TangentSpace 𝓘(Real, Real) s) k j =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff
            i (F (s, t)) (surfaceParamField (I := I) F (s, t)) *
          Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, t)) := by
  simpa [surfaceParamCurve, surfaceParamField] using
    frameGammaMat_fixed (I := I) cov x0 (surfaceParamCurve F t) s hst j k

/-- Product rule for the fixed-coordinate parameter-direction connection
matrix when the time parameter changes. -/
theorem gammaS_deriv_t_mat
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real)
    (hmem : ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ coordinateFrameSet (I := I) x0)
    (S T St : CoordinateIdx (𝕜 := Real) E -> Real)
    (hS :
      ∀ i : CoordinateIdx (𝕜 := Real) E,
        (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff
            i (F (s, t)) (surfaceParamField (I := I) F (s, t)) = S i)
    (hSderiv :
      ∀ i : CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff
              i (F (s, τ)) (surfaceParamField (I := I) F (s, τ)))
          (St i) t)
    (hCderiv :
      ∀ i j k : CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, τ)))
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            T a * Realized.christoffelCoordDerivAt (I := I) cov x0 a i j k) t) :
    HasDerivAt
      (fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (coordinateTrivializationAt (I := I) x0)
          (Module.finBasis Real E) (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s))
      (fun k j =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          (St i * Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, t)) +
            S i *
              (∑ a : CoordinateIdx (𝕜 := Real) E,
                T a * Realized.christoffelCoordDerivAt (I := I) cov x0 a i j k)))
      t := by
  classical
  change HasDerivAt
    (fun τ : Real => fun k j =>
      frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
        (coordinateTrivializationAt (I := I) x0)
        (Module.finBasis Real E) (surfaceParamCurve F τ) s
        (1 : TangentSpace 𝓘(Real, Real) s) k j)
    (fun k j =>
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        (St i * Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, t)) +
          S i *
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              T a * Realized.christoffelCoordDerivAt (I := I) cov x0 a i j k)))
    t
  rw [hasDerivAt_pi]
  intro k
  rw [hasDerivAt_pi]
  intro j
  let coeff : CoordinateIdx (𝕜 := Real) E -> Real -> Real := fun i τ =>
    (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff
      i (F (s, τ)) (surfaceParamField (I := I) F (s, τ))
  let C : CoordinateIdx (𝕜 := Real) E -> Real -> Real := fun i τ =>
    Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, τ))
  have hrhs :
      HasDerivAt
        (fun τ : Real => ∑ i : CoordinateIdx (𝕜 := Real) E, coeff i τ * C i τ)
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          (St i * Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, t)) +
            S i *
              (∑ a : CoordinateIdx (𝕜 := Real) E,
                T a * Realized.christoffelCoordDerivAt (I := I) cov x0 a i j k)))
        t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hmul := (hSderiv i).mul (hCderiv i j k)
    simpa [coeff, C, hS i, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hline :
      (fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (coordinateTrivializationAt (I := I) x0)
          (Module.finBasis Real E) (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s) k j) =ᶠ[𝓝 t]
        (fun τ : Real =>
          ∑ i : CoordinateIdx (𝕜 := Real) E, coeff i τ * C i τ) := by
    filter_upwards [hmem] with τ hτ
    simpa [coeff, C] using
      (frameGammaMat_param (I := I) cov x0 F s τ hτ j k)
  exact hrhs.congr_of_eventuallyEq hline

/-- Symmetry of lower Christoffel indices implies equality of the two
contracted connection terms `Gamma(T) S` and `Gamma(S) T`. -/
theorem gamma_mulVec_symm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : ι -> Real) (C : ι -> ι -> ι -> Real)
    (hsym : ∀ i j k : ι, C i j k = C j i k) :
    Matrix.mulVec ((fun k j => ∑ i : ι, T i * C i j k) : Matrix ι ι Real) S =
      Matrix.mulVec ((fun k j => ∑ i : ι, S i * C i j k) : Matrix ι ι Real) T := by
  classical
  ext k
  simp [Matrix.mulVec, dotProduct]
  calc
    ∑ x : ι, (∑ i : ι, T i * C i x k) * S x
        = ∑ x : ι, S x * ∑ i : ι, T i * C i x k := by
          simp [mul_comm]
    _ = ∑ x : ι, ∑ i : ι, S x * (T i * C i x k) := by
          simp [Finset.mul_sum]
    _ = ∑ i : ι, ∑ x : ι, S x * (T i * C i x k) := by
          rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ x : ι, T i * (S x * C x i k) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [hsym i x k]
          ring
    _ = ∑ i : ι, T i * ∑ x : ι, S x * C x i k := by
          simp [Finset.mul_sum]
    _ = ∑ x : ι, (∑ i : ι, S i * C i x k) * T x := by
          simp [mul_comm]

/-- Torsion-free connections have symmetric centered coordinate Christoffel
coefficients.  This local version avoids global Levi-Civita compactness
assumptions. -/
theorem christoffelCoordAt_symm_of_torsionFree
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    Realized.christoffelCoordAt (I := I) cov x0 i j k =
      Realized.christoffelCoordAt (I := I) cov x0 j i k := by
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hzero :
      hframe.coeff k x0
          (cov.torsion x0 (frame i x0) (frame j x0)) = 0 := by
    rw [htf x0]
    simp
  have h := Coordinates.torsion_coeff_eq_christoffel_skew
    (I := I) cov frame hframe i j k
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 i)
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 j)
  rw [coordinateFrameAt_bracket_zero (I := I) x0 i j] at h
  rw [hzero] at h
  have hdiff :
      Realized.christoffelCoordAt (I := I) cov x0 i j k -
        Realized.christoffelCoordAt (I := I) cov x0 j i k = 0 := by
    simpa [Realized.christoffelCoordAt, frame, hframe] using h.symm
  exact sub_eq_zero.mp hdiff

/-! ## Vector-valued coefficient derivative producers -/

/-- Parameter derivative of the time-time coordinate partial. -/
theorem SmoothSurface.coordTt_param_hasDerivAt_of_mem {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun σ : Real => coordTt (I := I) x₀ F σ t i)
      (coordVst (I := I) x₀ F s t i) s := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordTimeDeriv (I := I) x₀ F p.1 p.2 i
  let B : Real × Real -> Real :=
    fun p => coordTt (I := I) x₀ F p.1 p.2 i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) (0, (1 : Real))) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordTimeDeriv] using hD
  have hB : ContDiffAt Real ∞ B (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real A p) (0, (1 : Real))) (s, t) := by
      have hfder := hA.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [B, A, coordTt] using hD
  have hdiff : DifferentiableAt Real B (s, t) :=
    hB.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  simpa [B, coordVst] using
    modelLine_fst_hasDerivAt (A := B) (s := s) (t := t) hdiff

/-- Time derivative of the parameter-time coordinate partial. -/
theorem SmoothSurface.coordTs_time_hasDerivAt_of_mem {F : Surface M}
    (hF : SmoothSurface (I := I) F) {x₀ : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real => coordTs (I := I) x₀ F s τ i)
      (coordVts (I := I) x₀ F s t i) t := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordTimeDeriv (I := I) x₀ F p.1 p.2 i
  let B : Real × Real -> Real :=
    fun p => coordTs (I := I) x₀ F p.1 p.2 i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) (0, (1 : Real))) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordTimeDeriv] using hD
  have hB : ContDiffAt Real ∞ B (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real A p) ((1 : Real), 0)) (s, t) := by
      have hfder := hA.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [B, A, coordTs] using hD
  have hdiff : DifferentiableAt Real B (s, t) :=
    hB.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  simpa [B, coordVts] using
    modelLine_snd_hasDerivAt (A := B) (s := s) (t := t) hdiff

/-- Vector-valued parameter derivative of the fixed-frame time field
coefficients. -/
theorem SmoothSurface.frameVec_time_param_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasDerivAt
      (fun σ : Real =>
        frameVec (I := I) (coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceTimeField (I := I) F (σ, t)))
      (coordTs (I := I) (F (s, t)) F s t) s := by
  let x₀ : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x₀
  rw [hasDerivAt_pi]
  intro i
  have hscalar := hF.timeFrameCoeff_param_hasDerivAt (I := I) s t i
  have heq :
      (fun σ : Real =>
        frameVec (I := I) e (Module.finBasis Real E)
          (surfaceTimeField (I := I) F (σ, t)) i)
        =ᶠ[𝓝 s]
      (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ t i) := by
    filter_upwards [hF.coordMem_param (I := I) s t] with σ hσ
    exact congrFun (frameVec_timeField_eq (I := I) x₀ hσ) i
  simpa [x₀, e] using hscalar.congr_of_eventuallyEq heq

/-- Vector-valued time derivative of the fixed-frame time field coefficients. -/
theorem SmoothSurface.frameVec_time_time_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) (coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceTimeField (I := I) F (s, τ)))
      (coordTt (I := I) (F (s, t)) F s t) t := by
  let x₀ : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x₀
  rw [hasDerivAt_pi]
  intro i
  have hscalar := hF.timeFrameCoeff_time_hasDerivAt (I := I) s t i
  have heq :
      (fun τ : Real =>
        frameVec (I := I) e (Module.finBasis Real E)
          (surfaceTimeField (I := I) F (s, τ)) i)
        =ᶠ[𝓝 t]
      (fun τ : Real => timeFrameCoeff (I := I) x₀ F s τ i) := by
    filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
    exact congrFun (frameVec_timeField_eq (I := I) x₀ hτ) i
  simpa [x₀, e] using hscalar.congr_of_eventuallyEq heq

/-- Vector-valued time derivative of the fixed-frame parameter field
coefficients. -/
theorem SmoothSurface.frameVec_param_time_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) (coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceParamField (I := I) F (s, τ)))
      (coordSt (I := I) (F (s, t)) F s t) t := by
  let x₀ : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x₀
  rw [hasDerivAt_pi]
  intro i
  have hscalar := hF.paramFrameCoeff_time_hasDerivAt (I := I) s t i
  have heq :
      (fun τ : Real =>
        frameVec (I := I) e (Module.finBasis Real E)
          (surfaceParamField (I := I) F (s, τ)) i)
        =ᶠ[𝓝 t]
      (fun τ : Real => paramFrameCoeff (I := I) x₀ F s τ i) := by
    filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
    exact congrFun (frameVec_paramField_eq (I := I) x₀ hτ) i
  simpa [x₀, e] using hscalar.congr_of_eventuallyEq heq

/-- Parameter derivative of the time-direction `frameDerivVec`. -/
theorem SmoothSurface.frameDeriv_time_param_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasDerivAt
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceTimeCurve F σ)
          (fun τ => surfaceTimeField (I := I) F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t))
      (coordVst (I := I) (F (s, t)) F s t) s := by
  let x₀ : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x₀
  have hcoord :
      HasDerivAt (fun σ : Real => coordTt (I := I) x₀ F σ t)
        (coordVst (I := I) x₀ F s t) s := by
    rw [hasDerivAt_pi]
    intro i
    have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
      simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
    exact hF.coordTt_param_hasDerivAt_of_mem (I := I) hx i
  have heq :
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          e (Module.finBasis Real E) (surfaceTimeCurve F σ)
          (fun τ => surfaceTimeField (I := I) F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        =ᶠ[𝓝 s]
      (fun σ : Real => coordTt (I := I) x₀ F σ t) := by
    filter_upwards [hF.coordMem_param (I := I) s t] with σ hσ
    have hvec :
        HasDerivAt
          (fun τ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)))
          (coordTt (I := I) x₀ F σ t) t := by
      rw [hasDerivAt_pi]
      intro i
      have hscalar :=
        hF.timeFrameCoeff_time_hasDerivAt_of_mem (I := I)
          (x₀ := x₀) (s := σ) (t := t) hσ i
      have hline :
          (fun τ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)) i)
            =ᶠ[𝓝 t]
          (fun τ : Real => timeFrameCoeff (I := I) x₀ F σ τ i) := by
        filter_upwards [hF.coordMem_time_of_mem (I := I) hσ] with τ hτ
        exact congrFun (frameVec_timeField_eq (I := I) x₀ hτ) i
      exact hscalar.congr_of_eventuallyEq hline
    exact frameDerivVec_eq_of_hasDerivAt (I := I) e (Module.finBasis Real E)
      (gamma := surfaceTimeCurve F σ)
      (S := fun τ => surfaceTimeField (I := I) F (σ, τ)) hvec
  simpa [x₀, e] using hcoord.congr_of_eventuallyEq heq

/-- Time derivative of the parameter-direction `frameDerivVec` for the time
field. -/
theorem SmoothSurface.frameDeriv_param_time_hasDerivAt {F : Surface M}
    (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasDerivAt
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceParamCurve F τ)
          (fun σ => surfaceTimeField (I := I) F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s))
      (coordVts (I := I) (F (s, t)) F s t) t := by
  let x₀ : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x₀
  have hcoord :
      HasDerivAt (fun τ : Real => coordTs (I := I) x₀ F s τ)
        (coordVts (I := I) x₀ F s t) t := by
    rw [hasDerivAt_pi]
    intro i
    have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
      simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
    exact hF.coordTs_time_hasDerivAt_of_mem (I := I) hx i
  have heq :
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          e (Module.finBasis Real E) (surfaceParamCurve F τ)
          (fun σ => surfaceTimeField (I := I) F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        =ᶠ[𝓝 t]
      (fun τ : Real => coordTs (I := I) x₀ F s τ) := by
    filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
    have hvec :
        HasDerivAt
          (fun σ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)))
          (coordTs (I := I) x₀ F s τ) s := by
      rw [hasDerivAt_pi]
      intro i
      have hscalar :=
        hF.timeFrameCoeff_param_hasDerivAt_of_mem (I := I)
          (x₀ := x₀) (s := s) (t := τ) hτ i
      have hline :
          (fun σ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)) i)
            =ᶠ[𝓝 s]
          (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ τ i) := by
        filter_upwards [hF.coordMem_param_of_mem (I := I) hτ] with σ hσ
        exact congrFun (frameVec_timeField_eq (I := I) x₀ hσ) i
      exact hscalar.congr_of_eventuallyEq hline
    exact frameDerivVec_eq_of_hasDerivAt (I := I) e (Module.finBasis Real E)
      (gamma := surfaceParamCurve F τ)
      (S := fun σ => surfaceTimeField (I := I) F (σ, τ)) hvec
  simpa [x₀, e] using hcoord.congr_of_eventuallyEq heq

/-! ## Full scalar package for the surface curvature commutator -/

/-- Scalar and frame-coordinate data consumed by the fixed-coordinate surface
commutator.

This is the producer target for smooth surfaces.  It packages the data needed
by `Jacobi.curvComm_surface` without adding any new assumptions to the
Jacobi-facing `VariationCurvCommAt`. -/
structure CoordSurfJet
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s t : Real) where
  S : CoordinateIdx (𝕜 := Real) E -> Real
  T : CoordinateIdx (𝕜 := Real) E -> Real
  Ts : CoordinateIdx (𝕜 := Real) E -> Real
  St : CoordinateIdx (𝕜 := Real) E -> Real
  vt : CoordinateIdx (𝕜 := Real) E -> Real
  vst : CoordinateIdx (𝕜 := Real) E -> Real
  vts : CoordinateIdx (𝕜 := Real) E -> Real
  hmem_s :
    ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ coordinateFrameSet (I := I) (F (s, t))
  hmem_t :
    ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ coordinateFrameSet (I := I) (F (s, t))
  hS :
    ∀ i : CoordinateIdx (𝕜 := Real) E,
      paramFrameCoeff (I := I) (F (s, t)) F s t i = S i
  hT :
    ∀ i : CoordinateIdx (𝕜 := Real) E,
      timeFrameCoeff (I := I) (F (s, t)) F s t i = T i
  hTderiv :
    ∀ i : CoordinateIdx (𝕜 := Real) E,
      HasDerivAt
        (fun σ : Real => timeFrameCoeff (I := I) (F (s, t)) F σ t i)
        (Ts i) s
  hSderiv :
    ∀ i : CoordinateIdx (𝕜 := Real) E,
      HasDerivAt
        (fun τ : Real => paramFrameCoeff (I := I) (F (s, t)) F s τ i)
        (St i) t
  hCs :
    ∀ i j k : CoordinateIdx (𝕜 := Real) E,
      HasDerivAt
        (fun σ : Real =>
          Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (σ, t)))
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          S a * Realized.christoffelCoordDerivAt (I := I) cov
            (F (s, t)) a i j k) s
  hCt :
    ∀ i j k : CoordinateIdx (𝕜 := Real) E,
      HasDerivAt
        (fun τ : Real =>
          Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (s, τ)))
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          T a * Realized.christoffelCoordDerivAt (I := I) cov
            (F (s, t)) a i j k) t
  hvt_s : HasDerivAt
    (fun σ : Real =>
      frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
        (coordinateTrivializationAt (I := I) (F (s, t)))
        (Module.finBasis Real E) (surfaceTimeCurve F σ)
        (fun τ => surfaceTimeField (I := I) F (σ, τ)) t
        (1 : TangentSpace 𝓘(Real, Real) t)) vst s
  hvs : HasDerivAt
    (fun σ : Real =>
      frameVec (I := I)
        (coordinateTrivializationAt (I := I) (F (s, t)))
        (Module.finBasis Real E) (surfaceTimeField (I := I) F (σ, t))) Ts s
  hvs_t : HasDerivAt
    (fun τ : Real =>
      frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
        (coordinateTrivializationAt (I := I) (F (s, t)))
        (Module.finBasis Real E) (surfaceParamCurve F τ)
        (fun σ => surfaceTimeField (I := I) F (σ, τ)) s
        (1 : TangentSpace 𝓘(Real, Real) s)) vts t
  hvt : HasDerivAt
    (fun τ : Real =>
      frameVec (I := I)
        (coordinateTrivializationAt (I := I) (F (s, t)))
        (Module.finBasis Real E) (surfaceTimeField (I := I) F (s, τ))) vt t
  hmix_raw : vst = vts
  hmix : Ts = St

section CoordSurfJet

variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- A smooth surface produces the full fixed-coordinate scalar package used by
the Jacobi surface curvature commutator. -/
def SmoothSurface.coordSurfJet
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    CoordSurfJet (I := I) cov F s t := by
  classical
  let x₀ : M := F (s, t)
  let S : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordParamDeriv (I := I) x₀ F s t
  let T : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordTimeDeriv (I := I) x₀ F s t
  let Ts : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordTs (I := I) x₀ F s t
  let St : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordSt (I := I) x₀ F s t
  let vt : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordTt (I := I) x₀ F s t
  let vst : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordVst (I := I) x₀ F s t
  let vts : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordVts (I := I) x₀ F s t
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hS :
      ∀ i : CoordinateIdx (𝕜 := Real) E,
        paramFrameCoeff (I := I) x₀ F s t i = S i := by
    intro i
    simpa [S, x₀] using hF.paramFrameCoeff_eq_coordParamDeriv (I := I) hx i
  have hT :
      ∀ i : CoordinateIdx (𝕜 := Real) E,
        timeFrameCoeff (I := I) x₀ F s t i = T i := by
    intro i
    simpa [T, x₀] using hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hx i
  refine
    { S := S
      T := T
      Ts := Ts
      St := St
      vt := vt
      vst := vst
      vts := vts
      hmem_s := ?_
      hmem_t := ?_
      hS := hS
      hT := hT
      hTderiv := ?_
      hSderiv := ?_
      hCs := ?_
      hCt := ?_
      hvt_s := ?_
      hvs := ?_
      hvs_t := ?_
      hvt := ?_
      hmix_raw := ?_
      hmix := ?_ }
  · simpa [x₀] using hF.coordMem_param (I := I) s t
  · simpa [x₀] using hF.coordMem_time (I := I) s t
  · intro i
    simpa [Ts, x₀] using hF.timeFrameCoeff_param_hasDerivAt (I := I) s t i
  · intro i
    simpa [St, x₀] using hF.paramFrameCoeff_time_hasDerivAt (I := I) s t i
  · intro i j k
    simpa [S, x₀] using
      hF.christoffel_param_hasDerivAt (I := I) hcov s t S hS i j k
  · intro i j k
    simpa [T, x₀] using
      hF.christoffel_time_hasDerivAt (I := I) hcov s t T hT i j k
  · simpa [vst, x₀] using hF.frameDeriv_time_param_hasDerivAt (I := I) s t
  · simpa [Ts, x₀] using hF.frameVec_time_param_hasDerivAt (I := I) s t
  · simpa [vts, x₀] using hF.frameDeriv_param_time_hasDerivAt (I := I) s t
  · simpa [vt, x₀] using hF.frameVec_time_time_hasDerivAt (I := I) s t
  · ext i
    simpa [vst, vts, x₀] using hF.coordVst_eq_coordVts (I := I) s t i
  · ext i
    simpa [Ts, St, x₀] using hF.coordTs_eq_coordSt (I := I) s t i

end CoordSurfJet

/-! ## Canonical mixed derivative fields -/

/-- Fixed-center coefficient vector for `D_s T` in the coordinate frame
centered at `x0`.  This is the pointwise formula
`partial_s T + Gamma_s T`. -/
def dsTimeCoeffIn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real) :
    CoordinateIdx (𝕜 := Real) E -> Real :=
  coeffCov
    (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
      (coordinateTrivializationAt (I := I) x0) (Module.finBasis Real E)
      (surfaceParamCurve F t) s (1 : TangentSpace 𝓘(Real, Real) s))
    (coordTs (I := I) x0 F s t)
    (frameVec (I := I) (coordinateTrivializationAt (I := I) x0)
      (Module.finBasis Real E) (surfaceTimeField (I := I) F (s, t)))

/-- Fixed-center tangent vector represented by `dsTimeCoeffIn`. -/
def dsTimeFieldIn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real) : TangentSpace I (F (s, t)) :=
  frameSum (I := I) (coordinateTrivializationAt (I := I) x0)
    (Module.finBasis Real E)
    (dsTimeCoeffIn (I := I) cov x0 F s t)

/-- Centered coefficient vector for the canonical `D_s T` surface field. -/
def dsTimeCoeff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s t : Real) :
    CoordinateIdx (𝕜 := Real) E -> Real :=
  dsTimeCoeffIn (I := I) cov (F (s, t)) F s t

/-- Canonical surface field for the mixed derivative `D_s T`. -/
def dsTimeField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) : SurfaceFieldAlong I F :=
  fun p => dsTimeFieldIn (I := I) cov (F p) F p.1 p.2

/-- Time derivative of the fixed-center `D_s T` coefficient vector, expressed
by the model-space derivative of the coefficient function. -/
def dsTimeCoeffTimeDerivIn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real) :
    CoordinateIdx (𝕜 := Real) E -> Real :=
  (fderiv Real
    (fun τ : Real => dsTimeCoeffIn (I := I) cov x0 F s τ) t)
      (1 : Real)

/-- Fixed-center coefficient vector for `D_t(D_s T)`. -/
def dtdsTimeCoeffIn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real) :
    CoordinateIdx (𝕜 := Real) E -> Real :=
  coeffCov
    (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
      (coordinateTrivializationAt (I := I) x0) (Module.finBasis Real E)
      (surfaceTimeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t))
    (dsTimeCoeffTimeDerivIn (I := I) cov x0 F s t)
    (dsTimeCoeffIn (I := I) cov x0 F s t)

/-- Fixed-center tangent vector represented by `dtdsTimeCoeffIn`. -/
def dtdsTimeFieldIn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real) : TangentSpace I (F (s, t)) :=
  frameSum (I := I) (coordinateTrivializationAt (I := I) x0)
    (Module.finBasis Real E)
    (dtdsTimeCoeffIn (I := I) cov x0 F s t)

/-- Centered tangent vector for `D_t(D_s T)`. -/
def dtdsTimeField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) : SurfaceFieldAlong I F :=
  fun p => dtdsTimeFieldIn (I := I) cov (F p) F p.1 p.2

section MixedFields

variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Fixed-center construction of `D_s T`. -/
theorem SmoothSurface.hasParam_dsTimeIn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x0) :
    HasPBParamCovDerivAt (I := I) cov F (surfaceTimeField (I := I) F)
      s t (dsTimeFieldIn (I := I) cov x0 F s t) := by
  classical
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  have hxE : F (s, t) ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceParamCurve F t) s :=
    hF.mdiffAt_param (I := I) s t
  have hvec : HasDerivAt
      (fun σ : Real =>
        frameVec (I := I) e b (surfaceTimeField (I := I) F (σ, t)))
      (coordTs (I := I) x0 F s t) s := by
    rw [hasDerivAt_pi]
    intro i
    have hscalar := hF.timeFrameCoeff_param_hasDerivAt_of_mem
      (I := I) (x₀ := x0) (s := s) (t := t) hx i
    have heq :
        (fun σ : Real =>
          frameVec (I := I) e b (surfaceTimeField (I := I) F (σ, t)) i)
          =ᶠ[𝓝 s]
        (fun σ : Real => timeFrameCoeff (I := I) x0 F σ t i) := by
      filter_upwards [hF.coordMem_param_of_mem (I := I) hx] with σ hσ
      exact congrFun (frameVec_timeField_eq (I := I) x0 hσ) i
    exact hscalar.congr_of_eventuallyEq heq.symm
  have hframe := HasFrameAlongAt.of_frameVec_hasDerivAt
    (I := I) (cov := cov) (e := e) (b := b)
    (gamma := surfaceParamCurve F t)
    (S := fun σ => surfaceTimeField (I := I) F (σ, t))
    hxE hgamma hvec
  have htarget :
      frameSum (I := I) e b
        (coeffCov
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F t) s (1 : TangentSpace 𝓘(Real, Real) s))
          (coordTs (I := I) x0 F s t)
          (frameVec (I := I) e b (surfaceTimeField (I := I) F (s, t)))) =
        dsTimeFieldIn (I := I) cov x0 F s t := by
    rfl
  rw [← htarget]
  exact HasPBCovDerivAt.ofFrame (I := I) (I' := 𝓘(Real, Real)) hframe

/-- Centered construction of `D_s T`. -/
theorem SmoothSurface.hasParam_dsTime
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasPBParamCovDerivAt (I := I) cov F (surfaceTimeField (I := I) F)
      s t (dsTimeField (I := I) cov F (s, t)) := by
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  simpa [dsTimeField] using
    hF.hasParam_dsTimeIn (I := I) (cov := cov) hx

/-- Time derivative of the fixed-center coefficient vector for `D_s T`. -/
theorem SmoothSurface.dsTimeCoeffIn_hasDerivAt
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasDerivAt
      (fun τ : Real =>
        dsTimeCoeffIn (I := I) cov (F (s, t)) F s τ)
      (dsTimeCoeffTimeDerivIn (I := I) cov (F (s, t)) F s t) t := by
  classical
  let x0 : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  let jet := hF.coordSurfJet (I := I) (cov := cov) hcov s t
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x0 := by
    simpa [x0] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hGamma :
      HasDerivAt
        (fun τ : Real =>
          frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F τ) s
            (1 : TangentSpace 𝓘(Real, Real) s))
        (fun k j =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            (jet.St i * Realized.christoffelCoordFun (I := I) cov x0 i j k (F (s, t)) +
              jet.S i *
                (∑ a : CoordinateIdx (𝕜 := Real) E,
                  jet.T a * Realized.christoffelCoordDerivAt (I := I) cov x0 a i j k)))
        t := by
    have h := gammaS_deriv_t_mat (I := I) cov x0 F s t
      (by simpa [x0, jet] using jet.hmem_t) jet.S jet.T jet.St
      (by
        intro i
        simpa [x0, jet, paramFrameCoeff, surfaceParamField] using jet.hS i)
      (by
        intro i
        simpa [x0, jet, paramFrameCoeff, surfaceParamField] using jet.hSderiv i)
      (by
        intro i j k
        simpa [x0, jet] using jet.hCt i j k)
    simpa [x0, e, b] using h
  have hcoord :
      HasDerivAt
        (fun τ : Real => coordTs (I := I) x0 F s τ)
        (coordVts (I := I) x0 F s t) t := by
    rw [hasDerivAt_pi]
    intro i
    simpa [x0] using hF.coordTs_time_hasDerivAt_of_mem (I := I) hx i
  have hT :
      HasDerivAt
        (fun τ : Real =>
          frameVec (I := I) e b (surfaceTimeField (I := I) F (s, τ)))
        (coordTt (I := I) x0 F s t) t := by
    simpa [x0, e, b] using hF.frameVec_time_time_hasDerivAt (I := I) s t
  have hraw := hasDerivAt_coeffCov
    (Γ := fun τ : Real =>
      frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
        (surfaceParamCurve F τ) s (1 : TangentSpace 𝓘(Real, Real) s))
    (v := fun τ : Real =>
      frameVec (I := I) e b (surfaceTimeField (I := I) F (s, τ)))
    (dvFun := fun τ : Real => coordTs (I := I) x0 F s τ)
    hGamma hT hcoord
  have hfder := hraw.hasFDerivAt.fderiv
  simpa [dsTimeCoeffIn, dsTimeCoeffTimeDerivIn, x0, e, b, hfder] using hraw

/-- Fixed-center construction of `D_t(D_s T)`. -/
theorem SmoothSurface.hasTime_dsTimeIn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasPBTimeCovDerivAt (I := I) cov F
      (fun p : Real × Real =>
        dsTimeFieldIn (I := I) cov (F (s, t)) F p.1 p.2)
      s t (dtdsTimeFieldIn (I := I) cov (F (s, t)) F s t) := by
  classical
  let x0 : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x0 := by
    simpa [x0] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hxE : F (s, t) ∈ e.baseSet := by
    simp [e, x0, coordinateFrameSet, coordinateTrivializationAt] at hx ⊢
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    hF.mdiffAt_time (I := I) s t
  have hcoeff := hF.dsTimeCoeffIn_hasDerivAt (I := I) (cov := cov) hcov s t
  have hvec : HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) e b
          (dsTimeFieldIn (I := I) cov x0 F s τ))
      (dsTimeCoeffTimeDerivIn (I := I) cov x0 F s t) t := by
    have heq :
        (fun τ : Real =>
          frameVec (I := I) e b
            (dsTimeFieldIn (I := I) cov x0 F s τ))
          =ᶠ[𝓝 t]
        (fun τ : Real => dsTimeCoeffIn (I := I) cov x0 F s τ) := by
      filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
      have hτE : F (s, τ) ∈ e.baseSet := by
        simpa [e, x0, coordinateFrameSet, coordinateTrivializationAt] using hτ
      exact frameVec_frameSum (I := I) e b hτE
        (dsTimeCoeffIn (I := I) cov x0 F s τ)
    simpa [x0] using hcoeff.congr_of_eventuallyEq heq
  have hframe := HasFrameAlongAt.of_frameVec_hasDerivAt
    (I := I) (cov := cov) (e := e) (b := b)
    (gamma := surfaceTimeCurve F s)
    (S := fun τ => dsTimeFieldIn (I := I) cov x0 F s τ)
    hxE hgamma hvec
  have htarget :
      frameSum (I := I) e b
        (coeffCov
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t))
          (dsTimeCoeffTimeDerivIn (I := I) cov x0 F s t)
          (frameVec (I := I) e b (dsTimeFieldIn (I := I) cov x0 F s t))) =
        dtdsTimeFieldIn (I := I) cov x0 F s t := by
    have hself :
        frameVec (I := I) e b (dsTimeFieldIn (I := I) cov x0 F s t) =
          dsTimeCoeffIn (I := I) cov x0 F s t := by
      exact frameVec_frameSum (I := I) e b hxE
        (dsTimeCoeffIn (I := I) cov x0 F s t)
    rw [hself]
    rfl
  rw [← htarget]
  exact HasPBCovDerivAt.ofFrame (I := I) (I' := 𝓘(Real, Real)) hframe

/-- The centered `D_s T` field agrees near a point with the same construction
written in that point's fixed coordinate frame. -/
theorem SmoothSurface.dsTimeField_eq_fixed_eventually
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ∀ᶠ τ : Real in 𝓝 t,
      dsTimeField (I := I) cov F (s, τ) =
        dsTimeFieldIn (I := I) cov (F (s, t)) F s τ := by
  filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
  have hcenter := hF.hasParam_dsTime (I := I) (cov := cov) s τ
  have hfixed := hF.hasParam_dsTimeIn (I := I) (cov := cov) hτ
  exact HasPBParamCovDerivAt.unique (I := I) hcenter hfixed

/-- Centered construction of `D_t(D_s T)`. -/
theorem SmoothSurface.hasTime_dsTime
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasPBTimeCovDerivAt (I := I) cov F (dsTimeField (I := I) cov F)
      s t (dtdsTimeFieldIn (I := I) cov (F (s, t)) F s t) := by
  classical
  let x0 : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x0 := by
    simpa [x0] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hxE : F (s, t) ∈ e.baseSet := by
    simp [e, x0, coordinateFrameSet, coordinateTrivializationAt] at hx ⊢
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    hF.mdiffAt_time (I := I) s t
  have hcoeff := hF.dsTimeCoeffIn_hasDerivAt (I := I) (cov := cov) hcov s t
  have hvec_fixed : HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) e b
          (dsTimeFieldIn (I := I) cov x0 F s τ))
      (dsTimeCoeffTimeDerivIn (I := I) cov x0 F s t) t := by
    have heq :
        (fun τ : Real =>
          frameVec (I := I) e b
            (dsTimeFieldIn (I := I) cov x0 F s τ))
          =ᶠ[𝓝 t]
        (fun τ : Real => dsTimeCoeffIn (I := I) cov x0 F s τ) := by
      filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
      have hτE : F (s, τ) ∈ e.baseSet := by
        simpa [e, x0, coordinateFrameSet, coordinateTrivializationAt] using hτ
      exact frameVec_frameSum (I := I) e b hτE
        (dsTimeCoeffIn (I := I) cov x0 F s τ)
    simpa [x0] using hcoeff.congr_of_eventuallyEq heq
  have hvec : HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) e b (dsTimeField (I := I) cov F (s, τ)))
      (dsTimeCoeffTimeDerivIn (I := I) cov x0 F s t) t := by
    have heq :
        (fun τ : Real =>
          frameVec (I := I) e b (dsTimeField (I := I) cov F (s, τ)))
          =ᶠ[𝓝 t]
        (fun τ : Real =>
          frameVec (I := I) e b
            (dsTimeFieldIn (I := I) cov x0 F s τ)) := by
      filter_upwards [hF.dsTimeField_eq_fixed_eventually (I := I) (cov := cov) s t]
        with τ hτ
      rw [hτ]
    exact hvec_fixed.congr_of_eventuallyEq heq
  have hframe := HasFrameAlongAt.of_frameVec_hasDerivAt
    (I := I) (cov := cov) (e := e) (b := b)
    (gamma := surfaceTimeCurve F s)
    (S := fun τ => dsTimeField (I := I) cov F (s, τ))
    hxE hgamma hvec
  have htarget :
      frameSum (I := I) e b
        (coeffCov
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t))
          (dsTimeCoeffTimeDerivIn (I := I) cov x0 F s t)
          (frameVec (I := I) e b (dsTimeField (I := I) cov F (s, t)))) =
        dtdsTimeFieldIn (I := I) cov x0 F s t := by
    have hself :
        frameVec (I := I) e b (dsTimeField (I := I) cov F (s, t)) =
          dsTimeCoeffIn (I := I) cov x0 F s t := by
      exact frameVec_frameSum (I := I) e b hxE
        (dsTimeCoeffIn (I := I) cov x0 F s t)
    rw [hself]
    rfl
  rw [← htarget]
  exact HasPBCovDerivAt.ofFrame (I := I) (I' := 𝓘(Real, Real)) hframe

/-- Torsion-free coordinate calculus identifies `D_t S` with the canonical
`D_s T` field. -/
theorem SmoothSurface.hasTime_param_eq_dsTime
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasPBTimeCovDerivAt (I := I) cov F (surfaceParamField (I := I) F)
      s t (dsTimeField (I := I) cov F (s, t)) := by
  classical
  let x0 : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  let S : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordParamDeriv (I := I) x0 F s t
  let T : CoordinateIdx (𝕜 := Real) E -> Real :=
    coordTimeDeriv (I := I) x0 F s t
  let Γs : Matrix (CoordinateIdx (𝕜 := Real) E)
      (CoordinateIdx (𝕜 := Real) E) Real :=
    frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
      (surfaceParamCurve F t) s (1 : TangentSpace 𝓘(Real, Real) s)
  let Γt : Matrix (CoordinateIdx (𝕜 := Real) E)
      (CoordinateIdx (𝕜 := Real) E) Real :=
    frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
      (surfaceTimeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t)
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x0 := by
    simpa [x0] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hxE : F (s, t) ∈ e.baseSet := by
    simp [e, x0, coordinateFrameSet, coordinateTrivializationAt] at hx ⊢
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    hF.mdiffAt_time (I := I) s t
  have hvec : HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) e b (surfaceParamField (I := I) F (s, τ)))
      (coordSt (I := I) x0 F s t) t := by
    simpa [x0, e, b] using hF.frameVec_param_time_hasDerivAt (I := I) s t
  have hframe := HasFrameAlongAt.of_frameVec_hasDerivAt
    (I := I) (cov := cov) (e := e) (b := b)
    (gamma := surfaceTimeCurve F s)
    (S := fun τ => surfaceParamField (I := I) F (s, τ))
    hxE hgamma hvec
  have hSvec :
      frameVec (I := I) e b (surfaceParamField (I := I) F (s, t)) = S := by
    have h := frameVec_paramField_eq (I := I) x0 hx
    ext i
    rw [congrFun h i]
    simpa [S, x0] using hF.paramFrameCoeff_eq_coordParamDeriv (I := I) hx i
  have hTvec :
      frameVec (I := I) e b (surfaceTimeField (I := I) F (s, t)) = T := by
    have h := frameVec_timeField_eq (I := I) x0 hx
    ext i
    rw [congrFun h i]
    simpa [T, x0] using hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hx i
  have hΓt :
      Γt =
        (fun k j =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            T i * Realized.christoffelCoordAt (I := I) cov x0 i j k) := by
    ext k j
    have h := frameGammaMat_time (I := I) cov x0 F s t hx j k
    calc
      Γt k j =
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            timeFrameCoeff (I := I) x0 F s t i *
              Realized.christoffelCoordAt (I := I) cov x0 i j k := by
            simpa [Γt, timeFrameCoeff, x0, e, b, Realized.christoffelCoordAt,
              Realized.christoffelCoordFun] using h
      _ =
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            T i * Realized.christoffelCoordAt (I := I) cov x0 i j k := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hx i]
  have hΓs :
      Γs =
        (fun k j =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            S i * Realized.christoffelCoordAt (I := I) cov x0 i j k) := by
    ext k j
    have h := frameGammaMat_param (I := I) cov x0 F s t hx j k
    calc
      Γs k j =
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            paramFrameCoeff (I := I) x0 F s t i *
              Realized.christoffelCoordAt (I := I) cov x0 i j k := by
            simpa [Γs, paramFrameCoeff, x0, e, b, Realized.christoffelCoordAt,
              Realized.christoffelCoordFun] using h
      _ =
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            S i * Realized.christoffelCoordAt (I := I) cov x0 i j k := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hF.paramFrameCoeff_eq_coordParamDeriv (I := I) hx i]
  have hsym :
      ∀ i j k : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCoordAt (I := I) cov x0 i j k =
          Realized.christoffelCoordAt (I := I) cov x0 j i k := by
    intro i j k
    exact christoffelCoordAt_symm_of_torsionFree (I := I) htf x0 i j k
  have hΓmul :
      Γt.mulVec S = Γs.mulVec T := by
    rw [hΓt, hΓs]
    exact gamma_mulVec_symm S T
      (fun i j k => Realized.christoffelCoordAt (I := I) cov x0 i j k) hsym
  have hcoeff :
      coeffCov Γt (coordSt (I := I) x0 F s t)
          (frameVec (I := I) e b (surfaceParamField (I := I) F (s, t))) =
        dsTimeCoeffIn (I := I) cov x0 F s t := by
    have hmix : coordSt (I := I) x0 F s t = coordTs (I := I) x0 F s t := by
      ext i
      simpa [x0] using (hF.coordTs_eq_coordSt (I := I) s t i).symm
    change coeffCov Γt (coordSt (I := I) x0 F s t)
        (frameVec (I := I) e b (surfaceParamField (I := I) F (s, t))) =
      coeffCov Γs (coordTs (I := I) x0 F s t)
        (frameVec (I := I) e b (surfaceTimeField (I := I) F (s, t)))
    rw [hSvec, hTvec, hmix]
    ext k
    dsimp [coeffCov]
    rw [congrFun hΓmul k]
  have htarget :
      frameSum (I := I) e b
        (coeffCov Γt (coordSt (I := I) x0 F s t)
          (frameVec (I := I) e b (surfaceParamField (I := I) F (s, t)))) =
        dsTimeField (I := I) cov F (s, t) := by
    rw [hcoeff]
    rfl
  rw [← htarget]
  exact HasPBCovDerivAt.ofFrame (I := I) (I' := 𝓘(Real, Real)) hframe

end MixedFields

end Lecture07
end GlobalGeometry
end RicciFlower
