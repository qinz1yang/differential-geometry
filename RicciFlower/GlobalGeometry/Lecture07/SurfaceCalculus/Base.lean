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

/-- Local version of `SmoothSurface.coordAt_contMDiffAt`. -/
theorem coordAt_contMDiffAt_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    ContMDiffAt 𝓘(Real, Real × Real) 𝓘(Real, E) ∞
      (surfaceCoord (I := I) x₀ F) (s, t) := by
  have hx_chart : F (s, t) ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hchart : ContMDiffAt I 𝓘(Real, E) ∞
      (extChartAt I x₀) (F (s, t)) :=
    contMDiffAt_extChartAt' (I := I) hx_chart
  simpa [surfaceCoord] using hchart.comp (s, t) hF

/-- Local version of `SmoothSurface.coordCompAt_contMDiffAt`. -/
theorem coordCompAt_contDiffAt_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    ContDiffAt Real ∞
      (fun p : Real × Real => surfaceCoordComp (I := I) x₀ F p i) (s, t) := by
  have hcoord := coordAt_contMDiffAt_of_contMDiffAt (I := I) hF hx
  have hlin : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun y : E => (Module.finBasis Real E).repr y i) :=
    (LinearMap.toContinuousLinearMap
      ((Module.finBasis Real E).coord i)).contMDiff
  simpa [surfaceCoordComp] using
    (hlin.contMDiffAt.comp (s, t) hcoord).contDiffAt

/-- Local smoothness of a fixed-time parameter line. -/
theorem contMDiffAt_param_of_contMDiffAt {F : Surface M}
    {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t)) :
    ContMDiffAt 𝓘(Real, Real) I ∞ (surfaceParamCurve F t) s := by
  have hline :
      ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real × Real) ∞
        (fun σ : Real => (σ, t)) s := by
    simpa using
      ((contDiffAt_id.prodMk contDiffAt_const :
        ContDiffAt Real ∞ (fun σ : Real => (σ, t)) s).contMDiffAt)
  simpa [surfaceParamCurve] using hF.comp s hline

/-- Local smoothness of a fixed-parameter time line. -/
theorem contMDiffAt_time_of_contMDiffAt {F : Surface M}
    {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t)) :
    ContMDiffAt 𝓘(Real, Real) I ∞ (surfaceTimeCurve F s) t := by
  have hline :
      ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real × Real) ∞
        (fun τ : Real => (s, τ)) t := by
    simpa using
      ((contDiffAt_const.prodMk contDiffAt_id :
        ContDiffAt Real ∞ (fun τ : Real => (s, τ)) t).contMDiffAt)
  simpa [surfaceTimeCurve] using hF.comp t hline

/-- Local differentiability of a fixed-time parameter line. -/
theorem mdiffAt_param_of_contMDiffAt {F : Surface M}
    {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t)) :
    MDifferentiableAt 𝓘(Real, Real) I (surfaceParamCurve F t) s :=
  (contMDiffAt_param_of_contMDiffAt (I := I) hF).mdifferentiableAt (by simp)

/-- Local differentiability of a fixed-parameter time line. -/
theorem mdiffAt_time_of_contMDiffAt {F : Surface M}
    {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t)) :
    MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
  (contMDiffAt_time_of_contMDiffAt (I := I) hF).mdifferentiableAt (by simp)

/-- If a locally smooth surface point lies in a fixed coordinate-frame domain,
nearby points on the parameter line remain there. -/
theorem coordMem_param_of_mem_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ coordinateFrameSet (I := I) x₀ := by
  have hU : IsOpen (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameSet_open (I := I) x₀
  have hline : ContinuousAt (fun σ : Real => (σ, t)) s :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hFst : ContinuousAt F ((fun σ : Real => (σ, t)) s) :=
    hF.continuousAt
  have hcomp : ContinuousAt (fun σ : Real => F (σ, t)) s := by
    simpa [Function.comp_def] using
      (hFst.comp (f := fun σ : Real => (σ, t)) hline)
  exact hcomp.eventually_mem (hU.mem_nhds hx)

/-- If a locally smooth surface point lies in a fixed coordinate-frame domain,
nearby points on the time line remain there. -/
theorem coordMem_time_of_mem_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ coordinateFrameSet (I := I) x₀ := by
  have hU : IsOpen (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameSet_open (I := I) x₀
  have hline : ContinuousAt (fun τ : Real => (s, τ)) t :=
    ContinuousAt.prodMk continuousAt_const continuousAt_id
  have hFst : ContinuousAt F ((fun τ : Real => (s, τ)) t) :=
    hF.continuousAt
  have hcomp : ContinuousAt (fun τ : Real => F (s, τ)) t := by
    simpa [Function.comp_def] using
      (hFst.comp (f := fun τ : Real => (s, τ)) hline)
  exact hcomp.eventually_mem (hU.mem_nhds hx)

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

/-- Local version of `SmoothSurface.timeFrameCoeff_eq_coordDeriv`. -/
theorem timeFrameCoeff_eq_coordDeriv_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
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
    mdiffAt_time_of_contMDiffAt (I := I) hF
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

/-- Local version of `SmoothSurface.paramFrameCoeff_eq_coordDeriv`. -/
theorem paramFrameCoeff_eq_coordDeriv_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
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
    mdiffAt_param_of_contMDiffAt (I := I) hF
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

/-- Local version of `SmoothSurface.timeFrameCoeff_eq_coordTimeDeriv`. -/
theorem timeFrameCoeff_eq_coordTimeDeriv_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
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
  have hg : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) g t := by
    have hcomp := (coordAt_contMDiffAt_of_contMDiffAt (I := I) hF hx).comp t hline
    exact hcomp.mdifferentiableAt (by simp)
  have hscalar : HasDerivAt
      (fun τ : Real => surfaceCoordComp (I := I) x₀ F (s, τ) i)
      (coordTimeDeriv (I := I) x₀ F s t i) t := by
    have hdiff : DifferentiableAt Real
        (fun p : Real × Real => surfaceCoordComp (I := I) x₀ F p i) (s, t) :=
      (coordCompAt_contDiffAt_of_contMDiffAt (I := I) hF hx i).differentiableAt
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
  rw [timeFrameCoeff_eq_coordDeriv_of_contMDiffAt (I := I) hF hx i]
  rw [← hcomp]
  exact hmf_apply

/-- Local version of `SmoothSurface.paramFrameCoeff_eq_coordParamDeriv`. -/
theorem paramFrameCoeff_eq_coordParamDeriv_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
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
  have hg : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) g s := by
    have hcomp := (coordAt_contMDiffAt_of_contMDiffAt (I := I) hF hx).comp s hline
    exact hcomp.mdifferentiableAt (by simp)
  have hscalar : HasDerivAt
      (fun σ : Real => surfaceCoordComp (I := I) x₀ F (σ, t) i)
      (coordParamDeriv (I := I) x₀ F s t i) s := by
    have hdiff : DifferentiableAt Real
        (fun p : Real × Real => surfaceCoordComp (I := I) x₀ F p i) (s, t) :=
      (coordCompAt_contDiffAt_of_contMDiffAt (I := I) hF hx i).differentiableAt
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
  rw [paramFrameCoeff_eq_coordDeriv_of_contMDiffAt (I := I) hF hx i]
  rw [← hcomp]
  exact hmf_apply

/-- Local-on-open version of
`SmoothSurface.timeFrameCoeff_param_hasDerivAt_of_mem`. -/
theorem timeFrameCoeff_param_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ t i)
      (coordTs (I := I) x₀ F s t i) s := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordTimeDeriv (I := I) x₀ F p.1 p.2 i
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using coordCompAt_contDiffAt_of_contMDiffAt (I := I) hFat hx i
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
  have hline_mem : ∀ᶠ σ : Real in 𝓝 s, (σ, t) ∈ U := by
    have hline : ContinuousAt (fun σ : Real => (σ, t)) s :=
      ContinuousAt.prodMk continuousAt_id continuousAt_const
    have hcomp : ContinuousAt (fun σ : Real => (σ, t)) s := hline
    exact hcomp.eventually_mem (hU.mem_nhds hp)
  have heq :
      (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ t i)
        =ᶠ[𝓝 s] fun σ : Real => A (σ, t) := by
    filter_upwards
      [coordMem_param_of_mem_of_contMDiffAt (I := I) hFat hx, hline_mem]
      with σ hσ hσU
    have hFσ : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (σ, t) :=
      hF.contMDiffAt (hU.mem_nhds hσU)
    simpa [A] using
      timeFrameCoeff_eq_coordTimeDeriv_of_contMDiffAt (I := I) hFσ hσ i
  exact hderiv.congr_of_eventuallyEq heq

/-- Local-on-open version of
`SmoothSurface.paramFrameCoeff_time_hasDerivAt`. -/
theorem paramFrameCoeff_time_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real => paramFrameCoeff (I := I) x₀ F s τ i)
      (coordSt (I := I) x₀ F s t i) t := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordParamDeriv (I := I) x₀ F p.1 p.2 i
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using coordCompAt_contDiffAt_of_contMDiffAt (I := I) hFat hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) ((1 : Real), 0)) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordParamDeriv] using hD
  have hderiv :
      HasDerivAt (fun τ : Real => A (s, τ))
        (coordSt (I := I) x₀ F s t i) t := by
    have hdiff : DifferentiableAt Real A (s, t) :=
      hA.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    simpa [A, coordSt] using
      modelLine_snd_hasDerivAt (A := A) (s := s) (t := t) hdiff
  have hline_mem : ∀ᶠ τ : Real in 𝓝 t, (s, τ) ∈ U := by
    have hline : ContinuousAt (fun τ : Real => (s, τ)) t :=
      ContinuousAt.prodMk continuousAt_const continuousAt_id
    exact hline.eventually_mem (hU.mem_nhds hp)
  have heq :
      (fun τ : Real => paramFrameCoeff (I := I) x₀ F s τ i)
        =ᶠ[𝓝 t] fun τ : Real => A (s, τ) := by
    filter_upwards
      [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx, hline_mem]
      with τ hτ hτU
    have hFτ : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, τ) :=
      hF.contMDiffAt (hU.mem_nhds hτU)
    simpa [A] using
      paramFrameCoeff_eq_coordParamDeriv_of_contMDiffAt (I := I) hFτ hτ i
  exact hderiv.congr_of_eventuallyEq heq

/-- Local-on-open version of
`SmoothSurface.timeFrameCoeff_time_hasDerivAt_of_mem`. -/
theorem timeFrameCoeff_time_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun τ : Real => timeFrameCoeff (I := I) x₀ F s τ i)
      (coordTt (I := I) x₀ F s t i) t := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  let A : Real × Real -> Real :=
    fun p => coordTimeDeriv (I := I) x₀ F p.1 p.2 i
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using coordCompAt_contDiffAt_of_contMDiffAt (I := I) hFat hx i
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
  have hline_mem : ∀ᶠ τ : Real in 𝓝 t, (s, τ) ∈ U := by
    have hline : ContinuousAt (fun τ : Real => (s, τ)) t :=
      ContinuousAt.prodMk continuousAt_const continuousAt_id
    exact hline.eventually_mem (hU.mem_nhds hp)
  have heq :
      (fun τ : Real => timeFrameCoeff (I := I) x₀ F s τ i)
        =ᶠ[𝓝 t] fun τ : Real => A (s, τ) := by
    filter_upwards
      [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx, hline_mem]
      with τ hτ hτU
    have hFτ : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, τ) :=
      hF.contMDiffAt (hU.mem_nhds hτU)
    simpa [A] using
      timeFrameCoeff_eq_coordTimeDeriv_of_contMDiffAt (I := I) hFτ hτ i
  exact hderiv.congr_of_eventuallyEq heq

/-- Local version of `SmoothSurface.coordTs_eq_coordSt`. -/
theorem coordTs_eq_coordSt_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordTs (I := I) x₀ F s t i =
      coordSt (I := I) x₀ F s t i := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  have hφTop : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using coordCompAt_contDiffAt_of_contMDiffAt (I := I) hF hx i
  have hφ2 : ContDiffAt Real 2 φ (s, t) :=
    hφTop.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2
        (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  simpa [φ, coordTs, coordSt, coordTimeDeriv, coordParamDeriv] using
    modelMix2 (φ := φ) (s := s) (t := t) hφ2

/-- Local version of `SmoothSurface.coordVst_eq_coordVts`. -/
theorem coordVst_eq_coordVts_of_contMDiffAt {F : Surface M}
    {x₀ : M} {s t : Real}
    (hF : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t))
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordVst (I := I) x₀ F s t i =
      coordVts (I := I) x₀ F s t i := by
  let φ : Real × Real -> Real :=
    fun p => surfaceCoordComp (I := I) x₀ F p i
  have hφTop : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using coordCompAt_contDiffAt_of_contMDiffAt (I := I) hF hx i
  have hφ3 : ContDiffAt Real 3 φ (s, t) :=
    hφTop.of_le (by
      change ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2
        (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  simpa [φ, coordVst, coordVts, coordTt, coordTs, coordTimeDeriv] using
    modelMix3 (φ := φ) (s := s) (t := t) hφ3

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

/-- Local-on-open version of `SmoothSurface.christoffel_param_hasDerivAt`. -/
theorem christoffel_param_hasDerivAt_of_mem_on
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U)
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
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hcurve : MDifferentiableAt 𝓘(Real, Real) I
      (surfaceParamCurve F t) s :=
    mdiffAt_param_of_contMDiffAt (I := I) hFat
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

/-- Local-on-open version of `SmoothSurface.christoffel_time_hasDerivAt`. -/
theorem christoffel_time_hasDerivAt_of_mem_on
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U)
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
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hcurve : MDifferentiableAt 𝓘(Real, Real) I
      (surfaceTimeCurve F s) t :=
    mdiffAt_time_of_contMDiffAt (I := I) hFat
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
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
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
      change ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
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
    {ι : Type*} [Fintype ι]
    (S T : ι -> Real) (C : ι -> ι -> ι -> Real)
    (hsym : ∀ i j k : ι, C i j k = C j i k) :
    Matrix.mulVec ((fun k j => ∑ i : ι, T i * C i j k) : Matrix ι ι Real) S =
      Matrix.mulVec ((fun k j => ∑ i : ι, S i * C i j k) : Matrix ι ι Real) T := by
  classical
  ext k
  simp only [Matrix.mulVec, dotProduct]
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

/-- Local-on-open version of `SmoothSurface.coordTt_param_hasDerivAt_of_mem`. -/
theorem coordTt_param_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
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
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using coordCompAt_contDiffAt_of_contMDiffAt (I := I) hFat hx i
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

/-- Local-on-open version of `SmoothSurface.coordTs_time_hasDerivAt_of_mem`. -/
theorem coordTs_time_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
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
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using coordCompAt_contDiffAt_of_contMDiffAt (I := I) hFat hx i
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

/-- Local-on-open vector-valued parameter derivative of the fixed-frame time
field coefficients. -/
theorem frameVec_time_param_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    HasDerivAt
      (fun σ : Real =>
        frameVec (I := I) (coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (surfaceTimeField (I := I) F (σ, t)))
      (coordTs (I := I) x₀ F s t) s := by
  let e := coordinateTrivializationAt (I := I) x₀
  rw [hasDerivAt_pi]
  intro i
  have hscalar := timeFrameCoeff_param_hasDerivAt_of_mem_on
    (I := I) (F := F) hU hF hp hx i
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have heq :
      (fun σ : Real =>
        frameVec (I := I) e (Module.finBasis Real E)
          (surfaceTimeField (I := I) F (σ, t)) i)
        =ᶠ[𝓝 s]
      (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ t i) := by
    filter_upwards [coordMem_param_of_mem_of_contMDiffAt (I := I) hFat hx] with σ hσ
    exact congrFun (frameVec_timeField_eq (I := I) x₀ hσ) i
  exact hscalar.congr_of_eventuallyEq heq.symm

/-- Local-on-open vector-valued time derivative of the fixed-frame time field
coefficients. -/
theorem frameVec_time_time_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) (coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (surfaceTimeField (I := I) F (s, τ)))
      (coordTt (I := I) x₀ F s t) t := by
  let e := coordinateTrivializationAt (I := I) x₀
  rw [hasDerivAt_pi]
  intro i
  have hscalar := timeFrameCoeff_time_hasDerivAt_of_mem_on
    (I := I) (F := F) hU hF hp hx i
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have heq :
      (fun τ : Real =>
        frameVec (I := I) e (Module.finBasis Real E)
          (surfaceTimeField (I := I) F (s, τ)) i)
        =ᶠ[𝓝 t]
      (fun τ : Real => timeFrameCoeff (I := I) x₀ F s τ i) := by
    filter_upwards [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx] with τ hτ
    exact congrFun (frameVec_timeField_eq (I := I) x₀ hτ) i
  exact hscalar.congr_of_eventuallyEq heq.symm

/-- Local-on-open parameter derivative of the time-direction `frameDerivVec`. -/
theorem frameDeriv_time_param_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    HasDerivAt
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (surfaceTimeCurve F σ)
          (fun τ => surfaceTimeField (I := I) F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t))
      (coordVst (I := I) x₀ F s t) s := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hcoord :
      HasDerivAt (fun σ : Real => coordTt (I := I) x₀ F σ t)
        (coordVst (I := I) x₀ F s t) s := by
    rw [hasDerivAt_pi]
    intro i
    exact coordTt_param_hasDerivAt_of_mem_on (I := I) (F := F) hU hF hp hx i
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have heq :
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          e (Module.finBasis Real E) (surfaceTimeCurve F σ)
          (fun τ => surfaceTimeField (I := I) F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        =ᶠ[𝓝 s]
      (fun σ : Real => coordTt (I := I) x₀ F σ t) := by
    have hlineU : ∀ᶠ σ : Real in 𝓝 s, (σ, t) ∈ U := by
      have hline : ContinuousAt (fun σ : Real => (σ, t)) s :=
        ContinuousAt.prodMk continuousAt_id continuousAt_const
      exact hline.eventually_mem (hU.mem_nhds hp)
    filter_upwards [coordMem_param_of_mem_of_contMDiffAt (I := I) hFat hx,
      hlineU] with σ hσ hσU
    have hvec :
        HasDerivAt
          (fun τ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)))
          (coordTt (I := I) x₀ F σ t) t := by
      rw [hasDerivAt_pi]
      intro i
      have hline :
          (fun τ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)) i)
            =ᶠ[𝓝 t]
          (fun τ : Real => timeFrameCoeff (I := I) x₀ F σ τ i) := by
        filter_upwards [coordMem_time_of_mem_of_contMDiffAt
          (I := I) (hF.contMDiffAt (hU.mem_nhds hσU)) hσ] with τ hτ
        exact congrFun (frameVec_timeField_eq (I := I) x₀ hτ) i
      have hscalar :
          HasDerivAt
            (fun τ : Real => timeFrameCoeff (I := I) x₀ F σ τ i)
            (coordTt (I := I) x₀ F σ t i) t := by
        exact timeFrameCoeff_time_hasDerivAt_of_mem_on
          (I := I) (F := F) hU hF hσU hσ i
      exact hscalar.congr_of_eventuallyEq hline.symm
    exact frameDerivVec_eq_of_hasDerivAt (I := I) e (Module.finBasis Real E)
      (gamma := surfaceTimeCurve F σ)
      (S := fun τ => surfaceTimeField (I := I) F (σ, τ)) hvec
  exact hcoord.congr_of_eventuallyEq heq

/-- Local-on-open time derivative of the parameter-direction `frameDerivVec`
for the time field. -/
theorem frameDeriv_param_time_hasDerivAt_of_mem_on {F : Surface M}
    {U : Set (Real × Real)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x₀ : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀) :
    HasDerivAt
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (coordinateTrivializationAt (I := I) x₀)
          (Module.finBasis Real E) (surfaceParamCurve F τ)
          (fun σ => surfaceTimeField (I := I) F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s))
      (coordVts (I := I) x₀ F s t) t := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hcoord :
      HasDerivAt (fun τ : Real => coordTs (I := I) x₀ F s τ)
        (coordVts (I := I) x₀ F s t) t := by
    rw [hasDerivAt_pi]
    intro i
    exact coordTs_time_hasDerivAt_of_mem_on (I := I) (F := F) hU hF hp hx i
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have heq :
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          e (Module.finBasis Real E) (surfaceParamCurve F τ)
          (fun σ => surfaceTimeField (I := I) F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        =ᶠ[𝓝 t]
      (fun τ : Real => coordTs (I := I) x₀ F s τ) := by
    have hlineU : ∀ᶠ τ : Real in 𝓝 t, (s, τ) ∈ U := by
      have hline : ContinuousAt (fun τ : Real => (s, τ)) t :=
        ContinuousAt.prodMk continuousAt_const continuousAt_id
      exact hline.eventually_mem (hU.mem_nhds hp)
    filter_upwards [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx,
      hlineU] with τ hτ hτU
    have hvec :
        HasDerivAt
          (fun σ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)))
          (coordTs (I := I) x₀ F s τ) s := by
      rw [hasDerivAt_pi]
      intro i
      have hline :
          (fun σ : Real =>
            frameVec (I := I) e (Module.finBasis Real E)
              (surfaceTimeField (I := I) F (σ, τ)) i)
            =ᶠ[𝓝 s]
          (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ τ i) := by
        filter_upwards [coordMem_param_of_mem_of_contMDiffAt
          (I := I) (hF.contMDiffAt (hU.mem_nhds hτU)) hτ] with σ hσ
        exact congrFun (frameVec_timeField_eq (I := I) x₀ hσ) i
      have hscalar :
          HasDerivAt
            (fun σ : Real => timeFrameCoeff (I := I) x₀ F σ τ i)
            (coordTs (I := I) x₀ F s τ i) s := by
        exact timeFrameCoeff_param_hasDerivAt_of_mem_on
          (I := I) (F := F) hU hF hτU hτ i
      exact hscalar.congr_of_eventuallyEq hline.symm
    exact frameDerivVec_eq_of_hasDerivAt (I := I) e (Module.finBasis Real E)
      (gamma := surfaceParamCurve F τ)
      (S := fun σ => surfaceTimeField (I := I) F (σ, τ)) hvec
  exact hcoord.congr_of_eventuallyEq heq

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


end Lecture07
end GlobalGeometry
end RicciFlower
