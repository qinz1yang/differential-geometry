import RicciFlower.GlobalGeometry.Lecture07.SurfaceCalculus.Base

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Mixed surface calculus fields

This file contains the higher-order mixed-derivative field layer split out of
`RicciFlower.GlobalGeometry.Lecture07.SurfaceCalculus`.
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

/-- Local-on-open version of `SmoothSurface.coordSurfJet`. -/
def coordSurfJet_of_contMDiffOn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U) :
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
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [x₀] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hS :
      ∀ i : CoordinateIdx (𝕜 := Real) E,
        paramFrameCoeff (I := I) x₀ F s t i = S i := by
    intro i
    simpa [S, x₀] using
      paramFrameCoeff_eq_coordParamDeriv_of_contMDiffAt (I := I) hFat hx i
  have hT :
      ∀ i : CoordinateIdx (𝕜 := Real) E,
        timeFrameCoeff (I := I) x₀ F s t i = T i := by
    intro i
    simpa [T, x₀] using
      timeFrameCoeff_eq_coordTimeDeriv_of_contMDiffAt (I := I) hFat hx i
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
  · simpa [x₀] using coordMem_param_of_mem_of_contMDiffAt (I := I) hFat hx
  · simpa [x₀] using coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx
  · intro i
    simpa [Ts, x₀] using
      timeFrameCoeff_param_hasDerivAt_of_mem_on
        (I := I) (F := F) hU hF hp hx i
  · intro i
    simpa [St, x₀] using
      paramFrameCoeff_time_hasDerivAt_of_mem_on
        (I := I) (F := F) hU hF hp hx i
  · intro i j k
    simpa [S, x₀] using
      christoffel_param_hasDerivAt_of_mem_on
        (I := I) (cov := cov) hcov hU hF hp S hS i j k
  · intro i j k
    simpa [T, x₀] using
      christoffel_time_hasDerivAt_of_mem_on
        (I := I) (cov := cov) hcov hU hF hp T hT i j k
  · simpa [vst, x₀] using
      frameDeriv_time_param_hasDerivAt_of_mem_on
        (I := I) (F := F) hU hF hp hx
  · simpa [Ts, x₀] using
      frameVec_time_param_hasDerivAt_of_mem_on
        (I := I) (F := F) hU hF hp hx
  · simpa [vts, x₀] using
      frameDeriv_param_time_hasDerivAt_of_mem_on
        (I := I) (F := F) hU hF hp hx
  · simpa [vt, x₀] using
      frameVec_time_time_hasDerivAt_of_mem_on
        (I := I) (F := F) hU hF hp hx
  · ext i
    simpa [vst, vts, x₀] using
      coordVst_eq_coordVts_of_contMDiffAt (I := I) hFat hx i
  · ext i
    simpa [Ts, St, x₀] using
      coordTs_eq_coordSt_of_contMDiffAt (I := I) hFat hx i

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

/-- Fixed-center coefficient vector for `D_t T` in the coordinate frame
centered at `x0`.  This is the pointwise formula
`partial_t T + Gamma_t T`. -/
def dtTimeCoeffIn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real) :
    CoordinateIdx (𝕜 := Real) E -> Real :=
  coeffCov
    (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
      (coordinateTrivializationAt (I := I) x0) (Module.finBasis Real E)
      (surfaceTimeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t))
    (coordTt (I := I) x0 F s t)
    (frameVec (I := I) (coordinateTrivializationAt (I := I) x0)
      (Module.finBasis Real E) (surfaceTimeField (I := I) F (s, t)))

/-- Fixed-center tangent vector represented by `dtTimeCoeffIn`. -/
def dtTimeFieldIn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (F : Surface M) (s t : Real) : TangentSpace I (F (s, t)) :=
  frameSum (I := I) (coordinateTrivializationAt (I := I) x0)
    (Module.finBasis Real E)
    (dtTimeCoeffIn (I := I) cov x0 F s t)

/-- Centered coefficient vector for the canonical `D_t T` surface field. -/
def dtTimeCoeff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s t : Real) :
    CoordinateIdx (𝕜 := Real) E -> Real :=
  dtTimeCoeffIn (I := I) cov (F (s, t)) F s t

/-- Canonical surface field for the time acceleration `D_t T`. -/
def dtTimeField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) : SurfaceFieldAlong I F :=
  fun p => dtTimeFieldIn (I := I) cov (F p) F p.1 p.2

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

/-- Fixed-center construction of `D_t T`. -/
theorem SmoothSurface.hasTime_timeIn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x0) :
    HasPBTimeCovDerivAt (I := I) cov F (surfaceTimeField (I := I) F)
      s t (dtTimeFieldIn (I := I) cov x0 F s t) := by
  classical
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  have hxE : F (s, t) ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    hF.mdiffAt_time (I := I) s t
  have hvec : HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) e b (surfaceTimeField (I := I) F (s, τ)))
      (coordTt (I := I) x0 F s t) t := by
    rw [hasDerivAt_pi]
    intro i
    have hscalar := hF.timeFrameCoeff_time_hasDerivAt_of_mem
      (I := I) (x₀ := x0) (s := s) (t := t) hx i
    have heq :
        (fun τ : Real =>
          frameVec (I := I) e b (surfaceTimeField (I := I) F (s, τ)) i)
          =ᶠ[𝓝 t]
        (fun τ : Real => timeFrameCoeff (I := I) x0 F s τ i) := by
      filter_upwards [hF.coordMem_time_of_mem (I := I) hx] with τ hτ
      exact congrFun (frameVec_timeField_eq (I := I) x0 hτ) i
    exact hscalar.congr_of_eventuallyEq heq.symm
  have hframe := HasFrameAlongAt.of_frameVec_hasDerivAt
    (I := I) (cov := cov) (e := e) (b := b)
    (gamma := surfaceTimeCurve F s)
    (S := fun τ => surfaceTimeField (I := I) F (s, τ))
    hxE hgamma hvec
  have htarget :
      frameSum (I := I) e b
        (coeffCov
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t))
          (coordTt (I := I) x0 F s t)
          (frameVec (I := I) e b (surfaceTimeField (I := I) F (s, t)))) =
        dtTimeFieldIn (I := I) cov x0 F s t := by
    rfl
  rw [← htarget]
  exact HasPBCovDerivAt.ofFrame (I := I) (I' := 𝓘(Real, Real)) hframe

/-- Centered construction of `D_t T`. -/
theorem SmoothSurface.hasTime_time
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasPBTimeCovDerivAt (I := I) cov F (surfaceTimeField (I := I) F)
      s t (dtTimeField (I := I) cov F (s, t)) := by
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  simpa [dtTimeField] using
    hF.hasTime_timeIn (I := I) (cov := cov) hx

/-- The centered `D_t T` field agrees near a point with the same construction
written in that point's fixed coordinate frame. -/
theorem SmoothSurface.dtTimeField_eq_fixed_eventually
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ∀ᶠ τ : Real in 𝓝 t,
      dtTimeField (I := I) cov F (s, τ) =
        dtTimeFieldIn (I := I) cov (F (s, t)) F s τ := by
  filter_upwards [hF.coordMem_time (I := I) s t] with τ hτ
  have hcenter := hF.hasTime_time (I := I) (cov := cov) s τ
  have hfixed := hF.hasTime_timeIn (I := I) (cov := cov) hτ
  exact HasPBTimeCovDerivAt.unique (I := I) hcenter hfixed

/-- The centered `D_s T` field agrees near a point in the parameter surface
with the same construction written in that point's fixed coordinate frame. -/
theorem SmoothSurface.dsTimeField_eq_fixed_eventually_prod
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ∀ᶠ p : Real × Real in 𝓝 (s, t),
      dsTimeField (I := I) cov F p =
        dsTimeFieldIn (I := I) cov (F (s, t)) F p.1 p.2 := by
  have hU : IsOpen (coordinateFrameSet (I := I) (F (s, t))) :=
    coordinateFrameSet_open (I := I) (F (s, t))
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
      F p ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
  filter_upwards [hmem] with p hp
  have hcenter := hF.hasParam_dsTime (I := I) (cov := cov) p.1 p.2
  have hfixed := hF.hasParam_dsTimeIn (I := I) (cov := cov) hp
  exact HasPBParamCovDerivAt.unique (I := I) hcenter hfixed

/-- The centered `D_t T` field agrees near a point in the parameter surface
with the same construction written in that point's fixed coordinate frame. -/
theorem SmoothSurface.dtTimeField_eq_fixed_eventually_prod
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ∀ᶠ p : Real × Real in 𝓝 (s, t),
      dtTimeField (I := I) cov F p =
        dtTimeFieldIn (I := I) cov (F (s, t)) F p.1 p.2 := by
  have hU : IsOpen (coordinateFrameSet (I := I) (F (s, t))) :=
    coordinateFrameSet_open (I := I) (F (s, t))
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
      F p ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
  filter_upwards [hmem] with p hp
  have hcenter := hF.hasTime_time (I := I) (cov := cov) p.1 p.2
  have hfixed := hF.hasTime_timeIn (I := I) (cov := cov) hp
  exact HasPBTimeCovDerivAt.unique (I := I) hcenter hfixed

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

/-- Local-on-open construction of `D_s T` in a fixed coordinate frame. -/
theorem hasParam_dsTimeIn_of_contMDiffOn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {x0 : M} {s t : Real} (hp : (s, t) ∈ U)
    (hx : F (s, t) ∈ coordinateFrameSet (I := I) x0) :
    HasPBParamCovDerivAt (I := I) cov F (surfaceTimeField (I := I) F)
      s t (dsTimeFieldIn (I := I) cov x0 F s t) := by
  classical
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  have hxE : F (s, t) ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceParamCurve F t) s :=
    mdiffAt_param_of_contMDiffAt (I := I) hFat
  have hvec : HasDerivAt
      (fun σ : Real =>
        frameVec (I := I) e b (surfaceTimeField (I := I) F (σ, t)))
      (coordTs (I := I) x0 F s t) s := by
    rw [hasDerivAt_pi]
    intro i
    have hscalar := timeFrameCoeff_param_hasDerivAt_of_mem_on
      (I := I) (F := F) hU hF hp hx i
    have heq :
        (fun σ : Real =>
          frameVec (I := I) e b (surfaceTimeField (I := I) F (σ, t)) i)
          =ᶠ[𝓝 s]
        (fun σ : Real => timeFrameCoeff (I := I) x0 F σ t i) := by
      filter_upwards [coordMem_param_of_mem_of_contMDiffAt (I := I) hFat hx] with σ hσ
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

/-- Local-on-open centered construction of `D_s T`. -/
theorem hasParam_dsTime_of_contMDiffOn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U) :
    HasPBParamCovDerivAt (I := I) cov F (surfaceTimeField (I := I) F)
      s t (dsTimeField (I := I) cov F (s, t)) := by
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) (F (s, t)) :=
    coordinateFrameAt_mem (I := I) (F (s, t))
  simpa [dsTimeField] using
    hasParam_dsTimeIn_of_contMDiffOn (I := I) (cov := cov)
      hU hF hp hx

/-- Local-on-open torsion-free coordinate calculus identifies `D_t S` with
the canonical `D_s T` field. -/
theorem hasTime_param_eq_dsTime_of_contMDiffOn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U) :
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
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x0 := by
    simpa [x0] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hxE : F (s, t) ∈ e.baseSet := by
    simp [e, x0, coordinateFrameSet, coordinateTrivializationAt] at hx ⊢
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    mdiffAt_time_of_contMDiffAt (I := I) hFat
  have hvec : HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) e b (surfaceParamField (I := I) F (s, τ)))
      (coordSt (I := I) x0 F s t) t := by
    rw [hasDerivAt_pi]
    intro i
    have hscalar := paramFrameCoeff_time_hasDerivAt_of_mem_on
      (I := I) (F := F) hU hF hp hx i
    have heq :
        (fun τ : Real =>
          frameVec (I := I) e b (surfaceParamField (I := I) F (s, τ)) i)
          =ᶠ[𝓝 t]
        (fun τ : Real => paramFrameCoeff (I := I) x0 F s τ i) := by
      filter_upwards [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx] with τ hτ
      exact congrFun (frameVec_paramField_eq (I := I) x0 hτ) i
    exact hscalar.congr_of_eventuallyEq heq.symm
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
    simpa [S, x0] using
      paramFrameCoeff_eq_coordParamDeriv_of_contMDiffAt (I := I) hFat hx i
  have hTvec :
      frameVec (I := I) e b (surfaceTimeField (I := I) F (s, t)) = T := by
    have h := frameVec_timeField_eq (I := I) x0 hx
    ext i
    rw [congrFun h i]
    simpa [T, x0] using
      timeFrameCoeff_eq_coordTimeDeriv_of_contMDiffAt (I := I) hFat hx i
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
            rw [timeFrameCoeff_eq_coordTimeDeriv_of_contMDiffAt (I := I) hFat hx i]
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
            rw [paramFrameCoeff_eq_coordParamDeriv_of_contMDiffAt (I := I) hFat hx i]
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
      simpa [x0] using
        (coordTs_eq_coordSt_of_contMDiffAt (I := I) hFat hx i).symm
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

/-- Local-on-open time derivative of the fixed-center coefficient vector for
`D_s T`. -/
theorem dsTimeCoeffIn_hasDerivAt_of_contMDiffOn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U) :
    HasDerivAt
      (fun τ : Real =>
        dsTimeCoeffIn (I := I) cov (F (s, t)) F s τ)
      (dsTimeCoeffTimeDerivIn (I := I) cov (F (s, t)) F s t) t := by
  classical
  let x0 : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  let jet := coordSurfJet_of_contMDiffOn (I := I) (cov := cov) hcov hU hF hp
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
    exact coordTs_time_hasDerivAt_of_mem_on (I := I) (F := F) hU hF hp hx i
  have hT :
      HasDerivAt
        (fun τ : Real =>
          frameVec (I := I) e b (surfaceTimeField (I := I) F (s, τ)))
        (coordTt (I := I) x0 F s t) t := by
    simpa [x0, e, b] using
      frameVec_time_time_hasDerivAt_of_mem_on (I := I) (F := F) hU hF hp hx
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

/-- Local-on-open fixed-center construction of `D_t(D_s T)`. -/
theorem hasTime_dsTimeIn_of_contMDiffOn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U) :
    HasPBTimeCovDerivAt (I := I) cov F
      (fun p : Real × Real =>
        dsTimeFieldIn (I := I) cov (F (s, t)) F p.1 p.2)
      s t (dtdsTimeFieldIn (I := I) cov (F (s, t)) F s t) := by
  classical
  let x0 : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x0 := by
    simpa [x0] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hxE : F (s, t) ∈ e.baseSet := by
    simp [e, x0, coordinateFrameSet, coordinateTrivializationAt] at hx ⊢
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    mdiffAt_time_of_contMDiffAt (I := I) hFat
  have hcoeff := dsTimeCoeffIn_hasDerivAt_of_contMDiffOn
    (I := I) (cov := cov) hcov hU hF hp
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
      filter_upwards [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx] with τ hτ
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

/-- Local-on-open centered construction of `D_t(D_s T)`. -/
theorem hasTime_dsTime_of_contMDiffOn
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {U : Set (Real × Real)}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    {s t : Real} (hp : (s, t) ∈ U) :
    HasPBTimeCovDerivAt (I := I) cov F (dsTimeField (I := I) cov F)
      s t (dtdsTimeFieldIn (I := I) cov (F (s, t)) F s t) := by
  classical
  let x0 : M := F (s, t)
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
    hF.contMDiffAt (hU.mem_nhds hp)
  have hx : F (s, t) ∈ coordinateFrameSet (I := I) x0 := by
    simpa [x0] using coordinateFrameAt_mem (I := I) (F (s, t))
  have hxE : F (s, t) ∈ e.baseSet := by
    simp [e, x0, coordinateFrameSet, coordinateTrivializationAt] at hx ⊢
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t :=
    mdiffAt_time_of_contMDiffAt (I := I) hFat
  have hcoeff := dsTimeCoeffIn_hasDerivAt_of_contMDiffOn
    (I := I) (cov := cov) hcov hU hF hp
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
      filter_upwards [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx] with τ hτ
      have hτE : F (s, τ) ∈ e.baseSet := by
        simpa [e, x0, coordinateFrameSet, coordinateTrivializationAt] using hτ
      exact frameVec_frameSum (I := I) e b hτE
        (dsTimeCoeffIn (I := I) cov x0 F s τ)
    simpa [x0] using hcoeff.congr_of_eventuallyEq heq
  have hvec : HasDerivAt
      (fun τ : Real =>
        frameVec (I := I) e b (dsTimeField (I := I) cov F (s, τ)))
      (dsTimeCoeffTimeDerivIn (I := I) cov x0 F s t) t := by
    have hlineU : ∀ᶠ τ : Real in 𝓝 t, (s, τ) ∈ U := by
      have hline : ContinuousAt (fun τ : Real => (s, τ)) t :=
        ContinuousAt.prodMk continuousAt_const continuousAt_id
      exact hline.eventually_mem (hU.mem_nhds hp)
    have heq :
        (fun τ : Real =>
          frameVec (I := I) e b (dsTimeField (I := I) cov F (s, τ)))
          =ᶠ[𝓝 t]
        (fun τ : Real =>
          frameVec (I := I) e b
            (dsTimeFieldIn (I := I) cov x0 F s τ)) := by
      filter_upwards [coordMem_time_of_mem_of_contMDiffAt (I := I) hFat hx,
        hlineU] with τ hτ hτU
      have hcenter := hasParam_dsTime_of_contMDiffOn
        (I := I) (cov := cov) hU hF hτU
      have hfixed := hasParam_dsTimeIn_of_contMDiffOn
        (I := I) (cov := cov) hU hF hτU hτ
      have huniq := HasPBParamCovDerivAt.unique (I := I) hcenter hfixed
      rw [huniq]
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
    have hcenter := hasParam_dsTime_of_contMDiffOn
      (I := I) (cov := cov) hU hF hp
    have hfixed := hasParam_dsTimeIn_of_contMDiffOn
      (I := I) (cov := cov) hU hF hp hx
    have huniq := HasPBParamCovDerivAt.unique (I := I) hcenter hfixed
    have hself :
        frameVec (I := I) e b (dsTimeField (I := I) cov F (s, t)) =
          dsTimeCoeffIn (I := I) cov x0 F s t := by
      rw [huniq]
      exact frameVec_frameSum (I := I) e b hxE
        (dsTimeCoeffIn (I := I) cov x0 F s t)
    rw [hself]
    rfl
  rw [← htarget]
  exact HasPBCovDerivAt.ofFrame (I := I) (I' := 𝓘(Real, Real)) hframe

end MixedFields

end Lecture07
end GlobalGeometry
end RicciFlower
