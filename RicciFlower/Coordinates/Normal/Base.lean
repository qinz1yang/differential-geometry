import RicciFlower.Coordinates.ChartRegistration
import RicciFlower.GlobalGeometry.Lecture07.SprayChartPush
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate normal coordinates

This file contains the reusable coordinate-defined normal-coordinate front end.
It deliberately starts with relation-valued endpoint data instead of defining
an exponential map as a function.  A functional exponential map requires the
next analytic layer: uniqueness and smooth dependence of the local geodesic
flow on initial velocity.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open scoped Manifold ContDiff Topology
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-! ## Coordinate geodesic segments -/

/-- A curve satisfies the coordinate-defined geodesic equation on `s`, in the
fixed `extChartAt x0` coordinates.

This is intentionally coordinate-level.  It uses the canonical
`HasCoordCovAccelAt` predicate introduced in `CoordinateEquation.lean`, not the
older global-representative acceleration relation. -/
def IsCoordGeodesicOn
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (gamma : Curve M) (s : Set Real) : Prop :=
  (∀ t : Real, t ∈ s -> gamma t ∈ coordinateFrameSet (I := I) x0) ∧
    ∀ t : Real, t ∈ s ->
      HasCoordCovAccelAt (I := I) x0
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        gamma t 0

/-- A coordinate geodesic segment with prescribed initial tangent vector. -/
def IsCoordGeodesicSegment
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x)
    (gamma : Curve M) (s : Set Real) : Prop :=
  gamma 0 = x ∧
    curveVelocityBundle I gamma 0 = (⟨x, v⟩ : TangentBundle I M) ∧
      IsCoordGeodesicOn (I := I) g x gamma s

/-- A coordinate geodesic segment retaining the tangent-bundle spray witness.

This is the producer-side API for arguments, such as speed constancy and the
Gauss lemma, that need the regularity carried by the spray integral curve.  The
older relation-valued endpoint API intentionally forgets this witness. -/
structure SprayRadialSegment
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) where
  epsilon : Real
  epsilon_pos : 0 < epsilon
  interval_subset : Set.uIcc (0 : Real) 1 ⊆ Metric.ball (0 : Real) epsilon
  lift : Real -> TangentBundle I M
  lift_initial : lift 0 = (⟨x, v⟩ : TangentBundle I M)
  spray_integral :
    IsMIntegralCurveOn lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) epsilon)
  source :
    ∀ t ∈ Metric.ball (0 : Real) epsilon,
      projectCurve (I := I) lift t ∈
        (extChartAtCoordinateData (I := I) x).domain

namespace SprayRadialSegment

/-- The base curve of a spray-backed radial segment. -/
def gamma
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v) : Curve M :=
  projectCurve (I := I) G.lift

@[simp] theorem gamma_apply
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v) (t : Real) :
    G.gamma t = (G.lift t).proj :=
  rfl

theorem gamma_zero
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v) :
    G.gamma 0 = x := by
  simpa [gamma] using
    projectCurve_zero_of_lift (I := I)
      (u := (⟨x, v⟩ : TangentBundle I M)) G.lift_initial

theorem velocity_zero
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v) :
    curveVelocityBundle I G.gamma 0 =
      (⟨x, v⟩ : TangentBundle I M) := by
  have hf0 : IsMIntegralCurveAt G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x) 0 :=
    G.spray_integral.isMIntegralCurveAt
      (Metric.ball_mem_nhds (0 : Real) G.epsilon_pos)
  simpa [gamma] using
    projectCurve_initialVelocity_of_geodesicSprayIntegral
      (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
      (f := G.lift) G.lift_initial hf0

theorem integralAt
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v)
    {t : Real} (ht : t ∈ Metric.ball (0 : Real) G.epsilon) :
    IsMIntegralCurveAt G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t :=
  G.spray_integral.isMIntegralCurveAt (Metric.isOpen_ball.mem_nhds ht)

theorem lift_mdiffAt
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v)
    {t : Real} (ht : t ∈ Metric.ball (0 : Real) G.epsilon) :
    MDifferentiableAt 𝓘(Real, Real) I.tangent G.lift t :=
  (G.integralAt ht).hasMFDerivAt.mdifferentiableAt

theorem gamma_mdiffAt
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v)
    {t : Real} (ht : t ∈ Metric.ball (0 : Real) G.epsilon) :
    MDifferentiableAt 𝓘(Real, Real) I G.gamma t := by
  have hproj :
      MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M -> M) (G.lift t) := by
    exact (Bundle.contMDiffAt_proj (F := E) (E := TangentSpace I)
      (IB := I) (n := (1 : WithTop ℕ∞)) (p := G.lift t)).mdifferentiableAt
        one_ne_zero
  simpa [gamma, projectCurve, Function.comp_def] using
    hproj.comp t (G.lift_mdiffAt ht)

theorem geoOn
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v) :
    IsCoordGeodesicOn (I := I) g x G.gamma
      (Metric.ball (0 : Real) G.epsilon) := by
  constructor
  · intro t ht
    simpa [gamma] using G.source t ht
  · intro t ht
    have hode :=
      coordSprayODEOn (I := I) (g := g) (x := x) (v := v)
        (lift := G.lift) (epsilon := G.epsilon) (t := t)
        G.lift_initial G.spray_integral ht G.source
    simpa [gamma] using hode.zeroAccel

theorem segment
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v) :
    IsCoordGeodesicSegment (I := I) g x v G.gamma
      (Metric.ball (0 : Real) G.epsilon) :=
  ⟨G.gamma_zero, G.velocity_zero, G.geoOn⟩

end SprayRadialSegment

/-- Relation-valued coordinate exponential endpoint at time `tau`.

The relation says that some coordinate-defined geodesic segment with initial
data `(x, v)` reaches `y` at time `tau`.  The set `s` is explicit so later
theorems can use intervals, balls, or compact subintervals without changing
the public endpoint relation. -/
def CoordExpRelAtTime
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (tau : Real) (y : M) : Prop :=
  ∃ s : Set Real,
    Set.uIcc 0 tau ⊆ s ∧
      ∃ gamma : Curve M,
        IsCoordGeodesicSegment (I := I) g x v gamma s ∧
          gamma tau = y

/-- Relation-valued coordinate exponential endpoint at time `1`. -/
def CoordExpRel
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (y : M) : Prop :=
  CoordExpRelAtTime (I := I) g x v 1 y

/-! ## Short endpoint API -/

/-- Short public name for the time-one relation-valued coordinate exponential.

This is still a relation, not a function: uniqueness and smooth dependence of
the chart-fixed geodesic flow are the next analytic layer. -/
def expAt
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (y : M) : Prop :=
  CoordExpRel (I := I) g x v y

@[simp] theorem expAt_iff
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (y : M) :
    expAt (I := I) g x v y ↔ CoordExpRel (I := I) g x v y :=
  Iff.rfl

/-- Package a coordinate geodesic segment whose time domain contains `0` and
`1` as a time-one endpoint relation. -/
theorem expAt_of_segment
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {gamma : Curve M} {s : Set Real}
    (hs : Set.uIcc 0 1 ⊆ s)
    (hseg : IsCoordGeodesicSegment (I := I) g x v gamma s) :
    expAt (I := I) g x v (gamma 1) := by
  exact ⟨s, hs, gamma, hseg, rfl⟩

/-- A relation-valued coordinate exponential endpoint at time one lies in the
fixed coordinate chart used to define the coordinate geodesic segment. -/
theorem expAt_mem_source
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x} {y : M}
    (h : expAt (I := I) g x v y) :
    y ∈ coordinateFrameSet (I := I) x := by
  rcases h with ⟨s, hs, gamma, hseg, hgamma⟩
  have h1s : (1 : Real) ∈ s := hs Set.right_mem_uIcc
  have hcoord : gamma 1 ∈ coordinateFrameSet (I := I) x :=
    hseg.2.2.1 1 h1s
  simpa [hgamma] using hcoord

/-- Constant curves have zero coordinate-defined covariant acceleration in any
valid `extChartAt` coordinate package.

This reuses the representative-based compatibility layer only as a producer:
the ambient zero field realizes the velocity of a constant curve, and the
already-proved `toCoord` theorem converts that intrinsic pullback acceleration
to the coordinate-defined predicate. -/
private theorem coordAccel_const
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (x0 x : M) (t : Real)
    (hx : x ∈ coordinateFrameSet (I := I) x0) :
    HasCoordCovAccelAt (I := I) x0 cov (fun _ : Real => x) t 0 := by
  let gamma : Curve M := fun _ : Real => x
  let X : GlobalVectorField I M := fun _p : M => 0
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t := by
    simpa [gamma] using
      (mdifferentiableAt_const
        (I := 𝓘(Real, Real)) (I' := I) (c := x) (x := t))
  have hX : MDiffSectionAt (I := I) (F := E)
      (V := TangentSpace I) X (gamma t) := by
    simpa [MDiffSectionAt, X, gamma, zeroSection] using
      (Bundle.mdifferentiableAt_zeroSection
        (𝕜 := Real) (F := E) (E := TangentSpace I) (x := x))
  have hvel : RealizesVelocity (I := I) gamma X := by
    intro s
    simp [gamma, X, velocityAlong]
  have hpb :
      HasPullbackCovariantAccelerationAt (I := I) cov gamma t
        ((cov X (gamma t)) (curveVelocity I gamma t)) :=
    hasPullbackCovariantAccelerationAt_of_global_velocity
      (I := I) (cov := cov) (gamma := gamma) (X := X) (t := t)
      hgamma hX hvel
  have hcoord :
      HasCoordCovAccelAt (I := I) x0 cov gamma t
        ((cov X (gamma t)) (curveVelocity I gamma t)) :=
    hpb.toCoord (I := I) x0 (by simpa [gamma] using hx)
  simpa [gamma, X] using hcoord

/-- Time-one zero-velocity endpoint.

Mathematically this is realized by the constant coordinate geodesic.  The
proof now goes through the coordinate-defined acceleration layer, not through a
functional exponential map. -/
theorem expAt_zero
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    expAt (I := I) g x (0 : TangentSpace I x) x := by
  let gamma : Curve M := fun _ : Real => x
  refine expAt_of_segment (I := I) (g := g) (x := x)
    (v := (0 : TangentSpace I x)) (gamma := gamma)
    (s := Set.univ) (by intro t ht; simp) ?_
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · simp [gamma, zeroInitialVelocity]
  · constructor
    · intro t _ht
      simpa [gamma] using coordinateFrameAt_mem (I := I) x
    · intro t _ht
      simpa [gamma] using
        coordAccel_const (I := I)
          (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          x x t (coordinateFrameAt_mem (I := I) x)


end Coordinates
end RicciFlower
