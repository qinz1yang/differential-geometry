import RicciFlower.GlobalGeometry.Lecture07.SprayChartPush
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.ODE.Gronwall

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

/-! ## Fixed-chart time-one frontier -/

/-- The zero phase point `0_x ∈ TM` used to chart the time-one local flow. -/
private def phaseZero (x : M) : TangentBundle I M :=
  (⟨x, (0 : E)⟩ : TangentBundle I M)

/-- Initial phase coordinate in the tangent-bundle chart centered at `0_x`. -/
private def initPhase (x : M) (v : TangentSpace I x) : E × E :=
  extChartAt I.tangent (phaseZero (I := I) x)
    (⟨x, v⟩ : TangentBundle I M)

/-- Interpret model coordinates in the tangent-bundle chart centered at
`0_x`. -/
private def phaseOfModel (x : M) (z : E × E) : TangentBundle I M :=
  (extChartAt I.tangent (phaseZero (I := I) x)).symm z

@[simp] private theorem initPhase_zero (x : M) :
    initPhase (I := I) x (0 : TangentSpace I x) =
      extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x) := by
  rfl

/-- The initial-phase chart coordinate depends continuously on the initial
velocity at the zero vector. -/
private theorem initPhase_continuousAt_zero (x : M) :
    ContinuousAt
      (initPhase (I := I) x)
      (0 : TangentSpace I x) := by
  have hmk :
      ContinuousAt
        (fun v : TangentSpace I x =>
          (⟨x, v⟩ : TangentBundle I M))
        (0 : TangentSpace I x) := by
    simpa using
      (FiberBundle.continuous_totalSpaceMk E
        (TangentSpace I : M -> Type _) x).continuousAt
  have hchart :
      ContinuousAt
        (fun q : TangentBundle I M =>
          extChartAt I.tangent (phaseZero (I := I) x) q)
        (phaseZero (I := I) x) :=
    continuousAt_extChartAt (I := I.tangent)
      (phaseZero (I := I) x)
  have hzero :
      (⟨x, (0 : TangentSpace I x)⟩ : TangentBundle I M) =
        phaseZero (I := I) x := by
    rfl
  simpa [initPhase] using hchart.comp_of_eq hmk hzero

/-- Small initial velocities have model coordinates close to the zero phase
coordinate. -/
private theorem initPhase_small
    (x : M) {r : NNReal} (hr : 0 < r) :
    ∃ ρ > 0, ∀ v ∈ Metric.ball (0 : TangentSpace I x) ρ,
      initPhase (I := I) x v ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hrR : (0 : Real) < (r : Real) := by
    exact_mod_cast hr
  have hclosed : Metric.closedBall z0 (r : Real) ∈ 𝓝 z0 :=
    Metric.closedBall_mem_nhds z0 hrR
  have hpre :
      {v : TangentSpace I x |
        initPhase (I := I) x v ∈
          Metric.closedBall z0 (r : Real)} ∈
        𝓝 (0 : TangentSpace I x) := by
    simpa [z0] using
      (initPhase_continuousAt_zero (I := I) x).preimage_mem_nhds
        hclosed
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ρ, hρ, ?_⟩
  intro v hv
  simpa [z0] using hρsub hv

/-- Fixed-chart model vector field for the geodesic spray near `0_x`.

This is the object that should feed the uniform time-one Picard-Lindelof
argument: solve `z' = modelSpray g x z` on `[0, 1]`, then map the solution
back to `TM` with `phaseOfModel`. -/
private def modelSpray
    (g : SmoothRiemannianMetric I M) (x : M) (z : E × E) : E × E :=
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  tangentCoordChange I.tangent q (phaseZero (I := I) x) q
    (leviCivitaGeodesicSprayChart (I := I) g x q)

/-- Linearization of the fixed-chart model spray at the zero phase:
`(δx, δv) ↦ (δv, 0)`. -/
private def modelSprayLin : (E × E) →L[Real] (E × E) :=
  (ContinuousLinearMap.snd Real E E).prod
    (0 : (E × E) →L[Real] E)

@[simp] private theorem modelSprayLin_fst (z : E × E) :
    (modelSprayLin (E := E) z).1 = z.2 := by
  rfl

@[simp] private theorem modelSprayLin_snd (z : E × E) :
    (modelSprayLin (E := E) z).2 = 0 := by
  rfl

/-- Homogeneity of the quadratic Christoffel velocity term. -/
private theorem sprayQuad_smul
    (g : SmoothRiemannianMetric I M) (x : M)
    (y v : E) (a : Real) (k : CoordinateIdx (𝕜 := Real) E) :
    leviCivitaGeodesicSprayQuadratic (I := I) g x y (a • v) k =
      (a * a) *
        leviCivitaGeodesicSprayQuadratic (I := I) g x y v k := by
  classical
  simp [leviCivitaGeodesicSprayQuadratic, modelCoord, map_smul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Homogeneity of the model-space spray acceleration. -/
private theorem sprayAccel_smul
    (g : SmoothRiemannianMetric I M) (x : M)
    (y v : E) (a : Real) :
    leviCivitaGeodesicSprayAcceleration (I := I) g x y (a • v) =
      (a * a) •
        leviCivitaGeodesicSprayAcceleration (I := I) g x y v := by
  classical
  apply (Module.finBasis Real E).ext_elem
  intro k
  change modelCoord k
      (leviCivitaGeodesicSprayAcceleration (I := I) g x y (a • v)) =
    modelCoord k
      ((a * a) • leviCivitaGeodesicSprayAcceleration (I := I) g x y v)
  rw [modelCoord_leviCivitaGeodesicSprayAcceleration]
  have hrhs :
      modelCoord k
          ((a * a) •
            leviCivitaGeodesicSprayAcceleration (I := I) g x y v) =
        (a * a) * modelCoord k
          (leviCivitaGeodesicSprayAcceleration (I := I) g x y v) := by
    simp [modelCoord, map_smul]
  rw [hrhs, modelCoord_leviCivitaGeodesicSprayAcceleration,
    sprayQuad_smul]
  ring

/-- The tangent-bundle chart inverse centered at `0_x` is smooth at the chart
coordinate of `0_x`. -/
private theorem phaseOfModel_cdAt
    [I.Boundaryless] (x : M) :
    ContMDiffAt 𝓘(Real, E × E) I.tangent 1
      (phaseOfModel (I := I) x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  have hwithin :
      ContMDiffWithinAt 𝓘(Real, E × E) I.tangent 1
        (extChartAt I.tangent (phaseZero (I := I) x)).symm
        (Set.range I.tangent)
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :=
    contMDiffWithinAt_extChartAt_symm_range_self
      (I := I.tangent) (x := phaseZero (I := I) x) (n := (1 : WithTop ℕ∞))
  have hrange :
      Set.range I.tangent ∈
        𝓝 (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I.tangent)]
    exact Filter.univ_mem
  simpa [phaseOfModel] using hwithin.contMDiffAt hrange

/-- In the fixed tangent-bundle chart, the model vector field is locally the
chart-fiber RHS used to define the spray. -/
private theorem modelSpray_eq_fiber
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hsrc : (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source) :
    modelSpray (I := I) g x z =
      leviCivitaGeodesicSprayChartFiber (I := I) g x
        (phaseOfModel (I := I) x z) := by
  classical
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  let lift : Real -> TangentBundle I M :=
    fun t : Real => if t = 0 then phaseZero (I := I) x else q
  have hlift0 :
      lift 0 = (⟨x, (0 : E)⟩ : TangentBundle I M) := by
    simp [lift, phaseZero]
  have hsrc1 : (lift 1).proj ∈ (extChartAt I x).source := by
    simpa [lift, q] using hsrc
  have h :=
    chartVF_eq_fiber (I := I) (g := g) (x := x)
      (v0 := (0 : TangentSpace I x)) (lift := lift)
      (t0 := 0) (t := 1) hlift0 hsrc1
  have hone : (1 : Real) ≠ 0 := one_ne_zero
  have hlift1 : lift 1 = q := by
    simp [lift, hone]
  change
    tangentCoordChange I.tangent (lift 1) (lift 0) (lift 1)
        (leviCivitaGeodesicSprayChart (I := I) g x (lift 1)) =
      leviCivitaGeodesicSprayChartFiber (I := I) g x (lift 1) at h
  rw [hlift1, hlift0] at h
  simpa [modelSpray, q, phaseZero] using h

/-- The first component of the tangent-bundle chart centered over `x` is the
base `extChartAt x` coordinate. -/
private theorem chartPushLift_fst_eq_extChartAt_proj
    {x : M} {v0 : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift0 : lift t0 = (⟨x, v0⟩ : TangentBundle I M))
    {t : Real} (_hsrc : (lift t).proj ∈ (extChartAt I x).source) :
    (chartPushLift (I := I) lift t0 t).1 =
      extChartAt I x (lift t).proj := by
  rcases hq : lift t with ⟨y, w⟩
  simp [chartPushLift, hlift0, hq, TangentBundle.chartAt, extChartAt]

/-- In the fixed tangent-bundle chart target, the first model coordinate is
the base `extChartAt x` coordinate of the reconstructed tangent vector. -/
private theorem phaseOfModel_chart
    (x : M) {z : E × E}
    (hztarget : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source) :
    extChartAt I x (phaseOfModel (I := I) x z).proj = z.1 := by
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  let lift : Real -> TangentBundle I M :=
    fun t : Real => if t = 0 then phaseZero (I := I) x else q
  have hlift0 :
      lift 0 = (⟨x, (0 : E)⟩ : TangentBundle I M) := by
    simp [lift, phaseZero]
  have hqz :
      extChartAt I.tangent (phaseZero (I := I) x) q = z := by
    exact PartialEquiv.right_inv _ hztarget
  have hone : (1 : Real) ≠ 0 := one_ne_zero
  have hlift1 : lift 1 = q := by
    simp [lift, hone]
  have hchart :
      chartPushLift (I := I) lift 0 1 = z := by
    simpa [chartPushLift, hlift0, hlift1, q, phaseZero] using hqz
  have hsrc1 : (lift 1).proj ∈ (extChartAt I x).source := by
    simpa [hlift1, q] using hsrc
  have hfst :=
    chartPushLift_fst_eq_extChartAt_proj
      (I := I) (lift := lift) (t0 := 0) (t := 1)
      hlift0 hsrc1
  have hz := congrArg Prod.fst hchart
  rw [hfst] at hz
  simpa [hlift1, q] using hz

/-- On the fixed tangent-bundle chart target, the model spray is the explicit
first-order system `(x', v') = (v, -Γ(v,v))`. -/
private theorem modelSpray_eq_pair
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hztarget : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source) :
    modelSpray (I := I) g x z =
      (z.2, leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2) := by
  classical
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  let lift : Real -> TangentBundle I M :=
    fun t : Real => if t = 0 then phaseZero (I := I) x else q
  have hlift0 :
      lift 0 = (⟨x, (0 : E)⟩ : TangentBundle I M) := by
    simp [lift, phaseZero]
  have hqz :
      extChartAt I.tangent (phaseZero (I := I) x) q = z := by
    exact PartialEquiv.right_inv _ hztarget
  have hone : (1 : Real) ≠ 0 := one_ne_zero
  have hlift1 : lift 1 = q := by
    simp [lift, hone]
  have hsrc1 : (lift 1).proj ∈ (extChartAt I x).source := by
    simpa [hlift1, q] using hsrc
  have hchart :
      chartPushLift (I := I) lift 0 1 = z := by
    simpa [chartPushLift, hlift0, hlift1, q, phaseZero] using hqz
  have hfst :
      z.1 = extChartAt I x q.proj := by
    exact (phaseOfModel_chart (I := I) x hztarget hsrc).symm
  have hsnd :
      z.2 = chartFiberCoordAt (I := I) x q := by
    have h :=
      chartPushLift_snd_eq_chartFiberCoordAt
        (I := I) (lift := lift) (t0 := 0) (t := 1)
        hlift0 hsrc1
    have hz := congrArg Prod.snd hchart
    rw [h] at hz
    simpa [hlift1, q] using hz.symm
  rw [modelSpray_eq_fiber (I := I) g x hsrc]
  simp [leviCivitaGeodesicSprayChartFiber, q, hfst, hsnd]

/-- The tangent-bundle chart target centered at `0_x` is fiberwise full, so
scaling the second model coordinate preserves target membership. -/
private theorem phaseTarget_smul
    [I.Boundaryless] (x : M) {z : E × E} {a : Real}
    (hz : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target) :
    (z.1, a • z.2) ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target := by
  rw [FiberBundle.extChartAt_target] at hz ⊢
  exact ⟨hz.1, trivial⟩

/-- Scaling the fiber model coordinate keeps the reconstructed point over the
same fixed base chart source. -/
private theorem phaseSrc_smul
    [I.Boundaryless] (x : M) {z : E × E} {a : Real}
    (hz : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target) :
    (phaseOfModel (I := I) x (z.1, a • z.2)).proj ∈
      (extChartAt I x).source := by
  have hz' := phaseTarget_smul (I := I) x (z := z) (a := a) hz
  have hqsrc :
      phaseOfModel (I := I) x (z.1, a • z.2) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).source := by
    exact (extChartAt I.tangent (phaseZero (I := I) x)).map_target hz'
  simpa [phaseOfModel, phaseZero, extChartAt_source,
    TangentBundle.mem_chart_source_iff] using hqsrc.1

/-- Rescale a model-space spray solution so that a short-time solution becomes
a time-one candidate. -/
private def modelRescale (α : Real -> E × E) (τ : Real) : Real -> E × E :=
  fun s => ((α (τ * s)).1, τ • (α (τ * s)).2)

@[simp] private theorem modelRescale_zero
    (α : Real -> E × E) (τ : Real) :
    modelRescale α τ 0 = ((α 0).1, τ • (α 0).2) := by
  simp [modelRescale]

private theorem deriv_fst
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).1) F'.1 t := by
  have hfst : HasFDerivAt (ContinuousLinearMap.fst Real E E)
      (ContinuousLinearMap.fst Real E E) (F t) :=
    (ContinuousLinearMap.fst Real E E).hasFDerivAt
  simpa [Function.comp_def] using hfst.comp_hasDerivAt t hF

private theorem deriv_snd
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).2) F'.2 t := by
  have hsnd : HasFDerivAt (ContinuousLinearMap.snd Real E E)
      (ContinuousLinearMap.snd Real E E) (F t) :=
    (ContinuousLinearMap.snd Real E E).hasFDerivAt
  simpa [Function.comp_def] using hsnd.comp_hasDerivAt t hF

/-- Homogeneous reparametrization for the fixed-chart model spray. -/
private theorem modelRescale_deriv
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε τ s : Real} {α : Real -> E × E}
    (hαderiv : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt α (modelSpray (I := I) g x (α t)) t)
    (hsrc : ∀ t ∈ Set.Icc (-ε) ε,
      α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (α t)).proj ∈
          (extChartAt I x).source)
    (ht : τ * s ∈ Set.Ioo (-ε) ε) :
    HasDerivAt (modelRescale α τ)
      (modelSpray (I := I) g x (modelRescale α τ s)) s := by
  let t : Real := τ * s
  have htIcc : t ∈ Set.Icc (-ε) ε := Set.Ioo_subset_Icc_self ht
  have hscale : HasDerivAt (fun r : Real => τ * r) τ s := by
    simpa using (hasDerivAt_const_mul τ (x := s))
  have hcomp :
      HasDerivAt (fun r : Real => α (τ * r))
        (τ • modelSpray (I := I) g x (α t)) s := by
    simpa [t, Function.comp_def] using
      (hαderiv t ht).hasFDerivAt.comp_hasDerivAt s hscale
  have hfst :
      HasDerivAt (fun r : Real => (α (τ * r)).1)
        (τ • (modelSpray (I := I) g x (α t)).1) s := by
    simpa using deriv_fst hcomp
  have hsnd0 :
      HasDerivAt (fun r : Real => (α (τ * r)).2)
        (τ • (modelSpray (I := I) g x (α t)).2) s := by
    simpa using deriv_snd hcomp
  have hsnd :
      HasDerivAt (fun r : Real => τ • (α (τ * r)).2)
        (τ • (τ • (modelSpray (I := I) g x (α t)).2)) s := by
    simpa using hsnd0.const_smul τ
  have hprod :
      HasDerivAt (modelRescale α τ)
        (τ • (modelSpray (I := I) g x (α t)).1,
          τ • (τ • (modelSpray (I := I) g x (α t)).2)) s := by
    simpa [modelRescale, t] using hfst.prodMk hsnd
  have hαtarget :
      α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target :=
    (hsrc t htIcc).1
  have hαsrc :
      (phaseOfModel (I := I) x (α t)).proj ∈ (extChartAt I x).source :=
    (hsrc t htIcc).2
  have hβtarget :
      modelRescale α τ s ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target := by
    simpa [modelRescale, t] using
      phaseTarget_smul (I := I) x (z := α t) (a := τ) hαtarget
  have hβsrc :
      (phaseOfModel (I := I) x (modelRescale α τ s)).proj ∈
        (extChartAt I x).source := by
    simpa [modelRescale, t] using
      phaseSrc_smul (I := I) x (z := α t) (a := τ) hαtarget
  have hαpair :=
    modelSpray_eq_pair (I := I) g x hαtarget hαsrc
  have hβpair :=
    modelSpray_eq_pair (I := I) g x hβtarget hβsrc
  rw [hβpair]
  simpa [modelRescale, t, hαpair, sprayAccel_smul,
    smul_smul, mul_assoc, mul_comm, mul_left_comm] using hprod

/-- A fixed-chart model solution maps back to an integral curve of the
chart-fixed spray. -/
private theorem modelSol_integralOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} {β : Real -> E × E}
    (hβderiv : ∀ t ∈ Metric.ball (0 : Real) ε,
      HasDerivAt β (modelSpray (I := I) g x (β t)) t)
    (hβsrc : ∀ t ∈ Metric.ball (0 : Real) ε,
      β t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (β t)).proj ∈
          (extChartAt I x).source) :
    IsMIntegralCurveOn
      (fun t : Real => phaseOfModel (I := I) x (β t))
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) ε) := by
  intro t ht
  let q0 : TangentBundle I M := phaseZero (I := I) x
  let q : TangentBundle I M := phaseOfModel (I := I) x (β t)
  have hβt_target :
      β t ∈ (extChartAt I.tangent q0).target := by
    simpa [q0] using (hβsrc t ht).1
  have hq_src0 : q ∈ (extChartAt I.tangent q0).source := by
    simpa [q, q0, phaseOfModel] using
      (extChartAt I.tangent q0).map_target hβt_target
  have hq_src_self : q ∈ (extChartAt I.tangent q).source :=
    mem_extChartAt_source (I := I.tangent) q
  have hβderiv_t : HasDerivAt β
      (tangentCoordChange I.tangent q q0 q
        (leviCivitaGeodesicSprayChart (I := I) g x q)) t := by
    simpa [modelSpray, q, q0] using hβderiv t ht
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨?_, HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  · exact (continuousAt_extChartAt_symm'' hβt_target).comp hβderiv_t.continuousAt
  · simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt
      ((extChartAt I.tangent q ∘ (extChartAt I.tangent q0).symm) ∘ β)
      (leviCivitaGeodesicSprayChart (I := I) g x q) t
    rw [← tangentCoordChange_self (I := I.tangent) (x := q) (z := q)
        (v := leviCivitaGeodesicSprayChart (I := I) g x q) hq_src_self,
      ← tangentCoordChange_comp (I := I.tangent) (x := q0)
        ⟨⟨hq_src_self, hq_src0⟩, hq_src_self⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ hβderiv_t
    apply HasFDerivWithinAt.hasFDerivAt (s := Set.range I.tangent) _ <|
      mem_nhds_iff.mpr ⟨(extChartAt I.tangent q0).target,
        extChartAt_target_subset_range q0,
        isOpen_extChartAt_target (I := I.tangent) q0, hβt_target⟩
    rw [← (extChartAt I.tangent q0).right_inv hβt_target]
    exact hasFDerivWithinAt_tangentCoordChange
      (I := I.tangent) ⟨hq_src0, hq_src_self⟩

/-- Same-base initial tangent vectors have the expected model coordinates in
the tangent-bundle chart centered at `0_x`. -/
private theorem initPhase_eq_pair (x : M) (v : TangentSpace I x) :
    initPhase (I := I) x v = (extChartAt I x x, v) := by
  let q : TangentBundle I M := ⟨x, v⟩
  let lift : Real -> TangentBundle I M :=
    fun t : Real => if t = 0 then phaseZero (I := I) x else q
  have hlift0 :
      lift 0 = (⟨x, (0 : E)⟩ : TangentBundle I M) := by
    simp [lift, phaseZero]
  have hone : (1 : Real) ≠ 0 := one_ne_zero
  have hlift1 : lift 1 = q := by
    simp [lift, hone]
  have hsrc1 : (lift 1).proj ∈ (extChartAt I x).source := by
    simp [hlift1, q]
  have hchart :
      chartPushLift (I := I) lift 0 1 = initPhase (I := I) x v := by
    simp [chartPushLift, initPhase, hlift0, hlift1, q, phaseZero]
  apply Prod.ext
  · have hfst :=
      chartPushLift_fst_eq_extChartAt_proj
        (I := I) (lift := lift) (t0 := 0) (t := 1)
        hlift0 hsrc1
    have hz := congrArg Prod.fst hchart
    rw [hfst] at hz
    simpa [hlift1, q] using hz
  · have hsnd :=
      chartPushLift_snd_eq_chartFiberCoordAt
        (I := I) (lift := lift) (t0 := 0) (t := 1)
        hlift0 hsrc1
    have hz := congrArg Prod.snd hchart
    rw [hsnd] at hz
    have hfiber : chartFiberCoordAt (I := I) x q = v := by
      simpa [q] using chartFiberCoordAt_self (I := I) (u := q)
    rw [hlift1, hfiber] at hz
    exact hz.symm

/-- Scaling the fiber coordinate of an initial phase is the initial phase of
the scaled tangent vector. -/
private theorem initPhase_smul
    (x : M) (a : Real) (v : TangentSpace I x) :
    ((initPhase (I := I) x v).1, a • (initPhase (I := I) x v).2) =
      initPhase (I := I) x (a • v) := by
  rw [initPhase_eq_pair, initPhase_eq_pair]
  rfl

private theorem initPhase_sub
    (x : M) (v w : TangentSpace I x) :
    initPhase (I := I) x v - initPhase (I := I) x w =
      (0, v - w) := by
  rw [initPhase_eq_pair, initPhase_eq_pair]
  ext <;> simp
  rfl

private theorem norm_initPhase_sub
    (x : M) (v w : TangentSpace I x) :
    ‖initPhase (I := I) x v - initPhase (I := I) x w‖ =
      ‖v - w‖ := by
  rw [initPhase_sub]
  change max ‖(0 : E)‖ ‖v - w‖ = ‖v - w‖
  simp [norm_nonneg]

private theorem phaseZero_pair (x : M) :
    extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x) =
      (extChartAt I x x, (0 : E)) := by
  calc
    extChartAt I.tangent (phaseZero (I := I) x) (phaseZero (I := I) x)
        = initPhase (I := I) x (0 : TangentSpace I x) :=
      (initPhase_zero (I := I) x).symm
    _ = (extChartAt I x x, (0 : E)) := by
      exact initPhase_eq_pair (I := I) x (0 : TangentSpace I x)

private theorem norm_initPhase_zero
    (x : M) (v : TangentSpace I x) :
    ‖initPhase (I := I) x v -
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)‖ = ‖v‖ := by
  rw [← initPhase_zero (I := I) x]
  simpa using norm_initPhase_sub (I := I) x v (0 : TangentSpace I x)

private theorem half_mul_mem_Ioo
    {ε s : Real} (hε : 0 < ε)
    (hs : s ∈ Metric.ball (0 : Real) 2) :
    (ε / 2) * s ∈ Set.Ioo (-ε) ε := by
  have hτ : 0 < ε / 2 := half_pos hε
  have hsabs : |s| < 2 := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hs
  rcases abs_lt.mp hsabs with ⟨hslo, hshi⟩
  have hlo : (ε / 2) * (-2) < (ε / 2) * s :=
    mul_lt_mul_of_pos_left hslo hτ
  have hhi : (ε / 2) * s < (ε / 2) * 2 :=
    mul_lt_mul_of_pos_left hshi hτ
  constructor <;> nlinarith

private theorem uIcc01_mem_ball_two {t : Real}
    (ht : t ∈ Set.uIcc 0 1) :
    t ∈ Metric.ball (0 : Real) 2 := by
  rw [Metric.mem_ball]
  have hdist : dist (0 : Real) t ≤ dist (0 : Real) 1 :=
    Real.dist_left_le_of_mem_uIcc ht
  norm_num at hdist ⊢
  linarith

/-- The chart-fiber RHS, pulled back to the fixed model chart, is smooth at
`0_x`. -/
private theorem sprayFiber_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (fun z : E × E =>
        leviCivitaGeodesicSprayChartFiber (I := I) g x
          (phaseOfModel (I := I) x z))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  have hfiber :
      ContMDiffAt I.tangent 𝓘(Real, E × E) 1
        (leviCivitaGeodesicSprayChartFiber (I := I) g x)
        (phaseZero (I := I) x) := by
    have htop :=
      leviCivitaGeodesicSprayChartFiber_contMDiffAt_self
        (I := I) g x (0 : TangentSpace I x)
    simpa [phaseZero] using
      htop.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hphase := phaseOfModel_cdAt (I := I) x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hfiber' :
      ContMDiffAt I.tangent 𝓘(Real, E × E) 1
        (leviCivitaGeodesicSprayChartFiber (I := I) g x)
        (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hfiber
  have hcomp :
      ContMDiffAt 𝓘(Real, E × E) 𝓘(Real, E × E) 1
        ((leviCivitaGeodesicSprayChartFiber (I := I) g x) ∘
          phaseOfModel (I := I) x)
        z0 :=
    hfiber'.comp
      (x := z0)
      hphase
  simpa [Function.comp_def, z0] using hcomp.contDiffAt

/-- The fixed-chart model spray is `C^1` at the zero phase point. -/
private theorem modelSpray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1 (modelSpray (I := I) g x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hfiber := sprayFiber_cdAt (I := I) g x
  have hsrc_nhds :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseZero (I := I) x) := by
    have hproj :
        ContinuousAt
          (fun q : TangentBundle I M => q.proj)
          (phaseZero (I := I) x) :=
      (FiberBundle.continuous_proj E
        (TangentSpace I : M -> Type _)).continuousAt
    have hxsrc :
        (phaseZero (I := I) x).proj ∈ (extChartAt I x).source := by
      simp [phaseZero]
    exact hproj.preimage_mem_nhds
      (by
        simpa [extChartAt_source] using
          extChartAt_source_mem_nhds (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc_nhds' :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hsrc_nhds
  have hsrc_event :
      ∀ᶠ z in 𝓝 z0,
        (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source := by
    have hphase_cont := (phaseOfModel_cdAt (I := I) x).continuousAt
    simpa [z0] using hphase_cont.preimage_mem_nhds hsrc_nhds'
  refine hfiber.congr_of_eventuallyEq ?_
  filter_upwards [hsrc_event] with z hz
  exact modelSpray_eq_fiber (I := I) g x hz

/-- The fixed-chart model spray is strictly differentiable at the zero phase.

This is the direct consequence of `C¹` regularity, keeping Mathlib's `fderiv`
as the derivative.  `spray_strict_zero` below identifies this derivative with
the explicit linearization `modelSprayLin`. -/
private theorem modelSpray_strictAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    HasStrictFDerivAt
      (modelSpray (I := I) g x)
      (fderiv Real (modelSpray (I := I) g x)
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) :=
  (modelSpray_cdAt (I := I) g x).hasStrictFDerivAt one_ne_zero

/-- The Christoffel quadratic term has zero first derivative at the zero
fiber. -/
private theorem quad_fderiv_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (k : CoordinateIdx (𝕜 := Real) E) :
    HasFDerivAt
      (fun z : E × E =>
        leviCivitaGeodesicSprayQuadratic (I := I) g x z.1 z.2 k)
      (0 : (E × E) →L[Real] Real)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  classical
  let y0 : E := extChartAt I x x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hz0 : z0 = (y0, (0 : E)) := by
    simpa [z0, y0] using phaseZero_pair (I := I) x
  change HasFDerivAt
    (fun z : E × E =>
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          LeviCivita.leviCivitaChristoffelModelRHS
              (I := I) g x i j k z.1 *
            modelCoord i z.2 * modelCoord j z.2)
    (0 : (E × E) →L[Real] Real) z0
  convert (HasFDerivAt.fun_sum (𝕜 := Real) (E := E × E) (F := Real)
    (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
    (A := fun i (z : E × E) =>
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        LeviCivita.leviCivitaChristoffelModelRHS
            (I := I) g x i j k z.1 *
          modelCoord i z.2 * modelCoord j z.2)
    (A' := fun _ => (0 : (E × E) →L[Real] Real))
    (x := z0) fun i _hi => by
      convert (HasFDerivAt.fun_sum (𝕜 := Real) (E := E × E) (F := Real)
        (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
        (A := fun j (z : E × E) =>
          LeviCivita.leviCivitaChristoffelModelRHS
              (I := I) g x i j k z.1 *
            modelCoord i z.2 * modelCoord j z.2)
        (A' := fun _ => (0 : (E × E) →L[Real] Real))
        (x := z0) fun j _hj => by
          let Γ : E → Real :=
            LeviCivita.leviCivitaChristoffelModelRHS
              (I := I) g x i j k
          have hΓWithin :=
            LeviCivita.leviCivitaChristoffelModelRHS_contDiffWithinAt
              (I := I) g x i j k
          have hRange : Set.range I ∈ 𝓝 y0 := by
            exact Filter.mem_of_superset (extChartAt_target_mem_nhds (I := I) x)
              (extChartAt_target_subset_range (I := I) x)
          have hΓAt : ContDiffAt Real ∞ Γ y0 := by
            simpa [Γ, y0] using hΓWithin.contDiffAt hRange
          have hΓ :
              HasFDerivAt
                (fun z : E × E => Γ z.1)
                ((fderiv Real Γ y0).comp (ContinuousLinearMap.fst Real E E))
                z0 := by
            exact (hΓAt.differentiableAt (by simp)).hasFDerivAt.comp z0
              (hasFDerivAt_fst (𝕜 := Real) (E := E) (F := E) (p := z0))
          have hi :
              HasFDerivAt
                (fun z : E × E => modelCoord i z.2)
                (((Module.finBasis Real E).coord i).toContinuousLinearMap.comp
                  (ContinuousLinearMap.snd Real E E))
                z0 := by
            simpa [modelCoord] using
              (((Module.finBasis Real E).coord i).toContinuousLinearMap.hasFDerivAt.comp z0
                (hasFDerivAt_snd (𝕜 := Real) (E := E) (F := E) (p := z0)))
          have hj :
              HasFDerivAt
                (fun z : E × E => modelCoord j z.2)
                (((Module.finBasis Real E).coord j).toContinuousLinearMap.comp
                  (ContinuousLinearMap.snd Real E E))
                z0 := by
            simpa [modelCoord] using
              (((Module.finBasis Real E).coord j).toContinuousLinearMap.hasFDerivAt.comp z0
                (hasFDerivAt_snd (𝕜 := Real) (E := E) (F := E) (p := z0)))
          have hprod := (hΓ.mul hi).mul hj
          simpa [Γ, z0, hz0, y0, modelCoord, ContinuousLinearMap.zero_apply] using hprod) using 1
      · simp
      ) using 1
  · simp

/-- The model acceleration `-Γ(v,v)` has zero first derivative at the zero
fiber. -/
private theorem accel_fderiv_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    HasFDerivAt
      (fun z : E × E =>
        leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2)
      (0 : (E × E) →L[Real] E)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  classical
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  change HasFDerivAt
    (fun z : E × E =>
      ∑ k : CoordinateIdx (𝕜 := Real) E,
        (-leviCivitaGeodesicSprayQuadratic (I := I) g x z.1 z.2 k) •
          (Module.finBasis Real E k))
    (0 : (E × E) →L[Real] E) z0
  convert (HasFDerivAt.fun_sum (𝕜 := Real) (E := E × E) (F := E)
    (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
    (A := fun k (z : E × E) =>
      (-leviCivitaGeodesicSprayQuadratic (I := I) g x z.1 z.2 k) •
        (Module.finBasis Real E k))
    (A' := fun _ => (0 : (E × E) →L[Real] E))
    (x := z0) fun k _hk => by
      have hq := (quad_fderiv_zero (I := I) g x k).neg
      simpa [z0, ContinuousLinearMap.zero_smulRight] using
        hq.smul_const (Module.finBasis Real E k)) using 1
  · simp

/-- The explicit model pair `(v, -Γ(v,v))` linearizes to `(δx, δv) ↦
 (δv, 0)`. -/
private theorem sprayPair_fderiv
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    HasFDerivAt
      (fun z : E × E =>
        (z.2, leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2))
      (modelSprayLin (E := E))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  have hfst :
      HasFDerivAt (fun z : E × E => z.2)
        (ContinuousLinearMap.snd Real E E)
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :=
    hasFDerivAt_snd (𝕜 := Real) (E := E) (F := E)
      (p := extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
  have hsnd := accel_fderiv_zero (I := I) g x
  simpa [modelSprayLin] using hfst.prodMk hsnd

/-- The fixed-chart model spray has derivative `modelSprayLin` at the zero
phase. -/
private theorem spray_fderiv_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    HasFDerivAt
      (modelSpray (I := I) g x)
      (modelSprayLin (E := E))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have htarget :
      (extChartAt I.tangent (phaseZero (I := I) x)).target ∈ 𝓝 z0 := by
    have hzsrc :
        phaseZero (I := I) x ∈
          (extChartAt I.tangent (phaseZero (I := I) x)).source :=
      mem_extChartAt_source (I := I.tangent) (phaseZero (I := I) x)
    simpa [z0] using
      (isOpen_extChartAt_target (I := I.tangent)
        (phaseZero (I := I) x)).mem_nhds
        ((extChartAt I.tangent (phaseZero (I := I) x)).map_source hzsrc)
  have hsrc_nhds :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseZero (I := I) x) := by
    have hproj :
        ContinuousAt
          (fun q : TangentBundle I M => q.proj)
          (phaseZero (I := I) x) :=
      (FiberBundle.continuous_proj E
        (TangentSpace I : M -> Type _)).continuousAt
    have hxsrc :
        (phaseZero (I := I) x).proj ∈ (extChartAt I x).source := by
      simp [phaseZero]
    exact hproj.preimage_mem_nhds
      (by
        simpa [extChartAt_source] using
          extChartAt_source_mem_nhds (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc_event :
      ∀ᶠ z in 𝓝 z0,
        (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source := by
    have hphase_cont := (phaseOfModel_cdAt (I := I) x).continuousAt
    have hsrc_nhds' :
        {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
          𝓝 (phaseOfModel (I := I) x z0) := by
      simpa [hphase_self] using hsrc_nhds
    simpa [z0] using hphase_cont.preimage_mem_nhds hsrc_nhds'
  have hev :
      modelSpray (I := I) g x =ᶠ[𝓝 z0]
        fun z : E × E =>
          (z.2, leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2) := by
    filter_upwards [htarget, hsrc_event] with z hztarget hzsrc
    exact modelSpray_eq_pair (I := I) g x hztarget hzsrc
  exact (hev.hasFDerivAt_iff).2 (sprayPair_fderiv (I := I) g x)

/-- Strict differentiability of the fixed-chart model spray with the explicit
linearization `(δx, δv) ↦ (δv, 0)`. -/
private theorem spray_strict_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    HasStrictFDerivAt
      (modelSpray (I := I) g x)
      (modelSprayLin (E := E))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) :=
  (modelSpray_strictAt (I := I) g x).congr_fderiv
    (spray_fderiv_zero (I := I) g x).fderiv

/-- Pairwise little-o form of the strict linearization of the fixed-chart
model spray at the zero phase. -/
private theorem spray_o
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    (fun p : (E × E) × (E × E) =>
      modelSpray (I := I) g x p.1 -
        modelSpray (I := I) g x p.2 -
        modelSprayLin (E := E) (p.1 - p.2))
      =o[𝓝 ((extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x),
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)))]
        fun p : (E × E) × (E × E) => p.1 - p.2 :=
  (spray_strict_zero (I := I) g x).isLittleO

/-- A uniformly small integrand has a small interval integral.

This is an analytic bookkeeping lemma for the strict endpoint proof: once a
residual term is `o(g p)` uniformly in time, integration over a fixed bounded
interval preserves the little-o estimate. -/
private lemma isLittleO_intervalIntegral_of_uniform_bound
    {P V W : Type*}
    [NormedAddCommGroup V] [NormedSpace Real V] [SeminormedAddCommGroup W]
    {l : Filter P} {a b : Real}
    {r : P -> Real -> V} {g : P -> W}
    (hr : ∀ c > 0, ∀ᶠ p in l,
      ∀ t ∈ Set.uIoc a b, ‖r p t‖ ≤ c * ‖g p‖) :
    (fun p => ∫ t in a..b, r p t) =o[l] g := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  let c' : Real := c / (|b - a| + 1)
  have hc' : 0 < c' := by
    dsimp [c']
    positivity
  filter_upwards [hr c' hc'] with p hp
  have hbound : ∀ t ∈ Set.uIoc a b, ‖r p t‖ ≤ c' * ‖g p‖ := hp
  calc
    ‖∫ t in a..b, r p t‖
        ≤ (c' * ‖g p‖) * |b - a| := by
          exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ c * ‖g p‖ := by
      have hnorm : 0 ≤ ‖g p‖ := norm_nonneg _
      have habs : 0 ≤ |b - a| := abs_nonneg _
      have hden : 0 < |b - a| + 1 := by positivity
      have hcle : c' * |b - a| ≤ c := by
        dsimp [c']
        field_simp [hden.ne']
        have hA : |b - a| ≤ |b - a| + 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hA hc.le]
      rw [show (c' * ‖g p‖) * |b - a| =
          (c' * |b - a|) * ‖g p‖ by ring]
      exact mul_le_mul_of_nonneg_right hcle hnorm

/-- Uniform smallness on `[0,b]` survives integration over every subinterval
`0..t`, uniformly in `t`.

This is the estimate needed for the velocity error before integrating once
more to control the endpoint error. -/
private lemma eventually_norm_integral_zero_to_t_le
    {P V W : Type*}
    [NormedAddCommGroup V] [NormedSpace Real V] [SeminormedAddCommGroup W]
    {l : Filter P} {b : Real} (hb : 0 ≤ b)
    {r : P -> Real -> V} {g : P -> W}
    (hr : ∀ c > 0, ∀ᶠ p in l,
      ∀ s ∈ Set.Icc (0 : Real) b, ‖r p s‖ ≤ c * ‖g p‖) :
    ∀ c > 0, ∀ᶠ p in l,
      ∀ t ∈ Set.Icc (0 : Real) b,
        ‖∫ s in (0 : Real)..t, r p s‖ ≤ c * ‖g p‖ := by
  intro c hc
  let c' : Real := c / (b + 1)
  have hc' : 0 < c' := by
    dsimp [c']
    positivity
  filter_upwards [hr c' hc'] with p hp t ht
  have hbound : ∀ s ∈ Set.uIoc (0 : Real) t,
      ‖r p s‖ ≤ c' * ‖g p‖ := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : Real) b := by
      rcases ht with ⟨h0t, htb⟩
      rw [Set.mem_uIoc] at hs
      rcases hs with hs | hs
      · exact ⟨hs.1.le, le_trans hs.2 htb⟩
      · have hlt : s < s := lt_of_le_of_lt (le_trans hs.2 h0t) hs.1
        exact (lt_irrefl s hlt).elim
    exact hp s hsIcc
  calc
    ‖∫ s in (0 : Real)..t, r p s‖
        ≤ (c' * ‖g p‖) * |t - 0| := by
          exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ c * ‖g p‖ := by
      have htb : |t - 0| ≤ b := by
        rcases ht with ⟨h0t, htb⟩
        rw [sub_zero, abs_of_nonneg h0t]
        exact htb
      have hnorm : 0 ≤ ‖g p‖ := norm_nonneg _
      have htabs : 0 ≤ |t - 0| := abs_nonneg _
      have hcle : c' * |t - 0| ≤ c := by
        dsimp [c']
        have hden : 0 < b + 1 := by positivity
        field_simp [hden.ne']
        have hb1 : |t - 0| ≤ b + 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hb1 hc.le]
      rw [show (c' * ‖g p‖) * |t - 0| =
          (c' * |t - 0|) * ‖g p‖ by ring]
      exact mul_le_mul_of_nonneg_right hcle hnorm

/-- Normed-space form of a Lipschitz-on estimate. -/
private lemma lip_norm_sub_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {K : NNReal} {s : Set X} {f : X -> Y}
    (h : LipschitzOnWith K f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f x - f y‖ ≤ (K : Real) * ‖x - y‖ := by
  simpa [dist_eq_norm] using h.dist_le_mul x hx y hy

/-- The model-spray nonlinear residual is uniformly little-o along the chosen
Picard trajectories, on any time interval where the flow is controlled.

This is the first real propagation step from the strict linearization of the
spray to the endpoint estimate. -/
private lemma sprayRem_uniform
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε τ ρ : Real} {rModel : NNReal} {L' : NNReal}
    {α : E × E -> Real -> E × E}
    (hρ : 0 < ρ)
    (hτ : 0 < τ)
    (hsub : Set.Icc (0 : Real) τ ⊆ Set.Icc (-ε) ε)
    (hsmall : ∀ v ∈ Metric.ball (0 : TangentSpace I x) ρ,
      initPhase (I := I) x v ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel)
    (hzero : ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x))
    (hLip : ∀ t ∈ Set.Icc (-ε) ε,
      LipschitzOnWith L' (fun z => α z t)
        (Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel)) :
    ∀ c > 0, ∀ᶠ p : TangentSpace I x × TangentSpace I x in
      𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x),
      ∀ t ∈ Set.Icc (0 : Real) τ,
        ‖modelSpray (I := I) g x
            (α (initPhase (I := I) x (τ⁻¹ • p.1)) t) -
          modelSpray (I := I) g x
            (α (initPhase (I := I) x (τ⁻¹ • p.2)) t) -
          modelSprayLin (E := E)
            (α (initPhase (I := I) x (τ⁻¹ • p.1)) t -
              α (initPhase (I := I) x (τ⁻¹ • p.2)) t)‖
          ≤ c * ‖p.1 - p.2‖ := by
  intro c hc
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  let rem : (E × E) × (E × E) -> E × E := fun q =>
    modelSpray (I := I) g x q.1 -
      modelSpray (I := I) g x q.2 -
      modelSprayLin (E := E) (q.1 - q.2)
  let Csep : Real := (L' : Real) * ‖τ⁻¹‖
  let η : Real := c / (Csep + 1)
  have hCsep_nonneg : 0 ≤ Csep := by
    dsimp [Csep]
    positivity
  have hdenη : 0 < Csep + 1 := by positivity
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hremEvt :
      {q : (E × E) × (E × E) |
        ‖rem q‖ ≤ η * ‖q.1 - q.2‖} ∈ 𝓝 (z0, z0) := by
    simpa [rem, z0, η] using
      (spray_o (I := I) g x).bound hη
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hremEvt
  let Clip : Real := (L' : Real) + 1
  have hClip : 0 < Clip := by
    dsimp [Clip]
    positivity
  let σ : Real := min ρ (δ / Clip)
  have hσ : 0 < σ := by
    dsimp [σ]
    exact lt_min hρ (div_pos hδ hClip)
  have hcont1 :
      ContinuousAt
        (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.1)
        ((0, 0) : TangentSpace I x × TangentSpace I x) := by
    fun_prop
  have hcont2 :
      ContinuousAt
        (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.2)
        ((0, 0) : TangentSpace I x × TangentSpace I x) := by
    fun_prop
  have hnear1 := hcont1.preimage_mem_nhds (Metric.ball_mem_nhds _ hσ)
  have hnear2 := hcont2.preimage_mem_nhds (Metric.ball_mem_nhds _ hσ)
  filter_upwards [hnear1, hnear2] with p hp1 hp2 t ht
  let z1 : E × E := initPhase (I := I) x (τ⁻¹ • p.1)
  let z2 : E × E := initPhase (I := I) x (τ⁻¹ • p.2)
  have htE : t ∈ Set.Icc (-ε) ε := hsub ht
  have hp1ball : τ⁻¹ • p.1 ∈ Metric.ball (0 : TangentSpace I x) σ := by
    simpa using hp1
  have hp2ball : τ⁻¹ • p.2 ∈ Metric.ball (0 : TangentSpace I x) σ := by
    simpa using hp2
  have hp1ρ : τ⁻¹ • p.1 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hp1ball ⊢
    exact lt_of_lt_of_le hp1ball (min_le_left _ _)
  have hp2ρ : τ⁻¹ • p.2 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hp2ball ⊢
    exact lt_of_lt_of_le hp2ball (min_le_left _ _)
  have hz1 : z1 ∈ Metric.closedBall z0 rModel := by
    simpa [z1, z0] using hsmall (τ⁻¹ • p.1) hp1ρ
  have hz2 : z2 ∈ Metric.closedBall z0 rModel := by
    simpa [z2, z0] using hsmall (τ⁻¹ • p.2) hp2ρ
  have hz0 : z0 ∈ Metric.closedBall z0 rModel :=
    Metric.mem_closedBall_self (NNReal.coe_nonneg rModel)
  have hp1δ : ‖τ⁻¹ • p.1‖ < δ / Clip := by
    rw [Metric.mem_ball, dist_zero_right] at hp1ball
    exact lt_of_lt_of_le hp1ball (min_le_right _ _)
  have hp2δ : ‖τ⁻¹ • p.2‖ < δ / Clip := by
    rw [Metric.mem_ball, dist_zero_right] at hp2ball
    exact lt_of_lt_of_le hp2ball (min_le_right _ _)
  have hLδ : (L' : Real) * (δ / Clip) < δ := by
    have hLlt : (L' : Real) < Clip := by
      dsimp [Clip]
      linarith [NNReal.coe_nonneg L']
    have hδdiv : 0 < δ / Clip := div_pos hδ hClip
    calc
      (L' : Real) * (δ / Clip) < Clip * (δ / Clip) :=
        mul_lt_mul_of_pos_right hLlt hδdiv
      _ = δ := by
        field_simp [hClip.ne']
  have hclose1 : ‖α z1 t - z0‖ < δ := by
    have hle := lip_norm_sub_le (hLip t htE) hz1 hz0
    have hz := hzero t htE
    dsimp [z1] at hle
    rw [hz] at hle
    have hinit : ‖z1 - z0‖ < δ / Clip := by
      simpa [z1, z0] using
        (norm_initPhase_zero (I := I) x (τ⁻¹ • p.1)).trans_lt hp1δ
    exact lt_of_le_of_lt hle
      (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hinit.le (NNReal.coe_nonneg L'))
        hLδ)
  have hclose2 : ‖α z2 t - z0‖ < δ := by
    have hle := lip_norm_sub_le (hLip t htE) hz2 hz0
    have hz := hzero t htE
    dsimp [z2] at hle
    rw [hz] at hle
    have hinit : ‖z2 - z0‖ < δ / Clip := by
      simpa [z2, z0] using
        (norm_initPhase_zero (I := I) x (τ⁻¹ • p.2)).trans_lt hp2δ
    exact lt_of_le_of_lt hle
      (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hinit.le (NNReal.coe_nonneg L'))
        hLδ)
  have hqball : (α z1 t, α z2 t) ∈ Metric.ball (z0, z0) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖(α z1 t - z0, α z2 t - z0)‖ < δ
    change max ‖α z1 t - z0‖ ‖α z2 t - z0‖ < δ
    exact max_lt hclose1 hclose2
  have hrem := hδsub hqball
  have hsep : ‖α z1 t - α z2 t‖ ≤ Csep * ‖p.1 - p.2‖ := by
    have hle := lip_norm_sub_le (hLip t htE) hz1 hz2
    have hinit : ‖z1 - z2‖ = ‖τ⁻¹ • (p.1 - p.2)‖ := by
      simp [z1, z2, norm_initPhase_sub, smul_sub]
    calc
      ‖α z1 t - α z2 t‖ ≤ (L' : Real) * ‖z1 - z2‖ := hle
      _ = (L' : Real) * ‖τ⁻¹ • (p.1 - p.2)‖ := by rw [hinit]
      _ = Csep * ‖p.1 - p.2‖ := by
        simp [Csep, norm_smul, mul_assoc, mul_comm, mul_left_comm]
  have hηC : η * Csep ≤ c := by
    dsimp [η]
    field_simp [hdenη.ne']
    nlinarith [mul_le_mul_of_nonneg_left
      (show Csep ≤ Csep + 1 by linarith) hc.le]
  calc
    ‖modelSpray (I := I) g x (α z1 t) -
          modelSpray (I := I) g x (α z2 t) -
          modelSprayLin (E := E) (α z1 t - α z2 t)‖
        = ‖rem (α z1 t, α z2 t)‖ := by rfl
    _ ≤ η * ‖α z1 t - α z2 t‖ := by
      simpa [rem] using hrem
    _ ≤ η * (Csep * ‖p.1 - p.2‖) :=
      mul_le_mul_of_nonneg_left hsep hη.le
    _ = (η * Csep) * ‖p.1 - p.2‖ := by ring
    _ ≤ c * ‖p.1 - p.2‖ :=
      mul_le_mul_of_nonneg_right hηC (norm_nonneg _)

/-- The zero phase point is an equilibrium of the fixed-chart model spray. -/
private theorem modelSpray_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    modelSpray (I := I) g x
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) = 0 := by
  have hq :
      phaseOfModel (I := I) x
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) =
        phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc :
      (phaseOfModel (I := I) x
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))).proj ∈
        (extChartAt I x).source := by
    rw [hq]
    simp [phaseZero]
  rw [modelSpray_eq_fiber (I := I) g x hsrc, hq]
  have hv :
      chartFiberCoordAt (I := I) x (phaseZero (I := I) x) = 0 := by
    simp [phaseZero]
    simpa [phaseZero] using
      chartFiberCoordAt_self (I := I)
        (u := (phaseZero (I := I) x))
  change
    (chartFiberCoordAt (I := I) x (phaseZero (I := I) x),
      leviCivitaGeodesicSprayAcceleration (I := I) g x
        (extChartAt I x (phaseZero (I := I) x).proj)
        (chartFiberCoordAt (I := I) x (phaseZero (I := I) x))) = (0, 0)
  rw [hv]
  simp [leviCivitaGeodesicSprayAcceleration,
    leviCivitaGeodesicSprayQuadratic, modelCoord]

/-- Local Picard-Lindelof data for the fixed-chart model spray near the zero
phase point.

This is uniform for initial phase points in a small closed model ball, but only
on a short time interval.  Extending this checked local flow to time `1` is the
remaining continuation argument for `exists_exp_one`. -/
private theorem modelSpray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => modelSpray (I := I) g x)
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x))
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (modelSpray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

/-- Picard-Lindelof local solutions stay in the controlling closed ball.

Mathlib's public existence theorem returns the derivative equation but hides
this bound.  The normal-coordinate endpoint proof needs the bound to keep the
model solution inside the fixed tangent-bundle chart source. -/
private theorem plSol_bounded
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 x : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    (hx : x ∈ Metric.closedBall x0 r) :
    ∃ α : Real -> F, α t0 = x ∧
      (∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt α (f t (α t)) (Set.Icc tmin tmax) t) ∧
      ∀ t : Real, α t ∈ Metric.closedBall x0 a := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le)
      x ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t
    exact α.compProj_mem_closedBall hf.mul_max_le

/-- Functional Picard-Lindelof flow with both Lipschitz dependence on the
initial condition and the closed-ball bound for the same chosen flow. -/
private theorem plFlow_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K) :
    ∃ α : F -> Real -> F,
      (∀ x ∈ Metric.closedBall x0 r, α x t0 = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (α x) (f t (α x t)) (Set.Icc tmin tmax) t) ∧
      (∀ x ∈ Metric.closedBall x0 r, ∀ t : Real,
        α x t ∈ Metric.closedBall x0 a) ∧
      (∀ x ∈ Metric.closedBall x0 r, ∀ t ∈ Set.Icc tmin tmax,
        α x t = ODE.picard f t0 x (α x) t) ∧
      ∃ L' : NNReal, ∀ t ∈ Set.Icc tmin tmax,
        LipschitzOnWith L' (fun x => α x t) (Metric.closedBall x0 r) := by
  classical
  have hfixed (x : F) (hx : x ∈ Metric.closedBall x0 r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose β hβ using hfixed
  let α : F -> Real -> F := fun x =>
    if hx : x ∈ Metric.closedBall x0 r then (β x hx).compProj else 0
  refine ⟨α, ?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · change (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t0 = x
      rw [dif_pos hx, ODE.FunSpace.compProj_val, ← hβ x hx,
        ODE.FunSpace.next_apply₀]
    · intro t ht
      change HasDerivWithinAt
        (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0)
        (f t ((if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t))
        (Set.Icc tmin tmax) t
      rw [dif_pos hx]
      apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
        (β x hx).continuous_compProj.continuousOn
        (fun _ _ => (β x hx).compProj_mem_closedBall hf.mul_max_le)
        x ht).congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hβ x hx]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro x hx t
    change (if hx' : x ∈ Metric.closedBall x0 r then
        (β x hx').compProj else 0) t ∈ Metric.closedBall x0 a
    rw [dif_pos hx]
    exact (β x hx).compProj_mem_closedBall hf.mul_max_le
  · intro x hx t ht
    change (if hx' : x ∈ Metric.closedBall x0 r then
        (β x hx').compProj else 0) t =
      ODE.picard f t0 x
        (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t
    rw [dif_pos hx, ODE.FunSpace.compProj_of_mem ht]
    have hfixed :=
      (ODE.FunSpace.isFixedPt_next_iff hf hx).mp (hβ x hx)
    simpa [dif_pos hx] using hfixed (⟨t, ht⟩ : Set.Icc tmin tmax)
  · obtain ⟨L', hL'⟩ :=
      ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    have : Nonempty (Set.Icc tmin tmax) := ⟨t0⟩
    have hdist :=
      hL' x y hx hy (β x hx) (β y hy) (hβ x hx) (hβ y hy)
    have hpoint :=
      (ContinuousMap.dist_le_iff_of_nonempty.mp hdist)
        (⟨t, ht⟩ : Set.Icc tmin tmax)
    change dist
        ((if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t)
        ((if hy' : y ∈ Metric.closedBall x0 r then
          (β y hy').compProj else 0) t) ≤
      ↑L' * dist x y
    rw [dif_pos hx, dif_pos hy]
    rw [ODE.FunSpace.compProj_of_mem ht, ODE.FunSpace.compProj_of_mem ht]
    simpa [ODE.FunSpace.toContinuousMap_apply_eq_apply] using hpoint

/-- Picard-Lindelof vector fields are interval-integrable along a controlled
continuous trajectory. -/
private lemma pl_int
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    {α : Real -> F}
    (hα : ContinuousOn α (Set.Icc tmin tmax))
    (hbound : ∀ s : Real, α s ∈ Metric.closedBall x0 a)
    {t : Real} (ht : t ∈ Set.Icc tmin tmax) :
    IntervalIntegrable (fun s : Real => f s (α s))
      MeasureTheory.volume (t0 : Real) t := by
  have hpair :
      ContinuousOn (fun s : Real => (s, α s)) (Set.Icc tmin tmax) :=
    continuousOn_id.prodMk hα
  have hF :
      ContinuousOn (fun s : Real => f s (α s)) (Set.Icc tmin tmax) := by
    refine hf.continuousOn_uncurry.comp hpair ?_
    intro s hs
    exact ⟨hs, hbound s⟩
  have hsub : Set.uIcc (t0 : Real) t ⊆ Set.Icc tmin tmax :=
    Set.uIcc_subset_Icc t0.2 ht
  exact (hF.mono hsub).intervalIntegrable

private lemma fst_int_sub
    {f g : Real -> E × E} {a b : Real}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ((∫ s in a..b, f s).1 - (∫ s in a..b, g s).1) =
      ∫ s in a..b, (f s - g s).1 := by
  calc
    ((∫ s in a..b, f s).1 - (∫ s in a..b, g s).1)
        = ((∫ s in a..b, f s) - (∫ s in a..b, g s)).1 := by
      rfl
    _ = (∫ s in a..b, f s - g s).1 := by
      rw [intervalIntegral.integral_sub hf hg]
    _ = ∫ s in a..b, (f s - g s).1 := by
      exact ((ContinuousLinearMap.fst Real E E).intervalIntegral_comp_comm
        (hf.sub hg)).symm

private lemma snd_int_sub
    {f g : Real -> E × E} {a b : Real}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ((∫ s in a..b, f s).2 - (∫ s in a..b, g s).2) =
      ∫ s in a..b, (f s - g s).2 := by
  calc
    ((∫ s in a..b, f s).2 - (∫ s in a..b, g s).2)
        = ((∫ s in a..b, f s) - (∫ s in a..b, g s)).2 := by
      rfl
    _ = (∫ s in a..b, f s - g s).2 := by
      rw [intervalIntegral.integral_sub hf hg]
    _ = ∫ s in a..b, (f s - g s).2 := by
      exact ((ContinuousLinearMap.snd Real E E).intervalIntegral_comp_comm
        (hf.sub hg)).symm

private lemma int_const_zero (τ : Real) (c : E) :
    (∫ _s in (0 : Real)..τ, c) = τ • c := by
  calc
    (∫ _s in (0 : Real)..τ, c) = (τ - 0) • c := by
      rw [intervalIntegral.integral_const]
    _ = τ • c := by
      rw [sub_zero]

private lemma const_int (τ : Real) (c : E) :
    IntervalIntegrable (fun _ : Real => c) MeasureTheory.volume (0 : Real) τ :=
  continuousOn_const.intervalIntegrable

private lemma int_sub_const
    {f h : Real -> E} {τ : Real} {c : E}
    (hf : IntervalIntegrable f MeasureTheory.volume (0 : Real) τ)
    (hc : IntervalIntegrable (fun _ : Real => c) MeasureTheory.volume (0 : Real) τ)
    (heq : Set.EqOn f (fun t : Real => c + h t) (Set.uIcc (0 : Real) τ)) :
    (∫ t in (0 : Real)..τ, f t) - τ • c =
      ∫ t in (0 : Real)..τ, h t := by
  calc
    (∫ t in (0 : Real)..τ, f t) - τ • c
        = (∫ t in (0 : Real)..τ, f t) -
            ∫ _t in (0 : Real)..τ, c := by
      rw [int_const_zero]
    _ = ∫ t in (0 : Real)..τ, f t - c := by
      rw [intervalIntegral.integral_sub hf hc]
    _ = ∫ t in (0 : Real)..τ, h t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.uIcc (0 : Real) τ := by simpa using ht
      change f t - c = h t
      rw [heq ht']
      change (c + h t) - c = h t
      abel

/-- A Picard-Lindelof solution whose controlling ball lies in the fixed chart
source gives an ordinary model ODE solution on the open time interval, with
source control for `phaseOfModel`. -/
private theorem modelFlow_src_of_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} (hε : 0 < ε) {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => modelSpray (I := I) g x)
      (tmin := 0 - ε) (tmax := 0 + ε)
      ⟨0, by simp [le_of_lt hε]⟩
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
      a r L K)
    (hsrc : Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) a ⊆
        {z : E × E |
          z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source})
    {z : E × E}
    (hz : z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r) :
    ∃ α : Real -> E × E,
      α 0 = z ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt α (modelSpray (I := I) g x (α t)) t) ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x (α t)).proj ∈
              (extChartAt I x).source := by
  obtain ⟨α, hα0, hαderiv, hαbound⟩ :=
    plSol_bounded (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl hz
  refine ⟨α, by simpa using hα0, ?_, ?_⟩
  · intro t ht
    have htIcc : t ∈ Set.Icc (-ε) ε := Set.Ioo_subset_Icc_self ht
    have hwithin := hαderiv t (by simpa using htIcc)
    have hIcc_mem : Set.Icc (0 - ε) (0 + ε) ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  · intro t ht
    exact hsrc (hαbound t)

/-- The fixed tangent-bundle model chart is a valid source neighborhood for
points whose model coordinates are close to the zero phase. -/
private theorem modelSrc_nhds
    [I.Boundaryless] (x : M) :
    {z : E × E |
      z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source} ∈
      𝓝 (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hsrc_nhds :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseZero (I := I) x) := by
    have hproj :
        ContinuousAt
          (fun q : TangentBundle I M => q.proj)
          (phaseZero (I := I) x) :=
      (FiberBundle.continuous_proj E
        (TangentSpace I : M -> Type _)).continuousAt
    exact hproj.preimage_mem_nhds
      (by
        simpa [extChartAt_source] using
          extChartAt_source_mem_nhds (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc_nhds' :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hsrc_nhds
  have hphase_cont := (phaseOfModel_cdAt (I := I) x).continuousAt
  have htarget :
      (extChartAt I.tangent (phaseZero (I := I) x)).target ∈ 𝓝 z0 :=
    (isOpen_extChartAt_target (I := I.tangent)
      (phaseZero (I := I) x)).mem_nhds
      ((extChartAt I.tangent (phaseZero (I := I) x)).map_source
        (mem_extChartAt_source (I := I.tangent) (phaseZero (I := I) x)))
  exact Filter.inter_mem htarget
    (by
      simpa [z0, Set.preimage, Function.comp_def] using
        hphase_cont.preimage_mem_nhds hsrc_nhds')

/-- Picard-Lindelof data at time `0`, shrunk so the whole controlling model
ball stays in the fixed tangent-bundle chart source. -/
private theorem modelSpray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) a ⊆
          {z : E × E |
            z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x z).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => modelSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (modelSrc_nhds (I := I) x)
  have hpl0 := hpl 0
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl0.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  let δnn : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a δnn
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have ha' : 0 < a' := by
    exact lt_min ha hδnn
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => modelSpray (I := I) g x)
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro z hz
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist z z0 ≤ (a' : Real) := by
    simpa [z0] using Metric.mem_closedBall.mp hz
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist z z0 ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

/-- Uniform short-time model flow with source control in the fixed
tangent-bundle chart around `0_x`. -/
private theorem modelFlow_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r,
        ∃ α : Real -> E × E,
          α 0 = z ∧
            (∀ t ∈ Set.Ioo (-ε) ε,
              HasDerivAt α (modelSpray (I := I) g x (α t)) t) ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (α t)).proj ∈
                  (extChartAt I x).source := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  refine ⟨ε, hε, r, hr, ?_⟩
  intro z hz
  exact modelFlow_src_of_pl (I := I) g x hε hpl hsrc hz

/-- Uniform short-time model flow with Lipschitz dependence on the initial
phase point.

This is the first analytic upgrade beyond relation-valued endpoint existence:
the Picard-Lindelof package supplies a single local flow `α z t` and a
Lipschitz estimate in the initial model phase `z`.  It does not yet assert
source control or strict differentiability of the endpoint map. -/
private theorem modelFlow_lipschitz
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ α : E × E -> Real -> E × E,
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          α z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (α z)
                (modelSpray (I := I) g x (α z t))
                (Set.Icc (-ε) ε) t) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun z => α z t)
                (Metric.closedBall
                  (extChartAt I.tangent (phaseZero (I := I) x)
                    (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, L', hLip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨ε, hε, r, hr, α, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- Uniform short-time model flow with source control and Lipschitz dependence
for the same chosen functional flow. -/
private theorem modelFlow_srcLip
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ α : E × E -> Real -> E × E,
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          α z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (α z)
                (modelSpray (I := I) g x (α z t))
                (Set.Icc (-ε) ε) t) ∧
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          ∀ t ∈ Set.Icc (-ε) ε,
            α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x (α z t)).proj ∈
                (extChartAt I x).source) ∧
        ∃ L' : NNReal,
          ∀ t ∈ Set.Icc (-ε) ε,
            LipschitzOnWith L'
              (fun z => α z t)
              (Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl
  refine ⟨ε, hε, r, hr, α, ?_, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro z hz t ht
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    exact hsrc (hbound z hz' t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- Functional Picard-Lindelof flow with all raw data retained.

This is the package needed for the strict endpoint frontier: the same chosen
flow carries the derivative equation, the Picard-Lindelof vector-field
Lipschitz bound, the closed-ball bound, chart-source control, and Lipschitz
dependence on the initial phase. -/
private theorem modelFlow_pack
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) a ⊆
          {z : E × E |
            z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x z).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => modelSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))
          a r L K ∧
        ∃ α : E × E -> Real -> E × E,
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            α z 0 = z ∧
              ∀ t ∈ Set.Icc (-ε) ε,
                HasDerivWithinAt (α z)
                  (modelSpray (I := I) g x (α z t))
                  (Set.Icc (-ε) ε) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t : Real,
              α z t ∈ Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) a) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              α z t =
                ODE.picard (fun _ : Real => modelSpray (I := I) g x)
                  (⟨0, by simp [le_of_lt hε]⟩ :
                    Set.Icc (0 - ε) (0 + ε)) z (α z) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              α z t ∈ (extChartAt I.tangent
                (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (α z t)).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun z => α z t)
                (Metric.closedBall
                  (extChartAt I.tangent (phaseZero (I := I) x)
                    (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, hbound, hpicard, L', hLip⟩ :=
    plFlow_bound (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl
  refine ⟨ε, hε, a, r, L, K, hr, hsrc, hpl, α, ?_, ?_, ?_, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro z hz t
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    simpa [z0] using hbound z hz' t
  · intro z hz t ht
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hpicard z hz' t ht'
  · intro z hz t ht
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    exact hsrc (hbound z hz' t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- The functional Picard-Lindelof flow fixes an equilibrium point.

This is a generic ODE uniqueness wrapper for the exact flow returned by the
Picard-Lindelof package.  In the normal-coordinate application the equilibrium
is the zero phase coordinate and the zero vector-field fact is
`modelSpray_zero`. -/
private theorem plFlow_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    (ht0 : (t0 : Real) ∈ Set.Ioo tmin tmax)
    {α : F -> Real -> F}
    (hflow : ∀ x ∈ Metric.closedBall x0 r,
      α x t0 = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (α x) (f t (α x t))
            (Set.Icc tmin tmax) t)
    (hbound : ∀ x ∈ Metric.closedBall x0 r, ∀ t : Real,
      α x t ∈ Metric.closedBall x0 a)
    (hzero : ∀ t ∈ Set.Ioo tmin tmax, f t x0 = 0) :
    ∀ t ∈ Set.Icc tmin tmax, α x0 t = x0 := by
  have hx0r : x0 ∈ Metric.closedBall x0 r :=
    Metric.mem_closedBall_self (NNReal.coe_nonneg r)
  have hαcont : ContinuousOn (α x0) (Set.Icc tmin tmax) := by
    exact HasDerivWithinAt.continuousOn
      (fun t ht => (hflow x0 hx0r).2 t ht)
  have hαderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt (α x0) (f t (α x0 t)) t := by
    intro t ht
    have hwithin := (hflow x0 hx0r).2 t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc tmin tmax ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hconstcont :
      ContinuousOn (fun _ : Real => x0) (Set.Icc tmin tmax) :=
    continuous_const.continuousOn
  have hconstderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt (fun _ : Real => x0)
        (f t ((fun _ : Real => x0) t)) t := by
    intro t ht
    simpa [hzero t ht] using
      (hasDerivAt_const (x := t) (c := x0))
  have hEq : Set.EqOn (α x0) (fun _ : Real => x0)
      (Set.Icc tmin tmax) := by
    exact ODE_solution_unique_of_mem_Icc
      (v := f) (s := fun _ : Real => Metric.closedBall x0 a)
      (K := K) (t₀ := (t0 : Real)) (a := tmin) (b := tmax)
      (fun t ht => hf.lipschitzOnWith t (Set.Ioo_subset_Icc_self ht))
      ht0 hαcont hαderiv
      (fun _ _ => hbound x0 hx0r _)
      hconstcont hconstderiv
      (fun _ _ => Metric.mem_closedBall_self (NNReal.coe_nonneg a))
      (hflow x0 hx0r).1
  intro t ht
  exact hEq ht

/-- The model flow produced at the zero phase keeps the zero phase fixed. -/
private theorem modelFlow_zero
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} (hε : 0 < ε) {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => modelSpray (I := I) g x)
      (tmin := 0 - ε) (tmax := 0 + ε)
      ⟨0, by simp [le_of_lt hε]⟩
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
      a r L K)
    {α : E × E -> Real -> E × E}
    (hflow : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      α z 0 = z ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt (α z)
            (modelSpray (I := I) g x (α z t))
            (Set.Icc (-ε) ε) t)
    (hbound : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t : Real,
        α z t ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) a) :
    ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have ht0 : ((⟨0, by simp [le_of_lt hε]⟩ :
      Set.Icc (0 - ε) (0 + ε)) : Real) ∈
      Set.Ioo (0 - ε) (0 + ε) := by
    simpa using hε
  have hzero : ∀ t ∈ Set.Ioo (0 - ε) (0 + ε),
      (fun _ : Real => modelSpray (I := I) g x) t z0 = 0 := by
    intro t ht
    simpa [z0] using modelSpray_zero (I := I) g x
  have hfix := plFlow_zero
    (F := E × E)
    (f := fun _ : Real => modelSpray (I := I) g x)
    (tmin := 0 - ε) (tmax := 0 + ε)
    (t0 := ⟨0, by simp [le_of_lt hε]⟩)
    (x0 := z0) (a := a) (r := r) (L := L) (K := K)
    hpl ht0
    (α := α)
    (by
      intro z hz
      simpa [z0] using hflow z hz)
    (by
      intro z hz t
      simpa [z0] using hbound z hz t)
    hzero
  intro t ht
  have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
    simpa using ht
  simpa [z0] using hfix t ht'

/-- Short-time model flow produced by the local Picard-Lindelof package.

This is still a short-time statement.  It is the checked analytic producer
that should feed either a continuation argument or the homogeneous rescaling
argument for `exists_exp_one`. -/
private theorem modelFlow_short
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r,
        ∃ α : Real -> E × E,
          α 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt α
                (modelSpray (I := I) g x (α t))
                (Set.Icc (-ε) ε) t := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  refine ⟨ε, hε, r, hr, ?_⟩
  intro z hz
  obtain ⟨α, hα0, hαderiv⟩ :=
    (hpl 0).exists_eq_forall_mem_Icc_hasDerivWithinAt
      (x := z) (by simpa [z0] using hz)
  refine ⟨α, hα0, ?_⟩
  intro t ht
  have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
    simpa using ht
  simpa using hαderiv t ht'

/-- Chart coordinate of the time-one endpoint produced from a fixed functional
model flow and the homogeneous time rescaling. -/
private def chartEnd
    (α : E × E -> Real -> E × E) (τ : Real) (x : M)
    (v : TangentSpace I x) : E :=
  (α (initPhase (I := I) x (τ⁻¹ • v)) τ).1

/-- Manifold endpoint produced from a fixed functional model flow and the
homogeneous time rescaling. -/
private def manifoldEnd
    (α : E × E -> Real -> E × E) (τ : Real) (x : M)
    (v : TangentSpace I x) : M :=
  (phaseOfModel (I := I) x
    (chartEnd (I := I) α τ x v,
      τ • (α (initPhase (I := I) x (τ⁻¹ • v)) τ).2)).proj

/-- Zero initial velocity has zero chart endpoint for a functional model flow
that fixes the zero phase. -/
private theorem chartEnd_zero
    {α : E × E -> Real -> E × E} {ε τ : Real} (x : M)
    (hτ : τ ∈ Set.Icc (-ε) ε)
    (hzero : ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :
    chartEnd (I := I) α τ x (0 : TangentSpace I x) =
      extChartAt I x x := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hinit :
      initPhase (I := I) x (τ⁻¹ • (0 : TangentSpace I x)) = z0 := by
    simp [z0]
  have hz : α z0 τ = z0 := by
    simpa [z0] using hzero τ hτ
  calc
    chartEnd (I := I) α τ x (0 : TangentSpace I x)
        = (α z0 τ).1 := by
          simp [chartEnd, z0]
    _ = z0.1 := by rw [hz]
    _ = extChartAt I x x := by
      simpa [z0] using congrArg Prod.fst (phaseZero_pair (I := I) x)

/-- Zero initial velocity gives the base point for a functional model flow
that fixes the zero phase. -/
private theorem manifoldEnd_zero
    {α : E × E -> Real -> E × E} {ε τ : Real} (x : M)
    (hτ : τ ∈ Set.Icc (-ε) ε)
    (hzero : ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :
    manifoldEnd (I := I) α τ x (0 : TangentSpace I x) = x := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hτzero : α z0 τ = z0 := by
    simpa [z0] using hzero τ hτ
  have hfst := chartEnd_zero (I := I) (α := α) (ε := ε)
    (τ := τ) x hτ hzero
  have hpair :
      (chartEnd (I := I) α τ x (0 : TangentSpace I x),
        τ • (α (initPhase (I := I) x
          (τ⁻¹ • (0 : TangentSpace I x))) τ).2) = z0 := by
    have hinit :
        initPhase (I := I) x (τ⁻¹ • (0 : TangentSpace I x)) = z0 := by
      simp [z0]
    rw [hfst, hinit, hτzero]
    apply Prod.ext
    · simpa [z0] using congrArg Prod.fst (phaseZero_pair (I := I) x)
    · have hsnd : z0.2 = (0 : E) := by
        simpa [z0] using congrArg Prod.snd (phaseZero_pair (I := I) x)
      rw [hsnd, smul_zero]
  have hphase :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  change (phaseOfModel (I := I) x
    (chartEnd (I := I) α τ x (0 : TangentSpace I x),
      τ • (α (initPhase (I := I) x
        (τ⁻¹ • (0 : TangentSpace I x))) τ).2)).proj = x
  rw [hpair]
  simpa [z0, phaseZero] using congrArg Bundle.TotalSpace.proj hphase

/-- In the fixed base chart, the manifold endpoint has coordinate
`chartEnd` whenever the underlying model phase is in the fixed tangent-bundle
chart target. -/
private theorem manifoldEnd_chart
    [I.Boundaryless]
    {α : E × E -> Real -> E × E} {τ : Real} (x : M)
    {v : TangentSpace I x}
    (htarget : α (initPhase (I := I) x (τ⁻¹ • v)) τ ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target) :
    extChartAt I x (manifoldEnd (I := I) α τ x v) =
      chartEnd (I := I) α τ x v := by
  let z : E × E := α (initPhase (I := I) x (τ⁻¹ • v)) τ
  let zβ : E × E := (z.1, τ • z.2)
  have hzβtarget :
      zβ ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target := by
    simpa [zβ] using
      phaseTarget_smul (I := I) x (z := z) (a := τ) (by simpa [z] using htarget)
  have hzβsrc :
      (phaseOfModel (I := I) x zβ).proj ∈ (extChartAt I x).source := by
    simpa [zβ] using
      phaseSrc_smul (I := I) x (z := z) (a := τ) (by simpa [z] using htarget)
  have hchart := phaseOfModel_chart (I := I) x hzβtarget hzβsrc
  simpa [manifoldEnd, chartEnd, z, zβ] using hchart

/-- Near zero, the manifold-valued functional endpoint has chart coordinate
`chartEnd`, provided the model flow stays in the fixed tangent-bundle chart
target. -/
private theorem chartEnd_eventually_eq
    [I.Boundaryless]
    {α : E × E -> Real -> E × E} {ε τ ρ : Real} {rModel : NNReal}
    (x : M) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hsmall : ∀ v ∈ Metric.ball (0 : TangentSpace I x) ρ,
      initPhase (I := I) x v ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel)
    (hsrc : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) rModel,
      ∀ t ∈ Set.Icc (-ε) ε,
        α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x (α z t)).proj ∈
            (extChartAt I x).source)
    (hτmem : τ ∈ Set.Icc (-ε) ε) :
    chartEnd (I := I) α τ x =ᶠ[𝓝 (0 : TangentSpace I x)]
      fun v : TangentSpace I x =>
        extChartAt I x (manifoldEnd (I := I) α τ x v) := by
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  have hball : Metric.ball (0 : TangentSpace I x) R ∈
      𝓝 (0 : TangentSpace I x) :=
    Metric.ball_mem_nhds _ hR
  filter_upwards [hball] with v hv
  let u : TangentSpace I x := τ⁻¹ • v
  let z : E × E := initPhase (I := I) x u
  have hu : u ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hv ⊢
    have hvnorm : ‖v‖ < τ * ρ := by
      simpa [R, dist_zero_right] using hv
    have hscale := mul_lt_mul_of_pos_left hvnorm (inv_pos.mpr hτ)
    have hnormu : ‖τ⁻¹ • v‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
      rw [← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul] at hscale
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscale
    simpa [u, dist_zero_right] using hnormu
  have hz : z ∈ Metric.closedBall
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) rModel := by
    exact hsmall u hu
  have htarget := (hsrc z hz τ hτmem).1
  have hchart := manifoldEnd_chart (I := I) (α := α) (τ := τ) x
    (v := v) htarget
  simpa [z, u] using hchart.symm

/-- First-coordinate Picard integral equation for the fixed chart endpoint. -/
private theorem chartEnd_picard
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε τ : Real} (hε : 0 < ε) {r : NNReal}
    {α : E × E -> Real -> E × E}
    (hpicard : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t ∈ Set.Icc (-ε) ε,
        α z t =
          ODE.picard (fun _ : Real => modelSpray (I := I) g x)
            (⟨0, by simp [le_of_lt hε]⟩ :
              Set.Icc (0 - ε) (0 + ε)) z (α z) t)
    {v : TangentSpace I x}
    (hv : initPhase (I := I) x (τ⁻¹ • v) ∈
      Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r)
    (hτmem : τ ∈ Set.Icc (-ε) ε) :
    chartEnd (I := I) α τ x v =
      (initPhase (I := I) x (τ⁻¹ • v)).1 +
        (∫ s in (0 : Real)..τ,
          modelSpray (I := I) g x
            (α (initPhase (I := I) x (τ⁻¹ • v)) s)).1 := by
  let z : E × E := initPhase (I := I) x (τ⁻¹ • v)
  have hp := hpicard z (by simpa [z] using hv) τ hτmem
  have hpfst := congrArg Prod.fst hp
  simpa [chartEnd, z, ODE.picard_apply] using hpfst

/-- The functional model endpoint realizes the relation-valued exponential
wherever the rescaled initial phase lies in the Picard-Lindelof ball. -/
private theorem end_expAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} (hε : 0 < ε) {r : NNReal}
    {α : E × E -> Real -> E × E}
    (hflow : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      α z 0 = z ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt (α z)
            (modelSpray (I := I) g x (α z t))
            (Set.Icc (-ε) ε) t)
    (hsrc : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t ∈ Set.Icc (-ε) ε,
        α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x (α z t)).proj ∈
            (extChartAt I x).source)
    {v : TangentSpace I x}
    (hv : initPhase (I := I) x ((ε / 2)⁻¹ • v) ∈
      Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r) :
    expAt (I := I) g x v (manifoldEnd (I := I) α (ε / 2) x v) := by
  classical
  let τ : Real := ε / 2
  let u : TangentSpace I x := τ⁻¹ • v
  let z : E × E := initPhase (I := I) x u
  have hz : z ∈ Metric.closedBall
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) r := by
    simpa [z, u, τ] using hv
  have hτ : 0 < τ := by
    exact half_pos hε
  have hα0 : α z 0 = z := (hflow z hz).1
  have hαderiv : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt (α z) (modelSpray (I := I) g x (α z t)) t := by
    intro t ht
    have hwithin := (hflow z hz).2 t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc (-ε) ε ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hαsrc : ∀ t ∈ Set.Icc (-ε) ε,
      α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (α z t)).proj ∈
          (extChartAt I x).source := hsrc z hz
  let β : Real -> E × E := modelRescale (α z) τ
  let lift : Real -> TangentBundle I M :=
    fun s : Real => phaseOfModel (I := I) x (β s)
  let gamma : Curve M := projectCurve (I := I) lift
  have hτu : τ • u = v := by
    change τ • (τ⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have hβ0 : β 0 = initPhase (I := I) x v := by
    calc
      β 0 = ((α z 0).1, τ • (α z 0).2) := by
        simp [β]
      _ = ((initPhase (I := I) x u).1,
            τ • (initPhase (I := I) x u).2) := by
        rw [hα0]
      _ = initPhase (I := I) x (τ • u) :=
        initPhase_smul (I := I) x τ u
      _ = initPhase (I := I) x v := by
        rw [hτu]
  have hqsrc :
      (⟨x, v⟩ : TangentBundle I M) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).source := by
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    simp [phaseZero]
  have hlift0 : lift 0 = (⟨x, v⟩ : TangentBundle I M) := by
    change phaseOfModel (I := I) x (β 0) =
      (⟨x, v⟩ : TangentBundle I M)
    rw [hβ0]
    simpa [initPhase] using
      PartialEquiv.left_inv
        (extChartAt I.tangent (phaseZero (I := I) x)) hqsrc
  have hβderiv : ∀ s ∈ Metric.ball (0 : Real) 2,
      HasDerivAt β (modelSpray (I := I) g x (β s)) s := by
    intro s hs
    exact modelRescale_deriv (I := I) g x hαderiv hαsrc
      (by simpa [τ] using half_mul_mem_Ioo hε hs)
  have hβsrc : ∀ s ∈ Metric.ball (0 : Real) 2,
      β s ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (β s)).proj ∈
          (extChartAt I x).source := by
    intro s hs
    have htIoo : τ * s ∈ Set.Ioo (-ε) ε := by
      simpa [τ] using half_mul_mem_Ioo hε hs
    have htIcc : τ * s ∈ Set.Icc (-ε) ε :=
      Set.Ioo_subset_Icc_self htIoo
    have hαtarget :
        α z (τ * s) ∈
          (extChartAt I.tangent (phaseZero (I := I) x)).target :=
      (hαsrc (τ * s) htIcc).1
    constructor
    · simpa [β, modelRescale] using
        phaseTarget_smul (I := I) x (z := α z (τ * s)) (a := τ)
          hαtarget
    · simpa [β, modelRescale] using
        phaseSrc_smul (I := I) x (z := α z (τ * s)) (a := τ)
          hαtarget
  have hspray : IsMIntegralCurveOn lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) 2) := by
    simpa [lift, β] using
      modelSol_integralOn (I := I) g x hβderiv hβsrc
  have hspray0 : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) 0 :=
    hspray.isMIntegralCurveAt
      (Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 2))
  have hsrcBall : ∀ s ∈ Metric.ball (0 : Real) 2,
      projectCurve (I := I) lift s ∈
        (extChartAtCoordinateData (I := I) x).domain := by
    intro s hs
    simpa [projectCurve, lift, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using (hβsrc s hs).2
  have hy : gamma 1 = manifoldEnd (I := I) α τ x v := by
    simp [gamma, lift, β, manifoldEnd, chartEnd, modelRescale, z, u, τ]
  rw [← hy]
  refine expAt_of_segment (I := I) (g := g)
    (x := x) (v := v) (gamma := gamma) (s := Set.uIcc 0 1)
    (by intro t ht; exact ht) ?_
  refine ⟨?_, ?_, ?_⟩
  · simpa [gamma] using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) hlift0
  · simpa [gamma] using
      projectCurve_initialVelocity_of_geodesicSprayIntegral
        (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
        (f := lift) hlift0 hspray0
  · constructor
    · intro t ht
      exact hsrcBall t (uIcc01_mem_ball_two ht)
    · intro t ht
      have htball : t ∈ Metric.ball (0 : Real) 2 :=
        uIcc01_mem_ball_two ht
      have hode := coordSprayODEOn
        (I := I) (g := g) (x := x) (v := v)
        (lift := lift) (epsilon := (2 : Real)) (t := t)
        hlift0 hspray htball hsrcBall
      exact hode.zeroAccel

/-- Uniform time-one local existence of spray-backed radial segments near zero
velocity.

This is the producer form of local geodesic existence.  It retains the
tangent-bundle lift, the spray integral-curve equation, and fixed-chart source
control, which are the data later needed for speed constancy and Gauss lemma
arguments. -/
theorem exists_sprayRadial
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    ∃ r > 0, ∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
      Nonempty (SprayRadialSegment (I := I) g x v) := by
  classical
  obtain ⟨ε, hε, rModel, hrModel, hflow⟩ :=
    modelFlow_src (I := I) g x
  obtain ⟨ρ, hρ, hsmall⟩ := initPhase_small (I := I) x hrModel
  let τ : Real := ε / 2
  have hτ : 0 < τ := by
    exact half_pos hε
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  refine ⟨R, hR, ?_⟩
  intro v hv
  let u : TangentSpace I x := τ⁻¹ • v
  have hu : u ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hv ⊢
    have hvnorm : ‖v‖ < τ * ρ := by
      simpa [R, dist_zero_right] using hv
    have hscale :=
      mul_lt_mul_of_pos_left hvnorm (inv_pos.mpr hτ)
    have hnormu : ‖τ⁻¹ • v‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
      rw [← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul] at hscale
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscale
    simpa [u, dist_zero_right] using hnormu
  obtain ⟨α, hα0, hαderiv, hαsrc⟩ :=
    hflow (initPhase (I := I) x u) (hsmall u hu)
  let β : Real -> E × E := modelRescale α τ
  let lift : Real -> TangentBundle I M :=
    fun s : Real => phaseOfModel (I := I) x (β s)
  have hτu : τ • u = v := by
    change τ • (τ⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have hβ0 : β 0 = initPhase (I := I) x v := by
    calc
      β 0 = ((α 0).1, τ • (α 0).2) := by
        simp [β]
      _ = ((initPhase (I := I) x u).1,
            τ • (initPhase (I := I) x u).2) := by
        rw [hα0]
      _ = initPhase (I := I) x (τ • u) :=
        initPhase_smul (I := I) x τ u
      _ = initPhase (I := I) x v := by
        rw [hτu]
  have hqsrc :
      (⟨x, v⟩ : TangentBundle I M) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).source := by
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    simp [phaseZero]
  have hlift0 : lift 0 = (⟨x, v⟩ : TangentBundle I M) := by
    change phaseOfModel (I := I) x (β 0) =
      (⟨x, v⟩ : TangentBundle I M)
    rw [hβ0]
    simpa [initPhase] using
      PartialEquiv.left_inv
        (extChartAt I.tangent (phaseZero (I := I) x)) hqsrc
  have hβderiv : ∀ s ∈ Metric.ball (0 : Real) 2,
      HasDerivAt β (modelSpray (I := I) g x (β s)) s := by
    intro s hs
    exact modelRescale_deriv (I := I) g x hαderiv hαsrc
      (half_mul_mem_Ioo hε hs)
  have hβsrc : ∀ s ∈ Metric.ball (0 : Real) 2,
      β s ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (β s)).proj ∈
          (extChartAt I x).source := by
    intro s hs
    have htIoo := half_mul_mem_Ioo hε hs
    have htIcc : τ * s ∈ Set.Icc (-ε) ε :=
      Set.Ioo_subset_Icc_self htIoo
    have hαtarget : α (τ * s) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target :=
      (hαsrc (τ * s) htIcc).1
    constructor
    · simpa [β, modelRescale] using
        phaseTarget_smul (I := I) x (z := α (τ * s)) (a := τ)
          hαtarget
    · simpa [β, modelRescale] using
        phaseSrc_smul (I := I) x (z := α (τ * s)) (a := τ)
          hαtarget
  have hspray : IsMIntegralCurveOn lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) 2) := by
    simpa [lift, β] using
      modelSol_integralOn (I := I) g x hβderiv hβsrc
  have hsrcBall : ∀ s ∈ Metric.ball (0 : Real) 2,
      projectCurve (I := I) lift s ∈
        (extChartAtCoordinateData (I := I) x).domain := by
    intro s hs
    simpa [projectCurve, lift, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using (hβsrc s hs).2
  refine ⟨{
    epsilon := 2
    epsilon_pos := by norm_num
    interval_subset := ?_
    lift := lift
    lift_initial := hlift0
    spray_integral := hspray
    source := hsrcBall }⟩
  intro t ht
  exact uIcc01_mem_ball_two ht

/-- Uniform time-one local existence of the relation-valued coordinate
exponential near zero velocity. -/
theorem exists_exp_one
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    ∃ r > 0, ∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
      ∃ y : M, expAt (I := I) g x v y := by
  obtain ⟨r, hr, hG⟩ := exists_sprayRadial (I := I) g x
  refine ⟨r, hr, ?_⟩
  intro v hv
  rcases hG v hv with ⟨G⟩
  exact ⟨G.gamma 1,
    expAt_of_segment (I := I) (g := g) (x := x) (v := v)
      (gamma := G.gamma) (s := Metric.ball (0 : Real) G.epsilon)
      G.interval_subset G.segment⟩

set_option maxHeartbeats 800000 in
/-- Strict derivative at zero for a functional local endpoint map.

This is intentionally stated only after choosing a genuine local endpoint
function realizing `expAt` on a ball.  An arbitrary `Classical.choose` from the
relation-valued endpoint would not be smooth; the missing proof is smooth
dependence and uniqueness of the chart-fixed geodesic flow, followed by the
standard zero-velocity linearization. -/
theorem expAt_strict
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    ∃ r > 0, ∃ exp : TangentSpace I x -> M,
      exp 0 = x ∧
        (∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
          expAt (I := I) g x v (exp v)) ∧
        HasStrictFDerivAt
          (fun v : TangentSpace I x => extChartAt I x (exp v))
          (ContinuousLinearMap.id Real (TangentSpace I x)) 0 := by
  classical
  obtain ⟨ε, hε, a, rModel, _L, _K, hrModel, _hsrc, hpl,
    α, hflow, hbound, hpicard, hsrcFlow, L', hLip⟩ :=
    modelFlow_pack (I := I) g x
  obtain ⟨ρ, hρ, hsmall⟩ := initPhase_small (I := I) x hrModel
  let τ : Real := ε / 2
  have hτ : 0 < τ := half_pos hε
  have hτmem : τ ∈ Set.Icc (-ε) ε := by
    constructor <;> dsimp [τ] <;> linarith
  have hzero := modelFlow_zero (I := I) g x hε hpl hflow hbound
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  refine ⟨R, hR, manifoldEnd (I := I) α τ x, ?_, ?_, ?_⟩
  · exact manifoldEnd_zero (I := I) (α := α) (ε := ε) (τ := τ)
      x hτmem hzero
  · intro v hv
    let u : TangentSpace I x := τ⁻¹ • v
    have hu : u ∈ Metric.ball (0 : TangentSpace I x) ρ := by
      rw [Metric.mem_ball] at hv ⊢
      have hvnorm : ‖v‖ < τ * ρ := by
        simpa [R, dist_zero_right] using hv
      have hscale :=
        mul_lt_mul_of_pos_left hvnorm (inv_pos.mpr hτ)
      have hnormu : ‖τ⁻¹ • v‖ < ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
        rw [← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul] at hscale
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscale
      simpa [u, dist_zero_right] using hnormu
    have hvsmall : initPhase (I := I) x ((ε / 2)⁻¹ • v) ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel := by
      simpa [τ, u] using hsmall u hu
    simpa [τ] using
      end_expAt (I := I) (g := g) (x := x)
        (ε := ε) hε (r := rModel) (α := α)
        hflow hsrcFlow hvsmall
  · have hstrict :
        HasStrictFDerivAt
          (fun v : TangentSpace I x =>
            extChartAt I x (manifoldEnd (I := I) α τ x v))
          (ContinuousLinearMap.id Real (TangentSpace I x)) 0 := by
      have hchartStrict :
          HasStrictFDerivAt
            (chartEnd (I := I) α τ x)
            (ContinuousLinearMap.id Real (TangentSpace I x)) 0 := by
        rw [hasStrictFDerivAt_iff_isLittleO]
        have hsub0τ : Set.Icc (0 : Real) τ ⊆ Set.Icc (-ε) ε := by
          intro t ht
          constructor
          · linarith [hε, ht.1]
          · exact le_trans ht.2 hτmem.2
        have huIcc0τ : Set.uIcc (0 : Real) τ ⊆ Set.Icc (-ε) ε := by
          intro t ht
          have htIcc : t ∈ Set.Icc (0 : Real) τ := by
            rw [Set.uIcc_of_le hτ.le] at ht
            exact ht
          constructor
          · linarith [hε, htIcc.1]
          · exact le_trans htIcc.2 hτmem.2
        have huIcc0τ' : Set.uIcc (0 : Real) τ ⊆ Set.Icc (0 - ε) (0 + ε) := by
          intro t ht
          have htE : t ∈ Set.Icc (-ε) ε := huIcc0τ ht
          constructor <;> linarith [htE.1, htE.2]
        have hres_uniform :
            ∀ c > 0, ∀ᶠ p : TangentSpace I x × TangentSpace I x in
              𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x),
              ∀ t ∈ Set.Icc (0 : Real) τ,
                ‖modelSpray (I := I) g x
                    (α (initPhase (I := I) x (τ⁻¹ • p.1)) t) -
                  modelSpray (I := I) g x
                    (α (initPhase (I := I) x (τ⁻¹ • p.2)) t) -
                  modelSprayLin (E := E)
                    (α (initPhase (I := I) x (τ⁻¹ • p.1)) t -
                      α (initPhase (I := I) x (τ⁻¹ • p.2)) t)‖
                  ≤ c * ‖p.1 - p.2‖ :=
          sprayRem_uniform (I := I) g x
            (ε := ε) (τ := τ) (ρ := ρ) (rModel := rModel)
            (L' := L') (α := α) hρ hτ hsub0τ hsmall hzero hLip
        let res : (TangentSpace I x × TangentSpace I x) -> Real -> E × E :=
          fun p t =>
            modelSpray (I := I) g x
                (α (initPhase (I := I) x (τ⁻¹ • p.1)) t) -
              modelSpray (I := I) g x
                (α (initPhase (I := I) x (τ⁻¹ • p.2)) t) -
              modelSprayLin (E := E)
                (α (initPhase (I := I) x (τ⁻¹ • p.1)) t -
                  α (initPhase (I := I) x (τ⁻¹ • p.2)) t)
        have hres_snd :
            ∀ c > 0, ∀ᶠ p : TangentSpace I x × TangentSpace I x in
              𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x),
              ∀ s ∈ Set.Icc (0 : Real) τ,
                ‖(res p s).2‖ ≤ c * ‖p.1 - p.2‖ := by
          intro c hc
          filter_upwards [hres_uniform c hc] with p hp s hs
          exact (norm_snd_le (res p s)).trans (hp s hs)
        have hvel_int :
            ∀ c > 0, ∀ᶠ p : TangentSpace I x × TangentSpace I x in
              𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x),
              ∀ t ∈ Set.Icc (0 : Real) τ,
                ‖∫ s in (0 : Real)..t, (res p s).2‖ ≤
                  c * ‖p.1 - p.2‖ :=
          eventually_norm_integral_zero_to_t_le (b := τ) hτ.le hres_snd
        have hdouble_int :
            (fun p : TangentSpace I x × TangentSpace I x =>
              ∫ t in (0 : Real)..τ,
                ∫ s in (0 : Real)..t, (res p s).2)
              =o[𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x)]
                fun p => p.1 - p.2 := by
          apply isLittleO_intervalIntegral_of_uniform_bound
          intro c hc
          filter_upwards [hvel_int c hc] with p hp t ht
          have htIcc : t ∈ Set.Icc (0 : Real) τ := by
            rw [Set.mem_uIoc] at ht
            rcases ht with ht | ht
            · exact ⟨ht.1.le, ht.2⟩
            · have hlt : t < t := lt_of_le_of_lt (le_trans ht.2 hτ.le) ht.1
              exact (lt_irrefl t hlt).elim
          exact hp t htIcc
        have hvel_formula :
            ∀ᶠ p : TangentSpace I x × TangentSpace I x in
              𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x),
              ∀ t ∈ Set.Icc (0 : Real) τ,
                (α (initPhase (I := I) x (τ⁻¹ • p.1)) t -
                    α (initPhase (I := I) x (τ⁻¹ • p.2)) t).2 =
                  (initPhase (I := I) x (τ⁻¹ • p.1) -
                    initPhase (I := I) x (τ⁻¹ • p.2)).2 +
                    ∫ s in (0 : Real)..t, (res p s).2 := by
          have hcont1 :
              ContinuousAt
                (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.1)
                ((0, 0) : TangentSpace I x × TangentSpace I x) := by
            exact (continuous_const.smul continuous_fst).continuousAt
          have hcont2 :
              ContinuousAt
                (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.2)
                ((0, 0) : TangentSpace I x × TangentSpace I x) := by
            exact (continuous_const.smul continuous_snd).continuousAt
          have hnear1 := hcont1.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
          have hnear2 := hcont2.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
          filter_upwards [hnear1, hnear2] with p hp1 hp2 t ht
          let z1 : E × E := initPhase (I := I) x (τ⁻¹ • p.1)
          let z2 : E × E := initPhase (I := I) x (τ⁻¹ • p.2)
          have hp1ball : τ⁻¹ • p.1 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
            simpa using hp1
          have hp2ball : τ⁻¹ • p.2 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
            simpa using hp2
          have hz1 : z1 ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) rModel := by
            simpa [z1] using hsmall (τ⁻¹ • p.1) hp1ball
          have hz2 : z2 ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) rModel := by
            simpa [z2] using hsmall (τ⁻¹ • p.2) hp2ball
          have htE : t ∈ Set.Icc (-ε) ε := hsub0τ ht
          have hp1pic := hpicard z1 hz1 t htE
          have hp2pic := hpicard z2 hz2 t htE
          have hsnd1 :
              (α z1 t).2 =
                z1.2 +
                  (∫ s in (0 : Real)..t,
                    modelSpray (I := I) g x (α z1 s)).2 := by
            have h := congrArg Prod.snd hp1pic
            simpa [z1, ODE.picard_apply] using h
          have hsnd2 :
              (α z2 t).2 =
                z2.2 +
                  (∫ s in (0 : Real)..t,
                    modelSpray (I := I) g x (α z2 s)).2 := by
            have h := congrArg Prod.snd hp2pic
            simpa [z2, ODE.picard_apply] using h
          have hres_snd_point :
              (fun s : Real => (res p s).2) =
                (fun s : Real =>
                  (modelSpray (I := I) g x (α z1 s) -
                    modelSpray (I := I) g x (α z2 s)).2) := by
            funext s
            simp [res, z1, z2, modelSprayLin_snd]
          calc
            (α (initPhase (I := I) x (τ⁻¹ • p.1)) t -
                α (initPhase (I := I) x (τ⁻¹ • p.2)) t).2
                = (α z1 t - α z2 t).2 := by rfl
            _ = (α z1 t).2 - (α z2 t).2 := by rfl
            _ = (z1.2 +
                    (∫ s in (0 : Real)..t,
                      modelSpray (I := I) g x (α z1 s)).2) -
                  (z2.2 +
                    (∫ s in (0 : Real)..t,
                      modelSpray (I := I) g x (α z2 s)).2) := by
              rw [hsnd1, hsnd2]
            _ = (z1 - z2).2 +
                  ((∫ s in (0 : Real)..t,
                      modelSpray (I := I) g x (α z1 s)).2 -
                    (∫ s in (0 : Real)..t,
                      modelSpray (I := I) g x (α z2 s)).2) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            _ = (initPhase (I := I) x (τ⁻¹ • p.1) -
                    initPhase (I := I) x (τ⁻¹ • p.2)).2 +
                  ∫ s in (0 : Real)..t, (res p s).2 := by
              change (z1 - z2).2 +
                    ((∫ s in (0 : Real)..t,
                        modelSpray (I := I) g x (α z1 s)).2 -
                      (∫ s in (0 : Real)..t,
                        modelSpray (I := I) g x (α z2 s)).2) =
                  (z1 - z2).2 + ∫ s in (0 : Real)..t, (res p s).2
              rw [hres_snd_point]
              have hα1cont :
                  ContinuousOn (α z1) (Set.Icc (0 - ε) (0 + ε)) := by
                rw [show (0 : Real) - ε = -ε by ring,
                  show (0 : Real) + ε = ε by ring]
                exact HasDerivWithinAt.continuousOn
                  (fun s hs => (hflow z1 hz1).2 s hs)
              have hα2cont :
                  ContinuousOn (α z2) (Set.Icc (0 - ε) (0 + ε)) := by
                rw [show (0 : Real) - ε = -ε by ring,
                  show (0 : Real) + ε = ε by ring]
                exact HasDerivWithinAt.continuousOn
                  (fun s hs => (hflow z2 hz2).2 s hs)
              have htE' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
                simpa using htE
              have hint1 :
                  IntervalIntegrable
                    (fun s : Real =>
                      modelSpray (I := I) g x (α z1 s))
                    MeasureTheory.volume (0 : Real) t := by
                exact pl_int (hf := hpl) hα1cont
                  (fun s => hbound z1 hz1 s) htE'
              have hint2 :
                  IntervalIntegrable
                    (fun s : Real =>
                      modelSpray (I := I) g x (α z2 s))
                    MeasureTheory.volume (0 : Real) t := by
                exact pl_int (hf := hpl) hα2cont
                  (fun s => hbound z2 hz2 s) htE'
              have hsubint :
                  ((∫ s in (0 : Real)..t,
                      modelSpray (I := I) g x (α z1 s)).2 -
                    (∫ s in (0 : Real)..t,
                      modelSpray (I := I) g x (α z2 s)).2) =
                    ∫ s in (0 : Real)..t,
                      (modelSpray (I := I) g x (α z1 s) -
                        modelSpray (I := I) g x (α z2 s)).2 := by
                exact snd_int_sub hint1 hint2
              rw [hsubint]
        have hendpoint :
            (fun p : TangentSpace I x × TangentSpace I x =>
              chartEnd (I := I) α τ x p.1 -
                chartEnd (I := I) α τ x p.2 -
                τ • (initPhase (I := I) x (τ⁻¹ • p.1) -
                  initPhase (I := I) x (τ⁻¹ • p.2)).2)
              =ᶠ[𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x)]
            (fun p : TangentSpace I x × TangentSpace I x =>
              ∫ t in (0 : Real)..τ,
                ∫ s in (0 : Real)..t, (res p s).2) := by
          have hcont1 :
              ContinuousAt
                (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.1)
                ((0, 0) : TangentSpace I x × TangentSpace I x) := by
            exact (continuous_const.smul continuous_fst).continuousAt
          have hcont2 :
              ContinuousAt
                (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.2)
                ((0, 0) : TangentSpace I x × TangentSpace I x) := by
            exact (continuous_const.smul continuous_snd).continuousAt
          have hnear1 := hcont1.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
          have hnear2 := hcont2.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
          filter_upwards [hnear1, hnear2, hvel_formula] with p hp1 hp2 hpvel
          let z1 : E × E := initPhase (I := I) x (τ⁻¹ • p.1)
          let z2 : E × E := initPhase (I := I) x (τ⁻¹ • p.2)
          have hp1ball : τ⁻¹ • p.1 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
            simpa using hp1
          have hp2ball : τ⁻¹ • p.2 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
            simpa using hp2
          have hz1 : z1 ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) rModel := by
            simpa [z1] using hsmall (τ⁻¹ • p.1) hp1ball
          have hz2 : z2 ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) rModel := by
            simpa [z2] using hsmall (τ⁻¹ • p.2) hp2ball
          have hchart1 :
              chartEnd (I := I) α τ x p.1 =
                z1.1 +
                  (∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z1 s)).1 := by
            simpa [z1] using
              chartEnd_picard (I := I) (g := g) (x := x)
                (ε := ε) (τ := τ) hε (r := rModel)
                (α := α) hpicard (v := p.1) hz1 hτmem
          have hchart2 :
              chartEnd (I := I) α τ x p.2 =
                z2.1 +
                  (∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z2 s)).1 := by
            simpa [z2] using
              chartEnd_picard (I := I) (g := g) (x := x)
                (ε := ε) (τ := τ) hε (r := rModel)
                (α := α) hpicard (v := p.2) hz2 hτmem
          have hfst_eq : z1.1 = z2.1 := by
            have h1 := congrArg Prod.fst
              (initPhase_eq_pair (I := I) x (τ⁻¹ • p.1))
            have h2 := congrArg Prod.fst
              (initPhase_eq_pair (I := I) x (τ⁻¹ • p.2))
            calc
              z1.1 = extChartAt I x x := by simpa [z1] using h1
              _ = z2.1 := by simpa [z2] using h2.symm
          have hα1cont :
              ContinuousOn (α z1) (Set.Icc (0 - ε) (0 + ε)) := by
            rw [show (0 : Real) - ε = -ε by ring,
              show (0 : Real) + ε = ε by ring]
            exact HasDerivWithinAt.continuousOn
              (fun s hs => (hflow z1 hz1).2 s hs)
          have hα2cont :
              ContinuousOn (α z2) (Set.Icc (0 - ε) (0 + ε)) := by
            rw [show (0 : Real) - ε = -ε by ring,
              show (0 : Real) + ε = ε by ring]
            exact HasDerivWithinAt.continuousOn
              (fun s hs => (hflow z2 hz2).2 s hs)
          have hτmem' : τ ∈ Set.Icc (0 - ε) (0 + ε) := by
            rw [show (0 : Real) - ε = -ε by ring,
              show (0 : Real) + ε = ε by ring]
            exact hτmem
          have hint1 :
              IntervalIntegrable
                (fun s : Real =>
                  modelSpray (I := I) g x (α z1 s))
                MeasureTheory.volume (0 : Real) τ := by
            exact pl_int (hf := hpl) hα1cont
              (fun s => hbound z1 hz1 s) hτmem'
          have hint2 :
              IntervalIntegrable
                (fun s : Real =>
                  modelSpray (I := I) g x (α z2 s))
                MeasureTheory.volume (0 : Real) τ := by
            exact pl_int (hf := hpl) hα2cont
              (fun s => hbound z2 hz2 s) hτmem'
          have hmodel_fst :
              ((∫ s in (0 : Real)..τ,
                  modelSpray (I := I) g x (α z1 s)).1 -
                (∫ s in (0 : Real)..τ,
                  modelSpray (I := I) g x (α z2 s)).1) =
                ∫ s in (0 : Real)..τ, (α z1 s - α z2 s).2 := by
            have hsubint :
                ((∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z1 s)).1 -
                  (∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z2 s)).1) =
                  ∫ s in (0 : Real)..τ,
                    (modelSpray (I := I) g x (α z1 s) -
                      modelSpray (I := I) g x (α z2 s)).1 := by
              exact fst_int_sub hint1 hint2
            rw [hsubint]
            apply intervalIntegral.integral_congr
            intro s hs
            have hsE : s ∈ Set.Icc (-ε) ε := huIcc0τ hs
            have hpair1 := modelSpray_eq_pair (I := I) g x
              (z := α z1 s) (hsrcFlow z1 hz1 s hsE).1 (hsrcFlow z1 hz1 s hsE).2
            have hpair2 := modelSpray_eq_pair (I := I) g x
              (z := α z2 s) (hsrcFlow z2 hz2 s hsE).1 (hsrcFlow z2 hz2 s hsE).2
            change
              (modelSpray (I := I) g x (α z1 s) -
                modelSpray (I := I) g x (α z2 s)).1 =
                (α z1 s - α z2 s).2
            rw [hpair1, hpair2]
            rfl
          have hα1contτ : ContinuousOn (α z1) (Set.uIcc (0 : Real) τ) :=
            hα1cont.mono huIcc0τ'
          have hα2contτ : ContinuousOn (α z2) (Set.uIcc (0 : Real) τ) :=
            hα2cont.mono huIcc0τ'
          let vel : Real -> E := fun s => (α z1 s - α z2 s).2
          let inner : Real -> E := fun t => ∫ s in (0 : Real)..t, (res p s).2
          have hvelCont :
              ContinuousOn vel (Set.uIcc (0 : Real) τ) :=
            (hα1contτ.sub hα2contτ).snd
          let c0 : E := (z1 - z2).2
          have hvelInt :
              IntervalIntegrable vel MeasureTheory.volume (0 : Real) τ :=
            hvelCont.intervalIntegrable
          have hconstInt :
              IntervalIntegrable
                (fun _ : Real => c0)
                MeasureTheory.volume (0 : Real) τ :=
            const_int (E := E) τ c0
          have hvel_to_res :=
            int_sub_const (E := E)
              (f := vel) (h := inner)
              (τ := τ) (c := c0) hvelInt hconstInt
              (by
                intro t ht
                have htIcc : t ∈ Set.Icc (0 : Real) τ := by
                  rw [Set.uIcc_of_le hτ.le] at ht
                  exact ht
                have hvelf := hpvel t htIcc
                change vel t = c0 + inner t
                change (α z1 t - α z2 t).2 =
                  (z1 - z2).2 + ∫ s in (0 : Real)..t, (res p s).2
                simpa [z1, z2] using hvelf)
          calc
            chartEnd (I := I) α τ x p.1 -
                chartEnd (I := I) α τ x p.2 -
                τ • (initPhase (I := I) x (τ⁻¹ • p.1) -
                  initPhase (I := I) x (τ⁻¹ • p.2)).2
                =
              ((z1.1 +
                  (∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z1 s)).1) -
                (z2.1 +
                  (∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z2 s)).1) -
                τ • c0) := by
              rw [hchart1, hchart2]
            _ =
              (((∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z1 s)).1 -
                  (∫ s in (0 : Real)..τ,
                    modelSpray (I := I) g x (α z2 s)).1) -
                τ • c0) := by
              rw [hfst_eq]
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            _ =
              (∫ s in (0 : Real)..τ, (α z1 s - α z2 s).2) -
                τ • c0 := by
              rw [hmodel_fst]
            _ = ∫ t in (0 : Real)..τ,
                  ∫ s in (0 : Real)..t, (res p s).2 := hvel_to_res
        have hE :
            (fun p : TangentSpace I x × TangentSpace I x =>
              chartEnd (I := I) α τ x p.1 -
                chartEnd (I := I) α τ x p.2 -
                τ • (initPhase (I := I) x (τ⁻¹ • p.1) -
                  initPhase (I := I) x (τ⁻¹ • p.2)).2)
              =o[𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x)]
                fun p => p.1 - p.2 :=
          hdouble_int.congr' hendpoint.symm Filter.EventuallyEq.rfl
        have hlin (p : TangentSpace I x × TangentSpace I x) :
            τ • ((initPhase (I := I) x (τ⁻¹ • p.1)).2 -
              (initPhase (I := I) x (τ⁻¹ • p.2)).2) =
              (ContinuousLinearMap.id Real (TangentSpace I x)) p.1 -
                (ContinuousLinearMap.id Real (TangentSpace I x)) p.2 := by
          have hsnd1 :
              (initPhase (I := I) x (τ⁻¹ • p.1)).2 = τ⁻¹ • p.1 := by
            simpa using congrArg Prod.snd
              (initPhase_eq_pair (I := I) x (τ⁻¹ • p.1))
          have hsnd2 :
              (initPhase (I := I) x (τ⁻¹ • p.2)).2 = τ⁻¹ • p.2 := by
            simpa using congrArg Prod.snd
              (initPhase_eq_pair (I := I) x (τ⁻¹ • p.2))
          calc
            τ • ((initPhase (I := I) x (τ⁻¹ • p.1)).2 -
                (initPhase (I := I) x (τ⁻¹ • p.2)).2)
                = τ • (τ⁻¹ • p.1 - τ⁻¹ • p.2) := by
              rw [hsnd1, hsnd2]
              rfl
            _ = p.1 - p.2 := by
              rw [smul_sub, smul_smul, smul_smul,
                mul_inv_cancel₀ hτ.ne', one_smul, one_smul]
            _ = (ContinuousLinearMap.id Real (TangentSpace I x)) p.1 -
                (ContinuousLinearMap.id Real (TangentSpace I x)) p.2 := by
              rfl
        simpa [hlin] using hE
      have hEq :
          chartEnd (I := I) α τ x =ᶠ[𝓝 (0 : TangentSpace I x)]
            fun v : TangentSpace I x =>
              extChartAt I x (manifoldEnd (I := I) α τ x v) :=
        chartEnd_eventually_eq (I := I) (α := α) (ε := ε) (τ := τ)
          (ρ := ρ) (rModel := rModel) x hτ hρ hsmall hsrcFlow hτmem
      exact hchartStrict.congr_of_eventuallyEq hEq
    simpa using hstrict

/-! ## What the current spray package proves -/

/-- The Picard-Lindelof spray producer gives a coordinate-defined geodesic
equation at the initial time. -/
theorem exists_coordGeoAt
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsCoordGeodesicOn (I := I) g x gamma ({0} : Set Real) := by
  obtain ⟨gamma, hgamma0, hvel, _hspray, _hode, hacc⟩ :=
    exists_local_geodesic_coordZero (I := I) g x v
  refine ⟨gamma, hgamma0, hvel, ?_⟩
  constructor
  · intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa [hgamma0] using coordinateFrameAt_mem (I := I) x
  · intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa using hacc

/-- The relation-valued endpoint exists at time `0`, by the local spray
producer and the checked initial-time coordinate acceleration theorem. -/
theorem coordExp_zero
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    CoordExpRelAtTime (I := I) g x v 0 x := by
  obtain ⟨gamma, hgamma0, hvel, hgeo⟩ :=
    exists_coordGeoAt (I := I) g x v
  refine ⟨({0} : Set Real), ?_, gamma, ?_, ?_⟩
  · intro t ht
    simpa using ht
  · exact ⟨hgamma0, hvel, hgeo⟩
  · simp [hgamma0]

/-- Local coordinate-geodesic existence on a genuine time ball.

The proof uses the chart-fixed spray IVP, shrinks the time ball so the base
projection remains in the original `extChartAt x` chart, and then applies the
fixed-chart scalar ODE bridge from `SprayChartPush.lean` at each time. -/
theorem exists_coordGeoOn
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ epsilon > 0, ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsCoordGeodesicOn (I := I) g x gamma
          (Metric.ball (0 : Real) epsilon) := by
  classical
  obtain ⟨G, -⟩ := exists_localGeodesicIVPAt_leviCivita (I := I) g x v
  let gamma : Curve M := projectCurve (I := I) G.lift
  have hballG : Metric.ball (0 : Real) G.epsilon ∈ 𝓝 (0 : Real) :=
    Metric.ball_mem_nhds _ G.epsilon_pos
  have hf0 : IsMIntegralCurveAt G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x) 0 :=
    G.spray_integral.isMIntegralCurveAt hballG
  have hproj_cont :
      ContinuousAt (fun t : Real => (G.lift t).proj) 0 := by
    exact (FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt.comp hf0.continuousAt
  have hsrc_nhds :
      (extChartAtCoordinateData (I := I) x).domain ∈
        𝓝 ((G.lift 0).proj) := by
    simpa [G.lift_initial, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using
      extChartAt_source_mem_nhds (I := I) x
  have hsrc_event :
      ∀ᶠ t in 𝓝 (0 : Real),
        (G.lift t).proj ∈
          (extChartAtCoordinateData (I := I) x).domain :=
    hproj_cont.preimage_mem_nhds hsrc_nhds
  have hgood :
      Metric.ball (0 : Real) G.epsilon ∩
          {t : Real | (G.lift t).proj ∈
            (extChartAtCoordinateData (I := I) x).domain} ∈
        𝓝 (0 : Real) :=
    Filter.inter_mem hballG hsrc_event
  rw [Metric.mem_nhds_iff] at hgood
  obtain ⟨epsilon, hepsilon, hepsilon_sub⟩ := hgood
  have hsubsetG :
      Metric.ball (0 : Real) epsilon ⊆
        Metric.ball (0 : Real) G.epsilon := by
    intro t ht
    exact (hepsilon_sub ht).1
  have hf_small : IsMIntegralCurveOn G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) epsilon) :=
    G.spray_integral.mono hsubsetG
  have hsrc_small :
      ∀ t ∈ Metric.ball (0 : Real) epsilon,
        projectCurve (I := I) G.lift t ∈
          (extChartAtCoordinateData (I := I) x).domain := by
    intro t ht
    simpa [projectCurve] using (hepsilon_sub ht).2
  refine ⟨epsilon, hepsilon, gamma, ?_, ?_, ?_⟩
  · simpa [gamma] using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) G.lift_initial
  · simpa [gamma] using
      projectCurve_initialVelocity_of_geodesicSprayIntegral
        (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
        (f := G.lift) G.lift_initial hf0
  · constructor
    · exact hsrc_small
    · intro t ht
      have hode :=
        coordSprayODEOn (I := I) (g := g) (x := x) (v := v)
          (lift := G.lift) (epsilon := epsilon) (t := t)
          G.lift_initial hf_small ht hsrc_small
      exact hode.zeroAccel

/-- Local relation-valued endpoint existence for small times, produced by the
checked local coordinate-geodesic segment theorem. -/
theorem exists_coordExpTime
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ epsilon > 0, ∀ tau ∈ Metric.ball (0 : Real) epsilon,
      ∃ y : M, CoordExpRelAtTime (I := I) g x v tau y := by
  obtain ⟨epsilon, hepsilon, gamma, hgamma0, hvel, hgeo⟩ :=
    exists_coordGeoOn (I := I) g x v
  refine ⟨epsilon, hepsilon, ?_⟩
  intro tau htau
  refine ⟨gamma tau, Metric.ball (0 : Real) epsilon, ?_,
    gamma, ?_, rfl⟩
  · intro s hs
    rw [Metric.mem_ball]
    have hdist : dist (0 : Real) s ≤ dist (0 : Real) tau :=
      Real.dist_left_le_of_mem_uIcc hs
    have htau' : dist (0 : Real) tau < epsilon := by
      simpa [Metric.mem_ball, dist_comm] using htau
    have hdist' : dist s (0 : Real) ≤ dist (0 : Real) tau := by
      simpa [dist_comm] using hdist
    exact hdist'.trans_lt htau'
  · exact ⟨hgamma0, hvel, hgeo⟩

/-! ## Future normal-coordinate package -/

/-- Data that would make the relation-valued endpoint into a normal-coordinate
chart around `x`.

This is a package of future facts, not an existence theorem.  The field
`exp_realizes` keeps the map tied to the relation-valued endpoint above, while
`source_inj` and `target_open` record the local chart facts that should follow
from smooth dependence of the geodesic flow and the inverse function theorem. -/
structure NormalCoordinateData
    (g : SmoothRiemannianMetric I M) (x : M) where
  radius : Real
  radius_pos : 0 < radius
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  exp_realizes :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        CoordExpRel (I := I) g x v (exp v)
  source_inj :
    Set.InjOn exp (Metric.ball (0 : TangentSpace I x) radius)
  target_open :
    IsOpen (exp '' Metric.ball (0 : TangentSpace I x) radius)

/-- Existence of the current normal-coordinate package.

This uses the functional endpoint from `expAt_strict` and the inverse function
theorem for its chart expression.  The endpoint relation itself supplies chart
source control through `expAt_mem_source`, so the open image statement can be
pulled back from the tangent-coordinate local homeomorphism. -/
theorem exists_normalData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalCoordinateData (I := I) g x) := by
  classical
  obtain ⟨r0, hr0, exp, hexp0, hreal, hstrict⟩ :=
    expAt_strict (I := I) g x
  let chartExp : TangentSpace I x -> TangentSpace I x :=
    fun v => extChartAt I x (exp v)
  let eIso : TangentSpace I x ≃L[Real] TangentSpace I x :=
    ContinuousLinearEquiv.refl Real (TangentSpace I x)
  have hstrictIso :
      HasStrictFDerivAt chartExp (eIso : TangentSpace I x →L[Real] TangentSpace I x)
        (0 : TangentSpace I x) := by
    simpa [chartExp, eIso] using hstrict
  let eIFT := hstrictIso.toOpenPartialHomeomorph chartExp
  have hIFTsrc : (0 : TangentSpace I x) ∈ eIFT.source := by
    simpa [eIFT] using hstrictIso.mem_toOpenPartialHomeomorph_source
  have hgood :
      Metric.ball (0 : TangentSpace I x) r0 ∩ eIFT.source ∈
        𝓝 (0 : TangentSpace I x) :=
    Filter.inter_mem (Metric.ball_mem_nhds _ hr0)
      (eIFT.open_source.mem_nhds hIFTsrc)
  rw [Metric.mem_nhds_iff] at hgood
  obtain ⟨r, hr, hrsub⟩ := hgood
  let B : Set (TangentSpace I x) := Metric.ball (0 : TangentSpace I x) r
  have hBsub_r0 : B ⊆ Metric.ball (0 : TangentSpace I x) r0 := by
    intro v hv
    exact (hrsub hv).1
  have hBsub_eIFT : B ⊆ eIFT.source := by
    intro v hv
    exact (hrsub hv).2
  have hsrc_exp : ∀ v ∈ B, exp v ∈ (extChartAt I x).source := by
    intro v hv
    have hv0 : v ∈ Metric.ball (0 : TangentSpace I x) r0 := hBsub_r0 hv
    have hcoord : exp v ∈ coordinateFrameSet (I := I) x :=
      expAt_mem_source (I := I) (hreal v hv0)
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hcoord
  have hchartOpen : IsOpen (chartExp '' B) := by
    simpa [eIFT, chartExp] using
      eIFT.isOpen_image_of_subset_source (Metric.isOpen_ball) hBsub_eIFT
  have htargetOpen : IsOpen (exp '' B) := by
    have hpreOpen :
        IsOpen ((extChartAt I x).source ∩
          (extChartAt I x) ⁻¹' (chartExp '' B)) := by
      rw [extChartAt]
      exact (chartAt H x).isOpen_extend_preimage' (I := I) hchartOpen
    have himage :
        exp '' B =
          (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' (chartExp '' B) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨hsrc_exp v hv, v, hv, rfl⟩
      · rintro ⟨hy_src, v, hv, h_eq⟩
        refine ⟨v, hv, ?_⟩
        apply (extChartAt I x).injOn (hsrc_exp v hv) hy_src
        simpa [chartExp] using h_eq
    simpa [B, himage] using hpreOpen
  refine ⟨{
    radius := r
    radius_pos := hr
    exp := exp
    exp_zero := hexp0
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }⟩
  · intro v hv
    exact hreal v (hBsub_r0 (by simpa [B] using hv))
  · intro v hv w hw h_eq
    have hvB : v ∈ B := by simpa [B] using hv
    have hwB : w ∈ B := by simpa [B] using hw
    apply eIFT.injOn (hBsub_eIFT hvB) (hBsub_eIFT hwB)
    change chartExp v = chartExp w
    exact congrArg (fun y : M => extChartAt I x y) h_eq
  · simpa [B] using htargetOpen

end Coordinates
end RicciFlower
