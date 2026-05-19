import RicciFlower.Coordinates.MetricCompatibility
import RicciFlower.Coordinates.Normal

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Foundations for the Gauss lemma

This file starts the Gauss-lemma layer from the checked coordinate normal
coordinate API.  It deliberately does not state the full differential-of-exp
orthogonality theorem yet: the current `NormalCoordinateData` exposes local
endpoint data, injectivity, and open image, but not the smooth local inverse or
variation-field API needed for the usual Gauss lemma.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open scoped BigOperators Manifold ContDiff Topology
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-! ## Radial coordinate geodesics -/

/-- A radial coordinate geodesic segment from `(x, v)`, normalized on the
time interval `uIcc 0 1`. -/
def IsRadialCoordGeodesic
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (gamma : Curve M) : Prop :=
  IsCoordGeodesicSegment (I := I) g x v gamma (Set.uIcc 0 1)

/-- Relation-valued radial endpoint at time `t`. -/
def CoordRadialEndpoint
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (t : Real) (y : M) : Prop :=
  CoordExpRelAtTime (I := I) g x v t y

@[simp] theorem coordRadialEndpoint_one_iff
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (y : M) :
    CoordRadialEndpoint (I := I) g x v 1 y ↔ expAt (I := I) g x v y :=
  Iff.rfl

/-- Constant curves have zero coordinate-defined covariant acceleration.

This public version is the small reusable producer needed for radial zero
velocity. -/
theorem coordAccelConst
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

/-- The zero initial velocity radial geodesic is the constant curve. -/
theorem radialZeroConst
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsRadialCoordGeodesic (I := I) g x (0 : TangentSpace I x)
      (fun _ : Real => x) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [zeroInitialVelocity]
  · constructor
    · intro t _ht
      exact coordinateFrameAt_mem (I := I) x
    · intro t _ht
      exact coordAccelConst (I := I) x x t
        (coordinateFrameAt_mem (I := I) x)

/-- A radial coordinate geodesic gives relation-valued radial endpoints at all
times in its normalized interval. -/
theorem radialEndpoint_of_radial
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x} {gamma : Curve M}
    (hgamma : IsRadialCoordGeodesic (I := I) g x v gamma)
    {t : Real} (ht : t ∈ Set.uIcc (0 : Real) 1) :
    CoordRadialEndpoint (I := I) g x v t (gamma t) := by
  refine ⟨Set.uIcc (0 : Real) 1, ?_, gamma, hgamma, rfl⟩
  exact Set.uIcc_subset_uIcc Set.left_mem_uIcc ht

/-- Restrict a coordinate geodesic segment on a larger time set to the
normalized radial interval. -/
theorem radial_of_segment
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x} {gamma : Curve M} {s : Set Real}
    (hs : Set.uIcc (0 : Real) 1 ⊆ s)
    (hseg : IsCoordGeodesicSegment (I := I) g x v gamma s) :
    IsRadialCoordGeodesic (I := I) g x v gamma := by
  rcases hseg with ⟨h0, hvel, hgeo⟩
  refine ⟨h0, hvel, ?_⟩
  constructor
  · intro t ht
    exact hgeo.1 t (hs ht)
  · intro t ht
    exact hgeo.2 t (hs ht)

namespace SprayRadialSegment

/-- A spray-backed segment projects to the older coordinate radial-geodesic
predicate, forgetting the tangent-bundle lift witness. -/
theorem radial
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v) :
    IsRadialCoordGeodesic (I := I) g x v G.gamma :=
  radial_of_segment (I := I) G.interval_subset G.segment

/-- A spray-backed segment gives relation-valued radial endpoints on the
normalized interval. -/
theorem endpoint
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    (G : SprayRadialSegment (I := I) g x v)
    {t : Real} (ht : t ∈ Set.uIcc (0 : Real) 1) :
    CoordRadialEndpoint (I := I) g x v t (G.gamma t) :=
  radialEndpoint_of_radial (I := I) G.radial ht

end SprayRadialSegment

/-- A time-one relation-valued endpoint contains a normalized radial
coordinate geodesic witness. -/
theorem exists_radial_of_expAt
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x} {y : M}
    (h : expAt (I := I) g x v y) :
    ∃ gamma : Curve M,
      IsRadialCoordGeodesic (I := I) g x v gamma ∧ gamma 1 = y := by
  rcases h with ⟨s, hs, gamma, hseg, hy⟩
  exact ⟨gamma, radial_of_segment (I := I) hs hseg, hy⟩

/-- Local existence of normalized radial coordinate geodesics near zero
velocity. -/
theorem exists_radial
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ r > 0, ∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
      ∃ gamma : Curve M, IsRadialCoordGeodesic (I := I) g x v gamma := by
  obtain ⟨r, hr, hSeg⟩ := exists_sprayRadial (I := I) g x
  refine ⟨r, hr, ?_⟩
  intro v hv
  rcases hSeg v hv with ⟨G⟩
  exact ⟨G.gamma, G.radial⟩

/-- Local relation-valued radial endpoints at all times `t ∈ [0,1]`, for all
small initial velocities. -/
theorem exists_radialEndpoint
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ r > 0, ∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
      ∀ t ∈ Set.uIcc (0 : Real) 1,
        ∃ y : M, CoordRadialEndpoint (I := I) g x v t y := by
  obtain ⟨r, hr, hSeg⟩ := exists_sprayRadial (I := I) g x
  refine ⟨r, hr, ?_⟩
  intro v hv t ht
  rcases hSeg v hv with ⟨G⟩
  exact ⟨G.gamma t, G.endpoint ht⟩

namespace NormalCoordinateData

/-- A normal-coordinate datum supplies a normalized radial coordinate geodesic
witness for each tangent vector in its source ball. -/
theorem exists_radial
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalCoordinateData (I := I) g x)
    {v : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) N.radius) :
    ∃ gamma : Curve M,
      IsRadialCoordGeodesic (I := I) g x v gamma ∧ gamma 1 = N.exp v :=
  exists_radial_of_expAt (I := I) (N.exp_realizes v hv)

/-- A normal-coordinate datum gives relation-valued radial endpoints along the
radial geodesic for each tangent vector in its source ball. -/
theorem exists_endpoint
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalCoordinateData (I := I) g x)
    {v : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) N.radius)
    {t : Real} (ht : t ∈ Set.uIcc (0 : Real) 1) :
    ∃ y : M, CoordRadialEndpoint (I := I) g x v t y := by
  rcases N.exists_radial (I := I) hv with ⟨gamma, hgamma, _hy⟩
  exact ⟨gamma t, radialEndpoint_of_radial (I := I) hgamma ht⟩

end NormalCoordinateData

/-! ## Speed and energy foundations -/

/-- Squared speed, re-exported in the coordinate normal-coordinate layer. -/
def coordSpeedSq (g : SmoothRiemannianMetric I M) (gamma : Curve M) (t : Real) :
    Real :=
  speedSq (I := I) g gamma t

@[simp] theorem coordSpeedSq_eq_speedSq
    (g : SmoothRiemannianMetric I M) (gamma : Curve M) (t : Real) :
    coordSpeedSq (I := I) g gamma t = speedSq (I := I) g gamma t :=
  rfl

/-- Squared speed expanded in the fixed `extChartAt x₀` coordinate frame.

This is the algebraic input for the later speed-constancy proof: after
differentiating this finite sum, metric compatibility supplies the derivative
of the metric components and the spray ODE supplies the derivatives of the
velocity components. -/
theorem coordSpeedSq_eq_sum
    (g : SmoothRiemannianMetric I M)
    (x0 : M) {gamma : Curve M} {t : Real}
    (hsrc : gamma t ∈ coordinateFrameSet (I := I) x0) :
    coordSpeedSq (I := I) g gamma t =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          (extChartAtCoordinateData (I := I) x0).velocityCoeff gamma i t *
            (extChartAtCoordinateData (I := I) x0).velocityCoeff gamma j t *
              metricCompForMetricInFrame (I := I) g
                (coordinateFrameAt (I := I) x0) (gamma t) i j := by
  classical
  let C : CoordinateChartData (I := I) (M := M) :=
    extChartAtCoordinateData (I := I) x0
  let V : TangentSpace I (gamma t) := curveVelocity I gamma t
  have hsrcC : gamma t ∈ C.domain := by
    simpa [C] using hsrc
  have hV :
      V = ∑ i : CoordinateIdx (𝕜 := Real) E,
        C.coeff i V • C.frame i (gamma t) := by
    have hcoeff :
        ∀ i : CoordinateIdx (𝕜 := Real) E,
          C.coeff i V = (C.hframe.toBasisAt hsrcC).repr V i := by
      intro i
      simp [C, CoordinateChartData.coeff, IsLocalFrameOn.coeff, hsrc]
    calc
      V = ∑ i : CoordinateIdx (𝕜 := Real) E,
          (C.hframe.toBasisAt hsrcC).repr V i • C.frame i (gamma t) := by
            simpa [C, IsLocalFrameOn.toBasisAt_coe] using
              ((C.hframe.toBasisAt hsrcC).sum_repr V).symm
      _ = ∑ i : CoordinateIdx (𝕜 := Real) E,
          C.coeff i V • C.frame i (gamma t) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hcoeff i]
  calc
    coordSpeedSq (I := I) g gamma t = g.inner (gamma t) V V := rfl
    _ = g.inner (gamma t)
        (∑ i : CoordinateIdx (𝕜 := Real) E, C.coeff i V • C.frame i (gamma t))
        (∑ j : CoordinateIdx (𝕜 := Real) E, C.coeff j V • C.frame j (gamma t)) := by
          conv_lhs =>
            rw [hV]
    _ = ∑ j : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          C.coeff j V *
            (C.coeff i V *
              g.inner (gamma t) (C.frame i (gamma t)) (C.frame j (gamma t))) := by
          simp [Finset.mul_sum]
    _ = ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          C.coeff i V * C.coeff j V *
            metricCompForMetricInFrame (I := I) g C.frame (gamma t) i j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [metricCompForMetricInFrame]
          ring
    _ = ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          (extChartAtCoordinateData (I := I) x0).velocityCoeff gamma i t *
            (extChartAtCoordinateData (I := I) x0).velocityCoeff gamma j t *
              metricCompForMetricInFrame (I := I) g
                (coordinateFrameAt (I := I) x0) (gamma t) i j := by
          simp [C, V, CoordinateChartData.velocityCoeff]

/-- Metric compatibility gives the time derivative of coordinate-frame metric
components along a differentiable curve. -/
theorem metricDerivAlong
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (x0 : M) {gamma : Curve M} {t : Real}
    (hsrc : gamma t ∈ coordinateFrameSet (I := I) x0)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (a b : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun s : Real =>
        metricCompForMetricInFrame (I := I) g
          (coordinateFrameAt (I := I) x0) (gamma s) a b)
      ((∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelAlongInFrame cov
            (coordinateFrameAt (I := I) x0)
            (coordinateFrameAt_isLocalFrame_one (I := I) x0)
            (gamma t) (curveVelocity I gamma t) a p *
              metricCompForMetricInFrame (I := I) g
                (coordinateFrameAt (I := I) x0) (gamma t) p b) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelAlongInFrame cov
            (coordinateFrameAt (I := I) x0)
            (coordinateFrameAt_isLocalFrame_one (I := I) x0)
            (gamma t) (curveVelocity I gamma t) b p *
              metricCompForMetricInFrame (I := I) g
                (coordinateFrameAt (I := I) x0) (gamma t) a p))
      t := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hf : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      (gamma t) := by
    exact metricComp_mdiffAt (I := I) g frame hframe
      (coordinateFrameSet_open (I := I) x0) hsrc a b
  have hderiv :
      HasDerivAt
        (fun s : Real =>
          metricCompForMetricInFrame (I := I) g frame (gamma s) a b)
        (extDerivFun (I := I)
          (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
          (gamma t) (curveVelocity I gamma t)) t :=
    extDerivFun_along_curve_eq_deriv (I := I) hf hgamma
  have hformula :=
    metricComp_extDeriv_tangent
      (I := I) g cov hmc frame hframe
      (coordinateFrameSet_open (I := I) x0) hsrc
      (curveVelocity I gamma t) a b
  rw [hformula] at hderiv
  simpa [frame, hframe] using hderiv

/-- Frontier for the Gauss lemma: coordinate-defined geodesics should have
constant squared speed.

The missing bridge is not the radial endpoint layer.  It is the analytic/local
calculus statement converting `HasCoordCovAccelAt ... 0` into the usual
metric-compatible derivative identity for
`t ↦ g.inner (gamma t) (gamma' t) (gamma' t)`. -/
theorem coordGeodesic_speedSq_const
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {x : M} {v : TangentSpace I x} {gamma : Curve M}
    (_hgamma : IsRadialCoordGeodesic (I := I) g x v gamma) :
    ∃ c : Real,
      ∀ t ∈ Set.uIcc (0 : Real) 1,
        coordSpeedSq (I := I) g gamma t = c := by
  sorry

/-!
Future Gauss-lemma target:

```
theorem gaussLemma_frontier
    (N : NormalCoordinateData (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) N.radius)
    -- `w` tangent to the normal-coordinate sphere through `v`
    :
    -- g.inner (N.exp v) ((mfderiv ... N.exp v) v) ((mfderiv ... N.exp v) w)
    --   = g.inner x v w
```

This needs either a smooth local inverse/differential API for `N.exp` away from
zero or a geodesic-variation/Jacobi-field layer.
-/

end Coordinates
end RicciFlower
