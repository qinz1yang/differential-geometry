import RicciFlower.GlobalGeometry.Lecture07.GeodesicSpray

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: chart-pushed geodesic spray

This file records the first chart-pushed form of the spray-integral geodesic
equation.  A lift `f : ℝ -> TM` solving the chart-fixed spray is pushed through
the tangent-bundle chart at `f t0`, giving an `E × E`-valued first-order ODE.

This is deliberately weaker than the later scalar second-order geodesic ODE:
we do not yet extract the two components `x' = v` and `v' = -Γ(v,v)`, and we
do not connect this layer to the covariant-acceleration predicates in
`CoordinateEquation.lean`.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle Filter
open scoped Manifold ContDiff Topology
open RicciFlower.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## Chart-pushed phase-space ODE -/

private theorem hasDerivAt_fst_of_prod
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).1) F'.1 t := by
  have hfst : HasFDerivAt (ContinuousLinearMap.fst Real E E)
      (ContinuousLinearMap.fst Real E E) (F t) :=
    (ContinuousLinearMap.fst Real E E).hasFDerivAt
  simpa [Function.comp_def] using hfst.comp_hasDerivAt t hF

private theorem hasDerivAt_snd_of_prod
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).2) F'.2 t := by
  have hsnd : HasFDerivAt (ContinuousLinearMap.snd Real E E)
      (ContinuousLinearMap.snd Real E E) (F t) :=
    (ContinuousLinearMap.snd Real E E).hasFDerivAt
  simpa [Function.comp_def] using hsnd.comp_hasDerivAt t hF

private theorem hasDerivAt_modelCoord_of_vector
    {F : Real -> E} {F' : E} {t : Real}
    (k : CoordinateIdx (𝕜 := Real) E)
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => modelCoord k (F s))
      (modelCoord k F') t := by
  let coord : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hcoord : HasFDerivAt coord coord (F t) := coord.hasFDerivAt
  simpa [Function.comp_def, coord, modelCoord] using
    hcoord.comp_hasDerivAt t hF

/-- The tangent-bundle lift pushed into the chart of `TM` centered at `lift t0`.

This is the phase-space curve whose coordinates are later expected to be
`(x(t), v(t))`. -/
def chartPushLift (lift : Real -> TangentBundle I M) (t0 : Real) :
    Real -> E × E :=
  fun t => extChartAt I.tangent (lift t0) (lift t)

@[simp] theorem chartPushLift_apply
    (lift : Real -> TangentBundle I M) (t0 t : Real) :
    chartPushLift (I := I) lift t0 t =
      extChartAt I.tangent (lift t0) (lift t) :=
  rfl

/-- The second component of the tangent-bundle chart centered over `x` is the
fixed-chart fiber coordinate over `x`. -/
theorem chartPushLift_snd_eq_chartFiberCoordAt
    {x : M} {v0 : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift0 : lift t0 = (⟨x, v0⟩ : TangentBundle I M))
    {t : Real} (_hsrc : (lift t).proj ∈ (extChartAt I x).source) :
    (chartPushLift (I := I) lift t0 t).2 =
      chartFiberCoordAt (I := I) x (lift t) := by
  rcases hq : lift t with ⟨y, w⟩
  simp [chartPushLift, hlift0, hq, chartFiberCoordAt,
    coordinateTrivializationAt, TangentBundle.chartAt,
    TangentBundle.trivializationAt_apply, extChartAt]

/-- The chart-pushed right-hand side of the fixed-chart Levi-Civita spray.

Mathlib's integral-curve API expresses the derivative in the chart at the base
time by transporting the vector field value with `tangentCoordChange`. -/
def chartPushVF
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (lift : Real -> TangentBundle I M) (t0 t : Real) : E × E :=
  tangentCoordChange I.tangent (lift t) (lift t0) (lift t)
    (leviCivitaGeodesicSprayChart (I := I) g x0 (lift t))

@[simp] theorem chartPushVF_apply
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (lift : Real -> TangentBundle I M) (t0 t : Real) :
    chartPushVF (I := I) g x0 lift t0 t =
      tangentCoordChange I.tangent (lift t) (lift t0) (lift t)
        (leviCivitaGeodesicSprayChart (I := I) g x0 (lift t)) :=
  rfl

/-- A spray integral curve becomes a first-order ODE in tangent-bundle chart
coordinates near the base time. -/
theorem chartPushLift_eventually_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x0 : M} {t0 : Real}
    {lift : Real -> TangentBundle I M}
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0) :
    ∀ᶠ t in 𝓝 t0,
      HasDerivAt (chartPushLift (I := I) lift t0)
        (chartPushVF (I := I) g x0 lift t0 t) t := by
  have h := hf.eventually_hasDerivAt
  filter_upwards [h] with t ht
  exact ht

/-- At the base time, the chart-pushed right-hand side is just the spray vector
field value, since the tangent coordinate change is the identity. -/
theorem chartPushVF_self
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (lift : Real -> TangentBundle I M) (t0 : Real) :
    chartPushVF (I := I) g x0 lift t0 t0 =
      leviCivitaGeodesicSprayChart (I := I) g x0 (lift t0) := by
  have hsrc : lift t0 ∈ (extChartAt I.tangent (lift t0)).source :=
    mem_extChartAt_source (I := I.tangent) (lift t0)
  simpa [chartPushVF] using
    tangentCoordChange_self (I := I.tangent)
      (x := lift t0) (z := lift t0)
      (v := leviCivitaGeodesicSprayChart (I := I) g x0 (lift t0)) hsrc

/-- When the tangent-bundle point lies over the fixed chart center, the spray
vector field has the same coordinates as its defining chart-fiber RHS. -/
theorem leviCivitaGeodesicSprayChart_eq_chartFiber_sameBase
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    leviCivitaGeodesicSprayChart (I := I) g x
        (⟨x, v⟩ : TangentBundle I M) =
      leviCivitaGeodesicSprayChartFiber (I := I) g x
        (⟨x, v⟩ : TangentBundle I M) := by
  classical
  let q : TangentBundle I M := ⟨x, v⟩
  let q0 : TangentBundle I M := ⟨x, (0 : E)⟩
  let e := trivializationAt (E × E) (TangentSpace I.tangent) q0
  have hq_source : q ∈ (chartAt (ModelProd H E) q0).source := by
    simp [q, q0]
  have hchart :
      chartAt (ModelProd H E) q =
        chartAt (ModelProd H E) q0 := by
    rw [TangentBundle.chartAt, TangentBundle.chartAt]
  have hExt :
      extChartAt I.tangent q0 =
        extChartAt I.tangent q := by
    simp [extChartAt, hchart]
  have hsymm :
      e.symmL Real q =
        ContinuousLinearMap.id Real (TangentSpace I.tangent q) := by
    rw [TangentBundle.symmL_trivializationAt
      (I := I.tangent) (𝕜 := Real) hq_source]
    rw [hExt]
    simpa [q] using
      (mfderivWithin_range_extChartAt_symm
        (I := I.tangent) (x := q))
  change
    e.symm q (leviCivitaGeodesicSprayChartFiber (I := I) g x q) =
      leviCivitaGeodesicSprayChartFiber (I := I) g x q
  rw [← e.symmL_apply Real, hsymm]
  rfl

/-- If the lift starts at `⟨x, v⟩`, the base-time chart-pushed right-hand side
is the fixed-chart spray fiber expression. -/
theorem chartPushVF_initial_eq_chartFiber
    (g : SmoothRiemannianMetric I M)
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M)) :
    chartPushVF (I := I) g x lift t0 t0 =
      leviCivitaGeodesicSprayChartFiber (I := I) g x
        (⟨x, v⟩ : TangentBundle I M) := by
  rw [chartPushVF_self, hlift]
  exact leviCivitaGeodesicSprayChart_eq_chartFiber_sameBase
    (I := I) g x v

/-- Initial first-component right-hand side: `x' = v`. -/
theorem chartPushVF_initial_fst
    (g : SmoothRiemannianMetric I M)
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M)) :
    (chartPushVF (I := I) g x lift t0 t0).1 = v := by
  rw [chartPushVF_initial_eq_chartFiber (I := I) g hlift]
  change chartFiberCoordAt (I := I) x
      (⟨x, v⟩ : TangentBundle I M) = v
  simpa using
    (chartFiberCoordAt_self (I := I)
      (u := (⟨x, v⟩ : TangentBundle I M)))

/-- Initial second-component right-hand side:
`v' = -Γ(v,v)` in the fixed chart centered at `x`. -/
theorem chartPushVF_initial_snd
    (g : SmoothRiemannianMetric I M)
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M)) :
    (chartPushVF (I := I) g x lift t0 t0).2 =
      leviCivitaGeodesicSprayAcceleration
        (I := I) g x (extChartAt I x x) v := by
  rw [chartPushVF_initial_eq_chartFiber (I := I) g hlift]
  change
    leviCivitaGeodesicSprayAcceleration
        (I := I) g x (extChartAt I x x)
        (chartFiberCoordAt (I := I) x
          (⟨x, v⟩ : TangentBundle I M)) =
      leviCivitaGeodesicSprayAcceleration
        (I := I) g x (extChartAt I x x) v
  rw [chartFiberCoordAt_self (I := I)
    (u := (⟨x, v⟩ : TangentBundle I M))]

/-- Initial scalar second-component right-hand side:
`(v^k)' = - Gamma^k_ij v^i v^j` at the base time. -/
theorem chartPushVF_initial_snd_modelCoord
    (g : SmoothRiemannianMetric I M)
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (k : CoordinateIdx (𝕜 := Real) E) :
    modelCoord k (chartPushVF (I := I) g x lift t0 t0).2 =
      -leviCivitaGeodesicSprayQuadratic
        (I := I) g x (extChartAt I x x) v k := by
  rw [chartPushVF_initial_snd (I := I) g hlift]
  exact modelCoord_leviCivitaGeodesicSprayAcceleration
    (I := I) g x (extChartAt I x x) v k

/-! ## Bridge to the coordinate-geodesic ODE package -/

/-- At the center of the `extChartAt` coordinate package, its frame coefficient
is the fixed model coordinate used by the spray definitions. -/
theorem extChartAtCoordinateData_coeff_eq_modelCoord
    (x : M) (v : TangentSpace I x)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (extChartAtCoordinateData (I := I) x).coeff k v =
      modelCoord k v := by
  change (coordinateFrameAt_isLocalFrame_one (I := I) x).coeff k x v =
    modelCoord k v
  rw [coordinateFrameAt_coeff_eq_toBasis_coord (I := I) x v k]
  rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x]
  rfl

/-- The coordinate-package Christoffel coefficient at the chart center agrees
with the smooth Levi-Civita model RHS used by the spray. -/
theorem extChartAtCoordinateData_christoffel_eq_leviCivitaModelRHS_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    (extChartAtCoordinateData (I := I) x).christoffel
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x i j k =
      LeviCivita.leviCivitaChristoffelModelRHS
        (I := I) g x i j k (extChartAt I x x) := by
  exact (LeviCivita.leviCivitaChristoffelModelRHS_center_eq_christoffel
    (I := I) g x i j k).symm

/-- At the center of the `extChartAt` coordinate package, velocity coefficients
are the fixed model coordinates of the velocity. -/
theorem extChartAtCoordinateData_velocityCoeff_eq_modelCoord
    (gamma : Curve M) (t : Real)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (extChartAtCoordinateData (I := I) (gamma t)).velocityCoeff gamma k t =
      modelCoord k (curveVelocity I gamma t) := by
  change (extChartAtCoordinateData (I := I) (gamma t)).coeff k
      (curveVelocity I gamma t) =
    modelCoord k (curveVelocity I gamma t)
  exact extChartAtCoordinateData_coeff_eq_modelCoord
    (I := I) (gamma t) (curveVelocity I gamma t) k

/-- In a fixed `extChartAt` coordinate package, frame coefficients are exactly
model coordinates of the fixed-chart fiber coordinate. -/
theorem extChartAtCoordinateData_coeff_eq_chartFiberCoordAt_of_mem
    (x : M) {y : M}
    (hy : y ∈ (extChartAtCoordinateData (I := I) x).domain)
    (v : TangentSpace I y)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (extChartAtCoordinateData (I := I) x).coeff k v =
      modelCoord k (chartFiberCoordAt (I := I) x
        (⟨y, v⟩ : TangentBundle I M)) := by
  classical
  let e := coordinateTrivializationAt (I := I) x
  let b := Module.finBasis Real E
  have hybase : y ∈ e.baseSet := by
    simpa [e, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt] using hy
  let σ : (z : M) -> TangentSpace I z :=
    fun z => if h : y = z then h ▸ v else 0
  have hσy : σ y = v := by
    simp [σ]
  have hcoeff := Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
    (𝕜 := Real) (F := E) (V := (TangentSpace I : M -> Type _)) (I := I)
    (e := e) (b := b) hybase σ k
  rw [hσy] at hcoeff
  have hcoeff' :
      e.localFrame_coeff I b k y v =
        modelCoord k (chartFiberCoordAt (I := I) x
          (⟨y, v⟩ : TangentBundle I M)) := by
    rw [hcoeff]
    simp [modelCoord, chartFiberCoordAt, coordinateTrivializationAt, e, b,
      Bundle.Trivialization.basisAt]
  simpa [CoordinateChartData.coeff, extChartAtCoordinateData,
    coordinateFrameAt, coordinateTrivializationAt, e, b] using hcoeff'

/-- If a lift is the tangent lift of `gamma` at `t`, then the coordinate
velocity of `gamma` equals the second chart-pushed fiber coordinate of the
lift. -/
theorem velocityCoeff_eq_chartPushLift_snd_of_velocityBundle
    {x : M} {v0 : TangentSpace I x}
    {gamma : Curve M} {lift : Real -> TangentBundle I M}
    {t0 t : Real}
    (hlift0 : lift t0 = (⟨x, v0⟩ : TangentBundle I M))
    (hvel : curveVelocityBundle I gamma t = lift t)
    (hsrc : gamma t ∈ (extChartAtCoordinateData (I := I) x).domain)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (extChartAtCoordinateData (I := I) x).velocityCoeff gamma k t =
      modelCoord k ((chartPushLift (I := I) lift t0 t).2) := by
  have hproj : gamma t = (lift t).proj := by
    simpa [curveVelocityBundle] using congrArg Bundle.TotalSpace.proj hvel
  have hsrc_lift : (lift t).proj ∈ (extChartAt I x).source := by
    simpa [← hproj, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using hsrc
  rw [chartPushLift_snd_eq_chartFiberCoordAt (I := I) hlift0 hsrc_lift]
  rw [← hvel]
  simpa [CoordinateChartData.velocityCoeff, curveVelocityBundle] using
    extChartAtCoordinateData_coeff_eq_chartFiberCoordAt_of_mem
      (I := I) x hsrc (curveVelocity I gamma t) k

/-- The Christoffel quadratic in the `extChartAt` coordinate-geodesic package
is exactly the spray's scalar quadratic at the chart center. -/
theorem extChartAtCoordinateData_christoffelVelocityQuadratic_eq_leviCivita
    (g : SmoothRiemannianMetric I M) {gamma : Curve M} {t : Real}
    {x : M} (hx : gamma t = x)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (extChartAtCoordinateData (I := I) x).christoffelVelocityQuadratic
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) gamma t k =
      leviCivitaGeodesicSprayQuadratic
        (I := I) g x (extChartAt I x x) (curveVelocity I gamma t) k := by
  subst x
  change
    (∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        (extChartAtCoordinateData (I := I) (gamma t)).christoffel
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) (gamma t) i j k *
          (extChartAtCoordinateData (I := I) (gamma t)).velocityCoeff gamma i t *
          (extChartAtCoordinateData (I := I) (gamma t)).velocityCoeff gamma j t) =
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        LeviCivita.leviCivitaChristoffelModelRHS
          (I := I) g (gamma t) i j k (extChartAt I (gamma t) (gamma t)) *
          modelCoord i (curveVelocity I gamma t) *
          modelCoord j (curveVelocity I gamma t)
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [extChartAtCoordinateData_christoffel_eq_leviCivitaModelRHS_center
      (I := I) g (gamma t) i j k]
  rw [extChartAtCoordinateData_velocityCoeff_eq_modelCoord
      (I := I) gamma t i]
  rw [extChartAtCoordinateData_velocityCoeff_eq_modelCoord
      (I := I) gamma t j]

/-- Pointwise version of the chart-pushed first-order ODE at the base time. -/
theorem chartPushLift_hasDerivAt_self
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x0 : M} {t0 : Real}
    {lift : Real -> TangentBundle I M}
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0) :
    HasDerivAt (chartPushLift (I := I) lift t0)
      (chartPushVF (I := I) g x0 lift t0 t0) t0 :=
  (chartPushLift_eventually_hasDerivAt (I := I) hf).self_of_nhds

/-- The first component of the chart-pushed lift satisfies the first component
of the chart-pushed ODE near the base time. -/
theorem chartPushLift_fst_eventually_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x0 : M} {t0 : Real}
    {lift : Real -> TangentBundle I M}
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0) :
    ∀ᶠ t in 𝓝 t0,
      HasDerivAt (fun s : Real => (chartPushLift (I := I) lift t0 s).1)
        (chartPushVF (I := I) g x0 lift t0 t).1 t := by
  filter_upwards [chartPushLift_eventually_hasDerivAt (I := I) hf] with t ht
  exact hasDerivAt_fst_of_prod ht

/-- The second component of the chart-pushed lift satisfies the second
component of the chart-pushed ODE near the base time. -/
theorem chartPushLift_snd_eventually_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x0 : M} {t0 : Real}
    {lift : Real -> TangentBundle I M}
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0) :
    ∀ᶠ t in 𝓝 t0,
      HasDerivAt (fun s : Real => (chartPushLift (I := I) lift t0 s).2)
        (chartPushVF (I := I) g x0 lift t0 t).2 t := by
  filter_upwards [chartPushLift_eventually_hasDerivAt (I := I) hf] with t ht
  exact hasDerivAt_snd_of_prod ht

/-- Base-time first-component equation for the chart-pushed lift. -/
theorem chartPushLift_fst_hasDerivAt_self
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x0 : M} {t0 : Real}
    {lift : Real -> TangentBundle I M}
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0) :
    HasDerivAt (fun s : Real => (chartPushLift (I := I) lift t0 s).1)
      (chartPushVF (I := I) g x0 lift t0 t0).1 t0 :=
  hasDerivAt_fst_of_prod
    (chartPushLift_hasDerivAt_self (I := I) hf)

/-- Base-time second-component equation for the chart-pushed lift. -/
theorem chartPushLift_snd_hasDerivAt_self
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x0 : M} {t0 : Real}
    {lift : Real -> TangentBundle I M}
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0) :
    HasDerivAt (fun s : Real => (chartPushLift (I := I) lift t0 s).2)
      (chartPushVF (I := I) g x0 lift t0 t0).2 t0 :=
  hasDerivAt_snd_of_prod
    (chartPushLift_hasDerivAt_self (I := I) hf)

/-- Initial first-component equation for a spray integral curve:
the derivative of chart position is the initial fiber velocity. -/
theorem chartPushLift_initial_fst_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t0) :
    HasDerivAt (fun s : Real => (chartPushLift (I := I) lift t0 s).1)
      v t0 := by
  have h := chartPushLift_fst_hasDerivAt_self (I := I) hf
  rw [chartPushVF_initial_fst (I := I) g hlift] at h
  exact h

/-- Initial second-component equation for a spray integral curve:
the derivative of chart velocity is the fixed-chart acceleration `-Γ(v,v)`. -/
theorem chartPushLift_initial_snd_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t0) :
    HasDerivAt (fun s : Real => (chartPushLift (I := I) lift t0 s).2)
      (leviCivitaGeodesicSprayAcceleration
        (I := I) g x (extChartAt I x x) v) t0 := by
  have h := chartPushLift_snd_hasDerivAt_self (I := I) hf
  rw [chartPushVF_initial_snd (I := I) g hlift] at h
  exact h

/-- Initial scalar second-component equation for a spray integral curve:
`(v^k)' = - Gamma^k_ij v^i v^j` in the fixed chart centered at `x`. -/
theorem chartPushLift_initial_snd_modelCoord_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t0)
    (k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun s : Real =>
        modelCoord k ((chartPushLift (I := I) lift t0 s).2))
      (-leviCivitaGeodesicSprayQuadratic
        (I := I) g x (extChartAt I x x) v k) t0 := by
  have hvec := chartPushLift_initial_snd_hasDerivAt
    (I := I) hlift hf
  have hcoord := hasDerivAt_modelCoord_of_vector
    k hvec
  simpa using hcoord

/-- Initial scalar second-component equation rewritten using the coordinate
package Christoffel quadratic.

This is the bridge from the chart-pushed spray RHS to the
`CoordinateEquation.lean` Christoffel convention.  It intentionally still
speaks about the chart-pushed fiber coordinate; the remaining bridge is to
identify that fiber-coordinate function with the velocity-coordinate function
of the projected curve on a neighborhood of the base time. -/
theorem chartPushLift_initial_snd_coordinateQuadratic_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {gamma : Curve M} {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t0)
    (hgamma0 : gamma t0 = x)
    (hvel0 : curveVelocity I gamma t0 = v)
    (k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun s : Real =>
        modelCoord k ((chartPushLift (I := I) lift t0 s).2))
      (-(extChartAtCoordinateData (I := I) x).christoffelVelocityQuadratic
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) gamma t0 k)
      t0 := by
  have hmodel :=
    chartPushLift_initial_snd_modelCoord_hasDerivAt
      (I := I) hlift hf k
  have hquad :=
    extChartAtCoordinateData_christoffelVelocityQuadratic_eq_leviCivita
      (I := I) g (gamma := gamma) (t := t0) hgamma0 k
  rw [hvel0] at hquad
  simpa [hquad] using hmodel

/-- The projected curve of a chart-fixed spray integral curve remains in the
initial coordinate package near the base time. -/
theorem projectCurve_mem_extChartAtCoordinateData_eventually_of_initial
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift0 : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t0) :
    ∀ᶠ t in 𝓝 t0,
      projectCurve (I := I) lift t ∈
        (extChartAtCoordinateData (I := I) x).domain := by
  have hproj_cont :
      ContinuousAt (fun t : Real => (lift t).proj) t0 := by
    exact (FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt.comp hf.continuousAt
  have hsrc :
      (extChartAtCoordinateData (I := I) x).domain ∈
        𝓝 ((lift t0).proj) := by
    simpa [hlift0, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using
      extChartAt_source_mem_nhds (I := I) x
  filter_upwards [hproj_cont.preimage_mem_nhds hsrc] with t ht
  simpa [projectCurve] using ht

/-- The coordinate velocity of the projected spray curve is eventually the
second component of the chart-pushed lift. -/
theorem velocityCoeff_eventuallyEq_chartPushLift_snd_of_geodesicSprayIntegral
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift0 : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t0)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (fun t : Real =>
      (extChartAtCoordinateData (I := I) x).velocityCoeff
        (projectCurve (I := I) lift) k t)
      =ᶠ[𝓝 t0]
    (fun t : Real =>
      modelCoord k ((chartPushLift (I := I) lift t0 t).2)) := by
  have hvel :=
    projectCurve_velocityBundle_eventually_eq_lift_of_initial
      (I := I) hlift0 hf
  have hsrc :=
    projectCurve_mem_extChartAtCoordinateData_eventually_of_initial
      (I := I) hlift0 hf
  filter_upwards [hvel, hsrc] with t hvel_t hsrc_t
  exact velocityCoeff_eq_chartPushLift_snd_of_velocityBundle
    (I := I) hlift0 hvel_t hsrc_t k

/-- A chart-fixed spray integral curve gives the scalar coordinate acceleration
of its projected curve at the base time. -/
theorem hasCoordinateAccelerationAt_projectCurve_of_geodesicSprayIntegral
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift0 : lift t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) t0) :
    HasCoordinateAccelerationAt (I := I)
      (extChartAtCoordinateData (I := I) x)
      (projectCurve (I := I) lift) t0
      (fun k : CoordinateIdx (𝕜 := Real) E =>
        -(extChartAtCoordinateData (I := I) x).christoffelVelocityQuadratic
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (projectCurve (I := I) lift) t0 k) := by
  intro k
  let gamma : Curve M := projectCurve (I := I) lift
  have hvelBundle0 :
      curveVelocityBundle I gamma t0 =
        (⟨x, v⟩ : TangentBundle I M) := by
    have hvelEventual :=
      projectCurve_velocityBundle_eventually_eq_lift_of_initial
        (I := I) hlift0 hf
    exact hvelEventual.self_of_nhds.trans hlift0
  have hgamma0 : gamma t0 = x := by
    simpa [gamma, projectCurve] using congrArg Bundle.TotalSpace.proj hlift0
  have hvel0 : curveVelocity I gamma t0 = v := by
    cases hgamma0
    simpa [gamma, curveVelocityBundle] using hvelBundle0
  have hderiv :=
    chartPushLift_initial_snd_coordinateQuadratic_hasDerivAt
      (I := I) (g := g) (x := x) (v := v) (gamma := gamma)
      (lift := lift) (t0 := t0) hlift0 hf hgamma0 hvel0 k
  have heq :=
    velocityCoeff_eventuallyEq_chartPushLift_snd_of_geodesicSprayIntegral
      (I := I) (g := g) (x := x) (v := v)
      (lift := lift) (t0 := t0) hlift0 hf k
  simpa [gamma] using hderiv.congr_of_eventuallyEq heq

/-- Scalar coordinate ODE produced by the geodesic spray.

Unlike `HasCoordinateGeodesicODEAt`, this predicate does not assert a
covariant-acceleration witness.  It is only the coordinate second-order ODE
`a^k + Gamma^k_ij v^i v^j = 0` supplied by the first-order spray system. -/
def HasCoordinateSprayODEAt
    (C : CoordinateChartData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) : Prop :=
  ∃ a : CoordinateIdx (𝕜 := Real) E -> Real,
    HasCoordinateAccelerationAt (I := I) C gamma t a ∧
      ∀ k : CoordinateIdx (𝕜 := Real) E,
        a k + C.christoffelVelocityQuadratic cov gamma t k = 0

/-- The scalar spray ODE is exactly zero coordinate-defined pullback
acceleration. -/
theorem HasCoordinateSprayODEAt.hasCoordinatePullbackAccelerationZero
    {C : CoordinateChartData (I := I) (M := M)}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real}
    (h : HasCoordinateSprayODEAt (I := I) C cov gamma t) :
    HasCoordinatePullbackAccelerationAt (I := I) C cov gamma t 0 := by
  rcases h with ⟨a, ha, hode⟩
  refine ⟨a, ?_, ?_⟩
  · exact (hasCoordinateAlongDerivativeAt_velocity_iff_accelerationAt
      (I := I) C gamma t a).2 ha
  · intro k
    rw [alongChristoffelTerm_velocity_eq_christoffelVelocityQuadratic
      (I := I) C cov gamma t k]
    simpa [CoordinateChartData.coeff] using (hode k).symm

/-- Eventual differentiability of the chart-pushed lift, as a lightweight
regularity consequence of the integral-curve equation. -/
theorem chartPushLift_eventually_differentiableAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x0 : M} {t0 : Real}
    {lift : Real -> TangentBundle I M}
    (hf : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0) :
    ∀ᶠ t in 𝓝 t0,
      DifferentiableAt Real (chartPushLift (I := I) lift t0) t := by
  filter_upwards [chartPushLift_eventually_hasDerivAt (I := I) hf] with t ht
  exact ht.differentiableAt

/-- Continuity at the base time of the chart-pushed lift, provided the lift is
continuous at that time. -/
theorem chartPushLift_continuousAt
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift : ContinuousAt lift t0) :
    ContinuousAt (chartPushLift (I := I) lift t0) t0 := by
  have hchart : ContinuousAt (extChartAt I.tangent (lift t0)) (lift t0) :=
    continuousAt_extChartAt (I := I.tangent) (lift t0)
  exact hchart.comp hlift

@[simp] theorem chartPushLift_self
    (lift : Real -> TangentBundle I M) (t0 : Real) :
    chartPushLift (I := I) lift t0 t0 =
      extChartAt I.tangent (lift t0) (lift t0) :=
  rfl

/-! ## Packaging for spray geodesics and local IVP -/

/-- A spray-geodesic witness exposes a chart-pushed first-order ODE for its
lift near the chosen time. -/
theorem IsSprayGeodesicAt.exists_chartPushLift_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {gamma : Curve M} {t0 : Real}
    (hgamma : IsSprayGeodesicAt (I := I) g gamma t0) :
    ∃ x0 : M, ∃ lift : Real -> TangentBundle I M,
      (∀ t : Real, (lift t).proj = gamma t) ∧
        IsMIntegralCurveAt lift
          (leviCivitaGeodesicSprayChart (I := I) g x0) t0 ∧
        ∀ᶠ t in 𝓝 t0,
          HasDerivAt (chartPushLift (I := I) lift t0)
            (chartPushVF (I := I) g x0 lift t0 t) t := by
  obtain ⟨lift, _hlift0, hproj, hf⟩ := hgamma
  exact ⟨gamma t0, lift, hproj, hf,
    chartPushLift_eventually_hasDerivAt (I := I) hf⟩

/-- Component form of the chart-pushed first-order ODE exposed from a
spray-geodesic witness. -/
theorem IsSprayGeodesicAt.exists_chartPushLift_component_hasDerivAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {gamma : Curve M} {t0 : Real}
    (hgamma : IsSprayGeodesicAt (I := I) g gamma t0) :
    ∃ x0 : M, ∃ lift : Real -> TangentBundle I M,
      (∀ t : Real, (lift t).proj = gamma t) ∧
        IsMIntegralCurveAt lift
          (leviCivitaGeodesicSprayChart (I := I) g x0) t0 ∧
        (∀ᶠ t in 𝓝 t0,
          HasDerivAt
            (fun s : Real => (chartPushLift (I := I) lift t0 s).1)
            (chartPushVF (I := I) g x0 lift t0 t).1 t) ∧
        (∀ᶠ t in 𝓝 t0,
          HasDerivAt
            (fun s : Real => (chartPushLift (I := I) lift t0 s).2)
            (chartPushVF (I := I) g x0 lift t0 t).2 t) := by
  obtain ⟨lift, _hlift0, hproj, hf⟩ := hgamma
  exact ⟨gamma t0, lift, hproj, hf,
    chartPushLift_fst_eventually_hasDerivAt (I := I) hf,
    chartPushLift_snd_eventually_hasDerivAt (I := I) hf⟩

/-- A centered spray geodesic satisfies the scalar coordinate geodesic ODE in
the `extChartAt` coordinate package at the base time. -/
theorem IsSprayGeodesicAt.hasCoordinateODE
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {gamma : Curve M} {t0 : Real}
    (hgamma : IsSprayGeodesicAt (I := I) g gamma t0) :
    HasCoordinateSprayODEAt (I := I)
      (extChartAtCoordinateData (I := I) (gamma t0))
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      gamma t0 := by
  obtain ⟨lift, hlift0, hproj, hf⟩ := hgamma
  have hgamma_eq : gamma = projectCurve (I := I) lift := by
    funext t
    exact (hproj t).symm
  subst gamma
  have hlift0' :
      lift t0 =
        (⟨projectCurve (I := I) lift t0,
          curveVelocity I (projectCurve (I := I) lift) t0⟩ :
            TangentBundle I M) := by
    simpa [curveVelocityBundle] using hlift0
  have ha :=
    hasCoordinateAccelerationAt_projectCurve_of_geodesicSprayIntegral
      (I := I) (g := g)
      (x := projectCurve (I := I) lift t0)
      (v := curveVelocity I (projectCurve (I := I) lift) t0)
      (lift := lift) (t0 := t0) hlift0' hf
  refine ⟨_, ha, ?_⟩
  intro k
  simp

/-- A centered spray geodesic has zero coordinate-defined pullback
acceleration in the `extChartAt` coordinate package at the base time. -/
theorem IsSprayGeodesicAt.hasCoordinatePullbackAccelerationZero
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {gamma : Curve M} {t0 : Real}
    (hgamma : IsSprayGeodesicAt (I := I) g gamma t0) :
    HasCoordinatePullbackAccelerationAt (I := I)
      (extChartAtCoordinateData (I := I) (gamma t0))
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      gamma t0 0 :=
  (IsSprayGeodesicAt.hasCoordinateODE
    (I := I) (g := g) (gamma := gamma) (t0 := t0) hgamma).hasCoordinatePullbackAccelerationZero

/-- Picard-Lindelof local existence, packaged with the chart-pushed
first-order ODE satisfied by the produced lift. -/
theorem exists_local_chartPush_geodesic_leviCivita
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ gamma : Curve M, ∃ lift : Real -> TangentBundle I M,
      lift 0 = (⟨x, v⟩ : TangentBundle I M) ∧
        gamma = projectCurve (I := I) lift ∧
        gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsMIntegralCurveAt lift
          (leviCivitaGeodesicSprayChart (I := I) g x) 0 ∧
        ∀ᶠ t in 𝓝 (0 : Real),
          HasDerivAt (chartPushLift (I := I) lift 0)
            (chartPushVF (I := I) g x lift 0 t) t := by
  obtain ⟨lift, hlift0, hf⟩ :=
    exists_isMIntegralCurveAt_leviCivitaGeodesicSprayChart
      (I := I) g x v
  refine ⟨projectCurve (I := I) lift, lift, hlift0, rfl, ?_, ?_, hf, ?_⟩
  · simpa using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) hlift0
  · exact projectCurve_initialVelocity_of_geodesicSprayIntegral
      (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
      (f := lift) hlift0 hf
  · exact chartPushLift_eventually_hasDerivAt (I := I) hf

/-- Local existence of a Levi-Civita spray geodesic, packaged with the scalar
coordinate ODE at the initial time. -/
theorem exists_local_geodesic
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsSprayGeodesicAt (I := I) g gamma 0 ∧
        HasCoordinateSprayODEAt (I := I)
          (extChartAtCoordinateData (I := I) x)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          gamma 0 := by
  obtain ⟨lift, hlift0, hf⟩ :=
    exists_isMIntegralCurveAt_leviCivitaGeodesicSprayChart
      (I := I) g x v
  let gamma : Curve M := projectCurve (I := I) lift
  have hgamma0 : gamma 0 = x := by
    simpa [gamma] using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) hlift0
  have hvel :
      curveVelocityBundle I gamma 0 =
        (⟨x, v⟩ : TangentBundle I M) := by
    simpa [gamma] using
      projectCurve_initialVelocity_of_geodesicSprayIntegral
        (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
        (f := lift) hlift0 hf
  have hspray : IsSprayGeodesicAt (I := I) g gamma 0 := by
    refine ⟨lift, ?_, ?_, ?_⟩
    · exact hlift0.trans hvel.symm
    · intro t
      rfl
    · simpa [hgamma0] using hf
  have hode :
      HasCoordinateSprayODEAt (I := I)
        (extChartAtCoordinateData (I := I) x)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        gamma 0 := by
    simpa [hgamma0] using
      IsSprayGeodesicAt.hasCoordinateODE
        (I := I) (g := g) (gamma := gamma) (t0 := 0) hspray
  exact ⟨gamma, hgamma0, hvel, hspray, hode⟩

/-- Local existence of a Levi-Civita spray geodesic, packaged with the
coordinate-defined zero pullback acceleration at the initial time. -/
theorem exists_local_geodesic_coordinateAccelerationZero
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsSprayGeodesicAt (I := I) g gamma 0 ∧
        HasCoordinateSprayODEAt (I := I)
          (extChartAtCoordinateData (I := I) x)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          gamma 0 ∧
        HasCoordinatePullbackAccelerationAt (I := I)
          (extChartAtCoordinateData (I := I) x)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          gamma 0 0 := by
  obtain ⟨gamma, hgamma0, hvel, hspray, hode⟩ :=
    exists_local_geodesic (I := I) g x v
  have hacc :
      HasCoordinatePullbackAccelerationAt (I := I)
        (extChartAtCoordinateData (I := I) (gamma 0))
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        gamma 0 0 :=
    IsSprayGeodesicAt.hasCoordinatePullbackAccelerationZero
      (I := I) (g := g) (gamma := gamma) (t0 := 0) hspray
  refine ⟨gamma, hgamma0, hvel, hspray, hode, ?_⟩
  simpa [hgamma0] using hacc

end Lecture07
end GlobalGeometry
end RicciFlower
