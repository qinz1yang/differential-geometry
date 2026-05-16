import RicciFlower.GlobalGeometry.Lecture07.InitialValue
import RicciFlower.GlobalGeometry.Lecture07.CoordinateEquation
import RicciFlower.LeviCivita.Smooth
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# GSM245 Lecture 7.3: geodesic spray and local IVP

This file starts the first-order ODE layer for geodesics.  The chart-fixed
spray is written in the `extChartAt` coordinates centered at `x0`, turning

`x''^k + Gamma^k_ij(x) x'^i x'^j = 0`

into a first-order system on the tangent bundle:

`x' = v`, `v'^k = - Gamma^k_ij(x) v^i v^j`.

The local existence theorem below is intentionally a spray-integral IVP, not
the older all-time global-extension predicate `IsGeodesic`.  The later bridge
from spray-integral curves to `HasIntrinsicGeodesicEquationAt` is a separate
coordinate-equation theorem.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle Filter
open scoped BigOperators Manifold ContDiff Topology
open RicciFlower.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## Chart-fixed spray -/

/-- The fixed-chart fiber coordinate of a tangent-bundle point. -/
def chartFiberCoordAt (x0 : M) (q : TangentBundle I M) : E :=
  (coordinateTrivializationAt (I := I) x0 q).2

@[simp] theorem chartFiberCoordAt_apply (x0 : M) (q : TangentBundle I M) :
    chartFiberCoordAt (I := I) x0 q =
      (coordinateTrivializationAt (I := I) x0 q).2 := rfl

@[simp] theorem chartFiberCoordAt_self (u : TangentBundle I M) :
    chartFiberCoordAt (I := I) u.proj u = u.2 := by
  rcases u with ⟨x, v⟩
  simp [chartFiberCoordAt, coordinateTrivializationAt,
    TangentBundle.trivializationAt_apply]
  have hdiff : MDiffAt (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (I := I) (x := x) (y := x)
      (mem_chart_source H x)
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe] at hdiff
  simpa [mfderiv, hdiff] using
    congrArg (fun L : TangentSpace I x →L[Real] E => L v)
      (mfderiv_extChartAt_self (I := I) (x := x))

/-- The fixed-chart fiber coordinate is the derivative of the fixed base chart
applied to the actual tangent vector. -/
theorem chartFiberCoordAt_eq_mfderiv_extChartAt
    (x0 : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (extChartAt I x0).source) :
    chartFiberCoordAt (I := I) x0 q =
      (mfderiv I 𝓘(Real, E) (extChartAt I x0) q.proj) q.2 := by
  have hq_chart : q.proj ∈ (chartAt H x0).source := by
    simpa [extChartAt_source] using hq
  have hlin :=
    TangentBundle.continuousLinearMapAt_trivializationAt
      (I := I) (𝕜 := Real) (x₀ := x0) (x := q.proj) hq_chart
  change ((coordinateTrivializationAt (I := I) x0 q).2) =
    (mfderiv I 𝓘(Real, E) (extChartAt I x0) q.proj) q.2
  rw [← hlin]
  change ((trivializationAt E (TangentSpace I : M -> Type _) x0 q).2) =
    (Trivialization.continuousLinearMapAt Real
      (trivializationAt E (TangentSpace I : M -> Type _) x0) q.proj) q.2
  have hbase :
      q.proj ∈
        (trivializationAt E (TangentSpace I : M -> Type _) x0).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hq_chart
  rw [(trivializationAt E (TangentSpace I : M -> Type _) x0).continuousLinearMapAt_apply Real]
  rw [(trivializationAt E (TangentSpace I : M -> Type _) x0).coe_linearMapAt_of_mem
    (R := Real) hbase]

/-- Model coordinate of a vector in the fixed finite basis. -/
def modelCoord (i : CoordinateIdx (𝕜 := Real) E) (v : E) : Real :=
  (Module.finBasis Real E).coord i v

/-- The coordinate quadratic `Gamma^k_ij(y) v^i v^j` in the fixed chart at
`x0`, using the smooth Levi-Civita Christoffel model already developed in
`LeviCivita/Smooth.lean`. -/
def leviCivitaGeodesicSprayQuadratic
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (y v : E) (k : CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ i : CoordinateIdx (𝕜 := Real) E,
    ∑ j : CoordinateIdx (𝕜 := Real) E,
      LeviCivita.leviCivitaChristoffelModelRHS (I := I) g x0 i j k y *
        modelCoord i v * modelCoord j v

/-- The model-space acceleration component of the geodesic spray,
`- Gamma(v,v)`. -/
def leviCivitaGeodesicSprayAcceleration
    (g : SmoothRiemannianMetric I M) (x0 : M) (y v : E) : E :=
  ∑ k : CoordinateIdx (𝕜 := Real) E,
    (-leviCivitaGeodesicSprayQuadratic (I := I) g x0 y v k) •
      (Module.finBasis Real E k)

/-- The `k`th coordinate of the model-space acceleration is exactly the
scalar geodesic ODE right-hand side `- Gamma^k_ij v^i v^j`. -/
@[simp] theorem modelCoord_leviCivitaGeodesicSprayAcceleration
    (g : SmoothRiemannianMetric I M) (x0 : M) (y v : E)
    (k : CoordinateIdx (𝕜 := Real) E) :
    modelCoord k
        (leviCivitaGeodesicSprayAcceleration (I := I) g x0 y v) =
      -leviCivitaGeodesicSprayQuadratic (I := I) g x0 y v k := by
  classical
  simp [modelCoord, leviCivitaGeodesicSprayAcceleration]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _hb hbk
    exact Finsupp.single_eq_of_ne hbk.symm
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

/-- The chart-fiber expression of the geodesic spray.  The first component is
the current velocity; the second is the coordinate acceleration. -/
def leviCivitaGeodesicSprayChartFiber
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (q : TangentBundle I M) : E × E :=
  let v := chartFiberCoordAt (I := I) x0 q
  (v, leviCivitaGeodesicSprayAcceleration
    (I := I) g x0 (extChartAt I x0 q.proj) v)

/-- The chart-fixed geodesic spray as a tangent vector on `TM`. -/
def leviCivitaGeodesicSprayChart
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (q : TangentBundle I M) : TangentSpace I.tangent q :=
  (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨x0, (0 : E)⟩ : TangentBundle I M)).symm q
    (leviCivitaGeodesicSprayChartFiber (I := I) g x0 q)

/-- The fixed chart domain for the spray on `TM`. -/
def geodesicSprayChartDomain (x0 : M) : Set (TangentBundle I M) :=
  {q : TangentBundle I M | q.proj ∈ (chartAt H x0).source}

theorem geodesicSprayChartDomain_isOpen (x0 : M) :
    IsOpen (geodesicSprayChartDomain (I := I) (M := M) x0) := by
  simpa [geodesicSprayChartDomain] using
    (chartAt H x0).open_source.preimage
      (FiberBundle.continuous_proj E (TangentSpace I : M -> Type _))

theorem chartFiberCoordAt_contMDiffAt_self
    (x : M) (v : TangentSpace I x) :
    ContMDiffAt I.tangent 𝓘(Real, E) ∞
      (chartFiberCoordAt (I := I) x)
      (⟨x, v⟩ : TangentBundle I M) := by
  classical
  let e := coordinateTrivializationAt (I := I) x
  have he :
      (id (⟨x, v⟩ : TangentBundle I M)) ∈ e.source := by
    simp [e, coordinateTrivializationAt]
  have hiff := e.contMDiffAt_iff
    (IM := I.tangent) (IB := I) (n := (∞ : WithTop ℕ∞))
    (f := id) (x₀ := (⟨x, v⟩ : TangentBundle I M)) he
  have hid : ContMDiffAt I.tangent (I.prod 𝓘(Real, E)) ∞
      (id : TangentBundle I M -> TangentBundle I M)
      (⟨x, v⟩ : TangentBundle I M) := contMDiffAt_id
  simpa [chartFiberCoordAt, e] using hiff.mp hid |>.2

theorem extChartAt_proj_contMDiffAt_self
    (x : M) (v : TangentSpace I x) :
    ContMDiffAt I.tangent 𝓘(Real, E) ∞
      (fun q : TangentBundle I M => extChartAt I x q.proj)
      (⟨x, v⟩ : TangentBundle I M) := by
  exact (contMDiffAt_extChartAt (I := I) (x := x)).comp
    (⟨x, v⟩ : TangentBundle I M)
    (Bundle.contMDiffAt_proj (F := E) (E := TangentSpace I)
      (IB := I) (n := (∞ : WithTop ℕ∞)))

theorem leviCivitaChristoffelModelRHS_comp_extChartAt_proj_contMDiffAt_self
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I.tangent 𝓘(Real) ∞
      (fun q : TangentBundle I M =>
        LeviCivita.leviCivitaChristoffelModelRHS
          (I := I) g x i j k (extChartAt I x q.proj))
      (⟨x, v⟩ : TangentBundle I M) := by
  have hΓWithin :=
    LeviCivita.leviCivitaChristoffelModelRHS_contDiffWithinAt
      (I := I) g x i j k
  have hRange :
      Set.range I ∈ 𝓝 (extChartAt I x x) := by
    exact Filter.mem_of_superset (extChartAt_target_mem_nhds (I := I) x)
      (extChartAt_target_subset_range (I := I) x)
  have hΓAt :
      ContDiffAt Real ∞
        (LeviCivita.leviCivitaChristoffelModelRHS
          (I := I) g x i j k)
        (extChartAt I x x) :=
    hΓWithin.contDiffAt hRange
  simpa [Function.comp_def] using
    hΓAt.comp_contMDiffAt
      (f := fun q : TangentBundle I M => extChartAt I x q.proj)
      (x := (⟨x, v⟩ : TangentBundle I M))
      (extChartAt_proj_contMDiffAt_self (I := I) x v)

theorem modelCoord_chartFiberCoordAt_contMDiffAt_self
    (x : M) (v : TangentSpace I x)
    (i : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I.tangent 𝓘(Real) ∞
      (fun q : TangentBundle I M =>
        modelCoord i (chartFiberCoordAt (I := I) x q))
      (⟨x, v⟩ : TangentBundle I M) := by
  have hcoord :
      ContDiffAt Real ∞
        (modelCoord i) (chartFiberCoordAt (I := I) x
          (⟨x, v⟩ : TangentBundle I M)) := by
    simpa [modelCoord] using
      (((Module.finBasis Real E).coord i).toContinuousLinearMap.contDiff.contDiffAt :
        ContDiffAt Real ∞
          (((Module.finBasis Real E).coord i).toContinuousLinearMap)
          (chartFiberCoordAt (I := I) x
            (⟨x, v⟩ : TangentBundle I M)))
  simpa [Function.comp_def] using
    hcoord.comp_contMDiffAt
      (f := chartFiberCoordAt (I := I) x)
      (x := (⟨x, v⟩ : TangentBundle I M))
      (chartFiberCoordAt_contMDiffAt_self (I := I) x v)

theorem leviCivitaGeodesicSprayQuadratic_contMDiffAt_self
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x)
    (k : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I.tangent 𝓘(Real) ∞
      (fun q : TangentBundle I M =>
        leviCivitaGeodesicSprayQuadratic (I := I) g x
          (extChartAt I x q.proj) (chartFiberCoordAt (I := I) x q) k)
      (⟨x, v⟩ : TangentBundle I M) := by
  classical
  unfold leviCivitaGeodesicSprayQuadratic
  refine ContMDiffAt.sum fun i _ => ?_
  refine ContMDiffAt.sum fun j _ => ?_
  have hΓ :=
    leviCivitaChristoffelModelRHS_comp_extChartAt_proj_contMDiffAt_self
      (I := I) g x v i j k
  have hi := modelCoord_chartFiberCoordAt_contMDiffAt_self (I := I) x v i
  have hj := modelCoord_chartFiberCoordAt_contMDiffAt_self (I := I) x v j
  exact (hΓ.mul hi).mul hj

theorem leviCivitaGeodesicSprayAcceleration_contMDiffAt_self
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ContMDiffAt I.tangent 𝓘(Real, E) ∞
      (fun q : TangentBundle I M =>
        leviCivitaGeodesicSprayAcceleration (I := I) g x
          (extChartAt I x q.proj) (chartFiberCoordAt (I := I) x q))
      (⟨x, v⟩ : TangentBundle I M) := by
  classical
  unfold leviCivitaGeodesicSprayAcceleration
  refine ContMDiffAt.sum fun k _ => ?_
  have hq :=
    leviCivitaGeodesicSprayQuadratic_contMDiffAt_self
      (I := I) g x v k
  have hbasis : ContMDiffAt I.tangent 𝓘(Real, E) ∞
      (fun _ : TangentBundle I M => Module.finBasis Real E k)
      (⟨x, v⟩ : TangentBundle I M) := contMDiffAt_const
  exact hq.neg.smul hbasis

theorem leviCivitaGeodesicSprayChartFiber_contMDiffAt_self
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ContMDiffAt I.tangent 𝓘(Real, E × E) ∞
      (leviCivitaGeodesicSprayChartFiber (I := I) g x)
      (⟨x, v⟩ : TangentBundle I M) := by
  have hfst := chartFiberCoordAt_contMDiffAt_self (I := I) x v
  have hsnd :=
    leviCivitaGeodesicSprayAcceleration_contMDiffAt_self
      (I := I) g x v
  simpa [leviCivitaGeodesicSprayChartFiber] using hfst.prodMk_space hsnd

/-! ## Local geodesics via spray integral curves -/

/-- Projection of a tangent-bundle curve to a base curve. -/
def projectCurve (f : Real -> TangentBundle I M) : Curve M :=
  fun t => (f t).proj

@[simp] theorem projectCurve_apply (f : Real -> TangentBundle I M) (t : Real) :
    projectCurve (I := I) f t = (f t).proj := rfl

theorem projectCurve_zero_of_lift
    {f : Real -> TangentBundle I M} {u : TangentBundle I M}
    (hf0 : f 0 = u) :
    projectCurve (I := I) f 0 = u.proj := by
  simp [projectCurve, hf0]

/-- Local geodesic predicate in the spray-integral sense.

This is intentionally separate from the global-extension predicate
`IsGeodesic` in `Geodesics.lean`. -/
def IsSprayGeodesicAt
    (g : SmoothRiemannianMetric I M) (gamma : Curve M) (t0 : Real) : Prop :=
  ∃ lift : Real -> TangentBundle I M,
    lift t0 = curveVelocityBundle I gamma t0 ∧
      (∀ t : Real, (lift t).proj = gamma t) ∧
        IsMIntegralCurveAt lift
          (leviCivitaGeodesicSprayChart (I := I) g (gamma t0)) t0

/-- Local geodesic initial-value data produced by the geodesic spray. -/
structure LocalGeodesicIVPAt
    (g : SmoothRiemannianMetric I M)
    (u : TangentBundle I M) where
  epsilon : Real
  epsilon_pos : 0 < epsilon
  lift : Real -> TangentBundle I M
  gamma : Curve M
  lift_initial : lift 0 = u
  projects :
    ∀ t ∈ Metric.ball (0 : Real) epsilon, gamma t = (lift t).proj
  spray_integral :
    IsMIntegralCurveOn lift
      (leviCivitaGeodesicSprayChart (I := I) g u.proj)
      (Metric.ball (0 : Real) epsilon)
  initial_position : gamma 0 = u.proj
  initial_velocity : curveVelocityBundle I gamma 0 = u

/-! ## Picard-Lindelof smoothness -/

/-- In the fixed `T(TM)` trivialization, the chart-fixed spray section has
fiber coordinate equal to the chart-fiber RHS. -/
theorem trivializationAt_apply_leviCivitaGeodesicSprayChart
    (g : SmoothRiemannianMetric I M) (x : M)
    {q : TangentBundle I M}
    (hq : q ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨x, (0 : E)⟩ : TangentBundle I M)).baseSet) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨x, (0 : E)⟩ : TangentBundle I M))
      ⟨q, leviCivitaGeodesicSprayChart (I := I) g x q⟩ =
        (q, leviCivitaGeodesicSprayChartFiber (I := I) g x q) := by
  exact (trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨x, (0 : E)⟩ : TangentBundle I M)).apply_mk_symm hq
      (leviCivitaGeodesicSprayChartFiber (I := I) g x q)

/-- Smoothness of the chart-fixed Levi-Civita spray section at the initial
tangent-bundle point.  This is the exact regularity input needed by
Mathlib's manifold Picard-Lindelof theorem. -/
theorem leviCivitaGeodesicSprayChart_contMDiffAt_self
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun q : TangentBundle I M =>
        (⟨q, leviCivitaGeodesicSprayChart (I := I) g x q⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (⟨x, v⟩ : TangentBundle I M) := by
  classical
  let q0 : TangentBundle I M := ⟨x, v⟩
  let e := trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨x, (0 : E)⟩ : TangentBundle I M)
  have hq0 : q0 ∈ e.baseSet := by
    simp [q0, e]
  have hsource :
      (⟨q0, leviCivitaGeodesicSprayChart (I := I) g x q0⟩ :
        TangentBundle I.tangent (TangentBundle I M)) ∈ e.source := by
    rw [Trivialization.source_eq]
    exact hq0
  have hiff := e.contMDiffAt_iff
    (IM := I.tangent) (IB := I.tangent)
    (n := (∞ : WithTop ℕ∞))
    (f := fun q : TangentBundle I M =>
      (⟨q, leviCivitaGeodesicSprayChart (I := I) g x q⟩ :
        TangentBundle I.tangent (TangentBundle I M)))
    (x₀ := q0) hsource
  refine hiff.mpr ⟨?_, ?_⟩
  · simpa [q0] using
      (contMDiffAt_id :
        ContMDiffAt I.tangent I.tangent ∞
          (fun q : TangentBundle I M => q) q0)
  · have hfiber :=
      leviCivitaGeodesicSprayChartFiber_contMDiffAt_self
        (I := I) g x v
    refine hfiber.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hq0] with q hq
    have htriv :=
      trivializationAt_apply_leviCivitaGeodesicSprayChart
        (I := I) g x (q := q) (by simpa [e] using hq)
    simpa using congrArg Prod.snd htriv

/-- Picard-Lindelof local integral curve for the chart-fixed geodesic spray. -/
theorem exists_isMIntegralCurveAt_leviCivitaGeodesicSprayChart
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ∃ f : Real -> TangentBundle I M,
      f 0 = (⟨x, v⟩ : TangentBundle I M) ∧
        IsMIntegralCurveAt f
          (leviCivitaGeodesicSprayChart (I := I) g x) 0 := by
  classical
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsmoothTop :
      ContMDiffAt I.tangent I.tangent.tangent ∞
        (fun q : TangentBundle I M =>
          (⟨q, leviCivitaGeodesicSprayChart (I := I) g x q⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (⟨x, v⟩ : TangentBundle I M) :=
    leviCivitaGeodesicSprayChart_contMDiffAt_self (I := I) g x v
  have hsmoothOne :
      ContMDiffAt I.tangent I.tangent.tangent 1
        (fun q : TangentBundle I M =>
          (⟨q, leviCivitaGeodesicSprayChart (I := I) g x q⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (⟨x, v⟩ : TangentBundle I M) :=
    hsmoothTop.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := leviCivitaGeodesicSprayChart (I := I) g x)
      (t₀ := (0 : Real)) (x₀ := (⟨x, v⟩ : TangentBundle I M)) hsmoothOne

/-- The chart-fixed spray projects to the current tangent vector in the base.

This is the first-order-system identity corresponding to the equation `x' = v`. -/
theorem mfderiv_proj_leviCivitaGeodesicSprayChart_self
    (g : SmoothRiemannianMetric I M) (u : TangentBundle I M) :
    (mfderiv I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M -> M) u)
      (leviCivitaGeodesicSprayChart (I := I) g u.proj u) = u.2 := by
  rcases u with ⟨x, v⟩
  let q : TangentBundle I M := ⟨x, v⟩
  let q0 : TangentBundle I M := ⟨x, (0 : E)⟩
  let e := trivializationAt (E × E) (TangentSpace I.tangent) q0
  let w : TangentSpace I.tangent q :=
    leviCivitaGeodesicSprayChart (I := I) g x q
  have hq_source : q ∈ (chartAt (ModelProd H E) q0).source := by
    simp [q, q0]
  have hbase_source : x ∈ (chartAt H x).source := mem_chart_source H x
  have htriv :
      e.continuousLinearMapAt Real q w =
        leviCivitaGeodesicSprayChartFiber (I := I) g x q := by
    have hbase : q ∈ e.baseSet := by
      simpa [e, q0] using hq_source
    simpa [w, leviCivitaGeodesicSprayChart, e, q0] using
      e.continuousLinearMapAt_symmL (R := Real) hbase
        (leviCivitaGeodesicSprayChartFiber (I := I) g x q)
  have hfirst :
      (e.continuousLinearMapAt Real q w).1 =
        (mfderiv I 𝓘(Real, E) (extChartAt I x) x)
          ((mfderiv I.tangent I
              (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w) := by
    have hlin :
        e.continuousLinearMapAt Real q =
          mfderiv I.tangent 𝓘(Real, E × E) (extChartAt I.tangent q0) q := by
      simpa [e, q0] using
        TangentBundle.continuousLinearMapAt_trivializationAt
          (I := I.tangent) (x₀ := q0) (x := q) hq_source
    rw [hlin]
    have hfst :
        ((mfderiv I.tangent 𝓘(Real, E × E)
            (extChartAt I.tangent q0) q) w).1 =
          (mfderiv I.tangent 𝓘(Real, E)
              ((ContinuousLinearMap.fst Real E E) ∘ extChartAt I.tangent q0) q) w := by
      rw [mfderiv_comp_apply
        (I := I.tangent) (I' := 𝓘(Real, E × E)) (I'' := 𝓘(Real, E))
        (g := (ContinuousLinearMap.fst Real E E : E × E -> E))
        (f := extChartAt I.tangent q0)
        (x := q) (v := w)]
      · rw [ContinuousLinearMap.mfderiv_eq]
        rfl
      · exact (ContinuousLinearMap.fst Real E E).mdifferentiableAt
      · exact mdifferentiableAt_extChartAt (I := I.tangent)
          (x := q0) (y := q) hq_source
    refine hfst.trans ?_
    have hchart :
        ((ContinuousLinearMap.fst Real E E) ∘ extChartAt I.tangent q0) =
          (fun z : TangentBundle I M => extChartAt I x z.proj) := by
      funext z
      simp [q0, TangentBundle.coe_chartAt_fst]
    rw [hchart]
    change
      (mfderiv I.tangent 𝓘(Real, E)
          ((extChartAt I x) ∘
            (Bundle.TotalSpace.proj : TangentBundle I M -> M)) q) w =
        (mfderiv I 𝓘(Real, E) (extChartAt I x) x)
          ((mfderiv I.tangent I
              (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w)
    rw [mfderiv_comp_apply
      (I := I.tangent) (I' := I) (I'' := 𝓘(Real, E))
      (g := extChartAt I x)
      (f := (Bundle.TotalSpace.proj : TangentBundle I M -> M))
      (x := q) (v := w)]
    · exact mdifferentiableAt_extChartAt (I := I) (x := x) (y := q.proj)
        (by simp [q])
    ·
      show MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M -> M) q
      exact (Bundle.contMDiffAt_proj (F := E) (E := TangentSpace I)
        (IB := I) (n := (1 : WithTop ℕ∞)) (p := q)).mdifferentiableAt
          one_ne_zero
  have hfirst_rhs :
      (e.continuousLinearMapAt Real q w).1 = v := by
    rw [htriv]
    change chartFiberCoordAt (I := I) x q = v
    simpa [q] using chartFiberCoordAt_self (I := I) (u := q)
  have hidentity :
      (mfderiv I 𝓘(Real, E) (extChartAt I x) x)
          ((mfderiv I.tangent I
              (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w) =
        (mfderiv I.tangent I
              (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w := by
    rw [mfderiv_extChartAt_self]
    rfl
  simpa [q, w] using hidentity ▸ hfirst.symm.trans hfirst_rhs

/-- The chart-fixed spray projects to the current tangent vector on the whole
fixed chart domain.  This is the coordinate-independent `x' = v` identity for
the first-order geodesic system. -/
theorem mfderiv_proj_leviCivitaGeodesicSprayChart
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (q : TangentBundle I M)
    (hq : q.proj ∈ (extChartAt I x0).source) :
    (mfderiv I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M -> M) q)
      (leviCivitaGeodesicSprayChart (I := I) g x0 q) = q.2 := by
  rcases q with ⟨y, v⟩
  let q : TangentBundle I M := ⟨y, v⟩
  let q0 : TangentBundle I M := ⟨x0, (0 : E)⟩
  let e := trivializationAt (E × E) (TangentSpace I.tangent) q0
  let w : TangentSpace I.tangent q :=
    leviCivitaGeodesicSprayChart (I := I) g x0 q
  have hq_chart : y ∈ (chartAt H x0).source := by
    simpa [q, extChartAt_source] using hq
  have hq_source : q ∈ (chartAt (ModelProd H E) q0).source := by
    rw [TangentBundle.mem_chart_source_iff]
    simpa [q, q0] using hq_chart
  have htriv :
      e.continuousLinearMapAt Real q w =
        leviCivitaGeodesicSprayChartFiber (I := I) g x0 q := by
    have hbase : q ∈ e.baseSet := by
      simpa [e, q0] using hq_source
    simpa [w, leviCivitaGeodesicSprayChart, e, q0] using
      e.continuousLinearMapAt_symmL (R := Real) hbase
        (leviCivitaGeodesicSprayChartFiber (I := I) g x0 q)
  have hfirst :
      (e.continuousLinearMapAt Real q w).1 =
        (mfderiv I 𝓘(Real, E) (extChartAt I x0) y)
          ((mfderiv I.tangent I
              (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w) := by
    have hlin :
        e.continuousLinearMapAt Real q =
          mfderiv I.tangent 𝓘(Real, E × E) (extChartAt I.tangent q0) q := by
      simpa [e, q0] using
        TangentBundle.continuousLinearMapAt_trivializationAt
          (I := I.tangent) (𝕜 := Real) (x₀ := q0) (x := q) hq_source
    rw [hlin]
    have hfst :
        ((mfderiv I.tangent 𝓘(Real, E × E)
            (extChartAt I.tangent q0) q) w).1 =
          (mfderiv I.tangent 𝓘(Real, E)
              ((ContinuousLinearMap.fst Real E E) ∘ extChartAt I.tangent q0) q) w := by
      rw [mfderiv_comp_apply
        (I := I.tangent) (I' := 𝓘(Real, E × E)) (I'' := 𝓘(Real, E))
        (g := (ContinuousLinearMap.fst Real E E : E × E -> E))
        (f := extChartAt I.tangent q0)
        (x := q) (v := w)]
      · rw [ContinuousLinearMap.mfderiv_eq]
        rfl
      · exact (ContinuousLinearMap.fst Real E E).mdifferentiableAt
      · exact mdifferentiableAt_extChartAt (I := I.tangent)
          (x := q0) (y := q) hq_source
    refine hfst.trans ?_
    have hchart :
        ((ContinuousLinearMap.fst Real E E) ∘ extChartAt I.tangent q0) =
          (fun z : TangentBundle I M => extChartAt I x0 z.proj) := by
      funext z
      simp [q0, TangentBundle.coe_chartAt_fst]
    rw [hchart]
    change
      (mfderiv I.tangent 𝓘(Real, E)
          ((extChartAt I x0) ∘
            (Bundle.TotalSpace.proj : TangentBundle I M -> M)) q) w =
        (mfderiv I 𝓘(Real, E) (extChartAt I x0) y)
          ((mfderiv I.tangent I
              (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w)
    rw [mfderiv_comp_apply
      (I := I.tangent) (I' := I) (I'' := 𝓘(Real, E))
      (g := extChartAt I x0)
      (f := (Bundle.TotalSpace.proj : TangentBundle I M -> M))
      (x := q) (v := w)]
    · exact mdifferentiableAt_extChartAt (I := I) (x := x0) (y := q.proj) hq_chart
    ·
      show MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M -> M) q
      exact (Bundle.contMDiffAt_proj (F := E) (E := TangentSpace I)
        (IB := I) (n := (1 : WithTop ℕ∞)) (p := q)).mdifferentiableAt
          one_ne_zero
  have hfirst_rhs :
      (e.continuousLinearMapAt Real q w).1 =
        chartFiberCoordAt (I := I) x0 q := by
    rw [htriv]
    rfl
  have hfiber :
      chartFiberCoordAt (I := I) x0 q =
        (mfderiv I 𝓘(Real, E) (extChartAt I x0) y) v := by
    simpa [q] using chartFiberCoordAt_eq_mfderiv_extChartAt
      (I := I) x0 q hq
  have hD :
      (mfderiv I 𝓘(Real, E) (extChartAt I x0) y)
          ((mfderiv I.tangent I
              (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w) =
        (mfderiv I 𝓘(Real, E) (extChartAt I x0) y) v :=
    (hfirst.symm.trans hfirst_rhs).trans hfiber
  have hinv :
      (mfderiv I 𝓘(Real, E) (extChartAt I x0) y).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := I) (x := x0) hq
  have hpre :=
    congrArg
      (fun z : E =>
        (mfderiv I 𝓘(Real, E) (extChartAt I x0) y).inverse z) hD
  change
    (mfderiv I 𝓘(Real, E) (extChartAt I x0) y).inverse
        ((mfderiv I 𝓘(Real, E) (extChartAt I x0) y)
          ((mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) q) w)) =
      (mfderiv I 𝓘(Real, E) (extChartAt I x0) y).inverse
        ((mfderiv I 𝓘(Real, E) (extChartAt I x0) y) v) at hpre
  rw [hinv.inverse_apply_self, hinv.inverse_apply_self] at hpre
  simpa [q, w] using hpre

/-- The base projection of a spray integral curve has the expected initial
velocity.

This is the exact first-component bridge from the tangent-bundle first-order
system to `curveVelocityBundle`. -/
theorem projectCurve_initialVelocity_of_geodesicSprayIntegral
    {g : SmoothRiemannianMetric I M}
    {u : TangentBundle I M} {f : Real -> TangentBundle I M}
    (hf0 : f 0 = u)
    (hf : IsMIntegralCurveAt f
      (leviCivitaGeodesicSprayChart (I := I) g u.proj) 0) :
    curveVelocityBundle I (projectCurve (I := I) f) 0 = u := by
  rcases u with ⟨x, v⟩
  have hf_deriv := hf.hasMFDerivAt
  have hf_mfderiv := hf_deriv.mfderiv
  have hproj_diff :
      MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f 0) := by
    exact (Bundle.contMDiffAt_proj (F := E) (E := TangentSpace I)
      (IB := I) (n := (1 : WithTop ℕ∞)) (p := f 0)).mdifferentiableAt
        one_ne_zero
  have hchain :
      mfderiv 𝓘(Real, Real) I
          ((Bundle.TotalSpace.proj : TangentBundle I M -> M) ∘ f) 0 1 =
        (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f 0))
          ((mfderiv 𝓘(Real, Real) I.tangent f 0) 1) := by
    exact mfderiv_comp_apply
      (I := 𝓘(Real, Real)) (I' := I.tangent) (I'' := I)
      (g := (Bundle.TotalSpace.proj : TangentBundle I M -> M))
      (f := f) (x := 0) hproj_diff hf_deriv.mdifferentiableAt 1
  have hvel : curveVelocity I (projectCurve (I := I) f) 0 = v := by
    simp only [curveVelocity, projectCurve]
    change
      (mfderiv 𝓘(Real, Real) I
          ((Bundle.TotalSpace.proj : TangentBundle I M -> M) ∘ f) 0) 1 = v
    rw [hchain, hf_mfderiv]
    have harg :
        ((ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
            (leviCivitaGeodesicSprayChart (I := I) g
              (⟨x, v⟩ : TangentBundle I M).proj (f 0))) 1) =
          leviCivitaGeodesicSprayChart (I := I) g
            (⟨x, v⟩ : TangentBundle I M).proj (f 0) := by
      simp [ContinuousLinearMap.smulRight_apply]
    have hproj_arg :
        (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f 0))
          ((ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
            (leviCivitaGeodesicSprayChart (I := I) g
              (⟨x, v⟩ : TangentBundle I M).proj (f 0))) 1) =
        (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f 0))
          (leviCivitaGeodesicSprayChart (I := I) g
            (⟨x, v⟩ : TangentBundle I M).proj (f 0)) :=
      congrArg
        (fun z =>
          (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f 0)) z) harg
    refine hproj_arg.trans ?_
    rw [hf0]
    exact mfderiv_proj_leviCivitaGeodesicSprayChart_self
      (I := I) g (⟨x, v⟩ : TangentBundle I M)
  refine TotalSpace.ext ?_ ?_
  · simp [curveVelocityBundle, hf0]
  · simp [curveVelocityBundle, hvel]
    exact HEq.rfl

/-- If a lift solves the chart-fixed geodesic spray and stays in the fixed
chart domain, then its base projection has the lift itself as tangent lift.

This is the reusable velocity-lift interface downstream coordinate ODE proofs
should use instead of redoing tangent-bundle chart calculations. -/
theorem projectCurve_velocityBundle_eventually_eq_lift
    {g : SmoothRiemannianMetric I M} {x0 : M}
    {f : Real -> TangentBundle I M} {t0 : Real}
    (hf : IsMIntegralCurveAt f
      (leviCivitaGeodesicSprayChart (I := I) g x0) t0)
    (hsrc : ∀ᶠ t in 𝓝 t0, (f t).proj ∈ (extChartAt I x0).source) :
    ∀ᶠ t in 𝓝 t0,
      curveVelocityBundle I (projectCurve (I := I) f) t = f t := by
  filter_upwards [hf, hsrc] with t ht hsrc_t
  have ht_mfderiv := ht.mfderiv
  have hproj_diff :
      MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f t) := by
    exact (Bundle.contMDiffAt_proj (F := E) (E := TangentSpace I)
      (IB := I) (n := (1 : WithTop ℕ∞)) (p := f t)).mdifferentiableAt
        one_ne_zero
  have hchain :
      mfderiv 𝓘(Real, Real) I
          ((Bundle.TotalSpace.proj : TangentBundle I M -> M) ∘ f) t 1 =
        (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f t))
          ((mfderiv 𝓘(Real, Real) I.tangent f t) 1) := by
    exact mfderiv_comp_apply
      (I := 𝓘(Real, Real)) (I' := I.tangent) (I'' := I)
      (g := (Bundle.TotalSpace.proj : TangentBundle I M -> M))
      (f := f) (x := t) hproj_diff ht.mdifferentiableAt 1
  have hvel : curveVelocity I (projectCurve (I := I) f) t = (f t).2 := by
    simp only [curveVelocity, projectCurve]
    change
      (mfderiv 𝓘(Real, Real) I
          ((Bundle.TotalSpace.proj : TangentBundle I M -> M) ∘ f) t) 1 =
        (f t).2
    rw [hchain, ht_mfderiv]
    have harg :
        ((ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
            (leviCivitaGeodesicSprayChart (I := I) g x0 (f t))) 1) =
          leviCivitaGeodesicSprayChart (I := I) g x0 (f t) := by
      simp [ContinuousLinearMap.smulRight_apply]
    have hproj_arg :
        (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f t))
          ((ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
            (leviCivitaGeodesicSprayChart (I := I) g x0 (f t))) 1) =
        (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f t))
          (leviCivitaGeodesicSprayChart (I := I) g x0 (f t)) :=
      congrArg
        (fun z =>
          (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M -> M) (f t)) z) harg
    refine hproj_arg.trans ?_
    exact mfderiv_proj_leviCivitaGeodesicSprayChart
      (I := I) g x0 (f t) hsrc_t
  refine TotalSpace.ext ?_ ?_
  · simp [curveVelocityBundle]
  · simp [curveVelocityBundle, hvel]

/-- A local chart-fixed geodesic spray integral curve is eventually the tangent
lift of its projected curve. -/
theorem projectCurve_velocityBundle_eventually_eq_lift_of_initial
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {f : Real -> TangentBundle I M} {t0 : Real}
    (hf0 : f t0 = (⟨x, v⟩ : TangentBundle I M))
    (hf : IsMIntegralCurveAt f
      (leviCivitaGeodesicSprayChart (I := I) g x) t0) :
    ∀ᶠ t in 𝓝 t0,
      curveVelocityBundle I (projectCurve (I := I) f) t = f t := by
  have hproj_cont :
      ContinuousAt (fun t : Real => (f t).proj) t0 := by
    exact (FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt.comp hf.continuousAt
  have hsrc :
      ∀ᶠ t in 𝓝 t0, (f t).proj ∈ (extChartAt I x).source := by
    have hxsrc : (extChartAt I x).source ∈ 𝓝 ((f t0).proj) := by
      simpa [hf0] using extChartAt_source_mem_nhds (I := I) x
    exact hproj_cont.preimage_mem_nhds hxsrc
  exact projectCurve_velocityBundle_eventually_eq_lift
    (I := I) hf hsrc

/-- Local geodesic IVP in spray-integral form. -/
theorem exists_localGeodesicIVPAt_leviCivita
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ G : LocalGeodesicIVPAt (I := I) g
        (⟨x, v⟩ : TangentBundle I M), True := by
  classical
  let u : TangentBundle I M := ⟨x, v⟩
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_leviCivitaGeodesicSprayChart (I := I) g x v
  obtain ⟨epsilon, hepsilon, hf_on⟩ := isMIntegralCurveAt_iff'.mp hf
  refine ⟨{
    epsilon := epsilon
    epsilon_pos := hepsilon
    lift := f
    gamma := projectCurve (I := I) f
    lift_initial := by simpa [u] using hf0
    projects := ?_
    spray_integral := ?_
    initial_position := ?_
    initial_velocity := ?_
  }, trivial⟩
  · intro t ht
    rfl
  · simpa [u] using hf_on
  · simpa [u] using projectCurve_zero_of_lift (I := I) (u := u) (by simpa [u] using hf0)
  · exact projectCurve_initialVelocity_of_geodesicSprayIntegral
      (I := I) (g := g) (u := u) (f := f) (by simpa [u] using hf0)
      (by simpa [u] using hf)

/-- User-facing local geodesic existence statement, with explicit epsilon,
initial point, initial velocity, and a tangent-bundle lift solving the spray
ODE on the local ball. -/
theorem exists_local_geodesic_leviCivita
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ epsilon > 0, ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        ∃ lift : Real -> TangentBundle I M,
          IsMIntegralCurveOn lift
            (leviCivitaGeodesicSprayChart (I := I) g x)
            (Metric.ball (0 : Real) epsilon) := by
  classical
  obtain ⟨G, -⟩ := exists_localGeodesicIVPAt_leviCivita (I := I) g x v
  refine ⟨G.epsilon, G.epsilon_pos, G.gamma, ?_, ?_, G.lift, ?_⟩
  · simpa using G.initial_position
  · simpa using G.initial_velocity
  · simpa using G.spray_integral

end Lecture07
end GlobalGeometry
end RicciFlower
