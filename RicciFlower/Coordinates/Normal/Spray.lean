import RicciFlower.Coordinates.Normal.Base
import Mathlib.Analysis.Calculus.MeanValue

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

/-! ## Fixed-chart time-one frontier -/

/-- The zero phase point `0_x ∈ TM` used to chart the time-one local flow. -/
def phaseZero (x : M) : TangentBundle I M :=
  (⟨x, (0 : E)⟩ : TangentBundle I M)

/-- Initial phase coordinate in the tangent-bundle chart centered at `0_x`. -/
def initPhase (x : M) (v : TangentSpace I x) : E × E :=
  extChartAt I.tangent (phaseZero (I := I) x)
    (⟨x, v⟩ : TangentBundle I M)

/-- Interpret model coordinates in the tangent-bundle chart centered at
`0_x`. -/
def phaseOfModel (x : M) (z : E × E) : TangentBundle I M :=
  (extChartAt I.tangent (phaseZero (I := I) x)).symm z

@[simp] theorem initPhase_zero (x : M) :
    initPhase (I := I) x (0 : TangentSpace I x) =
      extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x) := by
  rfl

/-- The initial-phase chart coordinate depends continuously on the initial
velocity at the zero vector. -/
theorem initPhase_continuousAt_zero (x : M) :
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
theorem initPhase_small
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
def modelSpray
    (g : SmoothRiemannianMetric I M) (x : M) (z : E × E) : E × E :=
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  tangentCoordChange I.tangent q (phaseZero (I := I) x) q
    (leviCivitaGeodesicSprayChart (I := I) g x q)

/-- Linearization of the fixed-chart model spray at the zero phase:
`(δx, δv) ↦ (δv, 0)`. -/
def modelSprayLin : (E × E) →L[Real] (E × E) :=
  (ContinuousLinearMap.snd Real E E).prod
    (0 : (E × E) →L[Real] E)

@[simp] theorem modelSprayLin_fst (z : E × E) :
    (modelSprayLin (E := E) z).1 = z.2 := by
  rfl

@[simp] theorem modelSprayLin_snd (z : E × E) :
    (modelSprayLin (E := E) z).2 = 0 := by
  rfl

/-- Homogeneity of the quadratic Christoffel velocity term. -/
theorem sprayQuad_smul
    (g : SmoothRiemannianMetric I M) (x : M)
    (y v : E) (a : Real) (k : CoordinateIdx (𝕜 := Real) E) :
    leviCivitaGeodesicSprayQuadratic (I := I) g x y (a • v) k =
      (a * a) *
        leviCivitaGeodesicSprayQuadratic (I := I) g x y v k := by
  classical
  simp only [leviCivitaGeodesicSprayQuadratic, modelCoord, map_smul,
    Finset.mul_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Homogeneity of the model-space spray acceleration. -/
theorem sprayAccel_smul
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
theorem phaseOfModel_contMDiffAt
    [I.Boundaryless] (x : M) :
    ContMDiffAt 𝓘(Real, E × E) I.tangent ∞
      (phaseOfModel (I := I) x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  have hwithin :
      ContMDiffWithinAt 𝓘(Real, E × E) I.tangent ∞
        (extChartAt I.tangent (phaseZero (I := I) x)).symm
        (Set.range I.tangent)
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :=
    contMDiffWithinAt_extChartAt_symm_range_self
      (I := I.tangent) (x := phaseZero (I := I) x) (n := (∞ : WithTop ℕ∞))
  have hrange :
      Set.range I.tangent ∈
        𝓝 (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I.tangent)]
    exact Filter.univ_mem
  simpa [phaseOfModel] using hwithin.contMDiffAt hrange

/-- The tangent-bundle chart inverse centered at `0_x` is `C¹` at the chart
coordinate of `0_x`. -/
theorem phaseOfModel_cdAt
    [I.Boundaryless] (x : M) :
    ContMDiffAt 𝓘(Real, E × E) I.tangent 1
      (phaseOfModel (I := I) x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) :=
  (phaseOfModel_contMDiffAt (I := I) x).of_le (by norm_num)

/-- In the fixed tangent-bundle chart, the model vector field is locally the
chart-fiber RHS used to define the spray. -/
theorem modelSpray_eq_fiber
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
theorem chartPushLift_fst_eq_extChartAt_proj
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
theorem phaseOfModel_chart
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
theorem modelSpray_eq_pair
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
theorem phaseTarget_smul
    [I.Boundaryless] (x : M) {z : E × E} {a : Real}
    (hz : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target) :
    (z.1, a • z.2) ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target := by
  rw [FiberBundle.extChartAt_target] at hz ⊢
  exact ⟨hz.1, trivial⟩

/-- Scaling the fiber model coordinate keeps the reconstructed point over the
same fixed base chart source. -/
theorem phaseSrc_smul
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
def modelRescale (α : Real -> E × E) (τ : Real) : Real -> E × E :=
  fun s => ((α (τ * s)).1, τ • (α (τ * s)).2)

@[simp] theorem modelRescale_zero
    (α : Real -> E × E) (τ : Real) :
    modelRescale α τ 0 = ((α 0).1, τ • (α 0).2) := by
  simp [modelRescale]

theorem deriv_fst
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).1) F'.1 t := by
  have hfst : HasFDerivAt (ContinuousLinearMap.fst Real E E)
      (ContinuousLinearMap.fst Real E E) (F t) :=
    (ContinuousLinearMap.fst Real E E).hasFDerivAt
  simpa [Function.comp_def] using hfst.comp_hasDerivAt t hF

theorem deriv_snd
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).2) F'.2 t := by
  have hsnd : HasFDerivAt (ContinuousLinearMap.snd Real E E)
      (ContinuousLinearMap.snd Real E E) (F t) :=
    (ContinuousLinearMap.snd Real E E).hasFDerivAt
  simpa [Function.comp_def] using hsnd.comp_hasDerivAt t hF

/-- Homogeneous reparametrization for the fixed-chart model spray. -/
theorem modelRescale_deriv
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
theorem modelSol_integralOn
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
theorem initPhase_eq_pair (x : M) (v : TangentSpace I x) :
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

/-- Linear map underlying the derivative of `initPhase` in the initial
velocity.  It inserts a tangent vector as the fiber component of the fixed
phase chart. -/
def initPhaseLin (x : M) :
    TangentSpace I x →L[Real] E × E :=
  (0 : TangentSpace I x →L[Real] E).prod
    (ContinuousLinearMap.id Real (TangentSpace I x))

/-- The initial-phase chart is affine in the initial velocity. -/
theorem initPhase_hasFDerivAt (x : M) (v : TangentSpace I x) :
    HasFDerivAt
      (initPhase (I := I) x)
      (initPhaseLin (I := I) x)
      v := by
  have hconst :
      HasFDerivAt
        (fun _ : TangentSpace I x => extChartAt I x x)
        (0 : TangentSpace I x →L[Real] E) v :=
    hasFDerivAt_const (extChartAt I x x) v
  have hid :
      HasFDerivAt
        (fun v : TangentSpace I x => v)
        (ContinuousLinearMap.id Real (TangentSpace I x)) v :=
    (ContinuousLinearMap.id Real (TangentSpace I x)).hasFDerivAt
  have hfun :
      (fun v : TangentSpace I x => (extChartAt I x x, v)) =
        initPhase (I := I) x := by
    funext u
    exact (initPhase_eq_pair (I := I) x u).symm
  have hpair := hconst.prodMk hid
  rw [hfun] at hpair
  simpa [initPhaseLin] using hpair

/-- The initial-phase chart is strictly differentiable in the initial
velocity; its derivative is the fiber-inclusion linear map. -/
theorem initPhase_hasStrictFDerivAt (x : M) (v : TangentSpace I x) :
    HasStrictFDerivAt
      (initPhase (I := I) x)
      (initPhaseLin (I := I) x)
      v := by
  have hconst :
      HasStrictFDerivAt
        (fun _ : TangentSpace I x => extChartAt I x x)
        (0 : TangentSpace I x →L[Real] E) v :=
    hasStrictFDerivAt_const (extChartAt I x x) v
  have hid :
      HasStrictFDerivAt
        (fun v : TangentSpace I x => v)
        (ContinuousLinearMap.id Real (TangentSpace I x)) v :=
    (ContinuousLinearMap.id Real (TangentSpace I x)).hasStrictFDerivAt
  have hfun :
      (fun v : TangentSpace I x => (extChartAt I x x, v)) =
        initPhase (I := I) x := by
    funext u
    exact (initPhase_eq_pair (I := I) x u).symm
  have hpair := hconst.prodMk hid
  rw [hfun] at hpair
  simpa [initPhaseLin] using hpair

/-- The initial-phase chart is smooth in the initial velocity. -/
theorem initPhase_contDiffAt {n : WithTop ℕ∞} (x : M) (v : TangentSpace I x) :
    ContDiffAt Real n (initPhase (I := I) x) v := by
  have hconst :
      ContDiffAt Real n
        (fun _ : TangentSpace I x => extChartAt I x x) v :=
    contDiffAt_const
  have hid :
      ContDiffAt Real n (fun v : TangentSpace I x => v) v := by
    simpa using (contDiffAt_id : ContDiffAt Real n (id : TangentSpace I x -> TangentSpace I x) v)
  have hfun :
      (fun v : TangentSpace I x => (extChartAt I x x, v)) =
        initPhase (I := I) x := by
    funext u
    exact (initPhase_eq_pair (I := I) x u).symm
  have hpair := hconst.prodMk hid
  rw [hfun] at hpair
  exact hpair

/-- Scaling the fiber coordinate of an initial phase is the initial phase of
the scaled tangent vector. -/
theorem initPhase_smul
    (x : M) (a : Real) (v : TangentSpace I x) :
    ((initPhase (I := I) x v).1, a • (initPhase (I := I) x v).2) =
      initPhase (I := I) x (a • v) := by
  rw [initPhase_eq_pair, initPhase_eq_pair]
  rfl

theorem initPhase_sub
    (x : M) (v w : TangentSpace I x) :
    initPhase (I := I) x v - initPhase (I := I) x w =
      (0, v - w) := by
  rw [initPhase_eq_pair, initPhase_eq_pair]
  ext <;> simp
  rfl

theorem norm_initPhase_sub
    (x : M) (v w : TangentSpace I x) :
    ‖initPhase (I := I) x v - initPhase (I := I) x w‖ =
      ‖v - w‖ := by
  rw [initPhase_sub]
  change max ‖(0 : E)‖ ‖v - w‖ = ‖v - w‖
  simp [norm_nonneg]

theorem phaseZero_pair (x : M) :
    extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x) =
      (extChartAt I x x, (0 : E)) := by
  calc
    extChartAt I.tangent (phaseZero (I := I) x) (phaseZero (I := I) x)
        = initPhase (I := I) x (0 : TangentSpace I x) :=
      (initPhase_zero (I := I) x).symm
    _ = (extChartAt I x x, (0 : E)) := by
      exact initPhase_eq_pair (I := I) x (0 : TangentSpace I x)

theorem norm_initPhase_zero
    (x : M) (v : TangentSpace I x) :
    ‖initPhase (I := I) x v -
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)‖ = ‖v‖ := by
  rw [← initPhase_zero (I := I) x]
  simpa using norm_initPhase_sub (I := I) x v (0 : TangentSpace I x)

theorem half_mul_mem_Ioo
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

theorem uIcc01_mem_ball_two {t : Real}
    (ht : t ∈ Set.uIcc 0 1) :
    t ∈ Metric.ball (0 : Real) 2 := by
  rw [Metric.mem_ball]
  have hdist : dist (0 : Real) t ≤ dist (0 : Real) 1 :=
    Real.dist_left_le_of_mem_uIcc ht
  norm_num at hdist ⊢
  linarith

/-- The chart-fiber RHS, pulled back to the fixed model chart, is smooth at
`0_x`. -/
theorem sprayFiber_contDiffAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real ∞
      (fun z : E × E =>
        leviCivitaGeodesicSprayChartFiber (I := I) g x
          (phaseOfModel (I := I) x z))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  have hfiber :
      ContMDiffAt I.tangent 𝓘(Real, E × E) ∞
        (leviCivitaGeodesicSprayChartFiber (I := I) g x)
        (phaseZero (I := I) x) := by
    have htop :=
      leviCivitaGeodesicSprayChartFiber_contMDiffAt_self
        (I := I) g x (0 : TangentSpace I x)
    simpa [phaseZero] using htop
  have hphase := phaseOfModel_contMDiffAt (I := I) x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hfiber' :
      ContMDiffAt I.tangent 𝓘(Real, E × E) ∞
        (leviCivitaGeodesicSprayChartFiber (I := I) g x)
        (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hfiber
  have hcomp :
      ContMDiffAt 𝓘(Real, E × E) 𝓘(Real, E × E) ∞
        ((leviCivitaGeodesicSprayChartFiber (I := I) g x) ∘
          phaseOfModel (I := I) x)
        z0 :=
    hfiber'.comp
      (x := z0)
      hphase
  simpa [Function.comp_def, z0] using hcomp.contDiffAt

/-- The chart-fiber RHS, pulled back to the fixed model chart, is `C¹` at
`0_x`. -/
theorem sprayFiber_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (fun z : E × E =>
        leviCivitaGeodesicSprayChartFiber (I := I) g x
          (phaseOfModel (I := I) x z))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) :=
  (sprayFiber_contDiffAt (I := I) g x).of_le (by norm_num)

/-- The fixed-chart model spray is smooth at the zero phase point. -/
theorem modelSpray_contDiffAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real ∞ (modelSpray (I := I) g x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hfiber := sprayFiber_contDiffAt (I := I) g x
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
    have hphase_cont := (phaseOfModel_contMDiffAt (I := I) x).continuousAt
    simpa [z0] using hphase_cont.preimage_mem_nhds hsrc_nhds'
  refine hfiber.congr_of_eventuallyEq ?_
  filter_upwards [hsrc_event] with z hz
  exact modelSpray_eq_fiber (I := I) g x hz

/-- The fixed-chart model spray is `C¹` at the zero phase point. -/
theorem modelSpray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1 (modelSpray (I := I) g x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) :=
  (modelSpray_contDiffAt (I := I) g x).of_le (by norm_num)

/-- The scalar Christoffel quadratic term in the explicit model spray is
smooth at every base coordinate in the fixed chart target. -/
theorem sprayQuad_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hy : z.1 ∈ (extChartAt I x).target)
    (k : CoordinateIdx (𝕜 := Real) E) :
    ContDiffAt Real ∞
      (fun z : E × E =>
        leviCivitaGeodesicSprayQuadratic (I := I) g x z.1 z.2 k)
      z := by
  classical
  unfold leviCivitaGeodesicSprayQuadratic
  refine ContDiffAt.sum fun i _ => ?_
  refine ContDiffAt.sum fun j _ => ?_
  let Γ : E -> Real :=
    LeviCivita.leviCivitaChristoffelModelRHS
      (I := I) g x i j k
  have hΓWithin :=
    LeviCivita.leviCivitaChristoffelModelRHS_contDiffWithinAt_of_mem
      (I := I) g x hy i j k
  have hRange : Set.range I ∈ 𝓝 z.1 := by
    exact Filter.mem_of_superset
      ((isOpen_extChartAt_target (I := I) x).mem_nhds hy)
      (extChartAt_target_subset_range (I := I) x)
  have hΓAt : ContDiffAt Real ∞ Γ z.1 := by
    simpa [Γ] using hΓWithin.contDiffAt hRange
  have hΓ : ContDiffAt Real ∞ (fun z : E × E => Γ z.1) z :=
    hΓAt.comp z contDiffAt_fst
  have hi : ContDiffAt Real ∞ (fun z : E × E => modelCoord i z.2) z := by
    simpa [modelCoord] using
      (((Module.finBasis Real E).coord i).toContinuousLinearMap.contDiff.contDiffAt.comp
        z contDiffAt_snd)
  have hj : ContDiffAt Real ∞ (fun z : E × E => modelCoord j z.2) z := by
    simpa [modelCoord] using
      (((Module.finBasis Real E).coord j).toContinuousLinearMap.contDiff.contDiffAt.comp
        z contDiffAt_snd)
  simpa [Γ] using (hΓ.mul hi).mul hj

/-- The explicit model acceleration is smooth at every base coordinate in the
fixed chart target. -/
theorem sprayAccel_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hy : z.1 ∈ (extChartAt I x).target) :
    ContDiffAt Real ∞
      (fun z : E × E =>
        leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2)
      z := by
  classical
  unfold leviCivitaGeodesicSprayAcceleration
  refine ContDiffAt.sum fun k _ => ?_
  have hq := (sprayQuad_contDiffAt_of_mem (I := I) g x hy k).neg
  have hbasis : ContDiffAt Real ∞
      (fun _ : E × E => Module.finBasis Real E k) z :=
    contDiffAt_const
  exact hq.smul hbasis

/-- The explicit model pair `(v, -Γ(v,v))` is smooth at every base coordinate
in the fixed chart target. -/
theorem sprayPair_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hy : z.1 ∈ (extChartAt I x).target) :
    ContDiffAt Real ∞
      (fun z : E × E =>
        (z.2, leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2))
      z := by
  have hfst : ContDiffAt Real ∞ (fun z : E × E => z.2) z := contDiffAt_snd
  have hsnd := sprayAccel_contDiffAt_of_mem (I := I) g x hy
  exact hfst.prodMk hsnd

/-- The fixed-chart model spray is smooth at every controlled phase point where
the tangent chart and base chart source conditions hold. -/
theorem modelSpray_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hztarget : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source) :
    ContDiffAt Real ∞ (modelSpray (I := I) g x) z := by
  have hchart := phaseOfModel_chart (I := I) x hztarget hsrc
  have hy : z.1 ∈ (extChartAt I x).target := by
    rw [← hchart]
    exact (extChartAt I x).map_source hsrc
  have hpair := sprayPair_contDiffAt_of_mem (I := I) g x hy
  have htarget :
      (extChartAt I.tangent (phaseZero (I := I) x)).target ∈ 𝓝 z :=
    (isOpen_extChartAt_target (I := I.tangent)
      (phaseZero (I := I) x)).mem_nhds hztarget
  have hphase_cont :
      ContinuousAt (phaseOfModel (I := I) x) z := by
    simpa [phaseOfModel] using
      (continuousAt_extChartAt_symm'' (I := I.tangent) hztarget)
  have hproj :
      ContinuousAt
        (fun q : TangentBundle I M => q.proj)
        (phaseOfModel (I := I) x z) :=
    (FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt
  have hsrc_nhds :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseOfModel (I := I) x z) := by
    exact hproj.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) x).mem_nhds hsrc)
  have hsrc_event :
      ∀ᶠ z' in 𝓝 z,
        (phaseOfModel (I := I) x z').proj ∈ (extChartAt I x).source :=
    hphase_cont.preimage_mem_nhds hsrc_nhds
  have hev :
      modelSpray (I := I) g x =ᶠ[𝓝 z]
        fun z : E × E =>
          (z.2, leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2) := by
    filter_upwards [htarget, hsrc_event] with z' hz'target hz'src
    exact modelSpray_eq_pair (I := I) g x hz'target hz'src
  exact hpair.congr_of_eventuallyEq hev

/-- Mean-value Taylor residual bound for the fixed-chart model spray on a
controlled convex set. -/
theorem modelSpray_taylor_bound
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {s : Set (E × E)} (hs : Convex Real s)
    (hctrl : ∀ z ∈ s,
      z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source)
    {z w : E × E} (hz : z ∈ s) (hw : w ∈ s) {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x) z‖ ≤ C) :
    ‖modelSpray (I := I) g x w - modelSpray (I := I) g x z -
      fderiv Real (modelSpray (I := I) g x) z (w - z)‖ ≤
        C * ‖w - z‖ := by
  have hdiff : ∀ u ∈ s, DifferentiableAt Real (modelSpray (I := I) g x) u := by
    intro u hu
    exact
      (modelSpray_contDiffAt_of_mem (I := I) g x
        (hctrl u hu).1 (hctrl u hu).2).differentiableAt (by simp)
  exact hs.norm_image_sub_le_of_norm_fderiv_le'
    (f := modelSpray (I := I) g x)
    (φ := fderiv Real (modelSpray (I := I) g x) z)
    hdiff hD hz hw

/-- The fixed-chart model spray is strictly differentiable at the zero phase.

This is the direct consequence of `C¹` regularity, keeping Mathlib's `fderiv`
as the derivative.  `spray_strict_zero` below identifies this derivative with
the explicit linearization `modelSprayLin`. -/
theorem modelSpray_strictAt
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
theorem quad_fderiv_zero
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
theorem accel_fderiv_zero
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
theorem sprayPair_fderiv
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
theorem spray_fderiv_zero
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
theorem spray_strict_zero
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
theorem spray_o
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
lemma isLittleO_intervalIntegral_of_uniform_bound
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
lemma eventually_norm_integral_zero_to_t_le
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
lemma lip_norm_sub_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {K : NNReal} {s : Set X} {f : X -> Y}
    (h : LipschitzOnWith K f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f x - f y‖ ≤ (K : Real) * ‖x - y‖ := by
  simpa [dist_eq_norm] using h.dist_le_mul x hx y hy

end Coordinates
end RicciFlower
