import RicciFlower.Coordinates.Normal.SmoothFlow

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

/-- The functional model endpoint realizes the relation-valued exponential
wherever the rescaled initial phase lies in the Picard-Lindelof ball. -/
theorem end_expAt
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

/-- A projected C1 variational flow gives a functional local endpoint realizing
`expAt`, and its fixed-chart endpoint has derivative `id` at zero.

This is the endpoint-facing consumer of `varFlow_chartEndDeriv0`: it packages
the C1 model-flow dependence into an actual local endpoint map, without
claiming a smooth local diffeomorphism. -/
theorem exists_varFlow_endpoint
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    ∃ R > 0, ∃ τ > 0,
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
          expAt (I := I) g x v
            (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v)) ∧
          HasFDerivAt
            (chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x)
            (ContinuousLinearMap.id Real (TangentSpace I x)) 0 := by
  classical
  obtain ⟨ε, hε, δ, hδ, rModel, hrModel, Ψ, hflow, hsrc, _hzero, _L', _hLip, hderiv⟩ :=
    varFlow_chartEndDeriv0 (I := I) g x
  obtain ⟨ρ, hρ, hsmall⟩ := initPhase_small (I := I) x hrModel
  let τ : Real := min δ (ε / 2) / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    exact half_pos (lt_min hδ (half_pos hε))
  have hτδ : τ ≤ δ := by
    dsimp [τ]
    have hmin : min δ (ε / 2) ≤ δ := min_le_left _ _
    linarith
  have hτIoc : τ ∈ Set.Ioc (0 : Real) δ := ⟨hτ, hτδ⟩
  have htwoτ_le : 2 * τ ≤ ε := by
    dsimp [τ]
    have hmin : min δ (ε / 2) ≤ ε / 2 := min_le_right _ _
    linarith
  have h2τ_pos : 0 < 2 * τ := by positivity
  have hsub : Set.Icc (-(2 * τ)) (2 * τ) ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, htwoτ_le]
  have hflowSmall :
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel,
        varModelFlow (E := E) Ψ z 0 = z ∧
          ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
            HasDerivWithinAt
              (varModelFlow (E := E) Ψ z)
              (modelSpray (I := I) g x
                (varModelFlow (E := E) Ψ z t))
              (Set.Icc (-(2 * τ)) (2 * τ)) t := by
    intro z hz
    refine ⟨(hflow z hz).1, ?_⟩
    intro t ht
    exact ((hflow z hz).2 t (hsub ht)).mono hsub
  have hsrcSmall :
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel,
        ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
          varModelFlow (E := E) Ψ z t ∈
            (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x (varModelFlow (E := E) Ψ z t)).proj ∈
              (extChartAt I x).source := by
    intro z hz t ht
    exact hsrc z hz t (hsub ht)
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  refine ⟨R, hR, τ, hτ, Ψ, ?_, ?_⟩
  · intro v hv
    let u : TangentSpace I x := τ⁻¹ • v
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
    have hvsmall :
        initPhase (I := I) x (((2 * τ) / 2)⁻¹ • v) ∈
          Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) rModel := by
      have hhalf : (2 * τ) / 2 = τ := by ring
      simpa [hhalf, u] using hsmall u hu
    simpa using
      end_expAt (I := I) (g := g) (x := x)
        (ε := 2 * τ) h2τ_pos (r := rModel)
        (α := varModelFlow (E := E) Ψ)
        hflowSmall hsrcSmall hvsmall
  · exact hderiv τ hτIoc

/-- A projected C1 variational flow gives a functional local endpoint realizing
`expAt`; its fixed-chart endpoint is `C1` and has derivative `id` at zero.

This is the C1 endpoint package needed before applying a smooth inverse
function theorem.  It still does not claim a smooth `PartialDiffeomorph`. -/
theorem exists_varFlow_c1_endpoint
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    ∃ R > 0, ∃ τ > 0,
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
            (0 : TangentSpace I x) = x ∧
        (∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
          expAt (I := I) g x v
            (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v)) ∧
          (∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
            extChartAt I x
              (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v) =
                chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x v) ∧
          ContDiffAt Real 1
            (chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x) 0 ∧
          HasFDerivAt
            (chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x)
            (ContinuousLinearMap.id Real (TangentSpace I x)) 0 := by
  classical
  obtain ⟨ε, hε, δ, hδ, rModel, hrModel, Ψ, hflow, hsrc, hzero, _L', _hLip, hC1deriv⟩ :=
    varFlow_chartEndC1 (I := I) g x
  obtain ⟨ρ, hρ, hsmall⟩ := initPhase_small (I := I) x hrModel
  let τ : Real := min δ (ε / 2) / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    exact half_pos (lt_min hδ (half_pos hε))
  have hτδ : τ ≤ δ := by
    dsimp [τ]
    have hmin : min δ (ε / 2) ≤ δ := min_le_left _ _
    linarith
  have htwoτ_le_delta : 2 * τ ≤ δ := by
    dsimp [τ]
    have hmin : min δ (ε / 2) ≤ δ := min_le_left _ _
    linarith
  have hτIoc : τ ∈ Set.Ioc (0 : Real) δ := ⟨hτ, hτδ⟩
  have htwoτ_le : 2 * τ ≤ ε := by
    dsimp [τ]
    have hmin : min δ (ε / 2) ≤ ε / 2 := min_le_right _ _
    linarith
  have h2τ_pos : 0 < 2 * τ := by positivity
  have hsub : Set.Icc (-(2 * τ)) (2 * τ) ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, htwoτ_le]
  have hflowSmall :
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel,
        varModelFlow (E := E) Ψ z 0 = z ∧
          ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
            HasDerivWithinAt
              (varModelFlow (E := E) Ψ z)
              (modelSpray (I := I) g x
                (varModelFlow (E := E) Ψ z t))
              (Set.Icc (-(2 * τ)) (2 * τ)) t := by
    intro z hz
    refine ⟨(hflow z hz).1, ?_⟩
    intro t ht
    exact ((hflow z hz).2 t (hsub ht)).mono hsub
  have hsrcSmall :
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel,
        ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
          varModelFlow (E := E) Ψ z t ∈
            (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x (varModelFlow (E := E) Ψ z t)).proj ∈
              (extChartAt I x).source := by
    intro z hz t ht
    exact hsrc z hz t (hsub ht)
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  refine ⟨R, hR, τ, hτ, Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · have hτsmall : τ ∈ Set.Icc (-(2 * τ)) (2 * τ) := by
      constructor <;> linarith
    have hzeroSmall :
        ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
          varModelFlow (E := E) Ψ
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) t =
            extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x) := by
      intro t ht
      exact hzero t ⟨by linarith [ht.1, htwoτ_le_delta],
        by linarith [ht.2, htwoτ_le_delta]⟩
    exact manifoldEnd_zero (I := I)
      (α := varModelFlow (E := E) Ψ) (ε := 2 * τ) (τ := τ)
      x hτsmall hzeroSmall
  · intro v hv
    let u : TangentSpace I x := τ⁻¹ • v
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
    have hvsmall :
        initPhase (I := I) x (((2 * τ) / 2)⁻¹ • v) ∈
          Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) rModel := by
      have hhalf : (2 * τ) / 2 = τ := by ring
      simpa [hhalf, u] using hsmall u hu
    simpa using
      end_expAt (I := I) (g := g) (x := x)
        (ε := 2 * τ) h2τ_pos (r := rModel)
        (α := varModelFlow (E := E) Ψ)
        hflowSmall hsrcSmall hvsmall
  · intro v hv
    let u : TangentSpace I x := τ⁻¹ • v
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
    have hvsmall :
        initPhase (I := I) x (((2 * τ) / 2)⁻¹ • v) ∈
          Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) rModel := by
      have hhalf : (2 * τ) / 2 = τ := by ring
      simpa [hhalf, u] using hsmall u hu
    have hτsmall : τ ∈ Set.Icc (-(2 * τ)) (2 * τ) := by
      constructor <;> linarith
    have htarget :
        varModelFlow (E := E) Ψ
            (initPhase (I := I) x (τ⁻¹ • v)) τ ∈
          (extChartAt I.tangent (phaseZero (I := I) x)).target := by
      have hhalf : (2 * τ) / 2 = τ := by ring
      simpa [hhalf] using
        (hsrcSmall
          (initPhase (I := I) x (((2 * τ) / 2)⁻¹ • v)) hvsmall
          τ hτsmall).1
    exact
      manifoldEnd_chart (I := I)
        (α := varModelFlow (E := E) Ψ) (τ := τ) x
        (v := v) htarget
  · exact (hC1deriv τ hτIoc).1
  · exact (hC1deriv τ hτIoc).2

/-- Strict derivative at zero for a functional local endpoint map.

This consumes the checked C1 variational-flow endpoint package.  The endpoint
function is the same chart-fixed endpoint used to realize `expAt` on a small
ball, so no arbitrary choice from the relation-valued API is involved. -/
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
  obtain ⟨R, hR, τ, _hτ, Ψ, hexp0, hreal, hchart, hC1, hderiv⟩ :=
    exists_varFlow_c1_endpoint (I := I) g x
  let exp : TangentSpace I x -> M :=
    manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
  let chartExp : TangentSpace I x -> TangentSpace I x :=
    chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x
  have hstrictChart :
      HasStrictFDerivAt chartExp
        (ContinuousLinearMap.id Real (TangentSpace I x)) 0 := by
    exact (by
      simpa [chartExp] using
        hC1.hasStrictFDerivAt' (by simpa [chartExp] using hderiv) one_ne_zero)
  have hEq :
      chartExp =ᶠ[𝓝 (0 : TangentSpace I x)]
        fun v : TangentSpace I x => extChartAt I x (exp v) := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds _ hR) ?_
    intro v hv
    exact (by simpa [exp, chartExp] using (hchart v hv).symm)
  refine ⟨R, hR, exp, ?_, ?_, ?_⟩
  · simpa [exp] using hexp0
  · intro v hv
    simpa [exp] using hreal v hv
  · exact hstrictChart.congr_of_eventuallyEq hEq

set_option maxHeartbeats 800000 in
/-- Legacy pairwise-integral proof of the strict endpoint theorem.

This is intentionally stated only after choosing a genuine local endpoint
function realizing `expAt` on a ball.  An arbitrary `Classical.choose` from the
relation-valued endpoint would not be smooth; the missing proof is smooth
dependence and uniqueness of the chart-fixed geodesic flow, followed by the
standard zero-velocity linearization. -/
private theorem strict_pairwise
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


end Coordinates
end RicciFlower
