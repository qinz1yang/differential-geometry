import RicciFlower.Coordinates.Normal.Data

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smooth endpoint frontier for the coordinate exponential map

This file isolates the remaining smooth-dependence theorem for the fixed-chart
geodesic endpoint.  The default normal-coordinate API uses the checked C1
endpoint package; this frontier upgrades the same endpoint package from C1 to
`C^∞`.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open Set Function
open scoped Manifold ContDiff Topology
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-- Compose smooth phase-endpoint dependence with the smooth initial-phase map
to get smoothness of the fixed-chart tangent endpoint. -/
private theorem chartEnd_smoothOn
    [I.Boundaryless]
    (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (τ : Real)
    (hbase :
      ∃ w : Set (ModelPhase (E := E)),
        IsOpen w ∧
          initPhase (I := I) x (0 : TangentSpace I x) ∈ w ∧
          ContDiffOn Real ∞ (fun z => timeBaseEndpoint (E := E) Ψ τ z) w) :
    ∃ u : Set (TangentSpace I x), IsOpen u ∧
      (0 : TangentSpace I x) ∈ u ∧
      ContDiffOn Real ∞
        (chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x) u := by
  classical
  obtain ⟨w, hwOpen, h0w, hbaseSmooth⟩ := hbase
  let scaleCLM : TangentSpace I x →L[Real] TangentSpace I x :=
    (τ⁻¹) • ContinuousLinearMap.id Real (TangentSpace I x)
  let ρ : TangentSpace I x -> ModelPhase (E := E) :=
    fun v => initPhase (I := I) x (scaleCLM v)
  let u : Set (TangentSpace I x) := ρ ⁻¹' w
  refine ⟨u, ?_, ?_, ?_⟩
  · have hρcont : Continuous ρ := by
      have hinitSmooth : ContDiff Real ∞ (initPhase (I := I) x) :=
        contDiff_iff_contDiffAt.mpr
          (fun v => initPhase_contDiffAt (I := I) (n := (∞ : WithTop ℕ∞)) x v)
      have hinit : Continuous (initPhase (I := I) x) := hinitSmooth.continuous
      exact hinit.comp scaleCLM.continuous
    exact hwOpen.preimage hρcont
  · simpa [u, ρ, scaleCLM, initPhase_zero] using h0w
  · have hinitSmooth : ContDiff Real ∞ (initPhase (I := I) x) :=
      contDiff_iff_contDiffAt.mpr
        (fun v => initPhase_contDiffAt (I := I) (n := (∞ : WithTop ℕ∞)) x v)
    have hρSmooth : ContDiff Real ∞ ρ := by
      simpa [ρ] using hinitSmooth.comp scaleCLM.contDiff
    have hcomp :
        ContDiffOn Real ∞
          (fun v : TangentSpace I x =>
            timeBaseEndpoint (E := E) Ψ τ (ρ v)) u :=
      hbaseSmooth.comp hρSmooth.contDiffOn (by intro v hv; exact hv)
    simpa [chartEnd_varModelFlow_eq_scaledBaseEnd, scaledBaseEnd, ρ, scaleCLM]
      using hcomp

/-- Smooth endpoint package for the chart-fixed variational-flow endpoint.

This is the precise remaining producer needed before transporting the endpoint
to the manifold exponential map.  All relation-valued endpoint facts are already
supplied by `exists_varFlow_c1_endpoint`; the frontier is the smooth local
diffeomorphism package for the fixed-chart endpoint. -/
theorem exists_varFlow_smooth_endpoint
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
          (∃ (a r : NNReal), 0 < r ∧
            (∀ z ∈ Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) r,
              varModelFlow (E := E) Ψ z 0 = z ∧
                ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
                  HasDerivWithinAt
                    (varModelFlow (E := E) Ψ z)
                    (modelSpray (I := I) g x
                      (varModelFlow (E := E) Ψ z t))
                    (Set.Icc (-(2 * τ)) (2 * τ)) t) ∧
            (∀ z ∈ Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) r,
              ∀ t : Real,
                varModelFlow (E := E) Ψ z t ∈
                  Metric.closedBall
                    (extChartAt I.tangent (phaseZero (I := I) x)
                      (phaseZero (I := I) x)) a) ∧
            (∀ z ∈ Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) r,
              ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
                varModelFlow (E := E) Ψ z t ∈
                  (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                  (phaseOfModel (I := I) x
                    (varModelFlow (E := E) Ψ z t)).proj ∈
                    (extChartAt I x).source)) ∧
          ∃ chartLD :
            PartialDiffeomorph
              (modelWithCornersSelf Real (TangentSpace I x))
              (modelWithCornersSelf Real (TangentSpace I x))
              (TangentSpace I x) (TangentSpace I x) (∞ : WithTop ℕ∞),
            (0 : TangentSpace I x) ∈ chartLD.source ∧
              chartLD.source ⊆ Metric.ball (0 : TangentSpace I x) R ∧
              ∀ v : TangentSpace I x, v ∈ chartLD.source ->
                chartLD v =
                  chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x v := by
  classical
  obtain ⟨ε, hε, δ0, hδ0, a, rModel, hrModel, Ψ, hflow, hbound, hsrc,
      hzeroConstAug, L', hLip, hBaseDeriv⟩ :=
    varFlow_deriv0 (I := I) g x
  let δ : Real := min δ0 ε
  have hδ : 0 < δ := lt_min hδ0 hε
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  let p0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  let Φ : VarPhase (E := E) × Real -> VarPhase (E := E) :=
    fun q => Ψ q.1 q.2
  let F : Real -> VarPhase (E := E) -> VarPhase (E := E) :=
    fun _ => varSpray (I := I) g x
  have hδsub : Set.Icc (-δ) δ ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, hδε]
  have hΦflowδ :
      RicciFlower.Analysis.ODE.Flow.IsLocalFlow
        F 0 p0 rModel (-δ) δ Φ := by
    have hcont :
        ContinuousOn Φ
          (Metric.closedBall p0 (rModel : Real) ×ˢ Set.Icc (-δ) δ) := by
      apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ (fun t ht => hLip t (hδsub ht))
      intro p hp
      exact (HasDerivWithinAt.continuousOn (hflow p hp).2).mono hδsub
    refine
    { htmin_le := by linarith [hδ],
      ht₀_le := by linarith [hδ],
      apply_initial := ?_,
      hasDerivWithinAt := ?_,
      continuousOn := hcont,
      exists_lipschitz := ?_ }
    · intro p hp
      simpa [Φ, p0] using (hflow p hp).1
    · intro p hp t ht
      simpa [Φ, F] using ((hflow p hp).2 t (hδsub ht)).mono hδsub
    · exact ⟨L', by
        intro t ht
        exact hLip t (hδsub ht)⟩
  let Ω : Set (Real × VarPhase (E := E)) :=
    Set.univ ×ˢ varSource (I := I) (E := E) x
  have hΩopen : IsOpen Ω := by
    simpa [Ω] using isOpen_univ.prod (isOpen_varSource (I := I) (E := E) x)
  have hΩsmooth :
      ContDiffOn Real ∞ (Function.uncurry F) Ω := by
    simpa [F, Ω, Function.uncurry] using
      varSpray_time_cdOn (I := I) g x
  have hΩflowδ :
      ∀ p ∈ Metric.closedBall p0 (rModel : Real), ∀ t ∈ Set.Icc (-δ) δ,
        (t, Φ (p, t)) ∈ Ω := by
    intro p hp t _ht
    have hpsrc : Ψ p t ∈ varSource (I := I) (E := E) x := by
      simpa [varSource, p0] using hsrc (hbound p hp t)
    exact ⟨Set.mem_univ _, by simpa [Φ] using hpsrc⟩
  have hΩone : ContDiffOn Real 1 (Function.uncurry F) Ω := by
    exact hΩsmooth.of_le (by norm_num)
  have hsub_delta :
      Set.Icc (0 - δ) (0 + δ) ⊆ Set.Icc (-δ) δ := by
    intro t ht
    simpa using ht
  obtain ⟨B, hB, hBbdδ⟩ :=
    RicciFlower.Analysis.ODE.Flow.exists_fderiv_bound_on_flow_tube_local
      (f := F) (t₀ := 0) (x₀ := p0) (r := rModel)
      (tmin := -δ) (tmax := δ) (Φ := Φ)
      hΦflowδ hΩopen hΩone hΩflowδ (T := δ) (ρ := (rModel : Real))
      hsub_delta le_rfl
  let Tcap : Real := min δ (1 / (2 * (B + 1)))
  have hTcap_pos : 0 < Tcap := by
    dsimp [Tcap]
    exact lt_min hδ (by positivity)
  let T_out : Real := Tcap / 2
  let T_mid : Real := Tcap / 4
  let T : Real := Tcap / 8
  have hT_pos : 0 < T := by
    dsimp [T]
    linarith [hTcap_pos]
  have hT_lt_mid : T < T_mid := by
    dsimp [T, T_mid]
    linarith [hTcap_pos]
  have hT_mid_lt_out : T_mid < T_out := by
    dsimp [T_mid, T_out]
    linarith [hTcap_pos]
  have hT_out_le_delta : T_out ≤ δ := by
    dsimp [T_out, Tcap]
    have hcap : min δ (1 / (2 * (B + 1))) ≤ δ := min_le_left _ _
    linarith
  have hT_le_delta : T ≤ δ := by
    dsimp [T, Tcap]
    have hcap : min δ (1 / (2 * (B + 1))) ≤ δ := min_le_left _ _
    linarith
  have hT_out_sub_delta :
      Set.Icc (0 - T_out) (0 + T_out) ⊆ Set.Icc (-δ) δ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, hT_out_le_delta]
  have hTsub_eps :
      Set.Icc (0 - T_out) (0 + T_out) ⊆ Set.Icc (-ε) ε :=
    hT_out_sub_delta.trans hδsub
  have hBT_mid : B * T_mid < 1 := by
    have h_cap_le : Tcap ≤ 1 / (2 * (B + 1)) := by
      dsimp [Tcap]
      exact min_le_right _ _
    have hT_mid_le : T_mid ≤ 1 / (8 * (B + 1)) := by
      dsimp [T_mid]
      have hstep : Tcap / 4 ≤ (1 / (2 * (B + 1))) / 4 := by linarith
      have heq : (1 / (2 * (B + 1))) / 4 = 1 / (8 * (B + 1)) := by
        field_simp
        ring
      linarith
    have hden : (0 : Real) < 8 * (B + 1) := by positivity
    calc B * T_mid ≤ B * (1 / (8 * (B + 1))) :=
            mul_le_mul_of_nonneg_left hT_mid_le hB
      _ = B / (8 * (B + 1)) := by ring
      _ ≤ 1 / 8 := by
            rw [div_le_div_iff₀ hden (by norm_num : (0 : Real) < 8)]
            nlinarith [hB]
      _ < 1 := by norm_num
  let ρ_out : NNReal := ⟨(rModel : Real) / 2, by positivity⟩
  let ρ_mid : NNReal := ⟨(rModel : Real) / 4, by positivity⟩
  let ρVar : NNReal := ⟨(rModel : Real) / 8, by positivity⟩
  let r' : NNReal := ⟨(rModel : Real) / 8, by positivity⟩
  have hr'_pos : 0 < r' := by
    dsimp [r']
    change (0 : Real) < (rModel : Real) / 8
    positivity
  have hρVar_pos : 0 < (ρVar : Real) := by
    dsimp [ρVar]
    change (0 : Real) < (rModel : Real) / 8
    positivity
  have hρ_lt_mid : (ρVar : Real) < (ρ_mid : Real) := by
    dsimp [ρVar, ρ_mid]
    change (rModel : Real) / 8 < (rModel : Real) / 4
    have hrReal : (0 : Real) < (rModel : Real) := by exact_mod_cast hrModel
    linarith
  have hρ_mid_lt_out : (ρ_mid : Real) < (ρ_out : Real) := by
    dsimp [ρ_mid, ρ_out]
    change (rModel : Real) / 4 < (rModel : Real) / 2
    have hrReal : (0 : Real) < (rModel : Real) := by exact_mod_cast hrModel
    linarith
  have hρρ' : (ρ_mid : Real) + (r' : Real) ≤ (rModel : Real) := by
    dsimp [ρ_mid, r']
    change (rModel : Real) / 4 + (rModel : Real) / 8 ≤ (rModel : Real)
    have hrReal : (0 : Real) ≤ (rModel : Real) := by exact_mod_cast (le_of_lt hrModel)
    linarith
  have hρ_out_le_r : (ρ_out : Real) ≤ (rModel : Real) := by
    dsimp [ρ_out]
    change (rModel : Real) / 2 ≤ (rModel : Real)
    have hrReal : (0 : Real) ≤ (rModel : Real) := by exact_mod_cast (le_of_lt hrModel)
    linarith
  have hA_bd :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) (ρ_out : Real),
        ∀ t ∈ Set.Icc (0 - T_out) (0 + T_out),
          ‖fderiv Real (varSpray (I := I) g x) (Ψ p t)‖ ≤ B := by
    intro p hp t ht
    have htδ : t ∈ Set.Icc (0 - δ) (0 + δ) := by
      simpa using hT_out_sub_delta ht
    exact hBbdδ p (Metric.closedBall_subset_closedBall hρ_out_le_r hp) t htδ
  obtain ⟨ρ, hρ, hsmall⟩ := initPhase_small (I := I) x hrModel
  let τ : Real := T / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    linarith [hT_pos]
  have hτδ : τ ≤ δ := by
    dsimp [τ]
    linarith [hT_le_delta]
  have htwoτ_le_delta : 2 * τ ≤ δ := by
    dsimp [τ]
    linarith [hT_le_delta]
  have htwoτ_le : 2 * τ ≤ ε := by
    linarith [htwoτ_le_delta, hδε]
  have hτT : τ ∈ Set.Ioo (0 - T) (0 + T) := by
    dsimp [τ]
    constructor <;> linarith [hT_pos]
  have h2τ_pos : 0 < 2 * τ := by positivity
  have hsub : Set.Icc (-(2 * τ)) (2 * τ) ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, htwoτ_le]
  have hflowAugSmall :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) rModel,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-(2 * τ)) (2 * τ)) t := by
    intro p hp
    refine ⟨(hflow p hp).1, ?_⟩
    intro t ht
    exact ((hflow p hp).2 t (hsub ht)).mono hsub
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
    exact varModelFlow_flow (I := I) (E := E) g x hflowAugSmall
  have hsrcSmall :
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel,
        ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
          varModelFlow (E := E) Ψ z t ∈
            (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x (varModelFlow (E := E) Ψ z t)).proj ∈
              (extChartAt I x).source := by
    exact varModelFlow_src (I := I) (E := E) x hbound hsrc
  have hLipSmall :
      ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) rModel) := by
    intro t ht
    exact hLip t (hsub ht)
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  have hzero :
      manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
          (0 : TangentSpace I x) = x := by
    have hτsmall : τ ∈ Set.Icc (-(2 * τ)) (2 * τ) := by
      constructor <;> linarith
    have hzeroSmall :
        ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
          varModelFlow (E := E) Ψ
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) t =
            extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x) := by
      intro t ht
      have hzeroAug :=
        hzeroConstAug t ⟨by linarith [ht.1, htwoτ_le_delta],
          by linarith [ht.2, htwoτ_le_delta]⟩
      simpa [varModelFlow, varZeroPhaseLin, varPhaseZero] using
        congrArg Prod.fst hzeroAug
    exact manifoldEnd_zero (I := I)
      (α := varModelFlow (E := E) Ψ) (ε := 2 * τ) (τ := τ)
      x hτsmall hzeroSmall
  have hreal :
      ∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
        expAt (I := I) g x v
          (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v) := by
    intro v hv
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
  have hchart :
      ∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
        extChartAt I x
          (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v) =
            chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x v := by
    intro v hv
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
  have hderiv :
      HasFDerivAt
        (chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x)
        (ContinuousLinearMap.id Real (TangentSpace I x)) 0 :=
    chartEnd_varModelFlow_deriv0 (I := I) (E := E) (Ψ := Ψ)
      (x := x) (b := τ)
      (scaledBaseEnd_deriv0 (I := I) (E := E) (Ψ := Ψ) (x := x)
        (b := τ) hτ.ne'
        (hBaseDeriv τ ⟨le_of_lt hτ, le_trans hτδ hδδ0⟩))
  have hboundSmall :
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel,
        ∀ t : Real,
          varModelFlow (E := E) Ψ z t ∈
            Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) a :=
    varModelFlow_bound (I := I) (E := E) x hbound
  refine ⟨R, hR, τ, hτ, Ψ, hzero, hreal, hchart, ?_, ?_⟩
  · exact ⟨a, rModel, hrModel, hflowSmall, hboundSmall, hsrcSmall⟩
  let chartExp : TangentSpace I x -> TangentSpace I x :=
    chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x
  obtain ⟨w, hwOpen, h0w, _hwSub, hbaseSmooth⟩ :=
    timeBaseEnd_smoothOn (I := I) g x Ψ
      (ε := ε) (τ := τ) (a := a) (r := rModel) (L' := L')
      hrModel hτT hT_pos hT_lt_mid hT_mid_lt_out hB hBT_mid hTsub_eps
      hr'_pos hρVar_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r
      hflow hbound hsrc hLip hA_bd
  obtain ⟨u, hu_open, h0u, hCInftyOn_raw⟩ :=
    chartEnd_smoothOn (I := I) (E := E) x Ψ τ
      ⟨w, hwOpen, h0w, hbaseSmooth⟩
  have hCInftyOn : ContDiffOn Real ∞ chartExp u := by
    simpa [chartExp] using hCInftyOn_raw
  -- Half 1: smooth inverse-function theorem.
  have hCInfty : ContDiffAt Real ∞ chartExp (0 : TangentSpace I x) :=
    hCInftyOn.contDiffAt (hu_open.mem_nhds h0u)
  let eIso : TangentSpace I x ≃L[Real] TangentSpace I x :=
    ContinuousLinearEquiv.refl Real (TangentSpace I x)
  have hderivIso :
      HasFDerivAt chartExp (eIso : TangentSpace I x →L[Real] TangentSpace I x)
        (0 : TangentSpace I x) := by
    simpa [chartExp, eIso] using hderiv
  let eIFT : OpenPartialHomeomorph (TangentSpace I x) (TangentSpace I x) :=
    ContDiffAt.toOpenPartialHomeomorph (𝕂 := Real)
      (f := chartExp) (f' := eIso) hCInfty hderivIso (by simp)
  have heIFT_coe : (eIFT : TangentSpace I x -> TangentSpace I x) = chartExp := rfl
  have hIFTsrc : (0 : TangentSpace I x) ∈ eIFT.source := by
    simpa [eIFT] using
      ContDiffAt.mem_toOpenPartialHomeomorph_source hCInfty hderivIso (by simp)
  -- The derivative of `chartExp` is invertible on a neighborhood of `0`:
  -- at `0` it is the identity, and invertibility is an open condition.
  have hfderiv0 :
      fderiv Real chartExp (0 : TangentSpace I x)
        = (eIso : TangentSpace I x →L[Real] TangentSpace I x) :=
    hderivIso.fderiv
  have hcontDeriv : ContinuousAt (fderiv Real chartExp) (0 : TangentSpace I x) :=
    hCInfty.continuousAt_fderiv (by simp)
  have hUnit0 : IsUnit (fderiv Real chartExp (0 : TangentSpace I x)) := by
    rw [hfderiv0]
    exact ⟨ContinuousLinearEquiv.toUnit eIso, rfl⟩
  have hUnitOpen :
      IsOpen
        {T : TangentSpace I x →L[Real] TangentSpace I x | IsUnit T} :=
    Units.isOpen
  have hpre_nhds :
      (fderiv Real chartExp) ⁻¹' {T | IsUnit T} ∈ 𝓝 (0 : TangentSpace I x) :=
    hcontDeriv.preimage_mem_nhds (hUnitOpen.mem_nhds hUnit0)
  obtain ⟨w, hw_sub, hw_open, h0w⟩ := mem_nhds_iff.mp hpre_nhds
  let s : Set (TangentSpace I x) :=
    Metric.ball (0 : TangentSpace I x) R ∩ (u ∩ (w ∩ eIFT.source))
  have hsOpen : IsOpen s :=
    Metric.isOpen_ball.inter (hu_open.inter (hw_open.inter eIFT.open_source))
  have hsSubSource : s ⊆ eIFT.source := fun v hv => hv.2.2.2
  have hsSubBall :
      s ⊆ Metric.ball (0 : TangentSpace I x) R := fun v hv => hv.1
  have hsSubU : s ⊆ u := fun v hv => hv.2.1
  have hsSubW : s ⊆ w := fun v hv => hv.2.2.1
  have h0s : (0 : TangentSpace I x) ∈ s :=
    ⟨Metric.mem_ball_self hR, h0u, h0w, hIFTsrc⟩
  have hforward :
      ContMDiffOn
        (modelWithCornersSelf Real (TangentSpace I x))
        (modelWithCornersSelf Real (TangentSpace I x))
        (∞ : WithTop ℕ∞) eIFT s := by
    have hf : ContDiffOn Real ∞ eIFT s := by
      simpa [heIFT_coe] using hCInftyOn.mono hsSubU
    exact hf.contMDiffOn
  have hinverse :
      ContMDiffOn
        (modelWithCornersSelf Real (TangentSpace I x))
        (modelWithCornersSelf Real (TangentSpace I x))
        (∞ : WithTop ℕ∞) eIFT.symm (eIFT '' s) := by
    rintro y ⟨v, hv, rfl⟩
    have hvU : v ∈ u := hsSubU hv
    have hvSrc : v ∈ eIFT.source := hsSubSource hv
    have hUnitv : IsUnit (fderiv Real chartExp v) := hw_sub (hsSubW hv)
    have hcdv : ContDiffAt Real ∞ chartExp v :=
      hCInftyOn.contDiffAt (hu_open.mem_nhds hvU)
    have hdiffv : DifferentiableAt Real chartExp v :=
      hcdv.differentiableAt (by simp)
    -- Package the invertible derivative as a continuous linear equivalence.
    let ev : TangentSpace I x ≃L[Real] TangentSpace I x :=
      ContinuousLinearEquiv.ofUnit hUnitv.unit
    have hev_coe :
        (ev : TangentSpace I x →L[Real] TangentSpace I x)
          = fderiv Real chartExp v := by
      ext z
      change (hUnitv.unit : TangentSpace I x →L[Real] TangentSpace I x) z
        = fderiv Real chartExp v z
      rw [hUnitv.unit_spec]
    have hFDerivv :
        HasFDerivAt chartExp
          (ev : TangentSpace I x →L[Real] TangentSpace I x) v := by
      rw [hev_coe]; exact hdiffv.hasFDerivAt
    have hsymm : eIFT.symm (eIFT v) = v := eIFT.left_inv hvSrc
    have hFDeriv_eIFT :
        HasFDerivAt (eIFT : TangentSpace I x -> TangentSpace I x)
          (ev : TangentSpace I x →L[Real] TangentSpace I x)
          (eIFT.symm (eIFT v)) := by
      rw [hsymm, heIFT_coe]; exact hFDerivv
    have hcd_eIFT :
        ContDiffAt Real ∞ (eIFT : TangentSpace I x -> TangentSpace I x)
          (eIFT.symm (eIFT v)) := by
      rw [hsymm, heIFT_coe]; exact hcdv
    have hsymmCD : ContDiffAt Real ∞ eIFT.symm (eIFT v) :=
      eIFT.contDiffAt_symm (f₀' := ev) (eIFT.map_source hvSrc)
        hFDeriv_eIFT hcd_eIFT
    exact hsymmCD.contMDiffAt.contMDiffWithinAt
  let chartLD :
      PartialDiffeomorph
        (modelWithCornersSelf Real (TangentSpace I x))
        (modelWithCornersSelf Real (TangentSpace I x))
        (TangentSpace I x) (TangentSpace I x) (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.ofOpenPartialHomeomorphRestr
      (I := modelWithCornersSelf Real (TangentSpace I x))
      (J := modelWithCornersSelf Real (TangentSpace I x))
      eIFT s hsOpen hsSubSource hforward hinverse
  refine ⟨chartLD, ?_, ?_, ?_⟩
  · simpa [chartLD, PartialDiffeomorph.ofOpenPartialHomeomorphRestr] using h0s
  · intro v hv
    have hvs : v ∈ s := by
      simpa [chartLD, PartialDiffeomorph.ofOpenPartialHomeomorphRestr] using hv
    exact hsSubBall hvs
  · intro v hv
    have hvs : v ∈ s := by
      simpa [chartLD, PartialDiffeomorph.ofOpenPartialHomeomorphRestr] using hv
    calc
      chartLD v = eIFT v := rfl
      _ = chartExp v := rfl
      _ = chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x v := rfl

end Coordinates
end RicciFlower
