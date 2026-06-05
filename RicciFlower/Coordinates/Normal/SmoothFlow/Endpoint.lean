import RicciFlower.Coordinates.Normal.SmoothFlow.Variational

/-!
# Endpoint adapters for the fixed-chart variational flow

This module contains the fixed-time endpoint, scaled endpoint, and chart-end
packages exported by the smooth-flow compatibility module.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Filter
open scoped Manifold ContDiff Topology Uniformity
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-- Fixed-time endpoint derivative for a source-controlled augmented flow.

This is the endpoint-facing name for `varBaseFlow_hasFDerivAt_of_flow`: the
map sending an initial phase to its fixed-time model endpoint has derivative
given by the variational component. -/
theorem timeEndpoint_hasFDerivAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      (varDerivFlow (E := E) Ψ z b)
      z :=
  varBaseFlow_hasFDerivAt_of_flow (I := I) g x Ψ z
    hb0 hb hflow hbound hsrc hLip hzopen

/-- Strict fixed-time endpoint derivative for a source-controlled augmented
flow.  This upgrades the checked C1 dependence using the fixed-time Lipschitz
dependence of the augmented Picard flow. -/
theorem timeEndpoint_hasStrictFDerivAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasStrictFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      (varDerivFlow (E := E) Ψ z b)
      z := by
  let idLin : ModelLin (E := E) :=
    ContinuousLinearMap.id Real (ModelPhase (E := E))
  have hpairCont :
      ContinuousAt (fun z' : ModelPhase (E := E) => (z', idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (f' := fun y : ModelPhase (E := E) => varDerivFlow (E := E) Ψ y b) ?_ ?_
  · have hU :
        {z' : ModelPhase (E := E) |
          (z', idLin) ∈ Metric.ball (varPhaseZero (I := I) (E := E) x) r} ∈
          𝓝 z :=
      hpairCont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
    filter_upwards [hU] with y hy
    exact timeEndpoint_hasFDerivAt (I := I) g x Ψ y hb0 hb
      hflow hbound hsrc hLip (by simpa [idLin] using hy)
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontAt :
        ContinuousAt (fun p : ModelPhase (E := E) × ModelLin (E := E) => Ψ p b)
          (z, idLin) :=
      (hLip b hbmem).continuousOn.continuousAt
        (Metric.closedBall_mem_nhds_of_mem (by simpa [idLin] using hzopen))
    have hcomp :
        ContinuousAt
          (fun z' : ModelPhase (E := E) => Ψ (z', idLin) b) z :=
      ContinuousAt.comp
        (f := fun z' : ModelPhase (E := E) => (z', idLin))
        (g := fun p : ModelPhase (E := E) × ModelLin (E := E) => Ψ p b)
        (x := z) hΨcontAt hpairCont
    simpa [varDerivFlow, idLin] using continuous_snd.continuousAt.comp hcomp

/-- Fixed-time endpoint is `C1` in the initial phase for a source-controlled
augmented variational flow. -/
theorem timeEndpoint_contDiffAt_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    ContDiffAt Real 1
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      z := by
  let idLin : ModelLin (E := E) :=
    ContinuousLinearMap.id Real (ModelPhase (E := E))
  let U : Set (ModelPhase (E := E)) :=
    {z' | (z', idLin) ∈ Metric.ball (varPhaseZero (I := I) (E := E) x) r}
  have hpairCont :
      ContinuousAt (fun z' : ModelPhase (E := E) => (z', idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine ⟨fun y : ModelPhase (E := E) => varDerivFlow (E := E) Ψ y b,
    U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : ModelPhase (E := E) × ModelLin (E := E) => Ψ p b)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : ModelPhase (E := E) => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : ModelPhase (E := E) => (y, idLin)) U
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn
          (fun y : ModelPhase (E := E) => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [varDerivFlow, idLin] using hcomp.snd
  · intro y hy
    exact timeEndpoint_hasFDerivAt (I := I) g x Ψ y hb0 hb
      hflow hbound hsrc hLip (by simpa [U, idLin] using hy)

/-- First coordinate of the fixed-time model endpoint.  This is the chart-base
coordinate that will become the normal exponential endpoint in the construction
chart. -/
def timeBaseEndpoint
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (b : Real) (z : ModelPhase (E := E)) : E :=
  (varBaseFlow (E := E) Ψ z b).1

/-- Derivative of the fixed-time base-coordinate endpoint. -/
theorem timeBaseEndpoint_hasFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {b : Real} {A : ModelLin (E := E)}
    (hA :
      HasFDerivAt
        (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
        A z) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp A)
      z := by
  have hfst :
      HasFDerivAt (fun w : ModelPhase (E := E) => w.1)
        (ContinuousLinearMap.fst Real E E) (varBaseFlow (E := E) Ψ z b) :=
    (ContinuousLinearMap.fst Real E E).hasFDerivAt
  simpa [timeBaseEndpoint, Function.comp_def] using hfst.comp z hA

/-- Strict derivative of the first coordinate of the fixed-time model
endpoint. -/
theorem timeBaseEndpoint_hasStrictFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {b : Real} {A : ModelLin (E := E)}
    (hA :
      HasStrictFDerivAt
        (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
        A z) :
    HasStrictFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp A)
      z := by
  have hfst :
      HasStrictFDerivAt (fun w : ModelPhase (E := E) => w.1)
        (ContinuousLinearMap.fst Real E E) (varBaseFlow (E := E) Ψ z b) :=
    (ContinuousLinearMap.fst Real E E).hasStrictFDerivAt
  simpa [timeBaseEndpoint, Function.comp_def] using
    HasStrictFDerivAt.comp (x := z) hfst hA

/-- `C1` regularity of the first coordinate of the fixed-time model
endpoint. -/
theorem timeBaseEndpoint_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {b : Real}
    (hA :
      ContDiffAt Real 1
        (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
        z) :
    ContDiffAt Real 1
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      z := by
  simpa [timeBaseEndpoint, Function.comp_def] using hA.fst

/-- Source-controlled version of `timeBaseEndpoint_hasFDerivAt`. -/
theorem timeBaseEndpoint_hasFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp (varDerivFlow (E := E) Ψ z b))
      z :=
  timeBaseEndpoint_hasFDerivAt (E := E)
    (timeEndpoint_hasFDerivAt (I := I) g x Ψ z
      hb0 hb hflow hbound hsrc hLip hzopen)

/-- Smooth dependence of the flat augmented variational flow on its augmented
initial condition, on an open neighborhood inside the controlled augmented
closed ball.

This is the robust self-map smooth-dependence frontier: the state space is the
plain Banach space `ModelPhase × ModelLin`, avoiding the dependent-pi
`ModelJetPrefix` coercion issue. -/
theorem varFlow_smoothOn
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ : (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
      ModelPhase (E := E) × ModelLin (E := E))
    {ε τ : Real} {a r : NNReal} {L' : NNReal}
    (_hr : 0 < r)
    {T_out T_mid T B : Real}
    (hτT : τ ∈ Set.Ioo (0 - T) (0 + T))
    (hT : 0 < T)
    (hT_lt_mid : T < T_mid)
    (hT_mid_lt_out : T_mid < T_out)
    (hB : 0 ≤ B)
    (hBT_mid : B * T_mid < 1)
    (hTsub : Set.Icc (0 - T_out) (0 + T_out) ⊆ Set.Icc (-ε) ε)
    {ρ_out ρ_mid ρ : NNReal} {r' : NNReal}
    (hr' : 0 < r')
    (hρpos : 0 < (ρ : Real))
    (hρ_lt_mid : (ρ : Real) < (ρ_mid : Real))
    (hρ_mid_lt_out : (ρ_mid : Real) < (ρ_out : Real))
    (hρρ' : (ρ_mid : Real) + (r' : Real) ≤ (r : Real))
    (hρ_out_le_r : (ρ_out : Real) ≤ (r : Real))
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hA_bd :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) (ρ_out : Real),
        ∀ t ∈ Set.Icc (0 - T_out) (0 + T_out),
          ‖fderiv Real (varSpray (I := I) g x) (Ψ p t)‖ ≤ B) :
    ∃ W : Set (ModelPhase (E := E) × ModelLin (E := E)),
      IsOpen W ∧
        varPhaseZero (I := I) (E := E) x ∈ W ∧
        W ⊆ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r ∧
        ContDiffOn Real ∞ (fun p => Ψ p τ) W := by
  classical
  let p0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  let Φ : VarPhase (E := E) × Real -> VarPhase (E := E) :=
    fun q => Ψ q.1 q.2
  let F : Real -> VarPhase (E := E) -> VarPhase (E := E) :=
    fun _ => varSpray (I := I) g x
  let W : Set (ModelPhase (E := E) × ModelLin (E := E)) :=
    Metric.ball p0 (ρ : Real)
  refine ⟨W, Metric.isOpen_ball, ?_, ?_, ?_⟩
  · exact Metric.mem_ball_self hρpos
  · intro p hp
    have hρ_le_r : (ρ : Real) ≤ (r : Real) :=
      le_trans (le_trans (le_of_lt hρ_lt_mid) (le_of_lt hρ_mid_lt_out)) hρ_out_le_r
    exact Metric.closedBall_subset_closedBall hρ_le_r (Metric.ball_subset_closedBall hp)
  · have hΦflow :
        RicciFlower.Analysis.ODE.Flow.IsLocalFlow
          F 0 p0 r (-ε) ε Φ := by
      have hT_out_pos : 0 < T_out := lt_trans (lt_trans hT hT_lt_mid) hT_mid_lt_out
      have hT_out_mem : T_out ∈ Set.Icc (0 - T_out) (0 + T_out) := by
        constructor <;> linarith
      have hεpos : 0 < ε := by
        have h := hTsub hT_out_mem
        linarith [h.2, hT_out_pos]
      have hcont :
          ContinuousOn Φ
            (Metric.closedBall p0 (r : Real) ×ˢ Set.Icc (-ε) ε) := by
        apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hLip
        intro p hp
        exact HasDerivWithinAt.continuousOn (hflow p hp).2
      refine
      { htmin_le := by linarith [hεpos],
        ht₀_le := by linarith [hεpos],
        apply_initial := ?_,
        hasDerivWithinAt := ?_,
        continuousOn := hcont,
        exists_lipschitz := ?_ }
      · intro p hp
        simpa [Φ, p0] using (hflow p hp).1
      · intro p hp t ht
        simpa [Φ, F] using (hflow p hp).2 t ht
      · exact ⟨L', by
          intro t ht
          simpa [Φ] using hLip t ht⟩
    let Ω : Set (Real × VarPhase (E := E)) :=
      Set.univ ×ˢ varSource (I := I) (E := E) x
    have hΩopen : IsOpen Ω := by
      simpa [Ω] using isOpen_univ.prod (isOpen_varSource (I := I) (E := E) x)
    have hΩsmooth :
        ContDiffOn Real ∞ (Function.uncurry F) Ω := by
      simpa [F, Ω, Function.uncurry] using
        varSpray_time_cdOn (I := I) g x
    have hΩflow :
        ∀ p ∈ Metric.closedBall p0 (r : Real), ∀ t ∈ Set.Icc (-ε) ε,
          (t, Φ (p, t)) ∈ Ω := by
      intro p hp t _ht
      have hpsrc : Ψ p t ∈ varSource (I := I) (E := E) x := by
        simpa [varSource] using hsrc (hbound p hp t)
      exact ⟨Set.mem_univ _, by simpa [Φ] using hpsrc⟩
    have hA_bd' :
        ∀ p ∈ Metric.closedBall p0 (ρ_out : Real),
          ∀ t ∈ Set.Icc (0 - T_out) (0 + T_out),
            ‖fderiv Real (F t) (Φ (p, t))‖ ≤ B := by
      intro p hp t ht
      simpa [F, Φ] using hA_bd p hp t ht
    have hjoint :
        ContDiffOn Real ∞ Φ
          (Metric.ball p0 ρ ×ˢ Set.Ioo (0 - T) (0 + T)) :=
      RicciFlower.Analysis.ODE.Flow.IsLocalFlow.contDiffOn_top_local
        (f := F) (t₀ := 0) (x₀ := p0) (r := r)
        (tmin := -ε) (tmax := ε) (Φ := Φ)
        hΦflow hΩopen hΩsmooth hΩflow hT hT_lt_mid hT_mid_lt_out
        hB hBT_mid hTsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd'
    have hconst :
        ContDiffOn Real ∞ (fun p : VarPhase (E := E) => (p, τ))
          W := by
      exact contDiff_id.contDiffOn.prodMk contDiff_const.contDiffOn
    have hfixed :
        ContDiffOn Real ∞ (fun p : VarPhase (E := E) => Φ (p, τ)) W :=
      hjoint.comp hconst (by
        intro p hp
        exact ⟨by simpa [W, p0] using hp, hτT⟩)
    simpa [Φ] using hfixed

/-- Smooth dependence of the fixed-time base endpoint on the initial model
phase, on an open neighborhood inside the controlled phase ball.

This is now a consumer of the flat augmented-flow smoothness frontier
`varFlow_smoothOn`. -/
theorem timeBaseEnd_smoothOn
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ : (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
      ModelPhase (E := E) × ModelLin (E := E))
    {ε τ : Real} {a r : NNReal} {L' : NNReal}
    (hr : 0 < r)
    {T_out T_mid T B : Real}
    (hτT : τ ∈ Set.Ioo (0 - T) (0 + T))
    (hT : 0 < T)
    (hT_lt_mid : T < T_mid)
    (hT_mid_lt_out : T_mid < T_out)
    (hB : 0 ≤ B)
    (hBT_mid : B * T_mid < 1)
    (hTsub : Set.Icc (0 - T_out) (0 + T_out) ⊆ Set.Icc (-ε) ε)
    {ρ_out ρ_mid ρVar : NNReal} {r' : NNReal}
    (hr' : 0 < r')
    (hρVar_pos : 0 < (ρVar : Real))
    (hρ_lt_mid : (ρVar : Real) < (ρ_mid : Real))
    (hρ_mid_lt_out : (ρ_mid : Real) < (ρ_out : Real))
    (hρρ' : (ρ_mid : Real) + (r' : Real) ≤ (r : Real))
    (hρ_out_le_r : (ρ_out : Real) ≤ (r : Real))
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hA_bd :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) (ρ_out : Real),
        ∀ t ∈ Set.Icc (0 - T_out) (0 + T_out),
          ‖fderiv Real (varSpray (I := I) g x) (Ψ p t)‖ ≤ B) :
    ∃ w : Set (ModelPhase (E := E)),
      IsOpen w ∧
        initPhase (I := I) x (0 : TangentSpace I x) ∈ w ∧
        w ⊆ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r ∧
        ContDiffOn Real ∞ (fun z => timeBaseEndpoint (E := E) Ψ τ z) w := by
  classical
  let idLin : ModelLin (E := E) :=
    ContinuousLinearMap.id Real (ModelPhase (E := E))
  let c : ModelPhase (E := E) :=
    extChartAt I.tangent (phaseZero (I := I) x) (phaseZero (I := I) x)
  let ι : ModelPhase (E := E) -> ModelPhase (E := E) × ModelLin (E := E) :=
    fun z => (z, idLin)
  obtain ⟨W, hWopen, hWzero, _hWsub, hWsmooth⟩ :=
    varFlow_smoothOn (I := I) g x Ψ (ε := ε) (τ := τ)
      (a := a) (r := r) (L' := L') hr hτT hT hT_lt_mid hT_mid_lt_out
      hB hBT_mid hTsub hr' hρVar_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r
      hflow hbound hsrc hLip hA_bd
  let w : Set (ModelPhase (E := E)) :=
    ι ⁻¹' W ∩ Metric.ball (c : ModelPhase (E := E)) (r : Real)
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · have hιcont : Continuous ι :=
      continuous_id.prodMk continuous_const
    exact (hWopen.preimage hιcont).inter Metric.isOpen_ball
  · have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
    have hball :
        (c : ModelPhase (E := E)) ∈
          Metric.ball (c : ModelPhase (E := E)) (r : Real) :=
      Metric.mem_ball_self hrReal
    exact ⟨by simpa [ι, idLin, c, initPhase_zero, varPhaseZero] using hWzero,
      by simpa [c, initPhase_zero] using hball⟩
  · intro z hz
    exact Metric.ball_subset_closedBall hz.2
  · have hιsmooth : ContDiff Real ∞ ι :=
      contDiff_id.prodMk contDiff_const
    have hcomp :
        ContDiffOn Real ∞ (fun z : ModelPhase (E := E) => Ψ (ι z) τ) w :=
      hWsmooth.comp hιsmooth.contDiffOn (by intro z hz; exact hz.1)
    simpa [timeBaseEndpoint, varBaseFlow, ι, idLin] using hcomp.fst.fst

/-- Source-controlled strict derivative of the fixed-time base-coordinate
endpoint. -/
theorem timeBaseEndpoint_hasStrictFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasStrictFDerivAt
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      ((ContinuousLinearMap.fst Real E E).comp (varDerivFlow (E := E) Ψ z b))
      z :=
  timeBaseEndpoint_hasStrictFDerivAt (E := E)
    (timeEndpoint_hasStrictFDerivAt (I := I) g x Ψ z
      hb0 hb hflow hbound hsrc hLip hzopen)

/-- Source-controlled `C1` regularity of the fixed-time base-coordinate
endpoint. -/
theorem timeBaseEndpoint_contDiffAt_one_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    ContDiffAt Real 1
      (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
      z :=
  timeBaseEndpoint_contDiffAt_one (E := E)
    (timeEndpoint_contDiffAt_one (I := I) g x Ψ z
      hb0 hb hflow hbound hsrc hLip hzopen)

/-- Pull back the base-coordinate endpoint derivative along the initial-phase
map `v ↦ initPhase x v`. -/
theorem timeBaseEndpoint_initPhase_hasFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {v : TangentSpace I x} {b : Real}
    {A : ModelPhase (E := E) →L[Real] E}
    (hA :
      HasFDerivAt
        (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
        A
        (initPhase (I := I) x v)) :
    HasFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (A.comp (initPhaseLin (I := I) x))
      v :=
  hA.comp v (initPhase_hasFDerivAt (I := I) x v)

/-- Pull back the strict base-coordinate endpoint derivative along the
initial-phase map `v ↦ initPhase x v`. -/
theorem timeBaseEndpoint_initPhase_hasStrictFDerivAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {v : TangentSpace I x} {b : Real}
    {A : ModelPhase (E := E) →L[Real] E}
    (hA :
      HasStrictFDerivAt
        (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
        A
        (initPhase (I := I) x v)) :
    HasStrictFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (A.comp (initPhaseLin (I := I) x))
      v :=
  HasStrictFDerivAt.comp (x := v) hA
    (initPhase_hasStrictFDerivAt (I := I) x v)

/-- Pull back `C1` regularity of the base-coordinate endpoint along the
initial-phase map. -/
theorem timeBaseEndpoint_initPhase_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {v : TangentSpace I x} {b : Real}
    (hA :
      ContDiffAt Real 1
        (fun z' : ModelPhase (E := E) => timeBaseEndpoint (E := E) Ψ b z')
        (initPhase (I := I) x v)) :
    ContDiffAt Real 1
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      v := by
  exact hA.comp v (initPhase_contDiffAt (I := I) (n := (1 : WithTop ℕ∞)) x v)

/-- Base-coordinate endpoint after the homogeneous time rescaling
`v ↦ b⁻¹ • v`.  This is the local chart expression of the exponential endpoint
when a short time `b` is used to reach time one by rescaling the initial
velocity. -/
def scaledBaseEnd
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (b : Real) (x : M) (v : TangentSpace I x) : E :=
  timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x (b⁻¹ • v))

/-- Source-controlled version of the velocity-space base endpoint derivative. -/
theorem timeBaseEndpoint_initPhase_hasFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (v : TangentSpace I x)
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hvopen :
      (initPhase (I := I) x v,
          ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (((ContinuousLinearMap.fst Real E E).comp
        (varDerivFlow (E := E) Ψ (initPhase (I := I) x v) b)).comp
          (initPhaseLin (I := I) x))
      v :=
  timeBaseEndpoint_initPhase_hasFDerivAt (E := E)
      (timeBaseEndpoint_hasFDerivAt_of_flow (I := I) g x Ψ
      (initPhase (I := I) x v) hb0 hb hflow hbound hsrc hLip hvopen)

/-- Source-controlled strict version of the velocity-space base endpoint
derivative. -/
theorem timeBaseEndpoint_initPhase_hasStrictFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (v : TangentSpace I x)
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hvopen :
      (initPhase (I := I) x v,
          ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasStrictFDerivAt
      (fun v' : TangentSpace I x =>
        timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v'))
      (((ContinuousLinearMap.fst Real E E).comp
        (varDerivFlow (E := E) Ψ (initPhase (I := I) x v) b)).comp
          (initPhaseLin (I := I) x))
      v :=
  timeBaseEndpoint_initPhase_hasStrictFDerivAt (E := E)
      (timeBaseEndpoint_hasStrictFDerivAt_of_flow (I := I) g x Ψ
      (initPhase (I := I) x v) hb0 hb hflow hbound hsrc hLip hvopen)

/-- If the unscaled short-time endpoint has derivative `b • id`, then the
homogeneously rescaled endpoint has derivative `id`. -/
theorem scaledBaseEnd_deriv0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (hb : b ≠ 0)
    (h :
      HasFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasFDerivAt
      (scaledBaseEnd (I := I) (E := E) Ψ b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  have hscale :
      HasFDerivAt
        (fun v : TangentSpace I x => b⁻¹ • v)
        (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x))
        0 := by
    simpa using
      ((ContinuousLinearMap.id Real (TangentSpace I x)).hasFDerivAt.const_smul b⁻¹)
  have h_at :
      HasFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        (b⁻¹ • (0 : TangentSpace I x)) := by
    simpa using h
  have hcomp := h_at.comp (0 : TangentSpace I x) hscale
  have hlin :
      (b • ContinuousLinearMap.id Real (TangentSpace I x)).comp
          (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x)) =
        ContinuousLinearMap.id Real (TangentSpace I x) := by
    ext v
    change b • (b⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
  convert hcomp using 1
  exact hlin.symm

/-- Strict version of `scaledBaseEnd_deriv0`. -/
theorem scaledBaseEnd_strict0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (hb : b ≠ 0)
    (h :
      HasStrictFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasStrictFDerivAt
      (scaledBaseEnd (I := I) (E := E) Ψ b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  have hscale :
      HasStrictFDerivAt
        (fun v : TangentSpace I x => b⁻¹ • v)
        (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x))
        0 := by
    simpa using
      ((ContinuousLinearMap.id Real (TangentSpace I x)).hasStrictFDerivAt.const_smul b⁻¹)
  have h_at :
      HasStrictFDerivAt
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b • ContinuousLinearMap.id Real (TangentSpace I x))
        (b⁻¹ • (0 : TangentSpace I x)) := by
    simpa using h
  have hcomp := HasStrictFDerivAt.comp (x := (0 : TangentSpace I x)) h_at hscale
  have hlin :
      (b • ContinuousLinearMap.id Real (TangentSpace I x)).comp
          (b⁻¹ • ContinuousLinearMap.id Real (TangentSpace I x)) =
        ContinuousLinearMap.id Real (TangentSpace I x) := by
    ext v
    change b • (b⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
  convert hcomp using 1
  exact hlin.symm

/-- `C1` regularity of the rescaled base endpoint at zero. -/
theorem scaledBaseEnd_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      ContDiffAt Real 1
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        0) :
    ContDiffAt Real 1
      (scaledBaseEnd (I := I) (E := E) Ψ b x)
      0 := by
  have hscale :
      ContDiffAt Real 1
        (fun v : TangentSpace I x => b⁻¹ • v)
        (0 : TangentSpace I x) := by
    simpa using
      ((contDiff_const_smul (𝕜 := Real)
        (n := (1 : WithTop ℕ∞)) (F := TangentSpace I x) b⁻¹).contDiffAt :
          ContDiffAt Real 1 (fun v : TangentSpace I x => b⁻¹ • v) 0)
  have h_at :
      ContDiffAt Real 1
        (fun v : TangentSpace I x =>
          timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
        (b⁻¹ • (0 : TangentSpace I x)) := by
    simpa using h
  simpa [scaledBaseEnd] using h_at.comp (0 : TangentSpace I x) hscale

/-- The rescaled base endpoint is exactly the existing `chartEnd` for the
model flow projected from the augmented variational flow. -/
theorem chartEnd_varModelFlow_eq_scaledBaseEnd
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (b : Real) (x : M) :
    chartEnd (I := I) (varModelFlow (E := E) Ψ) b x =
      scaledBaseEnd (I := I) (E := E) Ψ b x := by
  rfl

/-- Derivative of `chartEnd` for the model flow projected from an augmented
variational flow. -/
theorem chartEnd_varModelFlow_deriv0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      HasFDerivAt
        (scaledBaseEnd (I := I) (E := E) Ψ b x)
        (ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasFDerivAt
      (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  simpa [chartEnd_varModelFlow_eq_scaledBaseEnd (I := I) (E := E) Ψ b x] using h

/-- Strict derivative of `chartEnd` for the model flow projected from an
augmented variational flow. -/
theorem chartEnd_varModelFlow_strict0
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      HasStrictFDerivAt
        (scaledBaseEnd (I := I) (E := E) Ψ b x)
        (ContinuousLinearMap.id Real (TangentSpace I x))
        0) :
    HasStrictFDerivAt
      (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
      (ContinuousLinearMap.id Real (TangentSpace I x))
      0 := by
  simpa [chartEnd_varModelFlow_eq_scaledBaseEnd (I := I) (E := E) Ψ b x] using h

/-- `C1` regularity of `chartEnd` for the model flow projected from an
augmented variational flow. -/
theorem chartEnd_varModelFlow_contDiffAt_one
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {x : M} {b : Real}
    (h :
      ContDiffAt Real 1
        (scaledBaseEnd (I := I) (E := E) Ψ b x)
        0) :
    ContDiffAt Real 1
      (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
      0 := by
  simpa [chartEnd_varModelFlow_eq_scaledBaseEnd (I := I) (E := E) Ψ b x] using h

/-- Local augmented variational flow whose base component has the variational
component as Frechet derivative at every interior initial phase, for forward
times in the Picard interval. -/
theorem varFlow_hasFDerivAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ψ p t).1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ψ p t).1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Icc (0 : Real) ε,
              ∀ z : ModelPhase (E := E),
                (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
                  Metric.ball (varPhaseZero (I := I) (E := E) x) r ->
                HasFDerivAt
                  (fun z' : ModelPhase (E := E) =>
                    varBaseFlow (E := E) Ψ z' b)
                  (varDerivFlow (E := E) Ψ z b)
                  z := by
  obtain ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc_ball, hsrc_flow, L', hLip⟩ :=
    varFlow_src_bound (I := I) g x
  refine ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc_ball, hsrc_flow, L', hLip, ?_⟩
  intro b hb z hzopen
  have hbsub : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor
    · linarith [hε, ht.1]
    · exact le_trans ht.2 hb.2
  exact
    varBaseFlow_hasFDerivAt_of_flow (I := I) g x Ψ z
      hb.1 hbsub hflow hbound hsrc_ball hLip hzopen

/-- Short-time augmented variational flow whose base-coordinate endpoint has
the expected zero-velocity derivative in the initial tangent vector. -/
theorem varFlow_deriv0
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            Ψ (varPhaseZero (I := I) (E := E) x) t =
              varZeroPhaseLin (I := I) (E := E) x t) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Icc (0 : Real) δ,
              HasFDerivAt
                (fun v : TangentSpace I x =>
                  timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
                (b • ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    varSpray_pl0_src (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) hpl
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  obtain ⟨δ0, hδ0, hcand0⟩ :=
    varZeroPhaseLin_mem_closedBall_small (I := I) (E := E) x (a := a) ha
  let δ : Real := min δ0 ε
  have hδ : 0 < δ := lt_min hδ0 hε
  have hδε : δ ≤ ε := min_le_right _ _
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hcand :
      ∀ t ∈ Set.Icc (-δ) δ,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a := by
    intro t ht
    exact hcand0 t ⟨by linarith [ht.1, hδδ0], by linarith [ht.2, hδδ0]⟩
  have hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t := by
    intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by simpa using ht
    simpa using (hΨ p hp).2 t ht'
  have hLip' :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by simpa using ht
    simpa using hLip t ht'
  have hzeroEq :
      ∀ t ∈ Set.Icc (-δ) δ,
        Ψ (varPhaseZero (I := I) (E := E) x) t =
          varZeroPhaseLin (I := I) (E := E) x t :=
    varFlow_zero_phaseLin_of_pl (I := I) g x hε hδ hδε hpl
      hflow hbound hcand
  refine ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzeroEq, L', hLip', ?_⟩
  intro b hb
  have hbε : b ∈ Set.Icc (0 : Real) ε := ⟨hb.1, le_trans hb.2 hδε⟩
  have hbsub : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor
    · linarith [hε, ht.1]
    · exact le_trans ht.2 hbε.2
  have hinit :
      (initPhase (I := I) x (0 : TangentSpace I x),
          ContinuousLinearMap.id Real (ModelPhase (E := E))) =
        varPhaseZero (I := I) (E := E) x := by
    simp [varPhaseZero, initPhase_zero]
  have hvopen :
      (initPhase (I := I) x (0 : TangentSpace I x),
          ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r := by
    rw [hinit]
    exact Metric.mem_ball_self hrR
  have hderiv :=
    timeBaseEndpoint_initPhase_hasFDerivAt_of_flow (I := I) g x Ψ
      (0 : TangentSpace I x) hb.1 hbsub hflow hbound hsrc hLip' hvopen
  have hbδ : b ∈ Set.Icc (-δ) δ := ⟨by linarith [hb.1], hb.2⟩
  have hA :
      varDerivFlow (E := E) Ψ (initPhase (I := I) x (0 : TangentSpace I x)) b =
        phaseLinFlow (E := E) b := by
    have hΨeq :
        Ψ (initPhase (I := I) x (0 : TangentSpace I x),
            ContinuousLinearMap.id Real (ModelPhase (E := E))) b =
          varZeroPhaseLin (I := I) (E := E) x b := by
      simpa [hinit] using hzeroEq b hbδ
    simpa [varDerivFlow, varZeroPhaseLin] using congrArg Prod.snd hΨeq
  have hclm :
      (((ContinuousLinearMap.fst Real E E).comp
          (varDerivFlow (E := E) Ψ
            (initPhase (I := I) x (0 : TangentSpace I x)) b)).comp
          (initPhaseLin (I := I) x)) =
        b • ContinuousLinearMap.id Real (TangentSpace I x) := by
    rw [hA]
    ext v
    simp [initPhaseLin, phaseLinFlow, modelSprayLin]
    rfl
  rw [hclm] at hderiv
  exact hderiv

/-- Short-time augmented variational flow whose homogeneously rescaled
base-coordinate endpoint has derivative `id` at the zero initial tangent
vector. -/
theorem varFlow_scaledDeriv0
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            Ψ (varPhaseZero (I := I) (E := E) x) t =
              varZeroPhaseLin (I := I) (E := E) x t) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              HasFDerivAt
                (scaledBaseEnd (I := I) (E := E) Ψ b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip, hderiv⟩ :=
    varFlow_deriv0 (I := I) g x
  refine ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip, ?_⟩
  intro b hb
  exact scaledBaseEnd_deriv0 (I := I) (E := E) (Ψ := Ψ) (x := x)
    (b := b) (ne_of_gt hb.1) (hderiv b ⟨le_of_lt hb.1, hb.2⟩)

/-- Endpoint-facing package for the model flow projected from the augmented
variational flow: it solves the original model spray ODE, has fixed-chart
source control, and its rescaled `chartEnd` has derivative `id` at zero. -/
theorem varFlow_chartEndDeriv0
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          varModelFlow (E := E) Ψ z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt
                (varModelFlow (E := E) Ψ z)
                (modelSpray (I := I) g x
                  (varModelFlow (E := E) Ψ z t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              varModelFlow (E := E) Ψ z t ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x
                  (varModelFlow (E := E) Ψ z t)).proj ∈
                  (extChartAt I x).source) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            varModelFlow (E := E) Ψ
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) t =
              extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              HasFDerivAt
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip, hderiv⟩ :=
    varFlow_scaledDeriv0 (I := I) g x
  have hmodelZero :
      ∀ t ∈ Set.Icc (-δ) δ,
        varModelFlow (E := E) Ψ
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) t =
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x) := by
    intro t ht
    have h := hzero t ht
    simpa [varModelFlow, varZeroPhaseLin, varPhaseZero] using congrArg Prod.fst h
  refine ⟨ε, hε, δ, hδ, r, hr, Ψ, ?_, ?_, hmodelZero, L', hLip, ?_⟩
  · exact varModelFlow_flow (I := I) (E := E) g x hflow
  · exact varModelFlow_src (I := I) (E := E) x hbound hsrc
  · intro b hb
    exact chartEnd_varModelFlow_deriv0 (I := I) (E := E) (Ψ := Ψ)
      (x := x) (b := b) (hderiv b hb)

/-- Flow-retaining endpoint package for the projected augmented flow.

Compared with `varFlow_chartEndDeriv0`, this keeps the projected closed-ball
bound for `varModelFlow`.  That control is needed by the homogeneous scaling
lemmas used to build radial exponential geodesic germs. -/
theorem varFlow_modelData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          varModelFlow (E := E) Ψ z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt
                (varModelFlow (E := E) Ψ z)
                (modelSpray (I := I) g x
                  (varModelFlow (E := E) Ψ z t))
                (Set.Icc (-ε) ε) t) ∧
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
            ∀ t ∈ Set.Icc (-ε) ε,
              varModelFlow (E := E) Ψ z t ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x
                  (varModelFlow (E := E) Ψ z t)).proj ∈
                  (extChartAt I x).source) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            varModelFlow (E := E) Ψ
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) t =
              extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              HasFDerivAt
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ, hδ, a, r, hr, Ψ, hflow, hbound, hsrc, hzero, L', hLip,
      hderiv⟩ :=
    varFlow_scaledDeriv0 (I := I) g x
  have hmodelZero :
      ∀ t ∈ Set.Icc (-δ) δ,
        varModelFlow (E := E) Ψ
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) t =
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x) := by
    intro t ht
    have h := hzero t ht
    simpa [varModelFlow, varZeroPhaseLin, varPhaseZero] using congrArg Prod.fst h
  refine ⟨ε, hε, δ, hδ, a, r, hr, Ψ, ?_, ?_, ?_, hmodelZero, L', hLip, ?_⟩
  · exact varModelFlow_flow (I := I) (E := E) g x hflow
  · exact varModelFlow_bound (I := I) (E := E) x hbound
  · exact varModelFlow_src (I := I) (E := E) x hbound hsrc
  · intro b hb
    exact chartEnd_varModelFlow_deriv0 (I := I) (E := E) (Ψ := Ψ)
      (x := x) (b := b) (hderiv b hb)

/-- Endpoint-facing package for the projected augmented flow with both `C1`
regularity and derivative `id` at the zero initial tangent vector. -/
theorem varFlow_chartEndC1
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (δ : Real), ∃ (_hδ : 0 < δ),
      ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          varModelFlow (E := E) Ψ z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt
                (varModelFlow (E := E) Ψ z)
                (modelSpray (I := I) g x
                  (varModelFlow (E := E) Ψ z t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              varModelFlow (E := E) Ψ z t ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x
                  (varModelFlow (E := E) Ψ z t)).proj ∈
                  (extChartAt I x).source) ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            varModelFlow (E := E) Ψ
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) t =
              extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) ∧
          (∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Ioc (0 : Real) δ,
              ContDiffAt Real 1
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                0 ∧
              HasFDerivAt
                (chartEnd (I := I) (varModelFlow (E := E) Ψ) b x)
                (ContinuousLinearMap.id Real (TangentSpace I x))
                0) := by
  obtain ⟨ε, hε, δ0, hδ0, a, r, hr, Ψ, hflow, hbound, hsrc, hzero0, L', hLip, hderiv⟩ :=
    varFlow_deriv0 (I := I) g x
  let δ : Real := min δ0 ε
  have hδ : 0 < δ := lt_min hδ0 hε
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  have hzero :
      ∀ t ∈ Set.Icc (-δ) δ,
        varModelFlow (E := E) Ψ
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) t =
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x) := by
    intro t ht
    have ht0 : t ∈ Set.Icc (-δ0) δ0 := by
      constructor <;> linarith [ht.1, ht.2, hδδ0]
    have h := hzero0 t ht0
    simpa [varModelFlow, varZeroPhaseLin, varPhaseZero] using congrArg Prod.fst h
  refine ⟨ε, hε, δ, hδ, r, hr, Ψ, ?_, ?_, hzero, L', hLip, ?_⟩
  · exact varModelFlow_flow (I := I) (E := E) g x hflow
  · exact varModelFlow_src (I := I) (E := E) x hbound hsrc
  · intro b hb
    have hbIcc : b ∈ Set.Icc (0 : Real) δ0 :=
      ⟨le_of_lt hb.1, le_trans hb.2 hδδ0⟩
    have hbε : b ≤ ε := le_trans hb.2 hδε
    have hbsub : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε := by
      intro t ht
      constructor
      · linarith [hε, ht.1]
      · exact le_trans ht.2 hbε
    have hinit :
        (initPhase (I := I) x (0 : TangentSpace I x),
            ContinuousLinearMap.id Real (ModelPhase (E := E))) =
          varPhaseZero (I := I) (E := E) x := by
      simp [varPhaseZero, initPhase_zero]
    have hvopen :
        (initPhase (I := I) x (0 : TangentSpace I x),
            ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
          Metric.ball (varPhaseZero (I := I) (E := E) x) r := by
      rw [hinit]
      have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
      exact Metric.mem_ball_self hrR
    have hbaseC1 :
        ContDiffAt Real 1
          (fun z' : ModelPhase (E := E) =>
            timeBaseEndpoint (E := E) Ψ b z')
          (initPhase (I := I) x (0 : TangentSpace I x)) :=
      timeBaseEndpoint_contDiffAt_one_of_flow (I := I) g x Ψ
        (initPhase (I := I) x (0 : TangentSpace I x))
        (le_of_lt hb.1) hbsub hflow hbound hsrc hLip hvopen
    have hpull :
        ContDiffAt Real 1
          (fun v : TangentSpace I x =>
            timeBaseEndpoint (E := E) Ψ b (initPhase (I := I) x v))
          0 :=
      timeBaseEndpoint_initPhase_contDiffAt_one (E := E) hbaseC1
    refine ⟨?_, ?_⟩
    · exact chartEnd_varModelFlow_contDiffAt_one (I := I) (E := E)
        (Ψ := Ψ) (x := x) (b := b)
        (scaledBaseEnd_contDiffAt_one (I := I) (E := E) (Ψ := Ψ)
          (x := x) (b := b) hpull)
    · exact chartEnd_varModelFlow_deriv0 (I := I) (E := E) (Ψ := Ψ)
        (x := x) (b := b)
        (scaledBaseEnd_deriv0 (I := I) (E := E) (Ψ := Ψ) (x := x)
          (b := b) (ne_of_gt hb.1) (hderiv b hbIcc))


end Coordinates
end RicciFlower
