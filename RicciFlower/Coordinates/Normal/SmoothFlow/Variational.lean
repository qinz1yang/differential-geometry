import RicciFlower.Coordinates.Normal.SmoothFlow.GenericC1

/-!
# Fixed-chart variational smooth-flow layer

This module contains the fixed-chart augmented variational spray, Picard flow
packages, source control, and model-specific C1 error estimates.
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

/-- Smoothness of the augmented variational RHS for a finite jet-prefix ODE. -/
theorem jetVarRHS_cdAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelJetPrefix (E := E) N →L[Real] ModelJetPrefix (E := E) N)
    (hF : ContDiffAt Real ∞ F (ModelJetPrefix.base (E := E) N P)) :
    ContDiffAt Real ∞
      (variationalRHS (jetRHSPrefix (E := E) F N))
      (P, A) :=
  variationalRHS_contDiffAt (X := ModelJetPrefix (E := E) N)
    (F := jetRHSPrefix (E := E) F N) (z := P) (A := A)
    (jetRHSPrefix_contDiffAt (E := E) F N P hF)

/-- Smoothness of the parameterized augmented variational RHS for a finite
jet-prefix ODE, where the parameter space is the original model phase. -/
theorem jetParamVarRHS_cdAt
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelPhase (E := E) →L[Real] ModelJetPrefix (E := E) N)
    (hF : ContDiffAt Real ∞ F (ModelJetPrefix.base (E := E) N P)) :
    ContDiffAt Real ∞
      (paramVariationalRHS (P := ModelPhase (E := E))
        (jetRHSPrefix (E := E) F N))
      (P, A) :=
  paramVariationalRHS_contDiffAt
    (X := ModelJetPrefix (E := E) N) (P := ModelPhase (E := E))
    (F := jetRHSPrefix (E := E) F N) (z := P) (A := A)
    (jetRHSPrefix_contDiffAt (E := E) F N P hF)

/-- The successor finite-prefix RHS is the parameterized variational RHS of
the previous finite-prefix RHS along an actual fixed-time Taylor jet.  This is
the finite-state version of "the first variational equation of the `N`-jet ODE
is the `(N+1)`-jet ODE". -/
theorem jetRHSPrefix_succ_as_paramVarRHS
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Phi : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (N : Nat) (z : ModelPhase (E := E)) (t : Real)
    (hFcont : ContDiffAt Real ∞ F (Phi z t))
    (hF :
      HasFTaylorSeriesUpToOn (𝕜 := Real) (N + 1 : Nat)
        F
        (fun y : ModelPhase (E := E) => ftaylorSeries Real F y)
        Set.univ)
    (hPhi :
      HasFTaylorSeriesUpToOn (𝕜 := Real) (N + 1 : Nat)
        (fun y : ModelPhase (E := E) => Phi y t)
        (fun y : ModelPhase (E := E) => flowJet (E := E) Phi y t)
        Set.univ) :
    paramVariationalRHS (P := ModelPhase (E := E))
        (jetRHSPrefix (E := E) F N)
        (flowJetPrefix (E := E) Phi N z t,
          ModelJetPrefix.shiftedDeriv (E := E) N
            (flowJetPrefix (E := E) Phi (N + 1) z t))
      =
        (jetRHSPrefix (E := E) F N
            (flowJetPrefix (E := E) Phi N z t),
          ModelJetPrefix.shiftedDeriv (E := E) N
            (jetRHSPrefix (E := E) F (N + 1)
              (flowJetPrefix (E := E) Phi (N + 1) z t))) := by
  apply Prod.ext
  · rfl
  · dsimp [paramVariationalRHS]
    let P0 : ModelJetPrefix (E := E) N :=
      flowJetPrefix (E := E) Phi N z t
    let A0 : ModelPhase (E := E) →L[Real] ModelJetPrefix (E := E) N :=
      ModelJetPrefix.shiftedDeriv (E := E) N
        (flowJetPrefix (E := E) Phi (N + 1) z t)
    have hflow :
        HasFDerivAt
          (fun y : ModelPhase (E := E) => flowJetPrefix (E := E) Phi N y t)
          A0 z := by
      simpa [A0] using
        flowJetPrefix_hasFDerivAt_of_hasFTaylor (E := E) Phi N z t
          (hasFTaylorSeriesUpToOn_univ_iff.mp hPhi)
    have hjet :
        HasFDerivAt
          (jetRHSPrefix (E := E) F N)
          (fderiv Real (jetRHSPrefix (E := E) F N) P0) P0 := by
      exact
        ((jetRHSPrefix_contDiffAt (E := E) F N P0
          (by simpa [P0] using hFcont)).differentiableAt (by simp)).hasFDerivAt
    have hchain :
        HasFDerivAt
          (fun y : ModelPhase (E := E) =>
            jetRHSPrefix (E := E) F N
              (flowJetPrefix (E := E) Phi N y t))
          ((fderiv Real (jetRHSPrefix (E := E) F N) P0).comp A0) z := by
      simpa [P0] using hjet.comp z hflow
    have hdirect :=
      jetRHSPrefix_flowJetPrefix_hasFDerivAt (E := E) F Phi N z t hF hPhi
    exact (hdirect.unique hchain).symm

/-- Smoothness of the augmented variational RHS for the fixed-chart spray
finite jet-prefix ODE on the controlled chart/source region. -/
theorem sprayJetVarRHS_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelJetPrefix (E := E) N →L[Real] ModelJetPrefix (E := E) N)
    (hztarget :
      ModelJetPrefix.base (E := E) N P ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc :
      (phaseOfModel (I := I) x (ModelJetPrefix.base (E := E) N P)).proj ∈
        (extChartAt I x).source) :
    ContDiffAt Real ∞
      (variationalRHS
        (jetRHSPrefix (E := E) (modelSpray (I := I) g x) N))
      (P, A) :=
  jetVarRHS_cdAt (E := E) (modelSpray (I := I) g x) N P A
    (modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc)

/-- Smoothness of the parameterized augmented variational RHS for the
fixed-chart spray finite jet-prefix ODE on the controlled chart/source region. -/
theorem sprayJetParamVarRHS_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Nat) (P : ModelJetPrefix (E := E) N)
    (A : ModelPhase (E := E) →L[Real] ModelJetPrefix (E := E) N)
    (hztarget :
      ModelJetPrefix.base (E := E) N P ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc :
      (phaseOfModel (I := I) x (ModelJetPrefix.base (E := E) N P)).proj ∈
        (extChartAt I x).source) :
    ContDiffAt Real ∞
      (paramVariationalRHS (P := ModelPhase (E := E))
        (jetRHSPrefix (E := E) (modelSpray (I := I) g x) N))
      (P, A) :=
  jetParamVarRHS_cdAt (E := E) (modelSpray (I := I) g x) N P A
    (modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc)

/-- The zero point for the variational equation: zero phase and identity
linearized initial data. -/
def varPhaseZero (x : M) : ModelPhase (E := E) × ModelLin (E := E) :=
  (extChartAt I.tangent (phaseZero (I := I) x)
    (phaseZero (I := I) x),
    ContinuousLinearMap.id Real (ModelPhase (E := E)))

/-- The augmented vector field for the variational equation.

The first component is the model spray.  The second component is the linear ODE
`A' = DF(z) ∘ A` for derivatives with respect to the initial phase. -/
def varSpray
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    ModelPhase (E := E) × ModelLin (E := E) :=
  (modelSpray (I := I) g x p.1,
    (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2)

@[simp] theorem varSpray_fst
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    (varSpray (I := I) g x p).1 = modelSpray (I := I) g x p.1 := rfl

@[simp] theorem varSpray_snd
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    (varSpray (I := I) g x p).2 =
      (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2 := rfl

/-- The augmented variational vector field is smooth at `(0_x, id)`.

This is the higher-order regularity input for iterating the variational-equation
route: the augmented vector field loses one derivative through `fderiv`, but the
fixed-chart model spray is already smooth. -/
theorem varSpray_contDiffAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real ∞
      (varSpray (I := I) g x)
      (varPhaseZero (I := I) (E := E) x) := by
  let Z := ModelPhase (E := E)
  let z0 : Z :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  change
    ContDiffAt Real ∞
      (variationalRHS (modelSpray (I := I) g x))
      (z0, ContinuousLinearMap.id Real Z)
  exact variationalRHS_contDiffAt (X := Z)
    (F := modelSpray (I := I) g x) (z := z0)
    (A := ContinuousLinearMap.id Real Z)
    (modelSpray_contDiffAt (I := I) g x)

/-- The augmented variational vector field is `C¹` at `(0_x, id)`.

This corollary is the Picard-Lindelöf input used by the existing C1
variational-flow construction. -/
theorem varSpray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (varSpray (I := I) g x)
      (varPhaseZero (I := I) (E := E) x) := by
  exact (varSpray_contDiffAt (I := I) g x).of_le (by simp)

/-- The augmented variational vector field is smooth at every controlled phase
point. -/
theorem varSpray_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {p : ModelPhase (E := E) × ModelLin (E := E)}
    (hztarget : p.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x p.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real ∞ (varSpray (I := I) g x) p := by
  let Z := ModelPhase (E := E)
  have hF :
      ContDiffAt Real ∞ (modelSpray (I := I) g x) p.1 :=
    modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc
  change
      ContDiffAt Real ∞
        (variationalRHS (modelSpray (I := I) g x)) p
  exact variationalRHS_contDiffAt (X := Z)
    (F := modelSpray (I := I) g x) (z := p.1) (A := p.2) hF

/-- The augmented variational vector field is `C¹` at every controlled phase
point. -/
theorem varSpray_cdAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {p : ModelPhase (E := E) × ModelLin (E := E)}
    (hztarget : p.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x p.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real 1 (varSpray (I := I) g x) p := by
  exact (varSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc).of_le (by simp)

/-- Source-control domain for the augmented variational spray. -/
def varSource [I.Boundaryless] (x : M) : Set (VarPhase (E := E)) :=
  {p : VarPhase (E := E) |
    p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
      (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source}

/-- The augmented variational source-control domain is open. -/
theorem isOpen_varSource
    [I.Boundaryless] (x : M) :
    IsOpen (varSource (I := I) (E := E) x) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have htarget :
      {q : VarPhase (E := E) |
        q.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target} ∈ 𝓝 p := by
    exact continuousAt_fst.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := I.tangent)
        (phaseZero (I := I) x)).mem_nhds hp.1)
  have hphase :
      ContinuousAt (fun q : VarPhase (E := E) => phaseOfModel (I := I) x q.1) p := by
    exact (continuousAt_extChartAt_symm'' (I := I.tangent) hp.1).comp continuousAt_fst
  have hproj :
      ContinuousAt
        (fun q : VarPhase (E := E) => (phaseOfModel (I := I) x q.1).proj) p := by
    exact ((FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt).comp hphase
  have hsource :
      {q : VarPhase (E := E) |
        (phaseOfModel (I := I) x q.1).proj ∈ (extChartAt I x).source} ∈ 𝓝 p := by
    exact hproj.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) x).mem_nhds hp.2)
  change
    ({q : VarPhase (E := E) |
        q.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target} ∩
      {q : VarPhase (E := E) |
        (phaseOfModel (I := I) x q.1).proj ∈ (extChartAt I x).source}) ∈ 𝓝 p
  exact Filter.inter_mem htarget hsource

/-- The augmented variational spray is smooth on its source-control domain. -/
theorem varSpray_cdOn_source
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffOn Real ∞
      (varSpray (I := I) g x)
      (varSource (I := I) (E := E) x) := by
  intro p hp
  exact (varSpray_contDiffAt_of_mem (I := I) g x hp.1 hp.2).contDiffWithinAt

/-- The time-independent augmented variational spray is smooth on
`ℝ × varSource`. -/
theorem varSpray_time_cdOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffOn Real ∞
      (fun q : Real × VarPhase (E := E) => varSpray (I := I) g x q.2)
      (Set.univ ×ˢ varSource (I := I) (E := E) x) := by
  have hsrc := varSpray_cdOn_source (I := I) g x
  have hsnd :
      ContDiffOn Real ∞
        (fun q : Real × VarPhase (E := E) => q.2)
        (Set.univ ×ˢ varSource (I := I) (E := E) x) :=
    contDiff_snd.contDiffOn
  exact hsrc.comp hsnd (by intro q hq; exact hq.2)

/-- Local Picard-Lindelof data for the augmented variational equation. -/
theorem varSpray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => varSpray (I := I) g x)
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (varPhaseZero (I := I) (E := E) x)
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (varSpray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

/-- The augmented variational phase is source-controlled near `(0_x, id)` as
soon as its base phase is source-controlled. -/
theorem varSrc_nhds
    [I.Boundaryless] (x : M) :
    {p : ModelPhase (E := E) × ModelLin (E := E) |
      p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source} ∈
      𝓝 (varPhaseZero (I := I) (E := E) x) := by
  have hsrc := modelSrc_nhds (I := I) (E := E) x
  have hfst :
      ContinuousAt (fun p : ModelPhase (E := E) × ModelLin (E := E) => p.1)
        (varPhaseZero (I := I) (E := E) x) :=
    continuousAt_fst
  simpa [varPhaseZero, Set.preimage] using hfst.preimage_mem_nhds hsrc

/-- Picard-Lindelof data for the augmented variational equation, shrunk so the
whole controlling augmented ball keeps the base phase in the fixed chart
source. -/
theorem varSpray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
          {p : ModelPhase (E := E) × ModelLin (E := E) |
            p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x p.1).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => varSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (varPhaseZero (I := I) (E := E) x)
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := varSpray_pl (I := I) g x
  let p0 : ModelPhase (E := E) × ModelLin (E := E) :=
    varPhaseZero (I := I) (E := E) x
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (varSrc_nhds (I := I) (E := E) x)
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
      (f := fun _ : Real => varSpray (I := I) g x)
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro p hp
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist p p0 ≤ (a' : Real) := by
    simpa [p0] using Metric.mem_closedBall.mp hp
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist p p0 ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

/-- Uniform short-time augmented variational flow with Lipschitz dependence on
the augmented initial phase. -/
theorem varFlow_lipschitz
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ := varSpray_pl (I := I) g x
  obtain ⟨Ψ, hΨ, L', hLip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨ε, hε, r, hr, Ψ, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Uniform short-time augmented variational flow with Lipschitz dependence and
the closed-ball bound for the same chosen flow. -/
theorem varFlow_bound
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
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hpl⟩ := varSpray_pl (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) (hpl 0)
  refine ⟨ε, hε, a, r, hr, Ψ, ?_, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro p hp t
    simpa using hbound p hp t
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Uniform short-time augmented variational flow with Lipschitz dependence,
closed-ball bound, and base-phase source control for the same chosen flow. -/
theorem varFlow_src_bound
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
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hsrc, hpl⟩ :=
    varSpray_pl0_src (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) hpl
  refine ⟨ε, hε, a, r, hr, Ψ, ?_, ?_, hsrc, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro p hp t
    simpa using hbound p hp t
  · intro p hp t
    exact hsrc (hbound p hp t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Smoothness of the augmented variational RHS on a source-controlled closed
ball. -/
theorem varSpray_smoothBall
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {a : NNReal}
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source}) :
    ContDiffOn Real ∞
      (varSpray (I := I) g x)
      (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) := by
  intro p hp
  exact (varSpray_contDiffAt_of_mem (I := I) g x (hsrc hp).1 (hsrc hp).2).contDiffWithinAt

/-- The source-controlled augmented variational flow also carries smoothness of
the RHS on its whole closed control ball. -/
theorem varFlow_smoothTube
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
          (∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
          ContDiffOn Real ∞
            (varSpray (I := I) g x)
            (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) := by
  obtain ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc, hsrc_flow, L', hLip⟩ :=
    varFlow_src_bound (I := I) g x
  exact ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc, hsrc_flow,
    ⟨L', hLip⟩, varSpray_smoothBall (I := I) g x hsrc⟩

/-- Zero point for the second augmented variational equation: the first
augmented zero and the identity on the first augmented state. -/
def var2PhaseZero (x : M) : VarPhase (E := E) × VarLin (E := E) :=
  (varPhaseZero (I := I) (E := E) x,
    ContinuousLinearMap.id Real (VarPhase (E := E)))

/-- Smoothness of the second augmented RHS at the first augmented zero. -/
theorem var2Spray_contDiffAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real ∞
      (variationalRHS (varSpray (I := I) g x))
      (var2PhaseZero (I := I) (E := E) x) := by
  exact variationalRHS_contDiffAt (X := VarPhase (E := E))
    (F := varSpray (I := I) g x)
    (z := varPhaseZero (I := I) (E := E) x)
    (A := ContinuousLinearMap.id Real (VarPhase (E := E)))
    (varSpray_contDiffAt (I := I) g x)

/-- C1 regularity of the second augmented RHS at the first augmented zero. -/
theorem var2Spray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (variationalRHS (varSpray (I := I) g x))
      (var2PhaseZero (I := I) (E := E) x) := by
  exact (var2Spray_contDiffAt (I := I) g x).of_le (by simp)

/-- The second augmented RHS is smooth whenever the first augmented base point
is source-controlled. -/
theorem var2Spray_contDiffAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {q : VarPhase (E := E) × VarLin (E := E)}
    (hztarget : q.1.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x q.1.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real ∞ (variationalRHS (varSpray (I := I) g x)) q := by
  exact variationalRHS_contDiffAt (X := VarPhase (E := E))
    (F := varSpray (I := I) g x) (z := q.1) (A := q.2)
    (varSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc)

/-- The second augmented RHS is `C1` whenever the first augmented base point is
source-controlled. -/
theorem var2Spray_cdAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {q : VarPhase (E := E) × VarLin (E := E)}
    (hztarget : q.1.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x q.1.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real 1 (variationalRHS (varSpray (I := I) g x)) q := by
  exact (var2Spray_contDiffAt_of_mem (I := I) g x hztarget hsrc).of_le (by simp)

/-- Local Picard-Lindelof data for the second augmented variational equation. -/
theorem var2Spray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => variationalRHS (varSpray (I := I) g x))
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (var2PhaseZero (I := I) (E := E) x)
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (var2Spray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

set_option synthInstance.maxHeartbeats 80000 in
/-- Picard-Lindelof data for the second augmented equation, shrunk so the
controlling ball keeps the first augmented base phase in the fixed source. -/
theorem var2Spray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
          {q : VarPhase (E := E) × VarLin (E := E) |
            q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x q.1.1).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => variationalRHS (varSpray (I := I) g x))
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (var2PhaseZero (I := I) (E := E) x)
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := var2Spray_pl (I := I) g x
  let p0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  let q0 : VarPhase (E := E) × VarLin (E := E) :=
    (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (varSrc_nhds (I := I) (E := E) x)
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
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x))
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro q hq
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist q q0 ≤ (a' : Real) := by
    simpa [q0, p0, var2PhaseZero] using Metric.mem_closedBall.mp hq
  have hfst : dist q.1 p0 ≤ dist q q0 := by
    change dist q.1 p0 ≤ dist q (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist q.1 p0 ≤ dist q q0 := hfst
    _ ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

set_option synthInstance.maxHeartbeats 80000 in
/-- Picard-Lindelof data for the second augmented equation, shrunk so the
controlling ball keeps the first augmented base point in a prescribed
first-level closed ball and in the fixed source. -/
theorem var2Spray_pl0_ball
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ρ : NNReal} (hρ : 0 < ρ) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
          {q : VarPhase (E := E) × VarLin (E := E) |
            q.1 ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) ρ ∧
              q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x q.1.1).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => variationalRHS (varSpray (I := I) g x))
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (var2PhaseZero (I := I) (E := E) x)
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := var2Spray_pl (I := I) g x
  let p0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  let q0 : VarPhase (E := E) × VarLin (E := E) :=
    (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (varSrc_nhds (I := I) (E := E) x)
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
  let ρnn : NNReal := ρ / 2
  let a' : NNReal := min a (min δnn ρnn)
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have hρnn : 0 < ρnn := by
    simpa [ρnn] using half_pos hρ
  have ha' : 0 < a' := by
    exact lt_min ha (lt_min hδnn hρnn)
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x))
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro q hq
  have hdist : dist q q0 ≤ (a' : Real) := by
    simpa [q0, p0, var2PhaseZero] using Metric.mem_closedBall.mp hq
  have hfst : dist q.1 p0 ≤ dist q q0 := by
    change dist q.1 p0 ≤ dist q (p0, ContinuousLinearMap.id Real (VarPhase (E := E)))
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have haρ : (a' : Real) ≤ (ρ : Real) / 2 := by
    have : a' ≤ ρnn := le_trans (min_le_right _ _) (min_le_right _ _)
    exact_mod_cast this
  have hbase : q.1 ∈ Metric.closedBall p0 ρ := by
    rw [Metric.mem_closedBall]
    calc
      dist q.1 p0 ≤ dist q q0 := hfst
      _ ≤ (a' : Real) := hdist
      _ ≤ (ρ : Real) / 2 := haρ
      _ ≤ (ρ : Real) := by
        exact half_le_self (NNReal.coe_nonneg ρ)
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := le_trans (min_le_right _ _) (min_le_left _ _)
    exact_mod_cast this
  have hsrc := hδsub (by
    rw [Metric.mem_ball]
    calc
      dist q.1 p0 ≤ dist q q0 := hfst
      _ ≤ (a' : Real) := hdist
      _ ≤ δ / 2 := haδ
      _ < δ := half_lt_self hδ)
  exact ⟨hbase, hsrc.1, hsrc.2⟩

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Uniform short-time second augmented flow with Lipschitz dependence and the
closed-ball bound for the same chosen flow. -/
theorem var2Flow_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, _hsrc, hpl⟩ :=
    var2Spray_pl0_src (I := I) g x
  haveI hVarLinComplete : CompleteSpace (VarLin (E := E)) :=
    FiniteDimensional.complete Real (VarLin (E := E))
  obtain ⟨Ω, hΩ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := VarPhase (E := E) × VarLin (E := E))
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x)) hpl
  refine ⟨ε, hε, a, r, hr, Ω, ?_, ?_, L', ?_⟩
  · intro q hq
    refine ⟨(hΩ q hq).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΩ q hq).2 t ht'
  · intro q hq t
    simpa using hbound q hq t
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Uniform short-time second augmented flow with Lipschitz dependence,
closed-ball bound, and source control for the same chosen flow. -/
theorem var2Flow_src_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
            {q : VarPhase (E := E) × VarLin (E := E) |
              q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x q.1.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ω q t).1.1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ω q t).1.1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hsrc, hpl⟩ :=
    var2Spray_pl0_src (I := I) g x
  haveI hVarLinComplete : CompleteSpace (VarLin (E := E)) :=
    FiniteDimensional.complete Real (VarLin (E := E))
  obtain ⟨Ω, hΩ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := VarPhase (E := E) × VarLin (E := E))
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x)) hpl
  refine ⟨ε, hε, a, r, hr, Ω, ?_, ?_, hsrc, ?_, L', ?_⟩
  · intro q hq
    refine ⟨(hΩ q hq).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΩ q hq).2 t ht'
  · intro q hq t
    simpa using hbound q hq t
  · intro q hq t
    exact hsrc (hbound q hq t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Uniform short-time second augmented flow whose control ball projects into
a prescribed first-level control ball, with source control and Lipschitz
dependence for the same chosen flow. -/
theorem var2Flow_ball
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ρ : NNReal} (hρ : 0 < ρ) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
            {q : VarPhase (E := E) × VarLin (E := E) |
              q.1 ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) ρ ∧
                q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                  (phaseOfModel (I := I) x q.1.1).proj ∈
                    (extChartAt I x).source}) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ω q t).1 ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) ρ ∧
                (Ω q t).1.1 ∈
                  (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ω q t).1.1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hsrc, hpl⟩ :=
    var2Spray_pl0_ball (I := I) g x hρ
  haveI hVarLinComplete : CompleteSpace (VarLin (E := E)) :=
    FiniteDimensional.complete Real (VarLin (E := E))
  obtain ⟨Ω, hΩ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := VarPhase (E := E) × VarLin (E := E))
      (f := fun _ : Real => variationalRHS (varSpray (I := I) g x)) hpl
  refine ⟨ε, hε, a, r, hr, Ω, ?_, ?_, hsrc, ?_, L', ?_⟩
  · intro q hq
    refine ⟨(hΩ q hq).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΩ q hq).2 t ht'
  · intro q hq t
    simpa using hbound q hq t
  · intro q hq t
    exact hsrc (hbound q hq t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Smoothness of the second augmented RHS on a source-controlled closed ball. -/
theorem var2Spray_smoothBall
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {a : NNReal}
    (hsrc :
      Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
        {q : VarPhase (E := E) × VarLin (E := E) |
          q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x q.1.1).proj ∈ (extChartAt I x).source}) :
    ContDiffOn Real ∞
      (variationalRHS (varSpray (I := I) g x))
      (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) := by
  intro q hq
  exact
    (var2Spray_contDiffAt_of_mem (I := I) g x (hsrc hq).1 (hsrc hq).2).contDiffWithinAt

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The second augmented flow also carries smoothness of its RHS on the closed
control ball. -/
theorem var2Flow_smoothTube
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
          VarPhase (E := E) × VarLin (E := E),
        (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
          Ω q 0 = q ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ω q)
                (variationalRHS (varSpray (I := I) g x) (Ω q t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ω q t ∈
                Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
            {q : VarPhase (E := E) × VarLin (E := E) |
              q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x q.1.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ω q t).1.1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ω q t).1.1).proj ∈
                  (extChartAt I x).source) ∧
          (∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun q => Ω q t)
                (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r)) ∧
          ContDiffOn Real ∞
            (variationalRHS (varSpray (I := I) g x))
            (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a) := by
  obtain ⟨ε, hε, a, r, hr, Ω, hflow, hbound, hsrc, hsrc_flow, L', hLip⟩ :=
    var2Flow_src_bound (I := I) g x
  exact ⟨ε, hε, a, r, hr, Ω, hflow, hbound, hsrc, hsrc_flow,
    ⟨L', hLip⟩, var2Spray_smoothBall (I := I) g x hsrc⟩

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The base endpoint of the second augmented flow is `C1` in its first
augmented initial condition. -/
theorem var2Base_c1_of_flow
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ω : VarPhase (E := E) × VarLin (E := E) -> Real ->
      VarPhase (E := E) × VarLin (E := E))
    {ε b : Real} {a r L' : NNReal}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
        Ω q 0 = q ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ω q)
              (variationalRHS (varSpray (I := I) g x) (Ω q t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ q ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ω q t ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a ⊆
        {q : VarPhase (E := E) × VarLin (E := E) |
          q.1.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x q.1.1).proj ∈
              (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun q => Ω q t)
          (Metric.closedBall (var2PhaseZero (I := I) (E := E) x) r))
    {q : VarPhase (E := E)}
    (hqopen :
      (q, ContinuousLinearMap.id Real (VarPhase (E := E))) ∈
        Metric.ball (var2PhaseZero (I := I) (E := E) x) r) :
    ContDiffAt Real 1
      (fun q' : VarPhase (E := E) =>
        (Ω (q', ContinuousLinearMap.id Real (VarPhase (E := E))) b).1)
      q := by
  let idLin : VarLin (E := E) := ContinuousLinearMap.id Real (VarPhase (E := E))
  let q0 : VarPhase (E := E) := varPhaseZero (I := I) (E := E) x
  have hFdiff :
      ∀ p ∈ Metric.closedBall q0 (a : Real),
        DifferentiableAt Real (varSpray (I := I) g x) p := by
    intro p hp
    have hp2 :
        (p, idLin) ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a := by
      rw [Metric.mem_closedBall] at hp ⊢
      rw [Prod.dist_eq]
      have hid : dist idLin (ContinuousLinearMap.id Real (VarPhase (E := E))) = 0 := by
        simp [idLin]
      have hq : dist p q0 ≤ (a : Real) := hp
      have hmax : max (dist p q0) (dist idLin
          (ContinuousLinearMap.id Real (VarPhase (E := E)))) ≤ (a : Real) := by
        rw [hid, max_eq_left]
        · exact hq
        · exact dist_nonneg
      simpa [var2PhaseZero, q0] using hmax
    have hp_src := hsrc hp2
    exact
      (varSpray_contDiffAt_of_mem (I := I) g x hp_src.1 hp_src.2).differentiableAt
        (by simp)
  have hDcont :
      ∀ p ∈ Metric.closedBall q0 (a : Real),
        ContinuousAt (fderiv Real (varSpray (I := I) g x)) p := by
    intro p hp
    have hp2 :
        (p, idLin) ∈ Metric.closedBall (var2PhaseZero (I := I) (E := E) x) a := by
      rw [Metric.mem_closedBall] at hp ⊢
      rw [Prod.dist_eq]
      have hid : dist idLin (ContinuousLinearMap.id Real (VarPhase (E := E))) = 0 := by
        simp [idLin]
      have hq : dist p q0 ≤ (a : Real) := hp
      have hmax : max (dist p q0) (dist idLin
          (ContinuousLinearMap.id Real (VarPhase (E := E)))) ≤ (a : Real) := by
        rw [hid, max_eq_left]
        · exact hq
        · exact dist_nonneg
      simpa [var2PhaseZero, q0] using hmax
    have hp_src := hsrc hp2
    have hcd :
        ContDiffAt Real ∞ (varSpray (I := I) g x) p :=
      varSpray_contDiffAt_of_mem (I := I) g x hp_src.1 hp_src.2
    exact (hcd.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).continuousAt
  exact
    controlledBaseEndpoint_contDiffAt_one_of_fderiv_ball
      (X := VarPhase (E := E)) (F := varSpray (I := I) g x)
      (x0 := q0) (z := q) (Ψ := Ω)
      (a := a) (r := r) (L' := L') (ε := ε) (b := b)
      hb0 hb hflow hbound hLip hFdiff hDcont
      (by
        change
          (q, ContinuousLinearMap.id Real (VarPhase (E := E))) ∈
            Metric.ball (var2PhaseZero (I := I) (E := E) x) r
        exact hqopen)

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The base projection of a second augmented solution agrees with the
first-level augmented Picard flow through the same first-level initial point,
as long as the projected curve stays in the first-level controlling ball. -/
theorem var2Base_eq_varFlow_of_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {eps delta : Real} (heps : 0 < eps) (hdelta : 0 < delta)
    (hdle : delta ≤ eps)
    {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - eps) (tmax := 0 + eps)
      ⟨0, by simp [le_of_lt heps]⟩
      (varPhaseZero (I := I) (E := E) x)
      a r L K)
    {Psi : VarPhase (E := E) -> Real -> VarPhase (E := E)}
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Psi p 0 = p ∧
          ∀ t ∈ Set.Icc (-eps) eps,
            HasDerivWithinAt (Psi p)
              (varSpray (I := I) g x (Psi p t))
              (Set.Icc (-eps) eps) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Psi p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    {Omega : VarPhase (E := E) × VarLin (E := E) -> Real ->
      VarPhase (E := E) × VarLin (E := E)}
    {p : VarPhase (E := E)}
    (hp : p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hOinit :
      Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) 0 =
        (p, ContinuousLinearMap.id Real (VarPhase (E := E))))
    (hOderiv :
      ∀ t ∈ Set.Icc (-delta) delta,
        HasDerivWithinAt
          (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))))
          (variationalRHS (varSpray (I := I) g x)
            (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t))
          (Set.Icc (-delta) delta) t)
    (hObound :
      ∀ t ∈ Set.Icc (-delta) delta,
        (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1 ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) :
    ∀ t ∈ Set.Icc (-delta) delta,
      (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1 =
        Psi p t := by
  let t0delta : Set.Icc (0 - delta) (0 + delta) :=
    ⟨0, by simp [le_of_lt hdelta]⟩
  have hpldelta :
      IsPicardLindelof
        (fun _ : Real => varSpray (I := I) g x)
        (tmin := 0 - delta) (tmax := 0 + delta)
        t0delta
        (varPhaseZero (I := I) (E := E) x)
        a r L K := by
    exact hpl.shrink_time t0delta (by rfl) (by linarith) (by linarith)
  have hflowdelta :
      ∀ q ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Psi q t0delta = q ∧
          ∀ t ∈ Set.Icc (0 - delta) (0 + delta),
            HasDerivWithinAt (Psi q)
              ((fun _ : Real => varSpray (I := I) g x) t (Psi q t))
              (Set.Icc (0 - delta) (0 + delta)) t := by
    intro q hq
    refine ⟨by simpa [t0delta] using (hflow q hq).1, ?_⟩
    intro t ht
    have hteps : t ∈ Set.Icc (-eps) eps := by
      constructor <;> linarith [ht.1, ht.2, hdle]
    have hwithin := (hflow q hq).2 t hteps
    exact hwithin.mono (by
      intro s hs
      constructor <;> linarith [hs.1, hs.2, hdle])
  have ht0delta : (t0delta : Real) ∈ Set.Ioo (0 - delta) (0 + delta) := by
    simpa [t0delta] using hdelta
  let beta : Real -> VarPhase (E := E) :=
    fun t => (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1
  have hbetawithin :
      ∀ t ∈ Set.Icc (0 - delta) (0 + delta),
        HasDerivWithinAt beta
          ((fun _ : Real => varSpray (I := I) g x) t (beta t))
          (Set.Icc (0 - delta) (0 + delta)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (-delta) delta := by simpa using ht
    let idLin : VarLin (E := E) :=
      ContinuousLinearMap.id Real (VarPhase (E := E))
    have hfst :
        HasFDerivWithinAt (fun q : VarPhase (E := E) × VarLin (E := E) => q.1)
          (ContinuousLinearMap.fst Real (VarPhase (E := E)) (VarLin (E := E)))
          Set.univ (Omega (p, idLin) t) :=
      (hasFDerivAt_fst (𝕜 := Real) (E := VarPhase (E := E))
        (F := VarLin (E := E)) (p := Omega (p, idLin) t)).hasFDerivWithinAt
    have hmaps :
        Set.MapsTo (Omega (p, idLin)) (Set.Icc (0 - delta) (0 + delta)) Set.univ := by
      intro y hy
      trivial
    have hO' :
        HasDerivWithinAt (Omega (p, idLin))
          (variationalRHS (varSpray (I := I) g x) (Omega (p, idLin) t))
          (Set.Icc (0 - delta) (0 + delta)) t := by
      simpa [idLin] using hOderiv t ht'
    have hcomp := hfst.comp_hasDerivWithinAt t hO' hmaps
    change HasDerivWithinAt
      (fun τ : Real => (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) τ).1)
      (varSpray (I := I) g x
        (Omega (p, ContinuousLinearMap.id Real (VarPhase (E := E))) t).1)
      (Set.Icc (0 - delta) (0 + delta)) t
    simpa [idLin, variationalRHS, paramVariationalRHS, Function.comp_def] using hcomp
  have hbetacont :
      ContinuousOn beta (Set.Icc (0 - delta) (0 + delta)) := by
    exact HasDerivWithinAt.continuousOn hbetawithin
  have hbetaderiv :
      ∀ t ∈ Set.Ioo (0 - delta) (0 + delta),
        HasDerivAt beta
          ((fun _ : Real => varSpray (I := I) g x) t (beta t)) t := by
    intro t ht
    have hwithin := hbetawithin t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc (0 - delta) (0 + delta) ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hbeta0 : beta t0delta = p := by
    simpa [beta, t0delta] using congrArg Prod.fst hOinit
  have hbetabound :
      ∀ t ∈ Set.Icc (0 - delta) (0 + delta),
        beta t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a := by
    intro t ht
    have ht' : t ∈ Set.Icc (-delta) delta := by simpa using ht
    simpa [beta] using hObound t ht'
  have hEq :=
    plFlow_eq_of_solution_at
      (F := VarPhase (E := E))
      (f := fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - delta) (tmax := 0 + delta)
      (t0 := t0delta)
      (x0 := varPhaseZero (I := I) (E := E) x)
      (x := p)
      (a := a) (r := r) (L := L) (K := K)
      hpldelta ht0delta hp
      (alpha := Psi) hflowdelta hbound
      (beta := beta)
      hbeta0 hbetacont hbetaderiv hbetabound
  intro t ht
  have ht' : t ∈ Set.Icc (0 - delta) (0 + delta) := by simpa using ht
  exact (hEq t ht').symm

/-- Source control descends from a convex augmented closed ball to base-phase
segments. -/
theorem varBase_segment_src_of_bound
    [I.Boundaryless]
    (x : M) {a : NNReal}
    {p q : ModelPhase (E := E) × ModelLin (E := E)}
    (hp : p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hq : q ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    {u : ModelPhase (E := E)}
    (hu : u ∈ segment Real p.1 q.1) :
    u ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
      (phaseOfModel (I := I) x u).proj ∈ (extChartAt I x).source := by
  rcases hu with ⟨c, d, hc, hd, hcd, hu⟩
  let w : ModelPhase (E := E) × ModelLin (E := E) := c • p + d • q
  have hwseg : w ∈ segment Real p q := by
    refine ⟨c, d, hc, hd, hcd, ?_⟩
    rfl
  have hwball :
      w ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a :=
    (convex_closedBall (varPhaseZero (I := I) (E := E) x) (a : Real)).segment_subset
      hp hq hwseg
  have hwsrc := hsrc hwball
  rw [← hu]
  simpa [w]
    using hwsrc

/-- Base component of an augmented variational flow. -/
def varBaseFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).1

/-- The model flow extracted from an augmented variational flow by fixing the
linear initial condition to the identity and projecting to the base phase. -/
def varModelFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)) :
    ModelPhase (E := E) -> Real -> ModelPhase (E := E) :=
  fun z t => varBaseFlow (E := E) Ψ z t

@[simp] theorem varModelFlow_apply
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) :
    varModelFlow (E := E) Ψ z t = varBaseFlow (E := E) Ψ z t := rfl

/-- Source control for the segment between two base trajectories, obtained from
the source-controlled augmented flow bound. -/
theorem varBase_segment_src_of_flow_bound
    [I.Boundaryless]
    (x : M)
    {a r : NNReal}
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z h : ModelPhase (E := E)} {t : Real}
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ u ∈ segment Real
        (varBaseFlow (E := E) Ψ z t)
        (varBaseFlow (E := E) Ψ (z + h) t),
      u ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x u).proj ∈ (extChartAt I x).source := by
  intro u hu
  exact
    varBase_segment_src_of_bound (I := I) (E := E) x
      (hbound (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) hz0 t)
      (hbound (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) hzh0 t)
      hsrc hu

/-- Linearized component of an augmented variational flow. -/
def varDerivFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelLin (E := E) :=
  (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).2

/-- Explicit linear flow generated by `modelSprayLin`: `(dq, dv) ↦
`(dq + t • dv, dv)`. -/
def phaseLinFlow (t : Real) : ModelLin (E := E) :=
  ContinuousLinearMap.id Real (ModelPhase (E := E)) +
    t • modelSprayLin (E := E)

/-- The explicit augmented trajectory through the zero phase: the base phase is
fixed and the linear component is the flow of `modelSprayLin`. -/
def varZeroPhaseLin (x : M) (t : Real) :
    ModelPhase (E := E) × ModelLin (E := E) :=
  (extChartAt I.tangent (phaseZero (I := I) x)
    (phaseZero (I := I) x),
    phaseLinFlow (E := E) t)

@[simp] theorem phaseLinFlow_fst (t : Real) (z : ModelPhase (E := E)) :
    (phaseLinFlow (E := E) t z).1 = z.1 + t • z.2 := by
  simp [phaseLinFlow, modelSprayLin]

@[simp] theorem phaseLinFlow_snd (t : Real) (z : ModelPhase (E := E)) :
    (phaseLinFlow (E := E) t z).2 = z.2 := by
  simp [phaseLinFlow, modelSprayLin]

@[simp] theorem phaseLinFlow_zero :
    phaseLinFlow (E := E) 0 =
      ContinuousLinearMap.id Real (ModelPhase (E := E)) := by
  ext z <;> simp [phaseLinFlow]

@[simp] theorem phaseLinFlow_fiber_fst (t : Real) (v : E) :
    (phaseLinFlow (E := E) t (0, v)).1 = t • v := by
  simp

@[simp] theorem modelSprayLin_comp_phaseLinFlow (t : Real) :
    (modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t) =
      modelSprayLin (E := E) := by
  ext z <;> simp [phaseLinFlow, modelSprayLin]

/-- The explicit linear phase flow solves the variational equation at the zero
phase. -/
theorem phaseLinFlow_hasDerivAt (t : Real) :
    HasDerivAt
      (fun s : Real => phaseLinFlow (E := E) s)
      ((modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t))
      t := by
  have hlin :
      HasDerivAt
        (fun s : Real => s • modelSprayLin (E := E))
        (modelSprayLin (E := E)) t := by
    simpa using (hasDerivAt_id t).smul_const (modelSprayLin (E := E))
  rw [modelSprayLin_comp_phaseLinFlow]
  simpa [phaseLinFlow] using
    hlin.const_add (ContinuousLinearMap.id Real (ModelPhase (E := E)))

@[simp] theorem varZeroPhaseLin_zero (x : M) :
    varZeroPhaseLin (I := I) (E := E) x 0 =
      varPhaseZero (I := I) (E := E) x := by
  simp [varZeroPhaseLin, varPhaseZero]

/-- Along the zero base phase, the augmented variational vector field is the
explicit linearized spray equation. -/
theorem varSpray_zero_phaseLin
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    varSpray (I := I) g x (varZeroPhaseLin (I := I) (E := E) x t) =
      (0, (modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t)) := by
  apply Prod.ext
  · simpa using modelSpray_zero (I := I) g x
  · have hfd :
        fderiv Real (modelSpray (I := I) g x)
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) =
          modelSprayLin (E := E) :=
      (spray_fderiv_zero (I := I) g x).fderiv
    simp only [varSpray, varZeroPhaseLin]
    change
      (fderiv Real (modelSpray (I := I) g x)
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x))).comp
          (phaseLinFlow (E := E) t) =
        (modelSprayLin (E := E)).comp (phaseLinFlow (E := E) t)
    rw [hfd]

/-- The curve with zero base phase and explicit linearized flow solves the
augmented variational ODE. -/
theorem varZeroPhaseLin_hasDerivAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    HasDerivAt
      (varZeroPhaseLin (I := I) (E := E) x)
      (varSpray (I := I) g x (varZeroPhaseLin (I := I) (E := E) x t))
      t := by
  have hbase :
      HasDerivAt
        (fun _s : Real =>
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))
        (0 : ModelPhase (E := E)) t :=
    hasDerivAt_const (x := t)
      (c := extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
  have hlin := phaseLinFlow_hasDerivAt (E := E) t
  have hprod := hbase.prodMk hlin
  rw [varSpray_zero_phaseLin (I := I) g x t]
  simpa [varZeroPhaseLin] using hprod

/-- The explicit zero-phase linearized trajectory stays in any positive
augmented closed ball after shrinking time around zero. -/
theorem varZeroPhaseLin_mem_closedBall_small
    (x : M) {a : NNReal} (ha : 0 < a) :
    ∃ δ : Real, 0 < δ ∧
      ∀ t ∈ Set.Icc (-δ) δ,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a := by
  have hbase :
      ContinuousAt
        (fun _s : Real =>
          extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) 0 :=
    continuousAt_const
  have hlin :
      ContinuousAt (fun s : Real => phaseLinFlow (E := E) s) 0 :=
    (phaseLinFlow_hasDerivAt (E := E) 0).continuousAt
  have hcont :
      ContinuousAt (varZeroPhaseLin (I := I) (E := E) x) 0 := by
    simpa [varZeroPhaseLin] using hbase.prodMk hlin
  have hball :
      Metric.ball (varPhaseZero (I := I) (E := E) x) (a : Real) ∈
        𝓝 (varPhaseZero (I := I) (E := E) x) :=
    Metric.ball_mem_nhds _ (by exact_mod_cast ha)
  have hev :
      ∀ᶠ t : Real in 𝓝 0,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.ball (varPhaseZero (I := I) (E := E) x) (a : Real) :=
    hcont.eventually (by simpa using hball)
  rcases Metric.mem_nhds_iff.mp hev with ⟨ρ, hρ, hρsub⟩
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  intro t ht
  have ht_abs : |t| ≤ ρ / 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have htball : t ∈ Metric.ball (0 : Real) ρ := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [sub_zero] using lt_of_le_of_lt ht_abs (half_lt_self hρ)
  exact Metric.ball_subset_closedBall (hρsub htball)

/-- On a sufficiently small time interval, any Picard-Lindelof augmented flow
through the zero variational phase agrees with the explicit zero-phase
linearized trajectory. -/
theorem varFlow_zero_phaseLin_of_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε δ : Real} (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε)
    {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - ε) (tmax := 0 + ε)
      ⟨0, by simp [le_of_lt hε]⟩
      (varPhaseZero (I := I) (E := E) x)
      a r L K)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
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
          Ψ p t ∈ Metric.closedBall
            (varPhaseZero (I := I) (E := E) x) a)
    (hcand :
      ∀ t ∈ Set.Icc (-δ) δ,
        varZeroPhaseLin (I := I) (E := E) x t ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) :
    ∀ t ∈ Set.Icc (-δ) δ,
      Ψ (varPhaseZero (I := I) (E := E) x) t =
        varZeroPhaseLin (I := I) (E := E) x t := by
  let t0ε : Set.Icc (0 - ε) (0 + ε) := ⟨0, by simp [le_of_lt hε]⟩
  let t0δ : Set.Icc (0 - δ) (0 + δ) := ⟨0, by simp [le_of_lt hδ]⟩
  have hplδ :
      IsPicardLindelof
        (fun _ : Real => varSpray (I := I) g x)
        (tmin := 0 - δ) (tmax := 0 + δ)
        t0δ
        (varPhaseZero (I := I) (E := E) x)
        a r L K := by
    exact hpl.shrink_time t0δ (by rfl) (by linarith) (by linarith)
  have hflowδ :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p t0δ = p ∧
          ∀ t ∈ Set.Icc (0 - δ) (0 + δ),
            HasDerivWithinAt (Ψ p)
              ((fun _ : Real => varSpray (I := I) g x) t (Ψ p t))
              (Set.Icc (0 - δ) (0 + δ)) t := by
    intro p hp
    refine ⟨by simpa [t0δ] using (hflow p hp).1, ?_⟩
    intro t ht
    have htε : t ∈ Set.Icc (-ε) ε := by
      constructor <;> linarith [ht.1, ht.2, hδε]
    have hwithin := (hflow p hp).2 t htε
    exact hwithin.mono (by
      intro s hs
      constructor <;> linarith [hs.1, hs.2, hδε])
  have ht0δ : (t0δ : Real) ∈ Set.Ioo (0 - δ) (0 + δ) := by
    simpa [t0δ] using hδ
  have hβcont :
      ContinuousOn (varZeroPhaseLin (I := I) (E := E) x)
        (Set.Icc (0 - δ) (0 + δ)) := by
    intro t ht
    exact (varZeroPhaseLin_hasDerivAt (I := I) g x t).continuousAt.continuousWithinAt
  have hβderiv :
      ∀ t ∈ Set.Ioo (0 - δ) (0 + δ),
        HasDerivAt (varZeroPhaseLin (I := I) (E := E) x)
          ((fun _ : Real => varSpray (I := I) g x) t
            (varZeroPhaseLin (I := I) (E := E) x t)) t := by
    intro t _ht
    simpa using varZeroPhaseLin_hasDerivAt (I := I) g x t
  have hEq :=
    plFlow_eq_of_solution
      (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x)
      (tmin := 0 - δ) (tmax := 0 + δ)
      (t0 := t0δ)
      (x0 := varPhaseZero (I := I) (E := E) x)
      (a := a) (r := r) (L := L) (K := K)
      hplδ ht0δ
      (α := Ψ) hflowδ hbound
      (β := varZeroPhaseLin (I := I) (E := E) x)
      (by simp [t0δ]) hβcont hβderiv
      (by
        intro t ht
        have ht' : t ∈ Set.Icc (-δ) δ := by simpa using ht
        exact hcand t ht')
  intro t ht
  have ht' : t ∈ Set.Icc (0 - δ) (0 + δ) := by simpa using ht
  exact hEq t ht'

/-- The base trajectory of an augmented solution is continuous on any smaller
time interval. -/
theorem varBaseFlow_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨ :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
      (Set.Icc (0 : Real) b) := by
  have hcont :
      ContinuousOn
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (Set.Icc (0 : Real) b) :=
    (HasDerivWithinAt.continuousOn hΨ).mono hb
  simpa [varBaseFlow] using continuous_fst.comp_continuousOn hcont

/-- The linearized trajectory of an augmented solution is continuous on any
smaller time interval. -/
theorem varDerivFlow_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨ :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (fun t => varDerivFlow (E := E) Ψ z t)
      (Set.Icc (0 : Real) b) := by
  have hcont :
      ContinuousOn
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (Set.Icc (0 : Real) b) :=
    (HasDerivWithinAt.continuousOn hΨ).mono hb
  simpa [varDerivFlow] using continuous_snd.comp_continuousOn hcont

/-- The derivative of the model spray is bounded along a source-controlled base
trajectory on a compact time interval. -/
theorem modelSpray_fderiv_bound_on_baseFlow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hsrc : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source) :
    ∃ B : Real, ∀ t ∈ Set.Icc (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B := by
  have hbase :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  have hDF :
      ContinuousOn
        (fun t =>
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t))
        (Set.Icc (0 : Real) b) := by
    intro t ht
    have hDFat :
        ContinuousAt
          (fderiv Real (modelSpray (I := I) g x))
          (varBaseFlow (E := E) Ψ z t) := by
      exact
        ((modelSpray_contDiffAt_of_mem (I := I) g x
          (hsrc t ht).1 (hsrc t ht).2).fderiv_right (m := 1)
          (by
            exact WithTop.coe_le_coe.2
              (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousAt
    exact hDFat.comp_continuousWithinAt (hbase.continuousWithinAt ht)
  exact isCompact_Icc.exists_bound_of_continuousOn hDF

/-- Uniform continuity of `D(modelSpray)` in a tube around a compact,
source-controlled base trajectory. -/
theorem modelSpray_fderiv_uniform_tube
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {K : Set Real} (hK : IsCompact K)
    {γ : Real -> ModelPhase (E := E)}
    (hγ : ContinuousOn γ K)
    (hsrc : ∀ t ∈ K,
      γ t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (γ t)).proj ∈ (extChartAt I x).source) :
    ∀ c > 0, ∃ δ > 0, ∀ t ∈ K, ∀ u : ModelPhase (E := E),
      dist u (γ t) < δ ->
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x) (γ t)‖ ≤ c := by
  intro c hc
  let D : ModelPhase (E := E) -> ModelLin (E := E) :=
    fderiv Real (modelSpray (I := I) g x)
  have hcomp : IsCompact (γ '' K) :=
    hK.image_of_continuousOn hγ
  have hDcont : ∀ y ∈ γ '' K, ContinuousAt D y := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact
      ((modelSpray_contDiffAt_of_mem (I := I) g x
        (hsrc t ht).1 (hsrc t ht).2).fderiv_right (m := 1)
        (by
          exact WithTop.coe_le_coe.2
            (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousAt
  have hU :
      {p : ModelPhase (E := E) × ModelPhase (E := E) |
        p.1 ∈ γ '' K ->
          (D p.1, D p.2) ∈
            {q : ModelLin (E := E) × ModelLin (E := E) |
              dist q.1 q.2 < c}} ∈
        𝓤 (ModelPhase (E := E)) :=
    hcomp.uniformContinuousAt_of_continuousAt D hDcont
      (Metric.dist_mem_uniformity hc)
  rcases Metric.mem_uniformity_dist.mp hU with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu
  have hpair :
      ((γ t, u) : ModelPhase (E := E) × ModelPhase (E := E)) ∈
        {p : ModelPhase (E := E) × ModelPhase (E := E) |
          p.1 ∈ γ '' K ->
            (D p.1, D p.2) ∈
              {q : ModelLin (E := E) × ModelLin (E := E) |
                dist q.1 q.2 < c}} :=
    hδsub (by simpa [dist_comm] using hu)
  have hγmem : γ t ∈ γ '' K := ⟨t, ht, rfl⟩
  have hdist : dist (D (γ t)) (D u) < c := hpair hγmem
  have hnorm : ‖D u - D (γ t)‖ < c := by
    have hdist' : dist (D u) (D (γ t)) < c := by
      simpa [dist_comm] using hdist
    simpa [D, dist_eq_norm] using hdist'
  simpa [D] using le_of_lt hnorm

@[simp] theorem varBaseFlow_zero_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)}
    (hΨ0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varBaseFlow (E := E) Ψ z 0 = z := by
  simpa [varBaseFlow] using congrArg Prod.fst hΨ0

@[simp] theorem varDerivFlow_zero_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)}
    (hΨ0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varDerivFlow (E := E) Ψ z 0 =
      ContinuousLinearMap.id Real (ModelPhase (E := E)) := by
  simpa [varDerivFlow] using congrArg Prod.snd hΨ0

/-- A base phase in the model closed ball gives an augmented phase in the
corresponding variational closed ball when the linear component is the identity. -/
theorem varPhase_mem_closedBall_of_base_mem
    {x : M} {r : NNReal} {z : ModelPhase (E := E)}
    (hz : z ∈ Metric.closedBall
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) r) :
    (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) r := by
  rw [Metric.mem_closedBall] at hz ⊢
  simpa [varPhaseZero, Prod.dist_eq] using hz

/-- The base component of an augmented flow solves the original model ODE. -/
theorem varBaseFlow_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z : ModelPhase (E := E)} {ε t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varBaseFlow (E := E) Ψ z)
      (modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t))
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let p : Z := z
  let A : L := ContinuousLinearMap.id Real Z
  have hfst :
      HasFDerivWithinAt (fun q : Z × L => q.1)
        (ContinuousLinearMap.fst Real Z L) Set.univ
        (Ψ (p, A) t) :=
    (hasFDerivAt_fst (𝕜 := Real) (E := Z) (F := L)
      (p := Ψ (p, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (p, A)) (Set.Icc (-ε) ε) Set.univ := by
    intro y hy
    trivial
  have hcomp := hfst.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, varBaseFlow, varSpray, Z, L, p, A] using hcomp

/-- A source-controlled augmented variational flow projects to a functional
model flow solving the original model spray ODE. -/
theorem varModelFlow_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {r : NNReal} {ε : Real}
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t) :
    ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      varModelFlow (E := E) Ψ z 0 = z ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt
            (varModelFlow (E := E) Ψ z)
            (modelSpray (I := I) g x (varModelFlow (E := E) Ψ z t))
            (Set.Icc (-ε) ε) t := by
  intro z hz
  have hp :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    varPhase_mem_closedBall_of_base_mem (I := I) (E := E) hz
  refine ⟨?_, ?_⟩
  · exact varBaseFlow_zero_of_flow (E := E) (hflow _ hp).1
  · intro t ht
    exact varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x
      ((hflow _ hp).2 t ht)

/-- A closed-ball-bounded augmented variational flow projects to a
closed-ball-bounded model flow. -/
theorem varModelFlow_bound
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (x : M) {a r : NNReal}
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) :
    ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t : Real,
        varModelFlow (E := E) Ψ z t ∈
          Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) a := by
  intro z hz t
  have hp :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    varPhase_mem_closedBall_of_base_mem (I := I) (E := E) hz
  have hq := hbound _ hp t
  rw [Metric.mem_closedBall] at hq ⊢
  let z0 : ModelPhase (E := E) :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hfst :
      dist (varModelFlow (E := E) Ψ z t) z0 ≤
        dist (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t)
          (varPhaseZero (I := I) (E := E) x) := by
    change
      dist (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).1 z0 ≤
        dist (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t)
          (z0, ContinuousLinearMap.id Real (ModelPhase (E := E)))
    rw [Prod.dist_eq]
    exact le_max_left _ _
  exact hfst.trans hq

/-- Source control for the projected model flow extracted from an augmented
closed-ball-bounded variational flow. -/
theorem varModelFlow_src
    [I.Boundaryless]
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (x : M) {a r : NNReal} {ε : Real}
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈
              (extChartAt I x).source}) :
    ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t ∈ Set.Icc (-ε) ε,
        varModelFlow (E := E) Ψ z t ∈
          (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x (varModelFlow (E := E) Ψ z t)).proj ∈
            (extChartAt I x).source := by
  intro z hz t _ht
  have hp :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    varPhase_mem_closedBall_of_base_mem (I := I) (E := E) hz
  have hs := hsrc (hbound _ hp t)
  simpa [varModelFlow, varBaseFlow] using hs

/-- The linear component of an augmented flow solves the variational equation. -/
theorem varDerivFlow_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z : ModelPhase (E := E)} {ε t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varDerivFlow (E := E) Ψ z)
      ((fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)).comp
        (varDerivFlow (E := E) Ψ z t))
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let p : Z := z
  let A : L := ContinuousLinearMap.id Real Z
  have hsnd :
      HasFDerivWithinAt (fun q : Z × L => q.2)
        (ContinuousLinearMap.snd Real Z L) Set.univ
        (Ψ (p, A) t) :=
    (hasFDerivAt_snd (𝕜 := Real) (E := Z) (F := L)
      (p := Ψ (p, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (p, A)) (Set.Icc (-ε) ε) Set.univ := by
    intro y hy
    trivial
  have hcomp := hsnd.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, varBaseFlow, varDerivFlow, varSpray, Z, L, p, A] using hcomp

/-- Error between the base flow at `z + h` and the linearized approximation
from the augmented flow at `z`. -/
def varError
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  varBaseFlow (E := E) Ψ (z + h) t -
    varBaseFlow (E := E) Ψ z t -
    varDerivFlow (E := E) Ψ z t h

/-- The variational approximation error is continuous on any smaller time
interval where both augmented trajectories solve the ODE. -/
theorem varError_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z h : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨzh :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b) := by
  have hbase_zh :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ (z + h) t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨzh
  have hbase_z :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  have hder_z :
      ContinuousOn (fun t => varDerivFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varDerivFlow_continuousOn_of_flow (E := E) hb hΨz
  simpa [varError, flowError] using
    flowError_continuousOn (Φ := varBaseFlow (E := E) Ψ)
      (A := varDerivFlow (E := E) Ψ) hbase_zh hbase_z hder_z

/-- Raw right-hand side of the error equation. -/
def varErrorRHS
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  modelSpray (I := I) g x (varBaseFlow (E := E) Ψ (z + h) t) -
    modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t) -
    fderiv Real (modelSpray (I := I) g x)
      (varBaseFlow (E := E) Ψ z t)
      (varDerivFlow (E := E) Ψ z t h)

/-- Taylor residual part of the error equation. -/
def varTaylorRem
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  modelSpray (I := I) g x (varBaseFlow (E := E) Ψ (z + h) t) -
    modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t) -
    fderiv Real (modelSpray (I := I) g x)
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t -
        varBaseFlow (E := E) Ψ z t)

/-- Pointwise Taylor-residual estimate for the error equation. -/
theorem varTaylorRem_norm_le
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C) :
    ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
      C * ‖varBaseFlow (E := E) Ψ (z + h) t -
        varBaseFlow (E := E) Ψ z t‖ := by
  simpa [varTaylorRem] using
    modelSpray_taylor_bound (I := I) g x hs hctrl hz hzh hD

/-- Lipschitz dependence of the augmented flow controls the separation of the
base components. -/
theorem varBaseFlow_dist_le_of_lipschitz
    (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {r L' : NNReal} {z h : ModelPhase (E := E)} {t : Real}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    dist (varBaseFlow (E := E) Ψ (z + h) t)
      (varBaseFlow (E := E) Ψ z t) ≤ (L' : Real) * ‖h‖ := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let pzh : Z × L := (z + h, ContinuousLinearMap.id Real Z)
  let pz : Z × L := (z, ContinuousLinearMap.id Real Z)
  have hdist := hLip.dist_le_mul pzh hzh pz hz
  have hfst :
      dist (varBaseFlow (E := E) Ψ (z + h) t)
        (varBaseFlow (E := E) Ψ z t) ≤
          dist (Ψ pzh t) (Ψ pz t) := by
    change dist (Ψ pzh t).1 (Ψ pz t).1 ≤ dist (Ψ pzh t) (Ψ pz t)
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hpdist : dist pzh pz = ‖h‖ := by
    have hzdist : dist (z + h) z = ‖h‖ := by
      rw [dist_eq_norm]
      have hsub : z + h - z = h := by
        abel
      rw [hsub]
    simp [pzh, pz, dist_prod_same_right, hzdist]
  exact hfst.trans (by simpa [hpdist] using hdist)

/-- The Lipschitz flow estimate turns the compact tube continuity of
`D(modelSpray)` into a uniform derivative-difference bound on trajectory
segments for sufficiently small initial perturbations. -/
theorem modelSpray_fderiv_segment_small_of_lipschitz
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {ε b : Real} {r L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hsrc_base : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ η > 0, ∃ ρ > 0, ∀ h : ModelPhase (E := E),
      (L' : Real) * ‖h‖ < ρ ->
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r ->
      ∀ t ∈ Set.Ico (0 : Real) b,
        ∀ u ∈ segment Real
            (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t),
          ‖fderiv Real (modelSpray (I := I) g x) u -
            fderiv Real (modelSpray (I := I) g x)
              (varBaseFlow (E := E) Ψ z t)‖ ≤ η := by
  intro η hη
  have hbase :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  obtain ⟨ρ, hρ, hρsmall⟩ :=
    modelSpray_fderiv_uniform_tube (I := I) g x
      (K := Set.Icc (0 : Real) b) isCompact_Icc hbase hsrc_base η hη
  refine ⟨ρ, hρ, ?_⟩
  intro h hsmall hzh0 t ht u hu
  have htcc : t ∈ Set.Icc (0 : Real) b := ⟨ht.1, le_of_lt ht.2⟩
  have hsegball :
      u ∈ Metric.closedBall
          (varBaseFlow (E := E) Ψ z t)
          (dist (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t)) :=
    segment_subset_closedBall_left
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t) hu
  have hbase_dist :
      dist (varBaseFlow (E := E) Ψ z t)
        (varBaseFlow (E := E) Ψ (z + h) t) ≤ (L' : Real) * ‖h‖ := by
    simpa [dist_comm] using
      varBaseFlow_dist_le_of_lipschitz (E := E) x (hLip t ht) hz0 hzh0
  have hu_dist :
      dist u (varBaseFlow (E := E) Ψ z t) < ρ := by
    have hle :
        dist u (varBaseFlow (E := E) Ψ z t) ≤
          dist (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t) := by
      simpa [Metric.mem_closedBall] using hsegball
    exact lt_of_le_of_lt (hle.trans hbase_dist) hsmall
  exact hρsmall t htcc u hu_dist

/-- Taylor residual estimate after applying the augmented-flow Lipschitz bound
to the base separation. -/
theorem varTaylorRem_norm_le_of_lipschitz
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    {r L' : NNReal}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
      C * ((L' : Real) * ‖h‖) := by
  have hTaylor :=
    varTaylorRem_norm_le (I := I) g x Ψ z h t hs hctrl hz hzh hD
  have hsep :=
    varBaseFlow_dist_le_of_lipschitz (I := I) (E := E) x hLip hz0 hzh0
  rw [dist_eq_norm] at hsep
  have hC : 0 ≤ C := (norm_nonneg _).trans (hD _ hz)
  exact hTaylor.trans (mul_le_mul_of_nonneg_left hsep hC)

/-- Gronwall-ready pointwise estimate for the approximation-error RHS. -/
theorem varErrorRHS_norm_le
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {B C : Real}
    (hB :
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    {r L' : NNReal}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
      B * ‖varError (E := E) Ψ z h t‖ +
        C * ((L' : Real) * ‖h‖) := by
  have hRem :
      ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
        C * ((L' : Real) * ‖h‖) :=
    varTaylorRem_norm_le_of_lipschitz (I := I) g x Ψ z h t
      hs hctrl hz hzh hD hLip hz0 hzh0
  change
    ‖flowErrorRHS (modelSpray (I := I) g x)
        (varBaseFlow (E := E) Ψ) (varDerivFlow (E := E) Ψ) z h t‖ ≤
      B * ‖flowError (varBaseFlow (E := E) Ψ)
          (varDerivFlow (E := E) Ψ) z h t‖ +
        C * ((L' : Real) * ‖h‖)
  exact flowErrorRHS_norm_le
    (F := modelSpray (I := I) g x)
    (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ)
    z h t hB (by simpa [flowTaylorRem, varTaylorRem] using hRem)

/-- The raw error RHS is the Taylor residual plus the linearized equation
applied to the current error. -/
theorem varErrorRHS_eq_taylorRem_add
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) :
    varErrorRHS (I := I) g x Ψ z h t =
      varTaylorRem (I := I) g x Ψ z h t +
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)
          (varError (E := E) Ψ z h t) := by
  change
    flowErrorRHS (modelSpray (I := I) g x)
        (varBaseFlow (E := E) Ψ) (varDerivFlow (E := E) Ψ) z h t =
      flowTaylorRem (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ) z h t +
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)
          (flowError (varBaseFlow (E := E) Ψ) (varDerivFlow (E := E) Ψ) z h t)
  exact flowErrorRHS_eq_taylorRem_add
    (F := modelSpray (I := I) g x)
    (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ) z h t

/-- The approximation error satisfies the expected inhomogeneous linear ODE. -/
theorem varError_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z h : ModelPhase (E := E)} {ε t : Real}
    (hΨzh :
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varError (E := E) Ψ z h)
      (varErrorRHS (I := I) g x Ψ z h t)
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  have hbase_zh :
      HasDerivWithinAt
        (varBaseFlow (E := E) Ψ (z + h))
        (modelSpray (I := I) g x
          (varBaseFlow (E := E) Ψ (z + h) t))
        (Set.Icc (-ε) ε) t :=
    varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x hΨzh
  have hbase_z :
      HasDerivWithinAt
        (varBaseFlow (E := E) Ψ z)
        (modelSpray (I := I) g x
          (varBaseFlow (E := E) Ψ z t))
        (Set.Icc (-ε) ε) t :=
    varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x hΨz
  have hA :
      HasDerivWithinAt
        (varDerivFlow (E := E) Ψ z)
        ((fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)).comp
          (varDerivFlow (E := E) Ψ z t))
        (Set.Icc (-ε) ε) t :=
    varDerivFlow_hasDerivWithinAt (I := I) (E := E) g x hΨz
  simpa [varError, varErrorRHS, flowError, flowErrorRHS, Z] using
    flowError_hasDerivWithinAt
      (F := modelSpray (I := I) g x)
      (Φ := varBaseFlow (E := E) Ψ)
      (A := varDerivFlow (E := E) Ψ)
      (z := z) (h := h) (s := Set.Icc (-ε) ε) (t := t)
      hbase_zh hbase_z hA

/-- Restrict the approximation-error ODE from the Picard time interval to a
smaller closed interval. -/
theorem varError_hasDerivWithinAt_Icc
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z h : ModelPhase (E := E)} {ε a b t : Real}
    (hab : Set.Icc a b ⊆ Set.Icc (-ε) ε)
    (hΨzh :
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varError (E := E) Ψ z h)
      (varErrorRHS (I := I) g x Ψ z h t)
      (Set.Icc a b) t :=
  (varError_hasDerivWithinAt (I := I) g x hΨzh hΨz).mono hab

/-- The approximation error is zero at the initial time for a flow with the
expected augmented initial conditions. -/
theorem varError_zero
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (z h : ModelPhase (E := E))
    (hΨzh :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varError (E := E) Ψ z h 0 = 0 := by
  simp [varError, varBaseFlow, varDerivFlow, hΨzh, hΨz]

/-- If the variational approximation error is little-o in the initial
perturbation, then the linear component of the augmented flow is the Frechet
derivative of the base flow at the fixed time. -/
theorem varBaseFlow_hasFDerivAt_of_error
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {t : Real}
    (herr :
      (fun h : ModelPhase (E := E) => varError (E := E) Ψ z h t)
        =o[𝓝 0] (fun h : ModelPhase (E := E) => h)) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' t)
      (varDerivFlow (E := E) Ψ z t)
      z := by
  exact flow_hasFDerivAt_of_error (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ)
    (by simpa [flowError, varError] using herr)

/-- Fixed-time C1-dependence checkpoint from an eventual Gronwall bound with a
vanishing Taylor-residual coefficient. -/
theorem varBaseFlow_hasFDerivAt_of_gronwall
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {t B L T : Real}
    {C : ModelPhase (E := E) -> Real}
    (hC : Tendsto C (𝓝 0) (𝓝 0))
    (hbound : ∀ᶠ h in 𝓝 (0 : ModelPhase (E := E)),
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' t)
      (varDerivFlow (E := E) Ψ z t)
      z := by
  exact flow_hasFDerivAt_of_gronwall (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ) (C := C) (B := B) (L := L) (T := T)
    hC (by simpa [flowError, varError] using hbound)

/-- Gronwall bound for the approximation error once the error RHS has the
standard linear-plus-forcing estimate. -/
theorem varError_norm_le_gronwall
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a b δ K ε : Real}
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt
        (varError (E := E) Ψ z h)
        (varErrorRHS (I := I) g x Ψ z h t)
        (Set.Ici t) t)
    (ha : ‖varError (E := E) Ψ z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
        K * ‖varError (E := E) Ψ z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound δ K ε (t - a) :=
  flowError_norm_le_gronwall
    (F := modelSpray (I := I) g x)
    (Φ := varBaseFlow (E := E) Ψ)
    (A := varDerivFlow (E := E) Ψ)
    z h (by simpa [flowError, varError] using hcont)
    (by
      intro t ht
      simpa [flowError, flowErrorRHS, varError, varErrorRHS] using hderiv t ht)
    (by simpa [flowError, varError] using ha)
    (by
      intro t ht
      simpa [flowError, flowErrorRHS, varError, varErrorRHS] using hbound t ht)

/-- Version of `varError_norm_le_gronwall` for derivatives known on the
closed interval itself. -/
theorem varError_norm_le_gronwall_Icc
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a b δ K ε : Real}
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt
        (varError (E := E) Ψ z h)
        (varErrorRHS (I := I) g x Ψ z h t)
        (Set.Icc a b) t)
    (ha : ‖varError (E := E) Ψ z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
        K * ‖varError (E := E) Ψ z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound δ K ε (t - a) :=
  varError_norm_le_gronwall (I := I) g x Ψ z h hcont
    (fun t ht =>
      (hderiv t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
    ha hbound

/-- Main checked Gronwall estimate for the variational approximation error on
a fixed forward time interval. -/
theorem varError_norm_le_gronwall_of_flow_bounds
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal} {s : Set (ModelPhase (E := E))}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : ∀ t ∈ Set.Ico (0 : Real) b, varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : ∀ t ∈ Set.Ico (0 : Real) b,
      varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b, ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_Icc (I := I) g x Ψ z h hcont
      (fun t ht => varError_hasDerivWithinAt_Icc (I := I) g x hb
        (hΨzh t ht) (hΨz t ht))
      ?_ ?_
  · have hzero := varError_zero (E := E) z h hΨzh0 hΨz0
    simp [hzero]
  · intro t ht
    exact
      varErrorRHS_norm_le (I := I) g x Ψ z h t hs hctrl
        (hz t ht) (hzh t ht) (hB t ht) (hD t ht)
        (hLip t ht) hz0 hzh0

/-- Time-dependent convex-set version of
`varError_norm_le_gronwall_of_flow_bounds`.

This is the useful form for the C1-dependence proof: at each time the Taylor
estimate can be taken on the segment between the two base trajectories. -/
theorem varError_norm_le_gronwall_of_time_sets
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal}
    {s : Real -> Set (ModelPhase (E := E))}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hs : ∀ t ∈ Set.Ico (0 : Real) b, Convex Real (s t))
    (hctrl : ∀ t ∈ Set.Ico (0 : Real) b, ∀ q ∈ s t,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : ∀ t ∈ Set.Ico (0 : Real) b, varBaseFlow (E := E) Ψ z t ∈ s t)
    (hzh : ∀ t ∈ Set.Ico (0 : Real) b,
      varBaseFlow (E := E) Ψ (z + h) t ∈ s t)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b, ∀ u ∈ s t,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_Icc (I := I) g x Ψ z h hcont
      (fun t ht => varError_hasDerivWithinAt_Icc (I := I) g x hb
        (hΨzh t ht) (hΨz t ht))
      ?_ ?_
  · have hzero := varError_zero (E := E) z h hΨzh0 hΨz0
    simp [hzero]
  · intro t ht
    exact
      varErrorRHS_norm_le (I := I) g x Ψ z h t (hs t ht) (hctrl t ht)
        (hz t ht) (hzh t ht) (hB t ht) (hD t ht)
        (hLip t ht) hz0 hzh0

/-- Segment-specialized Gronwall estimate for the variational approximation
error.

This is the form closest to the differentiability proof: the Taylor estimate is
taken on the segment from `Phi z t` to `Phi (z + h) t`. -/
theorem varError_norm_le_gronwall_of_segment_bounds
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hctrl : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ q ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_of_time_sets (I := I) g x Ψ z h hb
      hcont hΨzh hΨz hΨzh0 hΨz0 ?_ hctrl ?_ ?_ hB hD hLip hz0 hzh0
  · intro t _ht
    exact convex_segment (𝕜 := Real)
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)
  · intro t _ht
    exact left_mem_segment Real
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)
  · intro t _ht
    exact right_mem_segment Real
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)

/-- Segment-specialized Gronwall estimate using source control and continuity
directly from the bounded augmented flow. -/
theorem varError_norm_le_gronwall_of_segment_bounds_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a r : NNReal} {ε b B C : Real} {L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨzh : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_of_segment_bounds (I := I) g x Ψ z h hb
      ?_ (fun t ht => hΨzh t (hb ht)) (fun t ht => hΨz t (hb ht))
      hΨzh0 hΨz0 ?_ hB hD hLip hz0 hzh0
  · exact varError_continuousOn_of_flow (E := E) hb hΨzh hΨz
  · intro t _ht
    exact
      varBase_segment_src_of_flow_bound (I := I) (E := E) x
        hbound hsrc hz0 hzh0

/-- C1-dependence checkpoint: for a source-controlled augmented flow, the
linearized component is the Frechet derivative of the fixed-time base flow at
any interior initial phase. -/
theorem varBaseFlow_hasFDerivAt_of_flow
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
      z := by
  let pz : ModelPhase (E := E) × ModelLin (E := E) :=
    (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))
  have hz0 : pz ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    Metric.ball_subset_closedBall hzopen
  have hsrc_base : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source := by
    intro t ht
    have hs := hsrc (hbound pz hz0 t)
    simpa [pz, varBaseFlow] using hs
  obtain ⟨B, hBcc⟩ :=
    modelSpray_fderiv_bound_on_baseFlow (I := I) g x hb
      (hflow pz hz0).2 hsrc_base
  have hDsmall :=
    modelSpray_fderiv_segment_small_of_lipschitz (I := I) g x
      (Ψ := Ψ) (z := z) (ε := ε) (b := b) (r := r) (L' := L') hb
      (hflow pz hz0).2 hsrc_base
      (fun t ht => hLip t (hb ⟨ht.1, le_of_lt ht.2⟩)) hz0
  have hinit_cont :
      ContinuousAt
        (fun h : ModelPhase (E := E) =>
          (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        0 := by
    have hleft : ContinuousAt (fun h : ModelPhase (E := E) => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : ModelPhase (E := E) => z + h) 0)
    have hright :
        ContinuousAt
          (fun _h : ModelPhase (E := E) =>
            ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 :=
      continuousAt_const
    exact hleft.prodMk_nhds hright
  have hzh_eventually :
      ∀ᶠ h : ModelPhase (E := E) in 𝓝 0,
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) r := by
    have hzopen0 :
        (fun h : ModelPhase (E := E) =>
          (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E)))) 0 ∈
            Metric.ball (varPhaseZero (I := I) (E := E) x) r := by
      simpa using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  have herr :
      (fun h : ModelPhase (E := E) => varError (E := E) Ψ z h b)
        =o[𝓝 0] (fun h : ModelPhase (E := E) => h) := by
    refine
      isLittleO_of_gronwall_bound_eventually
        (X := ModelPhase (E := E)) (Y := ModelPhase (E := E))
        (B := B) (L := (L' : Real)) (T := b) ?_
    intro η hη
    obtain ⟨ρ, hρ, hDρ⟩ := hDsmall η hη
    have hmul_cont :
        Continuous
          (fun h : ModelPhase (E := E) => (L' : Real) * ‖h‖) :=
      continuous_const.mul continuous_norm
    have hsmall_eventually :
        ∀ᶠ h : ModelPhase (E := E) in 𝓝 0, (L' : Real) * ‖h‖ < ρ := by
      have hball :=
        (hmul_cont.continuousAt (x := (0 : ModelPhase (E := E)))).eventually
          (Metric.ball_mem_nhds
            ((L' : Real) * ‖(0 : ModelPhase (E := E))‖) hρ)
      filter_upwards [hball] with h hh
      have habs : |(L' : Real) * ‖h‖| < ρ := by
        simpa [Real.dist_eq] using hh
      exact (abs_lt.1 habs).2
    filter_upwards [hzh_eventually, hsmall_eventually] with h hzh0 hsmall
    let pzh : ModelPhase (E := E) × ModelLin (E := E) :=
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E)))
    have hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ η :=
      hDρ h hsmall hzh0
    have hgr :=
      varError_norm_le_gronwall_of_segment_bounds_flow (I := I) g x Ψ z h
        (a := a) (r := r) (L' := L') hb
        (hflow pzh hzh0).2 (hflow pz hz0).2
        (hflow pzh hzh0).1 (hflow pz hz0).1
        hbound hsrc
        (fun t ht => hBcc t ⟨ht.1, le_of_lt ht.2⟩)
        hD
        (fun t ht => hLip t (hb ⟨ht.1, le_of_lt ht.2⟩))
        hz0 hzh0
    simpa using hgr b ⟨hb0, le_rfl⟩
  exact varBaseFlow_hasFDerivAt_of_error (E := E) herr


end Coordinates
end RicciFlower
