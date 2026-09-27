import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowSurvivalStep
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSurvival
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorInitialCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowFlowRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowRestriction
import DifferentialGeometry.Geometry.Metric.Pullback.LocalRestriction

set_option autoImplicit false
noncomputable section
open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u uE uH uM
private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

private theorem exists_event_prefix_terminal_anchor
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (next : Fin H.eventCount) (hfirst : first ≤ next.castSucc) (hlast : next.succ ≤ last)
    {τ : ℝ} (hτ : τ ∈ Ioo (H.time next.castSucc) (H.time next.succ))
    (x : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle x) :
    ∃ (G : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
      (L : G.TerminalLimitMetric) (z : G.terminalRegularOpen)
      (B : BackwardPointTrace H first next.castSucc hfirst z.val),
      (∀ t, G.flow.base.metric t = (H.event next).incoming.flow.base.metric t) ∧
      G.flow.base.metric (H.time next.castSucc) = H.initialMetric next.castSucc ∧
      G.terminalRegularRegion = univ ∧
      L.metric = ((H.event next).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen ∧
      z.val = A.point next.castSucc hfirst (next.castSucc_lt_succ.le.trans hlast) ∧
      ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hj : j ≤ next.castSucc),
        B.point j hf hj = A.point j hf (hj.trans (next.castSucc_lt_succ.le.trans hlast)) := by
  let P := H.stage next.castSucc
  let S := (H.event next).incoming.closedPrefix τ hτ.1 hτ.2
  let G := S.restrictIncoming le_rfl S.lt le_rfl
  let L := S.endpointTerminalLimitMetric P
  have hreg : G.terminalRegularRegion = univ := S.terminalRegularRegion_eq_univ P
  let z : G.terminalRegularOpen :=
    ⟨A.point next.castSucc hfirst (next.castSucc_lt_succ.le.trans hlast), by
      change _ ∈ G.terminalRegularRegion
      rw [hreg]
      trivial⟩
  let B := A.restrictLast hfirst (next.castSucc_lt_succ.le.trans hlast)
  exact ⟨G, L, z, B, fun _ => rfl, H.event_initial next, hreg, rfl, rfl, fun _ _ _ => rfl⟩

private theorem exists_incoming_prefix_terminal_anchor
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s τ : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (hτ : τ ∈ Ioo (H.time last) s)
    (x : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle x) :
    ∃ (G₀ : (H.stage last).IncomingSlab (H.time last) τ)
      (L₀ : G₀.TerminalLimitMetric) (z : G₀.terminalRegularOpen)
      (B : BackwardPointTrace H first last hle z.val),
      (∀ t, G₀.flow.base.metric t = G.flow.base.metric t) ∧
      G₀.flow.base.metric (H.time last) = H.initialMetric last ∧
      G₀.terminalRegularRegion = univ ∧
      L₀.metric = (G.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen ∧
      z.val = x ∧ ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last),
        B.point j hf hl = A.point j hf hl := by
  let P := H.stage last
  let S := G.closedPrefix τ hτ.1 hτ.2
  let G₀ := S.restrictIncoming le_rfl S.lt le_rfl
  let L₀ := S.endpointTerminalLimitMetric P
  have hreg : G₀.terminalRegularRegion = univ := S.terminalRegularRegion_eq_univ P
  let z : G₀.terminalRegularOpen := ⟨x, by
    change x ∈ G₀.terminalRegularRegion
    rw [hreg]
    trivial⟩
  exact ⟨G₀, L₀, z, A, fun _ => rfl, hinit, hreg, rfl, rfl, fun _ _ _ => rfl⟩



private def incomingWindowControl
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (D q : ℝ) (hq : 0 < q) (g₀ : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (J : standardCapWindow D → (H.stage first).Carrier)
    (z : standardCapWindow D) (x : G.terminalRegularOpen) (P C₀ ε η : ℝ) (N : ℕ) : Prop :=
  ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
    IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
    (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
    H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
    ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
      (gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G))
      (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 (q * (s - H.time first))
          (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
      IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
      (∀ t, S.base.metric t =
        localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
      (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
          (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) y z.2 j k)
          (Icc 0 (q * (s - H.time first)) ×ˢ
            (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
      (∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ y : standardCapWindow D,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ P ^ 2 ∧ |S.scalar t y| ≤ C₀) ∧
      ∃ Q : StandardSolution, ENNReal.ofReal (q * (s - H.time first)) < Q.val.lifetime ∧
        ∀ t ∈ Icc 0 (q * (s - H.time first)),
          (∀ j ≤ N, ∀ y : standardCapWindow D,
            metricDerivNorm j (S.base.metric t)
              ((Q.val.metric t).restrictOpen (standardCapWindow D))
              (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
          ∀ j ≤ 2, ∀ y : standardCapWindow D,
            metricDerivNorm j (S.base.metric t)
              ((Q.val.metric t).restrictOpen (standardCapWindow D))
              (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η


private theorem exists_uniform_incoming_window_curvature_bound
    (C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀) :
    ∃ η ε₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ D : ℝ, 65 ≤ D → ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      4 ≤ m → ζ ≤ ε₀ →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (J : standardCapWindow D → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x z)) →
      (∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), A.point first le_rfl hle = J z →
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel
            (H.backwardSurvivorIncomingDomain first last hle G))
          (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (q * (s - H.time first))
              (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
          (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                (H.backwardSurvivorIncomingDomain first last hle G)) ∧
          (∀ t ∈ Icc (H.time last) s,
            gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
          IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric ∧
          (∀ t, S.base.metric t =
            localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
          (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) y z.2 j k)
              (Icc 0 (q * (s - H.time first)) ×ˢ
                (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          ∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ y : standardCapWindow D,
            normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤
              (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2 := by
  obtain ⟨η₁, ε₀, hη₁, hε₀, hεhalf, hsurvive⟩ :=
    exists_uniform_incoming_cap_window_survival_time_of_radius_lower_bound C₀ C hC₀
  let η := min η₁ (2 * C * C₀ + 1)⁻¹
  refine ⟨η, ε₀, lt_min hη₁ (by positivity), hε₀, hεhalf, ?_⟩
  intro D hD
  obtain ⟨δ₀, hδ₀, hsurvive⟩ := hsurvive D hD
  refine ⟨δ₀, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal htime z x Atrace hanchor
  obtain ⟨Ξ, hΞs, hbirth⟩ := hsurvive w hm hζ hupper H first last hle s G hinit J hJ
    q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records hfixed hlower hδ hderiv hfinal
    (htime.trans (min_le_left _ _)) z x.val Atrace hanchor
  have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun y =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΞs.isImmersion.isImmersionAt y)
  have htime2 : 2 * C * C₀ * (q * (s - H.time first)) ≤ 1 := by
    have hh := htime.trans (min_le_right _ _)
    have hden : 0 < 2 * (C : ℝ) * C₀ + 1 := by positivity
    have hm := (le_div_iff₀ hden).mp (show q * (s - H.time first) ≤
      1 / (2 * (C : ℝ) * C₀ + 1) from by simpa only [one_div] using hh)
    have ht0 := (H.time_strictMono.monotone hle).trans G.lt.le
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr ht0)]
  obtain ⟨gflow, hslabs, hlast, S, hS, hSzero, hmetric, hgram, hRm⟩ :=
    exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound G L hinit Ξ hΞ J hbirth
      hq₀ hq hq₀Q w.windowMetric hzero haq
      (fun y j hf hl => hderiv j hf hl _) (fun y => hfinal _) hscalar records hfixed hlower htime2
  refine ⟨Ξ, hΞs, hbirth, ?_, hΞ, gflow, S, hslabs, hlast, hS, hSzero, hmetric, hgram, hRm⟩
  exact H.backwardSurvivorIncomingMap_eq_of_initial_point_eq first last hle G J Ξ hbirth
    x Atrace z hanchor.symm

private theorem scalar_le_of_normalized_terminal_scalar_bound
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (Xi : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hXi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Xi)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : gflow s = H.backwardSurvivorIncomingMetric first last hle G L s)
    (g : SmoothRiemannianMetric ThreeModel (H.stage last).Carrier)
    (hL : L.metric = g.restrictOpen G.terminalRegularOpen)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (q : ℝ) (hq : 0 < q)
    (hmetric : ∀ t, S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Xi hXi)
    (C₀ : ℝ) (x : X) (hscalar : |S.scalar (q * (s - H.time first)) x| ≤ C₀) :
    metricScalarAt g (Xi x).val.val ≤ C₀ * q := by
  have hclock : H.time first + q * (s - H.time first) / q = s := by
    rw [mul_div_cancel_left₀ _ hq.ne']
    ring
  have hh := (le_abs_self (S.scalar (q * (s - H.time first)) x)).trans hscalar
  change metricScalarAt (S.base.metric (q * (s - H.time first))) x ≤ C₀ at hh
  rw [hmetric, hclock, metricScalarAt_localPull, metricScalarAt_scaleMetric, hlast,
    H.backwardSurvivorIncomingMetric_terminal first last hle G L,
    metricScalarAt_localPull, hL, CheegerGromovCompactness.metricScalarAt_restrictOpen] at hh
  change q⁻¹ * metricScalarAt g (Xi x).val.val ≤ C₀ at hh
  rwa [← div_eq_inv_mul, div_le_iff₀ hq] at hh


private theorem exists_incoming_window_control_step_of_earlier_prefix
    (Θ P Creset Cstate : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1)
    (hCstate : 0 < Cstate) (hCreset : Creset ≤ Cstate) :
    ∃ ηtip δstep : ℝ, 0 < ηtip ∧ 0 < δstep ∧ ∀ R : ℝ, 32 < R →
      ∃ δsurg : ℝ, 0 < δsurg ∧
      ∀ {E H₀ M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H₀ M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA R m ζ),
      4 ≤ m → ζ ≤ 1/2 →
      (∀ x : standardCapWindow R, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3/2 : ℝ)*StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (next : Fin H.eventCount) (hnext : first ≤ next.castSucc) (hnextlast : next.succ ≤ last)
        (J : standardCapWindow R → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
      ∀ (τ : ℝ) (G₀ : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
        (L₀ : G₀.TerminalLimitMetric),
      (∀ t, G₀.flow.base.metric t = (H.event next).incoming.flow.base.metric t) →
      L₀.metric = ((H.event next).incoming.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen →
      τ ∈ Ico (H.time next.castSucc) (H.time next.succ) →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), q₀ ≤ Cstate*q → 1 ≤ a₀*q →
      (∀ x (v a : TangentSpace ThreeModel x), w.windowMetric.inner x v a =
        q * (H.initialMetric first).inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x a)) →
      ∀ (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      (∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q*(s-H.time first) ≤ Θ → q*(s-τ) ≤ δstep →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3/a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
        ∀ b, (records j).delta b ≤ δsurg) →
      ∀ (D ε η : ℝ) (hD : 0 < D) (hDR : D ≤ R) (N : ℕ),
      let inc : standardCapWindow D → standardCapWindow R :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)));
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (Atr : BackwardPointTrace H first last hle x.val),
      Atr.point first le_rfl hle = J (inc z) →
      ∀ x₀ : G₀.terminalRegularOpen,
      incomingWindowControl H first next.castSucc hnext τ G₀ L₀ R q hq w.windowMetric J
        (inc z) x₀ P Cstate 1 ηtip 2 →
      (∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow R)
          (RealTimeInterval.closed 0 (q*(s-H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
        (∀ (y : standardCapWindow R) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun a : ℝ × standardCapWindow R => chartGramMatrix (S.base.metric a.1) y a.2 i j)
            (Icc 0 (q*(s-H.time first)) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
        (∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ y : standardCapWindow R,
          nablaKRm04NormSqIntrinsic S 0 t y ≤
            max (P^2) ((2*Real.sqrt 3*(Cstate+max (2*Cstate) (Real.exp 4)))^2)) →
        ∃ F : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (q*(s-H.time first))
              (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
          IsSolutionOn F ∧
          (∀ t, F.base.metric t = (S.base.metric t).restrictOpenOfSubset
            (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)) :
              standardCapWindow D ≤ standardCapWindow R)) ∧
          F.base.metric 0 = (w.restrictWindow hD hDR).windowMetric ∧
          (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun a : ℝ × standardCapWindow D => chartGramMatrix (F.base.metric a.1) y a.2 i j)
              (Icc 0 (q*(s-H.time first)) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ y : standardCapWindow D,
            nablaKRm04NormSqIntrinsic F 0 t y ≤ P^2 ∧ |F.scalar t y| ≤ Creset) ∧
          ∃ Q : StandardSolution, ENNReal.ofReal (q*(s-H.time first)) < Q.val.lifetime ∧
            ∀ t ∈ Icc 0 (q*(s-H.time first)),
              (∀ j ≤ N, ∀ y : standardCapWindow D, metricDerivNorm j (F.base.metric t)
                ((Q.val.metric t).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
              ∀ j ≤ 2, ∀ y : standardCapWindow D, metricDerivNorm j (F.base.metric t)
                ((Q.val.metric t).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η) →
      incomingWindowControl H first last hle s G L D q hq
        (w.restrictWindow hD hDR).windowMetric (J ∘ inc) z x P Cstate ε η N := by
  obtain ⟨ηtip,δstep,hηtip,hδstep,hstep⟩ :=
    exists_uniform_incoming_cap_window_step_of_standard_tip_metric_close Θ (P^2) Cstate C hΘ.le hΘ1 hCstate
  refine ⟨ηtip,δstep,hηtip,hδstep,?_⟩
  intro R hR
  obtain ⟨δsurg,hδsurg,hstep⟩ := hstep R hR
  refine ⟨δsurg,hδsurg,?_⟩
  intro E H₀ M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle next hnext hnextlast J hJ τ G₀ L₀ hsource hterminal hτ q q₀ a₀ hq hq₀ haq hzero
    s G L hinit hderiv hfinal hfull hremain parameters records hfixed hlower hdelta
    D ε η hD hDR N inc z x Atr hanchor x₀ hprior hreset
  obtain ⟨Ψ,hΨs,hbirth₀,hmarked₀,hΨ,gflow₀,S₀,hslabs₀,hlast₀,hS₀,hzero₀,hmetric₀,hgram₀,hcurv₀,Q,hQ,hclose₀⟩ := hprior
  have hτage : 0 < q*(τ-H.time first) :=
    mul_pos hq (sub_pos.mpr ((H.time_strictMono.monotone hnext).trans_lt G₀.lt))
  have hτs : τ < s := hτ.2.trans_le (H.time_strictMono.monotone hnextlast) |>.trans G.lt
  have hτΘ : q*(τ-H.time first) ∈ Icc 0 Θ :=
    ⟨hτage.le,(mul_le_mul_of_nonneg_left (sub_le_sub_right hτs.le _) hq.le).trans hfull⟩
  have hscalar (y : standardCapWindow R) : (H.event next).incoming.flow.scalar τ (Ψ y).val.val ≤ Cstate*q :=
    scalar_le_of_normalized_terminal_scalar_bound H first next.castSucc hnext τ G₀ L₀
      Ψ hΨ gflow₀ (hlast₀ τ ⟨G₀.lt.le,le_rfl⟩) ((H.event next).incoming.flow.base.metric τ)
      hterminal S₀ q hq hmetric₀ Cstate y (hcurv₀ _ ⟨hτage.le,le_rfl⟩ y).2
  let tip : standardCapWindow R := ⟨0, by change ‖(0 : ThreeSpace)‖ < R+1; norm_num; linarith⟩
  have htipclose : ∀ j ≤ 2, metricDerivNorm j (S₀.base.metric (q*(τ-H.time first)))
      ((Q.val.metric (q*(τ-H.time first))).restrictOpen (standardCapWindow R))
      (StandardCap.metric.restrictOpen (standardCapWindow R)) tip ≤ ηtip :=
    fun j hj => ((hclose₀ _ ⟨hτage.le,le_rfl⟩).2 j hj tip).le
  obtain ⟨Ξ,hΞs,hbirth,hmarked,hΞ,gflow,hslabs,hlast,S,hS,hSzero,hmetric,hgram,hpast,hRm⟩ :=
    hstep w hm hζ hupper H first last hle next hnext hnextlast J hJ G₀ L₀ hsource hterminal hτ
      Ψ hΨ hbirth₀ gflow₀ hslabs₀ hlast₀ hq hq₀ haq hzero S₀ (fun t _ => hmetric₀ t)
      (fun t ht y => (hcurv₀ t ht y).1) hscalar hderiv G L hinit hfinal hfull hremain
      Q (q*(τ-H.time first)) hτΘ tip rfl htipclose parameters records hfixed hlower hdelta
      (inc z) x Atr hanchor
  obtain ⟨F,hF,hFmetric,hFzero,hFgram,hFcurv,Q',hQ',hFclose⟩ := hreset S hS hSzero hgram
    (by intro t ht y; simpa only [nablaKRm04NormSqIntrinsic,nablaKRm04Field_zero,Nat.add_zero] using hRm t ht y)
  have hi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict
      (fun v : standardCapWindow D => (show standardCapWindow D ≤ standardCapWindow R from
        fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1))) v.property)
      (isLocalDiffeomorph_subtype_val (standardCapWindow D) y)
  let ΞD := Ξ ∘ inc
  have hΞD : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ΞD := isLocalDiffeomorph_comp hΞ hi
  have hΞDs : IsSmoothEmbedding ThreeModel ThreeModel ∞ ΞD :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      hΞD (hΞs.isEmbedding.injective.comp (by
        intro a b hab
        exact Subtype.ext (congrArg (fun v : standardCapWindow R => v.val) hab)))
  refine ⟨ΞD,hΞDs,(fun y => hbirth (inc y)),hmarked,hΞD,gflow,F,hslabs,hlast,hF,hFzero,?_,hFgram,?_,Q',hQ',hFclose⟩
  · intro t
    rw [hFmetric,hmetric]
    exact localPullMetric_restrictOpenOfSubset_eq _ _ Ξ hΞ ΞD hΞD rfl
  · intro t ht y
    have hh := hFcurv t ht y
    refine ⟨?_,hh.2.trans hCreset⟩
    simpa only [nablaKRm04NormSqIntrinsic,nablaKRm04Field_zero,Nat.add_zero] using hh.1

private theorem incoming_raw_control_of_same_final_prefix
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {τ s R q r a₀ P Creset A ε η : ℝ} {N : ℕ} {C : ℝ≥0}
    (hq : 0 < q) (hA : 0 < A) (hCA : Creset ≤ A) (hrA : r ≤ A * q) (haq : 1 ≤ a₀ * q)
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (G₀ : (H.stage last).IncomingSlab (H.time last) τ) (L₀ : G₀.TerminalLimitMetric)
    (hsource₀ : ∀ t, G₀.flow.base.metric t = G.flow.base.metric t)
    (hterminal₀ : L₀.metric = (G.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (hτs : τ < s)
    (g₀ : SmoothRiemannianMetric ThreeModel (standardCapWindow R))
    (J : standardCapWindow R → (H.stage first).Carrier)
    (hzero : ∀ y (v w : TangentSpace ThreeModel y), g₀.inner y v w =
      q * (H.initialMetric first).inner (J y)
        (mfderiv ThreeModel ThreeModel J y v) (mfderiv ThreeModel ThreeModel J y w))
    (z₀ : standardCapWindow R) (x₀ : G₀.terminalRegularOpen)
    (hprior : incomingWindowControl H first last hle τ G₀ L₀ R q hq g₀ J z₀ x₀ P Creset ε η N)
    (hfinal : ∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo τ s, r < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (htime : 2*C*A*(q*(s-τ)) ≤ 1)
    (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3/a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (z : standardCapWindow R) (x : G.terminalRegularOpen)
    (Atrace : BackwardPointTrace H first last hle x.val)
    (hanchor : Atrace.point first le_rfl hle = J z) :
    ∃ Ξ : standardCapWindow R → H.backwardSurvivorIncomingDomain first last hle G,
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
      (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
      H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
      ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingDomain first last hle G))
        (S : SolutionOn (I := ThreeModel) (M := standardCapWindow R)
          (RealTimeInterval.closed 0 (q * (s - H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)) ∧
        (∀ t ∈ Icc (H.time last) s,
          gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
        IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
        (∀ t, S.base.metric t =
          localPullMetric (scaleMetric q hq (gflow (H.time first+t/q))) Ξ hΞ) ∧
        (∀ (y : standardCapWindow R) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun v : ℝ × standardCapWindow R => chartGramMatrix (S.base.metric v.1) y v.2 i j)
            (Icc 0 (q*(s-H.time first)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
        ∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ y : standardCapWindow R,
          normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤
            max (P^2) ((2*Real.sqrt 3*(A+max (2*A) (Real.exp 4)))^2) := by
  obtain ⟨Ξ₀,hΞ₀s,hbirth₀,hmarked₀,hΞ₀,gflow₀,S₀,hslabs₀,hlast₀,hS₀,hS₀zero,
    hmetric₀,hgram₀,hcurv₀,Q₀,hQ₀,hclose₀⟩ := hprior
  let Υ := Subtype.val ∘ Ξ₀
  have hΥ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Υ :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ₀
  have hΥs : IsSmoothEmbedding ThreeModel ThreeModel ∞ Υ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      hΥ (Subtype.val_injective.comp hΞ₀s.isEmbedding.injective)
  have hτ : τ ∈ Ico (H.time last) s := ⟨G₀.lt.le,hτs⟩
  have huτ : q*(τ-H.time first) ∈ Icc 0 (q*(τ-H.time first)) :=
    ⟨mul_nonneg hq.le (sub_nonneg.mpr ((H.time_strictMono.monotone hle).trans G₀.lt.le)),le_rfl⟩
  have hscalar (y : standardCapWindow R) : G.flow.scalar τ (Υ y).val ≤ A * q := by
    have hs := (hcurv₀ _ huτ y).2
    change |metricScalarAt (S₀.base.metric _) y| ≤ Creset at hs
    rw [hmetric₀, show H.time first + q*(τ-H.time first)/q = τ by field_simp; ring,
      hlast₀ τ ⟨G₀.lt.le,le_rfl⟩, metricScalarAt_localPull, metricScalarAt_scaleMetric,
      backwardSurvivorIncomingMetric, metricScalarAt_localPull,
      OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal,
      hterminal₀, metricScalarAt_restrictOpen] at hs
    change |q⁻¹ * G.flow.scalar τ (Υ y).val| ≤ Creset at hs
    have hlo := (le_abs_self _).trans (hs.trans hCA)
    rw [← div_eq_inv_mul, div_le_iff₀ hq] at hlo
    exact hlo
  obtain ⟨Ξ,hΞ,hΞs,hmark,hprojection,hbirth,gflow,hslabs,hlast,S,hS,hSzero,
    hmetric,hgram,hoverlap,hRm⟩ :=
    exists_normalized_backwardSurvivorIncoming_embedding_solution_curvature_bound_of_final_scalar_bound_at_time
      G L hinit Υ hΥs hA hq hrA haq hτ (fun y => hfinal (Υ y).val) hscalar htime
      J hbirth₀ g₀ hzero records hfixed hlower G₀ L₀ hsource₀ hterminal₀ Ξ₀ hΞ₀ (fun _ => rfl)
      gflow₀ hslabs₀ hlast₀ S₀ (fun t _ => hmetric₀ t) (fun t ht y => (hcurv₀ t ht y).1)
  exact ⟨Ξ,hΞs,hbirth,hmark x Atrace z hanchor.symm,hΞ,gflow,S,
    hslabs,hlast,hS,hSzero,hmetric,hgram,hRm⟩


private theorem incoming_window_control_of_restricted_flow
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    {D R q P C₀ ε η : ℝ} {N : ℕ} (hDR : D ≤ R) (hq : 0 < q)
    (g₀ : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (J : standardCapWindow R → (H.stage first).Carrier)
    (z : standardCapWindow D) (x : G.terminalRegularOpen)
    (Ξ : standardCapWindow R → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞs : IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (hbirth : ∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y)
    (hmarked : H.backwardSurvivorIncomingMap first last hle G
      (Ξ (TopologicalSpace.Opens.inclusion
        (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)) :
          standardCapWindow D ≤ standardCapWindow R) z)) = x)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (S : SolutionOn (I := ThreeModel) (M := standardCapWindow R)
      (RealTimeInterval.closed 0 (q * (s - H.time first))
        (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)))
    (hSmetric : ∀ t, S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ)
    (F : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
      (RealTimeInterval.closed 0 (q * (s - H.time first))
        (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)))
    (hF : IsSolutionOn F)
    (hFmetric : ∀ t, F.base.metric t = (S.base.metric t).restrictOpenOfSubset
      (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)) :
        standardCapWindow D ≤ standardCapWindow R))
    (hFzero : F.base.metric 0 = g₀)
    (hFgram : ∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
        (fun z : ℝ × standardCapWindow D => chartGramMatrix (F.base.metric z.1) y z.2 i j)
        (Icc 0 (q * (s - H.time first)) ×ˢ
          (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet))
    (hFcurv : ∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ y : standardCapWindow D,
      nablaKRm04NormSqIntrinsic F 0 t y ≤ P ^ 2 ∧ |F.scalar t y| ≤ C₀)
    (Q : StandardSolution) (hQ : ENNReal.ofReal (q * (s - H.time first)) < Q.val.lifetime)
    (hFclose : ∀ t ∈ Icc 0 (q * (s - H.time first)),
      (∀ j ≤ N, ∀ y : standardCapWindow D,
        metricDerivNorm j (F.base.metric t)
          ((Q.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
      ∀ j ≤ 2, ∀ y : standardCapWindow D,
        metricDerivNorm j (F.base.metric t)
          ((Q.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η) :
    incomingWindowControl H first last hle s G L D q hq g₀
      (J ∘ TopologicalSpace.Opens.inclusion
        (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)) :
          standardCapWindow D ≤ standardCapWindow R)) z x P C₀ ε η N := by
  let incD : standardCapWindow D → standardCapWindow R :=
    TopologicalSpace.Opens.inclusion
      (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)))
  have hiD : IsLocalDiffeomorph ThreeModel ThreeModel ∞ incD := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun v : standardCapWindow D =>
      (show standardCapWindow D ≤ standardCapWindow R from
        fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1))) v.property)
      (isLocalDiffeomorph_subtype_val (standardCapWindow D) y)
  let ΞD := Ξ ∘ incD
  have hΞD : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ΞD :=
    isLocalDiffeomorph_comp hΞ hiD
  have hΞDs : IsSmoothEmbedding ThreeModel ThreeModel ∞ ΞD :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      hΞD (hΞs.isEmbedding.injective.comp (by
        intro a b hab
        exact Subtype.ext (congrArg (fun v : standardCapWindow R => v.val) hab)))
  refine ⟨ΞD, hΞDs, (fun y => hbirth (incD y)), hmarked, hΞD, gflow, F,
    hslabs, hlast, hF, hFzero, ?_, hFgram, ?_, Q, hQ, hFclose⟩
  · intro t
    rw [hFmetric, hSmetric]
    exact localPullMetric_restrictOpenOfSubset_eq _ _ Ξ hΞ ΞD hΞD rfl
  · intro t ht y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hFcurv t ht y


private theorem incoming_window_control_step_of_final_prefix
    {E H₀ M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H₀ M] [IsManifold I ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ R : ℝ}
    (w : StandardCap.CanonicalStaticInsertionWitness d A hA R m ζ)
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {τ s D q r a₀ P Creset Cstate ε η ε₀ η₀ : ℝ} {N N₀ : ℕ} {C : ℝ≥0}
    (hD : 0 < D) (hDR : D ≤ R) (hq : 0 < q) (hCstate : 0 < Cstate)
    (hCresetState : Creset ≤ Cstate) (hrA : r ≤ Cstate * q) (haq : 1 ≤ a₀ * q)
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (G₀ : (H.stage last).IncomingSlab (H.time last) τ) (L₀ : G₀.TerminalLimitMetric)
    (hsource₀ : ∀ t, G₀.flow.base.metric t = G.flow.base.metric t)
    (hterminal₀ : L₀.metric = (G.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (hτs : τ < s)
    (J : standardCapWindow R → (H.stage first).Carrier)
    (hzero : ∀ y (v a : TangentSpace ThreeModel y), w.windowMetric.inner y v a =
      q * (H.initialMetric first).inner (J y)
        (mfderiv ThreeModel ThreeModel J y v) (mfderiv ThreeModel ThreeModel J y a))
    (hfinal : ∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo τ s, r < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (htime : 2*C*Cstate*(q*(s-τ)) ≤ 1)
    (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3/a₀ ≤ metricScalarAt (H.initialMetric 0) x) :
    let inc : standardCapWindow D → standardCapWindow R :=
      TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)));
    ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
      (Atrace : BackwardPointTrace H first last hle x.val),
      Atrace.point first le_rfl hle = J (inc z) →
    ∀ x₀ : G₀.terminalRegularOpen,
      incomingWindowControl H first last hle τ G₀ L₀ R q hq w.windowMetric J
        (inc z) x₀ P Cstate ε₀ η₀ N₀ →
      (∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow R)
          (RealTimeInterval.closed 0 (q*(s-H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
        (∀ (y : standardCapWindow R) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun a : ℝ × standardCapWindow R => chartGramMatrix (S.base.metric a.1) y a.2 i j)
            (Icc 0 (q*(s-H.time first)) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
        (∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ y : standardCapWindow R,
          nablaKRm04NormSqIntrinsic S 0 t y ≤
            max (P^2) ((2*Real.sqrt 3*(Cstate+max (2*Cstate) (Real.exp 4)))^2)) →
        ∃ F : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (q*(s-H.time first))
              (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
          IsSolutionOn F ∧
          (∀ t, F.base.metric t = (S.base.metric t).restrictOpenOfSubset
            (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)) :
              standardCapWindow D ≤ standardCapWindow R)) ∧
          F.base.metric 0 = (w.restrictWindow hD hDR).windowMetric ∧
          (∀ (y : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun a : ℝ × standardCapWindow D => chartGramMatrix (F.base.metric a.1) y a.2 i j)
              (Icc 0 (q*(s-H.time first)) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ t ∈ Icc 0 (q*(s-H.time first)), ∀ y : standardCapWindow D,
            nablaKRm04NormSqIntrinsic F 0 t y ≤ P^2 ∧ |F.scalar t y| ≤ Creset) ∧
          ∃ Q : StandardSolution, ENNReal.ofReal (q*(s-H.time first)) < Q.val.lifetime ∧
            ∀ t ∈ Icc 0 (q*(s-H.time first)),
              (∀ j ≤ N, ∀ y : standardCapWindow D, metricDerivNorm j (F.base.metric t)
                ((Q.val.metric t).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
              ∀ j ≤ 2, ∀ y : standardCapWindow D, metricDerivNorm j (F.base.metric t)
                ((Q.val.metric t).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η) →
      incomingWindowControl H first last hle s G L D q hq
        (w.restrictWindow hD hDR).windowMetric (J ∘ inc) z x P Cstate ε η N := by
  intro inc z x Atrace hanchor x₀ hprior hreset
  obtain ⟨Ξ,hΞs,hbirth,hmarked,hΞ,gflow,S,hslabs,hlast,hS,hSzero,hmetric,hgram,hRm⟩ :=
    incoming_raw_control_of_same_final_prefix H first last hle hq hCstate le_rfl hrA haq
      G L hinit G₀ L₀ hsource₀ hterminal₀ hτs w.windowMetric J hzero (inc z) x₀ hprior
      hfinal htime parameters records hfixed hlower (inc z) x Atrace hanchor
  obtain ⟨F,hF,hFmetric,hFzero,hFgram,hFcurv,Q,hQ,hFclose⟩ := hreset S hS hSzero hgram
    (by intro t ht y; simpa only [nablaKRm04NormSqIntrinsic,nablaKRm04Field_zero,Nat.add_zero] using hRm t ht y)
  apply incoming_window_control_of_restricted_flow H first last hle s G L hDR hq
    (w.restrictWindow hD hDR).windowMetric J z x Ξ hΞs hΞ hbirth hmarked gflow hslabs hlast
    S hmetric F hF hFmetric hFzero hFgram _ Q hQ hFclose
  intro t ht y
  exact ⟨(hFcurv t ht y).1, (hFcurv t ht y).2.trans hCresetState⟩

private def preparedIncomingControl
    (Θ T : ℝ) (C : ℝ≥0) (P Creset Cbirth : ℝ) : Prop :=
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
      ∃ R : ℝ, ∃ hDR : D + 1 < R, ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hR : R ≤ Dbig), m₀ ≤ m → ζ ≤ ζ₀ →
      let hDD : D ≤ Dbig := by linarith;
      let inc : standardCapWindow D → standardCapWindow Dbig :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)));
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ min Θ T →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (Atrace : BackwardPointTrace H first last hle x.val),
        Atrace.point first le_rfl hle = Jbig (inc z) →
      incomingWindowControl H first last hle s G L D q hq
        (w.restrictWindow hD hDD).windowMetric (Jbig ∘ inc) z x P Creset ε η N

private theorem prepared_incoming_control_mono
    {Θ T U P Creset Cbirth : ℝ} {C : ℝ≥0} (hTU : T ≤ U)
    (h : preparedIncomingControl.{u, uE, uH, uM} Θ U C P Creset Cbirth) :
    preparedIncomingControl.{u, uE, uH, uM} Θ T C P Creset Cbirth := by
  intro E H₀ _ _ _ _ _ I _ D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, h⟩ := h (I := I) D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
  exact h w hR hm hζ H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal
    (htime.trans (min_le_min_left _ hTU)) z x Atrace hanchor

private theorem exists_prepared_incoming_window_control
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
      preparedIncomingControl.{u, uE, uH, uM} Θ Θ C P Creset Cbirth := by
  obtain ⟨P, Creset, hP, hCreset, hreset⟩ :=
    StandardCap.exists_uniform_standard_cap_restriction_of_curvature_bound Θ hΘ hΘ1
  obtain ⟨Cbirth, hCbirth, hscalarBirth⟩ :=
    StandardCap.exists_uniform_window_image_scalar_bound_of_scaled_pullback
  obtain ⟨ηbase, εbase, hηbase, hεbase, hεbaseHalf, hbase⟩ :=
    exists_uniform_incoming_window_curvature_bound Cbirth C hCbirth
  let Cstep := max Cbirth Creset
  have hCstep : 0 < Cstep := hCbirth.trans_le (le_max_left _ _)
  have hbasePrepared : preparedIncomingControl.{u, uE, uH, uM} Θ ηbase C P Cstep Cbirth := by
    intro E H₀ _ _ _ _ _ I _ D ε η hD hε hη N
    let Kbirth := (2 * Real.sqrt 3 * (Cbirth + max (2 * Cbirth) (Real.exp 4))) ^ 2
    obtain ⟨Rcompare, hRcompare, m₀, hm₀, ζreset, hζreset, hζresetHalf, hreset⟩ :=
      hreset (I := I) Kbirth D ε η hD hε hη N
    let Rflow := max 65 Rcompare
    have hRflow : 0 < Rflow := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    obtain ⟨δ₀, hδ₀, hbase⟩ := hbase Rflow (le_max_left _ _)
    refine ⟨Rflow + 1, by dsimp only [Rflow]; linarith only [hRcompare, le_max_right (65 : ℝ) Rcompare],
      m₀, hm₀, min εbase ζreset, δ₀, lt_min hεbase hζreset,
      (min_le_left _ _).trans hεbaseHalf, hδ₀, ?_⟩
    intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
      H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
      parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
    have hRDbig : Rflow ≤ Dbig := by linarith only [hR]
    let hsub : standardCapWindow Rflow ≤ standardCapWindow Dbig :=
      fun _ hx => hx.trans_le (add_le_add hRDbig (le_refl 1))
    let incR : standardCapWindow Rflow → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion hsub
    have hiR : IsLocalDiffeomorph ThreeModel ThreeModel ∞ incR := fun y =>
      isLocalDiffeomorphAt_subtypeCodRestrict (fun v : standardCapWindow Rflow => hsub v.property)
        (isLocalDiffeomorph_subtype_val (standardCapWindow Rflow) y)
    have hiRs : IsSmoothEmbedding ThreeModel ThreeModel ∞ incR :=
      DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
        hiR (by intro a b hab; exact Subtype.ext (congrArg (fun v : standardCapWindow Dbig => v.val) hab))
    let wR := w.restrictWindow hRflow hRDbig
    let JR := Jbig ∘ incR
    have hJR : IsSmoothEmbedding ThreeModel ThreeModel ∞ JR := hJbig.comp hiRs (by simp)
    have hζhalf : ζ ≤ 1 / 2 := (hζ.trans (min_le_left _ _)).trans hεbaseHalf
    have hinner (y : standardCapWindow Rflow) : ‖(incR y).val‖ < Dbig :=
      y.property.trans_le hR
    have hupper : ∀ y : standardCapWindow Rflow, ∀ v : TangentSpace ThreeModel y,
        wR.windowMetric.inner y v v ≤ (3/2 : ℝ)*StandardCap.metric.inner y.val v v := by
      intro y v
      rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
      have hb := (w.window_inner_bounds hζhalf (hinner y) v).2
      rw [standardCapMetric_eq_metric] at hb
      exact hb
    have hzeroR : ∀ y (v a : TangentSpace ThreeModel y), wR.windowMetric.inner y v a =
        q * (H.initialMetric first).inner (JR y) (mfderiv ThreeModel ThreeModel JR y v)
          (mfderiv ThreeModel ThreeModel JR y a) := by
      intro y v a
      rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
      change w.windowMetric.inner (incR y) v a = _
      have hz := hzero (incR y) (show TangentSpace ThreeModel (incR y) from v)
        (show TangentSpace ThreeModel (incR y) from a)
      have hd := mfderiv_comp y (hJbig.contMDiff.mdifferentiableAt (by simp))
        (hiR.contMDiff.mdifferentiableAt (by simp))
      simp only [incR, mfderiv_opens_incl] at hd
      dsimp only [TangentSpace] at hd hz ⊢
      rw [hd]
      exact hz
    have hscalarR : ∀ y : standardCapWindow Rflow,
        metricScalarAt (H.initialMetric first) (JR y) ≤ Cbirth*q := by
      intro y
      exact (le_abs_self _).trans
        (hscalarBirth w hζhalf (by omega) _ Jbig hJbig q hq hzero (incR y) (hinner y))
    have hDR : D ≤ Rflow := by dsimp only [Rflow]; linarith only [hRcompare, le_max_right (65 : ℝ) Rcompare]
    let incD : standardCapWindow D → standardCapWindow Rflow :=
      TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)))
    have hanchorR : Atrace.point first le_rfl hle = JR (incD z) := hanchor
    obtain ⟨Ξ, hΞs, hbirth, hmarked, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
      hSmetric, hSgram, hRm⟩ := hbase wR (hm₀.trans hm) (hζ.trans (min_le_left _ _)) hupper
        H first last hle s G L hinit JR hJR q q₀ a₀ hq hq₀ hq₀Q haq hzeroR hscalarR
        parameters records hfixed hlower hdelta hderiv hfinal (htime.trans (min_le_right _ _))
        (incD z) x Atrace hanchorR
    let T := q * (s - H.time first)
    have hT : 0 < T := mul_pos hq (sub_pos.mpr ((H.time_strictMono.monotone hle).trans_lt G.lt))
    obtain ⟨hDR', F, hF, hFmetric, hFzero, hFgram, hFcurv, Q, hQ, hFclose⟩ :=
      hreset wR (le_max_right _ _) hm (hζ.trans (min_le_right _ _)) T hT
        (htime.trans (min_le_left _ _)) S hS hSzero hSgram
        (by intro t ht y; simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm t ht y)
    have hiD : IsLocalDiffeomorph ThreeModel ThreeModel ∞ incD := fun y =>
      isLocalDiffeomorphAt_subtypeCodRestrict (fun v : standardCapWindow D =>
        (show standardCapWindow D ≤ standardCapWindow Rflow from
          fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1))) v.property)
        (isLocalDiffeomorph_subtype_val (standardCapWindow D) y)
    let ΞD := Ξ ∘ incD
    have hΞD : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ΞD := isLocalDiffeomorph_comp hΞ hiD
    have hΞDs : IsSmoothEmbedding ThreeModel ThreeModel ∞ ΞD :=
      DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
        hΞD (hΞs.isEmbedding.injective.comp (by
          intro a b hab
          exact Subtype.ext (congrArg (fun v : standardCapWindow Rflow => v.val) hab)))
    refine ⟨ΞD, hΞDs, (fun y => hbirth (incD y)), hmarked, hΞD, gflow, F,
      hslabs, hlast, hF, ?_, ?_, hFgram, ?_, Q, hQ, hFclose⟩
    · rw [hFzero]
      apply SmoothRiemannianMetric.ext_inner
      intro y v a
      rfl
    · intro t
      rw [hFmetric, hSmetric]
      exact localPullMetric_restrictOpenOfSubset_eq _ _ Ξ hΞ ΞD hΞD rfl
    · intro t ht y
      have hb := hFcurv t ht y
      refine ⟨?_, hb.2.trans (le_max_right _ _)⟩
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hb.1
  obtain ⟨εtip, δstep, hεtip, hδstep, hstep⟩ :=
    exists_incoming_window_control_step_of_earlier_prefix Θ P Creset Cstep C
      hΘ hΘ1 hCstep (le_max_right _ _)
  let δ := min ηbase (min δstep (2 * ((C : ℝ) + 1) * Cstep)⁻¹)
  have hδ : 0 < δ := lt_min hηbase (lt_min hδstep (by positivity))
  have hcontrol : ∀ n : ℕ,
      preparedIncomingControl.{u, uE, uH, uM} Θ (((n : ℝ) + 1) * δ / 2) C P Cstep Cbirth := by
    intro n
    induction n with
    | zero =>
      have hzero : ((0 : ℕ) + 1 : ℝ) * δ / 2 ≤ ηbase := by
        have hh : δ ≤ ηbase := min_le_left _ _
        norm_num
        linarith only [hh, hδ]
      exact @prepared_incoming_control_mono Θ _ ηbase P Cstep Cbirth C hzero hbasePrepared
    | succ n ih =>
      intro E H₀ _ _ _ _ _ I _ D ε η hD hε hη N
      let Knext := max (P^2) ((2 * Real.sqrt 3 * (Cstep + max (2*Cstep) (Real.exp 4)))^2)
      obtain ⟨Rcompare, hRcompare, mreset, hmreset, ζreset, hζreset, hζresetHalf, hresetD⟩ :=
        hreset (I := I) Knext D ε η hD hε hη N
      let Rflow := max 65 Rcompare
      have hRflow : 0 < Rflow := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hDRflow : D + 1 < Rflow := hRcompare.trans_le (le_max_right _ _)
      obtain ⟨δprotect, hδprotect, hstepR⟩ := hstep Rflow
        (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
      obtain ⟨Rlarge, hRlarge, mlarge, hmlarge, ζlarge, δlarge, hζlarge, hζlargeHalf,
        hδlarge, ihLarge⟩ := ih (I := I) Rflow 1 εtip hRflow (by norm_num) hεtip 2
      obtain ⟨Rsmall, hRsmall, msmall, hmsmall, ζsmall, δsmall, hζsmall, hζsmallHalf,
        hδsmall, ihSmall⟩ := ih (I := I) D ε η hD hε hη N
      refine ⟨max Rlarge Rsmall, hRsmall.trans_le (le_max_right _ _),
        max mlarge (max msmall mreset), hmlarge.trans (le_max_left _ _),
        min ζlarge (min ζsmall ζreset), min δlarge (min δsmall δprotect),
        lt_min hζlarge (lt_min hζsmall hζreset), (min_le_left _ _).trans hζlargeHalf,
        lt_min hδlarge (lt_min hδsmall hδprotect), ?_⟩
      intro M _ _ _ _ g x₀ δinitial k d A hA Dbig m ζ w hR hm hζ hDD inc
        H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
        parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
      have hsmallR : Rsmall ≤ Dbig := (le_max_right _ _).trans hR
      have hsmallm : msmall ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
      have hsmallζ : ζ ≤ ζsmall := hζ.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hsmallcut : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
          ∀ b, (records j).delta b ≤ δsmall := by
        intro j hf hl b
        exact (hdelta j hf hl b).trans ((min_le_right _ _).trans (min_le_left _ _))
      by_cases hearly : q * (s - H.time first) ≤ ((n : ℝ)+1)*δ/2
      · exact ihSmall w hsmallR hsmallm hsmallζ H first last hle s G L hinit Jbig hJbig
          q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower hsmallcut hderiv hfinal
          (le_min (htime.trans (min_le_left _ _)) hearly) z x Atrace hanchor
      · have hlate : ((n : ℝ)+1)*δ/2 < q * (s - H.time first) := lt_of_not_ge hearly
        let a := H.time first + (((n : ℝ)+1)*δ/2 - δ/4)/q
        let b := H.time first + (((n : ℝ)+1)*δ/2)/q
        have hab : a < b := by
          dsimp only [a, b]
          apply add_lt_add_right
          exact (div_lt_div_iff_of_pos_right hq).mpr (by linarith only [hδ])
        obtain ⟨τ, hτ, hne⟩ := H.exists_time_mem_Ioo_ne_event_times hab
        have ha : H.time first < a := by
          dsimp only [a]
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          have hp : 0 < ((n : ℝ)+1)*δ/2-δ/4 := by nlinarith only [mul_nonneg hn hδ.le, hδ]
          exact lt_add_of_pos_right _ (div_pos hp hq)
        have hb : b < s := by
          dsimp only [b]
          have hd := (div_lt_iff₀ hq).mpr (by simpa only [mul_comm] using hlate : ((n : ℝ)+1)*δ/2 < (s-H.time first)*q)
          linarith only [hd]
        have hτs : τ ∈ Ioo (H.time first) s := ⟨ha.trans hτ.1, hτ.2.trans hb⟩
        have hτbound : q*(τ-H.time first) ≤ ((n : ℝ)+1)*δ/2 := by
          have hh : τ-H.time first < (((n : ℝ)+1)*δ/2)/q := by
            have hh := hτ.2
            dsimp only [b] at hh
            linarith only [hh]
          have hm := (lt_div_iff₀ hq).mp hh
          simpa only [mul_comm] using hm.le
        have hτlower : ((n : ℝ)+1)*δ/2 - δ/4 < q*(τ-H.time first) := by
          have hh : (((n : ℝ)+1)*δ/2-δ/4)/q < τ-H.time first := by
            have hh := hτ.1
            dsimp only [a] at hh
            linarith only [hh]
          have hm := (div_lt_iff₀ hq).mp hh
          simpa only [mul_comm] using hm
        have hremaining : q*(s-τ) ≤ δ := by
          have ht := htime.trans (min_le_right _ _)
          push_cast at ht
          nlinarith only [ht, hτlower, hδ]
        have hτΘ : q*(τ-H.time first) ≤ Θ :=
          (mul_le_mul_of_nonneg_left (sub_le_sub_right hτs.2.le _) hq.le).trans
            (htime.trans (min_le_left _ _))
        have hlargeR : Rlarge ≤ Dbig := (le_max_left _ _).trans hR
        have hlargem : mlarge ≤ m := (le_max_left _ _).trans hm
        have hlargeζ : ζ ≤ ζlarge := hζ.trans (min_le_left _ _)
        have hζhalf : ζ ≤ 1/2 := hlargeζ.trans hζlargeHalf
        have hRDbig : Rflow ≤ Dbig := (by linarith only [hRlarge] : Rflow ≤ Rlarge).trans hlargeR
        have hmargin : Rflow+1 ≤ Dbig := hRlarge.le.trans hlargeR
        let hsub : standardCapWindow Rflow ≤ standardCapWindow Dbig :=
          fun _ hx => hx.trans_le (add_le_add hRDbig (le_refl 1))
        let incR : standardCapWindow Rflow → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion hsub
        have hiR : IsLocalDiffeomorph ThreeModel ThreeModel ∞ incR := fun y =>
          isLocalDiffeomorphAt_subtypeCodRestrict (fun v : standardCapWindow Rflow => hsub v.property)
            (isLocalDiffeomorph_subtype_val (standardCapWindow Rflow) y)
        have hiRs : IsSmoothEmbedding ThreeModel ThreeModel ∞ incR :=
          DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
            hiR (by intro a b hab; exact Subtype.ext (congrArg (fun v : standardCapWindow Dbig => v.val) hab))
        let wR := w.restrictWindow hRflow hRDbig
        let JR := Jbig ∘ incR
        have hJR : IsSmoothEmbedding ThreeModel ThreeModel ∞ JR := hJbig.comp hiRs (by simp)
        have hinner (y : standardCapWindow Rflow) : ‖(incR y).val‖ < Dbig := y.property.trans_le hmargin
        have hupper : ∀ y : standardCapWindow Rflow, ∀ v : TangentSpace ThreeModel y,
            wR.windowMetric.inner y v v ≤ (3/2 : ℝ)*StandardCap.metric.inner y.val v v := by
          intro y v
          rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
          have hb := (w.window_inner_bounds hζhalf (hinner y) v).2
          rw [standardCapMetric_eq_metric] at hb
          exact hb
        have hzeroR : ∀ y (v a : TangentSpace ThreeModel y), wR.windowMetric.inner y v a =
            q * (H.initialMetric first).inner (JR y) (mfderiv ThreeModel ThreeModel JR y v)
              (mfderiv ThreeModel ThreeModel JR y a) := by
          intro y v a
          rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
          change w.windowMetric.inner (incR y) v a = _
          have hz := hzero (incR y) (show TangentSpace ThreeModel (incR y) from v)
            (show TangentSpace ThreeModel (incR y) from a)
          have hd := mfderiv_comp y (hJbig.contMDiff.mdifferentiableAt (by simp))
            (hiR.contMDiff.mdifferentiableAt (by simp))
          simp only [incR, mfderiv_opens_incl] at hd
          dsimp only [TangentSpace] at hd hz ⊢
          rw [hd]
          exact hz
        have hDR : D ≤ Rflow := by linarith only [hDRflow]
        let incD : standardCapWindow D → standardCapWindow Rflow :=
          TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDR (le_refl 1)))
        have hanchorR : Atrace.point first le_rfl hle = JR (incD z) := hanchor
        have hwindow : (wR.restrictWindow hD hDR).windowMetric = (w.restrictWindow hD hDD).windowMetric := by
          apply SmoothRiemannianMetric.ext_inner
          intro y v a
          rfl
        have hqstep : q₀ ≤ Cstep*q := hq₀Q.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le)
        have hmreset' : mreset ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
        have hζreset' : ζ ≤ ζreset := hζ.trans ((min_le_right _ _).trans (min_le_right _ _))
        have hT : 0 < q*(s-H.time first) := mul_pos hq (sub_pos.mpr ((H.time_strictMono.monotone hle).trans_lt G.lt))
        have hresetR := hresetD wR (le_max_right _ _) hmreset' hζreset'
          (q*(s-H.time first)) hT (htime.trans (min_le_left _ _))
        rcases H.mem_event_slab_or_after_stage_of_ne_time first last hτs hne with
          ⟨next, hnext, hnextlast, hτevent⟩ | hτfinal
        · obtain ⟨G₀, L₀, x₀, B, hsource₀, hinit₀, hreg₀, hterminal₀, hpoint₀, hB⟩ :=
            H.exists_event_prefix_terminal_anchor first last hle next hnext hnextlast hτevent x.val Atrace
          have hscalarEq : ∀ t y, G₀.flow.scalar t y = (H.event next).incoming.flow.scalar t y := by
            intro t y
            change metricScalarAt (G₀.flow.base.metric t) y = _
            rw [hsource₀]
            rfl
          have hfinal₀ : ∀ y : (H.stage next.castSucc).Carrier, ∀ t ∈ Ioo (H.time next.castSucc) τ,
              q₀ < G₀.flow.scalar t y →
              |derivWithin (fun v => G₀.flow.scalar v y) (Iic t) t| ≤ C * G₀.flow.scalar t y^2 := by
            intro y t ht hs
            simp only [hscalarEq] at hs ⊢
            exact hderiv next hnext hnextlast y t ⟨ht.1, ht.2.trans hτevent.2⟩ hs
          have hprior := ihLarge w hlargeR hlargem hlargeζ H first next.castSucc hnext τ G₀ L₀
            hinit₀ Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower
            (fun j hf hl b => (hdelta j hf (hl.trans (next.castSucc_lt_succ.le.trans hnextlast)) b).trans (min_le_left _ _))
            (fun j hf hl => hderiv j hf (hl.trans (next.castSucc_lt_succ.le.trans hnextlast)))
            hfinal₀ (le_min hτΘ hτbound) (incD z) x₀ B
            ((hB first le_rfl hnext).trans hanchor)
          have hresult := hstepR wR (hmlarge.trans hlargem) hζhalf hupper H first last hle next hnext hnextlast
            JR hJR τ G₀ L₀ hsource₀ hterminal₀ ⟨hτevent.1.le,hτevent.2⟩ q q₀ a₀ hq hqstep haq hzeroR
            s G L hinit (fun j hf hl => hderiv j (hnext.trans hf) hl) hfinal
            (htime.trans (min_le_left _ _))
            (hremaining.trans ((min_le_right _ _).trans (min_le_left _ _))) parameters records hfixed hlower
            (fun j hf hl b => (hdelta j (hnext.trans hf) hl b).trans ((min_le_right _ _).trans (min_le_right _ _)))
            D ε η hD hDR N z x Atrace hanchorR x₀ hprior
          apply hwindow ▸ hresult
          intro S hS hSzero hgram hcurv
          obtain ⟨hDR', F, hF, hFmetric, hFzero, hFgram, hFcurv, Q, hQ, hFclose⟩ :=
            hresetR S hS hSzero hgram hcurv
          exact ⟨F,hF,hFmetric,hFzero,hFgram,hFcurv,Q,hQ,hFclose⟩
        · obtain ⟨G₀, L₀, x₀, B, hsource₀, hinit₀, hreg₀, hterminal₀, hpoint₀, hB⟩ :=
            H.exists_incoming_prefix_terminal_anchor first last hle G hinit hτfinal x.val Atrace
          have hscalarEq : ∀ t y, G₀.flow.scalar t y = G.flow.scalar t y := by
            intro t y
            change metricScalarAt (G₀.flow.base.metric t) y = _
            rw [hsource₀]
            rfl
          have hfinal₀ : ∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) τ,
              q₀ < G₀.flow.scalar t y →
              |derivWithin (fun v => G₀.flow.scalar v y) (Iic t) t| ≤ C * G₀.flow.scalar t y^2 := by
            intro y t ht hs
            simp only [hscalarEq] at hs ⊢
            exact hfinal y t ⟨ht.1, ht.2.trans hτfinal.2⟩ hs
          have hprior := ihLarge w hlargeR hlargem hlargeζ H first last hle τ G₀ L₀
            hinit₀ Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower
            (fun j hf hl b => (hdelta j hf hl b).trans (min_le_left _ _)) hderiv
            hfinal₀ (le_min hτΘ hτbound) (incD z) x₀ B
            ((hB first le_rfl hle).trans hanchor)
          have hbudget : 2*C*Cstep*(q*(s-τ)) ≤ 1 := by
            have hp : 0 < 2*((C : ℝ)+1)*Cstep := by positivity
            have hd := hremaining.trans ((min_le_right _ _).trans (min_le_right _ _))
            have hh := (le_div_iff₀ hp).mp (show q*(s-τ) ≤ 1/(2*((C : ℝ)+1)*Cstep) from by
              simpa only [one_div] using hd)
            have hn := mul_nonneg hq.le (sub_nonneg.mpr hτfinal.2.le)
            nlinarith only [hh, mul_nonneg (show 0 ≤ 2*Cstep by positivity) hn]
          have hresult := incoming_window_control_step_of_final_prefix (ε := ε) (η := η) (N := N) wR H first last hle
            hD hDR hq hCstep (le_max_right _ _) hqstep haq G L hinit G₀ L₀ hsource₀ hterminal₀ hτfinal.2
            JR hzeroR (fun y t ht hs => hfinal y t ⟨hτfinal.1.trans ht.1,ht.2⟩ hs)
            hbudget parameters records hfixed hlower z x Atrace hanchorR x₀ hprior
          apply hwindow ▸ hresult
          intro S hS hSzero hgram hcurv
          obtain ⟨hDR', F, hF, hFmetric, hFzero, hFgram, hFcurv, Q, hQ, hFclose⟩ :=
            hresetR S hS hSzero hgram hcurv
          exact ⟨F,hF,hFmetric,hFzero,hFgram,hFcurv,Q,hQ,hFclose⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Θ / δ)
  have hlarge : Θ ≤ ((n : ℝ) + 1) * δ / 2 := by
    have hh := (div_lt_iff₀ hδ).mp hn
    nlinarith only [hh, hδ]
  exact ⟨P, Cstep, Cbirth, hP, hCstep, hCbirth, @prepared_incoming_control_mono Θ Θ _ P Cstep Cbirth C hlarge (hcontrol n)⟩

theorem exists_uniform_prepared_incoming_cap_window_flow_of_backward_trace
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
      ∃ R : ℝ, ∃ hDR : D + 1 < R, ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hR : R ≤ Dbig), m₀ ≤ m → ζ ≤ ζ₀ →
      let hDD : D ≤ Dbig := by linarith;
      let inc : standardCapWindow D → standardCapWindow Dbig :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)));
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ Θ →
      ∀ (z : standardCapWindow D) (x : (H.stage last).Carrier)
        (Atrace : BackwardPointTrace H first last hle x),
        Atrace.point first le_rfl hle = Jbig (inc z) →
      ∃ hx : x ∈ G.terminalRegularRegion,
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
          IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
          (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = (Jbig ∘ inc) y) ∧
          H.backwardSurvivorIncomingMap first last hle G (Ξ z) = ⟨x,hx⟩ ∧
          ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
            (gflow : ℝ → SmoothRiemannianMetric ThreeModel
              (H.backwardSurvivorIncomingDomain first last hle G))
            (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed 0 (q * (s - H.time first))
                (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
            (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
              ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
                gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                  (H.backwardSurvivorIncomingDomain first last hle G)) ∧
            (∀ t ∈ Icc (H.time last) s,
              gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
            IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
            (∀ t, S.base.metric t =
              localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
            (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) y z.2 j k)
                (Icc 0 (q * (s - H.time first)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
            (∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ y : standardCapWindow D,
              normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ P ^ 2 ∧ |S.scalar t y| ≤ Creset) ∧
            ∃ Q : StandardSolution, ENNReal.ofReal (q * (s - H.time first)) < Q.val.lifetime ∧
              ∀ t ∈ Icc 0 (q * (s - H.time first)),
                (∀ j ≤ N, ∀ y : standardCapWindow D,
                  metricDerivNorm j (S.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
                ∀ j ≤ 2, ∀ y : standardCapWindow D,
                  metricDerivNorm j (S.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η := by
  obtain ⟨P,Creset,Cbirth,hP,hCreset,hCbirth,hwindow⟩ :=
    exists_prepared_incoming_window_control.{u, uE, uH, uM} Θ C hΘ hΘ1
  simp only [preparedIncomingControl, incomingWindowControl, min_self] at hwindow
  refine ⟨P,Creset,Cbirth,hP,hCreset,hCbirth,?_⟩
  intro E H₀ _ _ _ _ _ I _ D ε η hD hε hη N
  obtain ⟨R,hDR,m₀,hm₀,ζ₀,δ₀,hζ₀,hζhalf,hδ₀,hwindow⟩ := hwindow (I := I) D ε η hD hε hη N
  refine ⟨R,hDR,m₀,hm₀,ζ₀,δ₀,hζ₀,hζhalf,hδ₀,?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
  have hscalar : ∀ τ ∈ Ioo (H.time last) s, G.flow.scalar τ x ≤ Creset*q := by
    intro τ hτ
    let Pstage := H.stage last
    let F := G.closedPrefix τ hτ.1 hτ.2
    let G₀ := F.restrictIncoming le_rfl F.lt le_rfl
    let L₀ := F.endpointTerminalLimitMetric Pstage
    have hreg : G₀.terminalRegularRegion = univ := F.terminalRegularRegion_eq_univ Pstage
    let x₀ : G₀.terminalRegularOpen := ⟨x, by
      change x ∈ G₀.terminalRegularRegion
      rw [hreg]
      trivial⟩
    have hscalarEq : ∀ t y, G₀.flow.scalar t y = G.flow.scalar t y := fun _ _ => rfl
    have hinit₀ : G₀.flow.base.metric (H.time last) = H.initialMetric last := hinit
    have hfinal₀ : ∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) τ,
        q₀ < G₀.flow.scalar t y →
        |derivWithin (fun v => G₀.flow.scalar v y) (Iic t) t| ≤ C * G₀.flow.scalar t y ^ 2 := by
      intro y t ht hs
      simp only [hscalarEq] at hs ⊢
      exact hfinal y t ⟨ht.1,ht.2.trans hτ.2⟩ hs
    have htime₀ : q*(τ-H.time first) ≤ Θ :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hτ.2.le _) hq.le).trans htime
    obtain ⟨Ξ,hΞs,hbirth,hmark,hΞ,gflow,S,hslabs,hlast,hS,hSzero,hmetric,hgram,hcurv,Q,hQ,hclose⟩ :=
      hwindow w hR hm hζ H first last hle τ G₀ L₀ hinit₀ Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
        parameters records hfixed hlower hdelta hderiv hfinal₀ htime₀ z x₀ Atrace hanchor
    have hage : 0 ≤ q*(τ-H.time first) := mul_nonneg hq.le
      (sub_nonneg.mpr ((H.time_strictMono.monotone hle).trans hτ.1.le))
    have hb := (le_abs_self (S.scalar (q*(τ-H.time first)) z)).trans
      (hcurv _ ⟨hage,le_rfl⟩ z).2
    have hclock : H.time first + q*(τ-H.time first)/q = τ := by
      rw [mul_div_cancel_left₀ _ hq.ne']
      ring
    change metricScalarAt (S.base.metric (q*(τ-H.time first))) z ≤ Creset at hb
    rw [hmetric,hclock,metricScalarAt_localPull,metricScalarAt_scaleMetric,
      hlast τ ⟨hτ.1.le,le_rfl⟩,H.backwardSurvivorIncomingMetric_terminal,
      metricScalarAt_localPull] at hb
    have hterminal : L₀.metric = (G.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen := rfl
    rw [hterminal,metricScalarAt_restrictOpen] at hb
    have hpoint : (Ξ z).val.val = x := congrArg Subtype.val hmark
    change q⁻¹ * G.flow.scalar τ (Ξ z).val.val ≤ Creset at hb
    rw [hpoint,←div_eq_inv_mul,div_le_iff₀ hq] at hb
    exact hb
  have hx : x ∈ G.terminalRegularRegion := by
    apply G.mem_terminalRegularRegion_of_frequently_scalar_le hq₀ hfinal
    exact (Filter.Eventually.mono (Ioo_mem_nhdsLT G.lt) (fun τ hτ => hscalar τ hτ)).frequently
  refine ⟨hx,?_⟩
  exact hwindow w hR hm hζ H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal htime z ⟨x,hx⟩ Atrace hanchor

theorem exists_uniform_prepared_incoming_cap_window_flow_of_bounded_normalized_time
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
      ∃ R : ℝ, ∃ hDR : D + 1 < R, ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hR : R ≤ Dbig), m₀ ≤ m → ζ ≤ ζ₀ →
      let hDD : D ≤ Dbig := by linarith;
      let inc : standardCapWindow D → standardCapWindow Dbig :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)));
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ Θ →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (Atrace : BackwardPointTrace H first last hle x.val),
        Atrace.point first le_rfl hle = Jbig (inc z) →
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
          IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
          (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = (Jbig ∘ inc) y) ∧
          H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
          ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
            (gflow : ℝ → SmoothRiemannianMetric ThreeModel
              (H.backwardSurvivorIncomingDomain first last hle G))
            (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed 0 (q * (s - H.time first))
                (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
            (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
              ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
                gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                  (H.backwardSurvivorIncomingDomain first last hle G)) ∧
            (∀ t ∈ Icc (H.time last) s,
              gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
            IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
            (∀ t, S.base.metric t =
              localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
            (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) y z.2 j k)
                (Icc 0 (q * (s - H.time first)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
            (∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ y : standardCapWindow D,
              normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ P ^ 2 ∧ |S.scalar t y| ≤ Creset) ∧
            ∃ Q : StandardSolution, ENNReal.ofReal (q * (s - H.time first)) < Q.val.lifetime ∧
              ∀ t ∈ Icc 0 (q * (s - H.time first)),
                (∀ j ≤ N, ∀ y : standardCapWindow D,
                  metricDerivNorm j (S.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) y < ε) ∧
                ∀ j ≤ 2, ∀ y : standardCapWindow D,
                  metricDerivNorm j (S.base.metric t)
                    ((Q.val.metric t).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) y < η := by
  obtain ⟨P,Creset,Cbirth,hP,hCreset,hCbirth,hwindow⟩ :=
    exists_uniform_prepared_incoming_cap_window_flow_of_backward_trace Θ C hΘ hΘ1
  refine ⟨P,Creset,Cbirth,hP,hCreset,hCbirth,?_⟩
  intro E H₀ _ _ _ _ _ I _ D ε η hD hε hη N
  obtain ⟨R,hDR,m₀,hm₀,ζ₀,δ₀,hζ₀,hζhalf,hδ₀,hwindow⟩ := hwindow (I := I) D ε η hD hε hη N
  refine ⟨R,hDR,m₀,hm₀,ζ₀,δ₀,hζ₀,hζhalf,hδ₀,?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
  obtain ⟨hx,hflow⟩ := hwindow w hR hm hζ H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal htime z x.val Atrace hanchor
  exact hflow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
