import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

def CanonicalNeighborhoodsThroughSurgeryStrongAt (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) (B ε Λ : ℝ) : Prop :=
  ∃ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime Cgrad : ℝ≥0)
    (κ a₀ : ℝ),
    1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < qcan ∧ 0 < τmin ∧ 0 < δmax ∧ 0 < ρmax ∧
    0 < εcap ∧ 0 < Dcap ∧ 0 < κ ∧ 0 < a₀ ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant ≤ Λ →
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ hend : H.time (Fin.last H.eventCount) = H.horizon, H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) ∧
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (H.time j.succ)) ∧
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan
          (H.time j.succ)) ∧
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) ∧
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        ∀ hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount),
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) ∧
        G.GradientBoundBefore Cgrad qcan s ∧
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) ∧
        G.SpatiallyCanonicalBefore ε C1s C2s qcan s ∧
        ∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hend G hG κ ε t₀

def CanonicalNeighborhoodsThroughSurgeryStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    Prop :=
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε Λ : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
    CanonicalNeighborhoodsThroughSurgeryStrongAt P₀ g₀ B ε Λ

def CanonicalNeighborhoodsThroughSurgeryOfRecenter (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) (Λ εbar : ℝ) : Prop :=
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∃ (C1 C2 qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime : ℝ≥0),
    1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < qcan ∧ 0 < τmin ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant ≤ Λ →
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) →
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) ∧
        ∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε

theorem canonicalNeighborhoodsThroughSurgeryOfRecenter_of_strong
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
    (hcn : CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ εbar : ℝ, 0 < εbar ∧ CanonicalNeighborhoodsThroughSurgeryOfRecenter P₀ g₀ Λ εbar := by
  obtain ⟨εbar, hεbar, hcn⟩ := hcn
  refine ⟨εbar, hεbar, ?_⟩
  intro B ε hB hε hε' hεbar'
  obtain ⟨C1, C2, _, _, qcan, τmin, δmax, ρmax, εcap, Dcap, mcap, Ctime, _, _, _, hC1, hC2, -, -,
    hqcan, hτ, hδmax, hρmax, hεcap, hDcap, -, -, hcl⟩ := hcn B ε Λ hB hε hε' hεbar' hΛ
  refine ⟨C1, C2, qcan, τmin, δmax, ρmax, εcap, Dcap, mcap, Ctime, hC1, hC2, hqcan, hτ, hδmax,
    hρmax, hεcap, hDcap, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ hΛp H hinit htime hhor hclass
  obtain ⟨hder, -, -, -, -, -, hslab⟩ :=
    hcl p₀ δbound ρbound hacc hD hm hδ hρ hΛp H hinit htime hhor hclass
  refine ⟨hder, fun s G hs hinitG hsing => ?_⟩
  obtain ⟨hderG, -, hcanG, -⟩ := hslab s G hs hinitG hsing
  exact ⟨hderG, hcanG⟩

def UniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B εbar : ℝ), 0 < B → 0 < εbar →
  ∃ Λ : ℝ, 0 < Λ ∧
  ∀ Ctime : ℝ≥0,
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ ε ≤ εbar ∧
  ∀ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Cgrad : ℝ≥0) (κ a₀ : ℝ),
    1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < δmax → 0 < ρmax →
    0 < εcap → 0 < Dcap → 0 < κ → 0 < a₀ →
  ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
    p₀.modelAccuracy ≤ εcap ∧ Dcap ≤ p₀.modelRadius ∧ mcap ≤ p₀.modelOrder ∧
    0 < δbound ∧ δbound ≤ δmax ∧ 0 < ρbound ∧ ρbound ≤ ρmax ∧ p₀.recenterConstant ≤ Λ ∧
    0 < v ∧
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ hend : H.time (Fin.last H.eventCount) = H.horizon, H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (H.time j.succ)) →
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan
          (H.time j.succ)) →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        ∀ hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount),
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) →
        G.GradientBoundBefore Cgrad qcan s →
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) →
        G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
        (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
            (H.time (Fin.last H.eventCount)) s)
          (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
            (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
          (q : CutoffParameters),
          E.incoming = G ∧
          (H.appendEvent E.incoming.lt E hinit).hasCanonicalCutoffRecords p₀ δbound ρbound ∧
          q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
          q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
          q.recenterConstant = p₀.recenterConstant ∧
          Nonempty (GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
            (Fin.last H.eventCount) q) ∧
          E.transition.boundaryFrameReversing ∧
          E.toMetricCutCapEvent.poincareStandardDiscarded ∧
          ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F

theorem exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong
    (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric)
    (hstep : UniformDebitSurgeryStepStrong P₀ g₀)
    (hcn : CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀) :
    Nonempty (PoincareControlledExtinction P₀.toClosedOrientedManifold g₀) := by
  apply exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants P₀ g₀
  obtain ⟨εbar, hεbar, hcn⟩ := hcn
  intro B hB
  obtain ⟨Λ, hΛ, hstepB⟩ := hstep B εbar hB hεbar
  obtain ⟨_, _, _, _, q₀, _, δ₀, ρ₀, ε₀, D₀, m₀, Ctime, _, _, _, -, -, -, -, hq₀, -, hδ₀, hρ₀,
    hε₀, hD₀, -, -, hcl₀⟩ := hcn B (min (1 / 22) εbar) Λ hB (lt_min (by norm_num) hεbar)
      ((min_le_left _ _).trans_lt (by norm_num)) (min_le_right _ _) hΛ
  obtain ⟨ε, hε, hε', hεbarε, hstepε⟩ := hstepB Ctime
  obtain ⟨C1, C2, C1s, C2s, q₁, τmin, δ₁, ρ₁, ε₁, D₁, m₁, _, Cgrad, κ, a₀, hC1, hC2, hC1s, hC2s,
    -, hτ, hδ₁, hρ₁, hε₁, -, hκ, ha₀, hcl₁⟩ := hcn B ε Λ hB hε hε' hεbarε hΛ
  obtain ⟨p₀, δbound, ρbound, v, hacc, hD, hm, -, hδle, -, hρle, hΛle, hv, hnext⟩ :=
    hstepε C1 C2 C1s C2s (max q₀ q₁) τmin (min δ₀ δ₁) (min ρ₀ ρ₁) (min ε₀ ε₁) (max D₀ D₁)
      (max m₀ m₁) Cgrad κ a₀ hC1 hC2 hC1s hC2s (lt_max_of_lt_left hq₀) hτ (lt_min hδ₀ hδ₁)
      (lt_min hρ₀ hρ₁) (lt_min hε₀ hε₁) (lt_max_of_lt_left hD₀) hκ ha₀
  refine ⟨p₀, v, fun H => H.hasCanonicalCutoffRecords p₀ δbound ρbound, hv,
    RetainedCoreHistory.hasCanonicalCutoffRecords_atZero P₀ g₀ p₀ δbound ρbound, ?_⟩
  intro H initial hInv p htime hhor hpf hpD hpm hpε hpc _ _ _ _ s G hs hinit hsing
  rw [le_min_iff] at hacc hδle hρle
  rw [max_le_iff] at hD hm
  obtain ⟨hderiv, -, -, -, -, -, hslab₀⟩ :=
    hcl₀ p₀ δbound ρbound hacc.1 hD.1 hm.1 hδle.1 hρle.1 hΛle H initial htime hhor hInv
  obtain ⟨-, hgrad, hcan, hspat, hpinch, hnc, hslab₁⟩ :=
    hcl₁ p₀ δbound ρbound hacc.2 hD.2 hm.2 hδle.2 hρle.2 hΛle H initial htime hhor hInv
  obtain ⟨hderivG, -⟩ := hslab₀ s G hs hinit hsing
  obtain ⟨-, hgradG, hcanG, hspatG, hncG⟩ := hslab₁ s G hs hinit hsing
  obtain ⟨Q, E, hinitE, q, hEG, hInvK, hqf, hqD, hqm, hqε, hqc, hrec, hbfr, hctrl, hdebit⟩ :=
    hnext H initial htime hhor hInv
      (fun j y t ht hR => hderiv j y t ht ((le_max_left _ _).trans_lt hR))
      (fun j => (H.toHistory.event j).incoming.gradientBoundBefore_of_threshold_le
        (le_max_right _ _) (hgrad j))
      (fun j => (H.toHistory.event j).incoming.canonicalBefore_of_threshold_le
        (le_max_right _ _) (hcan j))
      (fun j => (H.toHistory.event j).incoming.spatiallyCanonicalBefore_of_threshold_le
        (le_max_right _ _) (hspat j))
      hpinch hnc s G hs hinit hsing
      (fun y t ht hR => hderivG y t ht ((le_max_left _ _).trans_lt hR))
      (G.gradientBoundBefore_of_threshold_le (le_max_right _ _) hgradG)
      (fun y t ht hR hτ => hcanG y t ht ((le_max_right _ _).trans_lt hR) hτ)
      (G.spatiallyCanonicalBefore_of_threshold_le (le_max_right _ _) hspatG) hncG
  exact ⟨Q, E, hinitE, q, hEG, hInvK, hqf.trans hpf.symm, hqD.trans hpD.symm,
    hqm.trans hpm.symm, hqε.trans hpε.symm, hqc.trans hpc.symm, hrec, hbfr, hctrl, hdebit⟩

theorem CutoffParameters.recenterConstant_mul_le_half {p₀ : CutoffParameters} {Λ δ : ℝ}
    (hΛ : 0 < Λ) (hp : p₀.recenterConstant ≤ Λ) (hδ : δ ≤ (2 * Λ)⁻¹) :
    p₀.recenterConstant * δ ≤ 1 / 2 := by
  have h4 : (4 : ℝ) ≤ p₀.recenterConstant := p₀.recenterConstant_ge_four
  rcases le_or_gt δ 0 with h | h
  · nlinarith
  · calc p₀.recenterConstant * δ ≤ Λ * δ := mul_le_mul_of_nonneg_right hp h.le
      _ ≤ Λ * (2 * Λ)⁻¹ := mul_le_mul_of_nonneg_left hδ hΛ.le
      _ = 1 / 2 := by field_simp

theorem canonicalNeighborhoodsThroughSurgeryStrong_of_leaves
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (hpinch : PinchingThroughSurgery P₀ g₀) (hnon : NoncollapsingThroughSurgery P₀ g₀)
    (hcont : CanonicalNeighborhoodContinuation P₀ g₀)
    (hspat : SpatialCanonicalContinuation P₀ g₀) :
    CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀ := by
  obtain ⟨εbar, hεbar, hcont⟩ := hcont
  obtain ⟨εs, hεs, hspat⟩ := hspat
  refine ⟨min εbar εs, lt_min hεbar hεs, ?_⟩
  intro B ε Λ hB hε hε' hεbar' hΛ
  obtain ⟨phi, δP, ρP, εP, hphi, hδP, hρP, hεP, hP⟩ := hpinch B hB
  obtain ⟨C1, C2, τmin, Ctime, Cgrad, hC1, hC2, hτ, hF⟩ :=
    hcont B ε hB hε hε' (hεbar'.trans (min_le_left _ _))
  obtain ⟨C1s, C2s, Cs, hC1s, hC2s, hCs, hS⟩ :=
    hspat B ε hB hε hε' (hεbar'.trans (min_le_right _ _)) C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
  obtain ⟨κ, hκ, hN⟩ :=
    hnon B ε C1 C2 C1s C2s τmin Ctime Cgrad phi hB hε hε' hC1 hC2 hC1s hC2s hτ hphi
  obtain ⟨q₄, -, hS₄⟩ := hS κ phi hκ hphi
  obtain ⟨qcan, δF, ρF, εF, DF, mF, hq₄c, hqcan, hδF, hρF, hεF, hDF, hstep⟩ :=
    hF C1s C2s Cs hC1s hC2s hCs κ phi hκ hphi q₄
  obtain ⟨qs, δS, ρS, εS, DS, mS, hqs, hqsC, hδS, hρS, hεS, -, hsp⟩ := hS₄ qcan hq₄c
  obtain ⟨δN, ρN, εN, DN, mN, hδN, hρN, hεN, -, hball⟩ := hN qcan qs hqcan hqs
  obtain ⟨a₀, ha₀, hfix⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  have hΛinv : 0 < (2 * Λ)⁻¹ := inv_pos.mpr (by positivity)
  refine ⟨C1, C2, C1s, C2s, qs, τmin, min δP (min δF (min δS (min δN (2 * Λ)⁻¹))),
    min ρP (min ρF (min ρS ρN)), min εP (min εF (min εS εN)), max DF (max DS DN),
    max mF (max mS mN), Ctime, Cgrad, κ, a₀, hC1, hC2, hC1s, hC2s, hqcan.trans_le hqs, hτ,
    lt_min hδP (lt_min hδF (lt_min hδS (lt_min hδN hΛinv))),
    lt_min hρP (lt_min hρF (lt_min hρS hρN)), lt_min hεP (lt_min hεF (lt_min hεS hεN)),
    lt_max_of_lt_left hDF, hκ, ha₀, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ hΛp H hinit htime hhor hclass
  simp only [le_min_iff, max_le_iff] at hacc hD hm hδ hρ
  have hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound := ⟨⟨hinit⟩, htime, hhor, hclass,
    CutoffParameters.recenterConstant_mul_le_half hΛ hΛp hδ.2.2.2.2⟩
  have hP' := hP p₀ δbound ρbound hacc.1 hδ.1 hρ.1 H hH
  have hpinched : H.EventSlabsPinched phi :=
    fun j => hP' j.castSucc (H.time j.succ) (H.toHistory.event j).incoming
      (H.isContinuationSlab_event hhor j)
  have hF' := hstep qs hqs hqsC p₀ δbound ρbound hacc.2.1 hD.1 hm.1 hδ.2.1 hρ.2.1 H hH hpinched
  have hS' := hsp p₀ δbound ρbound hacc.2.2.1 hD.2.1 hm.2.1 hδ.2.2.1 hρ.2.2.1 H hH hpinched
  have hN' := hball p₀ δbound ρbound hacc.2.2.2 hD.2.2 hm.2.2 hδ.2.2.2.1 hρ.2.2.2 H hH hpinched
  have hstage : ∀ k : Fin (H.eventCount + 1),
      H.EventSlabsCanonical ε C1 C2 qcan τmin k ∧ H.EventSlabsDerivative Ctime qcan k ∧
        H.EventSlabsGradient Cgrad qcan k ∧ H.EventSlabsSpatiallyCanonical ε C1s C2s qs k ∧
        H.NoncollapsedBefore κ ε (H.time k) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      refine ⟨fun j hj => (Fin.not_lt_zero _ hj).elim, fun j hj => (Fin.not_lt_zero _ hj).elim,
        fun j hj => (Fin.not_lt_zero _ hj).elim, fun j hj => (Fin.not_lt_zero _ hj).elim, ?_⟩
      rw [H.time_zero]
      exact H.noncollapsedBefore_zero κ ε
    | succ j ih =>
      obtain ⟨hcanP, hderP, hgradP, hspatP, hncP⟩ := ih
      have hcl := (H.toHistory.event j).incoming.canonicalBefore_end_of_continuation_spatial
        (fun t₀ => H.NoncollapsedBefore κ ε t₀)
        (fun t₀ ht₀ hc hd hg hs =>
          hN'.1 j hcanP hderP hgradP hspatP t₀ ⟨ht₀.1, ht₀.2.le⟩ hc hd hg hs)
        hncP
        (fun t₀ ht₀ hc hd hg hs hn =>
          have hF₀ := hF'.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn
          (H.toHistory.event j).incoming.exists_boundsOn_spatiallyCanonicalOn hF₀
            (hS'.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn hF₀))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hcanP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.1
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hderP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.2.1
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hgradP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.2.2.1
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hspatP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.2.2.2
      · exact hN'.1 j hcanP hderP hgradP hspatP (H.time j.succ)
          ⟨H.time_strictMono j.castSucc_lt_succ, le_rfl⟩ hcl.1 hcl.2.1 hcl.2.2.1 hcl.2.2.2
  obtain ⟨hcanL, hderL, hgradL, hspatL, hncL⟩ := hstage (Fin.last H.eventCount)
  refine ⟨fun j y t ht hR => hderL j (Fin.castSucc_lt_last j) y t ht (hqs.trans_lt hR),
    fun j => (H.toHistory.event j).incoming.gradientBoundBefore_of_threshold_le hqs
      (hgradL j (Fin.castSucc_lt_last j)),
    fun j => (H.toHistory.event j).incoming.canonicalBefore_of_threshold_le hqs
      (hcanL j (Fin.castSucc_lt_last j)),
    fun j => hspatL j (Fin.castSucc_lt_last j), (hfix H.toHistory hinit).1, hncL, ?_⟩
  intro s G hs hinitG _
  have hG : H.IsContinuationSlab B (Fin.last H.eventCount) G := ⟨hs, hinitG⟩
  have hpinchG := hP' (Fin.last H.eventCount) s G hG
  have hcl := G.canonicalBefore_end_of_continuation_spatial
    (fun t₀ => H.TerminalNoncollapsedBefore htime G hinitG κ ε t₀)
    (fun t₀ ht₀ hc hd hg hsp =>
      hN'.2 s G hG hpinchG hcanL hderL hgradL hspatL t₀ ht₀ hc hd hg hsp)
    (H.terminalNoncollapsedBefore_start htime G hinitG κ ε)
    (fun t₀ ht₀ hc hd hg hsp hn =>
      have hF₀ := hF'.2 s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn
      G.exists_boundsOn_spatiallyCanonicalOn hF₀
        (hS'.2 s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn hF₀))
  refine ⟨fun y t ht hR => hcl.2.1 y t ht (hqs.trans_lt hR),
    G.gradientBoundBefore_of_threshold_le hqs hcl.2.2.1,
    fun y t ht hR hτ => hcl.1 y t ht (hqs.trans_lt hR) hτ, hcl.2.2.2, ?_⟩
  intro t₀ ht₀
  exact hN'.2 s G hG hpinchG hcanL hderL hgradL hspatL t₀ ht₀
    (G.canonicalBefore_mono ht₀.2.le hcl.1) (G.derivativeBoundBefore_mono ht₀.2.le hcl.2.1)
    (G.gradientBoundBefore_mono ht₀.2.le hcl.2.2.1)
    (G.spatiallyCanonicalBefore_mono ht₀.2.le hcl.2.2.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
