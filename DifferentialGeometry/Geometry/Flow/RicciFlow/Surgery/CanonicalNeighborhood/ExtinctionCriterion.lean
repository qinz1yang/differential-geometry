import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingModelCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SingularEventExtinction

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

def CanonicalNeighborhoodsThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 →
  ∃ (C1 C2 qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime : ℝ≥0),
    1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < qcan ∧ 0 < τmin ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
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

def UniformDebitSurgeryStep (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B : ℝ), 0 < B →
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 11 ∧
  ∀ (C1 C2 qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime : ℝ≥0),
    1 ≤ C1 → 1 ≤ C2 → 0 < qcan → 0 < τmin → 0 < δmax → 0 < ρmax → 0 < εcap → 0 < Dcap →
  ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
    p₀.modelAccuracy ≤ εcap ∧ Dcap ≤ p₀.modelRadius ∧ mcap ≤ p₀.modelOrder ∧
    0 < δbound ∧ δbound ≤ δmax ∧ 0 < ρbound ∧ ρbound ≤ ρmax ∧ 0 < v ∧
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) →
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) →
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) →
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

theorem exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods
    (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric)
    (hstep : UniformDebitSurgeryStep P₀ g₀) (hcn : CanonicalNeighborhoodsThroughSurgery P₀ g₀) :
    Nonempty (PoincareControlledExtinction P₀.toClosedOrientedManifold g₀) := by
  apply exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants P₀ g₀
  intro B hB
  obtain ⟨ε, hε, hε', hstepB⟩ := hstep B hB
  obtain ⟨C1, C2, qcan, τmin, δmax, ρmax, εcap, Dcap, mcap, Ctime, hC1, hC2, hqcan, hτ, hδmax,
    hρmax, hεcap, hDcap, hclass⟩ := hcn B ε hB hε hε'
  obtain ⟨p₀, δbound, ρbound, v, hacc, hD, hm, -, hδle, -, hρle, hv, hnext⟩ :=
    hstepB C1 C2 qcan τmin δmax ρmax εcap Dcap mcap Ctime hC1 hC2 hqcan hτ hδmax hρmax hεcap hDcap
  refine ⟨p₀, v, fun H => H.hasCanonicalCutoffRecords p₀ δbound ρbound, hv,
    RetainedCoreHistory.hasCanonicalCutoffRecords_atZero P₀ g₀ p₀ δbound ρbound, ?_⟩
  intro H initial hInv p htime hhor hpf hpD hpm hpε hpc _ _ _ _ s G hs hinit hsing
  obtain ⟨hderiv, hslab⟩ :=
    hclass p₀ δbound ρbound hacc hD hm hδle hρle H initial htime hhor hInv
  obtain ⟨hderivG, hcnG⟩ := hslab s G hs hinit hsing
  obtain ⟨Q, E, hinitE, q, hEG, hInvK, hqf, hqD, hqm, hqε, hqc, hrec, hbfr, hctrl, hdebit⟩ :=
    hnext H initial htime hhor hInv hderiv s G hs hinit hsing hderivG hcnG
  exact ⟨Q, E, hinitE, q, hEG, hInvK, hqf.trans hpf.symm, hqD.trans hpD.symm,
    hqm.trans hpm.symm, hqε.trans hpε.symm, hqc.trans hpc.symm, hrec, hbfr, hctrl, hdebit⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
