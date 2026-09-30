import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ActualEventGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Cutoff.UniformDebit
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Manifold
open scoped Manifold ContDiff ENNReal NNReal
set_option autoImplicit false
noncomputable section
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

def GeometricHorizonProduction (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ (p₀ : CutoffParameters) (v : ℝ) (Inv : RetainedCoreHistory.{u} → Prop),
      0 < v ∧ Inv (RetainedCoreHistory.atZero P g) ∧
      ∀ H : RetainedCoreHistory.{u}, InitialIdentification P g H.toHistory → Inv H →
        ∀ p : CutoffParameters,
        H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
        p.fixed = p₀.fixed → p.modelRadius = p₀.modelRadius →
        p.modelOrder = p₀.modelOrder → p.modelAccuracy = p₀.modelAccuracy →
        p.recenterConstant = p₀.recenterConstant →
        (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) →
        (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) →
          (∀ i : Fin H.eventCount,
            (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                (H.coreEvent i).outputMetric univ +
                  ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
        ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s), s ≤ B →
          G.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
          ∃ (Q : OrientedThreeStage.{u})
            (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
              (H.time (Fin.last H.eventCount)) s)
            (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
              (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
            (q : CutoffParameters),
            E.incoming = G ∧ Inv (H.appendEvent E.incoming.lt E hinit) ∧
            q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
            q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
            q.recenterConstant = p.recenterConstant ∧
            Nonempty (GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q) ∧ E.transition.boundaryFrameReversing ∧
            E.toMetricCutCapEvent.poincareStandardDiscarded ∧
            GC.Surgery.ActualMetricEventGeometry E.toMetricCutCapEvent ∧
            ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F

theorem geometric_horizon_production_of_strong
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (hstep : UniformDebitSurgeryStepStrong P₀ g₀)
    (hcn : CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀) :
    GeometricHorizonProduction P₀ g₀ := by
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
    hqm.trans hpm.symm, hqε.trans hpε.symm, hqc.trans hpc.symm, hrec, hbfr, hctrl,
    GC.Surgery.actual_metric_event_geometry E.toMetricCutCapEvent hbfr hctrl, hdebit⟩

theorem geometric_horizon_production
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hcn : CanonicalNeighborhoodsThroughSurgeryStrong P g) :
    GeometricHorizonProduction P g :=
  geometric_horizon_production_of_strong P g (uniform_debit_surgery_step P g) hcn

end
end GC.GeneralFlow
