import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def FineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 11 ∧
  ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧
  ∀ (κ C1s C2s qcan a₀ : ℝ) (Ctime Cgrad : ℝ≥0) (ε : ℝ),
    0 < κ → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < a₀ → 0 < ε → ε ≤ εcone →
  ∀ εc : ℝ, 0 < εc → εc < 1 / 2 →
  ∃ Kfine : ℝ, 1 ≤ Kfine ∧
  ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
  ∀ H : RetainedCoreHistory.{u}, InitialIdentification P₀ g₀ H.toHistory →
  ∀ hend : H.time (Fin.last H.eventCount) = H.horizon,
    H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
    (∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
    H.EventSlabsStronglyCanonical ε ε₁ C1s C2s qcan (Fin.last H.eventCount) →
    H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
  ∀ {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)),
    G.DerivativeBoundBefore Ctime qcan s → G.GradientBoundBefore Cgrad qcan s →
    H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1s C2s qcan s →
    (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
      H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
  ∀ {εP Λ : ℝ} (P : TerminalCorePresentation
      { stage := H.stage (Fin.last H.eventCount)
        startTime := H.time (Fin.last H.eventCount)
        endTime := s
        startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
        startTime_lt_endTime := G.lt
        slab := G
        terminal := L
        singular := hsing
        parameters := parameters } εP Λ), εP ≤ eta →
  ∀ Qc : ℝ, Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Qc →
    P.FineCutNecks εc Qc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
