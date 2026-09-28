import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionRegularCrossingBefore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReducedVolumeBounds
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def HistoryScalarDerivativeBoundBefore (H : RetainedCoreHistory.{u})
    (Ctime : ℝ≥0) (qcan t : ℝ) : Prop :=
  ∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
    ∀ s ∈ Ioo (H.time j) (H.toHistory.stageEndTime j), s < t →
      qcan < metricScalarAt (H.toHistory.stageMetric j s) y →
      |derivWithin (fun z => metricScalarAt (H.toHistory.stageMetric j z) y) (Iic s) s| ≤
        Ctime * metricScalarAt (H.toHistory.stageMetric j s) y ^ 2

theorem exists_uniform_regularMinimizerEndpoint_of_regularizedCost_lt
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0), 0 < r₀ → 0 < qcan → 0 < Λ → 0 < ρ →
    ∃ (δ₀ ε₀ R₀ : ℝ) (m₀ : ℕ), 0 < δ₀ ∧ 0 < ε₀ ∧ 0 < R₀ ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ ε₀ → R₀ ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder →
      p₀.recenterConstant ≤ Λ → δbound ≤ δ₀ → ρbound ≤ ρ →
    ∀ (H : RetainedCoreHistory.{u}), Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    ∀ (t : Icc (0 : ℝ) H.toHistory.horizon), HistoryScalarDerivativeBoundBefore H Ctime qcan t →
    ∀ (p : (H.toHistory.stageAt t).Carrier), H.toHistory.isParabolicallyRmControlledBall t p r₀ →
    ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t) (v : ℝ),
      v ≤ E →
    ∀ q : (H.stage first).Carrier,
      H.toHistory.regularizedCost first (H.toHistory.activeStage t) hle t (3 / a₀) 0 v p q <
        (A : WithTop ℝ) →
      q ∈ H.toHistory.regularMinimizerEndpoints first (H.toHistory.activeStage t) hle t
        (3 / a₀) v p := by
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  refine ⟨a₀, ha₀, ?_⟩
  intro E A r₀ qcan Λ ρ Ctime hr₀ hqcan hΛ hρ
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    ObservedHistory.exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_derivative_before.{u}
      A (max E 0) r₀ qcan a₀ Λ ρ Ctime (le_max_right E 0) hr₀ hqcan ha₀ hΛ hρ
  refine ⟨δ₀, ε₀, R₀, m₀, hδ₀, hε₀, hR₀, ?_⟩
  intro p₀ δbound ρbound haccuracy₀ hradius₀ horder₀ hrecenter₀ hδbound hρbound H hid hrecords
    t hderiv p hball first hle v hvE q hcost
  obtain ⟨identification⟩ := hid
  obtain ⟨parameters, -, hradius, horder, haccuracy, hrecenter, records, hcanonical, hdelta,
    hneck⟩ := hrecords
  have hstart := hinitial H.toHistory identification
  obtain ⟨-, -, gamma, hgamma, -, hrecent, hold, -, hmin, hregular⟩ :=
    hbarrier H.toHistory parameters (horder ▸ horder₀) (hradius ▸ hradius₀)
      (haccuracy ▸ haccuracy₀) (hrecenter ▸ hrecenter₀) (fun j => (hdelta j).trans hδbound)
      (fun j => (hneck j).trans hρbound) records hstart.1 hstart.2 t hderiv p hball first hle v
      (hvE.trans (le_max_left E 0)) (fun i _ _ b => hcanonical i b) q hcost
  exact ⟨gamma, hgamma, hrecent, hold, hregular, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
