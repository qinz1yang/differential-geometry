import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ {p₀ : CutoffParameters} {δ₀ ρ₀ : ℝ}, H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀ →
        H.EventSlabsPinched phi ∧
        ∀ (k : Fin (H.eventCount + 1)) {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s),
          G.flow.base.metric (H.time k) = H.initialMetric k →
          Perelman.PhiAlmostNonnegative G.flow (Ico (H.time k) s) phi := by
  obtain ⟨phi, hphi, hslab⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  refine ⟨phi, hphi, fun H hinit p₀ δ₀ ρ₀ hrec => ?_⟩
  obtain ⟨p, -, -, -, -, -, records, -, -, -⟩ := hrec
  exact ⟨fun j => hslab H.toHistory hinit p records j.castSucc (H.time j.succ)
      (H.toHistory.event j).incoming (H.toHistory.event_initial j),
    fun k s G hG => hslab H.toHistory hinit p records k s G hG⟩

theorem exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ {p₀ : CutoffParameters} {δ₀ ρ₀ : ℝ}, H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀ →
      ∀ (k : Fin (H.eventCount + 1)) {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s),
        G.flow.base.metric (H.time k) = H.initialMetric k → G.SingularEndpoint → a ≤ s := by
  obtain ⟨a, ha, hsing⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  refine ⟨a, ha, fun H hinit p₀ δ₀ ρ₀ hrec k s G hG hs => ?_⟩
  obtain ⟨p, -, -, -, -, -, records, -, -, -⟩ := hrec
  exact hsing H.toHistory hinit (fun i => (records i).singular) k s G hG hs

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
