import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

/-- A single pinching function is selected from the actual initial stage and
metric before any history or cutoff parameters. The closed final certificate
uses the actual final stage domain; it does not close an open continuation
estimate or assert the existence of a positive final slab. -/
theorem exists_pinching_certificates_for_identified_histories
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      ∀ (V : RetainedCoreHistory.{u})
        (_IV : InitialIdentification P g V.toHistory)
        (p : CutoffParameters)
        (_records : ∀ i : Fin V.eventCount,
          GeometricCutoffRecord V.toHistory i p),
        V.EventSlabsPinched phi ∧
        ∀ hfinal : V.time (Fin.last V.eventCount) < V.horizon,
          Perelman.PhiAlmostNonnegative (V.finalSlab hfinal).flow
            (Icc (V.time (Fin.last V.eventCount)) V.horizon) phi := by
  obtain ⟨a, ha, hzero⟩ :=
    exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  obtain ⟨phi, hphi, hall⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_observedHistories.{u} ha
  refine ⟨phi, hphi, ?_⟩
  intro V IV p records
  have hinitial := hzero V.toHistory IV
  have hphysical := (hall V.toHistory p records hinitial.1 hinitial.2).1
  constructor
  · intro j t ht x
    have hdomain : t ∈ V.toHistory.stageDomain j.castSucc := by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using ht
    have hp := hphysical j.castSucc t hdomain x
    rw [ObservedHistory.stageMetric_castSucc_apply] at hp
    exact hp
  · intro hfinal t ht x
    have hdomain : t ∈ V.toHistory.stageDomain (Fin.last V.eventCount) :=
      (V.toHistory.mem_stageDomain_last t).2 ht
    have hp := hphysical (Fin.last V.eventCount) t hdomain x
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfinal)] at hp
    exact hp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
