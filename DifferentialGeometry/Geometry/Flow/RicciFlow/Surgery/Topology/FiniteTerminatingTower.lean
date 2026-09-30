import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteEventHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryAbsorption
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionHorizon

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

namespace RetainedCoreHistory

variable {n : ℕ} (time : Fin (n + 1) → ℝ) (htime : StrictMono time) (hzero : time 0 = 0)
  (stage : Fin (n + 1) → OrientedThreeStage.{u}) (metric : (j : Fin (n + 1)) → (stage j).Metric)
  (event : (j : Fin n) → MetricCutCapEvent (stage j.castSucc) (stage j.succ)
    (time j.castSucc) (time j.succ))
  (hinitial : ∀ j, (event j).incoming.flow.base.metric (time j.castSucc) = metric j.castSucc)
  (houtput : ∀ j, (event j).outputMetric = metric j.succ)
  (hOld : ∀ j, (event j).old = (event j).transition.trace.retainedCore)

theorem finiteEvents_absorbingTower
    [hempty : IsEmpty (stage (Fin.last n)).Carrier] :
    let H := ofEvents time htime hzero stage metric event hinitial houtput hOld
    let hHempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
      simpa [H] using hempty
    ∃ T : RetainedCoreObservationTower (stage 0) (metric 0),
      towerExtinct T.toObservationTower ∧
      ∃ N : ℕ, 0 < N ∧ H.horizon ≤ (N : ℝ) ∧
        ∃ hN : H.horizon ≤ (N : ℝ),
          T.history N = @RetainedCoreHistory.emptyExtension H (by exact hHempty) (N : ℝ) hN
 := by
  dsimp
  let H := ofEvents time htime hzero stage metric event hinitial houtput hOld
  let A := ofEventsInitialIdentification time htime hzero stage metric event hinitial houtput hOld
  have hstage : H.stage (Fin.last H.eventCount) = stage (Fin.last n) := by
    simp [H]
  let hE : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := hstage ▸ hempty
  let T : RetainedCoreObservationTower (stage 0) (metric 0) :=
    @RetainedCoreHistory.absorbingTower _ _ H hE A
  refine ⟨T, ?_, ?_⟩
  · exact RetainedCoreHistory.towerExtinct_of_absorbingTower H A
  · let N : ℕ := Nat.ceil H.horizon + 1
    have hN : H.horizon ≤ (N : ℝ) := by
      dsimp [N]
      exact (Nat.le_ceil H.horizon).trans (by
        exact_mod_cast Nat.le_succ (Nat.ceil H.horizon))
    have hNpos : 0 < N := by
      dsimp [N]
      exact Nat.succ_pos _
    have hNhist : T.history N = @RetainedCoreHistory.emptyExtension H hE (N : ℝ) hN := by
      exact @RetainedCoreHistory.absorbingHistory_eq_emptyExtension H hE N hN
    exact ⟨N, hNpos, hN, hN, hNhist⟩

end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
