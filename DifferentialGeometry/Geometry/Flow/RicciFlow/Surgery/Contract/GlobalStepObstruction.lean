import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EmptyHistory

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem not_globalStepConclusion_of_empty_final
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (htime : τ ≤ H.time i.succ)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (hrecord : Nonempty (GeometricCutoffRecord H i p)) :
    ¬ GlobalStepConclusion p τ ε d k a₀ DiscardedCutOpen inputs := by
  intro h
  obtain ⟨hstar, hstar_pos, hstar_time, hstep⟩ := h
  obtain ⟨K, j, R, hj, hprefix, hcount, hτ, hpres, hradius, hdiscard, hpoincare,
      hscalar⟩ := hstep H i htime hrecord
  have hcount_empty := hprefix.eventCount_eq_of_empty
  omega

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem not_globalStepConclusion_of_false_discard
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (inputs : GlobalStepInputs.{u} p τ ε d k (fun _ => False))
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (htime : τ ≤ H.time i.succ)
    (hrecord : Nonempty (GeometricCutoffRecord H i p)) :
    ¬ GlobalStepConclusion p τ ε d k a₀ (fun _ => False) inputs := by
  intro h
  obtain ⟨hstar, hstar_pos, hstar_time, hstep⟩ := h
  obtain ⟨K, j, R, hj, hprefix, hcount, hτ, hpres, hradius, hdiscard, hpoincare,
      hscalar⟩ := hstep H i htime hrecord
  exact hdiscard

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem nonempty_final_stage_of_globalStepConclusion
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)
    (h : GlobalStepConclusion p τ ε d k a₀ DiscardedCutOpen inputs)
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (htime : τ ≤ H.time i.succ)
    (hrecord : Nonempty (GeometricCutoffRecord H i p)) :
    Nonempty (H.stage (Fin.last H.eventCount)).Carrier := by
  apply not_isEmpty_iff.mp
  intro hempty
  exact @not_globalStepConclusion_of_empty_final p τ ε d k a₀ DiscardedCutOpen inputs H i
    htime hempty hrecord h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
