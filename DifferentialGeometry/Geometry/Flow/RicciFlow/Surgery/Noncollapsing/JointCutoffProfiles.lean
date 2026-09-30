import DifferentialGeometry.Analysis.Order.CommonProfile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
set_option autoImplicit false
noncomputable section
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem exists_two_register_cutoff_parameters
    (p : CutoffParameters) {b c : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n) :
    ∃ q : CutoffParameters,
      Antitone q.delta ∧ q.neckRadius = p.neckRadius ∧
      q.protectedRadius = p.protectedRadius ∧ q.fixed = p.fixed ∧
      q.modelRadius = p.modelRadius ∧ q.modelOrder = p.modelOrder ∧
      q.modelAccuracy = p.modelAccuracy ∧ q.recenterConstant = p.recenterConstant ∧
      (∀ (n : ℕ) (t : ℝ), (n : ℝ) ≤ t →
        q.delta t < b n ∧ q.delta t < c n ∧
        q.delta t < b (n + 1) ∧ q.delta t < c (n + 1)) ∧
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
        (R : GeometricCutoffRecord H i q) (n : ℕ),
        (n : ℝ) ≤ H.time i.succ →
        ∀ α : (H.event i).transition.trace.tubes.Index,
          R.delta α < b n ∧ R.delta α < c n ∧
          R.delta α < b (n + 1) ∧ R.delta α < c (n + 1) := by
  obtain ⟨δ, hpos, hanti, hone, hbudget⟩ := commonProfile_two_registers hb hc
  let q : CutoffParameters := { p with
    delta := δ
    delta_pos := fun t _ => hpos t
    delta_lt_one := fun t _ => hone t }
  refine ⟨q, hanti, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hbudget, ?_⟩
  intro H i R n hn α
  obtain ⟨hb₀, hc₀, hb₁, hc₁⟩ := hbudget n (H.time i.succ) hn
  exact ⟨(R.delta_le α).trans_lt hb₀, (R.delta_le α).trans_lt hc₀,
    (R.delta_le α).trans_lt hb₁, (R.delta_le α).trans_lt hc₁⟩

end GC.GeneralFlow
