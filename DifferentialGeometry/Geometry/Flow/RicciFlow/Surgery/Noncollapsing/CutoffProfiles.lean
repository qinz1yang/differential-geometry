import DifferentialGeometry.Analysis.Order.CommonProfile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
set_option autoImplicit false
noncomputable section
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

def withCommonProfile (p : CutoffParameters) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) :
    CutoffParameters :=
  { p with
    delta := commonProfile b
    delta_pos := fun t _ => commonProfile_pos hb t
    delta_lt_one := fun t _ => commonProfile_lt_one b t }

theorem withCommonProfile_delta (p : CutoffParameters) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (t : ℝ) :
    (withCommonProfile p b hb).delta t = commonProfile b t := rfl

theorem recorded_neck_budgets (p : CutoffParameters) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (R : GeometricCutoffRecord H i (withCommonProfile p b hb))
    (n : ℕ) (hn : (n : ℝ) ≤ H.time i.succ)
    (α : (H.event i).transition.trace.tubes.Index) :
    R.delta α < b n ∧ R.delta α < b (n + 1) := by
  obtain ⟨h₀,h₁⟩ := commonProfile_interval_budgets hb n (H.time i.succ) hn
  exact ⟨(R.delta_le α).trans_lt h₀, (R.delta_le α).trans_lt h₁⟩

theorem recorded_nominal_radius_budget (p : CutoffParameters) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (R : GeometricCutoffRecord H i (withCommonProfile p b hb))
    (h : Nonempty (H.event i).transition.trace.tubes.Index) :
    R.nominalRadius h < commonProfile b (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) :=
  R.nominal_small h

end GC.GeneralFlow
